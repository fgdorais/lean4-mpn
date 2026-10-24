/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.HGCD
public import MPN.Generic.Ops64
public import MPN.Lehmer

/-!
# Greatest common divisor

`Num.gcd a b` is `Nat.gcd a.toNat b.toNat`, ported from `main`:

* Lehmer's algorithm (`gcdLehmer`): Euclid's steps on the leading 62 bits of the two numbers
  (`lehmerSteps`, in `Int64`) give a matrix of determinant `±1` (`lehmerMat`), which is applied to
  the full numbers at once (`NatOps.applyInvC`); when it does not apply or does not make the
  numbers smaller, one step of Euclid's algorithm is taken instead. Nothing about the steps on
  the words needs a proof: a matrix of determinant `±1` keeps the greatest common divisor.
* Half-gcd (`NatOps.hgcdReduce`, with Lehmer's matrices as its base step) from `gcdHalf` limbs.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Lehmer's steps on words -/

/-- The cofactors of a run of Lehmer's steps, as one object with unboxed fields. -/
structure Cofactors where
  A : Int64
  B : Int64
  C : Int64
  D : Int64

/--
Euclid's algorithm on the leading words `x ≥ y` of two numbers, with the cofactors `A`, `B`, `C`,
`D` of the steps so far, like GMP's `hgcd2` on one word: it stops when the remainder falls below
`2³¹`, half the bits of the words, which keeps the cofactors below `2³¹`, or when Jebelean's
condition fails, which makes the quotients those of the full numbers. Nothing is proved about it:
`lehmerMat` checks the determinant of the cofactors, and the caller that the numbers got smaller.
-/
def lehmerSteps (x y A B C D : Int64) : Nat → Cofactors
  | 0 => ⟨A, B, C, D⟩
  | f + 1 =>
    if y < 0x80000000 then ⟨A, B, C, D⟩
    else
      let q : Int64 := if x < y + y then 1 else x / y
      let r := x - q * y
      let C' := A - q * C
      let D' := B - q * D
      if r < C'.abs ∨ r < D'.abs ∨ y - r < (C' - C).abs ∨ y - r < (D' - D).abs ∨
          0x80000000 ≤ C'.abs ∨ 0x80000000 ≤ D'.abs then
        ⟨A, B, C, D⟩
      else lehmerSteps y r C D C' D' f

/-- Two words, as one object with unboxed fields. -/
structure LeadWords where
  x : Int64
  y : Int64

/--
The leading 62 bits of `a`, from its top nonzero limb, and the bits of `b` at the same positions,
as the words of Lehmer's algorithm. Their values only affect its speed.
-/
def leadWords (a b : UInt64Array) : LeadWords :=
  let L := MPN.log2 a.toUSlice
  let n := L / 64
  let c := (63 - L % 64).toUInt64
  let lead (t₁ t₀ : UInt64) : Int64 := (((t₁ <<< c) ||| ((t₀ >>> 1) >>> (63 - c))) >>> 2).toInt64
  let w (x : UInt64Array) (i : Nat) : UInt64 := if h : i < x.size then x[i] else 0
  ⟨lead (w a n) (w a (n - 1)), lead (w b n) (w b (n - 1))⟩

/--
`|x|` as a natural number, with word arithmetic: `Int64.toInt` goes through the constant `2⁶⁴`,
which the compiled code rebuilds from its digits at every call. Its value only affects speed.
-/
@[inline] def absN (x : Int64) : Nat := if x < 0 then (0 - x).toUInt64.toNat else x.toUInt64.toNat

/-- A limb holding `k`. -/
def limbOf (k : Nat) : UInt64Array := UInt64Array.replicate 1 k.toUInt64

private theorem toNat_limbOf (k : Nat) (h : k < 2 ^ 64) : (limbOf k).toNat = k := by
  simp [limbOf, toNat_eq_valAt, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/--
Lehmer's steps on the leading words of `a ≥ b` as a matrix: the cofactors `A`, `B`, `C`, `D` of
`lehmerSteps` give `M = [[|D|, |B|], [|C|, |A|]]`, whose `applyInv` is `(|A a + B b|, |C a + D b|)`,
when their determinant is `±1`.
-/
public def lehmerMat (a b : UInt64Array) : Option (Mat2 UInt64Array) :=
  let w := leadWords a b
  let m := lehmerSteps w.x w.y 1 0 0 1 100
  let A := absN m.A
  let B := absN m.B
  let C := absN m.C
  let D := absN m.D
  if A < 2 ^ 32 ∧ B < 2 ^ 32 ∧ C < 2 ^ 32 ∧ D < 2 ^ 32 then
    if D * A = B * C + 1 then some ⟨limbOf D, limbOf B, limbOf C, limbOf A, false⟩
    else if B * C = D * A + 1 then some ⟨limbOf D, limbOf B, limbOf C, limbOf A, true⟩
    else none
  else none

public theorem unimodular_lehmerMat (a b : UInt64Array) (S : Mat2 UInt64Array)
    (h : lehmerMat a b = some S) : ops64.Unimodular S := by
  unfold lehmerMat at h
  dsimp only at h
  split at h
  · rename_i hb
    obtain ⟨hA, hB, hC, hD⟩ := hb
    split at h
    · rename_i he
      rw [Option.some.injEq] at h
      subst h
      simp only [NatOps.Unimodular, ops64_val]
      rw [toNat_limbOf _ (by lia), toNat_limbOf _ (by lia), toNat_limbOf _ (by lia),
        toNat_limbOf _ (by lia)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      lia
    · split at h
      · rename_i _ he
        rw [Option.some.injEq] at h
        subst h
        simp only [NatOps.Unimodular, ops64_val]
        rw [toNat_limbOf _ (by lia), toNat_limbOf _ (by lia), toNat_limbOf _ (by lia),
          toNat_limbOf _ (by lia)]
        simp only [↓reduceIte]
        lia
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Lehmer's algorithm -/


/-- `|x|` as a word. -/
@[inline] def absW (x : Int64) : UInt64 := if x < 0 then (0 - x).toUInt64 else x.toUInt64

/-- Whether `a d = b c + 1`, on words, for `a, b, c, d < 2⁶²`. -/
@[inline] def eqPlusOne (a d b c : UInt64) : Bool :=
  let l := b * c + 1
  UInt64.mulh a d == UInt64.mulh b c + (if l = 0 then 1 else 0) && a * d == l

private theorem eqPlusOne_iff (a d b c : UInt64) (hb : b.toNat < 2 ^ 62) (hc : c.toNat < 2 ^ 62) :
    eqPlusOne a d b c = true → a.toNat * d.toNat = b.toNat * c.toNat + 1 := by
  simp only [eqPlusOne, Bool.and_eq_true, beq_iff_eq]
  rintro ⟨h₁, h₂⟩
  have e₁ := congrArg UInt64.toNat h₁
  have e₂ := congrArg UInt64.toNat h₂
  have hbc : b.toNat * c.toNat < 2 ^ 124 := by
    have := Nat.mul_lt_mul_of_lt_of_le hb (Nat.le_of_lt hc) (by decide : 0 < 2 ^ 62); lia
  rw [UInt64.toNat_mulh, UInt64.toNat_add, UInt64.toNat_mulh] at e₁
  rw [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_mul] at e₂
  have hd₁ := Nat.div_add_mod (a.toNat * d.toNat) (2 ^ 64)
  have hd₂ := Nat.div_add_mod (b.toNat * c.toNat) (2 ^ 64)
  have hq : b.toNat * c.toNat / 2 ^ 64 < 2 ^ 60 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; lia
  split at e₁
  · rename_i hl
    have hl' := congrArg UInt64.toNat hl
    rw [UInt64.toNat_add, UInt64.toNat_mul] at hl'
    simp only [UInt64.toNat_one, UInt64.toNat_zero] at hl' e₁ e₂
    have := Nat.mod_lt (b.toNat * c.toNat) (show 0 < 2 ^ 64 by decide)
    rw [Nat.mod_eq_of_lt (a := b.toNat * c.toNat / 2 ^ 64 + 1) (by lia)] at e₁
    lia
  · rename_i hl
    have hl' : (b * c + 1).toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [UInt64.toNat_add, UInt64.toNat_mul] at hl'
    simp only [UInt64.toNat_one, UInt64.toNat_zero, Nat.add_zero] at hl' e₁ e₂
    rw [Nat.mod_eq_of_lt (a := b.toNat * c.toNat / 2 ^ 64) (by lia)] at e₁
    have := Nat.mod_lt (b.toNat * c.toNat) (show 0 < 2 ^ 64 by decide)
    have : b.toNat * c.toNat % 2 ^ 64 + 1 < 2 ^ 64 := by
      rcases Nat.lt_or_ge (b.toNat * c.toNat % 2 ^ 64 + 1) (2 ^ 64) with h | h
      · exact h
      · exfalso; apply hl'; rw [show b.toNat * c.toNat % 2 ^ 64 + 1 = 2 ^ 64 by lia]
    rw [Nat.mod_eq_of_lt this] at e₂
    lia

/--
The numbers `|A x + B y|` and `|C x + D y|` of a step of Lehmer's algorithm with the cofactors
`m`, when they are valid: below `2⁶²`, of determinant `±1`, and each difference nonnegative in the
order the signs of the cofactors give, in one pass each (`mulSubMul`).
-/
def applyCof (x y : UInt64Array) (m : Cofactors) : Option (UInt64Array × UInt64Array) :=
  let A := absW m.A
  let B := absW m.B
  let C := absW m.C
  let D := absW m.D
  if A < 0x4000000000000000 ∧ B < 0x4000000000000000 ∧ C < 0x4000000000000000 ∧
      D < 0x4000000000000000 ∧ (eqPlusOne A D B C || eqPlusOne B C A D) then
    let u := if 0 ≤ m.A then mulSubMul x y A B else mulSubMul y x B A
    let v := if 0 ≤ m.D then mulSubMul y x D C else mulSubMul x y C D
    match u, v with
    | some u, some v => some (trimA u, trimA v)
    | _, _ => none
  else none

/-- A valid step of Lehmer's algorithm keeps the greatest common divisor. -/
private theorem gcd_applyCof (x y : UInt64Array) (m : Cofactors) (p : UInt64Array × UInt64Array)
    (h : applyCof x y m = some p) : Nat.gcd p.1.toNat p.2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold applyCof at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain ⟨hA, hB, hC, hD, hdet⟩ := hc
    rw [UInt64.lt_iff_toNat_lt] at hA hB hC hD
    simp only [UInt64.reduceToNat] at hA hB hC hD
    have hdet' : (absW m.A).toNat * (absW m.D).toNat = (absW m.B).toNat * (absW m.C).toNat + 1 ∨
        (absW m.B).toNat * (absW m.C).toNat = (absW m.A).toNat * (absW m.D).toNat + 1 := by
      rcases Bool.or_eq_true_iff.1 hdet with e | e
      · exact .inl (eqPlusOne_iff _ _ _ _ (by lia) (by lia) e)
      · exact .inr (eqPlusOne_iff _ _ _ _ (by lia) (by lia) e)
    split at h
    · rename_i u v hu hv
      rw [Option.some.injEq] at h
      subst h
      simp only [toNat_trimA]
      generalize absW m.A = A at *
      generalize absW m.B = B at *
      generalize absW m.C = C at *
      generalize absW m.D = D at *
      have eu : (u.toNat : Int) = A.toNat * x.toNat - B.toNat * y.toNat ∨
          (u.toNat : Int) = B.toNat * y.toNat - A.toNat * x.toNat := by
        split at hu
        · exact .inl (toNat_mulSubMul x y _ _ hA hB u hu)
        · exact .inr (toNat_mulSubMul y x _ _ hB hA u hu)
      have ev : (v.toNat : Int) = D.toNat * y.toNat - C.toNat * x.toNat ∨
          (v.toNat : Int) = C.toNat * x.toNat - D.toNat * y.toNat := by
        split at hv
        · exact .inl (toNat_mulSubMul y x _ _ hD hC v hv)
        · exact .inr (toNat_mulSubMul x y _ _ hC hD v hv)
      have g := NatOps.gcd_unimodular x.toNat y.toNat A.toNat (-(B.toNat : Int))
        (-(C.toNat : Int)) D.toNat (by
          rcases hdet' with e | e
          · left
            have : ((A.toNat * D.toNat : Nat) : Int) = ((B.toNat * C.toNat + 1 : Nat) : Int) := by
              rw [e]
            push_cast at this; lia
          · right
            have : ((B.toNat * C.toNat : Nat) : Int) = ((A.toNat * D.toNat + 1 : Nat) : Int) := by
              rw [e]
            push_cast at this; lia)
      rw [← g]
      congr 1
      · rcases eu with e | e <;> lia
      · rcases ev with e | e <;> lia
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The leading 128 bits of two numbers, as four words with unboxed fields. -/
structure Lead2 where
  xh : UInt64
  xl : UInt64
  yh : UInt64
  yl : UInt64

/--
The leading 128 bits of `a`, from its top nonzero limb, and the bits of `b` at the same
positions. Their values only affect speed.
-/
def lead2 (a b : UInt64Array) : Lead2 :=
  let L := MPN.log2 a.toUSlice
  let n := L / 64
  let c := (63 - L % 64).toUInt64
  let sh (t₁ t₀ : UInt64) : UInt64 := (t₁ <<< c) ||| ((t₀ >>> 1) >>> (63 - c))
  let w (x : UInt64Array) (i : Nat) : UInt64 := if i ≤ n ∧ n - i < x.size then x[n - i]! else 0
  ⟨sh (w a 0) (w a 1), sh (w a 1) (w a 2), sh (w b 0) (w b 1), sh (w b 1) (w b 2)⟩

/-- The high word of `A X + B Y` modulo `2¹²⁸` for words `A`, `B` in two's complement. -/
@[inline] def comb2h (A B : Int64) (xh xl yh yl : UInt64) : UInt64 :=
  let a := A.toUInt64
  let b := B.toUInt64
  let lo₁ := a * xl
  let lo₂ := b * yl
  let lo := lo₁ + lo₂
  UInt64.mulh a xl + a * xh - (if A < 0 then xl else 0) + UInt64.mulh b yl + b * yh -
    (if B < 0 then yl else 0) + (if lo < lo₁ then 1 else 0)

/-- The low word of `A X + B Y` modulo `2¹²⁸`. -/
@[inline] def comb2l (A B : Int64) (xl yl : UInt64) : UInt64 :=
  A.toUInt64 * xl + B.toUInt64 * yl

/--
The cofactors of two runs of Lehmer's steps, like GMP's `hgcd2`: the first on the leading 62
bits, applied to the leading 128 bits of both numbers, then the second on the leading 62 bits of
those, and their product, with cofactors below `2⁶²`. Nothing is proved about them: `applyCof`
checks them.
-/
def cofactors2 (x y : UInt64Array) : Cofactors :=
  let l := lead2 x y
  let m₁ := lehmerSteps (l.xh >>> 2).toInt64 (l.yh >>> 2).toInt64 1 0 0 1 100
  let xh := comb2h m₁.A m₁.B l.xh l.xl l.yh l.yl
  let xl := comb2l m₁.A m₁.B l.xl l.yl
  let yh := comb2h m₁.C m₁.D l.xh l.xl l.yh l.yl
  let yl := comb2l m₁.C m₁.D l.xl l.yl
  if xh = 0 ∨ xh < yh then m₁
  else
    let c := 63 - xh.log2
    let x₂ := (((xh <<< c) ||| ((xl >>> 1) >>> (63 - c))) >>> 2).toInt64
    let y₂ := (((yh <<< c) ||| ((yl >>> 1) >>> (63 - c))) >>> 2).toInt64
    let m₂ := lehmerSteps x₂ y₂ 1 0 0 1 100
    ⟨m₂.A * m₁.A + m₂.B * m₁.C, m₂.A * m₁.B + m₂.B * m₁.D, m₂.C * m₁.A + m₂.D * m₁.C,
      m₂.C * m₁.B + m₂.D * m₁.D⟩

/--
Lehmer's step on the full numbers: the cofactors of two runs on the leading words (`cofactors2`),
or of one run when those do not apply.
-/
def lehmerStep (x y : UInt64Array) : Option (UInt64Array × UInt64Array) :=
  match applyCof x y (cofactors2 x y) with
  | some p => some p
  | none =>
    let w := leadWords x y
    applyCof x y (lehmerSteps w.x w.y 1 0 0 1 100)

private theorem gcd_lehmerStep (x y : UInt64Array) (p : UInt64Array × UInt64Array)
    (h : lehmerStep x y = some p) : Nat.gcd p.1.toNat p.2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold lehmerStep at h
  split at h
  · rename_i q hq
    rw [Option.some.injEq] at h
    subst h
    exact gcd_applyCof x y _ q hq
  · exact gcd_applyCof x y _ p h

/-- `x mod y`. -/
def modN (x y : UInt64Array) : UInt64Array := (ops64.divRem x y).2

private theorem toNat_modN (x y : UInt64Array) (hy : y.toNat ≠ 0) :
    (modN x y).toNat = x.toNat % y.toNat :=
  (ops64.val_divRem x y hy).2

/-- `0`, as an array without limbs. -/
def zeroA : UInt64Array := UInt64Array.replicate 0 0

private theorem toNat_zeroA : zeroA.toNat = 0 := by simp [zeroA, toNat_eq_valAt]

/-- The greatest common divisor of two words, by Euclid's algorithm. -/
def wordGcd (a b : UInt64) : UInt64 := if _h : b = 0 then a else wordGcd b (a % b)
termination_by b.toNat
decreasing_by
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun e => _h (UInt64.toNat_inj.1 (by rw [e]; rfl)))

private theorem toNat_wordGcd (a b : UInt64) :
    (wordGcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  induction a, b using wordGcd.induct with
  | case1 a => rw [wordGcd]; simp
  | case2 a b h ih =>
    rw [wordGcd, dite_eq_right h, ih, UInt64.toNat_mod]
    exact (Nat.gcd_comm _ _).trans ((Nat.gcd_rec _ _).symm.trans (Nat.gcd_comm _ _))

private theorem toNat_small (x : UInt64Array) (h : x.size ≤ 1) :
    x.toNat = (Num.limbAt x 0).toNat := by
  rw [toNat_eq_valAt, Num.limbAt_eq]
  rcases Nat.lt_or_ge x.size 1 with h0 | h0
  · rw [show x.size = 0 by lia, valAt_zero, getElem!_neg x 0 (by lia)]; rfl
  · rw [show x.size = 1 by lia, valAt_one]

/--
The greatest common divisor by Lehmer's algorithm: Lehmer's step on the leading words, applied to
the full numbers when it is valid and makes them smaller, and otherwise one step of Euclid's
algorithm; on words when both numbers have at most one limb.
-/
public def gcdLehmer (x y : UInt64Array) : UInt64Array :=
  if x.size ≤ 1 ∧ y.size ≤ 1 then
    UInt64Array.replicate 1 (wordGcd (Num.limbAt x 0) (Num.limbAt y 0))
  else if _h : ops64.le y zeroA = true then x
  else if ops64.le y x = false then gcdLehmer y (modN x y)
  else
    match lehmerStep x y with
    | some p => if _hy : ops64.le y p.2 = false then gcdLehmer p.1 p.2 else gcdLehmer y (modN x y)
    | none => gcdLehmer y (modN x y)
termination_by y.toNat
decreasing_by
  all_goals first
    | (rw [← Bool.not_eq_true, ops64.le_iff] at _hy; simp only [ops64_val] at _hy; lia)
    | (rw [ops64.le_iff] at _h
       simp only [ops64_val, toNat_zeroA] at _h
       rw [toNat_modN _ _ (by lia)]
       exact Nat.mod_lt _ (by lia))

private theorem ne_zero_of (y : UInt64Array) (h : ¬ops64.le y zeroA = true) :
    y.toNat ≠ 0 := by
  rw [ops64.le_iff] at h
  simp only [ops64_val, toNat_zeroA] at h
  lia

private theorem gcd_mod_step (x y : UInt64Array) (hy : y.toNat ≠ 0) :
    Nat.gcd y.toNat (modN x y).toNat = Nat.gcd x.toNat y.toNat := by
  rw [toNat_modN _ _ hy, Nat.gcd_comm x.toNat y.toNat, Nat.gcd_rec y.toNat x.toNat, Nat.gcd_comm]

public theorem toNat_gcdLehmer (x y : UInt64Array) :
    (gcdLehmer x y).toNat = Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdLehmer.induct with
  | case1 x y hs =>
    rw [gcdLehmer, ite_eq_left hs, toNat_small x hs.1, toNat_small y hs.2, ← toNat_wordGcd]
    simp [toNat_eq_valAt]
  | case2 x y hs h =>
    rw [gcdLehmer, ite_eq_right hs, dite_eq_left_of_eq_true (eq_true h)]
    rw [ops64.le_iff] at h
    simp only [ops64_val, toNat_zeroA] at h
    rw [show y.toNat = 0 by lia, Nat.gcd_zero_right]
  | case3 x y hs h hlt ih =>
    rw [gcdLehmer, ite_eq_right hs, dite_eq_right h, ite_eq_left hlt, ih,
      gcd_mod_step _ _ (ne_zero_of y h)]
  | case4 x y hs h hlt p hp hy ih =>
    rw [gcdLehmer, ite_eq_right hs, dite_eq_right h, ite_eq_right hlt]
    simp only [hp, dite_eq_left_of_eq_true (eq_true hy), ih]
    exact gcd_lehmerStep x y p hp
  | case5 x y hs h hlt p hp hy ih =>
    rw [gcdLehmer, ite_eq_right hs, dite_eq_right h, ite_eq_right hlt]
    simp only [hp, dite_eq_right_of_eq_false (eq_false hy), ih,
      gcd_mod_step _ _ (ne_zero_of y h)]
  | case6 x y hs h hlt hp ih =>
    rw [gcdLehmer, ite_eq_right hs, dite_eq_right h, ite_eq_right hlt]
    simp only [hp, ih, gcd_mod_step _ _ (ne_zero_of y h)]

/-! ## Half-gcd -/

/-- A word as an array of one limb. -/
def wordA (w : UInt64) : UInt64Array := UInt64Array.replicate 1 w

private theorem toNat_wordA (w : UInt64) : (wordA w).toNat = w.toNat := by
  simp [wordA, toNat_eq_valAt]

/--
The matrix `[[|D|, |B|], [|C|, |A|]]` of the cofactors `m`, when they are below `2⁶²` and their
determinant is `±1`, checked on words.
-/
def cofMat (m : Cofactors) : Option (Mat2 UInt64Array) :=
  let A := absW m.A
  let B := absW m.B
  let C := absW m.C
  let D := absW m.D
  if A < 0x4000000000000000 ∧ B < 0x4000000000000000 ∧ C < 0x4000000000000000 ∧
      D < 0x4000000000000000 then
    if eqPlusOne D A B C then some ⟨wordA D, wordA B, wordA C, wordA A, false⟩
    else if eqPlusOne B C D A then some ⟨wordA D, wordA B, wordA C, wordA A, true⟩
    else none
  else none

private theorem unimodular_cofMat (m : Cofactors) (S : Mat2 UInt64Array)
    (h : cofMat m = some S) : ops64.Unimodular S := by
  unfold cofMat at h
  dsimp only at h
  split at h
  · rename_i hb
    obtain ⟨hA, hB, hC, hD⟩ := hb
    rw [UInt64.lt_iff_toNat_lt] at hA hB hC hD
    simp only [UInt64.reduceToNat] at hA hB hC hD
    split at h
    · rename_i he
      have e := eqPlusOne_iff _ _ _ _ (by lia) (by lia) he
      rw [Option.some.injEq] at h
      subst h
      simp only [NatOps.Unimodular, ops64_val, toNat_wordA, Bool.false_eq_true, ↓reduceIte]
      have : (((absW m.D).toNat * (absW m.A).toNat : Nat) : Int) =
          (((absW m.B).toNat * (absW m.C).toNat + 1 : Nat) : Int) := by rw [e]
      push_cast at this; lia
    · split at h
      · rename_i _ he
        have e := eqPlusOne_iff _ _ _ _ (by lia) (by lia) he
        rw [Option.some.injEq] at h
        subst h
        simp only [NatOps.Unimodular, ops64_val, toNat_wordA, ↓reduceIte]
        have : (((absW m.B).toNat * (absW m.C).toNat : Nat) : Int) =
            (((absW m.D).toNat * (absW m.A).toNat + 1 : Nat) : Int) := by rw [e]
        push_cast at this; lia
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The base step of half-gcd: the matrix of `cofactors2`, or of one run of Lehmer's steps. -/
public def lehmerMat2 (a b : UInt64Array) : Option (Mat2 UInt64Array) :=
  match cofMat (cofactors2 a b) with
  | some M => some M
  | none => lehmerMat a b

public theorem unimodular_lehmerMat2 (a b : UInt64Array) (S : Mat2 UInt64Array)
    (h : lehmerMat2 a b = some S) : ops64.Unimodular S := by
  unfold lehmerMat2 at h
  split at h
  · rename_i M hM
    rw [Option.some.injEq] at h
    subst h
    exact unimodular_cofMat _ _ hM
  · exact unimodular_lehmerMat a b S h

/-- The size below which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 8

/-- One reduction by half-gcd (`NatOps.hgcdReduce`), on the larger number first. -/
def hgcdOrd (x y : UInt64Array) : UInt64Array × UInt64Array :=
  if ops64.le y x then ops64.hgcdReduce lehmerMat2 hgcdBase x y
  else ops64.hgcdReduce lehmerMat2 hgcdBase y x

private theorem gcd_hgcdOrd (x y : UInt64Array) :
    Nat.gcd (hgcdOrd x y).1.toNat (hgcdOrd x y).2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold hgcdOrd
  split
  · exact ops64.gcd_hgcdReduce lehmerMat2 unimodular_lehmerMat2 hgcdBase x y
  · have := ops64.gcd_hgcdReduce lehmerMat2 unimodular_lehmerMat2 hgcdBase y x
    simp only [ops64_val] at this
    rw [this, Nat.gcd_comm]

/-- The smaller of two numbers. -/
def minN (x y : UInt64Array) : UInt64Array := if ops64.le x y then x else y

private theorem toNat_minN_le (x y : UInt64Array) : (minN x y).toNat ≤ y.toNat := by
  unfold minN
  split
  · rename_i h; rw [ops64.le_iff] at h; exact h
  · exact Nat.le_refl _

/--
The greatest common divisor: from `half` limbs in the smaller number, reductions by half-gcd while
they make it smaller, and Lehmer's algorithm (`gcdLehmer`) below and otherwise.
-/
public def gcdWith (half : Nat) (x y : UInt64Array) : UInt64Array :=
  if half ≤ (minN x y).size then
    let p := hgcdOrd x y
    if _hy : ops64.le (minN x y) p.2 = false then gcdWith half p.1 p.2 else gcdLehmer x y
  else gcdLehmer x y
termination_by y.toNat
decreasing_by
  rw [← Bool.not_eq_true, ops64.le_iff] at _hy
  simp only [ops64_val] at _hy
  have := toNat_minN_le x y
  lia

public theorem toNat_gcdWith (half : Nat) (x y : UInt64Array) :
    (gcdWith half x y).toNat = Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdWith.induct half with
  | case1 x y h p hy ih =>
    rw [gcdWith, ite_eq_left h]
    simp only [p] at hy ih
    rw [dite_eq_left_of_eq_true (eq_true hy), ih, gcd_hgcdOrd]
  | case2 x y h p hy =>
    rw [gcdWith, ite_eq_left h]
    simp only [p] at hy
    rw [dite_eq_right_of_eq_false (eq_false hy), toNat_gcdLehmer]
  | case3 x y h =>
    rw [gcdWith, ite_eq_right h, toNat_gcdLehmer]

/-- The number of limbs of the smaller number from which `gcd` uses half-gcd. -/
public def gcdHalf : Nat := 4096

/-- `Nat.gcd a.toNat b.toNat`. -/
public def Num.gcd (a b : UInt64Array) : UInt64Array := gcdWith gcdHalf a b

@[simp] public theorem Num.toNat_gcd (a b : UInt64Array) :
    (Num.gcd a b).toNat = Nat.gcd a.toNat b.toNat :=
  toNat_gcdWith ..

end MPN
