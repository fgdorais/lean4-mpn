/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.HGCD
public import MPN.Generic.Ops64
public import MPN.Lehmer
public import MPN.WordGcd

/-!
# Greatest common divisor

The parts of the greatest common divisor that depend on 64-bit limbs, for `main`'s `GNat.gcd`
(`MPN.NatGcd`, with the instance in `MPN.Nat`), ported from `main`:

* Lehmer's step (`lehmerStep`): two runs of Euclid's steps on the leading words of the two
  numbers (`cofactors2`, with `lehmerSteps` in `Int64`) give cofactors of about 62 bits, which are
  checked on words (`applyCof`: determinant `±1`) and applied to the full numbers in one pass each
  (`mulSubMul`). Nothing about the steps on the words needs a proof: a matrix of determinant `±1`
  keeps the greatest common divisor.
* Half-gcd (`NatOps.hgcdReduce`, `hgcd64`), whose base case up to `hgcdBase` limbs is the same
  steps with their matrix kept up to date in one pass per entry (`baseW`, `mulAddMul`).
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Lehmer's steps on words

`lehmerSteps`, with its `Cofactors`, and `LeadWords` are in `MPN.WordGcd`.
-/

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
public def lehmerStep (x y : UInt64Array) : Option (UInt64Array × UInt64Array) :=
  match applyCof x y (cofactors2 x y) with
  | some p => some p
  | none =>
    let w := leadWords x y
    applyCof x y (lehmerSteps w.x w.y 1 0 0 1 100)

public theorem gcd_lehmerStep (x y : UInt64Array) (p : UInt64Array × UInt64Array)
    (h : lehmerStep x y = some p) : Nat.gcd p.1.toNat p.2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold lehmerStep at h
  split at h
  · rename_i q hq
    rw [Option.some.injEq] at h
    subst h
    exact gcd_applyCof x y _ q hq
  · exact gcd_applyCof x y _ p h

/-! ## Half-gcd -/

/-- A `2 × 2` matrix of words below `2⁶²`, and the sign of its determinant. -/
structure WMat where
  s11 : UInt64
  s12 : UInt64
  s21 : UInt64
  s22 : UInt64
  neg : Bool

/-- `S` has entries below `2⁶²` and determinant `±1`, with the sign of `S.neg`. -/
def WMat.OK (S : WMat) : Prop :=
  S.s11.toNat < 2 ^ 62 ∧ S.s12.toNat < 2 ^ 62 ∧ S.s21.toNat < 2 ^ 62 ∧ S.s22.toNat < 2 ^ 62 ∧
    (S.neg = false → S.s11.toNat * S.s22.toNat = S.s12.toNat * S.s21.toNat + 1) ∧
    (S.neg = true → S.s12.toNat * S.s21.toNat = S.s11.toNat * S.s22.toNat + 1)

/--
The matrix `[[|D|, |B|], [|C|, |A|]]` of the cofactors `m`, whose `S⁻¹ (a, b)` is
`(|A a + B b|, |C a + D b|)`, when its entries are below `2⁶²` and its determinant is `±1`, checked
on words.
-/
def wmatOf (m : Cofactors) : Option WMat :=
  let A := absW m.A
  let B := absW m.B
  let C := absW m.C
  let D := absW m.D
  if A < 0x4000000000000000 ∧ B < 0x4000000000000000 ∧ C < 0x4000000000000000 ∧
      D < 0x4000000000000000 then
    if eqPlusOne D A B C then some ⟨D, B, C, A, false⟩
    else if eqPlusOne B C D A then some ⟨D, B, C, A, true⟩
    else none
  else none

private theorem ok_wmatOf (m : Cofactors) (S : WMat) (h : wmatOf m = some S) : S.OK := by
  unfold wmatOf at h
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
      exact ⟨hD, hB, hC, hA, fun _ => e, fun h => absurd h (by simp)⟩
    · split at h
      · rename_i _ he
        have e := eqPlusOne_iff _ _ _ _ (by lia) (by lia) he
        rw [Option.some.injEq] at h
        subst h
        exact ⟨hD, hB, hC, hA, fun h => absurd h (by simp), fun _ => e⟩
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/--
`S⁻¹ (a, b)` when its entries are nonnegative, by `mulSubMul` in one pass each: the numbers
`(x, y)` with `(a, b) = S (x, y)`.
-/
def applyW (S : WMat) (a b : UInt64Array) : Option (UInt64Array × UInt64Array) :=
  let x := if !S.neg then mulSubMul a b S.s22 S.s12 else mulSubMul b a S.s12 S.s22
  let y := if !S.neg then mulSubMul b a S.s11 S.s21 else mulSubMul a b S.s21 S.s11
  match x, y with
  | some x, some y => some (trimA x, trimA y)
  | _, _ => none

private theorem fwd_w_pos (a b x y p q r t : Int) (hd : p * t = q * r + 1)
    (hx : x = t * a - q * b) (hy : y = p * b - r * a) :
    a = p * x + q * y ∧ b = r * x + t * y := by
  subst hx hy; constructor <;> grind

private theorem fwd_w_neg (a b x y p q r t : Int) (hd : q * r = p * t + 1)
    (hx : x = q * b - t * a) (hy : y = r * a - p * b) :
    a = p * x + q * y ∧ b = r * x + t * y := by
  subst hx hy; constructor <;> grind

private theorem fwd_applyW (S : WMat) (hS : S.OK) (a b : UInt64Array)
    (p : UInt64Array × UInt64Array) (h : applyW S a b = some p) :
    a.toNat = S.s11.toNat * p.1.toNat + S.s12.toNat * p.2.toNat ∧
      b.toNat = S.s21.toNat * p.1.toNat + S.s22.toNat * p.2.toNat := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, hp, hn⟩ := hS
  unfold applyW at h
  dsimp only at h
  split at h
  · rename_i x y hx hy
    rw [Option.some.injEq] at h
    subst h
    simp only [toNat_trimA]
    suffices (a.toNat : Int) = S.s11.toNat * x.toNat + S.s12.toNat * y.toNat ∧
        (b.toNat : Int) = S.s21.toNat * x.toNat + S.s22.toNat * y.toNat by
      constructor <;> lia
    cases hs : S.neg
    · rw [hs] at hx hy
      simp only [Bool.not_false, ↓reduceIte] at hx hy
      have ex := toNat_mulSubMul _ _ _ _ h₂₂ h₁₂ x hx
      have ey := toNat_mulSubMul _ _ _ _ h₁₁ h₂₁ y hy
      have hd := hp hs
      exact fwd_w_pos _ _ _ _ _ _ _ _ (by have := congrArg (fun n : Nat => (n : Int)) hd; push_cast at this; exact this)
        ex ey
    · rw [hs] at hx hy
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx hy
      have ex := toNat_mulSubMul _ _ _ _ h₁₂ h₂₂ x hx
      have ey := toNat_mulSubMul _ _ _ _ h₂₁ h₁₁ y hy
      have hd := hn hs
      exact fwd_w_neg _ _ _ _ _ _ _ _ (by have := congrArg (fun n : Nat => (n : Int)) hd; push_cast at this; exact this)
        ex ey
  · exact absurd h (by simp)

/-- `M S`, by `mulAddMul`. -/
def mulMatW (M : Mat2 UInt64Array) (S : WMat) : Mat2 UInt64Array :=
  ⟨trimA (mulAddMul M.m11 M.m12 S.s11 S.s21), trimA (mulAddMul M.m11 M.m12 S.s12 S.s22),
    trimA (mulAddMul M.m21 M.m22 S.s11 S.s21), trimA (mulAddMul M.m21 M.m22 S.s12 S.s22),
    M.neg != S.neg⟩

/-- The matrix of the cofactors `m` and the numbers it takes to `a` and `b`, when it is valid. -/
def tryCof (a b : UInt64Array) (m : Cofactors) : Option (WMat × UInt64Array × UInt64Array) :=
  match wmatOf m with
  | some S =>
    match applyW S a b with
    | some p => some (S, p)
    | none => none
  | none => none

/-- A step of Lehmer's algorithm, as `lehmerStep`, with its matrix. -/
def stepW (a b : UInt64Array) : Option (WMat × UInt64Array × UInt64Array) :=
  match tryCof a b (cofactors2 a b) with
  | some r => some r
  | none =>
    let w := leadWords a b
    tryCof a b (lehmerSteps w.x w.y 1 0 0 1 100)

private theorem stepW_spec (a b : UInt64Array) (r : WMat × UInt64Array × UInt64Array)
    (h : stepW a b = some r) : r.1.OK ∧
      a.toNat = r.1.s11.toNat * r.2.1.toNat + r.1.s12.toNat * r.2.2.toNat ∧
      b.toNat = r.1.s21.toNat * r.2.1.toNat + r.1.s22.toNat * r.2.2.toNat := by
  have hc : ∀ m r, tryCof a b m = some r → r.1.OK ∧
      a.toNat = r.1.s11.toNat * r.2.1.toNat + r.1.s12.toNat * r.2.2.toNat ∧
      b.toNat = r.1.s21.toNat * r.2.1.toNat + r.1.s22.toNat * r.2.2.toNat := by
    intro m r h
    unfold tryCof at h
    split at h
    · rename_i S hS
      split at h
      · rename_i p hp
        rw [Option.some.injEq] at h
        subst h
        have hok := ok_wmatOf m S hS
        exact ⟨hok, fwd_applyW S hok a b p hp⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  unfold stepW at h
  split at h
  · rename_i q hq
    rw [Option.some.injEq] at h
    subst h
    exact hc _ _ hq
  · exact hc _ _ h

/-- Whether `b ≥ βˢ` for `s > 0`, from the position of its top bit. It only affects speed. -/
def geB (b : UInt64Array) (s : Nat) : Bool :=
  0 < s && fits (b.size + 1) && 64 * s ≤ MPN.log2 b.toUSlice

/--
Half-gcd's base case of word matrices, for `NatOps.smallBase`: Lehmer's steps of 62 bits
(`stepW`) applied by `mulSubMul`, and the matrix updated by `mulAddMul` (`mulMatW`).
-/
def steps64 : ops64.SmallSteps where
  W := WMat
  e₁₁ S := S.s11.toNat
  e₁₂ S := S.s12.toNat
  e₂₁ S := S.s21.toNat
  e₂₂ S := S.s22.toNat
  neg S := S.neg
  ok S := S.OK
  step := stepW
  mulMat := mulMatW
  geB := geB
  det_of_ok _ h := ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  step_spec a b r h := by
    obtain ⟨h₁, h₂, h₃⟩ := stepW_spec a b r h
    simp only [ops64_val]
    exact ⟨h₁, h₂, h₃⟩
  mulMat_spec M S h := by
    obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, -, -⟩ := h
    simp only [mulMatW, ops64_val, toNat_trimA]
    rw [toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂,
      toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Nat.mul_comm]

/-- The base case of half-gcd: `NatOps.smallBase` with `steps64`. -/
def baseW (s : Nat) (a b : UInt64Array) : Mat2 UInt64Array × UInt64Array × UInt64Array :=
  ops64.smallBase steps64 s a b

private theorem baseW_ok (s : Nat) (a b : UInt64Array) : ops64.HgcdOK a b (baseW s a b) :=
  ops64.smallBase_ok steps64 s a b

/-- The size up to which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 128

/-- One reduction of `x ≥ y` by half-gcd (`NatOps.hgcdReduce`). -/
public def hgcd64 (x y : UInt64Array) : UInt64Array × UInt64Array :=
  ops64.hgcdReduce baseW hgcdBase x y

public theorem gcd_hgcd64 (x y : UInt64Array) :
    Nat.gcd (hgcd64 x y).1.toNat (hgcd64 x y).2.toNat = Nat.gcd x.toNat y.toNat :=
  ops64.gcd_hgcdReduce _ baseW_ok hgcdBase x y

end MPN
