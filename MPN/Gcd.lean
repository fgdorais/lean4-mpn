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

* Lehmer's algorithm (`gcdLehmer`): two runs of Euclid's steps on the leading words of the two
  numbers (`cofactors2`, with `lehmerSteps` in `Int64`) give cofactors of about 62 bits, which are
  checked on words (`applyCof`: determinant `±1`) and applied to the full numbers in one pass each
  (`mulSubMul`); when they do not apply or do not make the numbers smaller, one step of Euclid's
  algorithm is taken instead. Nothing about the steps on the words needs a proof: a matrix of
  determinant `±1` keeps the greatest common divisor.
* Euclid's algorithm on pairs of words (`gcd2`, like GMP's `mpn_gcd_22`) once both numbers have at
  most two limbs.
* Half-gcd (`NatOps.hgcdReduce`) from `gcdHalf` limbs, whose base case up to `hgcdBase` limbs is
  the same steps with their matrix kept up to date in one pass per entry (`baseW`, `mulAddMul`).
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
`applyCof` and `wmatOf` check the cofactors, and the caller that the numbers got smaller.
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

/-! ## Two words -/

/-- The number `h β + l`. -/
def v2 (h l : UInt64) : Nat := h.toNat * 2 ^ 64 + l.toNat

/-- `(ah β + al) - (bh β + bl)` in two words. -/
@[inline] def sub2h (ah al bh bl : UInt64) : UInt64 := ah - bh - (if al < bl then 1 else 0)

private theorem toNat_sub_add (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat + (if a.toNat < b.toNat then 2 ^ 64 else 0) := by
  rw [UInt64.toNat_sub]
  have := a.toNat_lt; have := b.toNat_lt
  split
  · rw [Nat.mod_eq_of_lt (by lia)]; lia
  · rw [show 2 ^ 64 - b.toNat + a.toNat = a.toNat - b.toNat + 2 ^ 64 by lia, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by lia)]
    lia

private theorem v2_sub (ah al bh bl : UInt64) (h : v2 bh bl ≤ v2 ah al) :
    v2 (sub2h ah al bh bl) (al - bl) = v2 ah al - v2 bh bl := by
  unfold v2 sub2h at *
  have := al.toNat_lt; have := bl.toNat_lt; have := ah.toNat_lt; have := bh.toNat_lt
  have := (ah - bh).toNat_lt; have := (al - bl).toNat_lt
  have e₁ := toNat_sub_add al bl
  have e₂ := toNat_sub_add ah bh
  have e₃ := toNat_sub_add (ah - bh) (if al < bl then 1 else 0)
  have := (ah - bh - if al < bl then 1 else 0).toNat_lt
  generalize ah - bh - (if al < bl then 1 else 0) = t at *
  by_cases hl : al < bl
  · have hl' := UInt64.lt_iff_toNat_lt.1 hl
    simp only [hl, hl', ↓reduceIte, UInt64.toNat_one] at e₁ e₃
    split at e₃ <;> lia
  · have hl' := mt UInt64.lt_iff_toNat_lt.2 hl
    simp only [hl, hl', ↓reduceIte, UInt64.toNat_zero] at e₁ e₃
    split at e₃ <;> lia

/-- Whether `ah β + al < bh β + bl`. -/
@[inline] def lt2 (ah al bh bl : UInt64) : Bool := ah < bh || (ah == bh && al < bl)

private theorem lt2_iff (ah al bh bl : UInt64) : lt2 ah al bh bl = true ↔ v2 ah al < v2 bh bl := by
  unfold lt2 v2
  have := al.toNat_lt; have := bl.toNat_lt
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  constructor
  · rintro (h | ⟨h₁, h₂⟩) <;> lia
  · intro h
    rcases Nat.lt_or_ge ah.toNat bh.toNat with h' | h'
    · exact .inl h'
    · exact .inr ⟨by lia, by lia⟩

/-- The quotient estimate of a step: `⌊ah / (bh + 1)⌋`, at least `1`. -/
@[inline] def q2 (ah bh : UInt64) : UInt64 := let q := ah / (bh + 1); if q = 0 then 1 else q

private theorem q2_mul_le (ah al bh bl : UInt64) (h : v2 bh bl ≤ v2 ah al) :
    (q2 ah bh).toNat * v2 bh bl ≤ v2 ah al ∧ 1 ≤ (q2 ah bh).toNat := by
  unfold q2
  dsimp only
  split
  · simp only [UInt64.toNat_one]; lia
  · rename_i hq
    have hq' : (ah / (bh + 1)).toNat ≠ 0 := fun e => hq (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [UInt64.toNat_div] at hq' ⊢
    have hb1 : (bh + 1).toNat = bh.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]
      rcases Nat.lt_or_ge (bh.toNat + 1) (2 ^ 64) with e | e
      · exact Nat.mod_eq_of_lt e
      · exfalso; apply hq'
        rw [UInt64.toNat_add, UInt64.toNat_one, show bh.toNat + 1 = 2 ^ 64 by have := bh.toNat_lt; lia]
        simp
    rw [hb1] at hq' ⊢
    have hd := Nat.div_mul_le_self ah.toNat (bh.toNat + 1)
    have := bl.toNat_lt
    unfold v2
    constructor
    · have : ah.toNat / (bh.toNat + 1) * (bh.toNat * 2 ^ 64 + bl.toNat) ≤
          ah.toNat / (bh.toNat + 1) * ((bh.toNat + 1) * 2 ^ 64) :=
        Nat.mul_le_mul_left _ (by lia)
      have : ah.toNat / (bh.toNat + 1) * ((bh.toNat + 1) * 2 ^ 64) ≤ ah.toNat * 2 ^ 64 := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hd
      lia
    · lia

/-- The high word of `q (bh β + bl)`. -/
@[inline] def mul2h (q bh bl : UInt64) : UInt64 := q * bh + UInt64.mulh q bl

private theorem v2_mul (q bh bl : UInt64) (h : q.toNat * v2 bh bl < 2 ^ 128) :
    v2 (mul2h q bh bl) (q * bl) = q.toNat * v2 bh bl := by
  unfold v2 mul2h at *
  have hm := Nat.div_add_mod (q.toNat * bl.toNat) (2 ^ 64)
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mulh, UInt64.toNat_mul]
  have : q.toNat * bh.toNat * 2 ^ 64 + q.toNat * bl.toNat < 2 ^ 128 := by
    rw [Nat.mul_add, ← Nat.mul_assoc] at h; exact h
  have : q.toNat * bh.toNat < 2 ^ 64 := by
    rcases Nat.lt_or_ge (q.toNat * bh.toNat) (2 ^ 64) with e | e
    · exact e
    · exfalso
      have := Nat.mul_le_mul_right (2 ^ 64) e
      lia
  rw [Nat.mod_eq_of_lt (a := q.toNat * bh.toNat) this]
  have : q.toNat * bh.toNat + q.toNat * bl.toNat / 2 ^ 64 < 2 ^ 64 := by
    rcases Nat.lt_or_ge (q.toNat * bh.toNat + q.toNat * bl.toNat / 2 ^ 64) (2 ^ 64) with e | e
    · exact e
    · exfalso
      have := Nat.mul_le_mul_right (2 ^ 64) e
      lia
  rw [Nat.mod_eq_of_lt this]
  lia

/-- A step of `gcd2`: `a = (a - q b) + q b` with `q ≥ 1`. -/
private theorem v2_step (ah al bh bl : UInt64) (h : ¬lt2 ah al bh bl = true) :
    v2 (sub2h ah al (mul2h (q2 ah bh) bh bl) (q2 ah bh * bl)) (al - q2 ah bh * bl) +
      (q2 ah bh).toNat * v2 bh bl = v2 ah al ∧ 1 ≤ (q2 ah bh).toNat := by
  rw [lt2_iff] at h
  have hle : v2 bh bl ≤ v2 ah al := Nat.le_of_not_lt h
  obtain ⟨hq, h1⟩ := q2_mul_le ah al bh bl hle
  have h128 : v2 ah al < 2 ^ 128 := by
    unfold v2; have := ah.toNat_lt; have := al.toNat_lt; lia
  have hm := v2_mul (q2 ah bh) bh bl (Nat.lt_of_le_of_lt hq h128)
  have hq' : v2 (mul2h (q2 ah bh) bh bl) (q2 ah bh * bl) ≤ v2 ah al := by rw [hm]; exact hq
  rw [v2_sub _ _ _ _ hq', hm]
  exact ⟨Nat.sub_add_cancel hq, h1⟩

/--
The greatest common divisor of `ah β + al` and `bh β + bl` by Euclid's algorithm on pairs of words,
like GMP's `mpn_gcd_22`: steps `a - q b` with the estimate `q2` of the quotient, which is never too
large, until `b` fits in a word, then one remainder by `UInt64.div2` and `wordGcd`.
-/
def gcd2 (ah al bh bl : UInt64) : UInt64Array :=
  if bh = 0 then
    if bl = 0 then (UInt64Array.replicate 2 al).set! 1 ah
    else UInt64Array.replicate 1 (wordGcd bl (al - UInt64.div2 (ah % bl) al bl * bl))
  else if _h : lt2 ah al bh bl then gcd2 bh bl ah al
  else
    let q := q2 ah bh
    gcd2 bh bl (sub2h ah al (mul2h q bh bl) (q * bl)) (al - q * bl)
termination_by v2 ah al + v2 bh bl + (if v2 ah al < v2 bh bl then 1 else 0)
decreasing_by
  · rw [lt2_iff] at _h
    generalize v2 ah al = A at *
    generalize v2 bh bl = B at *
    split <;> (try split) <;> lia
  · rename_i hb
    obtain ⟨e, h1⟩ := v2_step ah al bh bl _h
    have hpos : 2 ^ 64 ≤ v2 bh bl := by
      have : bh.toNat ≠ 0 := fun e => hb (UInt64.toNat_inj.1 (by rw [e]; rfl))
      unfold v2; lia
    have hb1 : v2 bh bl ≤ (q2 ah bh).toNat * v2 bh bl := Nat.le_mul_of_pos_left _ h1
    rw [lt2_iff] at _h
    generalize v2 (sub2h ah al (mul2h (q2 ah bh) bh bl) (q2 ah bh * bl)) (al - q2 ah bh * bl) = R at *
    generalize v2 ah al = A at *
    generalize v2 bh bl = B at *
    generalize (q2 ah bh).toNat * B = P at *
    split <;> lia

private theorem toNat_pair (h l : UInt64) :
    ((UInt64Array.replicate 2 l).set! 1 h).toNat = v2 h l := by
  simp [toNat_eq_valAt, valAt_succ, v2]
  lia

private theorem toNat_gcd2 (ah al bh bl : UInt64) :
    (gcd2 ah al bh bl).toNat = Nat.gcd (v2 ah al) (v2 bh bl) := by
  induction ah, al, bh, bl using gcd2.induct with
  | case1 ah al =>
    rw [gcd2, ite_eq_left rfl, ite_eq_left rfl, toNat_pair]
    simp [v2]
  | case2 ah al bl hl =>
    rw [gcd2, ite_eq_left rfl, ite_eq_right hl]
    have hl' : 0 < bl.toNat := Nat.pos_of_ne_zero fun e => hl (UInt64.toNat_inj.1 (by rw [e]; rfl))
    have hr := (UInt64.toNat_div2_rem (ah % bl) al bl
      (by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ hl')).1
    simp only [toNat_eq_valAt, UInt64Array.size_replicate, valAt_one]
    simp only [show v2 0 bl = bl.toNat by simp [v2]]
    rw [show (UInt64Array.replicate 1 (wordGcd bl (al - UInt64.div2 (ah % bl) al bl * bl)))[0]! =
      wordGcd bl (al - UInt64.div2 (ah % bl) al bl * bl) by simp, toNat_wordGcd, hr,
      UInt64.toNat_mod, show (ah.toNat % bl.toNat * 2 ^ 64 + al.toNat) % bl.toNat =
        v2 ah al % bl.toNat by unfold v2; simp [Nat.add_mod, Nat.mul_mod],
      Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
  | case3 ah al bh bl hb h ih =>
    rw [gcd2, ite_eq_right hb, dite_eq_left h, ih, Nat.gcd_comm]
  | case4 ah al bh bl hb h q ih =>
    simp only [q] at ih
    rw [gcd2, ite_eq_right hb, dite_eq_right h, ih]
    obtain ⟨e, -⟩ := v2_step ah al bh bl h
    rw [← e, Nat.gcd_comm (_ + _), Nat.gcd_add_mul_right_right]

private theorem toNat_small (x : UInt64Array) (h : x.size ≤ 1) :
    x.toNat = (Num.limbAt x 0).toNat := by
  rw [toNat_eq_valAt, Num.limbAt_eq]
  rcases Nat.lt_or_ge x.size 1 with h0 | h0
  · rw [show x.size = 0 by lia, valAt_zero, getElem!_neg x 0 (by lia)]; rfl
  · rw [show x.size = 1 by lia, valAt_one]

private theorem toNat_small2 (x : UInt64Array) (h : x.size ≤ 2) :
    x.toNat = v2 (Num.limbAt x 1) (Num.limbAt x 0) := by
  rw [Num.limbAt_eq, Num.limbAt_eq, v2]
  rcases Nat.lt_or_ge x.size 2 with h1 | h1
  · rw [toNat_small x (by lia), Num.limbAt_eq, getElem!_neg x 1 (by lia)]
    change _ = 0 * 2 ^ 64 + _
    lia
  · rw [toNat_eq_valAt, show x.size = 2 by lia, valAt_succ, valAt_one]
    lia

/--
The greatest common divisor by Lehmer's algorithm: Lehmer's step on the leading words, applied to
the full numbers when it is valid and makes them smaller, and otherwise one step of Euclid's
algorithm; on words when both numbers have at most one limb, and on pairs of words (`gcd2`) when
they have at most two.
-/
public def gcdLehmer (x y : UInt64Array) : UInt64Array :=
  if x.size ≤ 1 ∧ y.size ≤ 1 then
    UInt64Array.replicate 1 (wordGcd (Num.limbAt x 0) (Num.limbAt y 0))
  else if x.size ≤ 2 ∧ y.size ≤ 2 then
    gcd2 (Num.limbAt x 1) (Num.limbAt x 0) (Num.limbAt y 1) (Num.limbAt y 0)
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
  | case2 x y hs hs2 =>
    rw [gcdLehmer, ite_eq_right hs, ite_eq_left hs2, toNat_gcd2, ← toNat_small2 x hs2.1,
      ← toNat_small2 y hs2.2]
  | case3 x y hs hs2 h =>
    rw [gcdLehmer, ite_eq_right hs, ite_eq_right hs2, dite_eq_left_of_eq_true (eq_true h)]
    rw [ops64.le_iff] at h
    simp only [ops64_val, toNat_zeroA] at h
    rw [show y.toNat = 0 by lia, Nat.gcd_zero_right]
  | case4 x y hs hs2 h hlt ih =>
    rw [gcdLehmer, ite_eq_right hs, ite_eq_right hs2, dite_eq_right h, ite_eq_left hlt, ih,
      gcd_mod_step _ _ (ne_zero_of y h)]
  | case5 x y hs hs2 h hlt p hp hy ih =>
    rw [gcdLehmer, ite_eq_right hs, ite_eq_right hs2, dite_eq_right h, ite_eq_right hlt]
    simp only [hp, dite_eq_left_of_eq_true (eq_true hy), ih]
    exact gcd_lehmerStep x y p hp
  | case6 x y hs hs2 h hlt p hp hy ih =>
    rw [gcdLehmer, ite_eq_right hs, ite_eq_right hs2, dite_eq_right h, ite_eq_right hlt]
    simp only [hp, dite_eq_right_of_eq_false (eq_false hy), ih,
      gcd_mod_step _ _ (ne_zero_of y h)]
  | case7 x y hs hs2 h hlt hp ih =>
    rw [gcdLehmer, ite_eq_right hs, ite_eq_right hs2, dite_eq_right h, ite_eq_right hlt]
    simp only [hp, ih, gcd_mod_step _ _ (ne_zero_of y h)]

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

private theorem det_mulW (a b c d e f g h : Int) :
    (e * a + g * b) * (f * c + h * d) - (f * a + h * b) * (e * c + g * d) =
      (a * d - b * c) * (e * h - f * g) := by
  grind

private theorem unimodular_mulMatW (M : Mat2 UInt64Array) (S : WMat) (hM : ops64.Unimodular M)
    (hS : S.OK) : ops64.Unimodular (mulMatW M S) := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, hp, hn⟩ := hS
  unfold NatOps.Unimodular at *
  simp only [mulMatW, ops64_val, toNat_trimA] at *
  rw [toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂,
    toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂]
  push_cast
  have e := det_mulW M.m11.toNat M.m12.toNat M.m21.toNat M.m22.toNat S.s11.toNat S.s12.toNat
    S.s21.toNat S.s22.toNat
  have hS : (S.s11.toNat * S.s22.toNat - S.s12.toNat * S.s21.toNat : Int) =
      if S.neg then -1 else 1 := by
    cases hs : S.neg
    · have := hp hs
      have : ((S.s11.toNat * S.s22.toNat : Nat) : Int) = ((S.s12.toNat * S.s21.toNat + 1 : Nat) : Int) := by
        rw [this]
      push_cast at this; simp; lia
    · have := hn hs
      have : ((S.s12.toNat * S.s21.toNat : Nat) : Int) = ((S.s11.toNat * S.s22.toNat + 1 : Nat) : Int) := by
        rw [this]
      push_cast at this; simp; lia
  rw [e, hM, hS]
  rcases Bool.eq_false_or_eq_true M.neg with h | h <;>
    rcases Bool.eq_false_or_eq_true S.neg with h' | h' <;> simp [h, h']

private theorem fwd_mulMatW (M : Mat2 UInt64Array) (S : WMat) (hS : S.OK)
    (a₀ b₀ a b x y : UInt64Array) (hF : ops64.Fwd M a₀ b₀ a b)
    (ha : a.toNat = S.s11.toNat * x.toNat + S.s12.toNat * y.toNat)
    (hb : b.toNat = S.s21.toNat * x.toNat + S.s22.toNat * y.toNat) :
    ops64.Fwd (mulMatW M S) a₀ b₀ x y := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, -, -⟩ := hS
  unfold NatOps.Fwd at *
  simp only [mulMatW, ops64_val, toNat_trimA] at *
  rw [toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂,
    toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂, hF.1, hF.2, ha, hb]
  constructor <;> grind

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
Lehmer's steps (`stepW`) while `b ≥ βˢ` and they make the numbers smaller, at most `fuel` of them,
with the product of their matrices (`mulMatW`).
-/
def baseLoopW (s : Nat) (a b : UInt64Array) (M : Mat2 UInt64Array) :
    Nat → Mat2 UInt64Array × UInt64Array × UInt64Array
  | 0 => (M, a, b)
  | fuel + 1 =>
    if geB b s then
      match stepW a b with
      | none => (M, a, b)
      | some r =>
        if ops64.le r.2.2 r.2.1 ∧ !(ops64.le b r.2.2) then
          baseLoopW s r.2.1 r.2.2 (mulMatW M r.1) fuel
        else (M, a, b)
    else (M, a, b)

private theorem baseLoopW_ok (s : Nat) (a₀ b₀ : UInt64Array) :
    ∀ fuel (a b : UInt64Array) (M : Mat2 UInt64Array), ops64.Unimodular M →
      ops64.Fwd M a₀ b₀ a b → ops64.HgcdOK a₀ b₀ (baseLoopW s a b M fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a b M hM hF; exact ⟨hM, hF⟩
  | succ fuel ih =>
    intro a b M hM hF
    simp only [baseLoopW]
    split
    · split
      · exact ⟨hM, hF⟩
      · rename_i r hr
        obtain ⟨hS, ha, hb⟩ := stepW_spec a b r hr
        split
        · exact ih _ _ _ (unimodular_mulMatW M r.1 hM hS)
            (fwd_mulMatW M r.1 hS a₀ b₀ a b _ _ hF ha hb)
        · exact ⟨hM, hF⟩
    · exact ⟨hM, hF⟩

/-- The base case of half-gcd: `baseLoopW` from the identity. -/
def baseW (s : Nat) (a b : UInt64Array) : Mat2 UInt64Array × UInt64Array × UInt64Array :=
  baseLoopW s a b ops64.matId (4 * a.size + 4)

private theorem baseW_ok (s : Nat) (a b : UInt64Array) : ops64.HgcdOK a b (baseW s a b) :=
  baseLoopW_ok s a b _ a b _ ops64.unimodular_matId (ops64.fwd_matId a b)

/-- The size up to which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 128

/-- One reduction by half-gcd (`NatOps.hgcdReduce`), on the larger number first. -/
def hgcdOrd (x y : UInt64Array) : UInt64Array × UInt64Array :=
  if ops64.le y x then ops64.hgcdReduce baseW hgcdBase x y
  else ops64.hgcdReduce baseW hgcdBase y x

private theorem gcd_hgcdOrd (x y : UInt64Array) :
    Nat.gcd (hgcdOrd x y).1.toNat (hgcdOrd x y).2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold hgcdOrd
  split
  · exact ops64.gcd_hgcdReduce _ baseW_ok hgcdBase x y
  · have := ops64.gcd_hgcdReduce _ baseW_ok hgcdBase y x
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
public def gcdHalf : Nat := 1024

/-- `Nat.gcd a.toNat b.toNat`. -/
public def Num.gcd (a b : UInt64Array) : UInt64Array := gcdWith gcdHalf a b

@[simp] public theorem Num.toNat_gcd (a b : UInt64Array) :
    (Num.gcd a b).toNat = Nat.gcd a.toNat b.toNat :=
  toNat_gcdWith ..

end MPN
