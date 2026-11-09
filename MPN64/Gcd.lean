/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.HGCD
public import MPN64.Generic.Ops64
public import MPN64.Arch.LinComb
public import MPN.WordGcd
public import MPN.LehmerStep

/-!
# Greatest common divisor

The parts of the greatest common divisor that depend on 64-bit limbs, for `main`'s `GNat.gcd`
(`MPN.NatGcd`, with the instance in `MPN.Nat`), ported from `main`:

* the cofactors of Lehmer's step (`lehmer64`, for `main`'s `LehmerStep`): two runs of Euclid's
  steps on the leading words of the two numbers (`cofactors2`, with `lehmerSteps` in `Int64`), or
  one run when those do not apply, give cofactors of about 62 bits, which are checked on words
  (`wmatOf`: entries below `2⁶²`, determinant `±1`); `LehmerStep` applies them to the full numbers
  in one pass each (`mulSubMul`). Nothing about the steps on the words needs a proof: a matrix of
  determinant `±1` keeps the greatest common divisor.
* Half-gcd (`NatOps.hgcdReduceP`, `hgcd64`), whose base case up to `hgcdBase` limbs is the same
  steps with their matrix kept up to date in one pass per entry (`LehmerStep.smallSteps`,
  `mulAddMul`).
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Lehmer's steps on words

`lehmerSteps`, with its `Cofactors`, and `LeadWords` are in `MPN.WordGcd`.
-/

/--
The leading 62 bits of `a`, from its top nonzero limb, and the bits of `b` at the same positions,
as the words of Lehmer's algorithm. Their values only affect its speed.
-/
public def leadWords (a b : UInt64Array) : LeadWords :=
  let L := MPN.W64.log2 a.toUSlice
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
  let L := MPN.W64.log2 a.toUSlice
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
public def cofactors2 (x y : UInt64Array) : Cofactors :=
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

/-- A `2 × 2` matrix of words below `2⁶²`, and the sign of its determinant, with unboxed fields. -/
public structure WMat where
  s11 : UInt64
  s12 : UInt64
  s21 : UInt64
  s22 : UInt64
  neg : Bool

/--
The matrix `[[|D|, |B|], [|C|, |A|]]` of the cofactors `m`, whose `S⁻¹ (a, b)` is
`(|A a + B b|, |C a + D b|)`, when its entries are below `2⁶²` and its determinant is `±1`, checked
on words.
-/
@[inline] public def wmatOf (m : Cofactors) : Option WMat :=
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

public theorem ok_wmatOf (m : Cofactors) (S : WMat) (h : wmatOf m = some S) :
    LehmerStep.OK UInt64Array S.s11 S.s12 S.s21 S.s22 S.neg := by
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

/-- Whether `b ≥ βˢ` for `s > 0`, from the position of its top bit. It only affects speed. -/
def geB (b : UInt64Array) (s : Nat) : Bool :=
  0 < s && fits (b.size + 1) && 64 * s ≤ MPN.W64.log2 b.toUSlice

/-- The value of an array, as `LehmerStep` reads it. -/
public theorem vA_eq (x : UInt64Array) : LehmerStep.vA x = x.toNat := (toNat_eq_valAt x).symm

/--
Lehmer's step on 64-bit limbs for `main`'s `LehmerStep`: the cofactors of two runs on the leading
words (`cofactors2`), or of one run when those do not apply, checked by `wmatOf`.
-/
public instance lehmer64 : LehmerOps UInt64Array UInt64 where
  trim := trimA
  vA_trim a := by rw [vA_eq, vA_eq, toNat_trimA]
  trimmed a := decide (a.size ≤ 1) || a[a.size - 1]! != 0
  trimmed_trim a := by
    rcases trimA_trimmed a with h | h
    · simp [h]
    · simp [h]
  W := WMat
  s11 := WMat.s11
  s12 := WMat.s12
  s21 := WMat.s21
  s22 := WMat.s22
  neg := WMat.neg
  wmat := wmatOf
  ok_wmat := ok_wmatOf
  cof₁ := cofactors2
  cof₂ a b := let w := leadWords a b; lehmerSteps w.x w.y 1 0 0 1 100
  two := true

/--
Half-gcd's base case of word matrices, for `NatOps.smallBase`: `main`'s `LehmerStep.smallSteps`
on the arrays themselves.
-/
public def steps64 : ops64.SmallSteps :=
  LehmerStep.smallSteps ops64 id id (fun x => by rw [ops64_val, id, vA_eq])
    (fun a => by rw [ops64_val, id, vA_eq]) geB

/-- The base case of half-gcd: `NatOps.smallBase` with `steps64`. -/
public def baseW (s : Nat) (a b : UInt64Array) : Mat2 UInt64Array × UInt64Array × UInt64Array :=
  ops64.smallBase steps64 s a b

public theorem baseW_ok (s : Nat) (a b : UInt64Array) : ops64.HgcdOK a b (baseW s a b) :=
  ops64.smallBase_ok steps64 s a b

/-- The size up to which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 128

end MPN.W64
