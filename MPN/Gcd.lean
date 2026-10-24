/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.HGCD
public import MPN.Generic.Ops64

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
  let A := m.A.toInt.natAbs
  let B := m.B.toInt.natAbs
  let C := m.C.toInt.natAbs
  let D := m.D.toInt.natAbs
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

/-- `x mod y`. -/
def modN (x y : UInt64Array) : UInt64Array := (ops64.divRem x y).2

private theorem toNat_modN (x y : UInt64Array) (hy : y.toNat ≠ 0) :
    (modN x y).toNat = x.toNat % y.toNat :=
  (ops64.val_divRem x y hy).2

/--
The greatest common divisor by Lehmer's algorithm: a matrix of Euclid's steps on the leading words,
applied to the full numbers when that is exact and makes them smaller, and otherwise one step of
Euclid's algorithm.
-/
public def gcdLehmer (x y : UInt64Array) : UInt64Array :=
  if _h : ops64.le y ops64.zero = true then x
  else if ops64.le y x = false then gcdLehmer y (modN x y)
  else
    match lehmerMat x y with
    | some M =>
      match ops64.applyInvC M x y with
      | some p => if _hy : ops64.le y p.2 = false then gcdLehmer p.1 p.2 else gcdLehmer y (modN x y)
      | none => gcdLehmer y (modN x y)
    | none => gcdLehmer y (modN x y)
termination_by y.toNat
decreasing_by
  all_goals first
    | (rw [← Bool.not_eq_true, ops64.le_iff] at _hy; simp only [ops64_val] at _hy; lia)
    | (rw [ops64.le_iff, ops64.val_zero] at _h
       simp only [ops64_val] at _h
       rw [toNat_modN _ _ (by lia)]
       exact Nat.mod_lt _ (by lia))

private theorem ne_zero_of (y : UInt64Array) (h : ¬ops64.le y ops64.zero = true) :
    y.toNat ≠ 0 := by
  rw [ops64.le_iff, ops64.val_zero] at h
  simp only [ops64_val] at h
  lia

private theorem gcd_mod_step (x y : UInt64Array) (hy : y.toNat ≠ 0) :
    Nat.gcd y.toNat (modN x y).toNat = Nat.gcd x.toNat y.toNat := by
  rw [toNat_modN _ _ hy, Nat.gcd_comm x.toNat y.toNat, Nat.gcd_rec y.toNat x.toNat, Nat.gcd_comm]

public theorem toNat_gcdLehmer (x y : UInt64Array) :
    (gcdLehmer x y).toNat = Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdLehmer.induct with
  | case1 x y h =>
    rw [gcdLehmer, dite_eq_left_of_eq_true (eq_true h)]
    rw [ops64.le_iff, ops64.val_zero] at h
    simp only [ops64_val] at h
    rw [show y.toNat = 0 by lia, Nat.gcd_zero_right]
  | case2 x y h hlt ih =>
    rw [gcdLehmer, dite_eq_right h, ite_eq_left hlt, ih, gcd_mod_step _ _ (ne_zero_of y h)]
  | case3 x y h hlt M hM p hp hy ih =>
    rw [gcdLehmer, dite_eq_right h, ite_eq_right hlt]
    simp only [hM, hp, dite_eq_left_of_eq_true (eq_true hy), ih]
    have := ops64.gcd_of_fwd M (unimodular_lehmerMat x y M hM) x y p.1 p.2
      (ops64.fwd_applyInvC M (unimodular_lehmerMat x y M hM) x y p hp)
    simp only [ops64_val] at this
    exact this.symm
  | case4 x y h hlt M hM p hp hy ih =>
    rw [gcdLehmer, dite_eq_right h, ite_eq_right hlt]
    simp only [hM, hp, dite_eq_right_of_eq_false (eq_false hy), ih,
      gcd_mod_step _ _ (ne_zero_of y h)]
  | case5 x y h hlt M hM hp ih =>
    rw [gcdLehmer, dite_eq_right h, ite_eq_right hlt]
    simp only [hM, hp, ih, gcd_mod_step _ _ (ne_zero_of y h)]
  | case6 x y h hlt hM ih =>
    rw [gcdLehmer, dite_eq_right h, ite_eq_right hlt]
    simp only [hM, ih, gcd_mod_step _ _ (ne_zero_of y h)]

/-! ## Half-gcd -/

/-- The size below which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 8

/-- One reduction by half-gcd (`NatOps.hgcdReduce`), on the larger number first. -/
def hgcdOrd (x y : UInt64Array) : UInt64Array × UInt64Array :=
  if ops64.le y x then ops64.hgcdReduce lehmerMat hgcdBase x y
  else ops64.hgcdReduce lehmerMat hgcdBase y x

private theorem gcd_hgcdOrd (x y : UInt64Array) :
    Nat.gcd (hgcdOrd x y).1.toNat (hgcdOrd x y).2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold hgcdOrd
  split
  · exact ops64.gcd_hgcdReduce lehmerMat unimodular_lehmerMat hgcdBase x y
  · have := ops64.gcd_hgcdReduce lehmerMat unimodular_lehmerMat hgcdBase y x
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
public def gcdHalf : Nat := 2304

/-- `Nat.gcd a.toNat b.toNat`. -/
public def Num.gcd (a b : UInt64Array) : UInt64Array := gcdWith gcdHalf a b

@[simp] public theorem Num.toNat_gcd (a b : UInt64Array) :
    (Num.gcd a b).toNat = Nat.gcd a.toNat b.toNat :=
  toNat_gcdWith ..

end MPN
