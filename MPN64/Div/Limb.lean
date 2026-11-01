/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Bits
public import MPN.Div.ByLimb
public import MPN64.Mul.Karatsuba

/-!
# Division by a limb

`divRem1 r a d` writes the limbs of `a / d` into `r` and returns `a % d`, like GMP's
`mpn_divrem_1`, by `main`'s `WordArray.divRem1W`: from the top limb down, by `UInt64.div2`, or by
Möller and Granlund's step with a precomputed reciprocal, checked, from `config.div1Recip` limbs
for a normalized `d` and from `config.div1Unnorm` limbs for another, normalized by a shift.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-- The reciprocal `⌊(β² - 1) / d⌋ - β` of a normalized `d`. -/
@[inline] public def recip21 (d : UInt64) : UInt64 := WordArray.recip21 UInt64Array d

/--
Writes the limbs of `a / d` into `r` and returns `a % d`, on the first `min r.size a.size` limbs,
like GMP's `mpn_divrem_1`. It requires `0 < d`. It takes the steps with the reciprocal from `t`
limbs for a normalized `d`, and from `tu` limbs for another, normalized by a shift.
-/
public def divRem1With (t tu : USize) (r a : USlice) (d : UInt64) : UInt64Array × UInt64 :=
  WordArray.divRem1W UInt64Array t tu r.array r.start a.array a.start (min a.size r.size)
    (r.loopBound (USize.min_le_right ..)) (a.loopBound (USize.min_le_left ..)) d

@[simp] public theorem size_divRem1With (t tu : USize) (r a : USlice) (d : UInt64) :
    (divRem1With t tu r a d).1.size = r.array.size :=
  (WordArray.divRem1W_frame (A := UInt64Array) t tu r.array r.start a.array a.start _ _ _ d).1

/-- `divRem1With` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_divRem1With (t tu : USize) (r a : USlice) (d : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (divRem1With t tu r a d).1[i]! = r.array[i]! :=
  (WordArray.divRem1W_frame (A := UInt64Array) t tu r.array r.start a.array a.start _ _ _ d).2 i
    (by rw [USize.toNat_min]; exact hi)

/-- The value of the quotient and the remainder, when `r` holds all of `a`. -/
private theorem divRem1With_full (t tu : USize) (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    d.toNat * (divRem1With t tu r a d).1.valAt r.start.toNat a.size.toNat +
        (divRem1With t tu r a d).2.toNat = a.toNat ∧
      (divRem1With t tu r a d).2.toNat < d.toNat := by
  have h := USize.le_iff_toNat_le.1 har
  obtain ⟨-, -, i₃, i₄⟩ := WordArray.divRem1W_spec (A := UInt64Array) t tu r.array r.start a.array
    a.start (min a.size r.size) (r.loopBound (USize.min_le_right ..))
    (a.loopBound (USize.min_le_left ..)) d hd
  simp only [USize.toNat_min, show min a.size.toNat r.size.toNat = a.size.toNat by lia] at i₃
  exact ⟨by rw [USlice.toNat_eq_valAt]; exact i₃, i₄⟩

public theorem valAt_divRem1With (t tu : USize) (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1With t tu r a d).1.valAt r.start.toNat a.size.toNat = a.toNat / d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1With_full t tu r a d hd har
  rw [← h₁, Nat.mul_add_div hd, Nat.div_eq_of_lt h₂, Nat.add_zero]

/-- The remainder of `divRem1With` is `a % d`. -/
public theorem toNat_divRem1With_snd (t tu : USize) (r a : USlice) (d : UInt64)
    (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1With t tu r a d).2.toNat = a.toNat % d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1With_full t tu r a d hd har
  rw [← h₁, Nat.mul_add_mod, Nat.mod_eq_of_lt h₂]

/-- `config.div1Recip` as a `USize`, at most `2³² - 1`. -/
public def div1RecipU : USize := (min config.div1Recip 4294967295).toUSize

/-- `config.div1Unnorm` as a `USize`, at most `2³² - 1`. -/
public def div1UnnormU : USize := (min config.div1Unnorm 4294967295).toUSize

/--
`divRem1With` with the steps with the reciprocal from `config.div1Recip` limbs for a normalized
divisor and from `config.div1Unnorm` for another.
-/
public def divRem1 (r a : USlice) (d : UInt64) : UInt64Array × UInt64 :=
  divRem1With div1RecipU div1UnnormU r a d

@[simp] public theorem size_divRem1 (r a : USlice) (d : UInt64) :
    (divRem1 r a d).1.size = r.array.size := size_divRem1With ..

/-- `divRem1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_divRem1 (r a : USlice) (d : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (divRem1 r a d).1[i]! = r.array[i]! := getElem!_divRem1With _ _ r a d i hi

public theorem valAt_divRem1 (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1 r a d).1.valAt r.start.toNat a.size.toNat = a.toNat / d.toNat :=
  valAt_divRem1With _ _ r a d hd har

/-- The remainder of `divRem1` is `a % d`. -/
public theorem toNat_divRem1_snd (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1 r a d).2.toNat = a.toNat % d.toNat :=
  toNat_divRem1With_snd _ _ r a d hd har

end MPN.W64
