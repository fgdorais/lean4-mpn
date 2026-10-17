/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic

/-!
# Comparison

`lt a b` decides `toNat a < toNat b` from the top limb down, like GMP's `mpn_cmp`, reading limbs
past the end of the shorter slice as `0`, so the slices may have any sizes.
-/

open ScalarArray

namespace MPN

/-- Compares the limbs of `a` and `b` below `i`, from the top down. -/
def ltLoop (a b : UInt32Array.Slice) : Nat → Bool
  | 0 => false
  | i + 1 =>
    let x := a.getD i 0
    let y := b.getD i 0
    if x < y then true else if y < x then false else ltLoop a b i

/-- Whether `a < b`, like GMP's `mpn_cmp`. The slices may have different sizes. -/
public def lt (a b : UInt32Array.Slice) : Bool := ltLoop a b (max a.size b.size)

private theorem ltLoop_iff (a b : UInt32Array.Slice) (i : Nat) :
    ltLoop a b i = true ↔
      ofLimbs (a.copy.toList.take i) < ofLimbs (b.copy.toList.take i) := by
  induction i with
  | zero => simp [ltLoop]
  | succ i ih =>
    have hx := ofLimbs_take_lt a.copy.toList i
    have hy := ofLimbs_take_lt b.copy.toList i
    rw [ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD, ← getD_eq_getD_toList_copy,
      ← getD_eq_getD_toList_copy]
    simp only [ltLoop]
    generalize ofLimbs (a.copy.toList.take i) = X at *
    generalize ofLimbs (b.copy.toList.take i) = Y at *
    generalize 2 ^ (32 * i) = P at *
    by_cases hlt : a.getD i 0 < b.getD i 0
    · have : (a.getD i 0).toNat + 1 ≤ (b.getD i 0).toNat := UInt32.lt_iff_toNat_lt.1 hlt
      have := Nat.mul_le_mul_left P this
      simp only [hlt, ↓reduceIte, true_iff]
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · by_cases hgt : b.getD i 0 < a.getD i 0
      · have : (b.getD i 0).toNat + 1 ≤ (a.getD i 0).toNat := UInt32.lt_iff_toNat_lt.1 hgt
        have := Nat.mul_le_mul_left P this
        simp only [hlt, hgt, ↓reduceIte, Bool.false_eq_true, false_iff, Nat.not_lt]
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      · have heq : a.getD i 0 = b.getD i 0 := by
          have h₁ : ¬ (a.getD i 0).toNat < (b.getD i 0).toNat :=
            fun h => hlt (UInt32.lt_iff_toNat_lt.2 h)
          have h₂ : ¬ (b.getD i 0).toNat < (a.getD i 0).toNat :=
            fun h => hgt (UInt32.lt_iff_toNat_lt.2 h)
          exact UInt32.toNat_inj.1 (by omega)
        simp only [hlt, hgt, ↓reduceIte]
        rw [ih, heq]
        omega

/-- `lt` decides `<` on the numbers. -/
public theorem lt_iff (a b : UInt32Array.Slice) : lt a b = true ↔ toNat a < toNat b := by
  rw [lt, ltLoop_iff, List.take_of_length_le (by simp; omega),
    List.take_of_length_le (by simp; omega)]
  rfl

end MPN
