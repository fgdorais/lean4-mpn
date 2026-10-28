/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic
public import MPN.UIntArray

/-!
# Values of the library's slices by `valAt`

`MPN.toNat` of a library slice or an array is `valAt` of its range of limbs, for the parts that
work on windows of arrays: the FFT and the instance of the Toom methods.
-/

open ScalarArray UInt32Array

namespace MPN

/-- The limbs `lo` to `lo + n - 1` of `a`, read as a list, have the value `valAt`. -/
public theorem ofLimbs_drop_take (a : UInt32Array) (lo n : Nat) :
    ofLimbs ((a.toList.drop lo).take n) = a.valAt lo n := by
  have hz : ∀ m lo', a.size ≤ lo' → a.valAt lo' m = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      intro lo' h'
      rw [valAt_succ, ihm (lo' + 1) (by lia), getElem!_neg a lo' (by lia)]; rfl
  induction n generalizing lo with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge lo a.size with h | h
    · rw [valAt_succ, List.drop_eq_getElem_cons (by simpa using h), List.take_succ_cons,
        ofLimbs_cons, ih (lo + 1), getElem!_eq_getElem _ _ h]
      simp
    · rw [List.drop_eq_nil_of_le (by simpa using h), hz _ lo h]
      simp

/-- The value of a library slice, by `valAt`. -/
public theorem toNat_eq_valAt (s : UInt32Array.Slice) :
    MPN.toNat s = s.array.valAt s.start s.size := by
  rw [MPN.toNat, ← ofLimbs_drop_take]
  congr 1
  rw [UInt32Array.Slice.copy, UInt32Array.toList_extract, List.extract_eq_take_drop,
    UInt32Array.Slice.size_eq]

/-- The value of an array, by `valAt`. -/
public theorem toNat_array_eq_valAt (a : UInt32Array) :
    MPN.toNat a.toSlice = a.valAt 0 a.size := by
  rw [toNat_toSlice, ← ofLimbs_drop_take, List.drop_zero, List.take_of_length_le (by simp)]

end MPN
