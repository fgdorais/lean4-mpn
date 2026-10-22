/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import ScalarArray.UInt64
public import MPN.UInt

/-!
# Limb arrays

-/

open ScalarArray

/-! ## `UInt32Array` -/

/-! ## `UInt64Array` -/

namespace ScalarArray.UInt64Array

/--
The natural number whose little-endian base `2⁶⁴` limbs are `a[lo], …, a[lo + n - 1]`, where
the limbs past the end of `a` are zero.
-/
public def valAt (a : UInt64Array) (lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => a[lo]!.toNat + 2 ^ 64 * a.valAt (lo + 1) n

@[simp] public theorem valAt_zero (a : UInt64Array) (lo : Nat) : a.valAt lo 0 = 0 := by
  rw [valAt]

public theorem valAt_succ (a : UInt64Array) (lo n : Nat) :
    a.valAt lo (n + 1) = a[lo]!.toNat + 2 ^ 64 * a.valAt (lo + 1) n := by
  rw [valAt]

@[simp] public theorem valAt_one (a : UInt64Array) (lo : Nat) : a.valAt lo 1 = a[lo]!.toNat := by
  simp [valAt_succ]

public theorem valAt_lt (a : UInt64Array) (lo n : Nat) : a.valAt lo n < 2 ^ (64 * n) := by
  induction n generalizing lo with
  | zero => simp
  | succ n ih =>
    have h₁ := ih (lo + 1)
    have h₂ := a[lo]!.toNat_lt
    rw [valAt_succ, Nat.mul_succ, Nat.pow_add]
    generalize a.valAt _ n = v at *
    generalize 2 ^ (64 * n) = P at *
    lia

/-- `valAt` only depends on the limbs it reads. -/
public theorem valAt_congr {a b : UInt64Array} {lo : Nat} :
    (n : Nat) → (∀ i, lo ≤ i → i < lo + n → a[i]! = b[i]!) → a.valAt lo n = b.valAt lo n
  | 0, _ => by simp
  | n + 1, h => by
    rw [valAt_succ, valAt_succ, h lo (by lia) (by lia),
      valAt_congr n fun i h₁ h₂ => h i (by lia) (by lia)]

/-- Splits `valAt` into its low `m` limbs and the `k` limbs above them. -/
public theorem valAt_add (a : UInt64Array) (lo m k : Nat) :
    a.valAt lo (m + k) = a.valAt lo m + 2 ^ (64 * m) * a.valAt (lo + m) k := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, valAt_succ, valAt_succ, ih, Nat.add_assoc lo, Nat.add_comm 1 m,
      Nat.mul_succ, Nat.pow_add]
    generalize a.valAt _ m = X
    generalize a.valAt _ k = Y
    generalize 2 ^ (64 * m) = P
    grind

/-- The natural number whose little-endian base `2⁶⁴` limbs are the elements of `a`. -/
public def toNat (a : UInt64Array) : Nat := a.valAt 0 a.size

public theorem toNat_eq_valAt (a : UInt64Array) : a.toNat = a.valAt 0 a.size := by
  rw [toNat]

public theorem getElem!_eq_getElem (a : UInt64Array) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  rw [getElem!_eq_getElem!_data, getElem_eq_getElem_data]
  simp [h]

public theorem getElem!_set! (a : UInt64Array) (i j : Nat) (v : UInt64) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [getElem!_eq_getElem!_data, getElem!_eq_getElem!_data, data_set!]
  have := a.size_data
  grind

@[simp] public theorem getElem!_set!_self (a : UInt64Array) (i : Nat) (v : UInt64)
    (h : i < a.size) : (a.set! i v)[i]! = v := by
  rw [getElem!_set!]
  simp [h]

public theorem getElem!_set!_of_ne (a : UInt64Array) {i j : Nat} (v : UInt64) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [getElem!_set!]
  simp [h]

/-- The natural number whose little-endian base `2⁶⁴` limbs are the elements of `s`. -/
public def Slice.toNat (s : UInt64Array.Slice) : Nat := s.array.valAt s.start s.size

public theorem Slice.toNat_eq_valAt (s : UInt64Array.Slice) :
    s.toNat = s.array.valAt s.start s.size := by
  rw [Slice.toNat]

public theorem Slice.getElem_eq_getElem! (s : UInt64Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]! := by
  have := s.stop_le_array_size
  rw [Slice.getElem_eq, getElem!_eq_getElem _ _ (by rw [Slice.size_eq] at h; lia)]

end ScalarArray.UInt64Array
