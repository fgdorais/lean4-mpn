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

/-! ### `USize` arithmetic -/

/-- `USize` addition that does not overflow. -/
public theorem _root_.USize.toNat_add_of_lt {a b : USize} (h : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

public theorem _root_.USize.toNat_min (a b : USize) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  have := @USize.le_iff_toNat_le a b
  split <;> lia

public theorem _root_.USize.min_le_left (a b : USize) : min a b ≤ a :=
  USize.le_iff_toNat_le.2 (by rw [USize.toNat_min]; lia)

public theorem _root_.USize.min_le_right (a b : USize) : min a b ≤ b :=
  USize.le_iff_toNat_le.2 (by rw [USize.toNat_min]; lia)

public theorem getElem!_uset (a : UInt64Array) (i : USize) (v : UInt64) (h : i.toNat < a.size)
    (j : Nat) : (a.uset i v h)[j]! = if i.toNat = j then v else a[j]! := by
  rw [getElem!_eq_getElem!_data, getElem!_eq_getElem!_data, data_uset]
  have := a.size_data
  grind

/-! ### Slices with `USize` bounds -/

/--
A region of a `UInt64Array` with `USize` bounds: the elements from index `start` up to, but not
including, `stop`. Since `stop` is a `USize`, so is every index of the region, and indexing it
needs no `Nat` arithmetic.
-/
public structure USlice where
  /-- The underlying array. -/
  array : UInt64Array
  /-- The starting index of the slice (inclusive). -/
  start : USize
  /-- The ending index of the slice (exclusive). -/
  stop : USize
  /-- The starting index is no later than the ending index. -/
  start_le_stop : start ≤ stop
  /-- The ending index is no later than the end of the array. -/
  stop_le_size : stop.toNat ≤ array.size

namespace USlice

/-- The number of elements of the slice. -/
@[inline, expose] public def size (s : USlice) : USize := s.stop - s.start

public theorem toNat_size (s : USlice) : s.size.toNat = s.stop.toNat - s.start.toNat :=
  USize.toNat_sub_of_le _ _ s.start_le_stop

/-- The index in the array of element `i` of the slice. -/
public theorem toNat_start_add (s : USlice) {i : USize} (h : i < s.size) :
    (s.start + i).toNat = s.start.toNat + i.toNat := by
  have := s.toNat_size
  have := USize.lt_iff_toNat_lt.1 h
  have := USize.le_iff_toNat_le.1 s.start_le_stop
  have := s.stop.toNat_lt_size
  exact USize.toNat_add_of_lt (by lia)

/-- The element at index `i` of the slice, counted from the start of the slice. -/
@[inline, expose] public def get (s : USlice) (i : USize) (h : i < s.size) : UInt64 :=
  s.array.uget (s.start + i) (by
    have := s.toNat_start_add h
    have := s.toNat_size
    have := USize.lt_iff_toNat_lt.1 h
    have := s.stop_le_size
    lia)

public instance : GetElem USlice USize UInt64 fun s i => i < s.size where
  getElem s i h := s.get i h

public theorem getElem_eq_getElem! (s : USlice) (i : USize) (h : i < s.size) :
    s[i] = s.array[s.start.toNat + i.toNat]! := by
  have := s.toNat_start_add h
  have := s.toNat_size
  have := USize.lt_iff_toNat_lt.1 h
  have := s.stop_le_size
  show s.array[s.start + i]'(by lia) = _
  rw [getElem_usize, getElem!_eq_getElem _ _ (by lia)]
  congr 1

/-- The natural number whose little-endian base `2⁶⁴` limbs are the elements of `s`. -/
public def toNat (s : USlice) : Nat := s.array.valAt s.start.toNat s.size.toNat

public theorem toNat_eq_valAt (s : USlice) : s.toNat = s.array.valAt s.start.toNat s.size.toNat :=
  by rw [toNat]

end USlice

/--
The whole of `a` as a `USlice`. An array has fewer than `USize.size` elements, since `USize` can
address all memory; were it not so, the slice would only have the first `a.size % USize.size`.
-/
@[inline, expose] public def toUSlice (a : UInt64Array) : USlice where
  array := a
  start := 0
  stop := a.usize
  start_le_stop := USize.le_iff_toNat_le.2 (by simp)
  stop_le_size := by simp [usize, Nat.mod_le]

/--
The elements of `a` from index `start` up to, but not including, `stop`, as a `USlice`. Bounds past
the end of `a` are clamped to it, and a `start` past `stop` to `stop`.
-/
@[inline, expose] public def uslice (a : UInt64Array) (start stop : USize) : USlice :=
  let stop' := if stop.toNat ≤ a.size then stop else a.usize
  { array := a
    start := min start stop'
    stop := stop'
    start_le_stop := USize.min_le_right ..
    stop_le_size := by
      simp only [stop']
      split
      · assumption
      · simp [usize, Nat.mod_le] }

public theorem uslice_start (a : UInt64Array) (start stop : USize) (h₁ : start ≤ stop)
    (h₂ : stop.toNat ≤ a.size) : (a.uslice start stop).start = start := by
  simp only [uslice, h₂, ↓reduceIte]
  apply USize.le_antisymm (USize.min_le_left ..)
  exact USize.le_iff_toNat_le.2 (by rw [USize.toNat_min]; have := USize.le_iff_toNat_le.1 h₁; lia)

public theorem uslice_stop (a : UInt64Array) (start stop : USize) (h : stop.toNat ≤ a.size) :
    (a.uslice start stop).stop = stop := by
  simp [uslice, h]

public theorem toUSlice_toNat (a : UInt64Array) (h : a.size < USize.size) :
    a.toUSlice.toNat = a.toNat := by
  rw [USlice.toNat_eq_valAt, toNat_eq_valAt]
  simp [toUSlice, USlice.size, usize, Nat.mod_eq_of_lt h]

end ScalarArray.UInt64Array
