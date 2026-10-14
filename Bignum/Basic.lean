/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import Bignum.Limbs

/-!
# Natural numbers as limbs

A natural number is stored as little-endian base 2³² limbs in a `UInt32Array`. The arithmetic
works on slices of limbs, so it accepts trailing zero limbs, and its results are trimmed so that
the most significant limb is nonzero.

The specification is `toNat`, defined through `ofLimbs` on the list of limbs. Trimmed arrays
represent each natural number exactly once, and `ofNat` and `toNat` are inverse bijections
between them and `Nat`.
-/

open ScalarArray

namespace Bignum

/-- Removes the trailing zero limbs. -/
public def trim (a : UInt32Array) : UInt32Array := a.popWhile (· == 0)

/-- Whether the most significant limb is nonzero. -/
public def isTrimmed (a : UInt32Array) : Bool :=
  if h : 0 < a.size then a[a.size - 1] != 0 else true

/-- The limbs of a natural number. -/
public def ofNat (n : Nat) : UInt32Array := loop n (.emptyWithCapacity (n.log2 / 32 + 1))
where
  loop (n : Nat) (acc : UInt32Array) : UInt32Array :=
    if h : n = 0 then acc else loop (n / 2 ^ 32) (acc.push n.toUInt32)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The natural number that a slice of limbs denotes. -/
@[expose] public def toNat (s : UInt32Array.Slice) : Nat := ofLimbs s.copy.toList

/-! ## Specification -/

@[simp] public theorem toNat_toSlice (a : UInt32Array) : toNat a.toSlice = ofLimbs a.toList := by
  simp [toNat]

public theorem toNat_of_size_eq_zero {s : UInt32Array.Slice} (h : s.size = 0) : toNat s = 0 := by
  have : s.copy.toList = [] := List.eq_nil_of_length_eq_zero (by simp [h])
  simp [toNat, this]

public theorem toNat_of_size_eq_one {s : UInt32Array.Slice} (h : s.size = 1) :
    toNat s = (s[0]'(by omega)).toNat := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 (by simp [h] : s.copy.toList.length = 1)
  have : s[0]'(by omega) = x := by
    have := congrArg (·[0]?) hx
    simp only [UInt32Array.getElem?_toList, List.getElem?_cons_zero] at this
    rw [getElem?_pos s.copy 0 (by simp [h]), Option.some.injEq] at this
    simpa using this
  simp [toNat, hx, this]

/-- The limb of `s` at `j`, or `0` past the end. -/
@[inline, expose] public def limb (s : UInt32Array.Slice) (j : Nat) : UInt32 :=
  if h : j < s.size then s[j] else 0

public theorem limb_eq_getD (s : UInt32Array.Slice) (j : Nat) :
    limb s j = s.copy.toList.getD j 0 := by
  by_cases h : j < s.size
  · simp [limb, h, List.getD_eq_getElem?_getD]
  · simp [limb, h, List.getD_eq_getElem?_getD]

/-- Splitting a slice at `k` splits its value. -/
public theorem toNat_slice_add_toNat_slice (s : UInt32Array.Slice) (k : Nat) (hk : k ≤ s.size) :
    toNat (s.slice 0 k) + 2 ^ (32 * k) * toNat (s.slice k s.size) = toNat s := by
  have h := ofLimbs_append (s.copy.toList.take k) (s.copy.toList.drop k)
  rw [List.take_append_drop, List.length_take_of_le (by simpa using hk)] at h
  simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.toList_extract, h]
  simp [List.extract_eq_take_drop, List.take_of_length_le]

/-- Cutting an array to its first `n` limbs keeps a value below `2^(32 n)`. -/
public theorem toNat_toSlice_of_lt (a : UInt32Array) (n : Nat) (h : toNat a < 2 ^ (32 * n)) :
    toNat (a.toSlice 0 n) = toNat a := by
  rw [toNat_toSlice] at h
  simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero, ofLimbs_take_of_lt h]
  rw [List.take_of_length_le (by simp)]

public theorem toNat_lt (s : UInt32Array.Slice) : toNat s < 2 ^ (32 * s.size) := by
  have := ofLimbs_lt s.copy.toList
  rwa [UInt32Array.length_toList, UInt32Array.Slice.size_copy] at this

public theorem isTrimmed_iff (a : UInt32Array) : isTrimmed a = true ↔ IsTrimmed a.toList := by
  rw [isTrimmed, IsTrimmed, List.getLast?_eq_getElem?, UInt32Array.getElem?_toList,
    UInt32Array.length_toList]
  by_cases h : 0 < a.size
  · simp [h, getElem?_pos a (a.size - 1) (by omega)]
  · simp [h, getElem?_neg a (a.size - 1) (by omega)]

public theorem toList_trim (a : UInt32Array) : (trim a).toList = trimLimbs a.toList := by
  simp [trim, trimLimbs]

@[simp] public theorem toNat_trim (a : UInt32Array) : toNat (trim a) = toNat a := by
  simp [toList_trim]

public theorem isTrimmed_trim (a : UInt32Array) : isTrimmed (trim a) = true := by
  simp [isTrimmed_iff, toList_trim, isTrimmed_trimLimbs]

private theorem ofLimbs_ofNat_loop (n : Nat) (acc : UInt32Array) :
    ofLimbs (ofNat.loop n acc).toList = ofLimbs acc.toList + 2 ^ (32 * acc.size) * n := by
  induction n, acc using ofNat.loop.induct with
  | case1 acc => simp [ofNat.loop]
  | case2 n acc h ih =>
    rw [ofNat.loop]
    simp only [h, ↓reduceDIte]
    rw [ih, UInt32Array.toList_push, ofLimbs_concat, UInt32Array.length_toList,
      UInt32Array.size_push, Nat.toUInt32_eq,
      UInt32.toNat_ofNat']
    have := Nat.mod_add_div n (2 ^ 32)
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    grind

private theorem isTrimmed_ofNat_loop (n : Nat) (acc : UInt32Array) (hn : n ≠ 0) :
    IsTrimmed (ofNat.loop n acc).toList := by
  induction n, acc using ofNat.loop.induct with
  | case1 => contradiction
  | case2 n acc h ih =>
    rw [ofNat.loop]
    simp only [h, ↓reduceDIte]
    by_cases hq : n / 2 ^ 32 = 0
    · rw [ofNat.loop]
      simp only [hq, ↓reduceDIte, UInt32Array.toList_push, IsTrimmed, List.getLast?_concat, ne_eq,
        Option.some.injEq]
      rw [← UInt32.toNat_inj, Nat.toUInt32_eq, UInt32.toNat_ofNat']
      simp only [UInt32.toNat_zero]
      omega
    · exact ih hq

@[simp] public theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  simp [ofNat, ofLimbs_ofNat_loop]

public theorem isTrimmed_ofNat (n : Nat) : isTrimmed (ofNat n) = true := by
  rw [isTrimmed_iff, ofNat]
  by_cases hn : n = 0
  · simp [hn, ofNat.loop]
  · exact isTrimmed_ofNat_loop n _ hn

/-- A trimmed array is the limbs of the number it denotes. -/
public theorem ofNat_toNat {a : UInt32Array} (h : isTrimmed a = true) : ofNat (toNat a) = a := by
  apply UInt32Array.toList_inj.1
  apply IsTrimmed.ofLimbs_inj ((isTrimmed_iff _).1 (isTrimmed_ofNat _)) ((isTrimmed_iff _).1 h)
  rw [← toNat_toSlice, ← toNat_toSlice, toNat_ofNat]

public theorem toList_copy_drop {a : UInt32Array.Slice} {j : Nat} (h : j < a.size) :
    a.copy.toList.drop j = a[j] :: a.copy.toList.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

/-! ## `USize` indices

The compiled loops use `USize` indices, which need these facts to agree with the `Nat` indices of
the specifications.
-/

/-- `x + y` in `USize` does not wrap when the sum is below `USize.size`. -/
public theorem toNat_add_usize {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

public theorem toNat_toUSize {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  simp [Nat.mod_eq_of_lt h]

public theorem uget_eq_getElem (a : UInt32Array) (i : USize) (k : Nat) (hk : i.toNat = k)
    (h : i.toNat < a.size) : a.uget i h = a[k]'(hk ▸ h) := by
  subst hk
  rfl

public theorem uset_eq_set (a : UInt32Array) (i : USize) (k : Nat) (hk : i.toNat = k) (v : UInt32)
    (h : i.toNat < a.size) : a.uset i v h = a.set k v (hk ▸ h) := by
  subst hk
  rfl

/-- `a` followed by `n` zero limbs, which has the same value. -/
public def padZeros (a : UInt32Array) (n : Nat) : UInt32Array := a ++ .replicate n 0

@[simp] public theorem size_padZeros (a : UInt32Array) (n : Nat) :
    (padZeros a n).size = a.size + n := by
  simp [padZeros]

@[simp] public theorem toNat_padZeros (a : UInt32Array) (n : Nat) :
    toNat (padZeros a n) = toNat a := by
  rw [toNat_toSlice, toNat_toSlice, padZeros, UInt32Array.toList_append,
    UInt32Array.toList_replicate, ofLimbs_append_replicate_zero]

/-- The limbs of `a` in a new array of `n` limbs, padded with zeros, copied with one `memcpy`. -/
public def copyPadded (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  a.array.copySlice a.start (.replicate n 0) 0 a.size

private theorem toList_copyPadded (a : UInt32Array.Slice) (n : Nat) :
    (copyPadded a n).toList = a.copy.toList ++ List.replicate (n - a.size) 0 := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have hs := a.size_eq
  have hstop : a.start + a.size = a.stop := by omega
  have hmin : min a.size (a.array.size - a.start) = a.size := by omega
  simp only [copyPadded, UInt32Array.toList_copySlice, UInt32Array.toList_replicate,
    UInt32Array.size_replicate, Nat.zero_add, hstop, hmin, List.extract_eq_take_drop,
    List.drop_replicate, Nat.sub_zero, List.take_replicate, Nat.min_def, UInt32Array.Slice.copy,
    UInt32Array.toList_extract]
  simp only [Nat.le_refl, ↓reduceIte]
  rfl

@[simp] public theorem size_copyPadded (a : UInt32Array.Slice) (n : Nat) (h : a.size ≤ n) :
    (copyPadded a n).size = n := by
  rw [← UInt32Array.length_toList, toList_copyPadded a n, List.length_append,
    UInt32Array.length_toList, UInt32Array.Slice.size_copy, List.length_replicate]
  omega

public theorem toNat_copyPadded (a : UInt32Array.Slice) (n : Nat) :
    toNat (copyPadded a n) = toNat a := by
  rw [toNat_toSlice, toList_copyPadded a n, ofLimbs_append_replicate_zero]
  rfl

/-- Shifts a number left by `k` limbs. -/
public def shiftLimbs (a : UInt32Array) (k : Nat) : UInt32Array :=
  if a.isEmpty then a else .replicate k 0 ++ a

end Bignum
