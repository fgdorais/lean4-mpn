/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import MPN.LimbArray
public import MPN.WordArray
public import ScalarArray.InPlaceSyntax
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import MPN32.Arch.UInt

/-!
# Limb arrays with `USize` bounds

The tooling of `main64`'s flat-array FFT on 32-bit limbs: the instance `limbArray32` of `main`'s
`LimbArray`, whose `valAt` is the value of a range of limbs; `USlice`, a region of an array with
`USize` bounds; `foldUInPlace`, the in-place loop; and `foldUInPlace2`, the in-place loop that
reads other windows of the array it writes. Their `@[csimp]` lemmas run lean4-scalar-arrays'
folds in their place. The rest of the library works on the library's slices and `MPN.toNat`.
-/

open ScalarArray

/-- Arrays of 32-bit limbs, for the limb-width-independent parts of `main`. -/
public instance limbArray32 : MPN.LimbArray UInt32Array UInt32 where
  w := 32
  w_pos := by decide
  size a := a.size
  get a i := a[i]!
  val x := x.toNat
  val_lt x := x.toNat_lt
  set a i v := a.set! i (UInt32.ofNat v)
  size_set a i v := UInt32Array.size_set! ..
  get_set_ne a i v j h := by
    show (a.set! i _)[j]! = a[j]!
    rw [UInt32Array.getElem!_eq_getElem!_toArray, UInt32Array.getElem!_eq_getElem!_toArray,
      UInt32Array.toArray_set!]
    have := a.size_toArray
    grind
  val_get_set_self a i v h := by
    show (a.set! i _)[i]!.toNat = _
    rw [UInt32Array.getElem!_eq_getElem!_toArray, UInt32Array.toArray_set!]
    have := a.size_toArray
    have : (a.toArray.set! i (UInt32.ofNat v))[i]! = UInt32.ofNat v := by grind
    rw [this, UInt32.toNat_ofNat']

namespace ScalarArray.UInt32Array

/--
The natural number whose little-endian base `2³²` limbs are `a[lo], …, a[lo + n - 1]`, where
the limbs past the end of `a` are zero.
-/
@[expose] public def valAt (a : UInt32Array) (lo n : Nat) : Nat := MPN.LimbArray.valAt a lo n

@[simp] public theorem valAt_zero (a : UInt32Array) (lo : Nat) : a.valAt lo 0 = 0 :=
  MPN.LimbArray.valAt_zero a lo

public theorem valAt_succ (a : UInt32Array) (lo n : Nat) :
    a.valAt lo (n + 1) = a[lo]!.toNat + 2 ^ 32 * a.valAt (lo + 1) n :=
  MPN.LimbArray.valAt_succ a lo n

@[simp] public theorem valAt_one (a : UInt32Array) (lo : Nat) : a.valAt lo 1 = a[lo]!.toNat := by
  simp [valAt_succ]

public theorem valAt_lt (a : UInt32Array) (lo n : Nat) : a.valAt lo n < 2 ^ (32 * n) :=
  MPN.LimbArray.valAt_lt a lo n

/-- `valAt` only depends on the limbs it reads. -/
public theorem valAt_congr {a b : UInt32Array} {lo : Nat} (n : Nat)
    (h : ∀ i, lo ≤ i → i < lo + n → a[i]! = b[i]!) : a.valAt lo n = b.valAt lo n :=
  MPN.LimbArray.valAt_congr n h

/-- Splits `valAt` into its low `m` limbs and the `k` limbs above them. -/
public theorem valAt_add (a : UInt32Array) (lo m k : Nat) :
    a.valAt lo (m + k) = a.valAt lo m + 2 ^ (32 * m) * a.valAt (lo + m) k :=
  MPN.LimbArray.valAt_add a lo m k

public theorem getElem!_eq_getElem (a : UInt32Array) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  rw [getElem!_eq_getElem!_toArray, getElem_eq_getElem_toArray]
  simp [h]

/-- `getD` with `0` reads as `getElem!`. -/
public theorem getD_zero_eq_getElem! (a : UInt32Array) (i : Nat) : a.getD i 0 = a[i]! := by
  rw [getD_eq_getD_getElem?]
  by_cases h : i < a.size
  · rw [getElem?_pos a i h, getElem!_eq_getElem a i h]
    rfl
  · rw [getElem?_neg a i h, getElem!_neg a i h]
    rfl

/-- The limbs past the end of `a` are zero. -/
public theorem valAt_of_size_le (a : UInt32Array) {lo : Nat} (n : Nat) (h : a.size ≤ lo) :
    a.valAt lo n = 0 := by
  induction n generalizing lo with
  | zero => simp
  | succ n ih => rw [valAt_succ, ih (by lia), getElem!_neg a lo (by lia)]; rfl

/-- Reading past the end of `a` adds nothing. -/
public theorem valAt_extend (a : UInt32Array) {lo m : Nat} (n : Nat) (h : a.size ≤ lo + m)
    (hm : m ≤ n) : a.valAt lo n = a.valAt lo m := by
  rw [show n = m + (n - m) by lia, valAt_add, valAt_of_size_le _ _ h, Nat.mul_zero, Nat.add_zero]

/-- The `n` limbs of `a` from `lo`, as many as there are past `lo`. -/
public theorem valAt_size_sub (a : UInt32Array) (lo n : Nat) :
    a.valAt lo (min n (a.size - lo)) = a.valAt lo n := by
  by_cases h : n ≤ a.size - lo
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by lia), valAt_extend a (m := a.size - lo) n (by lia) (by lia)]

public theorem getElem!_set (a : UInt32Array) (i : Nat) (v : UInt32) (h : i < a.size) (j : Nat) :
    (a.set i v h)[j]! = if i = j then v else a[j]! := by
  rw [getElem!_eq_getElem!_toArray, getElem!_eq_getElem!_toArray, toArray_set]
  have := a.size_toArray
  grind

/-- Limb `k` of `a` is a digit of its value. -/
public theorem toNat_getElem_eq (a : UInt32Array) {k : Nat} (hk : k < a.size) :
    a[k].toNat = a.valAt 0 a.size / 2 ^ (32 * k) % 2 ^ 32 := by
  have := MPN.LimbArray.val_get_eq a (n := a.size) hk
  change a[k]!.toNat = a.valAt 0 a.size / 2 ^ (32 * k) % 2 ^ 32 at this
  rwa [getElem!_eq_getElem a k hk] at this

/-- The limbs of a value below `2^(32 k)` are zero from `k` on. -/
public theorem getElem_eq_zero_of_valAt_lt (a : UInt32Array) {k : Nat} (hk : k < a.size)
    (h : a.valAt 0 a.size < 2 ^ (32 * k)) : a[k] = 0 :=
  UInt32.toNat_inj.1 (by rw [toNat_getElem_eq a hk, Nat.div_eq_of_lt h, Nat.zero_mod]; rfl)

/-- Arrays of the same size are determined by their values. -/
public theorem eq_of_valAt_eq {a b : UInt32Array} (h : a.size = b.size)
    (hv : a.valAt 0 a.size = b.valAt 0 b.size) : a = b :=
  ext_getElem h fun k hka hkb =>
    UInt32.toNat_inj.1 (by rw [toNat_getElem_eq a hka, toNat_getElem_eq b hkb, hv])

/-- Zeros are zero. -/
@[simp] public theorem valAt_replicate_zero (n lo m : Nat) :
    (UInt32Array.replicate n 0).valAt lo m = 0 :=
  MPN.LimbArray.valAt_eq_zero _ fun i _ _ => by
    change (UInt32Array.replicate n 0)[i]!.toNat = 0
    by_cases h : i < n
    · rw [getElem!_eq_getElem _ _ (by simpa using h)]
      simp
    · rw [getElem!_neg _ _ (by simpa using h)]
      rfl

/-- Replacing limb `k`, one of the `n` from `lo`, changes their value by the difference. -/
public theorem valAt_set (a : UInt32Array) (k : Nat) (v : UInt32) (h : k < a.size) (lo n : Nat)
    (h₁ : lo ≤ k) (h₂ : k < lo + n) :
    (a.set k v h).valAt lo n + 2 ^ (32 * (k - lo)) * a[k].toNat =
      a.valAt lo n + 2 ^ (32 * (k - lo)) * v.toNat := by
  have e : n = (k - lo) + (1 + (n - (k - lo) - 1)) := by lia
  have hk : lo + (k - lo) = k := by lia
  have hlow : (a.set k v h).valAt lo (k - lo) = a.valAt lo (k - lo) :=
    valAt_congr _ fun i _ hi => by rw [getElem!_set, ite_eq_right (by lia)]
  have hhigh :
      (a.set k v h).valAt (k + 1) (n - (k - lo) - 1) = a.valAt (k + 1) (n - (k - lo) - 1) :=
    valAt_congr _ fun i hi _ => by rw [getElem!_set, ite_eq_right (by lia)]
  rw [e, valAt_add, valAt_add a, hk, valAt_add (a.set k v h) k, valAt_add a k, valAt_one,
    valAt_one, getElem!_set, ite_eq_left rfl, getElem!_eq_getElem a k h, hlow, hhigh]
  generalize a.valAt lo (k - lo) = L
  generalize a.valAt (k + 1) (n - (k - lo) - 1) = H
  generalize 2 ^ (32 * (k - lo)) = P
  rw [Nat.mul_add, Nat.mul_add]
  lia

public theorem getElem!_set! (a : UInt32Array) (i j : Nat) (v : UInt32) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [getElem!_eq_getElem!_toArray, getElem!_eq_getElem!_toArray, toArray_set!]
  have := a.size_toArray
  grind

@[simp] public theorem getElem!_set!_self (a : UInt32Array) (i : Nat) (v : UInt32)
    (h : i < a.size) : (a.set! i v)[i]! = v := by
  rw [getElem!_set!]
  simp [h]

public theorem getElem!_set!_of_ne (a : UInt32Array) {i j : Nat} (v : UInt32) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [getElem!_set!]
  simp [h]

public theorem Slice.getElem_eq_getElem! (s : UInt32Array.Slice) (i : Nat) (h : i < s.size) :
    s[i] = s.array[s.start + i]! := by
  have := s.stop_le_array_size
  rw [Slice.getElem_eq, getElem!_eq_getElem _ _ (by rw [Slice.size_eq] at h; lia)]

/-! ### `USize` arithmetic -/

public theorem getElem!_uset (a : UInt32Array) (i : USize) (v : UInt32) (h : i.toNat < a.size)
    (j : Nat) : (a.uset i v h)[j]! = if i.toNat = j then v else a[j]! := by
  rw [getElem!_eq_getElem!_toArray, getElem!_eq_getElem!_toArray, toArray_uset]
  have := a.size_toArray
  grind

/-! ### Slices with `USize` bounds -/

/--
A region of a `UInt32Array` with `USize` bounds: the elements from index `start` up to, but not
including, `stop`. Since `stop` is a `USize`, so is every index of the region, and indexing it
needs no `Nat` arithmetic.
-/
public structure USlice where
  /-- The underlying array. -/
  array : UInt32Array
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
@[inline, expose] public def get (s : USlice) (i : USize) (h : i < s.size) : UInt32 :=
  s.array.uget (s.start + i) (by
    have := s.toNat_start_add h
    have := s.toNat_size
    have := USize.lt_iff_toNat_lt.1 h
    have := s.stop_le_size
    lia)

public instance : GetElem USlice USize UInt32 fun s i => i < s.size where
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

/-- The natural number whose little-endian base `2³²` limbs are the elements of `s`. -/
public def toNat (s : USlice) : Nat := s.array.valAt s.start.toNat s.size.toNat

public theorem toNat_eq_valAt (s : USlice) : s.toNat = s.array.valAt s.start.toNat s.size.toNat :=
  by rw [toNat]

end USlice

/--
The whole of `a` as a `USlice`. An array has fewer than `USize.size` elements, since `USize` can
address all memory; were it not so, the slice would only have the first `a.size % USize.size`.
-/
@[inline, expose] public def toUSlice (a : UInt32Array) : USlice where
  array := a
  start := 0
  stop := a.usize
  start_le_stop := USize.le_iff_toNat_le.2 (by simp)
  stop_le_size := by simp [usize, Nat.mod_le]

/--
The elements of `a` from index `start` up to, but not including, `stop`, as a `USlice`. Bounds past
the end of `a` are clamped to it, and a `start` past `stop` to `stop`.
-/
@[inline, expose] public def uslice (a : UInt32Array) (start stop : USize) : USlice :=
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

public theorem uslice_start (a : UInt32Array) (start stop : USize) (h₁ : start ≤ stop)
    (h₂ : stop.toNat ≤ a.size) : (a.uslice start stop).start = start := by
  simp only [uslice, h₂, ↓reduceIte]
  apply USize.le_antisymm (USize.min_le_left ..)
  exact USize.le_iff_toNat_le.2 (by rw [USize.toNat_min]; have := USize.le_iff_toNat_le.1 h₁; lia)

public theorem uslice_stop (a : UInt32Array) (start stop : USize) (h : stop.toNat ≤ a.size) :
    (a.uslice start stop).stop = stop := by
  simp [uslice, h]

public theorem toUSlice_toNat (a : UInt32Array) (h : a.size < USize.size) :
    a.toUSlice.toNat = a.valAt 0 a.size := by
  rw [USlice.toNat_eq_valAt]
  simp [toUSlice, USlice.size, usize, Nat.mod_eq_of_lt h]

/-! ### Loops over `USize` indices -/

/--
The bounds of a loop over limbs `rs` to `rs + n - 1` of `arr`: they are limbs of `arr`, and their
indices do not overflow.
-/
public abbrev LoopBound (arr : UInt32Array) (rs n : USize) : Prop :=
  rs.toNat + n.toNat ≤ arr.size ∧ rs.toNat + n.toNat < USize.size

public theorem LoopBound.of_uset {arr : UInt32Array} {rs n : USize} (hr : LoopBound arr rs n)
    (i : USize) (v : UInt32) (h) : LoopBound (arr.uset i v h) rs n := by
  simp only [LoopBound, size_uset] at hr ⊢
  exact hr

public theorem LoopBound.toNat_add {arr : UInt32Array} {rs n j : USize} (hr : LoopBound arr rs n)
    (h : j < n) : (rs + j).toNat = rs.toNat + j.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  exact USize.toNat_add_of_lt (by lia)

public theorem LoopBound.uset_bound {arr : UInt32Array} {rs n j : USize}
    (hr : LoopBound arr rs n) (h : j < n) : (rs + j).toNat < arr.size := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [hr.toNat_add h]
  lia

public theorem uget_eq_getElem! (a : UInt32Array) (i : USize) (h : i.toNat < a.size) :
    a.uget i h = a[i.toNat]! := by
  show a[i] = _
  rw [getElem_usize, getElem!_eq_getElem]

/-- `valAt` does not see a `uset` outside the limbs it reads. -/
public theorem valAt_uset_of (a : UInt32Array) (i : USize) (v : UInt32) (h : i.toNat < a.size)
    (lo n : Nat) (hi : i.toNat < lo ∨ lo + n ≤ i.toNat) :
    (a.uset i v h).valAt lo n = a.valAt lo n :=
  valAt_congr _ fun k h₁ h₂ => by
    rw [getElem!_uset]
    simp only [show ¬(i.toNat = k) by lia, ↓reduceIte]

/-- The first `n` limbs of `r`, for `n ≤ r.size`, as a loop bound. -/
public theorem USlice.loopBound (r : USlice) {n : USize} (hn : n ≤ r.size) :
    LoopBound r.array r.start n := by
  have := r.toNat_size
  have := USize.le_iff_toNat_le.1 hn
  have := USize.le_iff_toNat_le.1 r.start_le_stop
  have := r.stop.toNat_lt_size
  have := r.stop_le_size
  constructor <;> lia

/-! ### Sub-slices -/

/--
The elements of `s` from index `i` up to, but not including, `j`, as a `USlice` of the same array.
Bounds past the end of `s` are clamped to it, and an `i` past `j` to `j`.
-/
@[inline, expose] public def USlice.slice (s : USlice) (i j : USize) : USlice :=
  let j' := min j s.size
  let i' := min i j'
  { array := s.array
    start := s.start + i'
    stop := s.start + j'
    start_le_stop := by
      have := s.toNat_size
      have := s.stop.toNat_lt_size
      have := USize.le_iff_toNat_le.1 s.start_le_stop
      have hj : j'.toNat ≤ s.size.toNat := by simp only [j', USize.toNat_min]; lia
      have hi : i'.toNat ≤ j'.toNat := by simp only [i', USize.toNat_min]; lia
      rw [USize.le_iff_toNat_le, USize.toNat_add_of_lt (by lia), USize.toNat_add_of_lt (by lia)]
      lia
    stop_le_size := by
      have := s.toNat_size
      have := s.stop.toNat_lt_size
      have := s.stop_le_size
      have := USize.le_iff_toNat_le.1 s.start_le_stop
      have hj : j'.toNat ≤ s.size.toNat := by simp only [j', USize.toNat_min]; lia
      rw [USize.toNat_add_of_lt (by lia)]
      lia }

@[simp] public theorem USlice.array_slice (s : USlice) (i j : USize) :
    (s.slice i j).array = s.array := rfl

public theorem USlice.start_slice (s : USlice) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ s.size.toNat) : (s.slice i j).start.toNat = s.start.toNat + i.toNat := by
  have := s.toNat_size
  have := s.stop.toNat_lt_size
  have := USize.le_iff_toNat_le.1 s.start_le_stop
  simp only [slice]
  rw [USize.toNat_add_of_lt (by rw [USize.toNat_min, USize.toNat_min]; lia),
    USize.toNat_min, USize.toNat_min]
  lia

public theorem USlice.stop_slice (s : USlice) {j : USize} (i : USize)
    (hj : j.toNat ≤ s.size.toNat) : (s.slice i j).stop.toNat = s.start.toNat + j.toNat := by
  have := s.toNat_size
  have := s.stop.toNat_lt_size
  have := USize.le_iff_toNat_le.1 s.start_le_stop
  simp only [slice]
  rw [USize.toNat_add_of_lt (by rw [USize.toNat_min]; lia), USize.toNat_min]
  lia

public theorem USlice.size_slice (s : USlice) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ s.size.toNat) : (s.slice i j).size.toNat = j.toNat - i.toNat := by
  rw [(s.slice i j).toNat_size, s.stop_slice i hj, s.start_slice hij hj]
  lia

public theorem USlice.toNat_slice (s : USlice) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ s.size.toNat) :
    (s.slice i j).toNat = s.array.valAt (s.start.toNat + i.toNat) (j.toNat - i.toNat) := by
  rw [toNat_eq_valAt, s.start_slice hij hj, s.size_slice hij hj, array_slice]

/-- The low `m` of `n` limbs of a value: its residue modulo `2^(64 m)`. -/
public theorem valAt_mod (a : UInt32Array) (lo : Nat) {m n : Nat} (h : m ≤ n) :
    a.valAt lo m = a.valAt lo n % 2 ^ (32 * m) :=
  MPN.LimbArray.valAt_mod a lo h

/-- The same bounds on another array of the same size, such as the result of writing to `s`. -/
@[inline, expose] public def USlice.reseat (s : USlice) (arr : UInt32Array)
    (h : arr.size = s.array.size) : USlice where
  array := arr
  start := s.start
  stop := s.stop
  start_le_stop := s.start_le_stop
  stop_le_size := h ▸ s.stop_le_size

@[simp] public theorem USlice.array_reseat (s : USlice) (arr : UInt32Array) (h) :
    (s.reseat arr h).array = arr := rfl

@[simp] public theorem USlice.start_reseat (s : USlice) (arr : UInt32Array) (h) :
    (s.reseat arr h).start = s.start := rfl

@[simp] public theorem USlice.size_reseat (s : USlice) (arr : UInt32Array) (h) :
    (s.reseat arr h).size = s.size := rfl

@[simp] public theorem start_toUSlice (a : UInt32Array) : a.toUSlice.start = 0 := rfl

@[simp] public theorem array_toUSlice (a : UInt32Array) : a.toUSlice.array = a := rfl

public theorem size_toUSlice (a : UInt32Array) (h : a.size < USize.size) :
    a.toUSlice.size.toNat = a.size := by
  simp [toUSlice, USlice.size, usize, Nat.mod_eq_of_lt h]

/-! ### In-place loops

`foldUInPlace n f arr rs hr j b` replaces limbs `rs + j` to `rs + n - 1` of `arr` while threading
an accumulator: limb `rs + j` holding `x` becomes `(f j hj x b).1`, and `(f j hj x b).2` is the
next accumulator. Its definition is a loop of `uset`s, which checks that `arr` is exclusive at
every store; its implementation, through `foldUInPlaceThen`, makes `arr` exclusive once and then
stores without checks. That is safe because `f` only sees the limbs, never the array: anything
`f` reads, even another reference to the same array, is the object from before the loop.
-/

/-- Replaces limbs `rs + j` to `rs + n - 1` of `arr` with `f`, threading an accumulator. -/
@[expose] public def foldUInPlace {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β)
    (arr : UInt32Array) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) :
    UInt32Array × β :=
  if h : j < n then
    let p := f j h (arr.uget (rs + j) (hr.uset_bound h)) b
    foldUInPlace n f (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1) p.2
  else
    (arr, b)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem foldUInPlace_lt {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β) (h : j < n) :
    foldUInPlace n f arr rs hr j b =
      foldUInPlace n f (arr.uset (rs + j) (f j h (arr.uget (rs + j) (hr.uset_bound h)) b).1
        (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1)
        (f j h (arr.uget (rs + j) (hr.uset_bound h)) b).2 := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem foldUInPlace_ge {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β) (h : ¬j < n) :
    foldUInPlace n f arr rs hr j b = (arr, b) := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem size_foldUInPlace {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β) :
    (foldUInPlace n f arr rs hr j b).1.size = arr.size := by
  induction arr, hr, j, b using foldUInPlace.induct n f rs with
  | case1 arr hr j b h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    exact ih.trans (size_uset ..)
  | case2 arr hr j b h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]

/--
`foldUInPlace` followed by `g` on the new array and the last accumulator, which the loop calls
itself instead of returning a pair. `g` also receives a proof that the size is unchanged. The
compiler runs lean4-scalar-arrays' `foldlInPlaceRangeThen` in its place
(`foldUInPlaceThen_eq_lib`), which makes `arr` exclusive once, before the loop, and then stores
without checks.
-/
@[expose]
public def foldUInPlaceThen {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β → γ) : γ :=
  g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..) (foldUInPlace n f arr rs hr j b).2

public theorem foldUInPlaceThen_eq {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β → γ) :
    foldUInPlaceThen n f arr rs hr j b g =
      g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..)
        (foldUInPlace n f arr rs hr j b).2 := by
  rw [foldUInPlaceThen]

/-! ### The compiled loops

The loops above are plain recursions of `uget` and `uset`, which the proofs are about. The
compiler runs the in-place folds of lean4-scalar-arrays in their place, through `@[csimp]`
lemmas: the fold over the `USize` range `[rs + j, rs + n)`, with its index shifted by `j`.
-/

private theorem uset_eq_set' (a : UInt32Array) (i : USize) (v : UInt32) (h) (m : Nat)
    (hm : i.toNat = m) : a.uset i v h = a.set m v (hm ▸ h) := by
  subst hm; rfl

private theorem uget_eq_get' (a : UInt32Array) (i : USize) (h) (m : Nat) (hm : i.toNat = m) :
    a.uget i h = a[m]'(hm ▸ h) := by
  subst hm; rfl

public theorem toNat_shift {n j₀ k : USize} (h : j₀ < n) (hk : k.toNat < (n - j₀).toNat) :
    (j₀ + k).toNat = j₀.toNat + k.toNat ∧ j₀ + k < n := by
  have h₀ := USize.lt_iff_toNat_lt.1 h
  have hs : (n - j₀).toNat = n.toNat - j₀.toNat := USize.toNat_sub_of_le _ _ (USize.le_of_lt h)
  have hn := n.toNat_lt_size
  have e : (j₀ + k).toNat = j₀.toNat + k.toNat := USize.toNat_add_of_lt (by lia)
  exact ⟨e, USize.lt_iff_toNat_lt.2 (by rw [e]; lia)⟩

private theorem toNat_toUSize_of_le {n j₀ : USize} (h : j₀ < n) {k : Nat}
    (hk : k ≤ (n - j₀).toNat) : k.toUSize.toNat = k := by
  have hs : (n - j₀).toNat = n.toNat - j₀.toNat := USize.toNat_sub_of_le _ _ (USize.le_of_lt h)
  have := n.toNat_lt_size
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]

/-- The slice loop of the range fold from index `k` is `foldUInPlace` from `j₀ + k`. -/
private theorem rangeLoop_eq {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (rs j₀ : USize) (hj₀ : j₀ < n)
    (N : Nat) (hN : N = (n - j₀).toNat)
    (f' : (k : USize) → k.toNat < N → UInt32 → β → UInt32 × β)
    (hf : ∀ k hk h', f' k hk = f (j₀ + k) h') (k : Nat) (hkN : k ≤ N) :
    ∀ (s : UInt32Array.Slice) (hs : s.size = N) (_ : s.start = (rs + j₀).toNat)
      (hr : LoopBound s.array rs n) (b : β),
      ((Slice.foldlInPlace.loop N f' s hs k b).1.array, (Slice.foldlInPlace.loop N f' s hs k b).2) =
        foldUInPlace n f s.array rs hr (j₀ + k.toUSize) b := by
  subst hN
  have hsub : (n - j₀).toNat = n.toNat - j₀.toNat := USize.toNat_sub_of_le _ _ (USize.le_of_lt hj₀)
  have h₀ := USize.lt_iff_toNat_lt.1 hj₀
  have hn := n.toNat_lt_size
  induction hd : (n - j₀).toNat - k generalizing k with
  | zero =>
    intro s hs _ hr b
    rw [Slice.foldlInPlace.loop, dite_eq_right (by lia), foldUInPlace_ge]
    intro hlt
    have := USize.lt_iff_toNat_lt.1 hlt
    rw [USize.toNat_add_of_lt (by rw [toNat_toUSize_of_le hj₀ hkN]; lia),
      toNat_toUSize_of_le hj₀ hkN] at this
    lia
  | succ d ih =>
    intro s hs hst hr b
    have hk : k < (n - j₀).toNat := by lia
    have hkk := toNat_toUSize_of_le hj₀ (Nat.le_of_lt hk)
    obtain ⟨e, hlt⟩ := toNat_shift hj₀ (k := k.toUSize) (by rw [hkk]; exact hk)
    have hrs : (rs + (j₀ + k.toUSize)).toNat = (rs + j₀).toNat + k := by
      rw [hr.toNat_add hlt, hr.toNat_add hj₀, e, hkk]; lia
    rw [Slice.foldlInPlace.loop, dite_eq_left hk, foldUInPlace_lt _ _ _ _ _ _ _ hlt]
    dsimp only
    rw [hf _ _ hlt]
    have hget : s[k]'(by lia) = s.array.uget (rs + (j₀ + k.toUSize)) (hr.uset_bound hlt) := by
      rw [Slice.getElem_eq, uget_eq_get' _ _ _ (s.start + k) (by rw [hrs, hst])]
    simp only [hget]
    have hnext : j₀ + k.toUSize + 1 = j₀ + (k + 1).toUSize := by
      have hk1 := toNat_toUSize_of_le hj₀ (Nat.succ_le_of_lt hk)
      apply USize.toNat_inj.1
      rw [USize.toNat_add_of_lt (by rw [USize.toNat_one, e]; lia), USize.toNat_one, e,
        USize.toNat_add_of_lt (by rw [hk1]; lia), hk1, hkk]
      lia
    rw [hnext]
    refine (ih (k + 1) (by lia) (by lia) _ (by simpa using hs) (by simpa using hst)
      (by simpa [LoopBound] using hr) _).trans ?_
    congr 1
    rw [Slice.array_set, uset_eq_set' _ _ _ _ (s.start + k) (by rw [hrs, hst])]

/-- `foldUInPlaceThen` by `foldlInPlaceRangeThen` on `[rs + j, rs + n)`. -/
@[inline, expose] public def foldUInPlaceThenLib {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β → γ) : γ :=
  if h : j < n then
    arr.foldlInPlaceRangeThen (rs + j) (n - j) (by
        have h₀ := USize.lt_iff_toNat_lt.1 h
        rw [hr.toNat_add h, USize.toNat_sub_of_le _ _ (USize.le_of_lt h)]; lia) b
      (fun k hk x b => f (j + k) (toNat_shift h hk).2 x b) g
  else g arr rfl b

/--
`foldUInPlaceThen` with an accumulator of two parts by `foldlInPlaceRangeWith2AccThen` on
`[rs + j, rs + n)`, which keeps the parts apart.
-/
@[inline, expose] public def foldUInPlaceThen2Lib {β₁ β₂ γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β₁ → β₂ → UInt32 × β₁ × β₂) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b₁ : β₁) (b₂ : β₂)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β₁ → β₂ → γ) : γ :=
  if h : j < n then
    arr.foldlInPlaceRangeWith2AccThen (rs + j) (n - j) (by
        have h₀ := USize.lt_iff_toNat_lt.1 h
        rw [hr.toNat_add h, USize.toNat_sub_of_le _ _ (USize.le_of_lt h)]; lia) b₁ b₂
      (fun k hk x c₁ c₂ => f (j + k) (toNat_shift h hk).2 x c₁ c₂) g
  else g arr rfl b₁ b₂

public theorem foldUInPlaceThen2Lib_eq {β₁ β₂ γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β₁ → β₂ → UInt32 × β₁ × β₂) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b₁ : β₁) (b₂ : β₂)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β₁ → β₂ → γ) :
    foldUInPlaceThen2Lib n f arr rs hr j b₁ b₂ g =
      foldUInPlaceThenLib n (fun j h z c => f j h z c.1 c.2) arr rs hr j (b₁, b₂)
        (fun arr' h c => g arr' h c.1 c.2) := by
  unfold foldUInPlaceThen2Lib foldUInPlaceThenLib
  split
  · rw [foldlInPlaceRangeWith2AccThen_eq]
  · rfl

/-- A continuation applied to equal pairs, with the size proof carried along. -/
private theorem g_congr {β γ : Type} {arr : UInt32Array}
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β → γ) {p q : UInt32Array × β}
    (hpq : p = q) (hp : p.1.size = arr.size) : g p.1 hp p.2 = g q.1 (hpq ▸ hp) q.2 := by
  subst hpq; rfl

@[csimp] public theorem foldUInPlaceThen_eq_lib :
    @foldUInPlaceThen = @foldUInPlaceThenLib := by
  funext β γ n f arr rs hr j b g
  rw [foldUInPlaceThen, foldUInPlaceThenLib]
  split
  · rename_i h
    rw [foldlInPlaceRangeThen_eq]
    have h₀ := USize.lt_iff_toNat_lt.1 h
    have hs := USize.toNat_sub_of_le _ _ (USize.le_of_lt h)
    have hrj := hr.toNat_add h
    have := hr.1
    have hN : (arr.toSlice (rs + j).toNat ((rs + j).toNat + (n - j).toNat)).size =
        (n - j).toNat := by
      simp only [size_toSlice]; rw [hrj, hs]; lia
    have e := rangeLoop_eq n f rs j h _ hN
      (fun k hk => f (j + k) (toNat_shift h (by rw [← hN]; exact hk)).2)
      (fun _ _ _ => rfl) 0 (Nat.zero_le _)
      (arr.toSlice (rs + j).toNat ((rs + j).toNat + (n - j).toNat)) rfl
      (by simp only [start_toSlice]; rw [hrj, hs]; lia) (by simpa using hr) b
    simp only [array_toSlice, show (0 : Nat).toUSize = 0 from rfl, USize.add_zero] at e
    exact (g_congr g (Eq.trans rfl e) _).symm
  · rename_i h
    exact g_congr g (foldUInPlace_ge _ _ _ _ _ _ _ h) _

/-! ### The word arrays of `main`

The instances of `main`'s `WordArray` and `WordFolds` on `UInt32Array`, for its loops written for
limbs of any width. Its in-place loop reading other windows of the array it writes,
`foldUInPlace2Then`, runs lean4-scalar-arrays' `foldlInPlace2Then` (`fold2Then_eq` of
`wordFolds32`).
-/

/-- `log2` of a word is `Nat.log2` of its value. -/
public theorem _root_.UInt32.toNat_log2' (x : UInt32) : x.log2.toNat = x.toNat.log2 := by rfl

/--
One limb of a multiply-subtract pass by two limbs: `z - y (x₀ + β x₁) - (c₀ + β c₁)` and the two
limbs of the borrow out, in 64-bit words: `y x₀ + c₀` and `y x₁ + c₁` plus the high half of the
first and the borrow fit in them.
-/
@[inline, expose] public def subMul2W (z y x₀ x₁ c₀ c₁ : UInt32) : UInt32 × UInt32 × UInt32 :=
  let a₀ := y.toUInt64 * x₀.toUInt64 + c₀.toUInt64
  let lo := a₀.toUInt32
  let a₁ := y.toUInt64 * x₁.toUInt64 + c₁.toUInt64 + (a₀ >>> 32) + (decide (z < lo)).toUInt64
  (z - lo, a₁.toUInt32, (a₁ >>> 32).toUInt32)

public theorem val_subMul2W (z y x₀ x₁ c₀ c₁ : UInt32) :
    (subMul2W z y x₀ x₁ c₀ c₁).1.toNat + y.toNat * (x₀.toNat + 2 ^ 32 * x₁.toNat) +
        (c₀.toNat + 2 ^ 32 * c₁.toNat) =
      z.toNat + 2 ^ 32 * ((subMul2W z y x₀ x₁ c₀ c₁).2.1.toNat +
        2 ^ 32 * (subMul2W z y x₀ x₁ c₀ c₁).2.2.toNat) := by
  have hz := z.toNat_lt; have hy := y.toNat_lt; have hx₀ := x₀.toNat_lt; have hx₁ := x₁.toNat_lt
  have hc₀ := c₀.toNat_lt; have hc₁ := c₁.toNat_lt
  have hp₀ : y.toNat * x₀.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by lia) (by lia)
  have hp₁ : y.toNat * x₁.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by lia) (by lia)
  have e : y.toNat * (x₀.toNat + 2 ^ 32 * x₁.toNat) =
      y.toNat * x₀.toNat + 2 ^ 32 * (y.toNat * x₁.toNat) := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  rw [e]
  simp only [subMul2W, UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64,
    UInt64.toNat_toUInt32, UInt32.toNat_sub, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Bool.toUInt64, UInt32.lt_iff_toNat_lt, apply_ite UInt64.toNat, UInt64.toNat_one,
    UInt64.toNat_zero, decide_eq_true_eq, UInt64.reduceToNat]
  generalize y.toNat * x₀.toNat = p₀ at *
  generalize y.toNat * x₁.toNat = p₁ at *
  generalize z.toNat = Z at *
  generalize c₀.toNat = C₀ at *
  generalize c₁.toNat = C₁ at *
  split <;> lia

/-- The reads, writes and word operations of `UInt32Array`, for the loops of `main`. -/
public instance wordArray32 : MPN.WordArray UInt32Array UInt32 where
  uget a i h := a.uget i h
  uset a i v h := a.uset i v h
  uget_eq a i h := uget_eq_getElem! a i h
  size_uset a i v h := size_uset a i v h
  get_uset a i v h j := getElem!_uset a i v h j
  zeros n := UInt32Array.replicate n 0
  size_zeros n := by show (UInt32Array.replicate n 0).size = n; simp
  val_get_zeros n i := by
    show (UInt32Array.replicate n 0)[i]!.toNat = 0
    rw [UInt32Array.getElem!_eq_getElem!_toArray]
    simp only [UInt32Array.toArray_replicate]
    by_cases hi : i < n
    · simp [hi]
    · simp [hi]; rfl
  val_get_ge a i h := by
    show a[i]!.toNat = 0
    rw [getElem!_neg a i (Nat.not_lt.2 h)]; rfl
  pop a := a.pop
  size_pop a := UInt32Array.size_pop a
  get_pop a i h := by
    replace h : i < a.size - 1 := h
    show a.pop[i]! = a[i]!
    rw [getElem!_eq_getElem _ _ (by rw [UInt32Array.size_pop]; lia),
      getElem!_eq_getElem _ _ (by lia), UInt32Array.getElem_pop]
  extract a i j := a.extract i j
  size_extract a i j := UInt32Array.size_extract a i j
  get_extract a i j k h := by
    replace h : k < (a.extract i j).size := h
    show (a.extract i j)[k]! = a[i + k]!
    rw [getElem!_eq_getElem _ _ h, getElem!_eq_getElem _ _ (by simp at h; lia),
      UInt32Array.getElem_extract]
  zero := 0
  one := 1
  add x y := x + y
  sub x y := x - y
  shl x b := x <<< b
  shr x b := x >>> b
  addh := UInt32.addh
  subh := UInt32.subh
  mul x y := x * y
  mulh := UInt32.mulh
  div2 := UInt32.div2
  div2Rem := UInt32.div2Rem
  mulAdd2 y x z c := y.mulAddAdd x z c
  ltB x y := decide (x < y)
  eqB x y := x == y
  land x y := x &&& y
  lor x y := x ||| y
  xor x y := x ^^^ y
  log2 x := x.log2.toNat
  ofBool b := b.toUInt32
  subMulB z y x h := z.subMulBiased y x h
  unB h := ~~~h
  b0 := 0xFFFFFFFF
  addC x y c := x.addWithCarryWord y c
  -- With `e = y + 2³² - 1 - x ≥ 0`, which does not depend on `c`, the borrow `⌈(y + c - x) / 2³²⌉`
  -- is `(e + c) >>> 32` and the difference is the complement of `e + c`: the carried borrow goes
  -- through one add and one shift per limb. The low word reads `e` again, so that LLVM computes
  -- `e` once instead of adding `c` first.
  subC x y c :=
    let e := y.toUInt64 + 0xFFFFFFFF - x.toUInt64
    (~~~(e.toUInt32 + c), ((e + c.toUInt64) >>> 32).toUInt32)
  addDiffC := UInt32.addDiffStep
  copyIn d o s so n := s.copySlice so d o n
  subMul2B := subMul2W
  isZero x := x == 0
  ofUSize i := i.toUInt32
  wU := 32
  val_zero := rfl
  val_one := rfl
  val_add x y := UInt32.toNat_add x y
  val_sub x y := by
    show (x - y).toNat = (x.toNat + (2 ^ 32 - y.toNat)) % 2 ^ 32
    rw [UInt32.toNat_sub, Nat.add_comm]
  val_shl x b := by
    show (x <<< b).toNat = x.toNat * 2 ^ (b.toNat % 32) % 2 ^ 32
    rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
  val_shr x b := by
    show (x >>> b).toNat = x.toNat / 2 ^ (b.toNat % 32)
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  val_addh := UInt32.toNat_addh
  val_subh := UInt32.toNat_subh
  val_mul x y := UInt32.toNat_mul x y
  val_mulh := UInt32.toNat_mulh
  val_div2 h l d hd := UInt32.toNat_div2 h l d hd
  val_div2Rem h l d hd := UInt32.toNat_div2Rem h l d hd
  val_mulAdd2 y x z c := by
    have := UInt32.mulAddAdd_spec y x z c
    show (y.mulAddAdd x z c).1.toNat + 2 ^ 32 * (y.mulAddAdd x z c).2.toNat =
      y.toNat * x.toNat + z.toNat + c.toNat
    lia
  val_subMulB z y x h := by
    show (z.subMulBiased y x h).1.toNat + y.toNat * x.toNat + (~~~h).toNat =
      z.toNat + 2 ^ 32 * (~~~(z.subMulBiased y x h).2).toNat
    have e : z.subMulBiased y x h = z.subMulBiased y x (~~~(~~~h)) := by
      rw [UInt32.not_not]
    rw [e, UInt32.subMulBiased_not, UInt32.not_not]
    have := UInt32.subMul_spec z y x (~~~h)
    lia
  val_unB_b0 := by decide
  val_addC x y c := by
    show (x.addWithCarryWord y c).1.toNat + 2 ^ 32 * (x.addWithCarryWord y c).2.toNat =
      x.toNat + y.toNat + c.toNat
    have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
    simp only [UInt32.addWithCarryWord, UInt32.toNat_add, UInt64.toNat_add, UInt64.toNat_toUInt32,
      UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    lia
  val_subC x y c := by
    show (~~~((y.toUInt64 + 0xFFFFFFFF - x.toUInt64).toUInt32 + c)).toNat + y.toNat + c.toNat =
      x.toNat + 2 ^ 32 *
        (((y.toUInt64 + 0xFFFFFFFF - x.toUInt64) + c.toUInt64) >>> 32).toUInt32.toNat
    have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
    simp only [UInt32.toNat_not, UInt32.toNat_add, UInt64.toNat_sub, UInt64.toNat_add,
      UInt64.toNat_toUInt32,
      UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    lia
  val_addDiffC v x y z c hc := by
    have := UInt32.addDiffStep_spec v x y z c hc
    show (UInt32.addDiffStep v x y z c).1.toNat + 2 ^ 32 * (UInt32.addDiffStep v x y z c).2.toNat +
        y.toNat + z.toNat + 2 = v.toNat + x.toNat + c.toNat + 2 * 2 ^ 32 ∧
      (UInt32.addDiffStep v x y z c).2.toNat ≤ 3
    exact ⟨by lia, this.2⟩
  size_copyIn d o s so n hd := by
    replace hd : o + n ≤ d.size := hd
    show (s.copySlice so d o n).size = d.size
    rw [UInt32Array.size_copySlice]; lia
  get_copyIn d o s so n i hd hs := by
    replace hd : o + n ≤ d.size := hd
    replace hs : so + n ≤ s.size := hs
    show (s.copySlice so d o n)[i]! = if o ≤ i ∧ i < o + n then s[so + (i - o)]! else d[i]!
    have hm₁ : min o d.size = o := Nat.min_eq_left (by lia)
    have hm₂ : min n (s.size - so) = n := Nat.min_eq_left (by lia)
    by_cases hi : i < d.size
    · rw [getElem!_pos _ i (by rw [UInt32Array.size_copySlice]; lia), UInt32Array.getElem_copySlice]
      simp only [hm₁, hm₂]
      by_cases h₁ : o ≤ i ∧ i < o + n
      · rw [dite_eq_right (by lia), dite_eq_left (by lia), ite_eq_left h₁,
          getElem!_pos s _ (by lia)]
      · rw [ite_eq_right h₁, getElem!_pos d i hi]
        split
        · rfl
        · rw [dite_eq_right (by lia)]
    · rw [getElem!_neg _ i (by rw [UInt32Array.size_copySlice]; lia), getElem!_neg d i hi,
        ite_eq_right (by lia)]
  val_subMul2B := val_subMul2W
  ltB_iff x y := by
    show decide (x < y) = true ↔ x.toNat < y.toNat
    rw [decide_eq_true_iff, UInt32.lt_iff_toNat_lt]
  eqB_iff x y := by
    show (x == y) = true ↔ x.toNat = y.toNat
    rw [beq_iff_eq, UInt32.toNat_inj]
  isZero_iff x := by
    show (x == 0) = true ↔ x.toNat = 0
    rw [beq_iff_eq, ← UInt32.toNat_inj, UInt32.toNat_zero]
  val_ofUSize i := by
    show i.toUInt32.toNat = i.toNat % 2 ^ 32
    rw [USize.toNat_toUInt32]
  toNat_wU := by
    show (32 : USize).toNat = 32
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by cases USize.size_eq <;> simp_all [USize.size])]
  val_land x y := UInt32.toNat_and x y
  val_lor x y := UInt32.toNat_or x y
  val_xor x y := UInt32.toNat_xor x y
  log2_eq x := UInt32.toNat_log2' x
  val_ofBool b := by cases b <;> rfl
  w_ge := by decide

/-- The loop of `foldlInPlace2` from index `k` is `main`'s `foldUInPlace2` from `j₀ + k`. -/
private theorem loop2_eq {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → UInt32 → β → UInt32 × β) (rs xs ys j₀ : USize)
    (hj₀ : j₀ < n) (k : Nat) (hkN : k ≤ (n - j₀).toNat) :
    ∀ (arr : UInt32Array) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
      (hy : LoopBound arr ys n) (hx' hy' hr') (b : β),
      foldlInPlace2.loop (xs + j₀).toNat (ys + j₀).toNat (rs + j₀).toNat (n - j₀).toNat
          (fun k hk => f (j₀ + k) (toNat_shift hj₀ hk).2) arr hx' hy' hr' k b =
        MPN.WordArray.foldUInPlace2 n f arr rs xs ys hr hx hy (j₀ + k.toUSize) b := by
  have hsub : (n - j₀).toNat = n.toNat - j₀.toNat := USize.toNat_sub_of_le _ _ (USize.le_of_lt hj₀)
  have h₀ := USize.lt_iff_toNat_lt.1 hj₀
  have hn := n.toNat_lt_size
  induction hd : (n - j₀).toNat - k generalizing k with
  | zero =>
    intro arr hr hx hy hx' hy' hr' b
    rw [foldlInPlace2.loop, dite_eq_right (by lia), MPN.WordArray.foldUInPlace2]
    rw [dite_eq_right]
    intro hlt
    have := USize.lt_iff_toNat_lt.1 hlt
    rw [USize.toNat_add_of_lt (by rw [toNat_toUSize_of_le hj₀ hkN]; lia),
      toNat_toUSize_of_le hj₀ hkN] at this
    lia
  | succ d ih =>
    intro arr hr hx hy hx' hy' hr' b
    have hk : k < (n - j₀).toNat := by lia
    have hkk := toNat_toUSize_of_le hj₀ (Nat.le_of_lt hk)
    obtain ⟨e, hlt⟩ := toNat_shift hj₀ (k := k.toUSize) (by rw [hkk]; exact hk)
    have off (o : USize) (ho : LoopBound arr o n) :
        (o + (j₀ + k.toUSize)).toNat = (o + j₀).toNat + k := by
      rw [ho.toNat_add hlt, ho.toNat_add hj₀, e, hkk]; lia
    rw [foldlInPlace2.loop, dite_eq_left hk, MPN.WordArray.foldUInPlace2, dite_eq_left hlt]
    simp only [show ∀ (a : UInt32Array) i h, MPN.WordArray.uget a i h = a.uget i h from
        fun _ _ _ => rfl,
      show ∀ (a : UInt32Array) i v h, MPN.WordArray.uset a i v h = a.uset i v h from
        fun _ _ _ _ => rfl]
    have gx := uget_eq_get' arr (xs + (j₀ + k.toUSize)) (hx.uset_bound hlt) _ (off xs hx)
    have gy := uget_eq_get' arr (ys + (j₀ + k.toUSize)) (hy.uset_bound hlt) _ (off ys hy)
    simp only [gx, gy]
    have hnext : j₀ + k.toUSize + 1 = j₀ + (k + 1).toUSize := by
      have hk1 := toNat_toUSize_of_le hj₀ (Nat.succ_le_of_lt hk)
      apply USize.toNat_inj.1
      rw [USize.toNat_add_of_lt (by rw [USize.toNat_one, e]; lia), USize.toNat_one, e,
        USize.toNat_add_of_lt (by rw [hk1]; lia), hk1, hkk]
      lia
    have su := fun v => uset_eq_set' arr (rs + (j₀ + k.toUSize)) v (hr.uset_bound hlt) _ (off rs hr)
    simp only [hnext, su]
    exact ih (k + 1) (by lia) (by lia) _ _ _ _ _ _ _ _

/--
`main`'s `foldUInPlace2Then` by `foldlInPlace2Then` on the windows from `xs + j`, `ys + j`,
`rs + j`.
-/
@[inline, expose] public def foldUInPlace2ThenLib {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → UInt32 → β → UInt32 × β) (arr : UInt32Array)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β → γ) : γ :=
  if h : j < n then
    have hs := USize.toNat_sub_of_le _ _ (USize.le_of_lt h)
    have h₀ := USize.lt_iff_toNat_lt.1 h
    arr.foldlInPlace2Then (xs + j) (ys + j) (rs + j) (n - j)
      (by rw [hx.toNat_add h, hs]; have := hx.1; lia)
      (by rw [hy.toNat_add h, hs]; have := hy.1; lia)
      (by rw [hr.toNat_add h, hs]; have := hr.1; lia) b
      (fun k hk x y b => f (j + k) (toNat_shift h hk).2 x y b) g
  else g arr rfl b


/-- `main`'s plain in-place loop is the one of `UInt32Array`. -/
private theorem foldUInPlace_main {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt32 → β → UInt32 × β) (arr : UInt32Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β) :
    MPN.WordArray.foldUInPlace n f arr rs hr j b = foldUInPlace n f arr rs hr j b := by
  induction arr, hr, j, b using foldUInPlace.induct n f rs with
  | case1 arr hr j b h p ih =>
    rw [MPN.WordArray.foldUInPlace, dite_eq_left_of_eq_true (eq_true h), foldUInPlace_lt _ _ _ _ _ _ _ h]
    exact ih
  | case2 arr hr j b h =>
    rw [MPN.WordArray.foldUInPlace, dite_eq_right_of_eq_false (eq_false h), foldUInPlace_ge _ _ _ _ _ _ _ h]

/--
`main`'s `foldUInPlace2x2Then` as an `inplace` program: each step reads limbs `xs + k` and
`ys + k` and writes limbs `rs + k` and `ts + k`, with both accumulators unboxed, and the program
ends with `then`, so that they reach `g` unboxed too (lean4-scalar-arrays#71 asked for this shape
as a fold, #78 for the `then`).
-/
@[inline, expose] public def foldUInPlace2x2ThenLib {β₁ β₂ γ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → UInt32 → UInt32 → β₁ → UInt32 × β₁)
    (f₂ : (j : USize) → j < n → UInt32 → UInt32 → β₂ → UInt32 × β₂) (arr : UInt32Array)
    (rs ts xs ys : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hx : LoopBound arr xs n) (hy : LoopBound arr ys n) (j : USize) (b₁ : β₁) (b₂ : β₂)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β₁ → β₂ → γ) : γ :=
  have := hr.1; have := ht.1; have := hx.1; have := hy.1
  inplace arr do
    for k in j...n with (c₁ := b₁) (c₂ := b₂) do
      let x ← arr[xs + k]
      let y ← arr[ys + k]
      let (u, d₁) := f₁ k (USize.lt_iff_toNat_lt.2 (by assumption)) x y c₁
      let (v, d₂) := f₂ k (USize.lt_iff_toNat_lt.2 (by assumption)) x y c₂
      arr[rs + k] := u
      arr[ts + k] := v
      c₁ := d₁
      c₂ := d₂
    return (c₁, c₂)
  then fun (c₁, c₂) arr' h => g arr' h c₁ c₂

/-- The loop of `foldUInPlace2x2ThenLib` is `foldUInPlace2x2`, followed by the rest `k`. -/
private theorem run_fold2x2 {β₁ β₂ γ : Type} (n lo : USize)
    (f₁ : (j : USize) → j < n → UInt32 → UInt32 → β₁ → UInt32 × β₁)
    (f₂ : (j : USize) → j < n → UInt32 → UInt32 → β₂ → UInt32 × β₂) (arr₀ : UInt32Array)
    (rs ts xs ys : USize) (hr : LoopBound arr₀ rs n) (ht : LoopBound arr₀ ts n)
    (hx : LoopBound arr₀ xs n) (hy : LoopBound arr₀ ys n)
    (k : β₁ → β₂ → InPlace.Tail arr₀.size γ) :
    ∀ (arr : UInt32Array) (hs : arr.size = arr₀.size) (j : USize) (hlo : lo.toNat ≤ j.toNat)
      (b₁ : β₁) (b₂ : β₂) hr' ht' hx' hy',
      (InPlace.Tail.forIn2From lo n j hlo b₁ b₂ (fun k' _ hk next c₁ c₂ =>
        InPlace.Tail.readThen (xs + k') (hx.uset_bound (USize.lt_iff_toNat_lt.2 hk)) fun x =>
          InPlace.Tail.readThen (ys + k') (hy.uset_bound (USize.lt_iff_toNat_lt.2 hk)) fun y =>
            InPlace.Tail.writeThen (rs + k') (hr.uset_bound (USize.lt_iff_toNat_lt.2 hk))
                (f₁ k' (USize.lt_iff_toNat_lt.2 hk) x y c₁).1
              (InPlace.Tail.writeThen (ts + k') (ht.uset_bound (USize.lt_iff_toNat_lt.2 hk))
                  (f₂ k' (USize.lt_iff_toNat_lt.2 hk) x y c₂).1
                (next (f₁ k' (USize.lt_iff_toNat_lt.2 hk) x y c₁).2
                  (f₂ k' (USize.lt_iff_toNat_lt.2 hk) x y c₂).2))) k).run arr hs =
        (k (MPN.WordArray.foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr' ht' hx' hy' j b₁ b₂).2.1
            (MPN.WordArray.foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr' ht' hx' hy' j b₁ b₂).2.2).run
          (MPN.WordArray.foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr' ht' hx' hy' j b₁ b₂).1
          (Eq.trans (MPN.WordArray.size_foldUInPlace2x2 (A := UInt32Array) ..) hs) := by
  intro arr hs j
  induction hd : n.toNat - j.toNat generalizing arr j with
  | zero =>
    intro hlo b₁ b₂ hr' ht' hx' hy'
    have h : ¬ j < n := fun h => by have := USize.lt_iff_toNat_lt.1 h; lia
    have hf := MPN.WordArray.foldUInPlace2x2.eq_1 n f₁ f₂ arr rs ts xs ys hr' ht' hx' hy' j b₁ b₂
    rw [dite_eq_right_of_eq_false (eq_false h)] at hf
    rw [InPlace.Tail.forIn2From_eq, dite_eq_right_of_eq_false (eq_false h)]
    simp only [hf]
  | succ d ih =>
    intro hlo b₁ b₂ hr' ht' hx' hy'
    have h : j < n := USize.lt_iff_toNat_lt.2 (by lia)
    rw [InPlace.Tail.forIn2From_eq, dite_eq_left_of_eq_true (eq_true h)]
    have hf := MPN.WordArray.foldUInPlace2x2.eq_1 n f₁ f₂ arr rs ts xs ys hr' ht' hx' hy' j b₁ b₂
    rw [dite_eq_left_of_eq_true (eq_true h)] at hf
    simp only [InPlace.Tail.run_readThen, InPlace.Tail.run_writeThen, hf]
    exact ih _ _ _ (by rw [USize.toNat_add_one_of_lt h]; lia) _ _ _ _ _ _ _

/--
Three passes of updates over three windows in one, as an `inplace` program with three loop
variables: `foldUInPlace3Then`.
-/
@[inline, expose] public def foldUInPlace3ThenLib {β₁ β₂ β₃ γ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → UInt32 → β₁ → UInt32 × β₁)
    (f₂ : (j : USize) → j < n → UInt32 → β₂ → UInt32 × β₂)
    (f₃ : (j : USize) → j < n → UInt32 → β₃ → UInt32 × β₃) (arr : UInt32Array)
    (rs ts us : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hu : LoopBound arr us n) (j : USize) (b₁ : β₁) (b₂ : β₂) (b₃ : β₃)
    (g : (arr' : UInt32Array) → arr'.size = arr.size → β₁ → β₂ → β₃ → γ) : γ :=
  have := hr.1; have := ht.1; have := hu.1
  inplace arr do
    for k in j...n with (c₁ := b₁) (c₂ := b₂) (c₃ := b₃) do
      let x ← arr[rs + k]
      let y ← arr[ts + k]
      let z ← arr[us + k]
      let (u, d₁) := f₁ k (USize.lt_iff_toNat_lt.2 (by assumption)) x c₁
      let (v, d₂) := f₂ k (USize.lt_iff_toNat_lt.2 (by assumption)) y c₂
      let (w, d₃) := f₃ k (USize.lt_iff_toNat_lt.2 (by assumption)) z c₃
      arr[rs + k] := u
      arr[ts + k] := v
      arr[us + k] := w
      c₁ := d₁
      c₂ := d₂
      c₃ := d₃
    return (c₁, c₂, c₃)
  then fun (c₁, c₂, c₃) arr' h => g arr' h c₁ c₂ c₃

/-- The loop of `foldUInPlace3ThenLib` is `foldUInPlace3`, followed by the rest `k`. -/
private theorem run_fold3 {β₁ β₂ β₃ γ : Type} (n lo : USize)
    (f₁ : (j : USize) → j < n → UInt32 → β₁ → UInt32 × β₁)
    (f₂ : (j : USize) → j < n → UInt32 → β₂ → UInt32 × β₂)
    (f₃ : (j : USize) → j < n → UInt32 → β₃ → UInt32 × β₃) (arr₀ : UInt32Array)
    (rs ts us : USize) (hr : LoopBound arr₀ rs n) (ht : LoopBound arr₀ ts n)
    (hu : LoopBound arr₀ us n) (k : β₁ → β₂ → β₃ → InPlace.Tail arr₀.size γ) :
    ∀ (arr : UInt32Array) (hs : arr.size = arr₀.size) (j : USize) (hlo : lo.toNat ≤ j.toNat)
      (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) hr' ht' hu',
      (InPlace.Tail.forIn3From lo n j hlo b₁ b₂ b₃ (fun k' _ hk next c₁ c₂ c₃ =>
        InPlace.Tail.readThen (rs + k') (hr.uset_bound (USize.lt_iff_toNat_lt.2 hk)) fun x =>
          InPlace.Tail.readThen (ts + k') (ht.uset_bound (USize.lt_iff_toNat_lt.2 hk)) fun y =>
            InPlace.Tail.readThen (us + k') (hu.uset_bound (USize.lt_iff_toNat_lt.2 hk)) fun z =>
              InPlace.Tail.writeThen (rs + k') (hr.uset_bound (USize.lt_iff_toNat_lt.2 hk)) (f₁ k' (USize.lt_iff_toNat_lt.2 hk) x c₁).1
                (InPlace.Tail.writeThen (ts + k') (ht.uset_bound (USize.lt_iff_toNat_lt.2 hk)) (f₂ k' (USize.lt_iff_toNat_lt.2 hk) y c₂).1
                  (InPlace.Tail.writeThen (us + k') (hu.uset_bound (USize.lt_iff_toNat_lt.2 hk)) (f₃ k' (USize.lt_iff_toNat_lt.2 hk) z c₃).1
                    (next (f₁ k' (USize.lt_iff_toNat_lt.2 hk) x c₁).2 (f₂ k' (USize.lt_iff_toNat_lt.2 hk) y c₂).2
                      (f₃ k' (USize.lt_iff_toNat_lt.2 hk) z c₃).2)))) k).run arr hs =
        (k (MPN.WordArray.foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr' ht' hu' j b₁ b₂ b₃).2.1 (MPN.WordArray.foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr' ht' hu' j b₁ b₂ b₃).2.2.1
            (MPN.WordArray.foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr' ht' hu' j b₁ b₂ b₃).2.2.2).run
          (MPN.WordArray.foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr' ht' hu' j b₁ b₂ b₃).1
          (Eq.trans (MPN.WordArray.size_foldUInPlace3 (A := UInt32Array) ..) hs) := by
  intro arr hs j
  induction hd : n.toNat - j.toNat generalizing arr j with
  | zero =>
    intro hlo b₁ b₂ b₃ hr' ht' hu'
    have h : ¬ j < n := fun h => by have := USize.lt_iff_toNat_lt.1 h; lia
    have hf := MPN.WordArray.foldUInPlace3.eq_1 n f₁ f₂ f₃ arr rs ts us hr' ht' hu' j b₁ b₂ b₃
    rw [dite_eq_right_of_eq_false (eq_false h)] at hf
    rw [InPlace.Tail.forIn3From_eq, dite_eq_right_of_eq_false (eq_false h)]
    simp only [hf]
  | succ d ih =>
    intro hlo b₁ b₂ b₃ hr' ht' hu'
    have h : j < n := USize.lt_iff_toNat_lt.2 (by lia)
    rw [InPlace.Tail.forIn3From_eq, dite_eq_left_of_eq_true (eq_true h)]
    have hf := MPN.WordArray.foldUInPlace3.eq_1 n f₁ f₂ f₃ arr rs ts us hr' ht' hu' j b₁ b₂ b₃
    rw [dite_eq_left_of_eq_true (eq_true h)] at hf
    simp only [InPlace.Tail.run_readThen, InPlace.Tail.run_writeThen, hf]
    exact ih _ _ _ (by rw [USize.toNat_add_one_of_lt h]; lia) _ _ _ _ _ _ _

/-- `main`'s in-place loops on `UInt32Array`, by `foldlInPlaceRangeThen` and `foldlInPlace2Then`. -/
public instance wordFolds32 : MPN.WordFolds UInt32Array UInt32 where
  fold2Then := foldUInPlace2ThenLib
  fold2Then_eq := by
    intro β γ n f arr rs xs ys hr hx hy j b g
    rw [foldUInPlace2ThenLib, MPN.WordArray.foldUInPlace2Then]
    split
    · rename_i h
      rw [foldlInPlace2Then_eq]
      have e := loop2_eq n f rs xs ys j h 0 (Nat.zero_le _) arr hr hx hy
      simp only [show (0 : Nat).toUSize = 0 from rfl, USize.add_zero] at e
      exact g_congr g (Eq.trans rfl (e _ _ _ b)) _
    · rename_i h
      exact (g_congr g (q := (arr, b))
        (by rw [MPN.WordArray.foldUInPlace2, dite_eq_right h]) _).symm
  foldThen := foldUInPlaceThenLib
  foldThen_eq := by
    intro β γ n f arr rs hr j b g
    rw [← foldUInPlaceThen_eq_lib, foldUInPlaceThen, MPN.WordArray.foldUInPlaceThen]
    exact g_congr g (foldUInPlace_main n f arr rs hr j b).symm _
  foldThen2 := foldUInPlaceThen2Lib
  foldThen2_eq := by
    intro β₁ β₂ γ n f arr rs hr j b₁ b₂ g
    rw [foldUInPlaceThen2Lib_eq, ← foldUInPlaceThen_eq_lib, foldUInPlaceThen,
      MPN.WordArray.foldUInPlaceThen]
    exact g_congr (fun arr' h c => g arr' h c.1 c.2)
      (foldUInPlace_main _ (fun j h z c => f j h z c.1 c.2) arr rs hr j (b₁, b₂)).symm _
  fold2x2Then := foldUInPlace2x2ThenLib
  fold2x2Then_eq := by
    intro β₁ β₂ γ n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂ g
    simp only [foldUInPlace2x2ThenLib, runInPlaceThenOf_eq, InPlace.Tail.forIn2_eq]
    rw [run_fold2x2 n j f₁ f₂ arr rs ts xs ys hr ht hx hy _ arr rfl j (Nat.le_refl _) b₁ b₂
      hr ht hx hy]
    simp only [InPlace.Tail.run_done, MPN.WordArray.foldUInPlace2x2Then]
  fold3Then := foldUInPlace3ThenLib
  fold3Then_eq := by
    intro β₁ β₂ β₃ γ n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃ g
    simp only [foldUInPlace3ThenLib, runInPlaceThenOf_eq, InPlace.Tail.forIn3_eq]
    rw [run_fold3 n j f₁ f₂ f₃ arr rs ts us hr ht hu _ arr rfl j (Nat.le_refl _) b₁ b₂ b₃
      hr ht hu]
    simp only [InPlace.Tail.run_done, MPN.WordArray.foldUInPlace3Then]

/-- A sub-slice of a whole array, `toUSlice`. -/
public theorem toUSlice_slice (a : UInt32Array) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ a.size) (ha : a.size < USize.size) :
    (a.toUSlice.slice i j).array = a ∧ (a.toUSlice.slice i j).start.toNat = i.toNat ∧
      (a.toUSlice.slice i j).size.toNat = j.toNat - i.toNat ∧
      (a.toUSlice.slice i j).toNat = a.valAt i.toNat (j.toNat - i.toNat) := by
  have hs := size_toUSlice a ha
  refine ⟨rfl, ?_, a.toUSlice.size_slice hij (by rw [hs]; exact hj), ?_⟩
  · rw [a.toUSlice.start_slice hij (by rw [hs]; exact hj)]; simp
  · rw [a.toUSlice.toNat_slice hij (by rw [hs]; exact hj)]; simp

public theorem toNat_usize (a : UInt32Array) (ha : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp [usize, Nat.mod_eq_of_lt ha]

end ScalarArray.UInt32Array
