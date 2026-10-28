/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import ScalarArray.UInt64
public import MPN.UInt
public import MPN.LimbArray

/-!
# Limb arrays

-/

open ScalarArray

/-! ## `UInt32Array` -/

/-! ## `UInt64Array` -/

/-- Arrays of 64-bit limbs, for the limb-width-independent parts of `main`. -/
public instance limbArray64 : MPN.LimbArray UInt64Array UInt64 where
  w := 64
  w_pos := by decide
  size a := a.size
  get a i := a[i]!
  val x := x.toNat
  val_lt x := x.toNat_lt
  set a i v := a.set! i (UInt64.ofNat v)
  size_set a i v := UInt64Array.size_set! ..
  get_set_ne a i v j h := by
    show (a.set! i _)[j]! = a[j]!
    rw [UInt64Array.getElem!_eq_getElem!_data, UInt64Array.getElem!_eq_getElem!_data,
      UInt64Array.data_set!]
    have := a.size_data
    grind
  val_get_set_self a i v h := by
    show (a.set! i _)[i]!.toNat = _
    rw [UInt64Array.getElem!_eq_getElem!_data, UInt64Array.data_set!]
    have := a.size_data
    have : (a.data.set! i (UInt64.ofNat v))[i]! = UInt64.ofNat v := by grind
    rw [this, UInt64.toNat_ofNat']

namespace ScalarArray.UInt64Array

/--
The natural number whose little-endian base `2⁶⁴` limbs are `a[lo], …, a[lo + n - 1]`, where
the limbs past the end of `a` are zero.
-/
@[expose] public def valAt (a : UInt64Array) (lo n : Nat) : Nat := MPN.LimbArray.valAt a lo n

@[simp] public theorem valAt_zero (a : UInt64Array) (lo : Nat) : a.valAt lo 0 = 0 :=
  MPN.LimbArray.valAt_zero a lo

public theorem valAt_succ (a : UInt64Array) (lo n : Nat) :
    a.valAt lo (n + 1) = a[lo]!.toNat + 2 ^ 64 * a.valAt (lo + 1) n :=
  MPN.LimbArray.valAt_succ a lo n

@[simp] public theorem valAt_one (a : UInt64Array) (lo : Nat) : a.valAt lo 1 = a[lo]!.toNat := by
  simp [valAt_succ]

public theorem valAt_lt (a : UInt64Array) (lo n : Nat) : a.valAt lo n < 2 ^ (64 * n) :=
  MPN.LimbArray.valAt_lt a lo n

/-- `valAt` only depends on the limbs it reads. -/
public theorem valAt_congr {a b : UInt64Array} {lo : Nat} (n : Nat)
    (h : ∀ i, lo ≤ i → i < lo + n → a[i]! = b[i]!) : a.valAt lo n = b.valAt lo n :=
  MPN.LimbArray.valAt_congr n h

/-- Splits `valAt` into its low `m` limbs and the `k` limbs above them. -/
public theorem valAt_add (a : UInt64Array) (lo m k : Nat) :
    a.valAt lo (m + k) = a.valAt lo m + 2 ^ (64 * m) * a.valAt (lo + m) k :=
  MPN.LimbArray.valAt_add a lo m k

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

/-! ### Loops over `USize` indices -/

/-- The successor of an index below `n` does not overflow. -/
public theorem _root_.USize.toNat_add_one_of_lt {j n : USize} (h : j < n) :
    (j + 1).toNat = j.toNat + 1 := by
  have := USize.lt_iff_toNat_lt.1 h
  have := n.toNat_lt_size
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  rw [USize.toNat_add_of_lt (a := j) (b := 1) (by rw [USize.toNat_one]; lia), USize.toNat_one]

/--
The bounds of a loop over limbs `rs` to `rs + n - 1` of `arr`: they are limbs of `arr`, and their
indices do not overflow.
-/
public abbrev LoopBound (arr : UInt64Array) (rs n : USize) : Prop :=
  rs.toNat + n.toNat ≤ arr.size ∧ rs.toNat + n.toNat < USize.size

public theorem LoopBound.of_uset {arr : UInt64Array} {rs n : USize} (hr : LoopBound arr rs n)
    (i : USize) (v : UInt64) (h) : LoopBound (arr.uset i v h) rs n := by
  simp only [LoopBound, size_uset] at hr ⊢
  exact hr

public theorem LoopBound.toNat_add {arr : UInt64Array} {rs n j : USize} (hr : LoopBound arr rs n)
    (h : j < n) : (rs + j).toNat = rs.toNat + j.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  exact USize.toNat_add_of_lt (by lia)

public theorem LoopBound.uset_bound {arr : UInt64Array} {rs n j : USize}
    (hr : LoopBound arr rs n) (h : j < n) : (rs + j).toNat < arr.size := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [hr.toNat_add h]
  lia

public theorem uget_eq_getElem! (a : UInt64Array) (i : USize) (h : i.toNat < a.size) :
    a.uget i h = a[i.toNat]! := by
  show a[i] = _
  rw [getElem_usize, getElem!_eq_getElem]

/-- `valAt` does not see a `uset` outside the limbs it reads. -/
public theorem valAt_uset_of (a : UInt64Array) (i : USize) (v : UInt64) (h : i.toNat < a.size)
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
public theorem valAt_mod (a : UInt64Array) (lo : Nat) {m n : Nat} (h : m ≤ n) :
    a.valAt lo m = a.valAt lo n % 2 ^ (64 * m) :=
  MPN.LimbArray.valAt_mod a lo h

/-- The same bounds on another array of the same size, such as the result of writing to `s`. -/
@[inline, expose] public def USlice.reseat (s : USlice) (arr : UInt64Array)
    (h : arr.size = s.array.size) : USlice where
  array := arr
  start := s.start
  stop := s.stop
  start_le_stop := s.start_le_stop
  stop_le_size := h ▸ s.stop_le_size

@[simp] public theorem USlice.array_reseat (s : USlice) (arr : UInt64Array) (h) :
    (s.reseat arr h).array = arr := rfl

@[simp] public theorem USlice.start_reseat (s : USlice) (arr : UInt64Array) (h) :
    (s.reseat arr h).start = s.start := rfl

@[simp] public theorem USlice.size_reseat (s : USlice) (arr : UInt64Array) (h) :
    (s.reseat arr h).size = s.size := rfl

@[simp] public theorem start_toUSlice (a : UInt64Array) : a.toUSlice.start = 0 := rfl

@[simp] public theorem array_toUSlice (a : UInt64Array) : a.toUSlice.array = a := rfl

public theorem size_toUSlice (a : UInt64Array) (h : a.size < USize.size) :
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
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β)
    (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) :
    UInt64Array × β :=
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
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β) (h : j < n) :
    foldUInPlace n f arr rs hr j b =
      foldUInPlace n f (arr.uset (rs + j) (f j h (arr.uget (rs + j) (hr.uset_bound h)) b).1
        (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1)
        (f j h (arr.uget (rs + j) (hr.uset_bound h)) b).2 := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem foldUInPlace_ge {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β) (h : ¬j < n) :
    foldUInPlace n f arr rs hr j b = (arr, b) := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem size_foldUInPlace {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
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
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) : γ :=
  g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..) (foldUInPlace n f arr rs hr j b).2

public theorem foldUInPlaceThen_eq {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) :
    foldUInPlaceThen n f arr rs hr j b g =
      g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..)
        (foldUInPlace n f arr rs hr j b).2 := by
  rw [foldUInPlaceThen]

/-! ### The compiled loops

The loops above are plain recursions of `uget` and `uset`, which the proofs are about. The
compiler runs the in-place folds of lean4-scalar-arrays in their place, through `@[csimp]`
lemmas: the fold over the `USize` range `[rs + j, rs + n)`, with its index shifted by `j`.
-/

private theorem uset_eq_set (a : UInt64Array) (i : USize) (v : UInt64) (h) (m : Nat)
    (hm : i.toNat = m) : a.uset i v h = a.set m v (hm ▸ h) := by
  subst hm; rfl

private theorem uget_eq_get (a : UInt64Array) (i : USize) (h) (m : Nat) (hm : i.toNat = m) :
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
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (rs j₀ : USize) (hj₀ : j₀ < n)
    (N : Nat) (hN : N = (n - j₀).toNat)
    (f' : (k : USize) → k.toNat < N → UInt64 → β → UInt64 × β)
    (hf : ∀ k hk h', f' k hk = f (j₀ + k) h') (k : Nat) (hkN : k ≤ N) :
    ∀ (s : UInt64Array.Slice) (hs : s.size = N) (_ : s.start = (rs + j₀).toNat)
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
      rw [Slice.getElem_eq, uget_eq_get _ _ _ (s.start + k) (by rw [hrs, hst])]
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
    rw [Slice.array_set, uset_eq_set _ _ _ _ (s.start + k) (by rw [hrs, hst])]

/-- `foldUInPlaceThen` by `foldlInPlaceRangeThen` on `[rs + j, rs + n)`. -/
@[inline, expose] public def foldUInPlaceThenLib {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) : γ :=
  if h : j < n then
    arr.foldlInPlaceRangeThen (rs + j) (n - j) (by
        have h₀ := USize.lt_iff_toNat_lt.1 h
        rw [hr.toNat_add h, USize.toNat_sub_of_le _ _ (USize.le_of_lt h)]; lia) b
      (fun k hk x b => f (j + k) (toNat_shift h hk).2 x b) g
  else g arr rfl b

/-- A continuation applied to equal pairs, with the size proof carried along. -/
private theorem g_congr {β γ : Type} {arr : UInt64Array}
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) {p q : UInt64Array × β}
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

/-! ### In-place loops reading the same array

`foldUInPlace2 n f arr rs xs ys hr hx hy j b` is `foldUInPlace` where `f` also receives limbs
`xs + j` and `ys + j` of `arr` itself, read at the time of the step. A function on several windows
of one array, such as the butterflies of the FFT on its flat array, can then read and write them
without a second reference to the array, which would copy it. When each window read starts at or
after the window written, or ends before it, the limbs read are those from before the loop
(`foldUInPlace2_spec`).
-/

/-- Replaces limbs `rs + j` to `rs + n - 1` of `arr` with `f` of limbs `xs + j` and `ys + j`. -/
@[expose] public def foldUInPlace2 {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β)
    (arr : UInt64Array) (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β) : UInt64Array × β :=
  if h : j < n then
    let p := f j h (arr.uget (xs + j) (hx.uset_bound h)) (arr.uget (ys + j) (hy.uset_bound h)) b
    foldUInPlace2 n f (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs xs ys (hr.of_uset ..)
      (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2
  else
    (arr, b)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem size_foldUInPlace2 {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β) (arr : UInt64Array)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β) :
    (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1.size = arr.size := by
  induction arr, hr, hx, hy, j, b using foldUInPlace2.induct n f rs xs ys with
  | case1 arr hr hx hy j b h p ih =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]
    exact ih.trans (size_uset ..)
  | case2 arr hr hx hy j b h =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]

/--
`foldUInPlace2` followed by `g` on the new array and the last accumulator, like
`foldUInPlaceThen`. The compiler runs lean4-scalar-arrays' `foldlInPlace2Then` in its place
(`foldUInPlace2Then_eq_lib`), which makes `arr` exclusive once, then reads and stores without
checks.
-/
@[expose]
public def foldUInPlace2Then {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β) (arr : UInt64Array)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) : γ :=
  g (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (size_foldUInPlace2 ..)
    (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2

public theorem foldUInPlace2Then_eq {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β) (arr : UInt64Array)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) :
    foldUInPlace2Then n f arr rs xs ys hr hx hy j b g =
      g (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (size_foldUInPlace2 ..)
        (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 := by
  rw [foldUInPlace2Then]

/-- The loop of `foldlInPlace2` from index `k` is `foldUInPlace2` from `j₀ + k`. -/
private theorem loop2_eq {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β) (rs xs ys j₀ : USize)
    (hj₀ : j₀ < n) (k : Nat) (hkN : k ≤ (n - j₀).toNat) :
    ∀ (arr : UInt64Array) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
      (hy : LoopBound arr ys n) (hx' hy' hr') (b : β),
      foldlInPlace2.loop (xs + j₀).toNat (ys + j₀).toNat (rs + j₀).toNat (n - j₀).toNat
          (fun k hk => f (j₀ + k) (toNat_shift hj₀ hk).2) arr hx' hy' hr' k b =
        foldUInPlace2 n f arr rs xs ys hr hx hy (j₀ + k.toUSize) b := by
  have hsub : (n - j₀).toNat = n.toNat - j₀.toNat := USize.toNat_sub_of_le _ _ (USize.le_of_lt hj₀)
  have h₀ := USize.lt_iff_toNat_lt.1 hj₀
  have hn := n.toNat_lt_size
  induction hd : (n - j₀).toNat - k generalizing k with
  | zero =>
    intro arr hr hx hy hx' hy' hr' b
    rw [foldlInPlace2.loop, dite_eq_right (by lia), foldUInPlace2]
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
    rw [foldlInPlace2.loop, dite_eq_left hk, foldUInPlace2, dite_eq_left hlt]
    dsimp only
    have gx := uget_eq_get arr (xs + (j₀ + k.toUSize)) (hx.uset_bound hlt) _ (off xs hx)
    have gy := uget_eq_get arr (ys + (j₀ + k.toUSize)) (hy.uset_bound hlt) _ (off ys hy)
    simp only [gx, gy]
    have hnext : j₀ + k.toUSize + 1 = j₀ + (k + 1).toUSize := by
      have hk1 := toNat_toUSize_of_le hj₀ (Nat.succ_le_of_lt hk)
      apply USize.toNat_inj.1
      rw [USize.toNat_add_of_lt (by rw [USize.toNat_one, e]; lia), USize.toNat_one, e,
        USize.toNat_add_of_lt (by rw [hk1]; lia), hk1, hkk]
      lia
    have su := fun v => uset_eq_set arr (rs + (j₀ + k.toUSize)) v (hr.uset_bound hlt) _ (off rs hr)
    simp only [hnext, su]
    exact ih (k + 1) (by lia) (by lia) _ _ _ _ _ _ _ _

/-- `foldUInPlace2Then` by `foldlInPlace2Then` on the windows from `xs + j`, `ys + j`, `rs + j`. -/
@[inline, expose] public def foldUInPlace2ThenLib {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β) (arr : UInt64Array)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) : γ :=
  if h : j < n then
    have hs := USize.toNat_sub_of_le _ _ (USize.le_of_lt h)
    have h₀ := USize.lt_iff_toNat_lt.1 h
    arr.foldlInPlace2Then (xs + j) (ys + j) (rs + j) (n - j)
      (by rw [hx.toNat_add h, hs]; have := hx.1; lia)
      (by rw [hy.toNat_add h, hs]; have := hy.1; lia)
      (by rw [hr.toNat_add h, hs]; have := hr.1; lia) b
      (fun k hk x y b => f (j + k) (toNat_shift h hk).2 x y b) g
  else g arr rfl b

@[csimp] public theorem foldUInPlace2Then_eq_lib :
    @foldUInPlace2Then = @foldUInPlace2ThenLib := by
  funext β γ n f arr rs xs ys hr hx hy j b g
  rw [foldUInPlace2Then, foldUInPlace2ThenLib]
  split
  · rename_i h
    rw [foldlInPlace2Then_eq]
    have e := loop2_eq n f rs xs ys j h 0 (Nat.zero_le _) arr hr hx hy
    simp only [show (0 : Nat).toUSize = 0 from rfl, USize.add_zero] at e
    exact (g_congr g (Eq.trans rfl (e _ _ _ b)) _).symm
  · rename_i h
    exact g_congr g (q := (arr, b)) (by rw [foldUInPlace2, dite_eq_right h]) _

/--
`foldUInPlace2Then` as an intermediate result: the array and the accumulator of the loop, and the
size proof that `g` receives, as variables. Proofs about a chain of loops go through this, so
that the later loops mention variables, not the earlier loops.
-/
public theorem foldUInPlace2Then_cases {β γ : Type} {n : USize}
    {f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β} {arr : UInt64Array}
    {rs xs ys : USize} {hr : LoopBound arr rs n} {hx : LoopBound arr xs n}
    {hy : LoopBound arr ys n} {j : USize} {b : β}
    {g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ} {R : γ}
    (h : foldUInPlace2Then n f arr rs xs ys hr hx hy j b g = R) :
    ∃ a, ∃ ha : a.size = arr.size, ∃ c,
      foldUInPlace2 n f arr rs xs ys hr hx hy j b = (a, c) ∧ g a ha c = R := by
  rw [foldUInPlace2Then_eq] at h
  exact ⟨_, _, _, rfl, h⟩

/--
The value of `foldUInPlace2` for a step with a linear carry law: if every step turns limbs `x`,
`y` and the accumulator `c` into a limb `out` and an accumulator `c'` with
`out + 2⁶⁴ P c' + ux x + uy y + Q c = vx x + vy y + 2⁶⁴ Q c' + P c` and keeps the invariant `I`
of the accumulator, then the limbs written and the last accumulator satisfy the same law with the
values of the windows, as long as the windows read are not overwritten before they are read. `P`
is a carry and `Q` a borrow.
-/
public theorem foldUInPlace2_spec {β : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → UInt64 → β → UInt64 × β) (P Q : β → Nat)
    (ux uy vx vy : Nat) (I : β → Prop) (inv : ∀ j h x y c, I c → I (f j h x y c).2)
    (law : ∀ j h x y c, I c → (f j h x y c).1.toNat + 2 ^ 64 * P (f j h x y c).2 + ux * x.toNat +
      uy * y.toNat + Q c = vx * x.toNat + vy * y.toNat + 2 ^ 64 * Q (f j h x y c).2 + P c)
    (arr : UInt64Array) (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n)
    (hdx : rs.toNat ≤ xs.toNat ∨ xs.toNat + n.toNat ≤ rs.toNat)
    (hdy : rs.toNat ≤ ys.toNat ∨ ys.toNat + n.toNat ≤ rs.toNat) (j : USize) (b : β) (hb : I b) :
    (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1.size = arr.size ∧
      I (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1[i]! = arr[i]!) ∧
      (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
        2 ^ (64 * (n.toNat - j.toNat)) * P (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 +
        ux * arr.valAt (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        uy * arr.valAt (ys.toNat + j.toNat) (n.toNat - j.toNat) + Q b =
      vx * arr.valAt (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        vy * arr.valAt (ys.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (64 * (n.toNat - j.toNat)) * Q (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 +
        P b := by
  induction arr, hr, hx, hy, j, b using foldUInPlace2.induct n f rs xs ys with
  | case1 arr hr hx hy j b h p ih =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]
    have hI := inv j h (arr.uget (xs + j) (hx.uset_bound h)) (arr.uget (ys + j) (hy.uset_bound h))
      b hb
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    have hxi := hx.toNat_add h
    have hyi := hy.toNat_add h
    obtain ⟨ih₁, ih₀, ih₂, ih₃⟩ := ih hI
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (foldUInPlace2 n f (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2).1[rs.toNat + j.toNat]! =
          p.1 := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hri]
    have hX : (arr.uset (rs + j) p.1 (hr.uset_bound h)).valAt (xs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hY : (arr.uset (rs + j) p.1 (hr.uset_bound h)).valAt (ys.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hx' : arr.uget (xs + j) (hx.uset_bound h) = arr[xs.toNat + j.toNat]! := by
      rw [uget_eq_getElem!, hxi]
    have hy' : arr.uget (ys + j) (hy.uset_bound h) = arr[ys.toNat + j.toNat]! := by
      rw [uget_eq_getElem!, hyi]
    refine ⟨ih₁, ih₀, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hri]
      split <;> lia
    · rw [hX, hY] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc,
        ← Nat.add_assoc] at ih₃
      have hl := law j h (arr.uget (xs + j) (hx.uset_bound h)) (arr.uget (ys + j) (hy.uset_bound h))
        b hb
      rw [hx', hy'] at hl
      rw [hk, valAt_succ, valAt_succ, valAt_succ, hv, Nat.mul_succ, Nat.pow_add]
      show _ + _ * P (foldUInPlace2 n f (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2).2 + _ + _ + _ = _
      generalize (foldUInPlace2 n f (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2) = q at *
      simp only [p] at *
      generalize f j h arr[xs.toNat + j.toNat]! arr[ys.toNat + j.toNat]! b = p' at *
      generalize q.1.valAt _ _ = R at *
      generalize arr.valAt (xs.toNat + j.toNat + 1) k = X at *
      generalize arr.valAt (ys.toNat + j.toNat + 1) k = Y at *
      generalize 2 ^ (64 * k) = B at *
      grind
  | case2 arr hr hx hy j b h =>
    rw [foldUInPlace2]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this, Nat.add_comm, hb]

/-- A sub-slice of a whole array, `toUSlice`. -/
public theorem toUSlice_slice (a : UInt64Array) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ a.size) (ha : a.size < USize.size) :
    (a.toUSlice.slice i j).array = a ∧ (a.toUSlice.slice i j).start.toNat = i.toNat ∧
      (a.toUSlice.slice i j).size.toNat = j.toNat - i.toNat ∧
      (a.toUSlice.slice i j).toNat = a.valAt i.toNat (j.toNat - i.toNat) := by
  have hs := size_toUSlice a ha
  refine ⟨rfl, ?_, a.toUSlice.size_slice hij (by rw [hs]; exact hj), ?_⟩
  · rw [a.toUSlice.start_slice hij (by rw [hs]; exact hj)]; simp
  · rw [a.toUSlice.toNat_slice hij (by rw [hs]; exact hj)]; simp

public theorem toNat_usize (a : UInt64Array) (ha : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp [usize, Nat.mod_eq_of_lt ha]

end ScalarArray.UInt64Array
