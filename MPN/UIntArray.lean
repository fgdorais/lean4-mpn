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
    a.valAt lo m = a.valAt lo n % 2 ^ (64 * m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by lia⟩
  rw [valAt_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (valAt_lt ..)]

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

@[specialize]
private unsafe def foldUInPlaceThenImpl {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → UInt64 → β → UInt64 × β) (arr : UInt64Array) (rs : USize)
    (_ : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : UInt64Array) → arr'.size = arr.size → β → γ) : γ :=
  loop (ensureExclusiveUnsafe arr) j b
where
  @[specialize] loop (a : UInt64Array) (j : USize) (b : β) : γ :=
    if j < n then
      let p := f j lcProof (a.uget (rs + j) lcProof) b
      loop (setUnsafe a (rs + j) p.1) (j + 1) p.2
    else
      g a lcProof b

/--
`foldUInPlace` followed by `g` on the new array and the last accumulator, which the loop calls
itself instead of returning a pair. `g` also receives a proof that the size is unchanged. The
implementation makes `arr` exclusive once, before the loop, which then stores without checks.
-/
@[implemented_by foldUInPlaceThenImpl]
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

end ScalarArray.UInt64Array
