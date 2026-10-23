/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray

/-!
# Addition and subtraction

Like GMP's `mpn` functions, these write their result into the limbs of the slice `r`, in place
when its array is not shared, and return the array and the carry or borrow out. All the slices
have `USize` bounds, so the loops index with `USize`.

* `addN r a b c` and `subN r a b c` are `a + b + c` and `a - b - c` on the first `n` limbs, where
  `n` is the least of the sizes of `r`, `a` and `b`, like `mpn_add_n` and `mpn_sub_n`;
* `add1 r a c` and `sub1 r a c` are `a + c` and `a - c` on the first `min r.size a.size` limbs,
  like `mpn_add_1` and `mpn_sub_1`;
* `add r a b c` and `sub r a b c` are `a + b + c` and `a - b - c` on the first
  `min r.size a.size` limbs, for `b.size ≤ a.size`, like `mpn_add` and `mpn_sub`.

The carry and the borrow are words, so they may be any `UInt64`; from a carry or borrow of at most
one, the result is again at most one.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Addition -/

/-- One limb of `addN`: the low word of `x + y + c` and the carry out. -/
private theorem add_step (x y c : UInt64) :
    (x + y + c).toNat + 2 ^ 64 * (UInt64.addh (UInt64.addh 0 x y) (x + y) c).toNat =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_add, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize y.toNat = y at *
  generalize c.toNat = c at *
  lia

/--
Adds limbs `j` to `n - 1` of `a` and `b`, and the carry `c`, into `arr` from limb `rs + j` on.
-/
public def addNLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    UInt64Array × UInt64 :=
  if h : j < n then
    let x := a[j]'(USize.lt_of_lt_of_le h hn.1)
    let y := b[j]'(USize.lt_of_lt_of_le h hn.2)
    let s := x + y
    addNLoop (arr.uset (rs + j) (s + c) (hr.uset_bound h)) rs a b n hn (hr.of_uset ..) (j + 1)
      (UInt64.addh (UInt64.addh 0 x y) s c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `addNLoop`: limb `j` of `a + b + c`, and the carry out. -/
@[inline, expose] public def addNStep (a b : USlice) (n : USize) (hn : n ≤ a.size ∧ n ≤ b.size)
    (j : USize) (h : j < n) (_ : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let x := a[j]'(USize.lt_of_lt_of_le h hn.1)
  let y := b[j]'(USize.lt_of_lt_of_le h hn.2)
  let s := x + y
  (s + c, UInt64.addh (UInt64.addh 0 x y) s c)

private theorem addNLoop_eq_fold (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    addNLoop arr rs a b n hn hr j c = foldUInPlace n (addNStep a b n hn) arr rs hr j c := by
  induction arr, hr, j, c using addNLoop.induct rs a b n hn with
  | case1 arr hr j c h x y s ih =>
    rw [addNLoop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [addNLoop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `addNLoop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def addNLoopFast (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    UInt64Array × UInt64 :=
  foldUInPlaceThen n (addNStep a b n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem addNLoop_csimp : @addNLoop = @addNLoopFast := by
  funext arr rs a b n hn hr j c
  rw [addNLoopFast, foldUInPlaceThen_eq, addNLoop_eq_fold]

private theorem addNLoop_spec (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (addNLoop arr rs a b n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (addNLoop arr rs a b n hn hr j c).1[i]! = arr[i]!) ∧
      (addNLoop arr rs a b n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (addNLoop arr rs a b n hn hr j c).2.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) +
          b.array.valAt (b.start.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat := by
  induction arr, hr, j, c using addNLoop.induct rs a b n hn with
  | case1 arr hr j c h x y s ih =>
    rw [addNLoop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn.1
    have hnb := USize.le_iff_toNat_le.1 hn.2
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (addNLoop (arr.uset (rs + j) (s + c) (hr.uset_bound h)) rs a b n hn (hr.of_uset ..)
        (j + 1) (UInt64.addh (UInt64.addh 0 x y) s c)).1[rs.toNat + j.toNat]! = s + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn.1),
        ← USlice.getElem_eq_getElem! b j (USize.lt_of_lt_of_le h hn.2), Nat.mul_succ, Nat.pow_add]
      have := add_step x y c
      generalize (addNLoop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addNLoop _ _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [addNLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/-- The least of three sizes. -/
@[inline] def min3 (a b c : USize) : USize := min (min a b) c

private theorem toNat_min3 (a b c : USize) :
    (min3 a b c).toNat = min (min a.toNat b.toNat) c.toNat := by
  simp [min3, USize.toNat_min]

private theorem min3_le (r a b : USlice) :
    min3 a.size b.size r.size ≤ a.size ∧ min3 a.size b.size r.size ≤ b.size :=
  ⟨USize.le_trans (USize.min_le_left ..) (USize.min_le_left ..),
    USize.le_trans (USize.min_le_left ..) (USize.min_le_right ..)⟩

private theorem min3_bound (r a b : USlice) :
    LoopBound r.array r.start (min3 a.size b.size r.size) :=
  r.loopBound (USize.min_le_right ..)

/--
Writes the low `n` limbs of `a + b + c` into `r` and returns the carry out, where `n` is the least
of `r.size`, `a.size` and `b.size`, like GMP's `mpn_add_n` with a carry in.
-/
public def addN (r a b : USlice) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  addNLoop r.array r.start a b (min3 a.size b.size r.size) (min3_le r a b) (min3_bound r a b) 0 c

@[simp] public theorem size_addN (r a b : USlice) (c : UInt64) :
    (addN r a b c).1.size = r.array.size :=
  (addNLoop_spec _ _ _ _ _ (min3_le r a b) (min3_bound r a b) 0 c).1

/-- `addN` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_addN (r a b : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨
      r.start.toNat + min (min a.size.toNat b.size.toNat) r.size.toNat ≤ i) :
    (addN r a b c).1[i]! = r.array[i]! :=
  (addNLoop_spec _ _ _ _ _ (min3_le r a b) (min3_bound r a b) 0 c).2.1 i
    (by simpa [toNat_min3] using hi)

public theorem valAt_addN (r a b : USlice) (c : UInt64) :
    let n := min (min a.size.toNat b.size.toNat) r.size.toNat
    (addN r a b c).1.valAt r.start.toNat n + 2 ^ (64 * n) * (addN r a b c).2.toNat =
      a.array.valAt a.start.toNat n + b.array.valAt b.start.toNat n + c.toNat := by
  have := (addNLoop_spec r.array r.start a b _ (min3_le r a b) (min3_bound r a b) 0 c).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, toNat_min3] at this
  exact this

/-- `addN` on slices of the same size. -/
public theorem valAt_addN_of_size_eq (r a b : USlice) (c : UInt64) (hab : a.size = b.size)
    (hr : r.size = a.size) :
    (addN r a b c).1.valAt r.start.toNat r.size.toNat +
        2 ^ (64 * r.size.toNat) * (addN r a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  have := valAt_addN r a b c
  simp only [← hab, ← hr, Nat.min_self] at this
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt, ← hab, ← hr]
  exact this

/-! ### Carry propagation -/

/-- One limb of `add1`: the low word of `x + c` and the carry out. -/
private theorem add1_step (x c : UInt64) :
    (x + c).toNat + 2 ^ 64 * (UInt64.addh 0 x c).toNat = x.toNat + c.toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_add, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  lia

/-- Adds the carry `c` to limbs `j` to `n - 1` of `a` into `arr` from limb `rs + j` on. -/
public def add1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := a[j]'(USize.lt_of_lt_of_le h hn)
    add1Loop (arr.uset (rs + j) (x + c) (hr.uset_bound h)) rs a n hn (hr.of_uset ..) (j + 1)
      (UInt64.addh 0 x c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `add1Loop`: limb `j` of `a + c`, and the carry out. -/
@[inline, expose] public def add1Step (a : USlice) (n : USize) (hn : n ≤ a.size) (j : USize)
    (h : j < n) (_ : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let x := a[j]'(USize.lt_of_lt_of_le h hn)
  (x + c, UInt64.addh 0 x c)

private theorem add1Loop_eq_fold (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    add1Loop arr rs a n hn hr j c = foldUInPlace n (add1Step a n hn) arr rs hr j c := by
  induction arr, hr, j, c using add1Loop.induct rs a n hn with
  | case1 arr hr j c h =>
    rename_i ih
    rw [add1Loop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [add1Loop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `add1Loop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def add1LoopFast (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (add1Step a n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem add1Loop_csimp : @add1Loop = @add1LoopFast := by
  funext arr rs a n hn hr j c
  rw [add1LoopFast, foldUInPlaceThen_eq, add1Loop_eq_fold]

private theorem add1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (add1Loop arr rs a n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (add1Loop arr rs a n hn hr j c).1[i]! = arr[i]!) ∧
      (add1Loop arr rs a n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (add1Loop arr rs a n hn hr j c).2.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat := by
  induction arr, hr, j, c using add1Loop.induct rs a n hn with
  | case1 arr hr j c h x ih =>
    rw [add1Loop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (add1Loop (arr.uset (rs + j) (x + c) (hr.uset_bound h)) rs a n hn (hr.of_uset ..)
        (j + 1) (UInt64.addh 0 x c)).1[rs.toNat + j.toNat]! = x + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := add1_step x c
      generalize (add1Loop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (add1Loop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [add1Loop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

private theorem min_bound (r : USlice) (n : USize) :
    LoopBound r.array r.start (min n r.size) :=
  r.loopBound (USize.min_le_right ..)

/--
Writes the limbs of `a + c` into `r` and returns the carry out, on the first `min r.size a.size`
limbs, like GMP's `mpn_add_1`.
-/
public def add1 (r a : USlice) (c : UInt64) : UInt64Array × UInt64 :=
  add1Loop r.array r.start a (min a.size r.size) (USize.min_le_left ..) (min_bound r a.size) 0 c

@[simp] public theorem size_add1 (r a : USlice) (c : UInt64) :
    (add1 r a c).1.size = r.array.size :=
  (add1Loop_spec _ _ _ _ (USize.min_le_left ..) (min_bound r a.size) 0 c).1

/-- `add1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_add1 (r a : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (add1 r a c).1[i]! = r.array[i]! :=
  (add1Loop_spec _ _ _ _ (USize.min_le_left ..) (min_bound r a.size) 0 c).2.1 i
    (by simpa [USize.toNat_min] using hi)

public theorem valAt_add1 (r a : USlice) (c : UInt64) (har : a.size ≤ r.size) :
    (add1 r a c).1.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (add1 r a c).2.toNat =
      a.toNat + c.toNat := by
  have := (add1Loop_spec _ _ _ _ (USize.min_le_left ..) (min_bound r a.size) 0 c).2.2
  have h := USize.le_iff_toNat_le.1 har
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, USize.toNat_min,
    show min a.size.toNat r.size.toNat = a.size.toNat by lia] at this
  rw [USlice.toNat_eq_valAt]
  exact this

/-! ### General addition -/

private theorem size_addNLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (addNLoop arr rs a b n hn hr j c).1.size = arr.size :=
  (addNLoop_spec arr rs a b n hn hr j c).1

private theorem add_le (r a b : USlice) :
    min b.size (min a.size r.size) ≤ a.size ∧ min b.size (min a.size r.size) ≤ b.size :=
  ⟨USize.le_trans (USize.min_le_right ..) (USize.min_le_left ..), USize.min_le_left ..⟩

private theorem add_bound (r a b : USlice) :
    LoopBound r.array r.start (min b.size (min a.size r.size)) :=
  r.loopBound (USize.le_trans (USize.min_le_right ..) (USize.min_le_right ..))

private theorem add_bound₁ (r a b : USlice) (c : UInt64) :
    LoopBound (addNLoop r.array r.start a b _ (add_le r a b) (add_bound r a b) 0 c).1 r.start
      (min a.size r.size) := by
  have := min_bound r a.size
  simp only [LoopBound, size_addNLoop] at this ⊢
  exact this

/--
Writes the limbs of `a + b + c` into `r` and returns the carry out, on the first
`min r.size a.size` limbs, like GMP's `mpn_add`. It requires `b.size ≤ a.size`.
-/
public def add (r a b : USlice) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  let p := addNLoop r.array r.start a b _ (add_le r a b) (add_bound r a b) 0 c
  add1Loop p.1 r.start a (min a.size r.size) (USize.min_le_left ..) (add_bound₁ r a b c)
    (min b.size (min a.size r.size)) p.2

@[simp] public theorem size_add (r a b : USlice) (c : UInt64) :
    (add r a b c).1.size = r.array.size := by
  rw [add, (add1Loop_spec ..).1, size_addNLoop]

/-- `add` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_add (r a b : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (add r a b c).1[i]! = r.array[i]! := by
  have hn := USize.toNat_min a.size r.size
  have hm := USize.toNat_min b.size (min a.size r.size)
  rw [hn] at hm
  rw [add, (add1Loop_spec ..).2.1 i (by rw [hn, hm]; lia),
    (addNLoop_spec ..).2.1 i (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_add (r a b : USlice) (c : UInt64) (hba : b.size ≤ a.size)
    (har : a.size ≤ r.size) :
    (add r a b c).1.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (add r a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 hba
  have h₂ := USize.le_iff_toNat_le.1 har
  have hm : (min b.size (min a.size r.size)).toNat = b.size.toNat := by
    rw [USize.toNat_min, USize.toNat_min]; lia
  have hn : (min a.size r.size).toNat = a.size.toNat := by rw [USize.toNat_min]; lia
  have hN := (addNLoop_spec r.array r.start a b _ (add_le r a b) (add_bound r a b) 0 c).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hm] at hN
  obtain ⟨-, h₃, h₄⟩ := add1Loop_spec _ r.start a _ (USize.min_le_left ..) (add_bound₁ r a b c)
    (min b.size (min a.size r.size)) (addNLoop r.array r.start a b _ (add_le r a b)
      (add_bound r a b) 0 c).2
  rw [hm, hn] at h₄
  rw [hm, hn] at h₃
  have h₅ : (add r a b c).1.valAt r.start.toNat b.size.toNat =
      (addNLoop r.array r.start a b _ (add_le r a b) (add_bound r a b) 0 c).1.valAt r.start.toNat
        b.size.toNat :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [add] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, a.size.toNat = b.size.toNat + k := ⟨a.size.toNat - b.size.toNat, by lia⟩
  rw [show a.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt, hk, UInt64Array.valAt_add,
    UInt64Array.valAt_add, h₅, Nat.mul_add, Nat.pow_add]
  generalize (add1Loop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (add1Loop _ _ _ _ _ _ _ _).2.toNat = c' at *
  generalize (addNLoop _ _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (addNLoop _ _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize 2 ^ (64 * b.size.toNat) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

/-! ## Subtraction -/

/-- One limb of `subN`: the low word of `x - y - c` and the borrow out. -/
private theorem sub_step (x y c : UInt64) :
    (x - y - c).toNat + y.toNat + c.toNat =
      x.toNat + 2 ^ 64 * (UInt64.subh (UInt64.subh 0 x y) (x - y) c).toNat := by
  have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_subh, UInt64.toNat_sub, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize y.toNat = y at *
  generalize c.toNat = c at *
  split <;> split <;> lia

/--
Subtracts limbs `j` to `n - 1` of `b`, and the borrow `c`, from those of `a` into `arr` from
limb `rs + j` on.
-/
public def subNLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    UInt64Array × UInt64 :=
  if h : j < n then
    let x := a[j]'(USize.lt_of_lt_of_le h hn.1)
    let y := b[j]'(USize.lt_of_lt_of_le h hn.2)
    let s := x - y
    subNLoop (arr.uset (rs + j) (s - c) (hr.uset_bound h)) rs a b n hn (hr.of_uset ..) (j + 1)
      (UInt64.subh (UInt64.subh 0 x y) s c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `subNLoop`: limb `j` of `a - b - c`, and the borrow out. -/
@[inline, expose] public def subNStep (a b : USlice) (n : USize) (hn : n ≤ a.size ∧ n ≤ b.size)
    (j : USize) (h : j < n) (_ : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let x := a[j]'(USize.lt_of_lt_of_le h hn.1)
  let y := b[j]'(USize.lt_of_lt_of_le h hn.2)
  let s := x - y
  (s - c, UInt64.subh (UInt64.subh 0 x y) s c)

private theorem subNLoop_eq_fold (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    subNLoop arr rs a b n hn hr j c = foldUInPlace n (subNStep a b n hn) arr rs hr j c := by
  induction arr, hr, j, c using subNLoop.induct rs a b n hn with
  | case1 arr hr j c h =>
    rename_i ih
    rw [subNLoop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [subNLoop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `subNLoop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def subNLoopFast (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    UInt64Array × UInt64 :=
  foldUInPlaceThen n (subNStep a b n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem subNLoop_csimp : @subNLoop = @subNLoopFast := by
  funext arr rs a b n hn hr j c
  rw [subNLoopFast, foldUInPlaceThen_eq, subNLoop_eq_fold]

private theorem subNLoop_spec (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (subNLoop arr rs a b n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (subNLoop arr rs a b n hn hr j c).1[i]! = arr[i]!) ∧
      (subNLoop arr rs a b n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          b.array.valAt (b.start.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (subNLoop arr rs a b n hn hr j c).2.toNat := by
  induction arr, hr, j, c using subNLoop.induct rs a b n hn with
  | case1 arr hr j c h x y s ih =>
    rw [subNLoop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn.1
    have hnb := USize.le_iff_toNat_le.1 hn.2
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (subNLoop (arr.uset (rs + j) (s - c) (hr.uset_bound h)) rs a b n hn (hr.of_uset ..)
        (j + 1) (UInt64.subh (UInt64.subh 0 x y) s c)).1[rs.toNat + j.toNat]! = s - c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn.1),
        ← USlice.getElem_eq_getElem! b j (USize.lt_of_lt_of_le h hn.2), Nat.mul_succ, Nat.pow_add]
      have := sub_step x y c
      generalize (subNLoop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (subNLoop _ _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [subNLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/--
Writes the low `n` limbs of `a - b - c` into `r` and returns the borrow out, where `n` is the least
of `r.size`, `a.size` and `b.size`, like GMP's `mpn_sub_n` with a borrow in.
-/
public def subN (r a b : USlice) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  subNLoop r.array r.start a b (min3 a.size b.size r.size) (min3_le r a b) (min3_bound r a b) 0 c

@[simp] public theorem size_subN (r a b : USlice) (c : UInt64) :
    (subN r a b c).1.size = r.array.size :=
  (subNLoop_spec _ _ _ _ _ (min3_le r a b) (min3_bound r a b) 0 c).1

/-- `subN` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_subN (r a b : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨
      r.start.toNat + min (min a.size.toNat b.size.toNat) r.size.toNat ≤ i) :
    (subN r a b c).1[i]! = r.array[i]! :=
  (subNLoop_spec _ _ _ _ _ (min3_le r a b) (min3_bound r a b) 0 c).2.1 i
    (by simpa [toNat_min3] using hi)

public theorem valAt_subN (r a b : USlice) (c : UInt64) :
    let n := min (min a.size.toNat b.size.toNat) r.size.toNat
    (subN r a b c).1.valAt r.start.toNat n + b.array.valAt b.start.toNat n + c.toNat =
      a.array.valAt a.start.toNat n + 2 ^ (64 * n) * (subN r a b c).2.toNat := by
  have := (subNLoop_spec r.array r.start a b _ (min3_le r a b) (min3_bound r a b) 0 c).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, toNat_min3] at this
  exact this

/-- `subN` on slices of the same size. -/
public theorem valAt_subN_of_size_eq (r a b : USlice) (c : UInt64) (hab : a.size = b.size)
    (hr : r.size = a.size) :
    (subN r a b c).1.valAt r.start.toNat r.size.toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ (64 * r.size.toNat) * (subN r a b c).2.toNat := by
  have := valAt_subN r a b c
  simp only [← hab, ← hr, Nat.min_self] at this
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt, ← hab, ← hr]
  exact this

/-! ### Borrow propagation -/

/-- One limb of `sub1`: the low word of `x - c` and the borrow out. -/
private theorem sub1_step (x c : UInt64) :
    (x - c).toNat + c.toNat = x.toNat + 2 ^ 64 * (UInt64.subh 0 x c).toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_subh, UInt64.toNat_sub, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  split <;> lia

/-- Subtracts the borrow `c` from limbs `j` to `n - 1` of `a` into `arr` from limb `rs + j` on. -/
public def sub1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := a[j]'(USize.lt_of_lt_of_le h hn)
    sub1Loop (arr.uset (rs + j) (x - c) (hr.uset_bound h)) rs a n hn (hr.of_uset ..) (j + 1)
      (UInt64.subh 0 x c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `sub1Loop`: limb `j` of `a - c`, and the borrow out. -/
@[inline, expose] public def sub1Step (a : USlice) (n : USize) (hn : n ≤ a.size) (j : USize)
    (h : j < n) (_ : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let x := a[j]'(USize.lt_of_lt_of_le h hn)
  (x - c, UInt64.subh 0 x c)

private theorem sub1Loop_eq_fold (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    sub1Loop arr rs a n hn hr j c = foldUInPlace n (sub1Step a n hn) arr rs hr j c := by
  induction arr, hr, j, c using sub1Loop.induct rs a n hn with
  | case1 arr hr j c h =>
    rename_i ih
    rw [sub1Loop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [sub1Loop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `sub1Loop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def sub1LoopFast (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (sub1Step a n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem sub1Loop_csimp : @sub1Loop = @sub1LoopFast := by
  funext arr rs a n hn hr j c
  rw [sub1LoopFast, foldUInPlaceThen_eq, sub1Loop_eq_fold]

private theorem sub1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (sub1Loop arr rs a n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (sub1Loop arr rs a n hn hr j c).1[i]! = arr[i]!) ∧
      (sub1Loop arr rs a n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          c.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (sub1Loop arr rs a n hn hr j c).2.toNat := by
  induction arr, hr, j, c using sub1Loop.induct rs a n hn with
  | case1 arr hr j c h x ih =>
    rw [sub1Loop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (sub1Loop (arr.uset (rs + j) (x - c) (hr.uset_bound h)) rs a n hn (hr.of_uset ..)
        (j + 1) (UInt64.subh 0 x c)).1[rs.toNat + j.toNat]! = x - c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := sub1_step x c
      generalize (sub1Loop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (sub1Loop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [sub1Loop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/--
Writes the limbs of `a - c` into `r` and returns the borrow out, on the first `min r.size a.size`
limbs, like GMP's `mpn_sub_1`.
-/
public def sub1 (r a : USlice) (c : UInt64) : UInt64Array × UInt64 :=
  sub1Loop r.array r.start a (min a.size r.size) (USize.min_le_left ..) (min_bound r a.size) 0 c

@[simp] public theorem size_sub1 (r a : USlice) (c : UInt64) :
    (sub1 r a c).1.size = r.array.size :=
  (sub1Loop_spec _ _ _ _ (USize.min_le_left ..) (min_bound r a.size) 0 c).1

/-- `sub1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sub1 (r a : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (sub1 r a c).1[i]! = r.array[i]! :=
  (sub1Loop_spec _ _ _ _ (USize.min_le_left ..) (min_bound r a.size) 0 c).2.1 i
    (by simpa [USize.toNat_min] using hi)

public theorem valAt_sub1 (r a : USlice) (c : UInt64) (har : a.size ≤ r.size) :
    (sub1 r a c).1.valAt r.start.toNat a.size.toNat + c.toNat =
      a.toNat + 2 ^ (64 * a.size.toNat) * (sub1 r a c).2.toNat := by
  have := (sub1Loop_spec _ _ _ _ (USize.min_le_left ..) (min_bound r a.size) 0 c).2.2
  have h := USize.le_iff_toNat_le.1 har
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, USize.toNat_min,
    show min a.size.toNat r.size.toNat = a.size.toNat by lia] at this
  rw [USlice.toNat_eq_valAt]
  exact this

/-! ### General subtraction -/

private theorem size_subNLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (subNLoop arr rs a b n hn hr j c).1.size = arr.size :=
  (subNLoop_spec arr rs a b n hn hr j c).1

private theorem sub_le (r a b : USlice) :
    min b.size (min a.size r.size) ≤ a.size ∧ min b.size (min a.size r.size) ≤ b.size :=
  ⟨USize.le_trans (USize.min_le_right ..) (USize.min_le_left ..), USize.min_le_left ..⟩

private theorem sub_bound (r a b : USlice) :
    LoopBound r.array r.start (min b.size (min a.size r.size)) :=
  r.loopBound (USize.le_trans (USize.min_le_right ..) (USize.min_le_right ..))

private theorem sub_bound₁ (r a b : USlice) (c : UInt64) :
    LoopBound (subNLoop r.array r.start a b _ (sub_le r a b) (sub_bound r a b) 0 c).1 r.start
      (min a.size r.size) := by
  have := min_bound r a.size
  simp only [LoopBound, size_subNLoop] at this ⊢
  exact this

/--
Writes the limbs of `a - b - c` into `r` and returns the borrow out, on the first
`min r.size a.size` limbs, like GMP's `mpn_sub`. It requires `b.size ≤ a.size`.
-/
public def sub (r a b : USlice) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  let p := subNLoop r.array r.start a b _ (sub_le r a b) (sub_bound r a b) 0 c
  sub1Loop p.1 r.start a (min a.size r.size) (USize.min_le_left ..) (sub_bound₁ r a b c)
    (min b.size (min a.size r.size)) p.2

@[simp] public theorem size_sub (r a b : USlice) (c : UInt64) :
    (sub r a b c).1.size = r.array.size := by
  rw [sub, (sub1Loop_spec ..).1, size_subNLoop]

/-- `sub` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sub (r a b : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (sub r a b c).1[i]! = r.array[i]! := by
  have hn := USize.toNat_min a.size r.size
  have hm := USize.toNat_min b.size (min a.size r.size)
  rw [hn] at hm
  rw [sub, (sub1Loop_spec ..).2.1 i (by rw [hn, hm]; lia),
    (subNLoop_spec ..).2.1 i (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_sub (r a b : USlice) (c : UInt64) (hba : b.size ≤ a.size)
    (har : a.size ≤ r.size) :
    (sub r a b c).1.valAt r.start.toNat a.size.toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ (64 * a.size.toNat) * (sub r a b c).2.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 hba
  have h₂ := USize.le_iff_toNat_le.1 har
  have hm : (min b.size (min a.size r.size)).toNat = b.size.toNat := by
    rw [USize.toNat_min, USize.toNat_min]; lia
  have hn : (min a.size r.size).toNat = a.size.toNat := by rw [USize.toNat_min]; lia
  have hN := (subNLoop_spec r.array r.start a b _ (sub_le r a b) (sub_bound r a b) 0 c).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hm] at hN
  obtain ⟨-, h₃, h₄⟩ := sub1Loop_spec _ r.start a _ (USize.min_le_left ..) (sub_bound₁ r a b c)
    (min b.size (min a.size r.size)) (subNLoop r.array r.start a b _ (sub_le r a b)
      (sub_bound r a b) 0 c).2
  rw [hm, hn] at h₄
  rw [hm, hn] at h₃
  have h₅ : (sub r a b c).1.valAt r.start.toNat b.size.toNat =
      (subNLoop r.array r.start a b _ (sub_le r a b) (sub_bound r a b) 0 c).1.valAt r.start.toNat
        b.size.toNat :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [sub] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, a.size.toNat = b.size.toNat + k := ⟨a.size.toNat - b.size.toNat, by lia⟩
  rw [show a.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt, hk, UInt64Array.valAt_add,
    UInt64Array.valAt_add, h₅, Nat.mul_add, Nat.pow_add]
  generalize (sub1Loop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (sub1Loop _ _ _ _ _ _ _ _).2.toNat = c' at *
  generalize (subNLoop _ _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (subNLoop _ _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize 2 ^ (64 * b.size.toNat) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

/-! ## In place

`addInto r b c` and `subInto r b c` add `b + c` to the limbs of `r` and subtract `b + c` from them,
like `mpn_add` and `mpn_sub` with the result in place of their first operand. They read `r`'s
own limbs, so they do not share its array, which would copy it.
-/

/-- Adds limbs `j` to `n - 1` of `b`, and the carry `c`, to the limbs of `arr` from `rs + j` on. -/
public def addNIntoLoop (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize) (hn : n ≤ b.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := arr.uget (rs + j) (hr.uset_bound h)
    let y := b[j]'(USize.lt_of_lt_of_le h hn)
    let s := x + y
    addNIntoLoop (arr.uset (rs + j) (s + c) (hr.uset_bound h)) rs b n hn (hr.of_uset ..) (j + 1)
      (UInt64.addh (UInt64.addh 0 x y) s c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `addNIntoLoop`: limb `x` plus limb `j` of `b` and the carry, and the carry out. -/
@[inline, expose] public def addNIntoStep (b : USlice) (n : USize) (hn : n ≤ b.size) (j : USize)
    (h : j < n) (x : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let y := b[j]'(USize.lt_of_lt_of_le h hn)
  let s := x + y
  (s + c, UInt64.addh (UInt64.addh 0 x y) s c)

private theorem addNIntoLoop_eq_fold (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    addNIntoLoop arr rs b n hn hr j c = foldUInPlace n (addNIntoStep b n hn) arr rs hr j c := by
  induction arr, hr, j, c using addNIntoLoop.induct rs b n hn with
  | case1 arr hr j c h =>
    rename_i ih
    rw [addNIntoLoop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [addNIntoLoop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `addNIntoLoop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def addNIntoLoopFast (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (addNIntoStep b n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem addNIntoLoop_csimp : @addNIntoLoop = @addNIntoLoopFast := by
  funext arr rs b n hn hr j c
  rw [addNIntoLoopFast, foldUInPlaceThen_eq, addNIntoLoop_eq_fold]

private theorem addNIntoLoop_spec (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (addNIntoLoop arr rs b n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (addNIntoLoop arr rs b n hn hr j c).1[i]! = arr[i]!) ∧
      (addNIntoLoop arr rs b n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (addNIntoLoop arr rs b n hn hr j c).2.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          b.array.valAt (b.start.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat := by
  induction arr, hr, j, c using addNIntoLoop.induct rs b n hn with
  | case1 arr hr j c h x y s ih =>
    rw [addNIntoLoop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (addNIntoLoop (arr.uset (rs + j) (s + c) (hr.uset_bound h)) rs b n hn
        (hr.of_uset ..) (j + 1) (UInt64.addh (UInt64.addh 0 x y) s c)).1[rs.toNat + j.toNat]! =
          s + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (s + c) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hx : x = arr[rs.toNat + j.toNat]! := by
      show arr.uget (rs + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx,
        ← USlice.getElem_eq_getElem! b j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := add_step x y c
      generalize (addNIntoLoop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addNIntoLoop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [addNIntoLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/-- Adds the carry `c` to limbs `rs + j` to `rs + n - 1` of `arr`. -/
public def add1IntoLoop (arr : UInt64Array) (rs : USize) (n : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := arr.uget (rs + j) (hr.uset_bound h)
    add1IntoLoop (arr.uset (rs + j) (x + c) (hr.uset_bound h)) rs n (hr.of_uset ..) (j + 1)
      (UInt64.addh 0 x c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `add1IntoLoop`: limb `x` plus the carry, and the carry out. -/
@[inline, expose] public def add1IntoStep (n : USize) (j : USize) (_h : j < n) (x : UInt64)
    (c : UInt64) : UInt64 × UInt64 :=
  (x + c, UInt64.addh 0 x c)

private theorem add1IntoLoop_eq_fold (arr : UInt64Array) (rs : USize) (n : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    add1IntoLoop arr rs n hr j c = foldUInPlace n (add1IntoStep n) arr rs hr j c := by
  induction arr, hr, j, c using add1IntoLoop.induct rs n with
  | case1 arr hr j c h =>
    rename_i ih
    rw [add1IntoLoop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [add1IntoLoop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `add1IntoLoop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def add1IntoLoopFast (arr : UInt64Array) (rs : USize) (n : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (add1IntoStep n) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem add1IntoLoop_csimp : @add1IntoLoop = @add1IntoLoopFast := by
  funext arr rs n hr j c
  rw [add1IntoLoopFast, foldUInPlaceThen_eq, add1IntoLoop_eq_fold]

public theorem add1IntoLoop_spec (arr : UInt64Array) (rs : USize) (n : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (add1IntoLoop arr rs n hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (add1IntoLoop arr rs n hr j c).1[i]! = arr[i]!) ∧
      (add1IntoLoop arr rs n hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (add1IntoLoop arr rs n hr j c).2.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat := by
  induction arr, hr, j, c using add1IntoLoop.induct rs n with
  | case1 arr hr j c h x ih =>
    rw [add1IntoLoop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (add1IntoLoop (arr.uset (rs + j) (x + c) (hr.uset_bound h)) rs n (hr.of_uset ..)
        (j + 1) (UInt64.addh 0 x c)).1[rs.toNat + j.toNat]! = x + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (x + c) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hx : x = arr[rs.toNat + j.toNat]! := by
      show arr.uget (rs + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := add1_step x c
      generalize (add1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (add1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize arr.valAt _ k = R₀ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [add1IntoLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

private theorem addInto_bound (r b : USlice) (c : UInt64) :
    LoopBound (addNIntoLoop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).1 r.start r.size := by
  have := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
  simp only [LoopBound, (addNIntoLoop_spec ..).1] at this ⊢
  exact this

/--
Adds `b + c` to the limbs of `r` and returns the carry out, like GMP's `mpn_add` with the result in
place of its first operand. It requires `b.size ≤ r.size`.
-/
public def addInto (r b : USlice) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  let p := addNIntoLoop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 c
  add1IntoLoop p.1 r.start r.size (addInto_bound r b c) (min b.size r.size) p.2

@[simp] public theorem size_addInto (r b : USlice) (c : UInt64) :
    (addInto r b c).1.size = r.array.size := by
  rw [addInto, (add1IntoLoop_spec ..).1, (addNIntoLoop_spec ..).1]

/-- `addInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_addInto (r b : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (addInto r b c).1[i]! = r.array[i]! := by
  have hm := USize.toNat_min b.size r.size
  rw [addInto, (add1IntoLoop_spec ..).2.1 i (by lia), (addNIntoLoop_spec ..).2.1 i
    (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_addInto (r b : USlice) (c : UInt64) (hb : b.size ≤ r.size) :
    (addInto r b c).1.valAt r.start.toNat r.size.toNat +
        2 ^ (64 * r.size.toNat) * (addInto r b c).2.toNat =
      r.array.valAt r.start.toNat r.size.toNat + b.toNat + c.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 hb
  have hm : (min b.size r.size).toNat = b.size.toNat := by rw [USize.toNat_min]; lia
  obtain ⟨-, hN₂, hN⟩ := addNIntoLoop_spec r.array r.start b _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 c
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hm] at hN hN₂
  obtain ⟨-, h₃, h₄⟩ := add1IntoLoop_spec _ r.start r.size (addInto_bound r b c)
    (min b.size r.size) (addNIntoLoop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).2
  rw [hm] at h₄ h₃
  -- The limbs above `b` are still those of `r` when the carry reaches them.
  have h₆ : (addNIntoLoop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).1.valAt (r.start.toNat + b.size.toNat)
        (r.size.toNat - b.size.toNat) =
      r.array.valAt (r.start.toNat + b.size.toNat) (r.size.toNat - b.size.toNat) :=
    UInt64Array.valAt_congr _ fun i hi _ => hN₂ i (by lia)
  rw [h₆] at h₄
  have h₅ : (addInto r b c).1.valAt r.start.toNat b.size.toNat =
      (addNIntoLoop r.array r.start b _ (USize.min_le_left ..)
        (r.loopBound (USize.min_le_right ..)) 0 c).1.valAt r.start.toNat b.size.toNat :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [addInto] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, r.size.toNat = b.size.toNat + k := ⟨r.size.toNat - b.size.toNat, by lia⟩
  rw [show r.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, hk, UInt64Array.valAt_add, UInt64Array.valAt_add, h₅, Nat.mul_add,
    Nat.pow_add]
  generalize (add1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (add1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
  generalize (addNIntoLoop _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (addNIntoLoop _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize r.array.valAt _ k = R₀ at *
  generalize r.array.valAt _ b.size.toNat = L₀ at *
  generalize 2 ^ (64 * b.size.toNat) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

/--
Subtracts limbs `j` to `n - 1` of `b`, and the borrow `c`, from the limbs of `arr` from `rs + j`
on.
-/
public def subNIntoLoop (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize) (hn : n ≤ b.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := arr.uget (rs + j) (hr.uset_bound h)
    let y := b[j]'(USize.lt_of_lt_of_le h hn)
    let s := x - y
    subNIntoLoop (arr.uset (rs + j) (s - c) (hr.uset_bound h)) rs b n hn (hr.of_uset ..) (j + 1)
      (UInt64.subh (UInt64.subh 0 x y) s c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/--
The step of `subNIntoLoop`: limb `x` minus limb `j` of `b` and the borrow, and the borrow out.
-/
@[inline, expose] public def subNIntoStep (b : USlice) (n : USize) (hn : n ≤ b.size) (j : USize)
    (h : j < n) (x : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let y := b[j]'(USize.lt_of_lt_of_le h hn)
  let s := x - y
  (s - c, UInt64.subh (UInt64.subh 0 x y) s c)

private theorem subNIntoLoop_eq_fold (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    subNIntoLoop arr rs b n hn hr j c = foldUInPlace n (subNIntoStep b n hn) arr rs hr j c := by
  induction arr, hr, j, c using subNIntoLoop.induct rs b n hn with
  | case1 arr hr j c h =>
    rename_i ih
    rw [subNIntoLoop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [subNIntoLoop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `subNIntoLoop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def subNIntoLoopFast (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (subNIntoStep b n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem subNIntoLoop_csimp : @subNIntoLoop = @subNIntoLoopFast := by
  funext arr rs b n hn hr j c
  rw [subNIntoLoopFast, foldUInPlaceThen_eq, subNIntoLoop_eq_fold]

private theorem subNIntoLoop_spec (arr : UInt64Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (subNIntoLoop arr rs b n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (subNIntoLoop arr rs b n hn hr j c).1[i]! = arr[i]!) ∧
      (subNIntoLoop arr rs b n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          b.array.valAt (b.start.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (subNIntoLoop arr rs b n hn hr j c).2.toNat := by
  induction arr, hr, j, c using subNIntoLoop.induct rs b n hn with
  | case1 arr hr j c h x y s ih =>
    rw [subNIntoLoop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (subNIntoLoop (arr.uset (rs + j) (s - c) (hr.uset_bound h)) rs b n hn
        (hr.of_uset ..) (j + 1) (UInt64.subh (UInt64.subh 0 x y) s c)).1[rs.toNat + j.toNat]! =
          s - c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (s - c) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hx : x = arr[rs.toNat + j.toNat]! := by
      show arr.uget (rs + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx,
        ← USlice.getElem_eq_getElem! b j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := sub_step x y c
      generalize (subNIntoLoop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (subNIntoLoop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [subNIntoLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/-- Subtracts the borrow `c` from limbs `rs + j` to `rs + n - 1` of `arr`. -/
public def sub1IntoLoop (arr : UInt64Array) (rs : USize) (n : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := arr.uget (rs + j) (hr.uset_bound h)
    sub1IntoLoop (arr.uset (rs + j) (x - c) (hr.uset_bound h)) rs n (hr.of_uset ..) (j + 1)
      (UInt64.subh 0 x c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `sub1IntoLoop`: limb `x` minus the borrow, and the borrow out. -/
@[inline, expose] public def sub1IntoStep (n : USize) (j : USize) (_h : j < n) (x : UInt64)
    (c : UInt64) : UInt64 × UInt64 :=
  (x - c, UInt64.subh 0 x c)

private theorem sub1IntoLoop_eq_fold (arr : UInt64Array) (rs : USize) (n : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    sub1IntoLoop arr rs n hr j c = foldUInPlace n (sub1IntoStep n) arr rs hr j c := by
  induction arr, hr, j, c using sub1IntoLoop.induct rs n with
  | case1 arr hr j c h =>
    rename_i ih
    rw [sub1IntoLoop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [sub1IntoLoop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `sub1IntoLoop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def sub1IntoLoopFast (arr : UInt64Array) (rs : USize) (n : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (sub1IntoStep n) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem sub1IntoLoop_csimp : @sub1IntoLoop = @sub1IntoLoopFast := by
  funext arr rs n hr j c
  rw [sub1IntoLoopFast, foldUInPlaceThen_eq, sub1IntoLoop_eq_fold]

public theorem sub1IntoLoop_spec (arr : UInt64Array) (rs : USize) (n : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (sub1IntoLoop arr rs n hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (sub1IntoLoop arr rs n hr j c).1[i]! = arr[i]!) ∧
      (sub1IntoLoop arr rs n hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (sub1IntoLoop arr rs n hr j c).2.toNat := by
  induction arr, hr, j, c using sub1IntoLoop.induct rs n with
  | case1 arr hr j c h x ih =>
    rw [sub1IntoLoop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (sub1IntoLoop (arr.uset (rs + j) (x - c) (hr.uset_bound h)) rs n (hr.of_uset ..)
        (j + 1) (UInt64.subh 0 x c)).1[rs.toNat + j.toNat]! = x - c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (x - c) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hx : x = arr[rs.toNat + j.toNat]! := by
      show arr.uget (rs + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := sub1_step x c
      generalize (sub1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (sub1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize arr.valAt _ k = R₀ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [sub1IntoLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

private theorem subInto_bound (r b : USlice) (c : UInt64) :
    LoopBound (subNIntoLoop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).1 r.start r.size := by
  have := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
  simp only [LoopBound, (subNIntoLoop_spec ..).1] at this ⊢
  exact this

/--
Subtracts `b + c` from the limbs of `r` and returns the borrow out, like GMP's `mpn_sub` with the
result in place of its first operand. It requires `b.size ≤ r.size`.
-/
public def subInto (r b : USlice) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  let p := subNIntoLoop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 c
  sub1IntoLoop p.1 r.start r.size (subInto_bound r b c) (min b.size r.size) p.2

@[simp] public theorem size_subInto (r b : USlice) (c : UInt64) :
    (subInto r b c).1.size = r.array.size := by
  rw [subInto, (sub1IntoLoop_spec ..).1, (subNIntoLoop_spec ..).1]

/-- `subInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_subInto (r b : USlice) (c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (subInto r b c).1[i]! = r.array[i]! := by
  have hm := USize.toNat_min b.size r.size
  rw [subInto, (sub1IntoLoop_spec ..).2.1 i (by lia), (subNIntoLoop_spec ..).2.1 i
    (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_subInto (r b : USlice) (c : UInt64) (hb : b.size ≤ r.size) :
    (subInto r b c).1.valAt r.start.toNat r.size.toNat + b.toNat + c.toNat =
      r.array.valAt r.start.toNat r.size.toNat +
        2 ^ (64 * r.size.toNat) * (subInto r b c).2.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 hb
  have hm : (min b.size r.size).toNat = b.size.toNat := by rw [USize.toNat_min]; lia
  obtain ⟨-, hN₂, hN⟩ := subNIntoLoop_spec r.array r.start b _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 c
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hm] at hN hN₂
  obtain ⟨-, h₃, h₄⟩ := sub1IntoLoop_spec _ r.start r.size (subInto_bound r b c)
    (min b.size r.size) (subNIntoLoop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).2
  rw [hm] at h₄ h₃
  -- The limbs above `b` are still those of `r` when the borrow reaches them.
  have h₆ : (subNIntoLoop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).1.valAt (r.start.toNat + b.size.toNat)
        (r.size.toNat - b.size.toNat) =
      r.array.valAt (r.start.toNat + b.size.toNat) (r.size.toNat - b.size.toNat) :=
    UInt64Array.valAt_congr _ fun i hi _ => hN₂ i (by lia)
  rw [h₆] at h₄
  have h₅ : (subInto r b c).1.valAt r.start.toNat b.size.toNat =
      (subNIntoLoop r.array r.start b _ (USize.min_le_left ..)
        (r.loopBound (USize.min_le_right ..)) 0 c).1.valAt r.start.toNat b.size.toNat :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [subInto] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, r.size.toNat = b.size.toNat + k := ⟨r.size.toNat - b.size.toNat, by lia⟩
  rw [show r.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, hk, UInt64Array.valAt_add, UInt64Array.valAt_add, h₅, Nat.mul_add,
    Nat.pow_add]
  generalize (sub1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (sub1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
  generalize (subNIntoLoop _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (subNIntoLoop _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize r.array.valAt _ k = R₀ at *
  generalize r.array.valAt _ b.size.toNat = L₀ at *
  generalize 2 ^ (64 * b.size.toNat) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

end MPN
