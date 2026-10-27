/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray
public import MPN.UInt

/-!
# Addition and subtraction

Like GMP's `mpn` functions, these write their result into the limbs of the slice `r`, in place
when its array is not shared, and return the array and the carry or borrow out. All the slices
have `USize` bounds, so the loops index with `USize`.

* `subN r a b c` is `a - b - c` on the first `n` limbs, where `n` is the least of the sizes of
  `r`, `a` and `b`, like `mpn_sub_n`;
* `addInto r b c` adds `b + c` to the limbs of `r`, like `mpn_add` with the result in place of its
  first operand;
* `zeroInto r` clears the limbs of `r`.

They are `main64`'s, on 32-bit limbs and in the namespace `MPN.U`, and only those that the
flat-array FFT uses; the rest of the library has its own on the library's slices.

The carry and the borrow are words, so they may be any `UInt32`; from a carry or borrow of at most
one, the result is again at most one.
-/

open ScalarArray UInt32Array

namespace MPN.U

/-! ## Steps -/

/-- One limb of `addN`: the low word of `x + y + c` and the carry out. -/
public theorem add_step (x y c : UInt32) :
    (x + y + c).toNat + 2 ^ 32 * (UInt32.addh (UInt32.addh 0 x y) (x + y) c).toNat =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
  simp only [UInt32.toNat_addh, UInt32.toNat_add, UInt32.toNat_zero]
  generalize x.toNat = x at *
  generalize y.toNat = y at *
  generalize c.toNat = c at *
  lia

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

/-- One limb of carry propagation: the low word of `x + c` and the carry out. -/
private theorem add1_step (x c : UInt32) :
    (x + c).toNat + 2 ^ 32 * (UInt32.addh 0 x c).toNat = x.toNat + c.toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt32.toNat_addh, UInt32.toNat_add, UInt32.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  lia

/-! ## Subtraction -/

/-- One limb of `subN`: the low word of `x - y - c` and the borrow out. -/
public theorem sub_step (x y c : UInt32) :
    (x - y - c).toNat + y.toNat + c.toNat =
      x.toNat + 2 ^ 32 * (UInt32.subh (UInt32.subh 0 x y) (x - y) c).toNat := by
  have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
  simp only [UInt32.toNat_subh, UInt32.toNat_sub, UInt32.toNat_zero]
  generalize x.toNat = x at *
  generalize y.toNat = y at *
  generalize c.toNat = c at *
  split <;> split <;> lia

/--
Subtracts limbs `j` to `n - 1` of `b`, and the borrow `c`, from those of `a` into `arr` from
limb `rs + j` on.
-/
public def subNLoop (arr : UInt32Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
    UInt32Array × UInt32 :=
  if h : j < n then
    let x := a[j]'(USize.lt_of_lt_of_le h hn.1)
    let y := b[j]'(USize.lt_of_lt_of_le h hn.2)
    let s := x - y
    subNLoop (arr.uset (rs + j) (s - c) (hr.uset_bound h)) rs a b n hn (hr.of_uset ..) (j + 1)
      (UInt32.subh (UInt32.subh 0 x y) s c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `subNLoop`: limb `j` of `a - b - c`, and the borrow out. -/
@[inline, expose] public def subNStep (a b : USlice) (n : USize) (hn : n ≤ a.size ∧ n ≤ b.size)
    (j : USize) (h : j < n) (_ : UInt32) (c : UInt32) : UInt32 × UInt32 :=
  let x := a[j]'(USize.lt_of_lt_of_le h hn.1)
  let y := b[j]'(USize.lt_of_lt_of_le h hn.2)
  let s := x - y
  (s - c, UInt32.subh (UInt32.subh 0 x y) s c)

private theorem subNLoop_eq_fold (arr : UInt32Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
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
public def subNLoopFast (arr : UInt32Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
    UInt32Array × UInt32 :=
  foldUInPlaceThen n (subNStep a b n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem subNLoop_csimp : @subNLoop = @subNLoopFast := by
  funext arr rs a b n hn hr j c
  rw [subNLoopFast, foldUInPlaceThen_eq, subNLoop_eq_fold]

private theorem subNLoop_spec (arr : UInt32Array) (rs : USize) (a b : USlice) (n : USize)
    (hn : n ≤ a.size ∧ n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
    (subNLoop arr rs a b n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (subNLoop arr rs a b n hn hr j c).1[i]! = arr[i]!) ∧
      (subNLoop arr rs a b n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          b.array.valAt (b.start.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (32 * (n.toNat - j.toNat)) * (subNLoop arr rs a b n hn hr j c).2.toNat := by
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
    simp only [UInt32Array.size_uset] at ih₁
    have hv : (subNLoop (arr.uset (rs + j) (s - c) (hr.uset_bound h)) rs a b n hn (hr.of_uset ..)
        (j + 1) (UInt32.subh (UInt32.subh 0 x y) s c)).1[rs.toNat + j.toNat]! = s - c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt32Array.valAt_succ, UInt32Array.valAt_succ, UInt32Array.valAt_succ, hv,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn.1),
        ← USlice.getElem_eq_getElem! b j (USize.lt_of_lt_of_le h hn.2), Nat.mul_succ, Nat.pow_add]
      have := sub_step x y c
      generalize (subNLoop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (subNLoop _ _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt32.subh _ _ _).toNat = c₁ at *
      generalize 2 ^ (32 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [subNLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/--
Writes the low `n` limbs of `a - b - c` into `r` and returns the borrow out, where `n` is the least
of `r.size`, `a.size` and `b.size`, like GMP's `mpn_sub_n` with a borrow in.
-/
public def subN (r a b : USlice) (c : UInt32 := 0) : UInt32Array × UInt32 :=
  subNLoop r.array r.start a b (min3 a.size b.size r.size) (min3_le r a b) (min3_bound r a b) 0 c

@[simp] public theorem size_subN (r a b : USlice) (c : UInt32) :
    (subN r a b c).1.size = r.array.size :=
  (subNLoop_spec _ _ _ _ _ (min3_le r a b) (min3_bound r a b) 0 c).1

/-- `subN` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_subN (r a b : USlice) (c : UInt32) (i : Nat)
    (hi : i < r.start.toNat ∨
      r.start.toNat + min (min a.size.toNat b.size.toNat) r.size.toNat ≤ i) :
    (subN r a b c).1[i]! = r.array[i]! :=
  (subNLoop_spec _ _ _ _ _ (min3_le r a b) (min3_bound r a b) 0 c).2.1 i
    (by simpa [toNat_min3] using hi)

public theorem valAt_subN (r a b : USlice) (c : UInt32) :
    let n := min (min a.size.toNat b.size.toNat) r.size.toNat
    (subN r a b c).1.valAt r.start.toNat n + b.array.valAt b.start.toNat n + c.toNat =
      a.array.valAt a.start.toNat n + 2 ^ (32 * n) * (subN r a b c).2.toNat := by
  have := (subNLoop_spec r.array r.start a b _ (min3_le r a b) (min3_bound r a b) 0 c).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, toNat_min3] at this
  exact this

/-- `subN` on slices of the same size. -/
public theorem valAt_subN_of_size_eq (r a b : USlice) (c : UInt32) (hab : a.size = b.size)
    (hr : r.size = a.size) :
    (subN r a b c).1.valAt r.start.toNat r.size.toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ (32 * r.size.toNat) * (subN r a b c).2.toNat := by
  have := valAt_subN r a b c
  simp only [← hab, ← hr, Nat.min_self] at this
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt, ← hab, ← hr]
  exact this

/-! ## In place

`addInto r b c` adds `b + c` to the limbs of `r`, like `mpn_add` with the result in place of its
first operand. It reads `r`'s own limbs, so it does not share its array, which would copy it.
-/

/-- Adds limbs `j` to `n - 1` of `b`, and the carry `c`, to the limbs of `arr` from `rs + j` on. -/
public def addNIntoLoop (arr : UInt32Array) (rs : USize) (b : USlice) (n : USize) (hn : n ≤ b.size)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt32) : UInt32Array × UInt32 :=
  if h : j < n then
    let x := arr.uget (rs + j) (hr.uset_bound h)
    let y := b[j]'(USize.lt_of_lt_of_le h hn)
    let s := x + y
    addNIntoLoop (arr.uset (rs + j) (s + c) (hr.uset_bound h)) rs b n hn (hr.of_uset ..) (j + 1)
      (UInt32.addh (UInt32.addh 0 x y) s c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `addNIntoLoop`: limb `x` plus limb `j` of `b` and the carry, and the carry out. -/
@[inline, expose] public def addNIntoStep (b : USlice) (n : USize) (hn : n ≤ b.size) (j : USize)
    (h : j < n) (x : UInt32) (c : UInt32) : UInt32 × UInt32 :=
  let y := b[j]'(USize.lt_of_lt_of_le h hn)
  let s := x + y
  (s + c, UInt32.addh (UInt32.addh 0 x y) s c)

private theorem addNIntoLoop_eq_fold (arr : UInt32Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
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
public def addNIntoLoopFast (arr : UInt32Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) : UInt32Array × UInt32 :=
  foldUInPlaceThen n (addNIntoStep b n hn) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem addNIntoLoop_csimp : @addNIntoLoop = @addNIntoLoopFast := by
  funext arr rs b n hn hr j c
  rw [addNIntoLoopFast, foldUInPlaceThen_eq, addNIntoLoop_eq_fold]

private theorem addNIntoLoop_spec (arr : UInt32Array) (rs : USize) (b : USlice) (n : USize)
    (hn : n ≤ b.size) (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
    (addNIntoLoop arr rs b n hn hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (addNIntoLoop arr rs b n hn hr j c).1[i]! = arr[i]!) ∧
      (addNIntoLoop arr rs b n hn hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (32 * (n.toNat - j.toNat)) * (addNIntoLoop arr rs b n hn hr j c).2.toNat =
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
    simp only [UInt32Array.size_uset] at ih₁
    have hv : (addNIntoLoop (arr.uset (rs + j) (s + c) (hr.uset_bound h)) rs b n hn
        (hr.of_uset ..) (j + 1) (UInt32.addh (UInt32.addh 0 x y) s c)).1[rs.toNat + j.toNat]! =
          s + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (s + c) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt32Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
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
      rw [hk, UInt32Array.valAt_succ, UInt32Array.valAt_succ, UInt32Array.valAt_succ, hv, ← hx,
        ← USlice.getElem_eq_getElem! b j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := add_step x y c
      generalize (addNIntoLoop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addNIntoLoop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt32.addh _ _ _).toNat = c₁ at *
      generalize 2 ^ (32 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [addNIntoLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/-- Adds the carry `c` to limbs `rs + j` to `rs + n - 1` of `arr`. -/
public def add1IntoLoop (arr : UInt32Array) (rs : USize) (n : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt32) : UInt32Array × UInt32 :=
  if h : j < n then
    let x := arr.uget (rs + j) (hr.uset_bound h)
    add1IntoLoop (arr.uset (rs + j) (x + c) (hr.uset_bound h)) rs n (hr.of_uset ..) (j + 1)
      (UInt32.addh 0 x c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `add1IntoLoop`: limb `x` plus the carry, and the carry out. -/
@[inline, expose] public def add1IntoStep (n : USize) (j : USize) (_h : j < n) (x : UInt32)
    (c : UInt32) : UInt32 × UInt32 :=
  (x + c, UInt32.addh 0 x c)

private theorem add1IntoLoop_eq_fold (arr : UInt32Array) (rs : USize) (n : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
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
public def add1IntoLoopFast (arr : UInt32Array) (rs : USize) (n : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt32) : UInt32Array × UInt32 :=
  foldUInPlaceThen n (add1IntoStep n) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem add1IntoLoop_csimp : @add1IntoLoop = @add1IntoLoopFast := by
  funext arr rs n hr j c
  rw [add1IntoLoopFast, foldUInPlaceThen_eq, add1IntoLoop_eq_fold]

public theorem add1IntoLoop_spec (arr : UInt32Array) (rs : USize) (n : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt32) :
    (add1IntoLoop arr rs n hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (add1IntoLoop arr rs n hr j c).1[i]! = arr[i]!) ∧
      (add1IntoLoop arr rs n hr j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (32 * (n.toNat - j.toNat)) * (add1IntoLoop arr rs n hr j c).2.toNat =
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
    simp only [UInt32Array.size_uset] at ih₁
    have hv : (add1IntoLoop (arr.uset (rs + j) (x + c) (hr.uset_bound h)) rs n (hr.of_uset ..)
        (j + 1) (UInt32.addh 0 x c)).1[rs.toNat + j.toNat]! = x + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (x + c) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt32Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
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
      rw [hk, UInt32Array.valAt_succ, UInt32Array.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := add1_step x c
      generalize (add1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (add1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt32.addh _ _ _).toNat = c₁ at *
      generalize arr.valAt _ k = R₀ at *
      generalize 2 ^ (32 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [add1IntoLoop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

private theorem addInto_bound (r b : USlice) (c : UInt32) :
    LoopBound (addNIntoLoop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 c).1 r.start r.size := by
  have := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
  simp only [LoopBound, (addNIntoLoop_spec ..).1] at this ⊢
  exact this

/--
Adds `b + c` to the limbs of `r` and returns the carry out, like GMP's `mpn_add` with the result in
place of its first operand. It requires `b.size ≤ r.size`.
-/
public def addInto (r b : USlice) (c : UInt32 := 0) : UInt32Array × UInt32 :=
  let p := addNIntoLoop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 c
  add1IntoLoop p.1 r.start r.size (addInto_bound r b c) (min b.size r.size) p.2

@[simp] public theorem size_addInto (r b : USlice) (c : UInt32) :
    (addInto r b c).1.size = r.array.size := by
  rw [addInto, (add1IntoLoop_spec ..).1, (addNIntoLoop_spec ..).1]

/-- `addInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_addInto (r b : USlice) (c : UInt32) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (addInto r b c).1[i]! = r.array[i]! := by
  have hm := USize.toNat_min b.size r.size
  rw [addInto, (add1IntoLoop_spec ..).2.1 i (by lia), (addNIntoLoop_spec ..).2.1 i
    (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_addInto (r b : USlice) (c : UInt32) (hb : b.size ≤ r.size) :
    (addInto r b c).1.valAt r.start.toNat r.size.toNat +
        2 ^ (32 * r.size.toNat) * (addInto r b c).2.toNat =
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
    UInt32Array.valAt_congr _ fun i hi _ => hN₂ i (by lia)
  rw [h₆] at h₄
  have h₅ : (addInto r b c).1.valAt r.start.toNat b.size.toNat =
      (addNIntoLoop r.array r.start b _ (USize.min_le_left ..)
        (r.loopBound (USize.min_le_right ..)) 0 c).1.valAt r.start.toNat b.size.toNat :=
    UInt32Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [addInto] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, r.size.toNat = b.size.toNat + k := ⟨r.size.toNat - b.size.toNat, by lia⟩
  rw [show r.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, hk, UInt32Array.valAt_add, UInt32Array.valAt_add, h₅, Nat.mul_add,
    Nat.pow_add]
  generalize (add1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (add1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
  generalize (addNIntoLoop _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (addNIntoLoop _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize r.array.valAt _ k = R₀ at *
  generalize r.array.valAt _ b.size.toNat = L₀ at *
  generalize 2 ^ (32 * b.size.toNat) = P at *
  generalize 2 ^ (32 * k) = Q at *
  grind

/-! ## Clearing -/

/-- The step of `zeroInto`. -/
@[inline, expose] public def zeroStep (n : USize) (j : USize) (_h : j < n) (_x c : UInt32) :
    UInt32 × UInt32 :=
  (0, c)

/-- Clears the limbs of `r`. -/
public def zeroInto (r : USlice) : UInt32Array :=
  foldUInPlaceThen r.size (zeroStep r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0 fun arr _ _ => arr

private theorem zero_spec (n : USize) (arr : UInt32Array) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt32) :
    (foldUInPlace n (zeroStep n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (zeroStep n) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (zeroStep n) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
        (n.toNat - j.toNat) = 0 := by
  induction arr, hr, j, c using foldUInPlace.induct n (zeroStep n) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    simp only [UInt32Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt32Array.valAt_succ, hv, ih₃]
      rfl
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

public theorem zeroInto_spec (r : USlice) :
    (zeroInto r).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) →
        (zeroInto r)[i]! = r.array[i]!) ∧
      (zeroInto r).valAt r.start.toNat r.size.toNat = 0 := by
  rw [zeroInto, foldUInPlaceThen_eq]
  have := zero_spec r.size r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero] at this
  exact this

public theorem valAt_replicate_zero (n lo m : Nat) :
    (UInt32Array.replicate n 0).valAt lo m = 0 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [valAt_succ, ih]
    rw [getElem!_eq_getElem!_data, data_replicate]
    by_cases h : lo < n
    · simp [h]
    · simp [h]; rfl

end MPN.U
