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
def addNLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
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
def add1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
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
def subNLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (n : USize)
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
def sub1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
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

end MPN
