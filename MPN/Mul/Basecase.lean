/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray

/-!
# Schoolbook multiplication

Like GMP's `mpn` functions, these write their result into the limbs of the slice `r`, in place
when its array is not shared. All the slices have `USize` bounds, so the loops index with `USize`.

* `mul1 r a x c` writes the low limbs of `a * x + c` and returns the high limb, like `mpn_mul_1`;
* `addMul1 r a x c` adds `a * x + c` to the limbs of `r` and returns the carry out, like
  `mpn_addmul_1`;

both on the first `min r.size a.size` limbs, and

* `mulBasecase r a b` writes the `a.size + b.size` limbs of `a * b`, like `mpn_mul_basecase`. It
  requires `0 < b.size` and `a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.

`mulBasecase` writes the first row with `mul1`, then adds the rows two at a time, like GMP's
`mpn_addmul_2`: one pass over `a` adds `a (b[i] + β b[i + 1])` (`addMul2Loop`), with two carries,
so that each limb of the result is read and written once for two products of limbs. The pass runs
on lean4-scalar-arrays' `foldlInPlaceRangeWith2AccThen`, which keeps both carries unboxed; an odd
last row is a pass of `addMul1Loop`.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Multiplication by a limb -/

/-- One limb of `mul1`: the low word of `y * x + c` and the high word. -/
private theorem mul1_step (y x c : UInt64) :
    (y * x + c).toNat + 2 ^ 64 * (UInt64.addh (y.mulh x) (y * x) c).toNat =
      y.toNat * x.toNat + c.toNat := by
  have : y.toNat * x.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x.toNat_lt; lia)
  have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add, UInt64.toNat_mul]
  generalize y.toNat * x.toNat = p at *
  generalize c.toNat = c at *
  lia

/--
Writes limbs `j` to `n - 1` of `a * x`, plus the carry `c`, into `arr` from limb `rs + j` on.
-/
public def mul1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let y := a[j]'(USize.lt_of_lt_of_le h hn)
    let p := y * x
    mul1Loop (arr.uset (rs + j) (p + c) (hr.uset_bound h)) rs a n hn (hr.of_uset ..) x (j + 1)
      (UInt64.addh (y.mulh x) p c)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- The step of `mul1Loop`: limb `j` of `a * x` plus the carry, and the high word. -/
@[inline, expose] public def mul1Step (a : USlice) (n : USize) (hn : n ≤ a.size) (x : UInt64)
    (j : USize) (h : j < n) (_ : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let y := a[j]'(USize.lt_of_lt_of_le h hn)
  let p := y * x
  (p + c, UInt64.addh (y.mulh x) p c)

private theorem mul1Loop_eq_fold (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    mul1Loop arr rs a n hn hr x j c = foldUInPlace n (mul1Step a n hn x) arr rs hr j c := by
  induction arr, hr, j, c using mul1Loop.induct rs a n hn x with
  | case1 arr hr j c h =>
    rename_i ih
    rw [mul1Loop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [mul1Loop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `mul1Loop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def mul1LoopFast (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen n (mul1Step a n hn x) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem mul1Loop_csimp : @mul1Loop = @mul1LoopFast := by
  funext arr rs a n hn hr x j c
  rw [mul1LoopFast, foldUInPlaceThen_eq, mul1Loop_eq_fold]

public theorem mul1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    (mul1Loop arr rs a n hn hr x j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (mul1Loop arr rs a n hn hr x j c).1[i]! = arr[i]!) ∧
      (mul1Loop arr rs a n hn hr x j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (mul1Loop arr rs a n hn hr x j c).2.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) * x.toNat + c.toNat := by
  induction arr, hr, j, c using mul1Loop.induct rs a n hn x with
  | case1 arr hr j c h y p ih =>
    rw [mul1Loop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (mul1Loop (arr.uset (rs + j) (p + c) (hr.uset_bound h)) rs a n hn (hr.of_uset ..)
        x (j + 1) (UInt64.addh (y.mulh x) p c)).1[rs.toNat + j.toNat]! = p + c := by
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
      have := mul1_step y x c
      generalize (mul1Loop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (mul1Loop _ _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize a.array.valAt _ k = A at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [mul1Loop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/--
Writes the low limbs of `a * x + c` into `r` and returns the high limb, on the first
`min r.size a.size` limbs, like GMP's `mpn_mul_1`.
-/
public def mul1 (r a : USlice) (x : UInt64) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  mul1Loop r.array r.start a (min a.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 c

@[simp] public theorem size_mul1 (r a : USlice) (x c : UInt64) :
    (mul1 r a x c).1.size = r.array.size :=
  (mul1Loop_spec ..).1

/-- `mul1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mul1 (r a : USlice) (x c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (mul1 r a x c).1[i]! = r.array[i]! :=
  (mul1Loop_spec ..).2.1 i (by simpa [USize.toNat_min] using hi)

public theorem valAt_mul1 (r a : USlice) (x c : UInt64) (har : a.size ≤ r.size) :
    (mul1 r a x c).1.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (mul1 r a x c).2.toNat =
      a.toNat * x.toNat + c.toNat := by
  have := (mul1Loop_spec r.array r.start a _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 c).2.2
  have h := USize.le_iff_toNat_le.1 har
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, USize.toNat_min,
    show min a.size.toNat r.size.toNat = a.size.toNat by lia] at this
  rw [USlice.toNat_eq_valAt]
  exact this

/-! ## Adding a product by a limb -/

/-- One limb of `addMul1`: the low word of `z + y * x + c` and the high word. -/
private theorem addMul1_step (z y x c : UInt64) :
    (y * x + c + z).toNat +
        2 ^ 64 * (UInt64.addh (UInt64.addh (y.mulh x) (y * x) c) (y * x + c) z).toNat =
      z.toNat + y.toNat * x.toNat + c.toNat := by
  have : y.toNat * x.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x.toNat_lt; lia)
  have := c.toNat_lt; have := z.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add, UInt64.toNat_mul]
  generalize y.toNat * x.toNat = p at *
  generalize c.toNat = c at *
  generalize z.toNat = z at *
  lia

/--
Adds limbs `j` to `n - 1` of `a * x`, plus the carry `c`, to the limbs of `arr` from limb
`rs + j` on.
-/
public def addMul1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let y := a[j]'(USize.lt_of_lt_of_le h hn)
    let z := arr.uget (rs + j) (hr.uset_bound h)
    let p := y * x
    let t := p + c
    addMul1Loop (arr.uset (rs + j) (t + z) (hr.uset_bound h)) rs a n hn (hr.of_uset ..) x (j + 1)
      (UInt64.addh (UInt64.addh (y.mulh x) p c) t z)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/--
The step of `addMul1Loop`: limb `z` plus limb `j` of `a * x` plus the carry, and the high word.
-/
@[inline, expose] public def addMul1Step (a : USlice) (n : USize) (hn : n ≤ a.size) (x : UInt64)
    (j : USize) (h : j < n) (z : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let y := a[j]'(USize.lt_of_lt_of_le h hn)
  let p := y * x
  let t := p + c
  (t + z, UInt64.addh (UInt64.addh (y.mulh x) p c) t z)

private theorem addMul1Loop_eq_fold (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    addMul1Loop arr rs a n hn hr x j c = foldUInPlace n (addMul1Step a n hn x) arr rs hr j c := by
  induction arr, hr, j, c using addMul1Loop.induct rs a n hn x with
  | case1 arr hr j c h =>
    rename_i ih
    rw [addMul1Loop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [addMul1Loop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `addMul1Loop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def addMul1LoopFast (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    UInt64Array × UInt64 :=
  foldUInPlaceThen n (addMul1Step a n hn x) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem addMul1Loop_csimp : @addMul1Loop = @addMul1LoopFast := by
  funext arr rs a n hn hr x j c
  rw [addMul1LoopFast, foldUInPlaceThen_eq, addMul1Loop_eq_fold]

public theorem addMul1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    (addMul1Loop arr rs a n hn hr x j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (addMul1Loop arr rs a n hn hr x j c).1[i]! = arr[i]!) ∧
      (addMul1Loop arr rs a n hn hr x j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (addMul1Loop arr rs a n hn hr x j c).2.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) * x.toNat + c.toNat := by
  induction arr, hr, j, c using addMul1Loop.induct rs a n hn x with
  | case1 arr hr j c h y z p t ih =>
    rw [addMul1Loop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (addMul1Loop (arr.uset (rs + j) (t + z) (hr.uset_bound h)) rs a n hn (hr.of_uset ..)
        x (j + 1) (UInt64.addh (UInt64.addh (y.mulh x) p c) t z)).1[rs.toNat + j.toNat]! =
          t + z := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (t + z) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hz : z = arr[rs.toNat + j.toNat]! := by
      show arr.uget (rs + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hz,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := addMul1_step z y x c
      generalize (addMul1Loop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addMul1Loop _ _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize arr.valAt _ k = R₀ at *
      generalize a.array.valAt _ k = A at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [addMul1Loop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/--
Adds `a * x + c` to the limbs of `r` and returns the carry out, on the first `min r.size a.size`
limbs, like GMP's `mpn_addmul_1`.
-/
public def addMul1 (r a : USlice) (x : UInt64) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  addMul1Loop r.array r.start a (min a.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 c

@[simp] public theorem size_addMul1 (r a : USlice) (x c : UInt64) :
    (addMul1 r a x c).1.size = r.array.size :=
  (addMul1Loop_spec ..).1

/-- `addMul1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_addMul1 (r a : USlice) (x c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (addMul1 r a x c).1[i]! = r.array[i]! :=
  (addMul1Loop_spec ..).2.1 i (by simpa [USize.toNat_min] using hi)

public theorem valAt_addMul1 (r a : USlice) (x c : UInt64) (har : a.size ≤ r.size) :
    (addMul1 r a x c).1.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (addMul1 r a x c).2.toNat =
      r.array.valAt r.start.toNat a.size.toNat + a.toNat * x.toNat + c.toNat := by
  have := (addMul1Loop_spec r.array r.start a _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 c).2.2
  have h := USize.le_iff_toNat_le.1 har
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, USize.toNat_min,
    show min a.size.toNat r.size.toNat = a.size.toNat by lia] at this
  rw [USlice.toNat_eq_valAt]
  exact this

/-! ## Subtracting a product by a limb -/

/-- One limb of `subMul1`: the low word of `z - y * x - c` and the borrow out. -/
private theorem subMul1_step (z y x c : UInt64) :
    (z - (y * x + c)).toNat + y.toNat * x.toNat + c.toNat =
      z.toNat + 2 ^ 64 * (UInt64.subh (UInt64.addh (y.mulh x) (y * x) c) z (y * x + c)).toNat := by
  have : y.toNat * x.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x.toNat_lt; lia)
  have := c.toNat_lt; have := z.toNat_lt
  simp only [UInt64.toNat_subh, UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add,
    UInt64.toNat_sub, UInt64.toNat_mul]
  generalize y.toNat * x.toNat = p at *
  generalize c.toNat = c at *
  generalize z.toNat = z at *
  split <;> lia

/--
Subtracts limbs `j` to `n - 1` of `a * x`, plus the borrow `c`, from the limbs of `arr` from limb
`rs + j` on.
-/
public def subMul1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let y := a[j]'(USize.lt_of_lt_of_le h hn)
    let z := arr.uget (rs + j) (hr.uset_bound h)
    let p := y * x
    let t := p + c
    subMul1Loop (arr.uset (rs + j) (z - t) (hr.uset_bound h)) rs a n hn (hr.of_uset ..) x (j + 1)
      (UInt64.subh (UInt64.addh (y.mulh x) p c) z t)
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/--
The step of `subMul1Loop`: limb `z` minus limb `j` of `a * x` and the borrow, and the borrow out.
-/
@[inline, expose] public def subMul1Step (a : USlice) (n : USize) (hn : n ≤ a.size) (x : UInt64)
    (j : USize) (h : j < n) (z : UInt64) (c : UInt64) : UInt64 × UInt64 :=
  let y := a[j]'(USize.lt_of_lt_of_le h hn)
  let p := y * x
  let t := p + c
  (z - t, UInt64.subh (UInt64.addh (y.mulh x) p c) z t)

public theorem subMul1Loop_eq_fold (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    subMul1Loop arr rs a n hn hr x j c = foldUInPlace n (subMul1Step a n hn x) arr rs hr j c := by
  induction arr, hr, j, c using subMul1Loop.induct rs a n hn x with
  | case1 arr hr j c h =>
    rename_i ih
    rw [subMul1Loop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [subMul1Loop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

/-- `subMul1Loop` with `foldUInPlaceThen`, which checks that `arr` is exclusive once. -/
public def subMul1LoopFast (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    UInt64Array × UInt64 :=
  foldUInPlaceThen n (subMul1Step a n hn x) arr rs hr j c fun arr' _ c => (arr', c)

@[csimp] public theorem subMul1Loop_csimp : @subMul1Loop = @subMul1LoopFast := by
  funext arr rs a n hn hr x j c
  rw [subMul1LoopFast, foldUInPlaceThen_eq, subMul1Loop_eq_fold]

public theorem subMul1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    (subMul1Loop arr rs a n hn hr x j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (subMul1Loop arr rs a n hn hr x j c).1[i]! = arr[i]!) ∧
      (subMul1Loop arr rs a n hn hr x j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) * x.toNat + c.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (subMul1Loop arr rs a n hn hr x j c).2.toNat := by
  induction arr, hr, j, c using subMul1Loop.induct rs a n hn x with
  | case1 arr hr j c h y z p t ih =>
    rw [subMul1Loop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hna := USize.le_iff_toNat_le.1 hn
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (subMul1Loop (arr.uset (rs + j) (z - t) (hr.uset_bound h)) rs a n hn (hr.of_uset ..)
        x (j + 1) (UInt64.subh (UInt64.addh (y.mulh x) p c) z t)).1[rs.toNat + j.toNat]! =
          z - t := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) (z - t) (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hz : z = arr[rs.toNat + j.toNat]! := by
      show arr.uget (rs + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hz,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have := subMul1_step z y x c
      generalize (subMul1Loop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (subMul1Loop _ _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize arr.valAt _ k = R₀ at *
      generalize a.array.valAt _ k = A at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [subMul1Loop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/--
Subtracts `a * x + c` from the limbs of `r` and returns the borrow out, on the first
`min r.size a.size` limbs, like GMP's `mpn_submul_1`.
-/
public def subMul1 (r a : USlice) (x : UInt64) (c : UInt64 := 0) : UInt64Array × UInt64 :=
  subMul1Loop r.array r.start a (min a.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 c

@[simp] public theorem size_subMul1 (r a : USlice) (x c : UInt64) :
    (subMul1 r a x c).1.size = r.array.size :=
  (subMul1Loop_spec ..).1

/-- `subMul1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_subMul1 (r a : USlice) (x c : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (subMul1 r a x c).1[i]! = r.array[i]! :=
  (subMul1Loop_spec ..).2.1 i (by simpa [USize.toNat_min] using hi)

public theorem valAt_subMul1 (r a : USlice) (x c : UInt64) (har : a.size ≤ r.size) :
    (subMul1 r a x c).1.valAt r.start.toNat a.size.toNat + a.toNat * x.toNat + c.toNat =
      r.array.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (subMul1 r a x c).2.toNat := by
  have := (subMul1Loop_spec r.array r.start a _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 c).2.2
  have h := USize.le_iff_toNat_le.1 har
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, USize.toNat_min,
    show min a.size.toNat r.size.toNat = a.size.toNat by lia] at this
  rw [USlice.toNat_eq_valAt]
  exact this

/-! ## Adding a product by two limbs -/

/--
One limb of `addMul2`: the low word of `z + y (x₀ + β x₁) + c₀ + β c₁`, and the two words above
it, the new carries. The sum is below `β³`, so nothing is lost.
-/
@[inline, expose] public def addMul2Word (z y x₀ x₁ c₀ c₁ : UInt64) : UInt64 × UInt64 × UInt64 :=
  let lo₀ := y * x₀
  let lo₁ := y * x₁
  let s := z + lo₀
  let h₁ := UInt64.addh (y.mulh x₀) z lo₀
  let h₂ := UInt64.addh h₁ s c₀
  let t := h₂ + lo₁
  (s + c₀, t + c₁, UInt64.addh (UInt64.addh (y.mulh x₁) h₂ lo₁) t c₁)

private theorem addMul2_word (z y x₀ x₁ c₀ c₁ : UInt64) :
    (addMul2Word z y x₀ x₁ c₀ c₁).1.toNat +
        2 ^ 64 * ((addMul2Word z y x₀ x₁ c₀ c₁).2.1.toNat +
          2 ^ 64 * (addMul2Word z y x₀ x₁ c₀ c₁).2.2.toNat) =
      z.toNat + y.toNat * (x₀.toNat + 2 ^ 64 * x₁.toNat) + c₀.toNat + 2 ^ 64 * c₁.toNat := by
  have h₀ : y.toNat * x₀.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x₀.toNat_lt; lia)
  have h₁ : y.toNat * x₁.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x₁.toNat_lt; lia)
  have := c₀.toNat_lt; have := c₁.toNat_lt; have := z.toNat_lt
  simp only [addMul2Word, UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add,
    UInt64.toNat_mul]
  rw [Nat.mul_add y.toNat, show y.toNat * (2 ^ 64 * x₁.toNat) = 2 ^ 64 * (y.toNat * x₁.toNat) by
    grind]
  generalize y.toNat * x₀.toNat = p at *
  generalize y.toNat * x₁.toNat = q at *
  generalize c₀.toNat = c at *
  generalize c₁.toNat = d at *
  generalize z.toNat = z at *
  lia

/--
The step of `addMul2Loop`: limb `z` plus limb `j` of `a (x₀ + β x₁)` plus the carries, and the two
words above.
-/
@[inline, expose] public def addMul2Step (a : USlice) (n : USize) (hn : n ≤ a.size)
    (x₀ x₁ : UInt64) (j : USize) (h : j < n) (z : UInt64) (c : UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 :=
  addMul2Word z (a[j]'(USize.lt_of_lt_of_le h hn)) x₀ x₁ c.1 c.2

/--
Adds limbs `j` to `n - 1` of `a (x₀ + β x₁)`, plus the carries `c.1 + β c.2`, to the limbs of `arr`
from limb `rs + j` on: two rows of a product in one pass, like GMP's `mpn_addmul_2`.
-/
public def addMul2Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size)
    (hr : LoopBound arr rs n) (x₀ x₁ : UInt64) (j : USize) (c : UInt64 × UInt64) :
    UInt64Array × UInt64 × UInt64 :=
  if h : j < n then
    let p := addMul2Step a n hn x₀ x₁ j h (arr.uget (rs + j) (hr.uset_bound h)) c
    addMul2Loop (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs a n hn (hr.of_uset ..) x₀ x₁ (j + 1)
      p.2
  else
    (arr, c)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

private theorem addMul2Loop_eq_fold (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x₀ x₁ : UInt64) (j : USize)
    (c : UInt64 × UInt64) :
    addMul2Loop arr rs a n hn hr x₀ x₁ j c =
      foldUInPlace n (addMul2Step a n hn x₀ x₁) arr rs hr j c := by
  induction arr, hr, j, c using addMul2Loop.induct rs a n hn x₀ x₁ with
  | case1 arr hr j c h =>
    rename_i ih
    rw [addMul2Loop, foldUInPlace_lt _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]
    exact ih
  | case2 arr hr j c h =>
    rw [addMul2Loop, foldUInPlace_ge _ _ _ _ _ _ _ h]
    simp only [h, ↓reduceDIte]

public theorem addMul2Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x₀ x₁ : UInt64) (j : USize)
    (c : UInt64 × UInt64) :
    (addMul2Loop arr rs a n hn hr x₀ x₁ j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (addMul2Loop arr rs a n hn hr x₀ x₁ j c).1[i]! = arr[i]!) ∧
      (addMul2Loop arr rs a n hn hr x₀ x₁ j c).1.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            ((addMul2Loop arr rs a n hn hr x₀ x₁ j c).2.1.toNat +
              2 ^ 64 * (addMul2Loop arr rs a n hn hr x₀ x₁ j c).2.2.toNat) =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) *
            (x₀.toNat + 2 ^ 64 * x₁.toNat) + c.1.toNat + 2 ^ 64 * c.2.toNat := by
  induction arr, hr, j, c using addMul2Loop.induct rs a n hn x₀ x₁ with
  | case1 arr hr j c h p ih =>
    rw [addMul2Loop]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (addMul2Loop (arr.uset (rs + j) p.1 (hr.uset_bound h)) rs a n hn (hr.of_uset ..)
        x₀ x₁ (j + 1) p.2).1[rs.toNat + j.toNat]! = p.1 := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (rs + j) p.1 (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hz : arr.uget (rs + j) (hr.uset_bound h) = arr[rs.toNat + j.toNat]! := by
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        Nat.mul_succ, Nat.pow_add]
      have hw := addMul2_word (arr.uget (rs + j) (hr.uset_bound h))
        (a[j]'(USize.lt_of_lt_of_le h hn)) x₀ x₁ c.1 c.2
      rw [hz, USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn)] at hw
      have hp : p = addMul2Word arr[rs.toNat + j.toNat]! a.array[a.start.toNat + j.toNat]! x₀ x₁
          c.1 c.2 := by
        show addMul2Word _ _ _ _ _ _ = _
        rw [hz, USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn)]
      rw [← hp] at hw
      generalize (addMul2Loop _ _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addMul2Loop _ _ _ _ _ _ _ _ _ _).2.1.toNat = d₀ at *
      generalize (addMul2Loop _ _ _ _ _ _ _ _ _ _).2.2.toNat = d₁ at *
      generalize p.1.toNat = w at *
      generalize p.2.1.toNat = e₀ at *
      generalize p.2.2.toNat = e₁ at *
      generalize arr.valAt _ k = R₀ at *
      generalize a.array.valAt _ k = A at *
      generalize arr[rs.toNat + j.toNat]!.toNat = z at *
      generalize a.array[a.start.toNat + j.toNat]!.toNat = y at *
      generalize x₀.toNat + 2 ^ 64 * x₁.toNat = X at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [addMul2Loop]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/-! ## Schoolbook multiplication -/

/-- The bounds of `mulBasecaseLoop`: limbs `rs` to `rs + m + n - 1` of `arr`, without overflow. -/
public abbrev MulBound (arr : UInt64Array) (rs : USize) (m n : Nat) : Prop :=
  rs.toNat + m + n ≤ arr.size ∧ rs.toNat + m + n < USize.size

private theorem MulBound.toNat_row {arr : UInt64Array} {rs : USize} {a b : USlice}
    (hr : MulBound arr rs a.size.toNat b.size.toNat) {i : USize} (h : i < b.size) :
    (rs + i).toNat = rs.toNat + i.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  exact USize.toNat_add_of_lt (by lia)

private theorem MulBound.toNat_top {arr : UInt64Array} {rs : USize} {a b : USlice}
    (hr : MulBound arr rs a.size.toNat b.size.toNat) {i : USize} (h : i < b.size) :
    (rs + i + a.size).toNat = rs.toNat + i.toNat + a.size.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_of_lt (by rw [hr.toNat_row h]; lia), hr.toNat_row h]

private theorem MulBound.row {arr : UInt64Array} {rs : USize} {a b : USlice}
    (hr : MulBound arr rs a.size.toNat b.size.toNat) {i : USize} (h : i < b.size) :
    LoopBound arr (rs + i) a.size := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [LoopBound, hr.toNat_row h]
  constructor <;> lia

public theorem size_addMul1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    (addMul1Loop arr rs a n hn hr x j c).1.size = arr.size :=
  (addMul1Loop_spec ..).1

public theorem size_mul1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (n : USize)
    (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64) :
    (mul1Loop arr rs a n hn hr x j c).1.size = arr.size :=
  (mul1Loop_spec ..).1

/--
Adds rows `i` to `b.size - 1` of `a * b` to the limbs of `arr`, row `i` from limb `rs + i` on,
and stores the carry out of each row in the limb above it.
-/
def mulBasecaseLoop (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) : UInt64Array :=
  if h : i < b.size then
    let p := addMul1Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
      (hr.row h) b[i] 0 0
    mulBasecaseLoop (p.1.uset (rs + i + a.size) p.2 (by
        rw [size_addMul1Loop, hr.toNat_top h]
        have := USize.lt_iff_toNat_lt.1 h
        lia))
      rs a b (by simp only [MulBound, size_uset, p, size_addMul1Loop]; exact hr) (i + 1)
  else
    arr
termination_by b.size.toNat - i.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/--
`addMul1Loop` passing the array and the carry to a continuation `k` instead of returning a pair,
through `foldUInPlaceThen`: the compiler specializes the loop to each `k`, so that the carry stays
unboxed and nothing is allocated, and the array is made exclusive once. `k` receives a proof that
the array still has its size `S`.
-/
@[inline, expose] public def addMul1LoopK {β : Type} (S : Nat) (arr : UInt64Array)
    (hS : arr.size = S)
    (rs : USize) (a : USlice) (n : USize) (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64)
    (j : USize) (c : UInt64) (k : (arr' : UInt64Array) → arr'.size = S → UInt64 → β) : β :=
  foldUInPlaceThen n (addMul1Step a n hn x) arr rs hr j c fun arr' h' c => k arr' (h'.trans hS) c

public theorem addMul1LoopK_eq {β : Type} (S : Nat) (arr : UInt64Array) (rs : USize) (a : USlice)
    (n : USize) (hn : n ≤ a.size) (hr : LoopBound arr rs n) (x : UInt64) (j : USize) (c : UInt64)
    (k : (arr' : UInt64Array) → arr'.size = S → UInt64 → β) (hS : arr.size = S)
    (hk : (addMul1Loop arr rs a n hn hr x j c).1.size = S) :
    addMul1LoopK S arr hS rs a n hn hr x j c k =
      k (addMul1Loop arr rs a n hn hr x j c).1 hk (addMul1Loop arr rs a n hn hr x j c).2 := by
  rw [addMul1LoopK, foldUInPlaceThen_eq]
  simp only [addMul1Loop_eq_fold]

/--
One row of `mulBasecaseLoop` by `addMul1LoopK`: the carry goes to its limb inside the
continuation, so that it is never boxed, and the row returns the array with its size.
-/
@[inline] def mulRowK (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) (h : i < b.size) :
    {arr' : UInt64Array // arr'.size = arr.size} :=
  addMul1LoopK arr.size arr rfl (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
    (hr.row h) b[i] 0 0 fun arr' h' c =>
      ⟨arr'.uset (rs + i + a.size) c (by
          rw [h', hr.toNat_top h]
          have := USize.lt_iff_toNat_lt.1 h
          lia), by rw [size_uset, h']⟩

private theorem mulRowK_eq (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) (h : i < b.size) :
    (mulRowK arr rs a b hr i h).1 =
      (addMul1Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h)
        b[i] 0 0).1.uset (rs + i + a.size)
        (addMul1Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h)
          b[i] 0 0).2 (by
          rw [size_addMul1Loop, hr.toNat_top h]
          have := USize.lt_iff_toNat_lt.1 h
          lia) := by
  rw [mulRowK, addMul1LoopK_eq (hk := size_addMul1Loop ..)]

/-! ### Two rows per pass -/

private theorem ite_ne {α : Type} {k m : Nat} (x y : α) (h : k ≠ m) :
    (if k = m then x else y) = y := by simp [h]

private theorem ite_eq' {α : Type} {k m : Nat} (x y : α) (h : k = m) :
    (if k = m then x else y) = x := by simp [h]

private theorem MulBound.toNat_top₂ {arr : UInt64Array} {rs : USize} {a b : USlice}
    (hr : MulBound arr rs a.size.toNat b.size.toNat) {i : USize} (h : i < b.size)
    (h' : i + 1 < b.size) :
    (rs + i + a.size + 1).toNat = rs.toNat + i.toNat + a.size.toNat + 1 := by
  have := USize.lt_iff_toNat_lt.1 h'
  rw [USize.toNat_add_one_of_lt h] at this
  rw [USize.toNat_add_of_lt (by rw [hr.toNat_top h, USize.toNat_one]; lia), hr.toNat_top h,
    USize.toNat_one]

/-- The two carries of a pair of rows into the two limbs above it. -/
@[inline] def storeCarries (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) (h : i < b.size)
    (h' : i + 1 < b.size) (arr' : UInt64Array) (hs : arr'.size = arr.size) (c₀ c₁ : UInt64) :
    {arr'' : UInt64Array // arr''.size = arr.size} :=
  have h₁ := USize.lt_iff_toNat_lt.1 h'
  have h₀ := USize.toNat_add_one_of_lt h
  ⟨(arr'.uset (rs + i + a.size) c₀ (by rw [hs, hr.toNat_top h]; lia)).uset (rs + i + a.size + 1) c₁
      (by rw [size_uset, hs, hr.toNat_top₂ h h']; lia),
    by rw [size_uset, size_uset, hs]⟩

/--
Rows `i` and `i + 1` of `a * b` added to the limbs of `arr` from `rs + i` on in one pass of
`foldlInPlaceRangeWith2AccThen`, whose two carries stay unboxed, and the carries stored above
them by the continuation.
-/
@[inline] def mulRow2K (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) (h : i < b.size)
    (h' : i + 1 < b.size) : {arr' : UInt64Array // arr'.size = arr.size} :=
  have hb := hr.row h
  let x₀ := b[i]'h
  let x₁ := b[i + 1]'h'
  if h₀ : (0 : USize) < a.size then
    arr.foldlInPlaceRangeWith2AccThen (rs + i + 0) (a.size - 0) (by
        have h₀' := USize.lt_iff_toNat_lt.1 h₀
        rw [hb.toNat_add h₀, USize.toNat_sub_of_le _ _ (USize.le_of_lt h₀)]; lia) 0 0
      (fun k hk z c₀ c₁ => addMul2Step a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
        x₀ x₁ (0 + k) (toNat_shift h₀ hk).2 z (c₀, c₁))
      (fun arr' hs c₀ c₁ => storeCarries arr rs a b hr i h h' arr' hs c₀ c₁)
  else storeCarries arr rs a b hr i h h' arr rfl 0 0

private theorem mulRow2K_eq (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) (h : i < b.size)
    (h' : i + 1 < b.size) :
    (mulRow2K arr rs a b hr i h h').1 =
      (storeCarries arr rs a b hr i h h'
        (addMul2Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h)
          (b[i]'h) (b[i + 1]'h') 0 (0, 0)).1
        (by rw [(addMul2Loop_spec ..).1])
        (addMul2Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h)
          (b[i]'h) (b[i + 1]'h') 0 (0, 0)).2.1
        (addMul2Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h)
          (b[i]'h) (b[i + 1]'h') 0 (0, 0)).2.2).1 := by
  have e : mulRow2K arr rs a b hr i h h' =
      foldUInPlaceThen a.size (addMul2Step a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
        (b[i]'h) (b[i + 1]'h')) arr (rs + i) (hr.row h) 0 (0, 0)
        (fun arr' hs c => storeCarries arr rs a b hr i h h' arr' hs c.1 c.2) := by
    rw [foldUInPlaceThen_eq_lib]
    simp only [mulRow2K, foldUInPlaceThenLib, foldlInPlaceRangeWith2AccThen_eq]
  rw [e, foldUInPlaceThen_eq]
  simp only [addMul2Loop_eq_fold]

/--
`mulBasecaseLoop` two rows at a time by `mulRow2K`, and the last row by `mulRowK` when the rows
left are odd.
-/
def mulBasecaseLoop2 (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) : UInt64Array :=
  if h : i < b.size then
    if h' : i + 1 < b.size then
      let p := mulRow2K arr rs a b hr i h h'
      mulBasecaseLoop2 p.1 rs a b (by simp only [MulBound, p.2]; exact hr) (i + 1 + 1)
    else
      (mulRowK arr rs a b hr i h).1
  else
    arr
termination_by b.size.toNat - i.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h'
  rw [USize.toNat_add_one_of_lt h', USize.toNat_add_one_of_lt h] at *
  lia

private theorem mulBound_of (r a b : USlice) (h : a.size ≤ r.size ∧ b.size ≤ r.size - a.size) :
    MulBound r.array r.start a.size.toNat b.size.toNat := by
  have := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
  have := USize.le_iff_toNat_le.1 h.1
  have := USize.le_iff_toNat_le.1 h.2
  rw [USize.toNat_sub_of_le _ _ h.1] at this
  rw [LoopBound] at *
  constructor <;> lia

/--
Writes the `a.size + b.size` limbs of `a * b` into `r`, like GMP's `mpn_mul_basecase`. It
requires `0 < b.size` and `a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def mulBasecase (r a b : USlice) : UInt64Array :=
  if h : 0 < b.size ∧ a.size ≤ r.size ∧ b.size ≤ r.size - a.size then
    let hr := mulBound_of r a b h.2
    let p := mul1Loop r.array r.start a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
      (r.loopBound h.2.1) (b[(0 : USize)]'h.1) 0 0
    mulBasecaseLoop2 (p.1.uset (r.start + a.size) p.2 (by
        rw [size_mul1Loop, USize.toNat_add_of_lt (by lia)]
        have := USize.lt_iff_toNat_lt.1 h.1
        lia))
      r.start a b (by simp only [MulBound, size_uset, p, size_mul1Loop]; exact hr) 1
  else
    r.array

private theorem mulBasecaseLoop_spec (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) :
    (mulBasecaseLoop arr rs a b hr i).size = arr.size ∧
      (∀ k, (k < rs.toNat + i.toNat ∨ rs.toNat + a.size.toNat + b.size.toNat ≤ k) →
        (mulBasecaseLoop arr rs a b hr i)[k]! = arr[k]!) ∧
      (i.toNat ≤ b.size.toNat →
        (mulBasecaseLoop arr rs a b hr i).valAt rs.toNat (a.size.toNat + b.size.toNat) =
          arr.valAt rs.toNat (a.size.toNat + i.toNat) +
            2 ^ (64 * i.toNat) *
              (a.toNat * b.array.valAt (b.start.toNat + i.toNat) (b.size.toNat - i.toNat))) := by
  induction arr, hr, i using mulBasecaseLoop.induct rs a b with
  | case1 arr hr i h p ih =>
    rw [mulBasecaseLoop]
    simp only [h, ↓reduceDIte]
    have hi := USize.lt_iff_toNat_lt.1 h
    have hi₁ := USize.toNat_add_one_of_lt h
    have hrow := hr.toNat_row h
    have htop := hr.toNat_top h
    obtain ⟨hp₁, hp₂, hp₃⟩ := addMul1Loop_spec arr (rs + i) a a.size
      (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h) b[i] 0 0
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero, hrow] at hp₂ hp₃
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hi₁] at ih₂ ih₃
    simp only [size_uset] at ih₁
    replace ih₁ := ih₁.trans hp₁
    refine ⟨ih₁, fun k hk => ?_, fun _ => ?_⟩
    · rw [ih₂ k (by lia), getElem!_uset, htop]
      simp only [show ¬(rs.toNat + i.toNat + a.size.toNat = k) by lia, ↓reduceIte]
      exact hp₂ k (by lia)
    · rw [ih₃ (by lia)]
      -- The new row: the limbs below it, the row itself, and its carry.
      have hlow : (p.1.uset (rs + i + a.size) p.2 (by
            rw [size_addMul1Loop, htop]; lia)).valAt rs.toNat i.toNat =
          arr.valAt rs.toNat i.toNat :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [getElem!_uset, htop]
          simp only [show ¬(rs.toNat + i.toNat + a.size.toNat = k) by lia, ↓reduceIte]
          exact hp₂ k (by lia)
      have hrow' : (p.1.uset (rs + i + a.size) p.2 (by
            rw [size_addMul1Loop, htop]; lia)).valAt (rs.toNat + i.toNat) a.size.toNat =
          p.1.valAt (rs.toNat + i.toNat) a.size.toNat :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [getElem!_uset, htop]
          simp only [show ¬(rs.toNat + i.toNat + a.size.toNat = k) by lia, ↓reduceIte]
      have htop' : (p.1.uset (rs + i + a.size) p.2 (by
            rw [size_addMul1Loop, htop]; lia))[rs.toNat + i.toNat + a.size.toNat]! = p.2 := by
        rw [getElem!_uset, htop]
        simp
      rw [show a.size.toNat + (i.toNat + 1) = i.toNat + (a.size.toNat + 1) by lia,
        UInt64Array.valAt_add, UInt64Array.valAt_add _ _ a.size.toNat 1, UInt64Array.valAt_one,
        htop', hlow, hrow', Nat.add_comm a.size.toNat i.toNat, UInt64Array.valAt_add]
      obtain ⟨k, hk⟩ : ∃ k, b.size.toNat - i.toNat = k + 1 := ⟨b.size.toNat - i.toNat - 1, by lia⟩
      rw [show b.size.toNat - (i.toNat + 1) = k by lia, hk, UInt64Array.valAt_succ,
        ← USlice.getElem_eq_getElem! b i h, Nat.mul_succ, Nat.pow_add, ← Nat.add_assoc]
      rw [USlice.toNat_eq_valAt]
      generalize p.1.valAt _ _ = R at *
      generalize p.2.toNat = c at *
      generalize arr.valAt _ a.size.toNat = R₀ at *
      generalize arr.valAt _ i.toNat = L at *
      generalize b.array.valAt _ k = B at *
      generalize (b[i]'h).toNat = y at *
      generalize a.array.valAt _ _ = A at *
      generalize 2 ^ (64 * i.toNat) = P at *
      generalize 2 ^ (64 * a.size.toNat) = Q at *
      grind
  | case2 arr hr i h =>
    rw [mulBasecaseLoop]
    simp only [h, ↓reduceDIte]
    refine ⟨by simp, by simp, fun hi => ?_⟩
    have := USize.lt_iff_toNat_lt (a := i) (b := b.size)
    simp [show i.toNat = b.size.toNat by lia]

private theorem mulBasecaseLoop2_spec (arr : UInt64Array) (rs : USize) (a b : USlice)
    (hr : MulBound arr rs a.size.toNat b.size.toNat) (i : USize) :
    (mulBasecaseLoop2 arr rs a b hr i).size = arr.size ∧
      (∀ k, (k < rs.toNat + i.toNat ∨ rs.toNat + a.size.toNat + b.size.toNat ≤ k) →
        (mulBasecaseLoop2 arr rs a b hr i)[k]! = arr[k]!) ∧
      (i.toNat ≤ b.size.toNat →
        (mulBasecaseLoop2 arr rs a b hr i).valAt rs.toNat (a.size.toNat + b.size.toNat) =
          arr.valAt rs.toNat (a.size.toNat + i.toNat) +
            2 ^ (64 * i.toNat) *
              (a.toNat * b.array.valAt (b.start.toNat + i.toNat) (b.size.toNat - i.toNat))) := by
  induction arr, hr, i using mulBasecaseLoop2.induct rs a b with
  | case1 arr hr i h h' p ih =>
    rw [mulBasecaseLoop2]
    simp only [h, h', ↓reduceDIte]
    have hi := USize.lt_iff_toNat_lt.1 h
    have hi' := USize.lt_iff_toNat_lt.1 h'
    have hi₁ := USize.toNat_add_one_of_lt h
    have hi₂ := USize.toNat_add_one_of_lt h'
    rw [hi₁] at hi' hi₂
    have hrow := hr.toNat_row h
    have htop := hr.toNat_top h
    have htop₂ := hr.toNat_top₂ h h'
    have hp : p.1 = _ := mulRow2K_eq arr rs a b hr i h h'
    obtain ⟨q₁, q₂, q₃⟩ := addMul2Loop_spec arr (rs + i) a a.size
      (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h) (b[i]'h) (b[i + 1]'h') 0 (0, 0)
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero, hrow,
      Nat.mul_zero] at q₂ q₃
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = addMul2Loop arr (rs + i) a a.size
        (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (hr.row h) (b[i]'h) (b[i + 1]'h') 0 (0, 0) :=
      ⟨_, rfl⟩
    rw [← hQ] at q₁ q₂ q₃
    simp only [storeCarries, ← hQ] at hp
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hi₂] at ih₂ ih₃
    rw [p.2] at ih₁
    -- The limbs of `p` from those of `Q`.
    have hgp : ∀ k, p.1[k]! = if k = rs.toNat + i.toNat + a.size.toNat + 1 then Q.2.2 else
        if k = rs.toNat + i.toNat + a.size.toNat then Q.2.1 else Q.1[k]! := by
      intro k
      rw [hp, getElem!_uset, getElem!_uset, htop, htop₂]
      by_cases e₁ : rs.toNat + i.toNat + a.size.toNat + 1 = k
      · simp [e₁]
      · by_cases e₂ : rs.toNat + i.toNat + a.size.toNat = k
        · simp [e₂]
        · simp only [e₁, e₂, ↓reduceIte, show ¬ k = rs.toNat + i.toNat + a.size.toNat + 1 by lia,
            show ¬ k = rs.toNat + i.toNat + a.size.toNat by lia]
    refine ⟨ih₁, fun k hk => ?_, fun _ => ?_⟩
    · rw [ih₂ k (by lia), hgp, ite_ne _ _ (by lia), ite_ne _ _ (by lia)]
      exact q₂ k (by lia)
    · rw [ih₃ (by lia)]
      have hlow : p.1.valAt rs.toNat i.toNat = arr.valAt rs.toNat i.toNat :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [hgp, ite_ne _ _ (by lia), ite_ne _ _ (by lia)]; exact q₂ k (by lia)
      have hrow' : p.1.valAt (rs.toNat + i.toNat) a.size.toNat =
          Q.1.valAt (rs.toNat + i.toNat) a.size.toNat :=
        UInt64Array.valAt_congr _ fun k _ hk => by rw [hgp, ite_ne _ _ (by lia), ite_ne _ _ (by lia)]
      have hc : p.1.valAt (rs.toNat + i.toNat + a.size.toNat) 2 =
          Q.2.1.toNat + 2 ^ 64 * Q.2.2.toNat := by
        rw [UInt64Array.valAt_succ, UInt64Array.valAt_one, hgp, hgp, ite_ne _ _ (by lia), ite_eq' _ _ rfl,
          ite_eq' _ _ (by lia)]
      have hsplit : p.1.valAt rs.toNat (a.size.toNat + (i.toNat + 1 + 1)) =
          p.1.valAt rs.toNat i.toNat + 2 ^ (64 * i.toNat) *
            (p.1.valAt (rs.toNat + i.toNat) a.size.toNat + 2 ^ (64 * a.size.toNat) *
              p.1.valAt (rs.toNat + i.toNat + a.size.toNat) 2) := by
        rw [show a.size.toNat + (i.toNat + 1 + 1) = i.toNat + (a.size.toNat + 2) by lia,
          UInt64Array.valAt_add, UInt64Array.valAt_add _ _ a.size.toNat 2]
      have harr : arr.valAt rs.toNat (a.size.toNat + i.toNat) =
          arr.valAt rs.toNat i.toNat + 2 ^ (64 * i.toNat) *
            arr.valAt (rs.toNat + i.toNat) a.size.toNat := by
        rw [Nat.add_comm, UInt64Array.valAt_add]
      rw [hsplit, hlow, hrow', hc, harr]
      obtain ⟨k, hk⟩ : ∃ k, b.size.toNat - i.toNat = k + 2 := ⟨b.size.toNat - i.toNat - 2, by lia⟩
      have hb₀ := USlice.getElem_eq_getElem! b i h
      have hb₁ := USlice.getElem_eq_getElem! b (i + 1) h'
      rw [hi₁] at hb₁
      have hB : b.array.valAt (b.start.toNat + i.toNat) (k + 2) = (b[i]'h).toNat + 2 ^ 64 *
          ((b[i + 1]'h').toNat + 2 ^ 64 * b.array.valAt (b.start.toNat + (i.toNat + 1 + 1)) k) := by
        rw [UInt64Array.valAt_succ, UInt64Array.valAt_succ, ← hb₀,
          show b.start.toNat + i.toNat + 1 = b.start.toNat + (i.toNat + 1) by lia, ← hb₁,
          show b.start.toNat + (i.toNat + 1) + 1 = b.start.toNat + (i.toNat + 1 + 1) by lia]
      rw [show b.size.toNat - (i.toNat + 1 + 1) = k by lia, hk, hB]
      rw [USlice.toNat_eq_valAt]
      have hP : 2 ^ (64 * (i.toNat + 1 + 1)) = 2 ^ (64 * i.toNat) * (2 ^ 64 * 2 ^ 64) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1
      rw [hP]
      clear hgp hp hQ hlow hrow' hc hsplit
      generalize Q.1.valAt _ _ = R at *
      generalize Q.2.1.toNat = c₀ at *
      generalize Q.2.2.toNat = c₁ at *
      generalize arr.valAt (rs.toNat + i.toNat) a.size.toNat = R₀ at *
      generalize arr.valAt rs.toNat i.toNat = L at *
      generalize b.array.valAt _ k = B at *
      generalize (b[i]'h).toNat = y₀ at *
      generalize (b[i + 1]'h').toNat = y₁ at *
      generalize a.array.valAt _ _ = A at *
      generalize 2 ^ (64 * i.toNat) = P at *
      generalize 2 ^ (64 * a.size.toNat) = Q' at *
      grind
  | case2 arr hr i h h' =>
    rw [mulBasecaseLoop2]
    simp only [h, h', ↓reduceDIte]
    -- The last row: one step of `mulBasecaseLoop`.
    have hi₁ := USize.toNat_add_one_of_lt h
    have hlast : ¬(i + 1 < b.size) := h'
    have e : (mulRowK arr rs a b hr i h).1 = mulBasecaseLoop arr rs a b hr i := by
      rw [mulBasecaseLoop]
      simp only [h, ↓reduceDIte]
      rw [mulBasecaseLoop, mulRowK_eq]
      simp only [hlast, ↓reduceDIte]
    rw [e]
    exact mulBasecaseLoop_spec arr rs a b hr i
  | case3 arr hr i h =>
    rw [mulBasecaseLoop2]
    simp only [h, ↓reduceDIte]
    refine ⟨by simp, by simp, fun hi => ?_⟩
    have := USize.lt_iff_toNat_lt (a := i) (b := b.size)
    simp [show i.toNat = b.size.toNat by lia]

@[simp] public theorem size_mulBasecase (r a b : USlice) :
    (mulBasecase r a b).size = r.array.size := by
  rw [mulBasecase]
  split
  · rw [(mulBasecaseLoop2_spec ..).1, size_uset, size_mul1Loop]
  · rfl

/-- `mulBasecase` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulBasecase (r a b : USlice) (k : Nat)
    (hk : k < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ k) :
    (mulBasecase r a b)[k]! = r.array[k]! := by
  rw [mulBasecase]
  split
  · rename_i h
    have hr := mulBound_of r a b h.2
    have ht : (r.start + a.size).toNat = r.start.toNat + a.size.toNat :=
      USize.toNat_add_of_lt (by lia)
    rw [(mulBasecaseLoop2_spec ..).2.1 k (by rw [USize.toNat_one]; lia),
      getElem!_uset, ht]
    simp only [show ¬(r.start.toNat + a.size.toNat = k) by have := USize.lt_iff_toNat_lt.1 h.1; lia,
      ↓reduceIte]
    exact (mul1Loop_spec ..).2.1 k (by rw [USize.toNat_zero]; lia)
  · rfl

public theorem valAt_mulBasecase (r a b : USlice) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulBasecase r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
      a.toNat * b.toNat := by
  have h : 0 < b.size ∧ a.size ≤ r.size ∧ b.size ≤ r.size - a.size := by
    refine ⟨hb, USize.le_iff_toNat_le.2 (by lia), USize.le_iff_toNat_le.2 ?_⟩
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))]
    lia
  have hb' := USize.lt_iff_toNat_lt.1 hb
  have hm := mulBound_of r a b h.2
  have ht : (r.start + a.size).toNat = r.start.toNat + a.size.toNat :=
    USize.toNat_add_of_lt (by lia)
  rw [mulBasecase]
  simp only [h, and_self, ↓reduceDIte]
  obtain ⟨-, hp₂, hp₃⟩ := mul1Loop_spec r.array r.start a a.size
    (USize.le_iff_toNat_le.2 (Nat.le_refl _)) (r.loopBound h.2.1) (b[(0 : USize)]'hb) 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero] at hp₃
  rw [(mulBasecaseLoop2_spec ..).2.2 (by rw [USize.toNat_one]; lia),
    USize.toNat_one,
    UInt64Array.valAt_add, UInt64Array.valAt_one, getElem!_uset, ht]
  simp only [↓reduceIte]
  have hrow : ((mul1Loop r.array r.start a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
      (r.loopBound h.2.1) (b[(0 : USize)]'hb) 0 0).1.uset (r.start + a.size)
        (mul1Loop r.array r.start a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
          (r.loopBound h.2.1) (b[(0 : USize)]'hb) 0 0).2 (by
        rw [size_mul1Loop, ht]; lia)).valAt r.start.toNat a.size.toNat =
      (mul1Loop r.array r.start a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
        (r.loopBound h.2.1) (b[(0 : USize)]'hb) 0 0).1.valAt r.start.toNat a.size.toNat :=
    UInt64Array.valAt_congr _ fun k _ hk => by
      rw [getElem!_uset, ht]
      simp only [show ¬(r.start.toNat + a.size.toNat = k) by lia, ↓reduceIte]
  have hb₀ := USlice.getElem_eq_getElem! b 0 hb
  rw [USize.toNat_zero, Nat.add_zero] at hb₀
  have hB : b.array.valAt b.start.toNat b.size.toNat =
      (b[(0 : USize)]'hb).toNat +
        2 ^ 64 * b.array.valAt (b.start.toNat + 1) (b.size.toNat - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, b.size.toNat = k + 1 := ⟨b.size.toNat - 1, by lia⟩
    rw [hk, UInt64Array.valAt_succ, hb₀, Nat.add_sub_cancel]
  rw [hrow, USlice.toNat_eq_valAt b, hB]
  rw [← USlice.toNat_eq_valAt] at hp₃
  generalize (mul1Loop _ _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (mul1Loop _ _ _ _ _ _ _ _ _).2.toNat = c at *
  generalize b.array.valAt _ (b.size.toNat - 1) = B at *
  generalize (b[(0 : USize)]'hb).toNat = y at *
  generalize a.toNat = A at *
  generalize 2 ^ (64 * a.size.toNat) = Q at *
  grind

end MPN
