/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.UIntArray

/-!
# Carry propagation

`add1 r a c` writes `a + c` into the first `min r.size a.size` limbs of the slice `r`, in place
when its array is not shared, and returns the array and the carry out, like GMP's `mpn_add_1`.
With `c = 0` it copies `a`. The carry is a word, so it may be any `UInt64`. The other additions
and subtractions are `main`'s generic kernels (`MPN.AddSubW`, `MPN.Toom.Kernels`).
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Carry propagation -/

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

end MPN.W64
