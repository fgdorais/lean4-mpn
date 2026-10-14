/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Basic
public import Bignum.UInt

/-!
# Subtraction

* `subLimbs a b` is the `a.size` limbs of `a - b` when `b ≤ a` and `b` is no longer than `a`, like
  GMP's `mpn_sub`.
* `subAt r off a` subtracts `a` from `r` at limb `off` and propagates the borrow to the end of `r`,
  like GMP's `mpn_sub` followed by `mpn_decr_u`. It works in place when `r` is not shared.
-/

open ScalarArray

namespace Bignum

/-! ## Subtracting at an offset -/

/-- Subtracts `a[j...] + β` from `r` from limb `off + j` on, up to the end of `r`. -/
def subAtLoop (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat) (β : Bool) :
    UInt32Array × Bool :=
  if h : off + j < r.size then
    if a.size ≤ j ∧ β = false then
      (r, false)
    else
      let p := r[off + j].subWithBorrow (a.getD j 0) β
      subAtLoop (r.set (off + j) p.1 h) off a (j + 1) p.2
  else
    (r, β)
termination_by r.size - (off + j)

/--
Subtracts `a` from the limbs of `r` from `off` on and propagates the borrow to the end of `r`, like
GMP's `mpn_sub` followed by `mpn_decr_u`. Returns the new limbs and the borrow out of the last one.
-/
public def subAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array × Bool :=
  subAtLoop r off a 0 false

private theorem subAtLoop_spec (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat)
    (β : Bool) (ha : off + a.size ≤ r.size) (hj : off + j ≤ r.size) :
    (subAtLoop r off a j β).1.size = r.size ∧
      ofLimbs (subAtLoop r off a j β).1.toList +
          2 ^ (32 * (off + j)) * (β.toNat + ofLimbs (a.copy.toList.drop j)) =
        ofLimbs r.toList + 2 ^ (32 * r.size) * (subAtLoop r off a j β).2.toNat := by
  induction r, j, β using subAtLoop.induct off a with
  | case1 r j β h hstop =>
    rw [subAtLoop]
    simp only [h, hstop, ↓reduceDIte, ↓reduceIte, and_self]
    have : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    simp [this]
  | case2 r j β h hstop p ih =>
    rw [subAtLoop]
    simp only [h, hstop, ↓reduceDIte, ↓reduceIte]
    obtain ⟨ih₁, ih₂⟩ := ih (by simpa using ha) (by simp; omega)
    simp only [UInt32Array.size_set] at ih₁ ih₂
    refine ⟨ih₁, ?_⟩
    have hk : off + j < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList (off + j) p.1 hk
    have : p.1.toNat + (a.getD j 0).toNat + β.toNat = r[off + j].toNat + p.2.toNat * 2 ^ 32 :=
      UInt32.subWithBorrow_spec r[off + j] (a.getD j 0) β
    simp only [UInt32Array.getElem_toList] at hset
    rw [UInt32Array.toList_set, ← Nat.add_assoc off j 1, Nat.mul_add 32 (off + j) 1, Nat.mul_one,
      Nat.pow_add] at ih₂
    rw [ofLimbs_drop a.copy.toList j, ← getD_eq_getD_toList_copy]
    generalize ofLimbs (subAtLoop (r.set (off + j) p.1 h) off a (j + 1) p.2).1.toList = F at *
    generalize (subAtLoop (r.set (off + j) p.1 h) off a (j + 1) p.2).2.toNat = βf at *
    generalize ofLimbs (r.toList.set (off + j) p.1) = R₁ at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (a.copy.toList.drop (j + 1)) = A at *
    generalize 2 ^ (32 * (off + j)) = P at *
    generalize 2 ^ (32 * r.size) = Q at *
    generalize p.1.toNat = lo at *
    generalize p.2.toNat = hi at *
    generalize (a.getD j 0).toNat = y at *
    generalize r[off + j].toNat = z at *
    grind
  | case3 r j β h =>
    rw [subAtLoop]
    simp only [h, ↓reduceDIte]
    have h₁ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    have h₂ : off + j = r.size := by omega
    simp [h₁, h₂]

@[simp] public theorem size_subAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) : (subAt r off a).1.size = r.size :=
  (subAtLoop_spec r off a 0 false ha (by omega)).1

public theorem toNat_subAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) :
    toNat (subAt r off a).1 + 2 ^ (32 * off) * toNat a =
      toNat r + 2 ^ (32 * r.size) * (subAt r off a).2.toNat := by
  have := (subAtLoop_spec r off a 0 false ha (by omega)).2
  simpa [subAt, toNat] using this

/-- When the difference is not negative, `subAt` has no borrow out. -/
public theorem toNat_subAt_of_le (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) (hle : 2 ^ (32 * off) * toNat a ≤ toNat r) :
    toNat (subAt r off a).1 = toNat r - 2 ^ (32 * off) * toNat a := by
  have h := toNat_subAt r off a ha
  have hlt := ofLimbs_lt (subAt r off a).1.toList
  rw [UInt32Array.length_toList, size_subAt r off a ha] at hlt
  rw [toNat_toSlice, toNat_toSlice] at h
  rw [toNat_toSlice] at hle
  rw [toNat_toSlice, toNat_toSlice]
  cases hβ : (subAt r off a).2
  · simp only [hβ, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    omega
  · simp only [hβ, Bool.toNat_true, Nat.mul_one] at h
    omega

/-! ## The compiled loop

`subAtFast` runs `subAt`'s loop with `USize` indices, and `@[csimp]` makes the compiler use it, as
for `addMul1Fast`.
-/

/--
`subAtLoop` with `USize` indices: limb `j` of the subtrahend is at `offA + j` in `arr` when
`j < na`, and the loop runs while `j < m`, where `m` is the number of limbs of `r` from `offR` on.
-/
def subAtLoopU (r arr : UInt32Array) (offR offA na m : USize) (j : USize) (c : Bool)
    (hm : offR.toNat + m.toNat = r.size) (ha : offA.toNat + na.toNat ≤ arr.size)
    (hrs : r.size < USize.size) (has : arr.size < USize.size) : UInt32Array × Bool :=
  if hj : j < m then
    if na ≤ j ∧ c = false then
      (r, false)
    else
      have := USize.lt_iff_toNat_lt.1 hj
      have hir : (offR + j).toNat < r.size := by rw [toNat_add_usize (by omega)]; omega
      let y := if hy : j < na then
          arr.uget (offA + j) (by
            have := USize.lt_iff_toNat_lt.1 hy
            rw [toNat_add_usize (by omega)]; omega)
        else 0
      let p := (r.uget (offR + j) hir).subWithBorrow y c
      subAtLoopU (r.uset (offR + j) p.1 hir) arr offR offA na m (j + 1) p.2 (by simpa using hm)
        ha (by simpa using hrs) has
  else
    (r, c)
termination_by m.toNat - j.toNat
decreasing_by
  rw [toNat_add_usize (by rw [USize.toNat_one]; omega), USize.toNat_one]
  omega

private theorem subAtLoopU_eq (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat)
    (c : Bool) (hrs : r.size < USize.size) (has : a.array.size < USize.size)
    (ha' : off + a.size ≤ r.size) (hj : off + j ≤ r.size) (m : USize)
    (hmr : m.toNat = r.size - off) (hm ha) :
    subAtLoopU r a.array off.toUSize a.start.toUSize a.size.toUSize m j.toUSize c hm ha hrs has =
      subAtLoop r off a j c := by
  have hstop := a.stop_le_array_size
  have hstart := a.start_le_stop
  have hsize := a.size_eq
  have hoff : off < USize.size := by omega
  have hst : a.start < USize.size := by omega
  have hn : a.size < USize.size := by omega
  induction r, j, c using subAtLoop.induct off a with
  | case1 r j c h hstop' =>
    have hrm : r.size - off < USize.size := by omega
    rw [subAtLoopU, subAtLoop]
    have hlt : j.toUSize < m := by
      rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), hmr]
      omega
    have hle : a.size.toUSize ≤ j.toUSize := by
      rw [USize.le_iff_toNat_le, toNat_toUSize hn, toNat_toUSize (by omega)]
      exact hstop'.1
    simp only [h, hlt, hstop', hle, ↓reduceDIte, ↓reduceIte, and_self]
  | case2 r j c h hstop' p ih =>
    have hrm : r.size - off < USize.size := by omega
    rw [subAtLoopU, subAtLoop]
    have hlt : j.toUSize < m := by
      rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), hmr]
      omega
    have hnot : ¬ (a.size.toUSize ≤ j.toUSize ∧ c = false) := by
      rw [USize.le_iff_toNat_le, toNat_toUSize hn, toNat_toUSize (by omega)]
      exact hstop'
    simp only [h, hlt, hstop', hnot, ↓reduceDIte, ↓reduceIte]
    have hjs : j.toUSize + 1 = (j + 1).toUSize := by
      apply USize.toNat_inj.1
      rw [toNat_add_usize (by rw [toNat_toUSize (by omega), USize.toNat_one]; omega),
        toNat_toUSize (by omega), USize.toNat_one, toNat_toUSize (by omega)]
    have hir : (off.toUSize + j.toUSize).toNat = off + j := by
      rw [toNat_add_usize (by rw [toNat_toUSize hoff, toNat_toUSize (by omega)]; omega),
        toNat_toUSize hoff, toNat_toUSize (by omega)]
    -- The limb of the subtrahend read with `USize` indices is `a.getD j 0`.
    have hy : (if hy : j.toUSize < a.size.toUSize then
        a.array.uget (a.start.toUSize + j.toUSize) (by
          have := USize.lt_iff_toNat_lt.1 hy
          rw [toNat_add_usize (by omega)]; omega)
      else 0) = a.getD j 0 := by
      by_cases hja : j < a.size
      · have hy : j.toUSize < a.size.toUSize := by
          rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), toNat_toUSize hn]
          exact hja
        have hia : (a.start.toUSize + j.toUSize).toNat = a.start + j := by
          rw [toNat_add_usize (by rw [toNat_toUSize hst, toNat_toUSize (by omega)]; omega),
            toNat_toUSize hst, toNat_toUSize (by omega)]
        simp only [hy, ↓reduceDIte, UInt32Array.Slice.getD_eq, hja]
        rw [uget_eq_getElem a.array _ (a.start + j) hia]
        rfl
      · have hy : ¬ j.toUSize < a.size.toUSize := by
          rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), toNat_toUSize hn]
          exact hja
        simp only [hy, ↓reduceDIte, UInt32Array.Slice.getD_eq, hja]
    have ih' := ih (by simpa using hrs) (by simpa using ha') (by simp; omega) (by simp [hmr])
    rw [← hjs] at ih'
    simp only [p, ← hir] at ih'
    simp only [hy, uget_eq_getElem r _ (off + j) hir]
    simp only [← hir]
    exact ih' (by simp only [UInt32Array.size_set, toNat_toUSize hoff, hmr]; omega)
  | case3 r j c h =>
    have hrm : r.size - off < USize.size := by omega
    rw [subAtLoopU, subAtLoop]
    have hlt : ¬ j.toUSize < m := by
      rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), hmr]
      omega
    simp only [h, hlt, ↓reduceDIte]

/-- `subAt` with `USize` indices, which the compiler uses in its place. -/
public def subAtFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array × Bool :=
  if hs : r.size < USize.size ∧ a.array.size < USize.size ∧ off + a.size ≤ r.size then
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    subAtLoopU r a.array off.toUSize a.start.toUSize a.size.toUSize (r.size - off).toUSize 0 false
      (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega)
      (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega) hs.1 hs.2.1
  else
    subAtLoop r off a 0 false

@[csimp] public theorem subAt_eq_subAtFast : @subAt = @subAtFast := by
  funext r off a
  rw [subAt, subAtFast]
  split
  · rename_i hs
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (subAtLoopU_eq r off a 0 false hs.1 hs.2.1 hs.2.2 (by omega) _
      (toNat_toUSize (by omega)) _ _).symm
  · rfl

/-! ## Differences -/

/--
The `a.size` limbs of `a - b`, like GMP's `mpn_sub`: `a` is copied and `b` subtracted in place. It
is exact when `b ≤ a`.
-/
public def subLimbs (a b : UInt32Array.Slice) : UInt32Array :=
  (subAt (copyPadded a a.size) 0 b).1

@[simp] public theorem size_subLimbs (a b : UInt32Array.Slice) (hb : b.size ≤ a.size) :
    (subLimbs a b).size = a.size := by
  rw [subLimbs, size_subAt _ _ _ (by rw [size_copyPadded _ _ (Nat.le_refl _)]; omega),
    size_copyPadded _ _ (Nat.le_refl _)]

public theorem toNat_subLimbs (a b : UInt32Array.Slice) (hb : b.size ≤ a.size)
    (hle : toNat b ≤ toNat a) : toNat (subLimbs a b) = toNat a - toNat b := by
  rw [subLimbs, toNat_subAt_of_le _ _ _ (by rw [size_copyPadded _ _ (Nat.le_refl _)]; omega)
    (by rw [toNat_copyPadded]; simpa using hle), toNat_copyPadded]
  simp

/--
`x - y` as `x.size` limbs. Unlike `subLimbs`, `y` may be longer than `x`: it is cut to `x.size`
limbs, which keeps its value when `y ≤ x`.
-/
public def subVal (x y : UInt32Array) : UInt32Array := subLimbs x (y.toSlice 0 x.size)

@[simp] public theorem size_subVal (x y : UInt32Array) : (subVal x y).size = x.size := by
  rw [subVal, size_subLimbs _ _ (by simp; omega)]
  simp

public theorem toNat_subVal (x y : UInt32Array) (h : toNat y ≤ toNat x) :
    toNat (subVal x y) = toNat x - toNat y := by
  have hx := toNat_lt x
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero] at hx
  have hy : toNat (y.toSlice 0 x.size) = toNat y := toNat_toSlice_of_lt y x.size (by omega)
  rw [subVal, toNat_subLimbs _ _ (by simp; omega) (by rw [hy]; exact h), hy]

end Bignum
