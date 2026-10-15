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

`subAtFast` subtracts the limbs of `a` with `foldInPlace`, as `addMul1Fast` does, then propagates the
borrow with `subAt`'s own loop, which stops as soon as the borrow is gone. `@[csimp]` makes the
compiler use it in place of `subAt`.
-/

/-- `subAt` with `foldInPlace` over the limbs of `a`, which the compiler uses in its place. -/
public def subAtFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array × Bool :=
  if hs : r.size < USize.size ∧ a.array.size < USize.size ∧ off + a.size ≤ r.size then
    let p := r.foldInPlace off.toUSize a.size.toUSize false
      (fun k hk y c => y.subWithBorrow (limbU a hs.2.1 k hk) c)
      (by
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        exact hs.2.2)
    subAtLoop p.1 off a a.size p.2
  else
    subAtLoop r off a 0 false

/-- The fold of `subAtFast` from limb `j` on, then the borrow, is `subAtLoop` from limb `j` on. -/
private theorem foldInPlace_loop_subAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (has : a.array.size < USize.size) (s n : Nat) (hs : s = off) (hn : n = a.size) (j : Nat)
    (c : Bool) (ha : off + a.size ≤ r.size) (hj : j ≤ a.size) (h' hlen) :
    subAtLoop (UInt32Array.foldInPlace.loop a.size.toUSize
          (fun k hk y c => y.subWithBorrow (limbU a has k hk) c) s n r h' hlen j c).1 off a a.size
        (UInt32Array.foldInPlace.loop a.size.toUSize
          (fun k hk y c => y.subWithBorrow (limbU a has k hk) c) s n r h' hlen j c).2 =
      subAtLoop r off a j c := by
  subst s n
  induction r, j, c using subAtLoop.induct off a with
  | case1 r j c h hstop =>
    have : j = a.size := by omega
    subst this
    rw [UInt32Array.foldInPlace.loop]
    simp
  | case2 r j c h hstop p ih =>
    by_cases hja : j < a.size
    · rw [UInt32Array.foldInPlace.loop]
      conv => rhs; rw [subAtLoop]
      simp only [hja, ↓reduceDIte, h, hstop, ↓reduceIte, limbU_eq a has j _ hja]
      have hg : a.getD j 0 = a[j] := by simp [UInt32Array.Slice.getD_eq, hja]
      simp only [p, hg] at ih ⊢
      exact ih (by simpa using ha) (by omega) (by simpa using ha)
    · have : j = a.size := by omega
      subst this
      rw [UInt32Array.foldInPlace.loop]
      simp
  | case3 r j c h =>
    have : j = a.size := by omega
    subst this
    rw [UInt32Array.foldInPlace.loop]
    simp

@[csimp] public theorem subAt_eq_subAtFast : @subAt = @subAtFast := by
  funext r off a
  rw [subAt, subAtFast]
  split
  · rename_i hs
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (foldInPlace_loop_subAt r off a hs.2.1 _ _ (toNat_toUSize (by omega))
      (toNat_toUSize (by omega)) 0 false hs.2.2 (by omega) _ _).symm
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
