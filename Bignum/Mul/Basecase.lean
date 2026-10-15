/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Mul.Limb
public import Bignum.Mul.Comba

/-!
# Schoolbook multiplication

`mulBasecase a b` is the schoolbook algorithm, after GMP's `mpn_mul_basecase`: one `addMul1` of
`b` per limb of `a`. It takes quadratic time and is the base case of the faster algorithms.
-/

open ScalarArray

namespace Bignum

/-- Adds the rows `a[i] * b` from `i` on into `r`, one `addMul1` per row. -/
def mulBasecaseLoop (a b : UInt32Array.Slice) (r : UInt32Array) (i : Nat)
    (h : r.size = a.size + b.size) : UInt32Array :=
  if hi : i < a.size then
    mulBasecaseLoop a b (addMul1Set r i b a[i] (by omega)) (i + 1) (by simp [h])
  else
    r
termination_by a.size - i

/--
All `a.size + b.size` limbs of `a * b`, untrimmed, by the schoolbook algorithm. It runs `a.size`
rows of `b.size` limbs each, so it is fastest with the shorter operand as `a`.
-/
public def mulBasecase (a b : UInt32Array.Slice) : UInt32Array :=
  mulBasecaseLoop a b (.replicate (a.size + b.size) 0) 0 (by simp)

private theorem mulBasecaseLoop_spec (a b : UInt32Array.Slice) (r : UInt32Array) (i : Nat)
    (h : r.size = a.size + b.size) (hi : i ≤ a.size)
    (hr : ofLimbs r.toList = ofLimbs (a.copy.toList.take i) * toNat b) :
    (mulBasecaseLoop a b r i h).size = a.size + b.size ∧
      ofLimbs (mulBasecaseLoop a b r i h).toList = toNat a * toNat b := by
  induction r, i, h using mulBasecaseLoop.induct a b with
  | case1 r i h hi' ih =>
    rw [mulBasecaseLoop]
    simp only [hi', ↓reduceDIte]
    apply ih (by omega)
    -- The limb at `i + b.size` is zero, since the value so far is below `2^(32 (i + b.size))`.
    have hA := ofLimbs_lt (a.copy.toList.take i)
    have hB := toNat_lt b
    simp only [List.length_take, UInt32Array.length_toList, UInt32Array.Slice.size_copy,
      Nat.min_eq_left (Nat.le_of_lt hi')] at hA
    have hlt : ofLimbs r.toList < 2 ^ (32 * (i + b.size)) := by
      rw [hr, Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul'' hA hB
    have hk : i + b.size < r.toList.length := by simp; omega
    have hz : r.toList[i + b.size] = 0 := getElem_eq_zero_of_ofLimbs_lt hk hlt
    simp only [UInt32Array.getElem_toList] at hz
    have hadd := toNat_addMul1Set r i b a[i] (by omega) hz
    simp only [toNat_toSlice] at hadd
    rw [hadd, hr, ofLimbs_take_add_one _ _ (by simpa using hi'), toNat]
    simp only [UInt32Array.getElem_toList, UInt32Array.Slice.getElem_copy]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm a[i].toNat]
  | case2 r i h hi' =>
    rw [mulBasecaseLoop]
    simp only [hi', ↓reduceDIte]
    refine ⟨h, ?_⟩
    have : i = a.size := by omega
    rw [hr, this, List.take_of_length_le (by simp)]
    rfl

@[simp] public theorem size_mulBasecase (a b : UInt32Array.Slice) :
    (mulBasecase a b).size = a.size + b.size :=
  (mulBasecaseLoop_spec a b (.replicate (a.size + b.size) 0) 0 _ (Nat.zero_le _) (by simp)).1

public theorem toNat_mulBasecase (a b : UInt32Array.Slice) :
    toNat (mulBasecase a b) = toNat a * toNat b := by
  rw [toNat_toSlice, mulBasecase]
  exact (mulBasecaseLoop_spec a b (.replicate (a.size + b.size) 0) 0 _ (Nat.zero_le _) (by simp)).2

/-! ## The compiled product

`mulBasecaseFast` uses Comba's method (`Mul.Comba`) when the sizes allow it, and `@[csimp]` makes
the compiler use it in place of `mulBasecase`: both compute all `a.size + b.size` limbs of the
product, and limbs of a given length are determined by their value.
-/

/-- `mulBasecase`, by Comba's method when the sizes allow it. -/
public def mulBasecaseFast (a b : UInt32Array.Slice) : UInt32Array :=
  if h : CombaOK a b then combaMul a b h else mulBasecase a b

@[csimp] public theorem mulBasecase_eq_mulBasecaseFast : @mulBasecase = @mulBasecaseFast := by
  funext a b
  unfold mulBasecaseFast
  split
  · rename_i h
    obtain ⟨hs, hv⟩ := combaMul_spec a b h
    apply UInt32Array.toList_inj.1
    apply ofLimbs_inj_of_length (by simp [hs])
    rw [← toNat_toSlice, ← toNat_toSlice, toNat_mulBasecase, hv]
  · rfl

end Bignum
