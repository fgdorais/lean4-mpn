/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic
public import MPN.UInt
public import MPN.ValAt
public import MPN.AddSubW

/-!
# Subtraction

`subLimbs a b` is the `a.size` limbs of `a - b` when `b ≤ a` and `b` is no longer than `a`, like
GMP's `mpn_sub`, by `main`'s `subW`; `subVal x y` cuts `y` to the size of `x` first.
-/

open ScalarArray

namespace MPN

/-! ## Differences -/

/-- The `a.size` limbs of `a - b`, like GMP's `mpn_sub`, by `main`'s `subW`. -/
public def subLimbs (a b : UInt32Array.Slice) : UInt32Array :=
  WordArray.subW (UInt32Array.replicate a.size 0) 0 a.array a.start a.size b.array b.start b.size

@[simp] public theorem size_subLimbs (a b : UInt32Array.Slice) (_ : b.size ≤ a.size) :
    (subLimbs a b).size = a.size := by
  show LimbArray.size (A := UInt32Array) _ = _
  rw [subLimbs, WordArray.size_subW]; simp [LimbArray.size]

public theorem toNat_subLimbs (a b : UInt32Array.Slice) (hb : b.size ≤ a.size)
    (hle : toNat b ≤ toNat a) : toNat (subLimbs a b) = toNat a - toNat b := by
  rw [toNat_array_eq_valAt, size_subLimbs a b hb, toNat_eq_valAt a, toNat_eq_valAt b]
  rw [toNat_eq_valAt a, toNat_eq_valAt b] at hle
  exact (WordArray.subW_spec _ 0 a.array a.start a.size b.array b.start b.size
    (by simp [LimbArray.size]) hb hle).2

/--
`x - y` as `x.size` limbs. Unlike `subLimbs`, `y` may be longer than `x`: it is cut to `x.size`
limbs, which keeps its value when `y ≤ x`.
-/
public def subVal (x y : UInt32Array) : UInt32Array := subLimbs x (y.toSlice 0 x.size)

@[simp] public theorem size_subVal (x y : UInt32Array) : (subVal x y).size = x.size := by
  rw [subVal, size_subLimbs _ _ (by simp; lia)]
  simp

public theorem toNat_subVal (x y : UInt32Array) (h : toNat y ≤ toNat x) :
    toNat (subVal x y) = toNat x - toNat y := by
  have hx := toNat_lt x
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero] at hx
  have hy : toNat (y.toSlice 0 x.size) = toNat y := toNat_toSlice_of_lt y x.size (by lia)
  rw [subVal, toNat_subLimbs _ _ (by simp; lia) (by rw [hy]; exact h), hy]

end MPN
