/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Basic
public import MPN.AddSubW

/-!
# Subtraction

* `subLimbs a b` is the `a.size` limbs of `a - b` when `b ≤ a`, like GMP's `mpn_sub`, by `main`'s
  `WordArray.subN` on the windows of the slices.
* `subVal x y` is the same on arrays.
-/

open ScalarArray

namespace MPN.W32

/-- The `a.size` limbs of `a - b`, exact when `b ≤ a`. -/
public def subLimbs (a b : UInt32Array.Slice) : UInt32Array :=
  WordArray.subN a.array a.start a.size b.array b.start b.size

@[simp] public theorem size_subLimbs (a b : UInt32Array.Slice) : (subLimbs a b).size = a.size := by
  rw [subLimbs]; exact WordArray.size_subN a.array a.start a.size b.array b.start b.size

public theorem toNat_subLimbs (a b : UInt32Array.Slice) (hle : toNat b ≤ toNat a) :
    toNat (subLimbs a b) = toNat a - toNat b := by
  rw [toNat_array_eq_valAt, size_subLimbs, toNat_eq_valAt, toNat_eq_valAt]
  exact WordArray.valAt_subN _ _ _ _ _ _ hle

/-- `x - y` as `x.size` limbs, exact when `y ≤ x`. -/
public def subVal (x y : UInt32Array) : UInt32Array := WordArray.subN x 0 x.size y 0 y.size

@[simp] public theorem size_subVal (x y : UInt32Array) : (subVal x y).size = x.size := by
  rw [subVal]; exact WordArray.size_subN x 0 x.size y 0 y.size

public theorem toNat_subVal (x y : UInt32Array) (h : toNat y ≤ toNat x) :
    toNat (subVal x y) = toNat x - toNat y := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt] at h
  rw [toNat_array_eq_valAt, size_subVal, toNat_array_eq_valAt, toNat_array_eq_valAt]
  exact WordArray.valAt_subN _ _ _ _ _ _ h

end MPN.W32
