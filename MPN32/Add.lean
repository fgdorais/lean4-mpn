/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Basic
public import MPN.AddSubW

/-!
# Addition

* `addLimbs a b` is all `max a.size b.size + 1` limbs of `a + b`, like GMP's `mpn_add`, by
  `main`'s `WordArray.addN` on the windows of the slices.
* `add a b` is the trimmed sum.
-/

open ScalarArray

namespace MPN.W32

/-- All `max a.size b.size + 1` limbs of `a + b`, untrimmed. -/
public def addLimbs (a b : UInt32Array.Slice) : UInt32Array :=
  WordArray.addN a.array a.start a.size b.array b.start b.size

@[simp] public theorem size_addLimbs (a b : UInt32Array.Slice) :
    (addLimbs a b).size = max a.size b.size + 1 := by
  rw [addLimbs]; exact WordArray.size_addN a.array a.start a.size b.array b.start b.size

public theorem toNat_addLimbs (a b : UInt32Array.Slice) :
    toNat (addLimbs a b) = toNat a + toNat b := by
  rw [toNat_array_eq_valAt, size_addLimbs, toNat_eq_valAt, toNat_eq_valAt]
  exact WordArray.valAt_addN ..

/-- Adds two numbers. -/
public def add (a b : UInt32Array.Slice) : UInt32Array := trim (addLimbs a b)

@[simp] public theorem toNat_add (a b : UInt32Array.Slice) :
    toNat (add a b) = toNat a + toNat b := by
  rw [add, toNat_trim, toNat_addLimbs]

public theorem isTrimmed_add (a b : UInt32Array.Slice) : isTrimmed (add a b) = true :=
  isTrimmed_trim _

end MPN.W32
