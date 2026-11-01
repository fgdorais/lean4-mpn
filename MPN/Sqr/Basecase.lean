/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Basecase
public import MPN.Settings

/-!
# The schoolbook square

`sqrBasecase a` is `mulBasecase a a`: the product of `a` by itself by rows of `addMul1Set`, whose
loop is `main`'s generic pass. The square by the rows above the diagonal and the diagonal, which
reads each pair of limbs once, is not used in this experiment.
-/

open ScalarArray

namespace MPN

/-- The `2 a.size` limbs of `a²`, by the schoolbook product. -/
public def sqrBasecase (a : UInt32Array.Slice) : UInt32Array := mulBasecase a a

public theorem sqrBasecase_spec (a : UInt32Array.Slice) :
    (sqrBasecase a).size = a.size + a.size ∧ toNat (sqrBasecase a) = toNat a * toNat a :=
  ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

/-- `sqrBasecase`; the threshold is not used. -/
public def sqrBasecaseWith (_r : Nat) (a : UInt32Array.Slice) : UInt32Array := sqrBasecase a

end MPN
