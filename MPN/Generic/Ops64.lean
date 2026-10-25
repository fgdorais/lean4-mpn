/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops64Base
public import MPN.Div.DC

/-!
# The 64-bit instance of `NatOps`

`ops64` runs the base-generic algorithms (half-gcd, radix conversion) on whole arrays of 64-bit
limbs with the operations of `MPN.Num` (`ops64With`, `MPN.Generic.Ops64Base`) and `Num.divMod`.
-/

open ScalarArray UInt64Array

namespace MPN

/-- `(x / y, x mod y)`, by `Num.divMod`. -/
public def divRem64 (x y : UInt64Array) : UInt64Array × UInt64Array :=
  if fits (x.size + y.size + 1) then
    let p := Num.divMod x y
    (trimA p.1, trimA p.2)
  else (ofNat (x.toNat / y.toNat), ofNat (x.toNat % y.toNat))

/-- The operations of `MPN.Num` as `NatOps` at base `2⁶⁴`, with `Num.divMod`. -/
@[expose] public def ops64 : NatOps UInt64Array :=
  ops64With divRem64 fun x y hy => by
    rw [divRem64]; split
    · rename_i h
      dsimp only
      rw [toNat_trimA, toNat_trimA]
      exact Num.toNat_divMod _ _ (by lia) (lt_of_fits h)
    · exact ⟨toNat_ofNat _, toNat_ofNat _⟩

@[simp] public theorem ops64_val (x : UInt64Array) : ops64.val x = x.toNat := rfl

end MPN
