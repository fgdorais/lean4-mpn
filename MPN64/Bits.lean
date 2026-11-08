/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.AddSub
public import MPN64.Arch.MulBasecase
public import MPN.Shift
public import MPN.Bitwise
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2

/-!
# Bits

`log2 a` is `Nat.log2 a.toNat`, from the top nonzero limb. Shifts of arrays by any number of bits
are `Num.shl` and `Num.shr`, by `main`'s `WordArray.shlBits` and `shrBits`.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Base-two logarithm -/

/-- `Nat.log2 a.toNat`: the position of the top bit of `a`, or `0` when `a` is zero, by `main`'s
`WordArray.log2W` from the top limb down. -/
public def log2 (a : USlice) : Nat :=
  WordArray.log2W a.array a.start a.size (a.loopBound (USize.le_refl _))

@[simp] public theorem log2_eq (a : USlice) : log2 a = _root_.Nat.log2 a.toNat := by
  rw [log2, WordArray.log2W_eq, USlice.toNat_eq_valAt]
  rfl

end MPN.W64
