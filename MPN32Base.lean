/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Basic
public import MPN32.Arch.UInt
public import MPN32.Arch.UIntArray
public import MPN32.FoldInPlace
public import MPN32.Mul.Limb

/-!
# The base of `MPN32`

The modules of `MPN32` below the multiplications by a limb, which the library `MPN32Base` builds
without unrolling loops (see `lakefile.lean`).
-/
