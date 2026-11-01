/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Arch.UInt
public import MPN32.Arch.UIntArray
public import MPN32.Arch.Comba
public import MPN32.Arch.Rows
public import MPN32.Arch.SqrBasecase
public import MPN32.Arch.DivTwo
public import MPN32.Arch.LinComb

/-!
# The architecture layer on 32-bit limbs

What depends on the machine words of 32-bit limbs, beyond the shared code of `MPN`:

* `Arch.UInt`: the double-width word operations, in `UInt64` (`mulAddAdd`, `subMulBiased`, the
  carry words, `div2Rem`);
* `Arch.UIntArray`: the instances `limbArray32`, `wordArray32` and `wordFolds32` of `MPN`'s
  classes on `UInt32Array`, from which `MPN` derives the rest (`toomOpsW`, `fftOpsW`, `winOpsW`);
* `Arch.Comba` and `Arch.Rows`: the schoolbook product by Comba's method and by rows into wide
  accumulators, which keep whole products of 32-bit limbs in `UInt64` columns;
* `Arch.SqrBasecase`: the schoolbook square, each cross product once;
* `Arch.DivTwo`: the division of a word by two limbs (`div2Step`), for `MPN.Nat`'s words;
* `Arch.LinComb`: the kernels of the linear combinations of Lehmer's step (`linComb32`).

Each is a choice for the host's multiplier and divider, tuned on one machine, and the place to
look first on another target.
-/
