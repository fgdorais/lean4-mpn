/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Arch.UInt
public import MPN64.Arch.UIntArray
public import MPN64.Arch.MulBasecase
public import MPN64.Arch.SqrBasecase
public import MPN64.Arch.KaratsubaMid
public import MPN64.Arch.LinComb

/-!
# The architecture layer on 64-bit limbs

What depends on the machine words of 64-bit limbs, beyond the shared code of `MPN`:

* `Arch.UInt`: the high words of 64-bit sums, differences and products, inline C with
  `__uint128_t`;
* `Arch.UIntArray`: the instances `limbArray64`, `wordArray64` and `wordFolds64` of `MPN`'s
  classes on `UInt64Array`, from which `MPN` derives the rest (`toomOpsW`, `fftOpsW`, `winOpsW`);
* `Arch.MulBasecase`: the schoolbook product with two rows per pass (GMP's `mpn_addmul_2`);
* `Arch.SqrBasecase`: the schoolbook square, each cross product once;
* `Arch.KaratsubaMid`: the middle term of Karatsuba's method in one pass;
* `Arch.LinComb`: the kernels of the linear combinations of Lehmer's step (`linComb64`).

Each is a choice for the host's multiplier, tuned on one machine, and the place to look first on
another target.
-/
