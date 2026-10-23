/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UInt
public import MPN.UIntArray
public import MPN.AddSub
public import MPN.Linear
public import MPN.Mul.Basecase
public import MPN.Mul.Comba
public import MPN.Mul.Karatsuba
public import MPN.Mul.Toom
public import MPN.Sqr.Basecase
public import MPN.Sqr.Karatsuba

/-!
# MPN

Verified multi-precision arithmetic on `UInt64` limbs, in the style of GMP's `mpn` functions:

* `MPN.UInt`: the high words of sums, differences and products of words;
* `MPN.UIntArray`: `valAt`, `USlice` and the in-place loop `foldUInPlace`;
* `MPN.AddSub`: addition and subtraction;
* `MPN.Linear`: in-place passes for the Toom methods: `± b x`, halving, exact division by 3;
* `MPN.Mul.Basecase`, `MPN.Mul.Comba`, `MPN.Mul.Karatsuba`, `MPN.Mul.Toom`: multiplication;
* `MPN.Sqr.Basecase`, `MPN.Sqr.Karatsuba`: squaring.
-/
