/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UInt
public import MPN.Config
public import MPN.UIntArray
public import MPN.AddSub
public import MPN.Linear
public import MPN.Bits
public import MPN.Div.Limb
public import MPN.Div.Basecase
public import MPN.Mul.Basecase
public import MPN.Mul.Karatsuba
public import MPN.Mul.Toom
public import MPN.Sqr.Basecase
public import MPN.Sqr.Karatsuba
public import MPN.FFT.Roots
public import MPN.FFT.Algebra
public import MPN.WordGcd
public import MPN.FFT.Fermat
public import MPN.FFT.Transform
public import MPN.FFT.Mul
public import MPN.Num
public import MPN.Div.DC
public import MPN.Div.Mu
public import MPN.Sqrt
public import MPN.Generic.Ops
public import MPN.Generic.Barrett
public import MPN.Generic.DC
public import MPN.Generic.Sqrt
public import MPN.Generic.HGCD
public import MPN.Generic.Radix
public import MPN.Generic.Ops64
public import MPN.Lehmer
public import MPN.Gcd
public import MPN.Decimal

/-!
# MPN

Verified multi-precision arithmetic on `UInt64` limbs, in the style of GMP's `mpn` functions:

* `MPN.UInt`: the high words of sums, differences and products of words;
* `MPN.UIntArray`: `valAt`, `USlice` and the in-place loop `foldUInPlace`;
* `MPN.AddSub`: addition and subtraction;
* `MPN.Linear`: in-place passes for the Toom methods: `± b x`, halving, exact division by 3;
* `MPN.Bits`: shifts by any number of bits, clearing, and the base-two logarithm;
* `MPN.Div.Limb`, `MPN.Div.Basecase`: division by a limb and schoolbook division;
* `MPN.Mul.Basecase`, `MPN.Mul.Karatsuba`, `MPN.Mul.Toom`: multiplication;
* `MPN.Sqr.Basecase`, `MPN.Sqr.Karatsuba`: squaring;
* `MPN.FFT.Roots`, `MPN.FFT.Fermat`, `MPN.FFT.Transform`, `MPN.FFT.Mul`: FFT multiplication,
  from the inversion of the transform modulo `2^N + 1`, in-place residues modulo `2^(64 n) + 1`
  in the windows of one array, and the forward and inverse transforms on blocks of those
  windows.
* `MPN.Num`: whole arrays as numbers, each operation returning a new array;
* `MPN.Div.DC`: divide-and-conquer division on them, `Num.divMod`;
* `MPN.Div.Mu`: products modulo `β^N - 1` by the FFT (`mulModB`), and reductions modulo `β^N - 1`;
* `MPN.Sqrt`: the square root and its remainder, by Zimmermann's Karatsuba square root.
* `MPN.Generic.Ops`, `MPN.Generic.Barrett`, `MPN.Generic.HGCD`, `MPN.Generic.Radix`: base-generic
  algorithms from `main` (division by a reciprocal, half-gcd, decimal strings by divide and
  conquer) over `NatOps`;
* `MPN.Generic.Ops64`: the instance of `NatOps` for 64-bit limbs, on `MPN.Num`;
* `MPN.Lehmer`: `mulSubMul`, `a x - b y` in one pass, the kernel of Lehmer's step;
* `MPN.Gcd`: the greatest common divisor, by Lehmer's algorithm and half-gcd;
* `MPN.Decimal`: decimal strings, by chunks of nineteen digits and by divide and conquer.
-/
