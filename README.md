# Lean 4 / MPN

Verified multi-precision arithmetic for Lean 4, in the style of GMP's `mpn` functions. Every
operation is proved correct against `Nat`.

This branch is the part that does not depend on the width of a limb, which the two libraries
build on:

* [`main32`](https://github.com/fgdorais/lean4-mpn/tree/main32): a GMP-free `Nat` on `UInt32`
  limbs, `MPN.Nat`, in pure Lean with the full set of algorithms;
* [`main64`](https://github.com/fgdorais/lean4-mpn/tree/main64): `UInt64` limbs, with the high
  words of sums and products in inline C (`__uint128_t`), within a few times GMP's speed.

Both stay merged with `main`: a change to the common part is made here and merged into each.

## Modules

| module | contents |
|---|---|
| `MPN.Sum` | finite sums `sumRange f n`, for column sums of products and the inverse FFT |
| `MPN.NatMod` | congruences modulo the Fermat numbers of the FFT |
| `MPN.Poly` | coefficient lists and their values `polyVal x cs`: sums, products, even and odd parts |
| `MPN.LimbArray` | `LimbArray A L`: arrays of limbs of `w` bits, and `valAt`, the value of a range of limbs, with its lemmas, for limbs of any width |
| `MPN.FFT.Roots` | the inversion of the FFT's transform modulo a Fermat number, on natural numbers |
| `MPN.FFT.Algebra` | the algebra of the transforms modulo `2ᴺ + 1` for any `N`: bit reversal, the butterflies, and the coefficients they give (`fft_coef`, and `fft_coef_cyc` for products modulo `x^K - 1`) |
| `MPN.FFT.Windows` | the forward and inverse transforms with their proofs, in place on windows of `n + 1` limbs of one array, over the class `WinOps` of residue operations modulo `2^(w n) + 1` on a `LimbArray`, for limbs of any width `w` |
| `MPN.FFT.Product` | Schönhage–Strassen products, products modulo `2^(w N) - 1` and squares on one flat array, with their proofs, over `WinOps` and the class `FFTOps` of the other in-place operations, the pointwise products an argument |
| `MPN.WordGcd` | Euclid's algorithm on words, and the runs of Lehmer's steps on leading words |
| `MPN.Generic.Ops` | `NatOps α`: the operations of a representation of numbers at a base, with their specifications |
| `MPN.Generic.Barrett` | division by a reciprocal from Newton's iteration over `NatOps`, every estimate checked |
| `MPN.Generic.DC` | divide-and-conquer division (Burnikel and Ziegler) over `NatOps`, with the instance's base case |
| `MPN.Generic.Sqrt` | Zimmermann's Karatsuba square root over `NatOps`, with the instance's base case, and facts about `Nat.sqrt` |
| `MPN.Generic.HGCD` | half-gcd over `NatOps` (Schönhage, Möller), with the instance's base case |
| `MPN.Generic.Radix` | decimal strings by divide and conquer over `NatOps` |

An algorithm written and proved over `NatOps` serves both libraries with only a new instance.
