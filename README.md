# Lean 4 / MPN, 64-bit branch

Verified multi-precision arithmetic for Lean 4 on `UInt64` limbs, in the style of GMP's `mpn`
functions, stored in the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Every operation is proved
correct against `Nat`. The `main` branch is the GMP-free `Nat` on `UInt32` limbs with the full
set of algorithms; this branch explores 64-bit limbs.

The high words of 64-bit sums, differences and products are inline C with `__uint128_t`, so the
library builds only for 64-bit targets whose C compiler has that type, such as the clang that
comes with Lean.

## Operations

| module | functions | like GMP's |
|---|---|---|
| `MPN.UInt` | `addh`, `subh`, `mulh` on `UInt32` and `UInt64`: the high words | |
| `MPN.AddSub` | `addN`, `subN`; `add1`, `sub1`; `add`, `sub`; in place: `addInto`, `subInto` | `mpn_add_n`, `mpn_add_1`, `mpn_add`, … |
| `MPN.Mul.Basecase` | `mul1`, `addMul1`, `mulBasecase` | `mpn_mul_1`, `mpn_addmul_1`, `mpn_mul_basecase` |
| `MPN.Mul.Comba` | `mulComba`: schoolbook by columns | |
| `MPN.Mul.Karatsuba` | `mulKaratsuba`, from `karatsubaThreshold = 64` limbs | `mpn_kara_mul_n` |
| `MPN.Linear` | in place: `addMulInto`, `subMulInto`, `shl63Into` (halving), `rshiftInto`, `divExactInto` (by odd divisors of `2⁶⁴ - 1`: `divExact3Into`, `divExact5Into`) | `mpn_addmul_1`, `mpn_rshift`, `mpn_divexact_by3`, `mpn_divexact_1` |
| `MPN.Mul.Toom` | `mulToom`: Toom-4 and Toom-4 by 3 from `toom4Threshold = 600` limbs, Toom-3, Toom-3 by 2 and Toom-4 by 2 from `toom3Threshold = 384` limbs | `mpn_toom44_mul`, `mpn_toom43_mul`, `mpn_toom33_mul`, `mpn_toom32_mul`, `mpn_toom42_mul` |
| `MPN.FFT.Fermat` | in place on windows of one array, modulo `2^(64 n) + 1`: `normAt`, `addModAt`, `subModAt`, `mulPow2At` | `mpn_fft_add_modF`, `mpn_fft_sub_modF`, `mpn_fft_mul_2exp_modF` |
| `MPN.FFT.Transform` | `fwd`, `inv`: the transforms of length `2ᵏ`, in place | `mpn_fft_fft`, `mpn_fft_fftinv` |
| `MPN.FFT.Mul` | `fftMul`, `fftSqr`: Schönhage–Strassen with `2ᵏ` pieces; `MPN.mul` and `MPN.sqr`, which choose the FFT from `fftThreshold = 3072` limbs in the larger operand and `sqrFFTThreshold = 2048` limbs, and `mulToom` or `sqrKaratsuba` below | `mpn_mul_fft`, `mpn_mul`, `mpn_sqr` |
| `MPN.Sqr.Basecase` | `sqrBasecase` | `mpn_sqr_basecase` |
| `MPN.Sqr.Karatsuba` | `sqrKaratsuba`, from `sqrKaratsubaThreshold = 96` limbs | `mpn_kara_sqr_n` |

`MPN.UIntArray` holds the general tooling: `valAt`, the value of a range of limbs; `USlice`, a
region of an array with `USize` bounds; `foldUInPlace`, the in-place loop; and `foldUInPlace2`,
the in-place loop that reads other windows of the array it writes. `MPN.Sum`, `MPN.NatMod`,
`MPN.Poly` and `MPN.FFT.Roots` are mathematics on `Nat`: finite sums, congruences, polynomials
and the inversion of the transform.

## Conventions

- **Operands and results are `USlice`s.** A function writes its result into the limbs of the slice
  `r` and returns the new array, with the carry or borrow out where there is one. It writes as
  many limbs as its slices allow, or, for the products and squares, none when `r` is too short.
- **Every function has three theorems:** the array keeps its size, the limbs outside the ones it
  writes are unchanged, and the value of the limbs it writes, through `valAt`. The first two need
  no hypotheses.
- **The fast loops are proved equal to the simple ones.** Each loop is written as a plain
  recursion with `uget` and `uset`, which is what the theorems are about, and compiles, through a
  `@[csimp]` lemma or a continuation, to `foldUInPlaceThen`. That makes the array exclusive once
  and then stores without checks; its `implemented_by` implementation is the one piece of trusted
  code.

## Building

```sh
lake build        # the library
lake test         # the tests, which check every operation against Nat, compiled
lake build bench  # then .lake/build/bin/bench, see BENCH.md
```

The toolchain is Lean `v4.36.0-rc1`. [BENCH.md](BENCH.md) has the timings against `Nat`, how to
run them, and a history of the changes that affected speed.
