# Lean 4 / MPN, 64-bit branch

Verified multi-precision arithmetic for Lean 4 on `UInt64` limbs, in the style of GMP's `mpn`
functions, stored in the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Every operation is proved
correct against `Nat`. This is the `main64` branch; `main32` is the GMP-free `Nat` on `UInt32`
limbs with the full set of algorithms, and `main` is the part the two share (finite sums,
polynomials and the base-generic algorithms of `MPN.Generic`), which both merge.

The high words of 64-bit sums, differences and products are inline C with `__uint128_t`, so the
library builds only for 64-bit targets whose C compiler has that type, such as the clang that
comes with Lean.

## Operations

| module | functions | like GMP's |
|---|---|---|
| `MPN.UInt` | `addh`, `subh`, `mulh` on `UInt32` and `UInt64`: the high words | |
| `MPN.Config` | `Config`: the size thresholds of the algorithms; `config`, the library's, from its build options | GMP's `gmp-mparam.h` |
| `MPN.AddSub` | `addN`, `subN`; `add1`, `sub1`; `add`, `sub`; in place: `addInto`, `subInto` | `mpn_add_n`, `mpn_add_1`, `mpn_add`, … |
| `MPN.Mul.Basecase` | `mul1`, `addMul1`, `mulBasecase` | `mpn_mul_1`, `mpn_addmul_1`, `mpn_mul_basecase` |
| `MPN.Mul.Karatsuba` | `mulKaratsuba`, from `mulKaratsuba = 64` limbs | `mpn_kara_mul_n` |
| `MPN.Linear` | in place: `addMulInto`, `subMulInto`, `shl63Into` (halving), `rshiftInto`, `divExactInto` (by odd constants: `divExact3Into`, `divExact5Into`, `divExact7Into`, `divExact9Into`) | `mpn_addmul_1`, `mpn_rshift`, `mpn_divexact_by3`, `mpn_divexact_1` |
| `MPN.Bits` | `lshift`, `rshift` (by `0 < s < 64`), `shiftLeft`, `shiftRight` (by any number of bits), `zeroInto`, `log2` | `mpn_lshift`, `mpn_rshift`, `mpn_zero`, `mpn_sizeinbase` |
| `MPN.Div.Limb` | `divRem1`: division by a limb, with `UInt64.div2` (128 by 64 bits) | `mpn_divrem_1` |
| `MPN.Div.Basecase` | `divRem`: schoolbook division (Algorithm D) with normalization, `qEst` never too small and `addBack` | `mpn_tdiv_qr`, `mpn_sbpi1_div_qr` |
| `MPN.Num` | whole arrays as numbers: `add`, `sub`, `mul`, `sqr`, `shl`, `shr`, `low`, `lt`, `divMod`, each returning a new array | |
| `MPN.Div.DC` | `Num.divNorm`: divide-and-conquer division (Burnikel and Ziegler) on `MPN.Num`; `Num.divMod` from `divDC = 512` limbs | `mpn_dcpi1_div_qr` |
| `MPN.Generic.*` | shared with `main32` through `main`: `NatOps` (whole-number operations at any base), half-gcd (`HGCD`), decimal strings by divide and conquer (`Radix`); `Ops64` is the 64-bit instance on `MPN.Num` | `mpn_hgcd`, `mpn_get_str`, `mpn_set_str` |
| `MPN.Lehmer`, `MPN.Gcd` | `mulSubMul` (`a x - b y` in one pass), `mulAddMul` (`a x + b y`); `Num.gcd`: Euclid's algorithm on pairs of words (`gcd2`) up to two limbs, Lehmer's algorithm, and half-gcd with its own base case | `mpn_gcd_22`, `mpn_hgcd_mul_matrix1_vector`, `mpn_hgcd_matrix_mul_1`, `mpn_gcd` |
| `MPN.Decimal` | `Num.toDecimal`, `Num.ofDecimal?`: chunks of 19 digits, divide and conquer on long numbers | `mpn_get_str`, `mpn_set_str` |
| `MPN.Sqrt` | `sqrtRem`: Zimmermann's Karatsuba square root, Newton's iteration on a double word (`sqrt2`) at the bottom | `mpn_sqrtrem`, `mpn_dc_sqrtrem` |
| `MPN.Mul.Toom` | `mulToom`: Toom-6 from `mulToom6 = 768` limbs, Toom-4 from `mulToom4 = 600` and Toom-4 by 3 from `mulToom43 = 600` limbs, Toom-3 from `mulToom3 = 384`, Toom-3 by 2 from `mulToom32 = 176` and Toom-4 by 2 from `mulToom42 = 88` limbs, by the shape; `sqrToom`: the Toom-6 square from 1152 limbs, the Toom-4 square from 1000, the Toom-3 square from 600 | `mpn_toom6h_mul`, `mpn_toom44_mul`, `mpn_toom43_mul`, `mpn_toom33_mul`, `mpn_toom32_mul`, `mpn_toom42_mul`, `mpn_toom6_sqr`, `mpn_toom4_sqr`, `mpn_toom3_sqr` |
| `MPN.FFT.Fermat` | in place on windows of one array, modulo `2^(64 n) + 1`: `normAt`, `addModAt`, `subModAt`, `mulPow2At` | `mpn_fft_add_modF`, `mpn_fft_sub_modF`, `mpn_fft_mul_2exp_modF` |
| `MPN.FFT.Transform` | `fwd`, `inv`: the transforms of length `2ᵏ`, in place | `mpn_fft_fft`, `mpn_fft_fftinv` |
| `MPN.FFT.Mul` | `fftMul`, `fftSqr`: Schönhage–Strassen with `2ᵏ` pieces; `MPN.mul` and `MPN.sqr`, which split unbalanced products into pieces (`mulChunked`) and choose the FFT from `mulFFT = 4096` limbs in the larger operand and `sqrFFT = 2816` limbs, and `mulToom` or `sqrToom` below | `mpn_mul_fft`, `mpn_mul`, `mpn_sqr` |
| `MPN.Sqr.Basecase` | `sqrBasecase` | `mpn_sqr_basecase` |
| `MPN.Sqr.Karatsuba` | `sqrKaratsuba`, from `sqrKaratsuba = 96` limbs | `mpn_kara_sqr_n` |

`MPN.UIntArray` holds the general tooling: `valAt`, the value of a range of limbs; `USlice`, a
region of an array with `USize` bounds; `foldUInPlace`, the in-place loop; and `foldUInPlace2`,
the in-place loop that reads other windows of the array it writes. `MPN.Sum`, `MPN.NatMod`,
`MPN.Poly`, `MPN.FFT.Roots` and `MPN.FFT.Algebra` (from `main`) are mathematics on `Nat`: finite
sums, congruences, polynomials, the inversion of the transform, and the butterflies and
coefficients of the transforms modulo `2ᴺ + 1`.

## Conventions

- **Operands and results are `USlice`s.** A function writes its result into the limbs of the slice
  `r` and returns the new array, with the carry or borrow out where there is one. It writes as
  many limbs as its slices allow, or, for the products and squares, none when `r` is too short.
- **Every function has three theorems:** the array keeps its size, the limbs outside the ones it
  writes are unchanged, and the value of the limbs it writes, through `valAt`. The first two need
  no hypotheses.
- **The fast loops are proved equal to the simple ones.** Each loop is written as a plain
  recursion with `uget` and `uset`, which is what the theorems are about, and compiles, through a
  `@[csimp]` lemma or a continuation, to `foldUInPlaceThen` or `foldUInPlace2Then`, which `@[csimp]`
  lemmas in turn replace with lean4-scalar-arrays' in-place folds (`foldlInPlaceRangeThen`,
  `foldlInPlace2Then`). Those make the array exclusive once and then store without checks. The
  library has no `implemented_by` of its own; the inline C of the high words in `MPN.UInt` is the
  only code outside Lean.

## Building

```sh
lake build        # the library
lake test         # the tests, which check every operation against Nat, compiled
lake build bench  # then .lake/build/bin/bench, see BENCH.md
lake exe tune     # the thresholds for this machine, see below
```

The toolchain is Lean `v4.36.0-rc1`. [BENCH.md](BENCH.md) has the timings against `Nat`, how to
run them, and a history of the changes that affected speed.

## Tuning

Multiplication, squaring, division, the greatest common divisor and decimal strings switch
algorithms at size thresholds collected in `MPN.Config`; the functions that dispatch take a
`Config`, and the library's `MPN.config` comes from its build options. The defaults were measured
on one machine; `lake exe tune` measures them on yours in several minutes and prints the options
that set them. A project that depends on this library passes them with its `require`, together
with `march`, which compiles the library's C code for a given processor:

```toml
[[require]]
name = "lean4-mpn"
git = "https://github.com/fgdorais/lean4-mpn"
rev = "main64"
options = { march = "native", mulKaratsuba = "48", divDC = "384" }
```

The keys are the fields of `MPN.Config`: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`,
`mulToom43`, `mulToom4`, `mulToom6`, `mulFFT`, `mulFFTUnbal`, `mulFFTMin`, `mulUnbalanced`,
`mulChunkMax`, `sqrKaratsuba`, `sqrToom3`, `sqrToom4`, `sqrToom6`, `sqrFFT`, `divDC`, `gcdHalf`,
`strDC` and `parseDC`; an invalid value
stops the build. Lake keeps the configuration it elaborated, so after changing the options, build
once with `lake build -R`. In this package itself, the same options go on the command line:
`lake build -R -K mulKaratsuba=48`.

`MPN.Config` imports `Lean` at compile time for its thresholds, so write the main file of a
program as a `module` with a `public def main`: a main file that is not a module initializes
everything its imports use at compile time too, and links all of Lean.
