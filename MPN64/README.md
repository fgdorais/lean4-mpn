# MPN64: 64-bit limbs

Verified multi-precision arithmetic for Lean 4 on `UInt64` limbs, in the style of GMP's `mpn`
functions, stored in the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Every operation is proved
correct against `Nat`. This is the library `MPN64` (namespace `MPN.W64`); `MPN32` is the GMP-free
`Nat` on `UInt32` limbs with the full set of algorithms, and `MPN` is the part the two share
(finite sums, polynomials, the kernels over `WordArray` and the base-generic algorithms of
`MPN.Generic`), which both import. The module names below are in `MPN64/`.

The high words of 64-bit sums, differences and products are inline C with `__uint128_t`, so the
library builds only for 64-bit targets whose C compiler has that type, such as the clang that
comes with Lean.

## Operations

| module | functions | like GMP's |
|---|---|---|
| `MPN64.Arch.UInt` | `addh`, `subh`, `mulh` on `UInt32` and `UInt64`: the high words | |
| `MPN64.Config` | `Config`: the size thresholds of the algorithms; `config`, the library's, from its build options | GMP's `gmp-mparam.h` |
| `MPN.AddSubW` (shared) | `addW`, `subW`, `addN`, `subN`: the additions and subtractions, with the Toom kernels | `mpn_add`, `mpn_sub` |
| `MPN64.Arch.MulBasecase` | `mul1`, `addMul1`, `addMul2Loop` (two rows in one pass, its carries unboxed by lean4-scalar-arrays' `foldlInPlaceRangeWith2AccThen`), `mulBasecase` | `mpn_mul_1`, `mpn_addmul_1`, `mpn_addmul_2`, `mpn_mul_basecase` |
| `MPN64.Mul.Karatsuba` | `mulKaratsuba`, from `mulKaratsuba = 56` limbs, by `MPN`'s `MPN.Toom.mulKaratsuba` on `MPN`'s instance `toomOpsW` of the in-place passes, from `toomBase64` (`MPN64.Mul.ToomOps`): the products below the thresholds; Karatsuba's middle term is `MPN`'s `MPN.Toom.Mid` (`midW`) | `mpn_kara_mul_n` |
| `MPN64.Bits` | `lshift`, `rshift` (by `0 < s < 64`), `log2` | `mpn_lshift`, `mpn_rshift`, `mpn_sizeinbase` |
| `MPN64.Div.Limb` | `divRem1`: division by a limb, with `UInt64.div2` (128 by 64 bits) | `mpn_divrem_1` |
| `MPN64.Div.Basecase` | `divRem`: schoolbook division (Algorithm D) by `main`'s `MPN.Div.Basecase`, normalized by shifts | `mpn_tdiv_qr`, `mpn_sbpi1_div_qr` |
| `MPN64.Num` | whole arrays as numbers: `add`, `sub`, `mul`, `sqr`, `shl`, `shr`, `low`, `lt`, `divMod`, each returning a new array | |
| `MPN64.Div.DC` | `Num.divMod`: divide-and-conquer division (`MPN`'s `NatOps.divNorm`, Burnikel and Ziegler) from `divDC = 208` limbs, and Barrett's division with Newton's reciprocal of the top half of the divisor and wrapped remainders (`MPN`'s `NatOps.divMuT`, the products modulo `β^N - 1` by the FFT) from `divMu = 6144`; `Num.div`, the quotient alone, by Barrett's division without the last remainder (`NatOps.divQMuT`) from `divQMu = 4096` | `mpn_dcpi1_div_qr`, `mpn_mu_div_qr`, `mpn_mu_div_q` |
| `MPN.Generic.*` | shared with `MPN32` in `MPN`: `NatOps` (whole-number operations at any base), half-gcd (`HGCD`), decimal strings by divide and conquer (`Radix`); `Ops64` is the 64-bit instance on `MPN64.Num` | `mpn_hgcd`, `mpn_get_str`, `mpn_set_str` |
| `MPN64.Arch.LinComb`, `MPN64.Gcd` | `mulSubMul` (`a x - b y` in one pass), `mulAddMul` (`a x + b y`); `Num.gcd`: Euclid's algorithm on pairs of words (`gcd2`) up to two limbs, Lehmer's algorithm, and half-gcd (`MPN`'s `Bridge.hgcd`) with Lehmer's steps at its base | `mpn_gcd_22`, `mpn_hgcd_mul_matrix1_vector`, `mpn_hgcd_matrix_mul_1`, `mpn_gcd` |
| `MPN64.Decimal` | `Num.toDecimal`, `Num.ofDecimal?`: chunks of 19 digits, divide and conquer on long numbers | `mpn_get_str`, `mpn_set_str` |
| `MPN64.Sqrt` | `sqrtBase`: the base case of Zimmermann's Karatsuba square root (`MPN.Bridge.sqrtZ`), Newton's iteration on a double word (`sqrt2`) | `mpn_sqrtrem`, `mpn_dc_sqrtrem` |
| `MPN64.Mul.Toom` | by `MPN`'s `MPN.Toom.mulToom` and `MPN.Toom.sqrToom` on `toomOpsW`; `mulToom`: Toom-6 from `mulToom6 = 768` limbs, Toom-4 from `mulToom4 = 512` and Toom-4 by 3 from `mulToom43 = 592` limbs, Toom-3 from `mulToom3 = 368`, Toom-3 by 2 from `mulToom32 = 192` and Toom-4 by 2 from `mulToom42 = 104` limbs, by the shape; `sqrToom`: the Toom-6 square from 1039 limbs, the Toom-4 square from 714, the Toom-3 square from 544 | `mpn_toom6h_mul`, `mpn_toom44_mul`, `mpn_toom43_mul`, `mpn_toom33_mul`, `mpn_toom32_mul`, `mpn_toom42_mul`, `mpn_toom6_sqr`, `mpn_toom4_sqr`, `mpn_toom3_sqr` |
| `MPN.FFT.Fermat` | in place on windows of one array, modulo `2^(64 n) + 1`: `normAt`, `addModAt`, `subModAt`, `mulPow2At` | `mpn_fft_add_modF`, `mpn_fft_sub_modF`, `mpn_fft_mul_2exp_modF` |
| `MPN.FFT.Windows` (shared) | `WinOps.fwd`, `WinOps.inv`: the transforms of length `2ᵏ`, in place, on `MPN`'s instance `winOpsW` | `mpn_fft_fft`, `mpn_fft_fftinv` |
| `MPN64.FFT.Mul` | `fftMul`, `fftSqr`: Schönhage–Strassen with `2ᵏ` pieces; `MPN.W64.mul` and `MPN.W64.sqr`, by `MPN`'s `Dispatch.mul` and `Dispatch.sqr`, which split unbalanced products into pieces (`mulChunked`) and choose the FFT from `mulFFT = 6144` limbs in the larger operand and `sqrFFT = 5120` limbs, and `mulToom` or `sqrToom` below | `mpn_mul_fft`, `mpn_mul`, `mpn_sqr` |
| `MPN64.Arch.SqrBasecase` | `sqrBasecase` | `mpn_sqr_basecase` |
| `MPN64.Sqr.Karatsuba` | `sqrKaratsuba`, from `sqrKaratsuba = 88` limbs, by `MPN`'s `MPN.Toom.sqrKaratsuba` | `mpn_kara_sqr_n` |

`MPN64.Arch.UIntArray` holds the general tooling: the instance `limbArray64` of `MPN`'s `LimbArray`,
whose `valAt` is the value of a range of limbs; `USlice`, a region of an array with `USize`
bounds; `foldUInPlace`, the in-place loop; and `foldUInPlace2`, the in-place loop that reads other
windows of the array it writes. `MPN.Sum`, `MPN.NatMod`, `MPN.Poly`, `MPN.FFT.Roots` and
`MPN.FFT.Algebra` (from `MPN`) are mathematics on `Nat`: finite sums, congruences, polynomials,
the inversion of the transform, and the butterflies and coefficients of the transforms modulo
`2ᴺ + 1`. `MPN.FFT.Windows` (also from `MPN`) holds the transforms and their proofs for any limb
width, over the class `WinOps` of residue operations.

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
  library has no `implemented_by` of its own; the inline C of the high words in `MPN64.Arch.UInt`
  is the only code outside Lean.

## Building

```sh
lake build        # the library
lake test         # the tests, which check every operation against Nat, compiled
lake build bench64  # then .lake/build/bin/bench64, see BENCH.md
lake exe tune64     # the thresholds for this machine, see below
```

The toolchain is Lean `v4.36.0-rc2`. [BENCH.md](BENCH.md) has the timings against `Nat`, how to
run them, and a history of the changes that affected speed.

## Tuning

Multiplication, squaring, division, the greatest common divisor and decimal strings switch
algorithms at size thresholds collected in `MPN64.Config`; the functions that dispatch take a
`Config`, and the library's `MPN.W64.config` comes from its build options. The size crossovers were
measured on one machine (Zen 3), the choices of algorithm follow GMP's; `lake exe tune64` measures
them on yours in a few minutes and prints the options that set them. A project that depends on
this library passes them with its `require`, together with `march`, which compiles the library's C
code for a given processor:

```toml
[[require]]
name = "lean4-mpn"
git = "https://github.com/fgdorais/lean4-mpn"
rev = "main"
options = { march = "native", w64_mulKaratsuba = "48", w64_divDC = "384" }
```

The keys are the fields of `MPN64.Config`: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`,
`mulToom43`, `mulToom4`, `mulToom6`, `mulFFT`, `mulFFTUnbal`, `mulFFTMin`, `mulUnbalanced`,
`mulChunkMax`, `sqrKaratsuba`, `sqrToom3`, `sqrToom4`, `sqrToom6`, `sqrFFT`, `divDC`, `divMu`,
`divQMu`, `div1Recip`, `div1Unnorm`, `div32Recip`, `sqrtZimmermann`, `sqrtBase`, `gcdHalf`, `strDC`
and `parseDC`; an invalid value stops the build. Lake keeps the configuration it elaborated, so
after changing the options, build once with `lake build -R`. In this package itself, the same
options go on the command line: `lake build -R -K w64_mulKaratsuba=48`.

`MPN64.Config` imports `Lean` at compile time for its thresholds, so write the main file of a
program as a `module` with a `public def main`: a main file that is not a module initializes
everything its imports use at compile time too, and links all of Lean.
