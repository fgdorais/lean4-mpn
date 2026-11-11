# Benchmarks

This file tracks the performance of the library against Lean's `Nat`, which is backed by GMP. The
tables come from `lake exe bench` and are regenerated after each change that affects speed, and
the history at the end records what changed and by how much.

## Running

```sh
lake build bench                      # `lake build` alone does not rebuild it
for i in 1 2 3 4 5; do taskset -c 2 .lake/build/bin/bench; done > bench.txt
scripts/bench_md.py bench.txt         # the three tables below
```

Arguments select operations and sizes, for example `bench mul kara 4 16`, and `--no-nat` skips
`Nat`, and the conversions of the operands to it, for a profiler. Pinning the process to one core
with `taskset` makes the results steadier. Each time is the median of five trials, and the
columns `±MPN` and `±Nat` are the spread of those trials (sample standard deviation over mean).
A row with a GMP kernel for its operation has three more columns: `mpn`, the time of that kernel,
`MPN/mpn`, the ratio to it, and `±mpn`, its spread.

**Run it several times.** About one process in four runs every trial of the small operations
30–100% slower, mostly on the `Nat` side, with a spread of ±10–25% instead of the usual ±0.1–1%.
It is a property of the whole process: rerunning the same command gives the normal times. The
cause is unknown; it is not address randomization or page faults, and it never happened under
`perf stat`. `scripts/bench_md.py` keeps the fastest time of each cell over the runs it is given,
so five runs make the tables reliable. Within one run, distrust a row whose spread is above ±2%.

## How to read the tables

- **Sizes** are in 64-bit limbs, the same limbs as GMP's on this machine. A row of 16 limbs is
  1,024 bits.
- **The `Nat` column** is Lean's `Nat`: GMP with assembly kernels, behind a wrapper that allocates
  the result. A ratio is `MPN / Nat`, so below 1 means faster than `Nat`. For `str`, `parse` and
  `sqrt` it is not GMP: Lean's `Nat.repr`, `String.toNat?` and `Nat.sqrt` are written in Lean.
- **The `mpn` column** is GMP's own kernel for the operation (`mpn_add`, `mpn_mul`, `mpn_sqr`,
  `mpn_tdiv_qr`, `mpn_divrem_1`, `mpn_mod_1`, `mpn_sqrtrem`, `mpn_gcd`, `mpn_get_str`,
  `mpn_set_str`, …, `Bench/mpn.c`), from the GMP that Lean links into the executable, on the same
  limbs, writing into a buffer it keeps: no allocation, no `mpz` layer. It is the yardstick for
  the algorithms and kernels, where `Nat` also counts Lean's wrapper. `div` and `divmod` compare
  with `mpn_tdiv_qr`, which computes both results; the products of every algorithm (`mul`,
  `kara`, `toom`, `fft`, `auto`, `mulmod`) with `mpn_mul`, GMP's choice for the size. The
  library's side, and every column, includes the call of the timing loop, about 10 ns.
- **The library side allocates its output** with `UInt64Array.replicate`, which fills it with
  zeros, since its functions write into a given array. `addmul1` adds into a shared array, so it
  copies it first, as `Nat` allocates a new result.
- **One limb:** operands below `2⁶³` are `Nat`'s unboxed scalars, which need no allocation.
- **Results are checked in O(1)** on both sides (the size and the first limb, or the low word), so
  the time is the operation alone.
- **Machine:** AMD Ryzen 5 5600X (Zen 3), Linux 7.2, Lean `v4.36.0-rc2`, lean4-scalar-arrays
  `v1.1.0`, GMP 6.3.0 (Lean's), C compiled with `-falign-loops=64` (`-falign-loops=32` for the
  shared `MPN`; see the lakefile). Tables of 2026-11-09 at `a0aeba1`, the fastest of five runs
  (three for the large sizes) over the rows whose spread is within ±2% (history below).

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1`, on `USlice`s with `USize` indices |
| `shl`, `shr` | `MPN.lshift`, `MPN.rshift` | `n` limbs, by 13 bits | one pass, `USize` indices; `Nat`'s `<<<` and `>>>` |
| `div1` | `MPN.divRem1` by `0xF123456789ABCDEF` | `n` limbs by a normalized limb | one pass from the top, `UInt64.div2` (128 by 64 bits) per limb, and the checked 2-by-1 steps with a reciprocal (always, `div1Recip` = 0, like GMP) (`main`'s `WordArray.divRem1W`) |
| `div1u` | `MPN.divRem1` by `0x0123456789ABCDEF` | `n` limbs by an unnormalized limb | as `div1`, with the same steps on the dividend shifted in place (`divRem1U`; always, `div1Unnorm` = 0, like GMP) |
| `div` | `MPN.Num.div` | `2 n` by `n` limbs | the quotient alone: Barrett's division by the reciprocal of the top half of the divisor without the last remainder (`divQMuT`) from `divQMu = 4096` limbs in the divisor, below as `divmod` |
| `divmod` | `MPN.Num.divMod` | `2 n` by `n` limbs | Barrett's division by the reciprocal of the top half of the divisor with wrapped remainders (`divMuT`) from `divMu = 6144` limbs in the divisor, divide and conquer (`divNorm`) from `divDC = 208`, schoolbook below; `Nat` computes the quotient only |
| `sbdiv` | `MPN.divRem` | `2 n` by `n` limbs | schoolbook (Algorithm D), normalized |
| `sqrt` | `MPN.sqrtRem` | `n` limbs | Zimmermann's Karatsuba square root on `MPN.Num`; `Nat.sqrt` is Lean's Newton iteration on `Nat`, not GMP's `mpz_sqrt` |
| `mulmod` | `MPN.Num.mulModB` | `n` by `n` limbs modulo `β^n - 1` | the FFT with the pieces wrapping around (`fftMulModAt`), `2ᵏ` pieces for `k = fftK n`; `Nat` multiplies |
| `gcd` | `MPN.Num.gcd` | `n` and `n` limbs | Euclid's algorithm on pairs of words (`gcd2`) up to two limbs, Lehmer's algorithm with steps of 62 bits (`cofactors2`, `mulSubMul`), half-gcd of the top third (`hgcdReduceP`, as GMP's `mpn_gcd`) from `gcdHalf = 1536` limbs with its own base case (`baseW`, `mulAddMul`); `Nat.gcd` is GMP's |
| `str` | `MPN.Num.toDecimal` | `n` limbs | chunks of 19 digits, divide and conquer from `strDC = 40` limbs; `Nat.repr` is Lean's, not GMP |
| `parse` | `MPN.Num.ofDecimal?` | the digits of `n` limbs | chunks of 19 digits, divide and conquer from `19 parseDC` digits (`parseDC = 512`); `String.toNat?` is Lean's, not GMP |
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass, `USize` indices |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass, `USize` indices |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1` with a continuation, `USize` indices |
| `kara` | `MPN.mulKaratsuba` | `n` by `n` limbs | Karatsuba from 64 limbs (`mulKaratsuba`), `mulBasecase` below |
| `toom` | `MPN.mulToom` | `n` by `n` limbs | Toom-8 from 1792 limbs (`mulToom8`), Toom-6 from 768 (`mulToom6`), Toom-4 from 600 (`mulToom4`), Toom-3 from 384 (`mulToom3`), `mulKaratsuba` below |
| `kara2` | `MPN.mulKaratsuba` | `n` by `n / 2` limbs | as `kara` |
| `toom2` | `MPN.mulToom` | `n` by `n / 2` limbs | Toom-3 by 2 or Toom-4 by 2 from 384 limbs in the smaller operand, `mulKaratsuba` below |
| `fft` | `MPN.FFT.fftMul` | `n` by `n` limbs | Schönhage–Strassen with `2ᵏ` pieces, `k = fftK (2 n)`, the pointwise products by `mulToom` |
| `fft2` | `MPN.FFT.fftMul` | `n` by `n / 2` limbs | as `fft` |
| `fftK` | `MPN.FFT.fftMul` | `n` by `n` limbs | as `fft` with `2ᴷ` pieces, for example `fft9`, for tuning `fftK` |
| `auto` | `MPN.mul` | `n` by `n` limbs | the FFT from `mulFFT = 4096` limbs in the larger operand (`mulFFTUnbal = 3072` for shapes of `3 : 2` or more) with `mulFFTMin = 320` in the smaller, `mulToom` below |
| `auto2`, `auto4`, `auto8` | `MPN.mul` | `n` by `n / 2`, `n / 4`, `n / 8` limbs | as `auto`, with the unbalanced products split into pieces |
| `autobS` | `MPN.mul` | `n` by `S` limbs, for example `autob256` | as `auto2` |
| `fftbS`, `toombS` | `MPN.FFT.fftMul`, `MPN.mulToom` | `n` by `S` limbs, for example `fftb256` | for tuning `mulFFTMin` |
| `fftsqr` | `MPN.FFT.fftSqr` | `n` limbs | one forward transform, the pointwise squares by `sqrKaratsuba`, `k = fftK (2 n)` |
| `fsqK` | `MPN.FFT.fftSqr` | `n` limbs | as `fftsqr` with `2ᴷ` pieces, for example `fsq9` |
| `toomsqr` | `MPN.sqrToom` | `n` limbs | the Toom-8 square from 2816 limbs (`sqrToom8`), the Toom-6 square from 1039 (`sqrToom6`), the Toom-4 square from 1000 (`sqrToom4`), the Toom-3 square from 600 (`sqrToom3`), `sqrKaratsuba` below |
| `autosqr` | `MPN.sqr` | `n` limbs | the FFT from `sqrFFT = 2816` limbs, `sqrToom` below |
| `sqr` | `MPN.sqrBasecase` | `n` limbs | the cross products once by rows (`mul1`, `addMul1`), then doubled with the diagonal in one pass |
| `ksqr` | `MPN.sqrKaratsuba` | `n` limbs | Karatsuba with three squares from 96 limbs (`sqrKaratsuba`), `sqrBasecase` below |
| `mulref` | `Bench.refMul` | `n` by `n` limbs | schoolbook by rows, a hand-written loop with `Nat` indices and the arithmetic of `addMul1`; not part of the library, kept as a control since its code does not change |
| `badd`, `bsub`, `bmul`, `bdiv`, `bmod`, `bsqr`, `bpow` (`x³`), `blcm`, `blog2`, `bcmp` (`x < x + 1`), `beq` (two copies), `bhash`, `bgcd`, `bshl`, `bshr`, `band`, `bor`, `bxor`, `bsqrt`, `btostr`, `bofstr`, `btonat`, `bofnat` | `MPN.Nat` | `n` and `n` limbs (`bdiv`, `bsqrt`: `2n` limbs) | the verified natural numbers, `main`'s `GNat` on the instance `natLimbs64`: one word below `2⁶⁴`, otherwise trimmed limbs through `MPN.Num`; the time includes trimming the result |
| `bdiv1`, `bmod1` | `MPN.Nat` `/`, `%` | `n` limbs by `10⁹ + 7` | a word below `2³²`, unnormalized: `/` by `main`'s `WordArray.divRem1A`, `%` by `WordArray.mod1A` (the reciprocal steps by `d 2ˢ` on the dividend unshifted, then one step modulo `d`), no quotient |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.26 | 0.32 | 0.28 | 0.33 | 0.34 | 0.35 | 0.37 | 0.38 | 0.41 | 0.44 | 0.49 | 0.56 | 0.68 | 0.80 | 0.79 | 0.83 | 0.99 |
| `sub` | 0.32 | 0.28 | 0.32 | 0.29 | 0.30 | 0.31 | 0.33 | 0.33 | 0.36 | 0.38 | 0.45 | 0.53 | 0.67 | 0.77 | 0.85 | 0.90 | 1.20 |
| `shl` | 0.31 | 0.39 | 0.39 | 0.39 | 0.40 | 0.40 | 0.40 | 0.40 | 0.41 | 0.42 | 0.44 | 0.46 | 0.50 | 0.56 | 0.43 | 0.46 | 0.64 |
| `shr` | 2.19 | 0.38 | 0.39 | 0.38 | 0.40 | 0.42 | 0.45 | 0.39 | 0.39 | 0.40 | 0.41 | 0.42 | 0.47 | 0.53 | 0.42 | 0.47 | 0.57 |
| `div1` | 3.46 | 0.45 | 0.47 | 0.49 | 0.54 | 0.57 | 0.60 | 0.63 | 0.72 | 0.75 | 0.83 | 0.87 | 0.96 | 0.99 | 0.95 | 0.99 | 1.06 |
| `div1u` | 1.07 | 0.31 | 0.34 | 0.35 | 0.37 | 0.39 | 0.43 | 0.47 | 0.52 | 0.57 | 0.63 | 0.70 | 0.77 | 0.84 | 0.83 | 0.89 | 0.98 |
| `sbdiv` | 0.65 | 1.17 | 1.16 | 1.48 | 1.63 | 1.57 | 1.78 | 1.99 | 2.09 | 2.22 | 2.41 | 2.38 | 2.32 | 2.45 | 2.39 | 2.51 | 3.03 |
| `div` | 0.78 | 1.02 | 1.00 | 1.30 | 1.43 | 1.47 | 1.68 | 1.84 | 1.97 | 2.11 | 2.38 | 2.35 | 2.31 | 2.43 | 2.39 | 2.87 | 2.91 |
| `divmod` | 0.78 | 1.28 | 1.23 | 1.54 | 1.67 | 1.62 | 1.79 | 2.09 | 2.17 | 2.29 | 2.43 | 2.41 | 2.34 | 2.45 | 2.40 | 2.86 | 2.91 |
| `sqrt` | 1.82 | 0.33 | 1.02 | 0.85 | 1.00 | 1.19 | 1.37 | 1.54 | 1.49 | 1.10 | 1.02 | 0.93 | 0.62 | 0.57 | 0.37 | 0.28 | 0.23 |
| `mulmod` | 1.68 | 1.82 | 2.00 | 1.97 | 1.97 | 1.89 | 1.78 | 53.70 | 1.89 | 56.57 | 1.98 | 23.48 | 13.00 | 18.33 | 10.51 | 7.13 | 6.10 |
| `gcd` | 0.96 | 1.61 | 2.20 | 1.89 | 1.80 | 1.94 | 2.07 | 1.96 | 2.05 | 1.97 | 1.95 | 1.95 | 1.94 | 1.91 | 1.92 | 1.90 | 1.49 |
| `str` | 2.18 | 0.05 | 0.04 | 0.04 | 0.04 | 0.04 | 0.03 | 0.03 | 0.03 | 0.03 | 0.04 | 0.04 | 0.03 | 0.03 | 0.02 | 0.02 | 0.01 |
| `parse` | 1.02 | 0.14 | 0.10 | 0.08 | 0.07 | 0.07 | 0.06 | 0.06 | 0.06 | 0.06 | 0.06 | 0.05 | 0.05 | 0.05 | 0.04 | 0.04 | 0.04 |
| `mul1` | 0.27 | 0.31 | 0.28 | 0.32 | 0.34 | 0.34 | 0.34 | 0.36 | 0.39 | 0.41 | 0.45 | 0.49 | 0.56 | 0.67 | 0.63 | 0.67 | 0.78 |
| `addmul1` | 0.21 | 0.21 | 0.21 | 0.22 | 0.22 | 0.25 | 0.24 | 0.23 | 0.26 | 0.27 | 0.29 | 0.32 | 0.39 | 0.43 | 0.44 | 0.45 | 0.50 |
| `mul` | 0.40 | 0.42 | 0.47 | 0.52 | 0.57 | 0.66 | 0.79 | 0.91 | 1.19 | 1.37 | 1.69 | 1.95 | 2.26 | 2.67 | 3.26 | 3.66 | 5.70 |
| `sqr` | 0.32 | 0.45 | 0.51 | 0.53 | 0.59 | 0.65 | 0.70 | 0.75 | 0.87 | 0.92 | 1.07 | 1.26 | 1.42 | 1.65 | 2.05 | 2.32 | 3.75 |
| `kara` | 0.64 | 0.70 | 0.75 | 0.76 | 0.83 | 0.87 | 0.97 | 1.05 | 1.29 | 1.43 | 1.73 | 1.82 | 1.92 | 1.96 | 2.16 | 2.11 | 2.54 |
| `toom` | 0.73 | 0.77 | 0.88 | 0.90 | 0.94 | 0.94 | 1.04 | 1.10 | 1.32 | 1.46 | 1.74 | 1.82 | 1.93 | 1.97 | 2.15 | 2.13 | 2.49 |
| `kara2` | 4.57 | 0.79 | 0.68 | 0.70 | 0.77 | 0.81 | 0.88 | 0.94 | 1.07 | 1.03 | 1.31 | 1.50 | 1.81 | 2.09 | 2.57 | 2.98 | 4.18 |
| `toom2` | 5.17 | 0.90 | 0.78 | 0.80 | 0.90 | 0.91 | 0.95 | 1.01 | 1.11 | 1.05 | 1.33 | 1.49 | 1.78 | 2.08 | 2.56 | 2.32 | 2.63 |
| `fft` | 39.51 | 42.39 | 44.81 | 94.89 | 91.72 | 87.04 | 69.80 | 124.12 | 83.81 | 62.55 | 38.28 | 54.23 | 30.26 | 21.18 | 12.94 | 16.27 | 8.07 |
| `fft2` | 17.21 | 48.64 | 42.43 | 43.80 | 99.25 | 92.36 | 83.73 | 75.26 | 117.47 | 73.39 | 51.43 | 36.77 | 43.64 | 30.72 | 17.97 | 13.35 | 10.44 |
| `auto` | 0.74 | 0.82 | 0.91 | 0.91 | 0.97 | 0.97 | 1.05 | 1.12 | 1.34 | 1.47 | 1.74 | 1.82 | 1.94 | 1.97 | 2.15 | 2.10 | 2.48 |
| `ksqr` | 0.44 | 0.59 | 0.67 | 0.67 | 0.74 | 0.78 | 0.79 | 0.83 | 0.88 | 0.94 | 1.07 | 1.22 | 1.21 | 1.34 | 1.36 | 1.44 | 1.74 |
| `fftsqr` | 22.69 | 31.97 | 34.11 | 69.71 | 66.88 | 63.92 | 51.76 | 90.12 | 60.37 | 44.85 | 27.73 | 38.58 | 21.38 | 14.99 | 9.19 | 11.54 | 5.69 |
| `toomsqr` | 0.45 | 0.62 | 0.71 | 0.71 | 0.74 | 0.77 | 0.80 | 0.82 | 0.89 | 0.94 | 1.08 | 1.21 | 1.23 | 1.36 | 1.37 | 1.45 | 1.77 |
| `autosqr` | 0.43 | 0.59 | 0.66 | 0.67 | 0.75 | 0.79 | 0.82 | 0.84 | 0.88 | 0.94 | 1.07 | 1.21 | 1.23 | 1.36 | 1.37 | 1.46 | 1.76 |
| `mulref` | 0.23 | 0.31 | 0.45 | 0.58 | 0.99 | 1.36 | 2.12 | 2.80 | 3.93 | 5.05 | 6.37 | 7.38 | 8.58 | 9.90 | 12.03 | 13.47 | 21.07 |
| `badd` | 0.32 | 0.43 | 0.38 | 0.47 | 0.48 | 0.49 | 0.49 | 0.50 | 0.54 | 0.57 | 0.63 | 0.70 | 0.79 | 0.90 | 0.79 | 0.89 | 1.01 |
| `bsub` | 0.53 | 0.38 | 0.44 | 0.39 | 0.39 | 0.40 | 0.42 | 0.41 | 0.44 | 0.47 | 0.55 | 0.61 | 0.72 | 0.85 | 0.87 | 0.91 | 1.19 |
| `bmul` | 0.32 | 0.88 | 0.96 | 0.99 | 1.04 | 1.04 | 1.10 | 1.14 | 1.34 | 1.48 | 1.76 | 1.84 | 1.93 | 1.98 | 2.16 | 2.11 | 2.49 |
| `bdiv` | 0.46 | 1.31 | 1.28 | 1.49 | 1.63 | 1.66 | 1.81 | 1.96 | 2.05 | 2.19 | 2.43 | 2.38 | 2.34 | 2.45 | 2.37 | 2.87 | 2.90 |
| `bmod` | 0.55 | 1.12 | 1.10 | 1.46 | 1.60 | 1.47 | 1.53 | 1.72 | 1.65 | 1.55 | 1.56 | 1.52 | 1.54 | 1.63 | 1.76 | 2.08 | 2.17 |
| `bdiv1` | 1.54 | 0.39 | 0.40 | 0.40 | 0.46 | 0.48 | 0.52 | 0.56 | 0.62 | 0.67 | 0.75 | 0.79 | 0.84 | 0.91 | 0.87 | 0.90 | 0.98 |
| `bmod1` | 1.53 | 0.32 | 0.36 | 0.40 | 0.45 | 0.48 | 0.54 | 0.59 | 0.66 | 0.72 | 0.80 | 0.84 | 0.91 | 0.94 | 0.94 | 0.97 | 1.01 |
| `band` | 0.26 | 0.36 | 0.36 | 0.36 | 0.36 | 0.37 | 0.39 | 0.40 | 0.42 | 0.44 | 0.51 | 0.63 | 0.67 | 0.75 | 0.63 | 0.71 | 0.82 |
| `bor` | 0.14 | 0.32 | 0.33 | 0.32 | 0.35 | 0.36 | 0.37 | 0.39 | 0.44 | 0.47 | 0.54 | 0.60 | 0.69 | 0.82 | 0.72 | 0.76 | 0.96 |
| `bxor` | 0.13 | 0.32 | 0.32 | 0.33 | 0.35 | 0.36 | 0.37 | 0.39 | 0.44 | 0.46 | 0.53 | 0.59 | 0.70 | 0.83 | 0.70 | 0.79 | 0.97 |
| `bgcd` | 0.79 | 1.46 | 2.13 | 1.83 | 1.76 | 1.88 | 2.01 | 1.92 | 2.00 | 1.93 | 1.94 | 1.94 | 1.91 | 1.89 | 1.92 | 1.90 | 1.49 |
| `blcm` | 0.37 | 1.02 | 1.69 | 1.56 | 1.60 | 1.75 | 1.90 | 1.81 | 1.91 | 1.85 | 1.90 | 1.91 | 1.91 | 1.91 | 1.93 | 1.92 | 1.55 |
| `bsqr` | 0.25 | 0.69 | 0.76 | 0.79 | 0.88 | 0.89 | 0.91 | 0.90 | 0.92 | 0.97 | 1.08 | 1.24 | 1.23 | 1.36 | 1.37 | 1.45 | 1.77 |
| `bpow` | 1.21 | 1.82 | 1.75 | 1.71 | 1.69 | 1.64 | 1.59 | 1.40 | 1.51 | 1.64 | 1.88 | 2.12 | 2.21 | 2.26 | 2.40 | 2.46 | 2.71 |
| `bshl` | 0.49 | 0.53 | 0.54 | 0.54 | 0.54 | 0.54 | 0.54 | 0.54 | 0.56 | 0.55 | 0.58 | 0.59 | 0.62 | 0.66 | 0.50 | 0.53 | 0.62 |
| `bshr` | 1.37 | 0.51 | 0.50 | 0.50 | 0.52 | 0.54 | 0.57 | 0.50 | 0.50 | 0.51 | 0.51 | 0.53 | 0.56 | 0.62 | 0.49 | 0.54 | 0.60 |
| `bsqrt` | 0.23 | 0.65 | 0.91 | 1.09 | 1.39 | 1.09 | 1.31 | 0.97 | 1.10 | 0.69 | 0.55 | 0.39 | 0.30 | 0.20 | 0.16 | 0.14 | 0.12 |
| `blog2` | 0.58 | 1.10 | 1.10 | 1.10 | 1.10 | 1.10 | 1.09 | 1.08 | 1.10 | 1.08 | 1.06 | 1.09 | 1.09 | 1.09 | 1.08 | 1.10 | 1.08 |
| `btonat` | 1.02 | 1.75 | 2.69 | 3.90 | 6.34 | 8.39 | 13.10 | 17.37 | 26.84 | 34.91 | 51.80 | 67.07 | 98.26 | 123.20 | 136.14 | 158.10 | 246.76 |
| `bofnat` | 1.89 | 1.52 | 1.96 | 2.23 | 4.20 | 4.97 | 8.33 | 10.86 | 16.25 | 21.49 | 33.08 | 43.02 | 62.87 | 81.03 | 81.68 | 109.58 | 159.73 |
| `bcmp` | 0.93 | 0.94 | 0.92 | 0.95 | 0.93 | 0.95 | 0.98 | 0.96 | 0.96 | 0.97 | 1.14 | 1.03 | 1.03 | 1.03 | 1.02 | 1.02 | 1.01 |
| `beq` | 1.16 | 1.34 | 1.31 | 1.29 | 1.23 | 1.18 | 1.10 | 1.02 | 0.87 | 0.78 | 0.66 | 0.57 | 0.45 | 0.36 | 0.28 | 0.25 | 0.19 |
| `bhash` | 1.02 | 0.28 | 0.29 | 0.29 | 0.29 | 0.29 | 0.29 | 0.29 | 0.29 | 0.29 | 0.29 | 0.29 | 0.30 | 0.29 | 0.29 | 0.29 | 0.29 |
| `btostr` | 0.92 | 0.05 | 0.03 | 0.03 | 0.04 | 0.04 | 0.03 | 0.03 | 0.03 | 0.03 | 0.04 | 0.04 | 0.03 | 0.03 | 0.02 | 0.02 | 0.01 |
| `bofstr` | 1.73 | 0.22 | 0.15 | 0.13 | 0.11 | 0.10 | 0.10 | 0.09 | 0.09 | 0.09 | 0.08 | 0.08 | 0.08 | 0.07 | 0.06 | 0.06 | 0.05 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 36.4 ns | 37.3 ns | 38 ns | 39.3 ns | 40.7 ns | 41.7 ns | 44.1 ns | 45.9 ns | 50.6 ns | 55.4 ns | 66.2 ns | 78.8 ns | 106 ns | 136 ns | 191 ns | 234 ns | 435 ns |
| `sub` | 37.8 ns | 38.7 ns | 39.6 ns | 40.8 ns | 42.7 ns | 43.9 ns | 46.4 ns | 48.8 ns | 54.3 ns | 60.7 ns | 76.1 ns | 92.8 ns | 128 ns | 166 ns | 231 ns | 292 ns | 544 ns |
| `shl` | 43.4 ns | 43.8 ns | 42.8 ns | 43.3 ns | 44.2 ns | 44.5 ns | 44.5 ns | 45.3 ns | 46.8 ns | 48.8 ns | 52.6 ns | 57.1 ns | 66.3 ns | 78.9 ns | 96.7 ns | 115 ns | 197 ns |
| `shr` | 30.2 ns | 41.9 ns | 43.2 ns | 43 ns | 44.7 ns | 47.7 ns | 51.4 ns | 45.3 ns | 47.2 ns | 49.3 ns | 53.3 ns | 57.7 ns | 67.6 ns | 79.8 ns | 97.1 ns | 116 ns | 197 ns |
| `div1` | 52.9 ns | 54.6 ns | 57 ns | 60.1 ns | 66.9 ns | 74.4 ns | 84.5 ns | 96.3 ns | 123 ns | 147 ns | 199 ns | 246 ns | 351 ns | 451 ns | 650 ns | 851 ns | 1.65 µs |
| `div1u` | 60.8 ns | 65.5 ns | 71.1 ns | 74.4 ns | 80.7 ns | 87.7 ns | 99.5 ns | 114 ns | 140 ns | 165 ns | 215 ns | 267 ns | 371 ns | 478 ns | 683 ns | 891 ns | 1.73 µs |
| `sbdiv` | 77.1 ns | 143 ns | 164 ns | 234 ns | 282 ns | 283 ns | 400 ns | 576 ns | 882 ns | 1.28 µs | 2.23 µs | 3.59 µs | 6.88 µs | 11.8 µs | 24.1 µs | 41.6 µs | 155 µs |
| `div` | 93.4 ns | 123 ns | 142 ns | 205 ns | 248 ns | 266 ns | 379 ns | 536 ns | 837 ns | 1.22 µs | 2.21 µs | 3.55 µs | 6.83 µs | 11.7 µs | 24.1 µs | 47.6 µs | 149 µs |
| `divmod` | 93.6 ns | 156 ns | 174 ns | 245 ns | 291 ns | 291 ns | 405 ns | 610 ns | 917 ns | 1.32 µs | 2.25 µs | 3.64 µs | 6.93 µs | 11.8 µs | 24.2 µs | 47.8 µs | 149 µs |
| `sqrt` | 166 ns | 389 ns | 1.24 µs | 1.21 µs | 1.9 µs | 2.48 µs | 2.98 µs | 3.54 µs | 4.02 µs | 3.93 µs | 5.33 µs | 5.91 µs | 7.77 µs | 9.86 µs | 14.7 µs | 19.8 µs | 50.8 µs |
| `mulmod` | 239 ns | 255 ns | 260 ns | 268 ns | 284 ns | 301 ns | 357 ns | 13.8 µs | 721 ns | 31 µs | 1.86 µs | 33.1 µs | 34.7 µs | 74.8 µs | 78.5 µs | 83.4 µs | 183 µs |
| `gcd` | 104 ns | 286 ns | 843 ns | 1.05 µs | 1.65 µs | 2.48 µs | 4.04 µs | 5.24 µs | 8.74 µs | 11.9 µs | 19.3 µs | 27.7 µs | 47.4 µs | 70 µs | 128 µs | 201 µs | 592 µs |
| `str` | 79.7 ns | 336 ns | 474 ns | 634 ns | 1.18 µs | 1.52 µs | 2.02 µs | 3 µs | 4.72 µs | 6.93 µs | 13.2 µs | 19.2 µs | 29.2 µs | 43.2 µs | 65.9 µs | 108 µs | 281 µs |
| `parse` | 254 ns | 559 ns | 763 ns | 966 ns | 1.39 µs | 1.79 µs | 2.67 µs | 3.55 µs | 5.33 µs | 7.12 µs | 10.9 µs | 14.8 µs | 23.2 µs | 32.7 µs | 54.3 µs | 78.9 µs | 210 µs |
| `mul1` | 46.8 ns | 47.5 ns | 47.7 ns | 48 ns | 51.1 ns | 52.1 ns | 52.6 ns | 56.2 ns | 62.5 ns | 68.2 ns | 80.5 ns | 93.4 ns | 119 ns | 154 ns | 203 ns | 254 ns | 454 ns |
| `addmul1` | 47.9 ns | 48.5 ns | 50.2 ns | 49.7 ns | 50.7 ns | 52.1 ns | 54.7 ns | 57.5 ns | 64.5 ns | 71.1 ns | 84.9 ns | 101 ns | 132 ns | 168 ns | 227 ns | 283 ns | 504 ns |
| `mul` | 57.2 ns | 58.1 ns | 61.7 ns | 71.1 ns | 82.8 ns | 106 ns | 157 ns | 233 ns | 456 ns | 753 ns | 1.59 µs | 2.77 µs | 6.1 µs | 10.9 µs | 24.4 µs | 43.2 µs | 171 µs |
| `sqr` | 58 ns | 61.1 ns | 65.7 ns | 71.5 ns | 84 ns | 104 ns | 140 ns | 190 ns | 332 ns | 504 ns | 1 µs | 1.77 µs | 3.82 µs | 6.69 µs | 15.2 µs | 27.2 µs | 111 µs |
| `kara` | 90.3 ns | 94.7 ns | 96.4 ns | 103 ns | 119 ns | 138 ns | 195 ns | 269 ns | 491 ns | 786 ns | 1.63 µs | 2.56 µs | 5.17 µs | 8.01 µs | 16.1 µs | 24.9 µs | 76.2 µs |
| `toom` | 103 ns | 106 ns | 114 ns | 122 ns | 134 ns | 151 ns | 208 ns | 282 ns | 503 ns | 800 ns | 1.64 µs | 2.57 µs | 5.18 µs | 8.04 µs | 16.1 µs | 24.9 µs | 74.7 µs |
| `kara2` | 58.9 ns | 93.6 ns | 92.9 ns | 97.1 ns | 104 ns | 117 ns | 146 ns | 180 ns | 290 ns | 447 ns | 867 ns | 1.46 µs | 3.19 µs | 5.55 µs | 12.3 µs | 21.7 µs | 85.7 µs |
| `toom2` | 67.7 ns | 107 ns | 107 ns | 110 ns | 121 ns | 131 ns | 158 ns | 192 ns | 300 ns | 458 ns | 883 ns | 1.46 µs | 3.15 µs | 5.57 µs | 12.3 µs | 16.9 µs | 53.9 µs |
| `fft` | 5.61 µs | 5.85 µs | 5.87 µs | 13 µs | 13.3 µs | 14.1 µs | 14.1 µs | 31.9 µs | 32.1 µs | 34.4 µs | 36.1 µs | 77 µs | 81.4 µs | 86.4 µs | 96.8 µs | 192 µs | 242 µs |
| `fft2` | 222 ns | 5.74 µs | 5.77 µs | 6 µs | 13.2 µs | 13.3 µs | 13.9 µs | 14.3 µs | 31.6 µs | 32 µs | 34.1 µs | 36 µs | 76.8 µs | 81.4 µs | 86.1 µs | 96.9 µs | 214 µs |
| `auto` | 105 ns | 112 ns | 117 ns | 123 ns | 139 ns | 155 ns | 210 ns | 287 ns | 511 ns | 805 ns | 1.64 µs | 2.58 µs | 5.19 µs | 8.05 µs | 16.1 µs | 24.8 µs | 74.5 µs |
| `ksqr` | 79.4 ns | 80.4 ns | 85 ns | 90.4 ns | 105 ns | 123 ns | 158 ns | 211 ns | 338 ns | 512 ns | 1 µs | 1.72 µs | 3.28 µs | 5.43 µs | 10.1 µs | 16.8 µs | 51.5 µs |
| `fftsqr` | 4.13 µs | 4.38 µs | 4.4 µs | 9.48 µs | 9.63 µs | 10.1 µs | 10.3 µs | 22.8 µs | 23 µs | 24.4 µs | 25.9 µs | 54.4 µs | 57.5 µs | 60.7 µs | 68.4 µs | 135 µs | 169 µs |
| `toomsqr` | 82.4 ns | 84.4 ns | 89.7 ns | 94.9 ns | 106 ns | 122 ns | 159 ns | 209 ns | 339 ns | 512 ns | 1.01 µs | 1.72 µs | 3.31 µs | 5.5 µs | 10.2 µs | 17.1 µs | 52.5 µs |
| `autosqr` | 78.5 ns | 80.9 ns | 85.5 ns | 91.1 ns | 107 ns | 125 ns | 164 ns | 213 ns | 338 ns | 513 ns | 1 µs | 1.71 µs | 3.32 µs | 5.52 µs | 10.2 µs | 17.1 µs | 52.4 µs |
| `mulref` | 33.3 ns | 42.9 ns | 58.5 ns | 79.2 ns | 142 ns | 217 ns | 425 ns | 713 ns | 1.5 µs | 2.78 µs | 5.99 µs | 10.4 µs | 23 µs | 40.4 µs | 90 µs | 159 µs | 632 µs |
| `badd` | 44.5 ns | 51.3 ns | 51.9 ns | 57.1 ns | 58 ns | 59.8 ns | 59.3 ns | 61.4 ns | 67.7 ns | 73.5 ns | 85.5 ns | 99.4 ns | 126 ns | 155 ns | 203 ns | 250 ns | 454 ns |
| `bsub` | 64 ns | 53.8 ns | 54.1 ns | 55 ns | 56 ns | 56.9 ns | 60.2 ns | 62.1 ns | 67.8 ns | 75.4 ns | 91.1 ns | 107 ns | 137 ns | 175 ns | 238 ns | 300 ns | 559 ns |
| `bmul` | 45.4 ns | 122 ns | 126 ns | 135 ns | 150 ns | 167 ns | 222 ns | 293 ns | 512 ns | 811 ns | 1.65 µs | 2.6 µs | 5.19 µs | 8.07 µs | 16.1 µs | 24.9 µs | 74.6 µs |
| `bdiv` | 56.6 ns | 162 ns | 182 ns | 239 ns | 283 ns | 300 ns | 410 ns | 571 ns | 871 ns | 1.26 µs | 2.25 µs | 3.59 µs | 6.89 µs | 11.8 µs | 24.2 µs | 47.6 µs | 149 µs |
| `bmod` | 29.6 ns | 145 ns | 164 ns | 238 ns | 287 ns | 290 ns | 408 ns | 608 ns | 927 ns | 1.32 µs | 2.3 µs | 3.73 µs | 7.11 µs | 12 µs | 24.6 µs | 47.7 µs | 149 µs |
| `bdiv1` | 19.5 ns | 59.3 ns | 62.3 ns | 64.5 ns | 75.7 ns | 81.3 ns | 92.2 ns | 106 ns | 132 ns | 159 ns | 211 ns | 260 ns | 355 ns | 464 ns | 665 ns | 854 ns | 1.68 µs |
| `bmod1` | 19.4 ns | 30.1 ns | 34 ns | 38.4 ns | 44.5 ns | 50.4 ns | 62.4 ns | 73.3 ns | 97 ns | 121 ns | 167 ns | 213 ns | 306 ns | 404 ns | 587 ns | 769 ns | 1.52 µs |
| `band` | 19.5 ns | 41 ns | 41.7 ns | 41.9 ns | 42.7 ns | 43.2 ns | 45.3 ns | 47.2 ns | 51.5 ns | 56.4 ns | 67.2 ns | 87.5 ns | 103 ns | 128 ns | 163 ns | 202 ns | 364 ns |
| `bor` | 19.5 ns | 36.5 ns | 37.3 ns | 37.2 ns | 39.7 ns | 41.7 ns | 43.2 ns | 46.1 ns | 52.6 ns | 58.4 ns | 70.2 ns | 83.1 ns | 106 ns | 138 ns | 185 ns | 233 ns | 439 ns |
| `bxor` | 18.7 ns | 35.7 ns | 36.5 ns | 37.5 ns | 39.7 ns | 41.3 ns | 42.7 ns | 45.6 ns | 51.4 ns | 57.1 ns | 69.5 ns | 82.1 ns | 105 ns | 138 ns | 184 ns | 233 ns | 438 ns |
| `bgcd` | 85.2 ns | 260 ns | 817 ns | 1.02 µs | 1.61 µs | 2.4 µs | 3.94 µs | 5.12 µs | 8.52 µs | 11.7 µs | 19.2 µs | 27.6 µs | 46.7 µs | 69.2 µs | 128 µs | 201 µs | 592 µs |
| `blcm` | 122 ns | 427 ns | 1.07 µs | 1.28 µs | 1.9 µs | 2.76 µs | 4.38 µs | 5.66 µs | 9.34 µs | 12.7 µs | 21.3 µs | 30.8 µs | 53.2 µs | 79.5 µs | 146 µs | 229 µs | 672 µs |
| `bsqr` | 46 ns | 99 ns | 102 ns | 112 ns | 130 ns | 147 ns | 187 ns | 237 ns | 362 ns | 534 ns | 1.02 µs | 1.76 µs | 3.32 µs | 5.5 µs | 10.2 µs | 17.1 µs | 52.5 µs |
| `bpow` | 182 ns | 224 ns | 243 ns | 263 ns | 309 ns | 361 ns | 510 ns | 718 ns | 1.27 µs | 2.05 µs | 4.26 µs | 7.27 µs | 14.1 µs | 22.1 µs | 43.2 µs | 67.9 µs | 204 µs |
| `bshl` | 70 ns | 61.5 ns | 61.9 ns | 62.2 ns | 63.1 ns | 62.1 ns | 63.2 ns | 63.7 ns | 65.2 ns | 66.5 ns | 71.5 ns | 75.2 ns | 84.8 ns | 97.4 ns | 116 ns | 137 ns | 217 ns |
| `bshr` | 20.9 ns | 58.4 ns | 58.2 ns | 58.8 ns | 60.4 ns | 63.4 ns | 67.1 ns | 61.5 ns | 63 ns | 65.6 ns | 69.1 ns | 73.6 ns | 82.3 ns | 96.1 ns | 115 ns | 136 ns | 214 ns |
| `bsqrt` | 266 ns | 1.04 µs | 1.72 µs | 2.03 µs | 2.76 µs | 2.52 µs | 3.6 µs | 3.45 µs | 5.3 µs | 4.86 µs | 6.46 µs | 7.38 µs | 10.9 µs | 14.2 µs | 22.2 µs | 33.7 µs | 104 µs |
| `blog2` | 19 ns | 21.8 ns | 21.8 ns | 21.8 ns | 22.1 ns | 22.1 ns | 22 ns | 21.8 ns | 22.1 ns | 22.1 ns | 21.8 ns | 22.3 ns | 22.3 ns | 22.3 ns | 21.8 ns | 22.1 ns | 21.8 ns |
| `btonat` | 17.9 ns | 272 ns | 463 ns | 613 ns | 982 ns | 1.3 µs | 2.03 µs | 2.71 µs | 4.16 µs | 5.55 µs | 8.34 µs | 11 µs | 16.9 µs | 22.3 µs | 33.9 µs | 44.9 µs | 91.3 µs |
| `bofnat` | 25.2 ns | 228 ns | 328 ns | 337 ns | 634 ns | 745 ns | 1.25 µs | 1.65 µs | 2.47 µs | 3.31 µs | 5.16 µs | 6.84 µs | 10.5 µs | 14.1 µs | 21.4 µs | 28.6 µs | 58.3 µs |
| `bcmp` | 13.6 ns | 16.8 ns | 16.8 ns | 17.8 ns | 18.3 ns | 19.5 ns | 21.9 ns | 23.6 ns | 27.1 ns | 30.5 ns | 43.9 ns | 50.8 ns | 64.7 ns | 78.5 ns | 106 ns | 134 ns | 245 ns |
| `beq` | 17 ns | 24 ns | 24 ns | 24.2 ns | 24.2 ns | 24.2 ns | 24.4 ns | 24.4 ns | 24.4 ns | 24.5 ns | 25.3 ns | 25.9 ns | 26.6 ns | 27.6 ns | 29.4 ns | 33 ns | 47.3 ns |
| `bhash` | 19.3 ns | 19.6 ns | 20 ns | 19.9 ns | 20 ns | 20 ns | 20 ns | 20 ns | 20 ns | 19.9 ns | 20 ns | 19.7 ns | 20.4 ns | 20 ns | 19.7 ns | 19.7 ns | 19.7 ns |
| `btostr` | 33.5 ns | 334 ns | 470 ns | 613 ns | 1.17 µs | 1.49 µs | 1.97 µs | 3 µs | 4.71 µs | 6.97 µs | 13.4 µs | 19.3 µs | 29.1 µs | 43.5 µs | 66 µs | 108 µs | 280 µs |
| `bofstr` | 427 ns | 865 ns | 1.18 µs | 1.5 µs | 2.17 µs | 2.8 µs | 4.17 µs | 5.52 µs | 8.24 µs | 11 µs | 16.7 µs | 22.7 µs | 34.9 µs | 48.2 µs | 77.6 µs | 110 µs | 271 µs |

Ratio MPN / mpn, to GMP's kernel without allocating the result:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 2.78 | 2.80 | 2.81 | 2.95 | 2.97 | 3.02 | 3.11 | 3.12 | 3.16 | 3.13 | 3.12 | 3.19 | 3.32 | 3.49 | 3.58 | 3.43 | 3.35 |
| `sub` | 2.93 | 2.93 | 2.89 | 2.98 | 3.01 | 3.09 | 3.20 | 3.28 | 3.33 | 3.41 | 3.57 | 3.73 | 3.98 | 4.15 | 4.29 | 4.26 | 4.22 |
| `shl` | 3.50 | 3.48 | 3.45 | 3.36 | 3.43 | 3.40 | 3.35 | 3.36 | 3.34 | 3.34 | 2.74 | 2.67 | 2.70 | 2.76 | 2.61 | 2.43 | 2.42 |
| `shr` | 2.44 | 3.38 | 3.38 | 3.36 | 3.47 | 3.64 | 3.86 | 3.36 | 3.32 | 3.31 | 3.19 | 3.14 | 3.06 | 3.11 | 2.91 | 2.71 | 2.58 |
| `div1` | 3.62 | 3.57 | 3.52 | 3.36 | 3.05 | 2.79 | 2.30 | 2.09 | 1.91 | 1.76 | 1.64 | 1.55 | 1.49 | 1.44 | 1.40 | 1.38 | 1.35 |
| `div1u` | 3.78 | 3.81 | 3.74 | 3.58 | 3.14 | 2.89 | 2.46 | 2.24 | 1.99 | 1.82 | 1.64 | 1.53 | 1.43 | 1.40 | 1.34 | 1.33 | 1.30 |
| `sbdiv` | 4.10 | 5.81 | 4.05 | 4.40 | 4.01 | 3.30 | 2.56 | 2.41 | 1.98 | 1.76 | 1.66 | 1.55 | 1.55 | 1.65 | 1.76 | 1.86 | 2.28 |
| `div` | 4.99 | 5.12 | 3.52 | 3.85 | 3.53 | 3.11 | 2.45 | 2.24 | 1.88 | 1.68 | 1.65 | 1.54 | 1.54 | 1.63 | 1.76 | 2.12 | 2.19 |
| `divmod` | 5.01 | 6.47 | 4.31 | 4.61 | 4.15 | 3.39 | 2.60 | 2.55 | 2.06 | 1.80 | 1.69 | 1.57 | 1.56 | 1.64 | 1.75 | 2.13 | 2.19 |
| `sqrt` | 11.22 | 21.49 | 21.57 | 25.64 | 27.30 | 23.40 | 23.46 | 22.55 | 17.95 | 14.61 | 13.00 | 10.33 | 7.77 | 6.36 | 4.90 | 4.27 | 3.58 |
| `mulmod` | 17.70 | 18.21 | 14.69 | 12.18 | 8.82 | 6.62 | 4.25 | 101.47 | 2.79 | 75.24 | 2.32 | 26.06 | 14.16 | 19.74 | 10.99 | 7.32 | 6.22 |
| `gcd` | 1.72 | 1.77 | 2.35 | 1.97 | 1.85 | 1.97 | 2.09 | 1.98 | 2.06 | 1.98 | 1.96 | 1.95 | 1.94 | 1.91 | 1.92 | 1.90 | 1.49 |
| `str` | 2.12 | 5.57 | 5.15 | 5.56 | 6.56 | 6.01 | 4.67 | 4.59 | 3.93 | 3.63 | 5.55 | 5.30 | 5.02 | 4.82 | 4.31 | 4.56 | 4.23 |
| `parse` | 10.28 | 17.09 | 18.79 | 19.24 | 19.89 | 19.74 | 19.21 | 18.02 | 16.30 | 14.71 | 12.33 | 10.65 | 8.38 | 7.92 | 6.98 | 6.74 | 6.29 |
| `mul1` | 3.71 | 3.77 | 3.64 | 3.56 | 3.79 | 3.67 | 3.31 | 3.19 | 2.96 | 2.78 | 2.56 | 2.43 | 2.28 | 2.33 | 2.16 | 2.10 | 1.91 |
| `addmul1` | 3.80 | 3.73 | 3.83 | 3.85 | 3.70 | 3.62 | 3.36 | 3.16 | 2.92 | 2.73 | 2.50 | 2.42 | 2.31 | 2.30 | 2.18 | 2.10 | 1.89 |
| `mul` | 4.30 | 4.15 | 3.51 | 3.23 | 2.57 | 2.35 | 1.87 | 1.71 | 1.76 | 1.83 | 1.99 | 2.18 | 2.49 | 2.88 | 3.41 | 3.79 | 5.82 |
| `sqr` | 4.68 | 4.81 | 4.69 | 4.26 | 3.70 | 3.39 | 2.67 | 2.33 | 2.04 | 2.00 | 1.98 | 2.26 | 2.43 | 2.76 | 3.39 | 3.78 | 5.78 |
| `kara` | 6.89 | 6.76 | 5.45 | 4.68 | 3.71 | 3.05 | 2.32 | 1.98 | 1.90 | 1.91 | 2.04 | 2.02 | 2.11 | 2.11 | 2.25 | 2.18 | 2.60 |
| `toom` | 7.86 | 7.57 | 6.44 | 5.55 | 4.17 | 3.34 | 2.48 | 2.07 | 1.95 | 1.95 | 2.04 | 2.02 | 2.11 | 2.12 | 2.25 | 2.18 | 2.54 |
| `kara2` | 4.50 | 6.93 | 6.15 | 5.36 | 4.50 | 3.97 | 2.99 | 2.35 | 1.88 | 1.46 | 1.64 | 1.77 | 2.08 | 2.30 | 2.75 | 3.14 | 4.31 |
| `toom2` | 5.17 | 7.93 | 7.09 | 6.08 | 5.24 | 4.44 | 3.24 | 2.51 | 1.95 | 1.50 | 1.67 | 1.77 | 2.06 | 2.31 | 2.73 | 2.44 | 2.69 |
| `fft` | 428.24 | 417.86 | 331.64 | 590.91 | 413.04 | 311.26 | 167.86 | 234.56 | 124.42 | 83.70 | 45.12 | 60.63 | 33.22 | 22.74 | 13.54 | 16.84 | 8.26 |
| `fft2` | 16.95 | 425.19 | 382.12 | 331.49 | 571.43 | 450.85 | 284.84 | 187.42 | 205.19 | 105.26 | 64.46 | 43.64 | 50.20 | 34.06 | 19.18 | 14.00 | 10.75 |
| `auto` | 8.02 | 8.00 | 6.61 | 5.59 | 4.32 | 3.44 | 2.50 | 2.11 | 1.97 | 1.96 | 2.04 | 2.03 | 2.12 | 2.12 | 2.25 | 2.18 | 2.54 |
| `ksqr` | 6.35 | 6.33 | 6.07 | 5.38 | 4.63 | 4.02 | 3.02 | 2.60 | 2.09 | 2.02 | 1.98 | 2.19 | 2.10 | 2.25 | 2.25 | 2.33 | 2.68 |
| `fftsqr` | 344.17 | 344.88 | 314.29 | 564.29 | 424.23 | 330.07 | 196.94 | 280.79 | 141.98 | 97.21 | 51.08 | 69.21 | 36.86 | 25.19 | 15.27 | 18.78 | 8.80 |
| `toomsqr` | 6.87 | 6.65 | 6.41 | 5.65 | 4.67 | 3.97 | 3.03 | 2.57 | 2.08 | 2.02 | 2.00 | 2.19 | 2.12 | 2.28 | 2.27 | 2.38 | 2.73 |
| `autosqr` | 6.28 | 6.37 | 6.11 | 5.42 | 4.71 | 4.07 | 3.14 | 2.61 | 2.07 | 2.04 | 1.98 | 2.18 | 2.11 | 2.29 | 2.27 | 2.38 | 2.73 |
| `badd` | 3.40 | 3.86 | 3.84 | 4.29 | 4.20 | 4.33 | 4.18 | 4.18 | 4.20 | 4.15 | 4.01 | 3.85 | 3.94 | 3.96 | 3.79 | 3.70 | 3.47 |
| `bsub` | 4.74 | 3.90 | 3.95 | 3.99 | 3.94 | 4.01 | 4.15 | 4.14 | 4.16 | 4.21 | 4.26 | 4.12 | 4.25 | 4.45 | 4.45 | 4.41 | 4.30 |
| `bmul` | 3.41 | 8.71 | 7.12 | 6.14 | 4.67 | 3.69 | 2.65 | 2.15 | 1.98 | 1.97 | 2.06 | 2.05 | 2.12 | 2.13 | 2.25 | 2.18 | 2.55 |
| `bdiv` | 3.01 | 6.75 | 4.52 | 4.54 | 4.04 | 3.50 | 2.66 | 2.40 | 1.97 | 1.74 | 1.69 | 1.54 | 1.56 | 1.65 | 1.77 | 2.12 | 2.19 |
| `bmod` | 1.58 | 6.04 | 4.07 | 4.52 | 4.11 | 3.36 | 2.60 | 2.55 | 2.09 | 1.84 | 1.73 | 1.61 | 1.60 | 1.69 | 1.78 | 2.13 | 2.19 |
| `bdiv1` | 1.27 | 3.55 | 3.39 | 3.24 | 3.13 | 2.79 | 2.35 | 2.15 | 1.90 | 1.77 | 1.61 | 1.51 | 1.39 | 1.37 | 1.34 | 1.28 | 1.27 |
| `bmod1` | 1.40 | 1.92 | 1.88 | 1.85 | 1.71 | 1.50 | 1.32 | 1.20 | 1.09 | 1.04 | 0.98 | 0.94 | 0.91 | 0.91 | 0.88 | 0.87 | 0.86 |
| `band` | 1.64 | 3.47 | 3.48 | 3.55 | 3.50 | 3.48 | 3.38 | 3.32 | 3.22 | 3.19 | 3.15 | 3.50 | 3.24 | 3.28 | 3.06 | 2.99 | 2.84 |
| `bor` | 1.70 | 3.09 | 3.22 | 3.21 | 3.31 | 3.42 | 3.30 | 3.29 | 3.33 | 3.32 | 3.33 | 3.35 | 3.32 | 3.57 | 3.48 | 3.46 | 3.40 |
| `bxor` | 1.61 | 3.08 | 3.09 | 3.23 | 3.31 | 3.39 | 3.26 | 3.23 | 3.25 | 3.24 | 3.28 | 3.30 | 3.30 | 3.52 | 3.47 | 3.45 | 3.37 |
| `bgcd` | 1.42 | 1.60 | 2.28 | 1.91 | 1.80 | 1.90 | 2.04 | 1.94 | 2.01 | 1.94 | 1.95 | 1.94 | 1.91 | 1.89 | 1.92 | 1.90 | 1.49 |
| `bsqr` | 4.04 | 8.39 | 7.79 | 7.00 | 5.99 | 5.00 | 3.71 | 2.95 | 2.23 | 2.12 | 2.02 | 2.24 | 2.11 | 2.28 | 2.28 | 2.38 | 2.75 |
| `bshl` | 6.31 | 5.44 | 5.58 | 5.36 | 5.44 | 5.26 | 5.27 | 5.22 | 5.05 | 4.82 | 4.55 | 4.30 | 3.93 | 3.85 | 3.54 | 3.23 | 2.86 |
| `bshr` | 1.85 | 5.17 | 4.93 | 4.98 | 5.12 | 5.28 | 5.50 | 4.96 | 4.81 | 4.69 | 4.37 | 4.04 | 3.88 | 3.84 | 3.50 | 3.23 | 2.83 |
| `bsqrt` | 16.02 | 22.41 | 24.68 | 20.78 | 23.59 | 16.15 | 17.82 | 13.37 | 15.23 | 10.06 | 8.52 | 6.77 | 5.62 | 4.66 | 3.78 | 3.49 | 3.32 |
| `bcmp` | 1.18 | 1.44 | 1.41 | 1.47 | 1.45 | 1.48 | 1.53 | 1.55 | 1.64 | 1.56 | 1.97 | 1.59 | 1.70 | 1.72 | 1.78 | 1.84 | 1.90 |
| `btostr` | 0.91 | 5.62 | 5.09 | 5.38 | 6.54 | 5.89 | 4.56 | 4.59 | 3.92 | 3.65 | 5.68 | 5.35 | 5.01 | 4.87 | 4.31 | 4.56 | 4.22 |
| `bofstr` | 17.29 | 25.22 | 28.85 | 30.00 | 30.96 | 30.37 | 29.79 | 28.16 | 25.28 | 22.73 | 18.91 | 16.33 | 12.64 | 11.61 | 9.97 | 9.40 | 8.14 |

### Against GMP's kernels

The third table divides by GMP's kernels, which neither allocate their results nor pass through
Lean's `mpz` layer, so its small sizes show the library's fixed costs as much as its loops:

- **Linear operations** (`add`, `sub`, shifts, `mul1`, `addmul1`) are 1.9–4.3× `mpn`, `sub` up to
  4.3 from 128 limbs; on `MPN.Nat` (`badd` … `bxor`, `bshl`, `bshr`) 2.8–6.3× from 2 limbs, with
  the result's allocation and trim.
- **Products** (`auto`) are 2.0–2.5× `mpn_mul` from 16 to 512 limbs and 2.6–3.3× from 1024 to
  65536, but 3.4–8.0× up to 8 limbs; **squares** (`autosqr`) 2.0–2.4× from 24 to 256 limbs and
  2.7–3.7× from 512.
- **Division** (`div`) is 1.5–2.2× `mpn_tdiv_qr` from 16 to 512 limbs and 2.3–3.0× above, 2.5–5.1×
  below 16; by a word, `bdiv1` and `bmod1` are 0.86–1.8× `mpn_divrem_1` and `mpn_mod_1` from 32
  limbs.
- **`gcd`** is 1.5–2.2× `mpn_gcd` at every size from 4 limbs.
- **Over 4×:** `sqrt`, 10–27× `mpn_sqrtrem` up to 64 limbs and 3.4–4.3× from 256; `parse`, 5.7–20×
  `mpn_set_str` (`bofstr` 8–31×); `str`, 3.6–6.6× `mpn_get_str`; and every operation below about 8
  limbs, where allocation dominates. Against `Nat` these gaps do not show: Lean's `Nat.sqrt`,
  `Nat.repr` and `String.toNat?` are not GMP's, and its wrapper costs as much as the library's.

### Large sizes

The tables above stop at 512 limbs, below the reach of `mulToom`. These are from
`bench kara toom kara2 toom2 512 768 1024 1536 2048 4096`, the fastest of three runs, on
2026-11-09 (`a0aeba1`). The sizes are those of the larger operand.

| op | 512 | 768 | 1024 | 1536 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `kara` | 76.5 µs (2.54, 2.61) | 151 µs (2.87, 2.91) | 233 µs (3.06, 3.10) | 457 µs (3.24, 3.24) | 705 µs (3.29, 3.37) | 2.14 ms (4.17, 4.42) |
| `toom` | 74.9 µs (2.49, 2.55) | 136 µs (2.59, 2.62) | 207 µs (2.72, 2.76) | 363 µs (2.57, 2.59) | 544 µs (2.59, 2.60) | 1.46 ms (2.85, 3.20) |
| `kara2` | 86.8 µs (4.21, 4.36) | 194 µs (5.40, 5.53) | 341 µs (6.09, 6.19) | 767 µs (7.52, 7.59) | 1.37 ms (9.01, 9.07) | 5.57 ms (15.82, 16.78) |
| `toom2` | 54.1 µs (2.63, 2.72) | 99 µs (2.75, 2.81) | 159 µs (2.84, 2.89) | 293 µs (2.84, 2.90) | 446 µs (2.93, 2.95) | 1.2 ms (3.22, 3.63) |

The ratios to `Nat` and to `mpn` (`mpn_mul`) are in parentheses. `mulKaratsuba` splits both
operands at half the larger one, which needs the smaller one to be longer than that half, so on
`n` by `n / 2` limbs it is `mulBasecase`, and its ratio grows with the size. Toom-3 by 2 and Toom-4 by 2 keep it near 3. At
512 by 256 limbs `toom2` is still `mulKaratsuba`, so still `mulBasecase`.

### Large sizes, multiplication

From `bench toom fft auto toom2 fft2 mulmod 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-11-09 (`a0aeba1`), with the ratios to `Nat` and to `mpn`
(`mpn_mul`) in parentheses. `mulmod` is the product modulo `β^n - 1` of two operands of `n` limbs,
against the whole product on the other sides.

| op | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `toom` | 204 µs (2.69, 2.71) | 544 µs (2.53, 2.60) | 970 µs (2.68, 2.95) | 1.46 ms (2.86, 3.04) | 3.68 ms (2.85, 3.12) | 9.41 ms (3.35, 3.78) | 24.4 ms (3.76, 4.12) | 60.7 ms (4.50, 4.93) |
| `fft` | 534 µs (7.04, 7.13) | 811 µs (3.84, 3.88) | 1.18 ms (3.56, 3.58) | 1.74 ms (3.88, 3.90) | 3.3 ms (3.06, 3.08) | 7.34 ms (3.29, 3.32) | 16.1 ms (3.00, 3.01) | 35.9 ms (2.66, 2.92) |
| `auto` | 208 µs (2.73, 2.78) | 543 µs (2.57, 2.59) | 971 µs (2.92, 2.94) | 1.46 ms (3.24, 3.27) | 3.28 ms (3.04, 3.07) | 7.35 ms (3.30, 3.31) | 16.1 ms (3.00, 3.01) | 35.9 ms (2.90, 3.26) |
| `toom2` | 157 µs (2.80, 2.84) | 448 µs (2.95, 2.97) | 798 µs (3.23, 3.26) | 1.21 ms (3.60, 3.62) | 3.23 ms (4.22, 4.24) | 8.53 ms (5.02, 5.02) | 21.6 ms (5.52, 5.57) | 55.6 ms (5.72, 6.47) |
| `fft2` | 303 µs (5.41, 5.48) | 665 µs (4.38, 4.40) | 890 µs (3.59, 3.63) | 1.18 ms (3.53, 3.54) | 2.51 ms (3.27, 3.29) | 5.35 ms (3.13, 3.15) | 11.6 ms (2.97, 2.98) | 27.5 ms (2.83, 3.20) |
| `mulmod` | 229 µs (3.01, 3.05) | 509 µs (2.41, 2.42) | 632 µs (1.90, 1.92) | 776 µs (1.73, 1.74) | 1.73 ms (1.60, 1.60) | 3.3 ms (1.48, 1.49) | 7.38 ms (1.37, 1.38) | 16.2 ms (1.20, 1.47) |

### Unbalanced products

`MPN.mul`, the ratios to `Nat` and to `mpn` (`mpn_mul`), the fastest of three runs, on 2026-11-09
(`a0aeba1`): `auto2`,
`auto4`, `auto8` for `n` by `n / 2`, `n / 4`, `n / 8` limbs, and `autobS` for `n` by `S` limbs.

| n | `auto` | `auto2` | `auto4` | `auto8` | `b64` | `b128` | `b256` | `b320` | `b512` | `b1024` | `b2048` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.14, 2.19 | 2.28, 2.41 | 2.09, 2.23 | 1.52, 1.66 |  |  |  |  |  |  |  |
| 512 | 2.49, 2.55 | 2.49, 2.55 | 2.31, 2.39 | 2.11, 2.20 |  |  |  |  |  |  |  |
| 1024 | 2.70, 2.73 | 2.71, 2.75 | 2.49, 2.53 | 2.32, 2.38 | 2.12, 2.18 | 2.31, 2.36 | 2.48, 2.52 | 2.61, 2.64 | 2.71, 2.74 | 2.69, 2.72 | 2.74, 2.72 |
| 2048 | 2.52, 2.60 | 2.75, 2.77 | 2.71, 2.73 | 2.49, 2.52 |  |  |  |  |  |  |  |
| 3072 | 2.68, 2.85 | 2.95, 2.98 | 2.65, 2.68 | 2.71, 2.75 |  |  |  |  |  |  |  |
| 4096 | 2.83, 3.00 | 3.28, 3.29 | 3.14, 3.16 | 2.70, 2.74 | 2.10, 2.14 | 2.30, 2.34 | 2.49, 2.52 | 2.57, 2.60 | 2.69, 2.71 | 3.12, 3.15 | 3.27, 3.29 |
| 6144 | 2.77, 3.00 | 3.49, 3.52 | 4.07, 4.11 | 2.63, 2.63 |  |  |  |  |  |  |  |
| 8192 | 2.52, 2.78 | 3.27, 3.29 | 3.45, 3.47 | 2.90, 2.92 |  |  |  |  |  |  |  |
| 16384 | 2.68, 2.95 | 3.13, 3.13 | 3.20, 3.23 | 2.96, 2.98 | 2.09, 2.12 | 2.30, 2.35 | 2.45, 2.48 | 2.58, 2.60 | 2.69, 2.72 | 2.92, 2.95 | 2.96, 2.98 |
| 32768 | 2.44, 2.72 | 2.99, 3.01 | 3.04, 3.05 | 2.79, 2.80 |  |  |  |  |  |  |  |
| 65536 | 2.62, 2.92 | 2.84, 3.21 | 2.86, 3.27 | 3.01, 3.03 | 2.08, 2.12 | 2.30, 2.33 | 2.47, 2.50 | 2.57, 2.60 | 2.69, 2.72 | 2.89, 2.90 | 3.27, 3.30 |

Before the split, the products whose smaller operand was below the Toom shapes went to the
schoolbook method: 5–6 times `Nat` at `n` by 256 or 320 limbs, 10.8 at 1536 by 384. The cell
left above 4, 6144 by 1536 (4.13), is where the FFT and the Toom methods tie.

### Large sizes, division

From `bench sbdiv div sqrt 512 1024 2048 4096 8192 16384`, the fastest of three runs, on
2026-11-09 (`a0aeba1`). The sizes are those of the divisor (`div`, `sbdiv`:
`2 n` by `n` limbs) or of the operand (`sqrt`).

| op | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
|---|---:|---:|---:|---:|---:|---:|
| `sbdiv` | 155 µs (3.03, 2.27) | 599 µs (3.99, 3.04) | 2.37 ms (6.14, 4.87) | 9.86 ms (9.39, 8.29) | 37.3 ms (16.08, 14.29) | 149 ms (26.05, 22.24) |
| `div` | 149 µs (2.92, 2.19) | 460 µs (3.07, 2.34) | 1.35 ms (3.50, 2.77) | 3.54 ms (3.63, 2.97) | 7.79 ms (3.62, 2.98) | 16.4 ms (2.89, 2.58) |
| `sqrt` | 50.8 µs (0.23, 3.55) | 152 µs (0.18, 3.37) | 460 µs (0.19, 3.43) | 1.35 ms (0.20, 3.53) | 3.81 ms (0.23, 3.74) | 9.99 ms (0.24, 3.92) |

The ratios to `Nat` and to `mpn` are in parentheses; for `sqrt` the first is to Lean's `Nat.sqrt`,
not to GMP, and the second to `mpn_sqrtrem`. `div`
is divide and conquer up to `divQMu = 4096` divisor limbs, whose `O(M(n) log n)` makes its ratio
grow with the size, and from there Barrett's division by the reciprocal of the top half of the
divisor, as GMP's, which brings it back to 2.9 at 16384 limbs (2.6 against `mpn_tdiv_qr`, which
also computes the remainder).

### Large sizes, gcd and decimal strings

From `bench gcd str parse 512 1024 2048 4096 8192`, the fastest of three runs, on 2026-11-09
(`a0aeba1`), with the ratios to `Nat` and to `mpn` in parentheses. `str` and `parse` compare with
Lean's `Nat.repr` and `String.toNat?`, which are written in Lean, and with GMP's `mpn_get_str` and
`mpn_set_str`; `gcd` compares with `Nat.gcd`, GMP's `mpz_gcd`, and with `mpn_gcd`.

| op | 512 | 1024 | 2048 | 4096 | 8192 |
|---|---:|---:|---:|---:|---:|
| `gcd` | 599 µs (1.50, 1.51) | 1.94 ms (1.52, 1.52) | 6.44 ms (1.81, 1.82) | 19.1 ms (2.03, 2.03) | 54.2 ms (2.23, 2.23) |
| `str` | 278 µs (0.01, 4.20) | 778 µs (0.01, 4.09) | 2.19 ms (0.01, 3.95) | 6.12 ms (0.01, 3.83) | 16.5 ms (0.00, 3.78) |
| `parse` | 210 µs (0.03, 6.29) | 626 µs (0.03, 6.61) | 1.91 ms (0.03, 7.07) | 4.59 ms (0.02, 6.17) | 11.1 ms (0.01, 5.66) |

`gcd` is Lehmer's algorithm with steps of about 62 bits, like GMP's: two runs of Euclid's steps on
the leading words, the second on the leading 128 bits after the first (`cofactors2`), applied by
`mulSubMul` in one pass for each number; and from `gcdHalf = 1536` limbs half-gcd of the top
third of the limbs, as GMP's `mpn_gcd`, whose base case up to `hgcdBase = 128` limbs is the same
steps with the matrix updated in one pass per entry (`mulAddMul`); above the base case it runs on
the generic layer. At 16384 limbs `gcd` takes 151 ms, 2.51 times `Nat`. `gcdh<T>` sweeps `gcdHalf`.

### Large sizes, squares

From `bench ksqr toomsqr fftsqr autosqr 512 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-11-09 (`a0aeba1`), with the ratios to `Nat` and to `mpn`
(`mpn_sqr`) in parentheses.

| op | 512 | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ksqr` | 52.1 µs (1.75, 2.71) | 158 µs (2.10, 3.14) | 480 µs (2.25, 3.50) | 885 µs (2.47, 4.21) | 1.45 ms (2.85, 5.00) | 4.38 ms (3.45, 6.51) | 13.2 ms (4.85, 9.30) | 39.8 ms (6.20, 11.60) | 120 ms (9.02, 17.02) |
| `toomsqr` | 52.8 µs (1.77, 2.75) | 150 µs (1.99, 2.98) | 420 µs (2.01, 3.04) | 688 µs (2.10, 3.28) | 1.08 ms (2.43, 3.74) | 2.8 ms (2.62, 4.17) | 7.36 ms (3.36, 5.18) | 18.3 ms (3.46, 5.34) | 46.5 ms (3.50, 6.58) |
| `fftsqr` | 168 µs (5.64, 8.75) | 369 µs (4.89, 7.34) | 543 µs (2.60, 3.96) | 772 µs (2.35, 3.68) | 1.17 ms (2.64, 4.05) | 2.24 ms (2.09, 3.33) | 5.02 ms (2.28, 3.54) | 11.1 ms (2.10, 3.23) | 24.9 ms (1.87, 3.53) |
| `autosqr` | 53.2 µs (1.79, 2.77) | 151 µs (2.00, 3.00) | 419 µs (2.00, 3.06) | 691 µs (2.11, 3.29) | 1.08 ms (2.42, 3.74) | 2.24 ms (2.09, 3.32) | 5.04 ms (2.30, 3.55) | 11.1 ms (2.09, 3.24) | 24.9 ms (1.87, 3.52) |

**Tuning.**

- `fftK` comes from a sweep of `fft4` to `fft11` at 1024 to 65536 limbs per operand: the best
  number of pieces `K` has `K² / T` between 8 and 32 for `T` limbs in all, and the least `k` with
  `4ᵏ ≥ 10 T` is within 6% of the best everywhere (at 4096 limbs per operand, `k = 9` where 8 is
  best). For squares (`fsq6` to `fsq11`) it is the best from 8192 limbs and within 4% below.
- Toom-4 and Toom-4 by 3 beat Toom-3 by 5–9% from 1024 limbs, more above (the FFT takes over
  there); `mulToom4` between 384 and 1000 limbs makes no difference beyond ±2%, and is 600.
- Toom-6 beats Toom-4 by 3–8% from 1536 limbs, with `mulToom6` from 1000 to 2200 limbs
  within ±1% of each other; it is 1000.
- With Toom-6, the FFT ties `toom` at 4096 limbs per operand, balanced, but passes `toom2` at 3072
  by 1536, hence `mulFFT = 4096` limbs in the larger operand and `mulFFTUnbal = 3072`
  when the operands differ by `3 : 2` or more (it was 3072 for both with Toom-4, and 5120 limbs
  in all before).
- With `S` limbs in the smaller operand, below 384, `mulToom` is the schoolbook method, about
  3.5 µs per limb of `S` at 4096 limbs in the other and 14 µs at 16384, while the FFT costs what
  its total does (0.9 ms, 3.6 ms). They cross at `S` ≈ 260 for 4096 and 16384 limbs and 326 for
  65536 (`fftbS`, `toombS`), hence `mulFFTMin = 320`.
- Unbalanced products are split when the larger operand has at least twice the limbs of the
  smaller, which has at least `mulUnbalanced = 96`: pieces of the size of the smaller, each by
  `mulBal`. With 1536 limbs or more in the smaller operand, one FFT on the whole product beats
  one per piece by 10–20% (`autobS` against `fftbS`), and they tie at 1024: hence
  `mulChunkMax = 1024` when the larger operand is in the range of the FFT.
- The Toom-3 square passes `ksqr` at 600 to 768 limbs (2–3% slower at 512, 6–14% faster from
  1024), hence `sqrToom3 = 600`; the Toom-4 square adds 6–10% at 1024, 1536, 3072 and
  4096 limbs with a threshold of 700 or 1000, and is 1000. `fftsqr` passes `toomsqr` at 2816
  limbs, hence `sqrFFT = 2816` (it was 2048, against `ksqr`).
- The Toom-6 square gains 0–5% on the Toom-4 square (3% at 2048 limbs, 5% at 4096), with
  `sqrToom6` from 1200 to 2400 within noise; it is 1200, and `sqrFFT` stays.
- A product whose larger operand has twice the limbs of the smaller is always unbalanced for the
  FFT, which wins those from `mulFFTUnbal = 3072` limbs: the pieces of `mulChunked` beyond
  `mulChunkMax` stop there (4000 by 1700 limbs 1.41 → 1.15 ms).

## History

Times are the fastest of five runs, in the format of the tables above.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-22 | `5c419ae` | baseline: verified `add`/`sub`, `mul1`/`addMul1`, `mulBasecase` and `mulComba` on `UInt64` limbs, plain `Nat`-indexed loops | `mul` 184 ns at 4 limbs, 1.34 µs at 16, 17.7 µs at 64; `comba` 372 ns, 1.94 µs, 16.0 µs; `mulref` 92.2 ns, 887 ns, 13.2 µs |
| 2026-10-22 | `b13f8e6`+ | `add`/`sub` on `USlice`: `USize` indices, `uget`/`uset` without bounds checks; Lean `v4.36.0-rc1` (other rows within ±4%) | `add` 86.4 → 65.5 ns at 4 limbs, 130 → 80.2 ns at 16, 312 → 138 ns at 64, 1.01 µs → 346 ns at 256; `sub` likewise (−20%, −35%, −54%, −63%) |
| 2026-10-22 | `6c5e6dc`+ | `mul1`, `addMul1`, `mulBasecase` and `mulComba` on `USlice` with `USize` indices (`mulref` unchanged, ±1%) | `mul` 188 → 121 ns at 4 limbs, 1.35 µs → 551 ns at 16, 17.7 → 5.77 µs at 64, 264 → 79.1 µs at 256; `comba` 352 → 304 ns, 1.86 → 1.27 µs, 15.8 → 7.16 µs, 193 → 61.5 µs; `mul1`/`addmul1` −12–16% at 4 limbs, −58–68% from 64 |
| 2026-10-22 | `f5ee946`+ | `mulKaratsuba`, with `karatsubaThreshold = 64` chosen from a sweep of 8–96; in-place `addInto`/`subInto` | `kara` vs `mul`: 17.4 vs 20.6 µs at 128 limbs, 54.2 vs 78.4 µs at 256, 166 vs 305 µs at 512; below 64 limbs it is `mul` |
| 2026-10-22 | `f5ee946`+ | `mulBasecase` rows with `addMul1LoopK`, a specialized continuation instead of a pair and a boxed carry per row | `mul` 116 → 93.8 ns at 4 limbs, 238 → 154 ns at 8, 557 → 382 ns at 16, 5.69 → 4.91 µs at 64; `kara` −19–20% from 64 limbs (17.5 → 14.1 µs at 128, 167 → 136 µs at 512) |
| 2026-10-22 | `f5ee946`+ | the add/sub, `mul1` and `addMul1` loops through `foldUInPlaceThen` (`@[csimp]`): the array is made exclusive once per loop, not at every store | `add` 144 → 116 ns at 64 limbs, 368 → 274 ns at 256; `mul1`/`addmul1` −17–21% from 64; `mul` −24–31% from 4 limbs (4.85 → 3.49 µs at 64); `kara` −28–31% from 16 (135 → 94.4 µs at 512); `comba` (not converted) and `mulref` ±2% |
| 2026-10-22 | `727ea63`+ | `sqrBasecase` and `sqrKaratsuba` (`sqrKaratsubaThreshold = 96`, from a sweep of 24–128) | `sqr` vs `mul`: 200 vs 256 ns at 16 limbs, 1.82 vs 3.45 µs at 64, 28.8 vs 56.1 µs at 256; `ksqr` 3.67 µs at 96 limbs, 19.5 µs at 256, 59.8 µs at 512 (`kara` 94.4 µs) |
| 2026-10-23 | `bfe1b4c`+ | `mulToom`: Toom-3, Toom-3 by 2 and Toom-4 by 2 with the points `0, 1, 2, 3, ∞`, `toom3Threshold = 384`; new rows `toom`, `kara2`, `toom2` (large sizes above) | `toom` vs `kara`: 90.4 vs 94.8 µs at 512 limbs, 269 vs 292 µs at 1024, 775 vs 882 µs at 2048, 2.10 vs 2.66 ms at 4096; `toom2` vs `kara2` (`n` by `n / 2`): 210 vs 449 µs at 1024, 660 µs vs 1.79 ms at 2048, 1.56 vs 7.10 ms at 4096 |
| 2026-10-23 | `0b52bb2`+ | `MPN.FFT.fftMul`: Schönhage–Strassen on one flat array, in-place residues modulo `2^(64 n) + 1`, the forward and inverse transforms without a bit-reversal permutation; three copies of the whole array found with `gdb` on `lean_copy_sarray` and removed (a continuation reading the array before its loop, a pair kept alive past a write, and a parameter the compiler inferred as borrowed) | `fft` 71.9 → 10.7 ms at 16384 limbs before and after removing the copies; vs `toom`: 1.96 vs 2.10 ms at 4096, 4.09 vs 5.97 ms at 8192, 21.9 vs 45.4 ms at 32768 |
| 2026-10-23 | `a9d488f`+ | `fftK` from a sweep of `k` (the least `k` with `4ᵏ ≥ 10 T`, was `⌊log₂ T⌋ / 2 + 1`); `MPN.mul`, the FFT from `fftThreshold = 5120` limbs in all, `mulToom` below; new rows `fft2`, `auto` | `fft` 1.96 → 1.82 ms at 4096 limbs, 4.09 → 3.62 ms at 8192, 10.7 → 8.08 ms at 16384, 21.9 → 18.2 ms at 32768; `auto` within 3.3–4.0 of `Nat` from 1024 to 65536 limbs |
| 2026-10-23 | `514bf31`+ | `fftMinSmall` measured (320, was a guess of 512); `MPN.FFT.fftSqr`, one forward transform and pointwise squares; `MPN.sqr`, the FFT from `sqrFFTThreshold = 2048` limbs, `sqrKaratsuba` below; new rows `fftsqr`, `toomsqr`, `autosqr` | `autosqr` vs `ksqr`: 1.21 vs 1.67 ms at 4096 limbs, 5.29 vs 15.2 ms at 16384, 26.5 vs 137 ms at 65536; within 2.0–2.7 of `Nat` from 1024 limbs |
| 2026-10-23 | `a446651`+ | Toom-4 and Toom-4 by 3 (points `0, …, 5, ∞`, the interpolation in place with `rshiftInto` and `divExact5Into`), from `toom4Threshold = 600` limbs; `fftThreshold` now on the larger operand, 3072 limbs | `toom` 776 → 708 µs at 2048 limbs, 2.08 → 1.92 ms at 4096, 17.1 → 14.2 ms at 16384, 127 → 99.8 ms at 65536; `auto` within 3.0–4.0 of `Nat` from 1024 to 65536 limbs |
| 2026-10-23 | `6b4baa3`+ | unbalanced products split into pieces of the size of the smaller operand (`mulChunked`), from `chunkMinSmall = 96` limbs, below `chunkMaxSmall = 1024` when the larger operand is in the range of the FFT; new rows `auto2`, `auto4`, `auto8`, `autobS` | `MPN.mul` at 1536 by 384 limbs 10.8 → 3.3 times `Nat`, at `n` by 256 5.4 → 3.1, at 2048 by 512 8.0 → 3.3; every shape measured within 4 but 6144 by 1536 (4.27) |
| 2026-10-23 | `877a7a6`+ | Toom-3 and Toom-4 squares (`sqrToom`: one set of evaluations, squares for the products, the interpolations of the products), from `toom3SqrThreshold = 600` and `toom4SqrThreshold = 1000` limbs; `MPN.sqr` uses them below `sqrFFTThreshold`, now 2816 | `autosqr` 186 → 169 µs at 1024 limbs, 569 → 485 µs at 2048, 1.07 ms → 823 µs at 3072; within 2.0–2.7 of `Nat` from 512 to 65536 limbs |
| 2026-10-23 | `7afea80`+ | Toom-6 (points `0, …, 9, ∞`, the interpolation of degree 10 generated, 130 steps in place, its proof through `extract_lets`; exact division by any odd constant, `divExact7Into`, `divExact9Into`), from `toom6Threshold = 1000` limbs; `fftThreshold` 4096 and `fftThresholdUnbal` 3072 | `toom` 979 → 915 µs at 2560 limbs, 14.2 → 12.3 ms at 16384, 99.8 → 81.3 ms at 65536; `auto` at 3072 limbs 1.28 → 1.19 ms |
| 2026-10-23 | `a7402ca`+ | the Toom-6 square, from `toom6SqrThreshold = 1200` limbs; `mulChunked` beyond `chunkMaxSmall` only below `fftThresholdUnbal` | `toomsqr` 500 → 485 µs at 2048 limbs, 1.29 → 1.23 ms at 4096; 4000 by 1700 limbs 1.41 → 1.15 ms (4.03 → 3.26 times `Nat`) |
| 2026-10-23 | `767df92`+ | `MPN.Bits`: `lshift`/`rshift` by `0 < s < 64` (one pass, `foldUInPlaceThen`), `shiftLeft`/`shiftRight` by any number of bits, `log2`; new rows `shl`, `shr` | `shl` 0.41–0.64 of `Nat` from 2 to 64 limbs, 345 ns at 512 (1.05); `shr` likewise, 313 ns at 512 (0.92); at one limb `Nat`'s `>>>` returns a scalar without allocating (3.46) |
| 2026-10-24 | `0568ff8`+ | `MPN.divRem1`, schoolbook `MPN.divRem`, `MPN.Num` and `MPN.sqrtRem` (Zimmermann); new rows `div1`, `div`, `sqrt` | `div1` 0.40–0.98 of `Nat` up to 32 limbs, 1.64 at 512; `div` 2.9–5.9 (5.19 at 512, 9.4 at 2048 by 1024: no divide-and-conquer yet); `sqrt` 39 µs at 256 limbs, 89 µs at 512 (0.40 of Lean's `Nat.sqrt`) |
| 2026-10-24 | `0e975af`+ | divide-and-conquer division (`MPN.Num.divNorm`, Burnikel and Ziegler, the remainder of the estimate reused as in GMP) from `dcThreshold = 512` limbs, in `Num.divMod` and so in `sqrtRem`; new row `sbdiv` (large sizes above) | `div` vs `sbdiv` at `2 n` by `n`: 690 vs 904 µs at 1024 limbs, 1.96 vs 3.55 ms at 2048, 14.9 vs 56.6 ms at 8192 (6.29 vs 23.98 times `Nat`); `sqrt` 1.04 → 0.685 ms at 2048 limbs |
| 2026-10-24 | `ef5cd91`+ | schoolbook division in one array without allocating per step (`divStepIn`, `divLoopIn`): the quotient limb in the freed top limb of the window, the multiply-subtract fold ended by a continuation | `sbdiv` 429 → 251 ns at 2 limbs, 1.56 µs → 649 ns at 16, 7.77 → 4.52 µs at 64, 70.1 → 58.0 µs at 256 (4.20 → 3.47 times `Nat`); `div` within 3.5 of `Nat` up to 256 limbs, 4.04 at 512, 4.22 at 1024, 6.07 at 8192 |
| 2026-10-24 | `88fcfff`+ | products modulo `β^N - 1` by the FFT (`fft_coef_cyc`, `fftMulModAt`, `Num.mulModB`, `Num.modB`), like GMP's `mpn_mulmod_bnm1`; new row `mulmod` | `mulmod` vs `auto` (`n` by `n`): 839 µs vs 1.85 ms at 4096 limbs, 1.86 vs 3.69 ms at 8192, 3.67 vs 8.23 ms at 16384, 8.19 vs 18.6 ms at 32768 (0.45–0.5 of a product) |
| 2026-10-24 | `d813acd`+ | all tables regenerated (five runs of the default sizes, three of each large-size section), with `-falign-loops=64` for the C compiler: the same machine code of the square basecase (`sqrRowsLoop`) ran 11% slower when the library before it grew and moved it across a 64-byte boundary | `sqr` 2.13 → 1.90 µs at 64 limbs, `ksqr` 68.5 → 61.1 µs at 512, `autosqr` back to 2.0–2.7 times `Nat`; `add` 132 → 115 ns at 64 limbs; others within ±3%; `mul` 3.0–4.1 times `Nat` from 1024 limbs, `div` 4.07–6.59 from 512 |
| 2026-10-24 | `c2b5325`+ | `Num.gcd` (Lehmer's algorithm with the one-pass kernel `mulSubMul`, half-gcd from 2048 limbs) and decimal strings (`Num.toDecimal`, `Num.ofDecimal?`), from `main`'s generic layer on the new instance `ops64`; `Num.lt` compares from the top down without allocating; new rows `gcd`, `str`, `parse` (large sizes above) | `gcd` 0.89 of `Nat` at one limb, 4.7–6.4 from 4 limbs (8.8 at 2); `str` 8.35 ms and `parse` 5.51 ms at 4096 limbs (Lean's `Nat.repr` 1.09 s); `div` at 1024 limbs 4.23 → 4.10 from `Num.lt` |
| 2026-10-24 | `3267141`+ | Lehmer steps of 62 bits: a second run of Euclid's steps on the leading 128 bits after the first (`cofactors2`, like GMP's `hgcd2`), cofactors below `2⁶²` checked on words (`eqPlusOne`); the same for half-gcd's base step; `gcdHalf = 4096` | `gcd` 4.06 → 1.60 µs at 4 limbs, 81.4 → 41.7 µs at 64, 603 → 322 µs at 256, 6.49 → 3.32 ms at 1024; 2.5–3.2 times `Nat` from 4 to 1024 limbs, 4.7–5.1 from 4096 |
| 2026-10-24 | `9296210`+ | half-gcd with its own base case (`MPN.baseW`): Lehmer's steps of 62 bits applied by `mulSubMul`, the matrix updated by `mulAddMul` (`a x + b y` in one pass) instead of the generic `baseLoop`'s products, up to `hgcdBase = 128` limbs (was 8); `gcdHalf = 1024` (was 4096), from `gcdh<T>` | `gcd` 43.9 → 29.9 ms at 4096 limbs, 122 → 80.3 ms at 8192, 310 → 219 ms at 16384; 2.9–3.6 times `Nat` from 2048 limbs (was 3.4–5.1) |
| 2026-10-24 | `df64bb8`+ | `gcd2`: Euclid's algorithm on pairs of words like GMP's `mpn_gcd_22` (steps `a - q b` with `q = ⌊a₁ / (b₁ + 1)⌋`, never too large; one `UInt64.div2` and `wordGcd` once `b` fits in a word) when both numbers have at most two limbs; the `gcd` cells for 2 and 3 limbs only, from three runs of `bench gcd 1 2 3 4 5 6 8` (the machine was busy, so the other cells were kept) | `gcd` 1.17 µs → 269 ns at 2 limbs (6.57 → 1.49 times `Nat`), 1.54 → 1.35 µs at 3 (4.06 → 3.45) |
| 2026-10-24 | `e985b32`+ | all tables regenerated (five runs of the default sizes, three of each large-size section) after the gcd work and the split into `main`, `main32` and `main64` | `gcd` 2.37 at 4 limbs, 2.32 at 6, 2.79 at 8 (were 2.89, 2.64, 3.19: the two-word gcd ends each run of Lehmer's steps); the large sizes within 1% of `d813acd`; `add`, `sub`, `shl` 3–10 ns slower at every size with code unchanged since `d813acd` (ratios 0.51 → 0.57 at 4 limbs), likely code layout |
| 2026-10-25 | `4af732e`+ | lean4-scalar-arrays `85c955d` → `49cf1b1` (opaque array types, the array `foldInPlace` dropped, `ensureExclusive` public): `foldUInPlaceThen` calls `ensureExclusive` instead of `ensureExclusiveUnsafe`; tables not regenerated (they are at `85c955d`) | from three runs of `bench --no-nat` on 10 operations at 1 to 256 limbs, within ±2% from 64 limbs and within a few ns below (`sub` 9 ns faster at 1 to 4 limbs, `sqr` 9 ns slower at 1) |
| 2026-10-25 | `5b34dcf`+ | all tables regenerated on lean4-scalar-arrays `49cf1b1` (five runs of the default sizes, three of each large-size section) | within 8% of `e985b32` everywhere except the squares at 65536 limbs, where only `Nat` moved (`autosqr` 2.20 → 2.02 with the same 26.7 ms) |
| 2026-10-25 | `140f314`+ | Karatsuba's middle term in one pass (`karatsubaMid`, from `main32`'s `addDiffInto`): limb `r[k + i] + t[i] - z₀[i] - z₂[i]` with a carry between `-2` and `1` (its high word from `UInt64.addDiffh`, a `__uint128_t` sum), written into `t` with lean4-scalar-arrays' slice fold, then copied into `r` with `copySlice`; it replaces two `subInto` and an `addInto`, for `mulKaratsuba` and `sqrKaratsuba` | from three alternating runs against `5b34dcf`: `kara` 5–7% faster from 128 to 4096 limbs (1024: 287 → 266 µs), `ksqr` 4–7%, `toom`, `toomsqr`, `auto`, `autosqr` 3–7% from 128 to 2048 limbs; unchanged at 4096, where the FFT takes over. Tables not regenerated |
| 2026-10-25 | `98b3367`+ | the square root by `main`'s generic Zimmermann recursion (`NatOps.sqrtRemAux`) over `ops64`, with `sqrt2` on two limbs as its base; `NatOps.sqr` (`Num.sqr` in `ops64`) for the square of the quotient and the radix powers; `trimA` pops zero top limbs in place instead of copying them away, for every operation of `ops64` | from three alternating runs against `140f314`: `sqrt` 9–16% faster from 2 to 64 limbs, 2–4% from 1024; `gcd` 23–27% faster from 4 to 256 limbs, 7% at 4096; `str` 8–13% from 64 limbs, `parse` 2–8%; `div` within ±2.5%. Tables not regenerated |
| 2026-10-25 | `03b1884`+ | the thresholds as `MPN.Config` (as on `main32`), set by the build options of the lakefile; the dispatchers (`mulKaratsuba`, `sqrKaratsuba`, `mulToom`, `sqrToom`, the FFT, `MPN.mul`, `MPN.sqr`) take a `Config` and compare `Nat` thresholds; `lake exe tune` | from three alternating runs against `03b1884`: within ±1% from 16 limbs on `mul`, `sqr`, `div`, `gcd`, `str`, `sqrt`; `mul` 1–3 ns slower at 3 and 4 limbs (+3–5%), where `comba`, unchanged, moves by ±4–7% between the two builds. Defaults unchanged; two runs of `tune` on Zen 3 agree on all but the Toom squares (`sqrToom3` 864 and 480, `sqrToom4` 1152 and 672) |
| 2026-10-25 | `87e5294`+ | `divRem1` by Möller and Granlund's 2-by-1 step with a precomputed reciprocal (`div21`, like GMP's `udiv_qr_2by1`) for a normalized divisor from 12 limbs, each step checked exactly (`q d + r = R β + x`, `r < d`) so that neither the reciprocal nor the error bound needs a proof, `UInt64.div2` again if a check fails; `divRem1R` takes a known reciprocal | from three alternating runs against `87e5294`: `div1` 5–8% faster at 4 and 16 limbs, 26–34% from 64 (1024 limbs: 5.30 → 3.52 µs); `div`, `str` within the ±5% that their unchanged paths move between the two builds |
| 2026-10-25 | `f10e75a`+ | the quotient limbs of the schoolbook division by Möller and Granlund's 3-by-2 step with the reciprocal of the top two limbs of the divisor (`qEstR`, `recip32`, like GMP's `udiv_qr_3by2` and `invert_pi1`), checked exactly, `qEst` when a check fails, from `div32Threshold = 48` limbs in the divisor | from three alternating runs against `87e5294`: `sbdiv` and `div` 1–2% faster from 32 to 128 limbs, unchanged above; with the step at every size, 8–11% slower at 16 and 24 limbs, where computing the reciprocal costs more than the hardware divisions it saves |
| 2026-10-25 | `38e0223`+ | the interpolation of Toom-6 (`interp10`, both products and squares) by forward differences of `h(j) = w_j - j¹⁰ c₁₀` at `0, …, 9` and one exact division by `l!` per Newton coefficient (as on `main32`), 105 passes of which 15 divide or shift, where the divided differences took 130 and 40; generated with its proof by `scripts/toom6_interp.py` | from three alternating runs against `87e5294`: `toom` 2.3–4.5% faster from 1024 to 4096 limbs, `toomsqr` 4.2–6.1% from 1536; unchanged at 768, below Toom-6 |
| 2026-10-25 | `ac859f5`+ | each Toom shape with its own threshold, as on `main32`: `mulToom32 = 176` (Toom-3 by 2), `mulToom42 = 88` (Toom-4 by 2), `mulToom43 = 600` (Toom-4 by 3), where all started at `mulToom3 = 384`; `mulToom6` 1000 → 768 and `sqrToom6` 1200 → 1152 after the cheaper interpolation of Toom-6; `tune` measures the three shapes | from three alternating runs: `MPN.mulToom` on `n` by `s` limbs 7–43% faster where the shapes now start (512 by 256: −43%, 256 by 128: −31%); through `MPN.mul`, which splits shapes of `2 : 1` or more, 2–5% faster at ratios between 1.5 and 2 with the smaller operand from 176 to 384 limbs, unchanged elsewhere; `auto` 5–11% faster from 768 to 960 limbs, `autosqr` 7% at 1152 |
| 2026-10-26 | `cf4189d`+ | lean4-scalar-arrays 49cf1b1 → 187dcd4, whose `foldlInPlaceRangeThen` and `foldlInPlace2Then` replace the two `implemented_by` loops (`foldUInPlaceThen`, `foldUInPlace2Then`) through proved `@[csimp]` lemmas, so that no trusted Lean code is left; the rows of `mulBasecase` and of the square basecase loop outside the continuation of `addMul1LoopK`, which the library's loop would otherwise call once per row | from three alternating runs against the trusted loops on the same library: products and squares 4–10% faster at 4 to 256 limbs, Toom 4–5% faster from 2048; `mul1` 2–7% and `sbdiv` 3–8% slower at 1 to 64 limbs (a few ns per call); the rest within ±5% |
| 2026-10-27 | `983a6b1` | The butterflies and both transforms over the class `WinOps` (`MPN.FFT.Windows`, any limb width), with the instance `winOps64`; `@[expose, specialize]` definitions, so that the compiler calls the residue operations directly | From five runs against `92067b4`: `fft` and `fftsqr` +1–2% at 512 and 1024 limbs, within ±1% from 2048 to 32768; no array copies (gdb on `lean_copy_sarray`) |
| 2026-10-27 | `a29b3bb`+ | The products by the FFT from `main`'s `MPN.FFT.Product` (pieces, the load, pointwise, scale and recombination loops, `fftMulAt`, `fftMulModAt`, `fftSqrAt` and their proofs, for any limb width) on the instance `fftOps64` of `FFTOps`, with `mulToom` and `sqrKaratsuba` as the pointwise products; `MPN.FFT.Mul` 1767 → 916 lines | From five alternating runs against `a29b3bb`: `fft`, `fftsqr`, `mulmod` +0.4–2.7% from 512 to 8192 limbs, ±0.6% at 32768; the same instruction count (279.61 million for `fft` at 512 limbs, +0.006%) with 1–2% more cycles, so code layout |
| 2026-10-27 | `537513e`+ | Division by `main`'s Barrett division with Newton's reciprocal (`NatOps.divMu` on `ops64B`, normalized like divide and conquer) from `divMu = 16384` divisor limbs; below, divide and conquer. Measured at `2n / n`: even at 16384 limbs, ahead from 24576 | `div` 32768 limbs: 82.4 → 73.3 ms (−11%, 6.83 → 6.0× `Nat`), 65536: 204 → 163 ms (−20%, 7.40 → 5.98×); 16384 and below unchanged. The reciprocal costs 2.2 products of `n` limbs and the Barrett step 2.0, both with full products; GMP's whole division costs 2.1 of its own |
| 2026-10-27 | `add6ea5`+ | Barrett's division with wrapped remainders (`main`'s `NatOps.divMuW`): the remainder `x - q d` from residues modulo `β^N - 1`, `q d` by the FFT's `mulModB` (`mulMod64`, by `Num.mul` when the product does not wrap), exact because `recipW` checks its reciprocal through the error term of its last Newton step; `divMu` 16384 → 10240 | From three alternating runs against `add6ea5`: `div` 16384 limbs 33.1 → 29.0 ms (−12%), 32768: 73.3 → 64.0 ms, 65536: 162 → 142 ms (−12%); 5.0–5.5× `Nat` from 8192 limbs (was 5.4–7.4×). The Barrett step costs 1.5 products (was 2.0) |
| 2026-10-28 | `3a63203`+ | Karatsuba and the Toom methods from `main`'s `MPN.Toom` (products, squares, the interpolations generated with their proofs, the dispatchers, for any limb width) on the instance `toomOps64` of `ToomOps`, whose operations check their bounds and otherwise write the value from a `Nat` (never: gdb on the fallback); `Config` extends `Toom.Config`; `MPN.Mul.Toom` 4414 → 112 lines | From three alternating runs against `3a63203`: `kara` +2–3%, `ksqr` +1–3%, `toom` +2–4%, `toom2` +0–4%, `toomsqr` +0–2% from 128 to 4000 limbs, with the same calls of every kernel; `auto` and `autosqr` from 8192, `div`: ±1%. The cost is the `USlice`s that each operation builds for its kernel |
| 2026-10-28 | `03660db`+ | `mulBasecase` adds the rows after the first two at a time (`addMul2Loop`, like `mpn_addmul_2`): one pass reads and writes each limb of the result once for two products of limbs, on `foldlInPlaceRangeWith2AccThen` (lean4-scalar-arrays#49), whose two carries stay unboxed; the two limbs of `b` are bound before the pass, so that the loop takes them as arguments instead of reading them at every limb | From three alternating runs against `03660db`: `mul` (the schoolbook product) −5% to −14% from 12 to 64 limbs, −20% to −24% from 128 on, ±5 ns at 1 to 8 limbs; `kara` −5%, `toom` −4%, `auto`, `fft`, `div`, `gcd` and `str` −2% to −5% from 512 limbs. The library's product is 1.45–3.2× `Nat` from 32 to 32768 limbs; `div` is 5.2–5.9× from 8192 (was 5.3–6.0×) |
| 2026-10-28 | `da595e0` | `Num.div`, the quotient alone, by `main`'s `NatOps.divQMuW` from `divQMu = 5632` divisor limbs: Barrett's estimate of the quotient of `a β` decides `⌊a / d⌋` without the remainder of the last block unless its last limb is within 7 of `β`; the reciprocal from `recipG`, whose every Newton step computes `d μₕ` modulo `β^N - 1` (exact, since its error term is below `β^(n+1)` when `μₕ` is good) and checks its result; `divMu` 10240 → 8192. The `div` row now times `Num.div`, and the new `divmod` row `Num.divMod` | From three alternating runs against `a17c47e` (`div` was `Num.divMod`): quotient alone −5% at 5632 limbs, −9% at 6144, −15% at 8192, −21% at 10240, −22% at 16384, −23% at 32768 (62.6 → 48.0 ms), −26% at 65536 (140 → 104 ms), 3.8–4.6× `Nat` from 5632 limbs and 3.8–3.95× from 16384 (was 4.5–5.5×); `divMod` −8% at 10240, −10% at 16384 and 32768, −12% at 65536; below 5632 unchanged |
| 2026-10-28 | `bbb1e5d` | The residues modulo `2^(64 n) + 1` from `main`'s `MPN.FFT.Fermat` (incrAt, decrAt, normAt, addModAt, subModAt, mulPow2At and the guarded operations of `winOps64`, for any limb width) over `main`'s classes `WordArray` and `WordFolds`, with the instances `wordArray64` and `wordFolds64` (`foldlInPlace2Then`); the specialized loops are on unboxed `size_t` and `uint64_t` | From three alternating runs against `da595e0`: `fft`, `fftsqr` and `mulmod` −0.5% to −2% from 512 to 8192 limbs, ±1% at 32768 |
| 2026-10-29 | `b9e8f68` | The schoolbook division from `main`'s `MPN.Div.Schoolbook` (`qEst`, the checked 3-by-2 step `qEstR`, `addBack`, `divStepIn`, `divLoopIn`, for any limb width) over `WordArray`, whose instance gives the multiply-subtract step (`subMulB`); the divisor as an array and an offset | From three alternating runs against `bbb1e5d`: `sbdiv` −4% to −9% from 2 to 32 limbs, ±1% at 128, +7% at 512 and +8% at 2048 with 13% fewer instructions (the same carry chain; more cycles in the inner loop, so code layout); `div` −2% to −5% up to 32 limbs, +1% to +3% from 128; `gcd` and `str` ±2% |
| 2026-10-29 | `a14de09` | `mulSubMul` and `mulAddMul`, the kernels of Lehmer's step and of the matrices of half-gcd, from `main`'s `MPN.LinComb` over the instance `linComb64` of `LinCombOps` (`msWord`, `maWord`, the signed carry `sval`, `Num.limbAt`) | From three alternating runs against `96243f1`: `gcd` ±2% from 2 to 8192 limbs. Reading the limbs inside the step, rather than by the instance's `limb`, made the compiler box the step's pair at a join point, an allocation per limb: up to 4.5 times slower |
| 2026-10-29 | `dc10903`+ | `MPN.Nat`, `main`'s verified `GNat` on the instance `natLimbs64` of `NatLimbs`: `MPN.Num`'s operations with trimmed results, limb-wise bitwise operations, `sqrtRem` and `Num.gcd`; new rows `badd` … `bofstr` | At 1, 4, 16, 64 and 256 limbs against `Nat`: `badd` 0.33–1.04, `bsub` 0.57–1.07, `bmul` 0.34 at a word, 0.99 at 4 limbs, 2.28 at 256; `bdiv` 1.47 at a word, 2.7–3.0 from 2 to 64 limbs, 3.62 at 256; `bgcd` 1.6–2.3; `bshl`/`bshr` 0.57–1.0 (`bshr` 1.50 at a word, 20 against 14 ns); `bsqrt` 0.27–2.0; `btostr` 0.02–0.05 and `bofstr` 0.06–0.22 from 2 limbs (Lean's decimal code) |
| 2026-10-29 | `d6d60d8` | The greatest common divisor from `main`'s `MPN.NatGcd` (`gcd2`, Lehmer's loop, half-gcd's loop, `lcm`, for any limbs) on `MPN.Nat` with the instance `gcdLimbs64` of `GcdLimbs`, which gives Lehmer's step (`cofactors2`, `applyCof`), the words of `gcd2` (`UInt64.mulh`, `div2`) and half-gcd (`hgcd64`); `MPN.gcdWith` and `Num.gcd` convert their arrays to `MPN.Nat` and back | From three alternating runs against `10bc7af`: `bgcd` −53% at 1 limb (on words), −7% at 2, +2–4% from 3 to 16 limbs, +0.4–1% from 64 (the conversions of each Lehmer step's results); `gcd` (`Num.gcd`) +5–6% to 64 limbs, +1% from 1024 |
| 2026-10-31 | `ce57a98` | `main`'s `LinCombOps.limb` takes a `USize` index, and `linComb64` reads by `LinComb.limbU` (`uget` against the size as a `USize`) instead of `Num.limbAt`: a `Nat` index cost a conversion and a comparison of `Nat`s for each limb of `x` and `y` in `mulSubMul` and `mulAddMul` | From three alternating runs against `f9a3037`: `bgcd` −6% at 64 limbs, −14% at 256, −7% at 1024, −2% at 4096 and 16384, ±1% below 64 |
| 2026-10-31 | `7283bac` | Lehmer's step and half-gcd's base case from `main`'s `MPN.LehmerStep` on the instance `lehmer64` of `LehmerOps`, which gives the leading words, `cofactors2` with one run as the fallback, and the check of the cofactors on words (`wmatOf`); the matrices are its own structure of unboxed words (a structure over the limbs boxed each entry: +10% from 4 to 64 limbs), Lehmer's step builds no matrix, and `wmatOf` is inlined | From three alternating runs against `05f6488`: `bgcd` −1.2% to +1.1% from 2 to 16384 limbs |
| 2026-10-31 | `193427d` | Decimal strings by chunks of nineteen digits from `main`'s `MPN.DecChunks` (`toDecimal` by divisions by `10¹⁹`, the reading of digits by chunks, their proofs) on the instance `dec64` of `DecOps`, with its own unboxed state of reading; the digits of a chunk are counted in a `UInt32` (a `Nat` count made `parse` 7–10% slower) | From three alternating runs against `1b83098`: `str`, `parse`, `btostr`, `bofstr` ±1% from 16 to 1024 limbs, +2% to +4% at 1 and 4 limbs (4–11 ns) |
| 2026-10-31 | `06390c0` | Decimal strings by divide and conquer from `main`'s `DecChunks.toDecimalWith` and `DecChunks.ofDecimalWith` on `ops64` | From three alternating runs against `34bf3ea`: `str` and `parse` ±1% from 16 to 4096 limbs |
| 2026-10-31 | `c150cea` | `lshift` and `rshift` from `main`'s `MPN.Shift` (`WordArray.lshiftW`, `rshiftW`: one in-place fold over the window written, the source read by `uget`, with their proofs) on the windows of slices; the old steps read the source through `USlice` indexing | From three alternating runs against `06390c0`: `shl` −11% at 16 limbs, −22% at 64, −38% at 256, −44% at 1024; `shr` −11% to −43% from 64 limbs, +1% to +2.5% at 4 and 16; `bshl`, `bshr` alike; `div`, `sbdiv`, `sqrt` 0% to −6%; `gcd` +0.5% to +2% |
| 2026-10-31 | `97cd2c7` | `MPN.log2` from `main`'s `WordArray.log2W` (the window from its top nonzero limb, by the new `WordArray.log2` of a limb) and the bitwise operations of `MPN.Nat` from `WordArray.bitW` (one in-place fold by the new `lor` and `xor`, and `land`), with their proofs | From three alternating runs against `8e29d9a`+merge: `gcd` −3% from 4 to 256 limbs, `str` −3% at 4 and 16 limbs, `div` and `sqrt` ±1% (2% at 4 limbs) |
| 2026-10-31 | `97cd2c7`+ | New rows `band`, `bor`, `bxor` (`MPN.Nat` `&&&`, `\|\|\|`, `^^^`); against `Nat` they are 0.14–0.7× up to 256 limbs, 0.9–1.2× from 1024 | Measured on the commit before `97cd2c7` with these rows: `bitW` made them 43–46% faster at 2 limbs, 72–79% at 16, 90–93% at 256 and 4096 (38.1 µs → 2.6–3.3 µs at 4096); the old `bitA` built an array by `ofFn` of `Num.limbAt` |
| 2026-10-31 | `6c83e98` | Conversions between `MPN.Nat` and `Nat` by halves: `main`'s `LimbArray.valAtFast` (the value of the limbs, joined by shifts, `@[csimp]` for `valAt`) and `ofNatPush` (the limbs of a `Nat`, split by shifts, from the low word of each leaf, `@[csimp]` for `ofNatN`), `O(n log n)` instead of limb by limb on growing `Nat`s | `btonat`: 16.1 ms → 0.79 ms at 4096 limbs, 1.30 ms → 0.20 ms at 1024; `bofnat`: 1.34 s → 0.50 ms at 4096, 39.7 ms → 0.12 ms at 1024, 37.5 → 7.2 µs at 64; about 120–190 ns a limb from 64 limbs, which a copy of GMP's limbs in C would cut to a few |
| 2026-10-31 | `main` `pow` | `GNat.pow` stops at the exponent 1: it squared `x` for an exponent 0 that it then dropped, so `x³` took a square of twice the length that it never used | `bpow` −49% at 2 and 16 limbs, −42% at 256, −39% at 4096; 1.3×, 2.6× and 3.0× `Nat` at 16, 256 and 4096 limbs (was 2.6×, 4.6× and 4.9×) |
| 2026-10-31 | `eaa633e` | `Num.lt` by `main`'s `WordArray.ltW` (`@[csimp]`): from the top limb down by `uget`, one comparison for each equal limb and `ltB` at the first that differs, instead of `limbAt` and two comparisons | `bcmp` −14% at 4 limbs, −29% at 16, −56% at 256, −60% at 4096: 0.97–1.01× `Nat` (was 1.3–2.5×); `bsub`, `div`, `gcd` ±1.7% |
| 2026-10-31 | `64aa68a`, `main` `log2` | `MPN.Nat`'s hash of a large number from its size and its bottom and top limbs, in constant time like `Nat`'s (its low word), instead of every limb; `GNat.log2` of words by `UInt64.log2`, and of limbs by `WordArray.log2W` on the array instead of on a new `USlice` | `bhash` 0.22× `Nat` from 2 to 4096 limbs (was 0.32× at 2 limbs up to 56× at 4096); `blog2` 33 → 29 ns from 2 limbs (1.9× `Nat`, 15 ns) |
| 2026-10-31 | `8e9bbe9` | `divRem1` from `main`'s `WordArray.divRem1W` (the loop from the top down over any step, `div2` or the checked 2-by-1 step with the reciprocal, `div21`, all generic), replacing 383 lines | From three alternating runs against `64aa68a`, measured at `9d0e616` (with `div2Rem` and `div1Recip`; the first measurement compared a stale binary with itself): `div1` −5% to −8.5% from 12 limbs (the fallback no longer copies `r`), +2–4% at 1–3; `str` and `btostr` −2% to −6% from 12 limbs; `bdiv`, `bmod`, `sbdiv` +2–7% at 2–16 limbs, which do not call `divRem1`, with the same instruction count (layout); ±1% above |
| 2026-10-31 | `9d0e616` | The size from which `divRem1` takes the steps with the reciprocal is `Config.div1Recip` (default 12), and `lake exe tune` measures it | See the row above |
| 2026-10-31 | `b39f807` | `recip32` from `main`'s generic `WordArray.recip32`; the threshold of the 3-by-2 steps with the reciprocal is `Config.div32Recip` (default 48, was the constant `div32Threshold`), measured by `lake exe tune` | From three alternating runs against `9d0e616`: `sbdiv`, `div` −2.5% to +0.4% from 4 to 512 limbs |
| 2026-10-31 | `7998798` | The square root of `MPN.Nat` takes Newton's iteration (`sqrtNewton`) for roots below `Config.sqrtZimmermann` = 48 limbs and as the base of Zimmermann's recursion up to `Config.sqrtBase` = 19 limbs, as `lake exe tune` finds; before, the recursion went down to roots of one limb | From three alternating runs against `c494c56`: `bsqrt` −10% to −28% from 3 to 32 limbs, +9% at 2, ±5% from 48; `sqrt` (`sqrtRem`, unchanged) +1% to +4% |
| 2026-10-31 | `60bf91f` | Division by an unnormalized limb takes `main`'s `divRem1U` (the dividend shifted into the quotient's window, divided there in place by the checked 2-by-1 steps with the reciprocal of the shifted divisor) from `Config.div1Unnorm` = 48 limbs, where `lake exe tune` finds it winning; new row `div1u` | `lake exe tune`: 261 ns against 279 ns at 48 limbs, 535 ns against 682 ns at 128 (−22%); from three alternating runs against `7b37832`: `div1` +7% at 2 limbs (the test of the divisor), ±2% from 32; `str`, `btostr`, `bmod` −4% to +4% |
| 2026-11-01 | `5c5c5b4` | GMP's algorithm choices as the defaults: the reciprocal steps of division by a limb (normalized or not) and of schoolbook division always (`div1Recip`, `div1Unnorm`, `div32Recip` = 0), the square root by Zimmermann's recursion down to one limb (`sqrtZimmermann`, `sqrtBase` = 1); the size crossovers stay as measured | From three alternating runs against `da4d9b6`: `div1` ±3%; `div1u` +72% up to 4 limbs, +14% at 16, ±0.4% from 64 (the fixed cost of the shift, much of it `UInt64.log2`, a loop over the bits); `sbdiv`, `bdiv` +5% to +9% at 2–16 limbs, ±1% from 64; `bsqrt` +22% to +28% at 4–16 limbs (Newton's iteration off), ±1.5% from 64; `str`, `btostr` ±3% |
| 2026-11-01 | `main` `081b691` | `UInt64.log2` by a binary search (`log2Fast`, `@[csimp]`): six shifts and comparisons instead of the runtime's loop over the bits | From three alternating runs against `ba78955`: `blog2` −40% to −45%; `div1u` −20% up to 4 limbs, −13% at 16, −1% at 256; `bdiv` −17% to −20% up to 4 limbs, −9% at 16; `bsqrt` −3% to −10%; `btostr` −2% to −8%; `div1` +20% at 16 limbs only, with the same instruction count (layout) |
| 2026-11-01 | `2a37702` | `sqrt2` from `main`'s `WordArray.sqrt2W` (Newton's iteration from `2^(⌊log₂ N / 2⌋ + 1)` instead of the all-ones word) | From three alternating runs against `5584458`: `sqrt`, `bsqrt` ±2%; at small sizes the arrays of the recursion take the time (`perf`: allocation and freeing ~45%, `sqrt2` 3%) |
| 2026-11-01 | `main` `b766b6f` | Division by an unnormalized limb forms each limb of `a 2ˢ` in the loop (`divLoopSh`), like GMP's `mpn_divrem_1`, instead of shifting `a` first and dividing in place: one pass instead of two | From four alternating runs against `640da81`: `div1u` −14% at 1 limb, −7% to −11% at 2–4, −3% to −5% from 16; `div1` −2% to −11% up to 16 (the smaller driver); `btostr`, `bsqrt` ±2% (+5.5% `bsqrt` at 1 limb, which does not divide by a limb) |
| 2026-11-01 | `main` `89944f8` | Zimmermann's square root divides by `2t` once per step, for the quotient and the remainder, instead of by `t` and then by 2 | From three alternating runs against `6c5b212`: `bsqrt` −5% from 4 to 64 limbs, −3% at 256, −2% at 1024, ±1% at 2 and 4096 |
| 2026-11-01 | `b561de1`, `main` `baed7bf` | The steps of Zimmermann's square root build `X` and `U` by the new `NatOps.join` (`x βᵏ + y mod βᵏ`, `main`'s `WordArray.joinW`: two copies into one array of zeros) instead of a shift, a cut and an addition | From three alternating runs against the previous commit: `bsqrt` −16% to −21% from 2 to 64 limbs, −6% at 256, −2% at 1024; with it, the recursion beats Newton's iteration (the former `sqrtZimmermann` = 48, `sqrtBase` = 19) from 4 limbs |
| 2026-11-01 | `e20bd7a` | `mul1`, `addMul1`, `subMul1` from `main`'s `WordArray.mul1Step`, `addMul1Step`, `subMul1Step` (the new field `mulAdd2`) with their specs from `main`'s fold lemmas | From three alternating runs against `ca82fbd`: `mul1` −1% to −8%; `addmul1`, `mul`, `sqr`, `div` ±2%; `kara`, `toom` +3% to +5% at 1–16 limbs, where they are the unchanged schoolbook product (layout), ±1% above |
| 2026-11-01 | `3c5d26e` | The linear operations of the Toom methods (`addInto` to `sum`) from `main`'s generic kernels `MPN.Toom.Kernels`; `MPN.Linear` and the wrappers are gone | From three alternating runs against `aa10e79`: `kara`, `toom`, `bmul` −2.5% to −5% from 64 to 1024 limbs; `mul`, `sqr`, `ksqr` ±1%; `toomsqr` +7.6% at 64 limbs, ±3% above |
| 2026-11-01 | `dea9980` | The operations of the FFT (`addRange`, `reduce`, `addCoef`, `zeroRange`) from `main`'s generic kernels `MPN.FFT.Kernels`: `reduce` subtracts the halves of a pointwise product in one pass reading both | From three alternating runs against `5b216e9`: `fft` −0.8% to −2.2%, `fftsqr` −1.2% to −5.7%, `mulmod` −0.6% to −3.2%, `fft2` −0.4% to −3.7% from 1024 to 65536 limbs |
| 2026-11-01 | `a5e6af6` | Addition and subtraction (`Num.add`, `Num.sub`, so `MPN.Nat`'s) from `main`'s generic `addW` and `subW`, with the new field `subC`; the bench rows `add` and `sub` time them (`add` now writes `a.size + 1` limbs) | From three alternating runs against `236cdc9`, 4 to 4096 limbs: `add` −5.3% to −35%, `sub` −1.4% to −26%, `badd` −5.6% to −32%, `bsub` −1.9% to −39%, `sqrt` −9% to −17% to 64 limbs; `fft`, `fftsqr`, `kara`, `div` ±2.3%; `mul` at 4 limbs +11% (its basecase does not add or subtract) |
| 2026-11-01 | `2142117` | `Num.divMod` and `Num.div` through `MPN.Dispatch.Div` (`divN`, `divQN`), the square root through `sqrtBy`; `Num.div` takes `divQMu` from `divDC` on | From two alternating runs against `1db0c1c`, 16 to 32768 limbs: `div`, `divmod`, `bdiv`, `bmod`, `sqrt`, `bsqrt`, `btostr` within ±2.2% |
| 2026-11-01 | `cdbf580` | The square root, half-gcd and Lehmer's step through `MPN.Bridge` over `bridge64`: `Nat.sqrt` computes the root alone, where the array-level `sqrtRemWith` also computed the remainder, and `sqrtRem` on arrays goes through it | From two alternating runs against `0fc1c90`, 4 to 4096 limbs: `bsqrt` −8% to −31%, `bgcd` −0.4% to −5.9%, `sqrt` (`sqrtRem` on arrays) +11.5% at 4 limbs from the conversions, ±0.4% from 16 limbs |
| 2026-11-01 | `73cccd8` | `trimA`, `ofNatN` and `Num.lt` from `main`'s `MPN.Trim` (`trimTo 1`, `ofNatLen`, `ltA` by `ltW`) | From three alternating runs against `cdbf580` with `-falign-functions=64 -falign-loops=64` on both builds, 4 to 256 limbs: `bofnat` −5.1% to +1.5%, `badd`, `bsub`, `bmul` −7.7% to +2.4%; default builds, 4 to 4096 limbs: `bcmp`, `bdiv`, `btostr` within ±2.7% |
| 2026-11-01 | `dd67e5e` | `mulMod64` by the shared `Dispatch.mulModW`; Barrett's division only when the quotient has `divMu` (or `divQMu`) limbs too | From two alternating runs against `73cccd8`: `btostr` −18% at 16384 limbs and −15% at 32768 (the top division of decimal output has a short quotient, now by blocks), `div`, `divmod` within ±1% from 1024 to 32768 limbs except `divmod` +12.5% at exactly 8192 (also with aligned builds; 8320 and 9216 are flat, the profile of the library's code is the same, and the old `mulMod64` back in place removes it: not explained) |
| 2026-11-01 | `530a9f4` | The size crossovers as `tune64` (on `Tune.Shared`) measures them on Zen 3, the choices of algorithm kept as GMP's: `mulFFT` 4096 → 6144, `sqrFFT` 2816 → 5120, `divDC` 512 → 208, `gcdHalf` 1024 → 2560, `parseDC` 512 → 1536, and smaller moves of the Toom thresholds | From two alternating runs against `c776af9`, 16 to 32768 limbs, without `Nat`: `bgcd` −18% and `bofstr` −18% at 1024 limbs, `bmul` −14% and `bsqr` −8.5% at 4096, `btostr` −4% to −7% from 4096, `bdiv`, `bmod` −1% to −4.5% from 1024, the rest within ±3.3% |
| 2026-11-05 | `4143568` | Schoolbook division two quotient limbs per pass (`Schoolbook.divLoop2In`) from `div2Rows = 16` divisor limbs: the two limbs estimated together by two checked 3-by-2 steps and Knuth's test by the third divisor limb, one multiply-subtract pass of two rows with its carries off the dependency chain (`subMul2W`) | From three alternating runs against `8dafb3a`, without `Nat`: `sbdiv` −12.6% at 64 limbs, −24% to −35% from 128 to 4096; `div`, `divmod` −12% at 64, −24% at 128, −11% at 256, −7% at 512, −5% at 1024, −1.2% to −2.6% at 2048 and 4096, ±1.4% below 32; `bsqrt` −4% to −10% and `btostr` −2% to −5% from 256 limbs |
| 2026-11-06 | `adfb500` | Schoolbook division from `main`'s shared `MPN.Div.Basecase` (`Schoolbook.divRemN`): the operands normalized by shifts into new arrays (the divisor not copied when already normalized), the quotient and the remainder copied out by the new `WordArray.extract`; `divRem` returns new arrays instead of writing into given ones | From three alternating runs against `d9c0a41`, without `Nat`: `div`, `divmod` −41% to −45% at 2 and 3 limbs, −26% at 4, −31% at 8, −11% to −14% at 16, −6% to −7% at 32, −2% at 64 and 256, −1% to −1.6% at 1024; `sbdiv` −47% at 2, −28% at 4, −31% at 8, −12% at 16, −5% at 32, ±0.5% from 256; with aligned builds also `bsqrt` −4% to −8% up to 64 limbs and −1.5% from 1024, `bgcd` −7.7% at 8 and ±1.5% elsewhere |
| 2026-11-06 | `c30bc5e` | The normalization before division by blocks (`Num.divMod`, `Num.div`) by `main`'s `Schoolbook.shlArr`, `shlFitArr` and `shrArr`, shared with the schoolbook division, instead of `low (shl a c)` and `shr` | From three alternating runs against `dc30925`, without `Nat`, 128 to 16384 limbs: `div`, `divmod`, `btostr` within ±0.8%; `bsqrt` +1% to +2% at 128 and 256, which do not reach the change (layout) |
| 2026-11-07 | `08b891d` | `land`, `lor`, `xor` of `MPN.Nat` from `main`'s `WordArray.landA`, `lorA`, `xorA` (`bitA`: `bitW` into at least one new limb, trimmed), replacing the own `bitA` and its `norm` | From three alternating runs against `feab648`, without `Nat`, 2 to 1024 limbs: `band`, `bor`, `bxor` −2% to +4%, `bcmp` −1% to −5% |
| 2026-11-07 | `4d3f349` | `Num.shl` and `Num.shr` by `main`'s `WordArray.shlBits` and `shrBits` (into new limbs at once, instead of zero limbs, a slice shift and a copy); the slice shifts by any number of bits and `zeroInto` removed | From three alternating runs against `08b891d`, without `Nat`: `bshl` −26% up to 16 limbs, −14% to −17% at 64 and 256, −5.6% at 1024; `bshr` −20% to −25% up to 64, −9% at 256, −4% at 1024; `bsqrt` −12% to −15% up to 64, −4% from 256; `btostr` ±1.7% |
| 2026-11-07 | `043fb75` | Guards on sizes by `main`'s `WordArray.fitsU` (this library's `fits`, moved) instead of `< USize.size`, a comparison with a big number; `log2` of arrays from `main`'s `WordArray.log2A` | From three alternating runs against `4d3f349`, without `Nat`, 2 to 1024 limbs: `band` −1% to −6%, `bshl` −2% to −7%, `div`, `sbdiv`, `bdiv` −5% to +0.5%, `bsqrt` −0.6% to −2.3%, `blog2` ±1.6% (+8% to +10% with `log2A` guarded by `USize.size`), `bshr` ±1.4% |
| 2026-11-07 | `985e2ce` | `Num.divMod` and `Num.div` by `main`'s shared driver `MPN.Div.Driver` (`divRemG`, `divQG`: Algorithm D below `divDC`, the normalized division by blocks over `ops64B` from there), replacing the own normalization and dispatch | From three alternating runs against `3860d1e`, without `Nat`: `div` −7% to −14% up to 8 limbs, `bdiv` −7% to −11%, `divmod`, `bmod` −3% to +5%, ±2% from 64 limbs; `bgcd` −2% to −5% at 3 to 64; with aligned builds of both, `div` −6% to −16%, `bdiv` −4% to −18%, `bmod` −4% to −11% up to 16 limbs, ±1% at 256 |
| 2026-11-07 | `622800a` | Decimal strings by `main`'s `MPN.DecWord` (`isZeroA`, `divRem1A`, `mulAddA` on any `WordArray`, trimmed), replacing `isZero`, `divRem1N` and `mulAddLimb` | From three alternating runs against `985e2ce`, without `Nat`: `str`, `btostr` −12% to −22% up to 16 limbs, −8% to −10% at 64 and 256, −4.6% at 1024 (the quotients trimmed as they shrink); `parse`, `bofstr` −0.2% to −5% |
| 2026-11-08 | `898656d` | The shared code `MPN` built with loops aligned to 32 bytes (this library keeps 64) | From three alternating runs against `b408895`, without `Nat`, at 4, 64 and 1024 limbs: `add` −0.5% to −11%, `mul` −6% at 4 limbs, `shl` −1% to −6%, the rest of `sub`, `mul1`, `toom`, `div`, `gcd`, `str` within ±3.2% |
| 2026-11-08 | `a84e2ff` | `ops64With` (so `ops64`, `ops64B`) by `main`'s shared `NatOps` on arrays, `WordArray.opsA` (`MPN.Generic.OpsArray`), on the products, sum and difference of `MPN.Num` | From three alternating runs against `898656d`, without `Nat`, 16 to 16384 limbs over `div`, `divmod`, `sqrt`, `gcd`, `str`, `parse` and their `MPN.Nat` rows: mean −0.1%; at 16 limbs `sqrt` +4.6%, `btostr` +3.7%, `gcd`, `bgcd` −3%, `str` −2.7%; the rest within ±2.5% |
| 2026-11-08 | `4e5e269` | `main`'s `WordArray.opsA` trims `shl`, `pow` and `mulMod` too | From three alternating runs against `a84e2ff`, without `Nat`, 16 to 16384 limbs over `div`, `divmod`, `sqrt`, `gcd`, `str`, `parse`: mean +0.6%, all rows within ±2.7% |
| 2026-11-08 | `478b578` | `Num.add` and `Num.sub` are `main`'s new `WordArray.addN` and `subN`, the same calls of `addW` and `subW` | From three alternating runs against `3d9f272`, 4 to 4096 limbs, mean +0.05% over 48 rows: `add`, `sub` within ±2%, `badd` −10% at 16 limbs and +4.6% at 4, `bsqrt` +3% to +4% to 16 limbs, the rest within ±3% |
| 2026-11-08 | `31f24a7` | Karatsuba's middle term by `main`'s shared `WordArray.midW` with the new fields `addDiffC` (the `__uint128_t` sum) and `copyIn` (`copySlice`), as `karatsubaMid` did, but with its bounds proved instead of a `LoopBound` test at run time; `MPN64.Arch.KaratsubaMid` removed | From three alternating runs against `478b578`, 16 to 4096 limbs, mean −0.8% over 70 rows: `kara`, `ksqr`, `toom`, `auto` −0.4% to −3% from 64 limbs; at 16 limbs, below Karatsuba, `sqr` −14% and `ksqr` −11% against `kara` +5.7% and `mul` +3.9% (placement) |
| 2026-11-08 | `4504f02` | `lshift` and `rshift` removed; the rows `shl` and `shr` time `Num.shl` and `Num.shr` (`main`'s `shlBits`, `shrBits`, which allocate their result) instead of the in-place kernels | From three alternating runs against `aa10f07`: `shl` −11% to −12% and `shr` −15% to −16% at 4 and 64 limbs, −1% to −3% from 1024; `add` −4% to 64 limbs; `div`, `sqrt` within ±1% |
| 2026-11-08 | `d558004`, `d41b576` | The unused restatements of the FFT transforms removed; `Num.low` by `main`'s `loA` and `MPN64.AddSub` (`add1`) removed | From three runs and five more of the outliers, alternating, against `4504f02`, mean +1.1% over 52 rows: `mul` +13% to +25% at 2 and 4 limbs and `gcd` +4% from 4 limbs with the same code at the same alignment, the time in the runtime's allocator (placement); `fft` −3.5% at 4; the rest within ±3% |
| 2026-11-08 | `c4bc02b` | Barrett's division by the reciprocal of the top half of the divisor (`main`'s `NatOps.divMuT`, `divQMuT`, as GMP's `mpn_mu_div_qr`): `recipG` on the top `k + 1` limbs, `k` about half the quotient, and the quotient in blocks of `k` limbs; `divMu` 8192 → 6144, `divQMu` 6144 → 4096 | From three alternating runs against `c6b2764`, without `Nat`: `div` −9% at 4096 limbs, −17% at 5120, −19% to −23% from 6144 to 65536 (9.80 → 7.95 ms at 8192); `divmod` −5.5% at 6144, −16% to −26% from 8192 (13.2 → 9.7 ms at 8192, no longer bimodal by size); `sqrt` and `str` −5% to −7% at 32768; the rest within ±2%, except, from placement (same code, moved), `add` +5% at 4 limbs and +13% at 16, `div` +6% at 1 |
| 2026-11-08 | `8763715` | Half-gcd of the top third of the limbs in the gcd loop (`main`'s `NatOps.hgcdReduceP`, as GMP's `mpn_gcd`: `hgcd` on the top `n - ⌊2n/3⌋` limbs, extended by `applySplit`); `gcdHalf` 2560 → 1536, from a sweep (1536: −4% to −5% from 2048 to 4096 limbs, 1024 within ±1%; split points 1/2, 3/5 and 3/4 at most as fast as 2/3) | From three alternating runs against `c4bc02b`, without `Nat`: `gcd` −8% at 4096 limbs, −11% at 8192, −13% at 16384, −14% at 32768 (457 → 392 ms); `blcm` the same; with the new `gcdHalf`, −5% at 2048; 2.2 times `Nat` at 8192 and 2.6 at 32768 (was 2.6 and 3.1); the rest within ±3%, except, from placement, `add` −5% to −12% at 4 to 64 limbs (back from `c4bc02b`), `sqrt` +4% at 1 |
| 2026-11-08 | `b65f73e` | Toom-8 and the Toom-8 square (`main`'s `toom88`, `toom8Sqr`, as GMP's `mpn_toom8h_mul`, `mpn_toom8_sqr`), the interpolation of degree 14 through the falling factorials; `mulToom8 = 1792`, `sqrToom8 = 2816`, from sweeps of one level against Toom-6 (products: +1% to +2% below 1792, −1.5% to −5% from there; squares oscillate, −1.5% on average from 2816; the FFT stays ahead from 8192) | From three alternating runs against `bffeab6`, without `Nat`: `auto` −1.3% at 1792 limbs, −2% to −3.4% from 2048 to 5120; `autosqr` −4.9% at 3072, +0.9% at 4096; `div` and `gcd` within ±1%; the rest within ±3%, except, from placement (same code), `sub` +8% at 4 and 16 limbs |
| 2026-11-09 | `a9173ec` | lean4-scalar-arrays v1.1.0 (was `fe6af25` on its `main`): the slice iterator without a stack frame per element, small changes to the in-place folds | From three alternating runs against `447d8fa`, without `Nat`, 4 to 1024 limbs: mean +0.3% over 55 rows, `sqr` −3.4% at 4 limbs and +3.2% at 16, `gcd` +2.9% at 64, the rest within ±2% |
| 2026-11-09 | `6d99d39` | The remainder by a word without the quotient: `main`'s `WordArray.modLoop` (`divLoop` without writing the quotient, like GMP's `mpn_mod_1`) and `mod1W`, the checked steps with the reciprocal, for an unnormalized `d` by `d 2ˢ` on the dividend unshifted and one more step modulo `d`; `modW` is `mod1A` and `divW` is `divRem1A`, instead of the general division by an array of one limb; new rows `bdiv1`, `bmod1` | From three alternating runs against `9d46499`: `bmod` −75% at 1 limb (121 → 30 ns, 0.53 of `Nat`), `bdiv` −54% (121 → 56 ns); `bmod1` −78% at 2 limbs, −59% at 16, −38% at 64, −20% at 256, −13% at 1024; `bdiv1` −48% at 2, −40% at 16, −24% at 64, −5% at 1024; `bmod`, `bdiv` from 2 limbs, which do not divide by a word, −1% to +4% |
| 2026-11-09 | `db395d1` | Algorithm D in one array (`main`'s `Schoolbook.workS`) with three ends: both results (`divRemN`), the quotient alone (`divQN`, which `divQG` takes) and the remainder alone (`modN`: shifted back in place by `WordArray.rshDown`, the quotient limbs popped off, no new array); `Num.mod` by the new remainder driver `Div.divRG`, which `MPN.Nat`'s `%` takes | From three alternating runs against `6d99d39`: `bmod` −25% at 2 limbs, −20% at 4, −11% at 8, −4% at 16, ±2% from 32; `bdiv` −15% at 2 to 4 limbs, −11% at 8 and 16, −6% at 32, −2% at 64; `div` −15% to −17% at 2 to 4, −10% at 16, −2% at 64; `divmod`, `sbdiv`, `bgcd`, `bsqrt`, `btostr` within ±3% (`sbdiv` +6% at 2 limbs, unchanged code) |
| 2026-11-09 | `535f0fb` | Decimal strings: `main`'s `isNatFast` (`String.isNat`'s automaton by `String.foldl`, a byte of state, proved equal to it) instead of `String.isNat`, whose slice iterator cost about 6 ns per character; the chunks written as words (`DecOps.chunkWord`) instead of `Nat`, big from `2⁶³`, each digit built directly (`digitW`) instead of `Nat.digitChar` | From three alternating runs against `a0aeba1`: `parse` −41% to −49% up to 64 limbs (16 limbs: 3.53 → 1.96 µs, 9.9× `mpn_set_str`), −31% at 256; `bofstr` −44% to −59%; `str`, `btostr` −24% to −29% from 2 to 16 limbs (16: 2.12 µs, 3.2× `mpn_get_str`), −18% at 64, −14% at 256 |
| 2026-11-09 | `16fa28e` | The square root's remainder from Zimmermann's recursion (`Bridge.sqrtRemZ`) instead of squaring the root again: as it is when the operand needs no shift, and renormalized as GMP's `mpn_sqrtrem` from roots of `sqrtRemRenorm = 40` limbs (`x - s² = (R + 2 s s₀ 2ᶜ + s₀²) / 4ᶜ`), where it passes the square; numbers of two words, and the recursion's base case, by `sqrtRem2` on words (`sqrt2`, the remainder by `mulh` with a borrow) | From three alternating runs against `d2218e2`: `sqrt` −72% at 2 limbs (113 ns), −23% at 4, −10% to −15% from 16 to 64, −24% at 128, −33% to −37% from 256 (3.0× `mpn_sqrtrem` at 256, 2.3× at 512 and 1024; still 9–24× from 4 to 64); `bsqrt` −84% at 1 limb (44 ns), within ±6% above |
| 2026-11-09 | `d023db1` | Decimal digits by division by `10¹⁹` in place (`main`'s `WordArray.divLoopIn`, `divLoopInR`: each quotient limb written over the limb it reads, the steps with the reciprocal checked one by one), instead of a new array per chunk | From three alternating runs against `d2218e2`: `str`, `btostr` −12% to −15% from 2 to 16 limbs, −9% to −10% at 32, −5% to −8% from 64 (2.5–4.1× `mpn_get_str` from 16 limbs) |
| 2026-11-09 | `81dfc27` | Decimal strings read by bytes (`main`'s `DecChunks.readB`, `String.getUTF8Byte` with the state in the loop's arguments, equal to the fold of `step` on ASCII characters) and checked by bytes (`isNatB`, `isNatFast`'s automaton on the UTF-8 bytes, equal to `String.isNat` on every string) | From three alternating runs against `908dbdf`: `parse` −27% to −36% up to 64 limbs (16 limbs: 1.26 µs, 6.4× `mpn_set_str`; 64: 4.3×), −19% at 256, −8% at 1024; `bofstr` −24% to −34% up to 64, −19% at 256, −8% at 1024 |
| 2026-11-09 | `2b3324c` | Subtraction's borrow by a compare (`UInt64.subb`, `b + (x < y)` in C, in `subC`): the double-width form of `subh` put a negation on the borrow's chain, four operations where addition has three; `subh` keeps its form in the multiply-subtract and the gcd's linear combinations, where the compare compiled worse | From three alternating runs against `57925c9`: `sub` −12% at 64 limbs, −19% at 256, −21% at 1024 (3.3–3.4× `mpn_sub` from 128, was 4.0–4.3, as `add`); `bsub` −12% at 64, −18% to −21% from 256 (3.5–3.6×); `div`, `gcd`, `sqrt`, `toom` within ±1.1% (`toom` −3% to −4% at 4 and 16 limbs) |
| 2026-11-10 | `2b3324c` | The same change on an Apple M2 (arm64, macOS, Lean `v4.36.0-rc2`), measured against `57925c9` | From three alternating runs: `sub` −28% at 64 limbs, −32% at 256, −34% at 1024, −38% at 4096 (5.2–5.6× `mpn_sub` from 256 limbs before, 3.3–3.8× after, as `add`); `bsub` −23% to −37%; `add`, `div`, `gcd`, `sqrt`, `toom` within the noise. On the M2, `toom` is 4.1–4.2× `mpn_mul` at 4096 limbs and `div` 3.7× `mpn_tdiv_qr` |
| 2026-11-10 | `6c9fe8e` | The FFT's subtraction and negation modulo `2ᴺ + 1` (`subStep`, `negStep`) by `subC`, whose borrow is a compare, instead of the double-width `subh` | From three alternating runs against `2b3324c`, without `Nat`: `fft` −3% at 2048 limbs, −4% at 8192 and 32768; `fftsqr` −1% to −5%; `mulmod` −1% to −5% (the most at 32768); ±1% at 512 |
| 2026-11-10 | `6c9fe8e` | The same change on an Apple M2, measured against `2b3324c` (a profile there put the subtraction loop at 19–21% of an FFT product, the transforms' linear loops at 56–58%, the pointwise products at 34–38%) | From three alternating runs, without `Nat`: `fft`, `fftsqr` −9% to −10% at 2048 limbs, −10% to −12% from 8192; `mulmod` −7% at 2048, −10% to −12% from 8192; `auto`, `autosqr` −10% to −11% from 8192 (about 3.8× `mpn_mul` at 8192, 4.0× at 16384, 3.4× at 32768, from 4.3, 4.5, 3.8), unchanged at 2048 (Toom) |
| 2026-11-10 | `264533d` | The digits of a long decimal string as an array by one `String.foldl` (`DecChunks.digitArray`), instead of a list, filtered, then converted | From three alternating runs against `9987274`: `parse` −30% at 1536 limbs, −26% at 2048, −21% at 4096, −17% at 8192 (4.2–4.6× `mpn_set_str`, from 5.1–6.2×); `bofstr` the same |
| 2026-11-10 | `2a87ccd` | `parseDC` 1536 → 1024, from `tune64` after `264533d` (the two methods within 1–3% from 704 to 1024 limbs) | From three alternating runs against `264533d`: `parse`, `bofstr` −3% at 1024 limbs, −11% to −12% at 1152, −18% at 1280, unchanged at 768 and from 1536 |
| 2026-11-10 | `307c4e7` | Two rows of `mulBasecase` per pass (`mulRow2K`) as an `inplace` program of lean4-scalar-arrays (`71b78ae`, #74), whose loop runs into the carry stores with both carries unboxed, instead of `foldlInPlaceRangeWith2AccThen` | From three alternating runs against the fold on the same library: `mul` −2% to −3% at 16 limbs, −6% at 32, −8% at 48 and 128, −7% at 1024 (690 → 644 µs); ±2% at 4 |
| 2026-11-10 | `04211a4` | The square's cross products two rows per pass (`sqrRowsLoop2`, like `mpn_sqr_basecase` with `mpn_addmul_2`): row `i`'s first product alone, then `aᵢ + β aᵢ₊₁` times the limbs above, as an in-place program by `InPlace.runForIn2Then` (in the `inplace` notation, its result pair cost 14–15%) | From three alternating runs against `83fd498`: `sqr` −12% at 16 limbs, −13% at 32 and 48, −15% at 64, −14% at 88 (3.35 → 2.88 µs), ±1% at 8; `autosqr` −12% at 128 and 256, −9% at 1024, −6% to −9% at 4096 |
| 2026-11-10 | `971e47d` | The FFT's butterflies add and subtract in one pass (`WinOps.addSubMod`, `addSubModAt`): two windows read and two written, on the new `WordFolds.fold2x2Then` as an in-place program (`InPlace.runForIn2Then`); the first inverse butterfly of a block reads `y` without a copy | From three alternating runs against `04211a4`, without `Nat`: `fft` −9% to −10% at 2048 limbs, −7% to −8% at 8192, −6% at 32768; `fftsqr` −11%, −9%, −6% to −7%; `auto` −7% to −8% at 16384 |
| 2026-11-10 | `2e9d606` | lean4-scalar-arrays `83f8921` (#79): the in-place kernels in the `inplace` notation ending with `then`, which hands the program's result to a continuation unpaired; `mulRow2K` ends with `then`, `sqrRow2K` and the butterflies' fused fold move from hand-built programs to the notation | From three alternating runs against `f192ba0`, without `Nat`: `mul` −10% at 8 limbs, −15% to −16% at 16, −10% to −11% at 32, −8% at 48, −3% at 128, ±1% at 4 and 1024; `sqr`, `autosqr`, `fft`, `fftsqr` ±1% |
| 2026-11-10 | `bf95b76` | Toom-3's values and their products in windows of one array each (`pointsW`, `interp4W`, `ToomOps.subMulWin` between windows of the same array): 3 new arrays instead of 9 per product, the same passes | From three alternating runs against `01f543d`, without `Nat`: `toom` −0.5% to −1.5% from 384 to 504 limbs, −1% at 3584; `auto` ±1% at 3072 and 4096 |
| 2026-11-11 | `85578e7` | Toom-3's first interpolation stage in one pass: the three values minus `X0 + m Xd` (`ToomOps.sub3Lin`, on `WordFolds.fold3Then`, an `inplace` program with three loop variables) instead of eight passes | From three alternating runs against `addef22`, without `Nat`: `toom` −1% to −1.7% from 384 to 504 limbs, −1.5% at 3584; `auto` −2% at 3072, ±1% at 4096; 32-bit `mul` within ±1% from 768 to 2048 limbs |
| 2026-11-11 | `3d7140e` | Toom-3's values at 1, 2 and 3 in one pass per operand (`ToomOps.evals3`, on `WordFolds.fold3Then`) instead of nine passes | From three alternating runs against `d25f94d`, without `Nat`: `toom` −1.5% to −2.5% from 384 to 504 limbs, −1.5% at 3584; `auto` −1% to −2.5% at 3072, ±1% at 4096; 32-bit `mul` within ±1% from 768 to 2048 limbs |
