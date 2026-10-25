# Benchmarks

This file tracks the performance of the library against Lean's `Nat`, which is backed by GMP. The
tables come from `lake exe bench` and are regenerated after each change that affects speed, and
the history at the end records what changed and by how much.

## Running

```sh
lake build bench                      # `lake build` alone does not rebuild it
for i in 1 2 3 4 5; do taskset -c 2 .lake/build/bin/bench; done > bench.txt
scripts/bench_md.py bench.txt         # the two tables below
```

Arguments select operations and sizes, for example `bench mul comba 4 16`, and `--no-nat` skips
`Nat`, for a profiler. Pinning the process to one core with `taskset` makes the results steadier.
Each time is the median of five trials, and the last two columns, `±MPN` and `±Nat`, are the
spread of those trials (sample standard deviation over mean, from `Batteries.RunningStats`).

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
  the result. A ratio is `MPN / Nat`, so below 1 means faster than `Nat`.
- **The library side allocates its output** with `UInt64Array.replicate`, which fills it with
  zeros, since its functions write into a given array. `addmul1` adds into a shared array, so it
  copies it first, as `Nat` allocates a new result.
- **One limb:** operands below `2⁶³` are `Nat`'s unboxed scalars, which need no allocation.
- **Results are checked in O(1)** on both sides (the size and the first limb, or the low word), so
  the time is the operation alone.
- **Machine:** AMD Ryzen 5 5600X (Zen 3), Linux 7.1, Lean `v4.36.0-rc1`, lean4-scalar-arrays
  `85c955d`, C compiled with `-falign-loops=64` (lakefile). Tables of 2026-10-24 at `d813acd`
  (history below).

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1`, on `USlice`s with `USize` indices |
| `shl`, `shr` | `MPN.lshift`, `MPN.rshift` | `n` limbs, by 13 bits | one pass, `USize` indices; `Nat`'s `<<<` and `>>>` |
| `div1` | `MPN.divRem1` | `n` limbs by a limb | one pass from the top, `UInt64.div2` (128 by 64 bits) per limb |
| `div` | `MPN.Num.divMod` | `2 n` by `n` limbs | divide and conquer (`divNorm`) from `dcThreshold = 512` limbs in the divisor, schoolbook below; `Nat` computes the quotient only |
| `sbdiv` | `MPN.divRem` | `2 n` by `n` limbs | schoolbook (Algorithm D), normalized |
| `sqrt` | `MPN.sqrtRem` | `n` limbs | Zimmermann's Karatsuba square root on `MPN.Num`; `Nat.sqrt` is Lean's Newton iteration on `Nat`, not GMP's `mpz_sqrt` |
| `mulmod` | `MPN.Num.mulModB` | `n` by `n` limbs modulo `β^n - 1` | the FFT with the pieces wrapping around (`fftMulModAt`), `2ᵏ` pieces for `k = fftK n`; `Nat` multiplies |
| `gcd` | `MPN.Num.gcd` | `n` and `n` limbs | Euclid's algorithm on pairs of words (`gcd2`) up to two limbs, Lehmer's algorithm with steps of 62 bits (`cofactors2`, `mulSubMul`), half-gcd from `gcdHalf = 1024` limbs with its own base case (`baseW`, `mulAddMul`); `Nat.gcd` is GMP's |
| `str` | `MPN.Num.toDecimal` | `n` limbs | chunks of 19 digits, divide and conquer from `strDC = 40` limbs; `Nat.repr` is Lean's, not GMP |
| `parse` | `MPN.Num.ofDecimal?` | the digits of `n` limbs | chunks of 19 digits, divide and conquer from `19 parseDC` digits (`parseDC = 512`); `String.toNat?` is Lean's, not GMP |
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass, `USize` indices |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass, `USize` indices |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1` with a continuation, `USize` indices |
| `kara` | `MPN.mulKaratsuba` | `n` by `n` limbs | Karatsuba from 64 limbs (`karatsubaThreshold`), `mulBasecase` below |
| `toom` | `MPN.mulToom` | `n` by `n` limbs | Toom-6 from 1000 limbs (`toom6Threshold`), Toom-4 from 600 (`toom4Threshold`), Toom-3 from 384 (`toom3Threshold`), `mulKaratsuba` below |
| `kara2` | `MPN.mulKaratsuba` | `n` by `n / 2` limbs | as `kara` |
| `toom2` | `MPN.mulToom` | `n` by `n / 2` limbs | Toom-3 by 2 or Toom-4 by 2 from 384 limbs in the smaller operand, `mulKaratsuba` below |
| `fft` | `MPN.FFT.fftMul` | `n` by `n` limbs | Schönhage–Strassen with `2ᵏ` pieces, `k = fftK (2 n)`, the pointwise products by `mulToom` |
| `fft2` | `MPN.FFT.fftMul` | `n` by `n / 2` limbs | as `fft` |
| `fftK` | `MPN.FFT.fftMul` | `n` by `n` limbs | as `fft` with `2ᴷ` pieces, for example `fft9`, for tuning `fftK` |
| `auto` | `MPN.mul` | `n` by `n` limbs | the FFT from `fftThreshold = 4096` limbs in the larger operand (`fftThresholdUnbal = 3072` for shapes of `3 : 2` or more) with `fftMinSmall = 320` in the smaller, `mulToom` below |
| `auto2`, `auto4`, `auto8` | `MPN.mul` | `n` by `n / 2`, `n / 4`, `n / 8` limbs | as `auto`, with the unbalanced products split into pieces |
| `autobS` | `MPN.mul` | `n` by `S` limbs, for example `autob256` | as `auto2` |
| `fftbS`, `toombS` | `MPN.FFT.fftMul`, `MPN.mulToom` | `n` by `S` limbs, for example `fftb256` | for tuning `fftMinSmall` |
| `fftsqr` | `MPN.FFT.fftSqr` | `n` limbs | one forward transform, the pointwise squares by `sqrKaratsuba`, `k = fftK (2 n)` |
| `fsqK` | `MPN.FFT.fftSqr` | `n` limbs | as `fftsqr` with `2ᴷ` pieces, for example `fsq9` |
| `toomsqr` | `MPN.sqrToom` | `n` limbs | the Toom-6 square from 1200 limbs (`toom6SqrThreshold`), the Toom-4 square from 1000 (`toom4SqrThreshold`), the Toom-3 square from 600 (`toom3SqrThreshold`), `sqrKaratsuba` below |
| `autosqr` | `MPN.sqr` | `n` limbs | the FFT from `sqrFFTThreshold = 2816` limbs, `sqrToom` below |
| `sqr` | `MPN.sqrBasecase` | `n` limbs | the cross products once by rows (`mul1`, `addMul1`), then doubled with the diagonal in one pass |
| `ksqr` | `MPN.sqrKaratsuba` | `n` limbs | Karatsuba with three squares from 96 limbs (`sqrKaratsubaThreshold`), `sqrBasecase` below |
| `comba` | `MPN.mulComba` | `n` by `n` limbs | schoolbook by columns into a three-word accumulator, `USize` indices |
| `mulref` | `Bench.refMul` | `n` by `n` limbs | schoolbook by rows, a hand-written loop with `Nat` indices and the arithmetic of `addMul1`; not part of the library, kept as a control since its code does not change |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.42 | 0.52 | 0.46 | 0.51 | 0.55 | 0.54 | 0.58 | 0.59 | 0.63 | 0.67 | 0.74 | 0.79 | 0.90 | 1.00 | 0.95 | 1.00 | 1.14 |
| `sub` | 0.52 | 0.45 | 0.53 | 0.47 | 0.50 | 0.52 | 0.54 | 0.51 | 0.58 | 0.63 | 0.64 | 0.76 | 0.86 | 0.98 | 1.00 | 1.06 | 1.31 |
| `shl` | 0.31 | 0.41 | 0.40 | 0.42 | 0.43 | 0.43 | 0.45 | 0.47 | 0.50 | 0.52 | 0.59 | 0.63 | 0.74 | 0.84 | 0.69 | 0.79 | 1.09 |
| `shr` | 3.56 | 0.43 | 0.42 | 0.44 | 0.45 | 0.45 | 0.47 | 0.49 | 0.52 | 0.54 | 0.59 | 0.64 | 0.76 | 0.87 | 0.70 | 0.86 | 1.06 |
| `div1` | 3.05 | 0.42 | 0.44 | 0.46 | 0.51 | 0.55 | 0.65 | 0.75 | 0.90 | 1.01 | 1.16 | 1.29 | 1.43 | 1.52 | 1.52 | 1.59 | 1.69 |
| `div` | 1.09 | 2.41 | 2.28 | 2.27 | 2.29 | 2.40 | 2.43 | 2.46 | 2.50 | 2.72 | 3.12 | 3.01 | 3.20 | 3.34 | 3.30 | 3.47 | 4.04 |
| `sbdiv` | 0.70 | 2.03 | 1.93 | 1.92 | 2.03 | 2.12 | 2.22 | 2.28 | 2.40 | 2.65 | 3.07 | 2.98 | 3.19 | 3.33 | 3.28 | 3.45 | 4.26 |
| `sqrt` | 5.20 | 0.41 | 1.57 | 1.39 | 1.97 | 2.13 | 2.73 | 2.84 | 2.97 | 2.28 | 2.05 | 1.85 | 1.19 | 1.01 | 0.63 | 0.45 | 0.33 |
| `gcd` | 0.87 | 1.49 | 3.45 | 2.89 | 2.64 | 3.19 | 3.05 | 2.80 | 2.90 | 2.88 | 2.92 | 2.94 | 2.98 | 3.02 | 3.09 | 3.04 | 2.45 |
| `str` | 3.11 | 0.05 | 0.04 | 0.04 | 0.05 | 0.04 | 0.04 | 0.04 | 0.04 | 0.04 | 0.05 | 0.05 | 0.04 | 0.04 | 0.02 | 0.02 | 0.02 |
| `parse` | 1.08 | 0.14 | 0.10 | 0.09 | 0.07 | 0.07 | 0.06 | 0.06 | 0.06 | 0.06 | 0.05 | 0.05 | 0.05 | 0.05 | 0.04 | 0.04 | 0.07 |
| `mul1` | 0.25 | 0.28 | 0.26 | 0.29 | 0.30 | 0.32 | 0.33 | 0.36 | 0.38 | 0.40 | 0.44 | 0.49 | 0.57 | 0.66 | 0.56 | 0.64 | 0.78 |
| `addmul1` | 0.19 | 0.19 | 0.18 | 0.20 | 0.20 | 0.23 | 0.22 | 0.22 | 0.24 | 0.25 | 0.29 | 0.31 | 0.38 | 0.44 | 0.42 | 0.47 | 0.51 |
| `mul` | 0.38 | 0.41 | 0.48 | 0.51 | 0.64 | 0.71 | 0.88 | 0.99 | 1.29 | 1.54 | 1.95 | 2.31 | 2.78 | 3.37 | 4.16 | 4.71 | 7.41 |
| `sqr` | 0.30 | 0.45 | 0.50 | 0.54 | 0.58 | 0.64 | 0.73 | 0.74 | 0.86 | 0.94 | 1.10 | 1.27 | 1.49 | 1.75 | 2.10 | 2.37 | 3.72 |
| `comba` | 0.80 | 1.33 | 1.91 | 2.40 | 3.19 | 3.92 | 4.65 | 4.92 | 5.26 | 5.25 | 5.07 | 5.02 | 4.70 | 4.79 | 5.00 | 5.14 | 6.85 |
| `kara` | 0.41 | 0.44 | 0.52 | 0.55 | 0.60 | 0.69 | 0.91 | 1.01 | 1.31 | 1.56 | 1.97 | 2.13 | 2.30 | 2.41 | 2.61 | 2.59 | 3.15 |
| `ksqr` | 0.33 | 0.48 | 0.55 | 0.56 | 0.61 | 0.68 | 0.74 | 0.76 | 0.86 | 0.96 | 1.13 | 1.27 | 1.36 | 1.50 | 1.57 | 1.64 | 2.01 |
| `mulref` | 0.23 | 0.35 | 0.53 | 0.73 | 1.25 | 1.78 | 2.84 | 3.68 | 5.32 | 6.92 | 8.67 | 10.00 | 11.71 | 13.57 | 16.49 | 18.64 | 29.04 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 59.4 ns | 61.2 ns | 62.5 ns | 62.3 ns | 66.1 ns | 65.9 ns | 70.4 ns | 73.3 ns | 79.3 ns | 86.4 ns | 99.5 ns | 113 ns | 142 ns | 174 ns | 230 ns | 276 ns | 484 ns |
| `sub` | 62.6 ns | 64.1 ns | 66.2 ns | 65.6 ns | 70.6 ns | 72.4 ns | 76.8 ns | 80 ns | 86.8 ns | 96.3 ns | 111 ns | 127 ns | 161 ns | 198 ns | 266 ns | 325 ns | 584 ns |
| `shl` | 44.1 ns | 45.6 ns | 45.4 ns | 47.6 ns | 48.3 ns | 48.3 ns | 50.8 ns | 53.8 ns | 57.1 ns | 61.2 ns | 71.3 ns | 79.3 ns | 99.7 ns | 121 ns | 153 ns | 201 ns | 341 ns |
| `shr` | 47 ns | 48 ns | 47.5 ns | 49.8 ns | 50.8 ns | 51.4 ns | 54 ns | 56.9 ns | 61.5 ns | 65 ns | 73.8 ns | 82.8 ns | 104 ns | 127 ns | 157 ns | 203 ns | 348 ns |
| `div1` | 46.4 ns | 50.5 ns | 53.9 ns | 58 ns | 64.8 ns | 73.3 ns | 93.4 ns | 116 ns | 156 ns | 197 ns | 280 ns | 364 ns | 530 ns | 695 ns | 1.02 µs | 1.35 µs | 2.67 µs |
| `div` | 132 ns | 304 ns | 322 ns | 354 ns | 387 ns | 424 ns | 539 ns | 701 ns | 1.05 µs | 1.56 µs | 2.91 µs | 4.58 µs | 9.51 µs | 16.2 µs | 33.7 µs | 58 µs | 208 µs |
| `sbdiv` | 84.4 ns | 256 ns | 272 ns | 299 ns | 343 ns | 376 ns | 491 ns | 652 ns | 1.01 µs | 1.52 µs | 2.86 µs | 4.53 µs | 9.48 µs | 16.1 µs | 33.5 µs | 57.9 µs | 220 µs |
| `sqrt` | 484 ns | 483 ns | 1.98 µs | 1.99 µs | 3.69 µs | 4.38 µs | 5.87 µs | 6.54 µs | 8.03 µs | 8.1 µs | 10.8 µs | 11.7 µs | 14.9 µs | 17.5 µs | 25.3 µs | 31.9 µs | 74.7 µs |
| `gcd` | 96.5 ns | 269 ns | 1.35 µs | 1.6 µs | 2.43 µs | 4.08 µs | 5.95 µs | 7.47 µs | 12.4 µs | 17.4 µs | 28.9 µs | 41.7 µs | 72.8 µs | 111 µs | 206 µs | 322 µs | 979 µs |
| `str` | 111 ns | 399 ns | 543 ns | 723 ns | 1.35 µs | 1.74 µs | 2.35 µs | 3.59 µs | 6.02 µs | 9.34 µs | 17.1 µs | 25.3 µs | 37.5 µs | 58 µs | 85.9 µs | 142 µs | 375 µs |
| `parse` | 265 ns | 569 ns | 780 ns | 988 ns | 1.42 µs | 1.82 µs | 2.72 µs | 3.61 µs | 5.42 µs | 7.29 µs | 11.1 µs | 15.2 µs | 24.1 µs | 33.2 µs | 55.4 µs | 81.4 µs | 399 µs |
| `mul1` | 43.9 ns | 43.8 ns | 46 ns | 46 ns | 47.3 ns | 50 ns | 51.9 ns | 56.9 ns | 61.9 ns | 68.4 ns | 79.2 ns | 92.8 ns | 120 ns | 156 ns | 201 ns | 255 ns | 451 ns |
| `addmul1` | 44 ns | 44.5 ns | 45.3 ns | 46.6 ns | 48.6 ns | 49.7 ns | 53.7 ns | 56.5 ns | 63 ns | 69.5 ns | 85 ns | 101 ns | 136 ns | 173 ns | 231 ns | 290 ns | 522 ns |
| `mul` | 55.4 ns | 55.3 ns | 62.4 ns | 67.5 ns | 92.6 ns | 113 ns | 176 ns | 258 ns | 498 ns | 837 ns | 1.84 µs | 3.3 µs | 7.49 µs | 13.8 µs | 31.2 µs | 55.6 µs | 223 µs |
| `sqr` | 56.8 ns | 62.6 ns | 66.6 ns | 73.4 ns | 85.2 ns | 103 ns | 145 ns | 192 ns | 329 ns | 514 ns | 1.05 µs | 1.81 µs | 4.02 µs | 7.08 µs | 15.8 µs | 28 µs | 111 µs |
| `comba` | 115 ns | 181 ns | 246 ns | 319 ns | 460 ns | 623 ns | 920 ns | 1.28 µs | 2.03 µs | 2.84 µs | 4.78 µs | 7.13 µs | 12.7 µs | 19.6 µs | 37.5 µs | 60.6 µs | 207 µs |
| `kara` | 59.1 ns | 60.3 ns | 66.7 ns | 72.6 ns | 88.2 ns | 111 ns | 180 ns | 263 ns | 504 ns | 843 ns | 1.85 µs | 3.02 µs | 6.18 µs | 9.8 µs | 19.6 µs | 30.8 µs | 94.9 µs |
| `ksqr` | 62.1 ns | 67.4 ns | 72.6 ns | 76.9 ns | 89.7 ns | 109 ns | 148 ns | 197 ns | 333 ns | 520 ns | 1.06 µs | 1.81 µs | 3.69 µs | 6.09 µs | 11.8 µs | 19.4 µs | 60 µs |
| `mulref` | 33 ns | 47.9 ns | 68.9 ns | 96.6 ns | 180 ns | 283 ns | 566 ns | 956 ns | 2.05 µs | 3.75 µs | 8.16 µs | 14.3 µs | 31.5 µs | 55.5 µs | 124 µs | 220 µs | 874 µs |

### Large sizes

The tables above stop at 512 limbs, below the reach of `mulToom`. These are from
`bench kara toom kara2 toom2 512 768 1024 1536 2048 4096`, the fastest of three runs, on
2026-10-24 (`d813acd`, loops aligned). The sizes are those of the larger operand.

| op | 512 | 768 | 1024 | 1536 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `kara` | 95.9 µs (3.19) | 187 µs (3.54) | 295 µs (3.86) | 567 µs (3.99) | 887 µs (4.13) | 2.68 ms (5.14) |
| `toom` | 91.3 µs (3.03) | 167 µs (3.17) | 254 µs (3.33) | 452 µs (3.18) | 692 µs (3.17) | 1.80 ms (3.48) |
| `kara2` | 113 µs (5.49) | 253 µs (7.05) | 449 µs (8.02) | 1.01 ms (9.81) | 1.79 ms (11.70) | 7.16 ms (18.84) |
| `toom2` | 112 µs (5.46) | 130 µs (3.62) | 210 µs (3.72) | 398 µs (3.86) | 632 µs (4.13) | 1.56 ms (3.98) |

The ratio to `Nat` is in parentheses. `mulKaratsuba` splits both operands at half the larger
one, which needs the smaller one to be longer than that half, so on `n` by `n / 2` limbs it is
`mulBasecase`, and its ratio grows with the size. Toom-3 by 2 and Toom-4 by 2 keep it near 4. At
512 by 256 limbs `toom2` is still `mulKaratsuba`, so still `mulBasecase`.

### Large sizes, multiplication

From `bench toom fft auto toom2 fft2 mulmod 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-24 (`d813acd`, loops aligned). `mulmod` is the product
modulo `β^n - 1` of two operands of `n` limbs, against the whole product on the `Nat` side.

| op | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `toom` | 253 µs (3.32) | 693 µs (3.19) | 1.21 ms (3.31) | 1.80 ms (3.48) | 4.88 ms (4.10) | 12.4 ms (4.66) | 32.9 ms (5.09) | 81.7 ms (6.10) |
| `fft` | 550 µs (7.24) | 864 µs (4.06) | 1.28 ms (3.81) | 1.83 ms (4.05) | 3.63 ms (3.33) | 8.08 ms (3.62) | 18.3 ms (3.40) | 40.6 ms (3.03) |
| `auto` | 251 µs (3.29) | 687 µs (3.24) | 1.20 ms (3.58) | 1.83 ms (4.04) | 3.62 ms (3.35) | 8.09 ms (3.61) | 18.2 ms (3.40) | 40.6 ms (3.03) |
| `toom2` | 207 µs (3.70) | 626 µs (4.12) | 988 µs (3.98) | 1.55 ms (4.61) | 3.97 ms (5.16) | 10.8 ms (6.32) | 27.3 ms (6.98) | 70.8 ms (7.29) |
| `fft2` | 318 µs (5.69) | 690 µs (4.54) | 955 µs (3.85) | 1.28 ms (3.80) | 2.70 ms (3.51) | 6.05 ms (3.54) | 13.2 ms (3.38) | 31.8 ms (3.27) |
| `mulmod` | 242 µs (3.18) | 533 µs (2.51) | 666 µs (1.99) | 826 µs (1.83) | 1.84 ms (1.70) | 3.64 ms (1.63) | 8.16 ms (1.52) | 18.4 ms (1.37) |

### Unbalanced products

`MPN.mul`, ratio to `Nat` only, the fastest of three runs, on 2026-10-24 (`d813acd`, loops
aligned): `auto2`, `auto4`, `auto8` for `n` by `n / 2`, `n / 4`, `n / 8` limbs, and `autobS` for
`n` by `S` limbs.

| n | `auto` | `auto2` | `auto4` | `auto8` | `b64` | `b128` | `b256` | `b320` | `b512` | `b1024` | `b2048` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.64 | 2.80 | 2.68 | 1.89 |  |  |  |  |  |  |  |
| 512 | 3.05 | 3.08 | 2.82 | 2.72 |  |  |  |  |  |  |  |
| 1024 | 3.33 | 3.27 | 3.06 | 2.81 | 2.74 | 2.85 | 3.10 | 3.17 | 3.29 | 3.29 | 3.35 |
| 2048 | 3.19 | 3.32 | 3.26 | 3.04 |  |  |  |  |  |  |  |
| 3072 | 3.32 | 3.80 | 3.26 | 3.26 |  |  |  |  |  |  |  |
| 4096 | 3.52 | 3.81 | 4.03 | 3.25 | 2.70 | 2.85 | 3.10 | 3.15 | 3.24 | 4.02 | 3.80 |
| 6144 | 2.98 | 3.68 | 4.27 | 3.21 |  |  |  |  |  |  |  |
| 8192 | 2.81 | 3.49 | 3.68 | 3.46 |  |  |  |  |  |  |  |
| 16384 | 2.94 | 3.54 | 3.53 | 3.23 | 2.71 | 2.83 | 3.08 | 3.18 | 3.26 | 3.37 | 3.24 |
| 32768 | 2.83 | 3.37 | 3.35 | 3.05 |  |  |  |  |  |  |  |
| 65536 | 3.04 | 3.26 | 3.23 | 3.40 | 2.83 | 2.85 | 3.08 | 3.16 | 3.26 | 4.00 | 3.71 |

Before the split, the products whose smaller operand was below the Toom shapes went to the
schoolbook method: 5–6 times `Nat` at `n` by 256 or 320 limbs, 10.8 at 1536 by 384. The cells
left above 4, 4096 by 1024 (4.03–4.11) and 6144 by 1536 (4.30), are where the FFT and the Toom
methods tie.

### Large sizes, division

From `bench sbdiv div sqrt 512 1024 2048 4096 8192 16384`, the fastest of three runs, on
2026-10-24 (`d813acd`, loops aligned). The sizes are those of the divisor (`div`, `sbdiv`:
`2 n` by `n` limbs) or of the operand (`sqrt`).

| op | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
|---|---:|---:|---:|---:|---:|---:|
| `sbdiv` | 220 µs (4.28) | 859 µs (5.69) | 3.40 ms (8.37) | 13.9 ms (13.24) | 55.3 ms (23.43) | 221 ms (38.50) |
| `div` | 209 µs (4.07) | 638 µs (4.23) | 1.84 ms (4.74) | 5.24 ms (5.33) | 14.3 ms (6.59) | 36.5 ms (6.36) |
| `sqrt` | 75.0 µs (0.33) | 205 µs (0.24) | 607 µs (0.24) | 1.77 ms (0.26) | 4.95 ms (0.29) | 12.7 ms (0.31) |

The ratio to `Nat` is in parentheses; for `sqrt` it is to Lean's `Nat.sqrt`, not to GMP. The
divide-and-conquer division costs `O(M(n) log n)`, and its ratio grows slowly with the size, where
GMP switches to division by Newton's iteration.

### Large sizes, gcd and decimal strings

From `bench gcd str parse 512 1024 2048 4096 8192`, the fastest of three runs, on 2026-10-24.
`str` and `parse` compare with Lean's `Nat.repr` and `String.toNat?`, which are written in Lean,
not with GMP's `mpz_get_str` and `mpz_set_str`; `gcd` compares with `Nat.gcd`, GMP's `mpz_gcd`.

| op | 512 | 1024 | 2048 | 4096 | 8192 |
|---|---:|---:|---:|---:|---:|
| `gcd` | 990 µs (2.45) | 3.33 ms (2.55) | 10.3 ms (2.86) | 29.9 ms (3.14) | 80.3 ms (3.28) |
| `str` | 376 µs (0.02) | 1.06 ms (0.01) | 2.98 ms (0.01) | 8.35 ms (0.01) | 22.5 ms (0.01) |
| `parse` | 401 µs (0.07) | 925 µs (0.06) | 2.24 ms (0.04) | 5.51 ms (0.03) | 13.5 ms (0.02) |

`gcd` is Lehmer's algorithm with steps of about 62 bits, like GMP's: two runs of Euclid's steps on
the leading words, the second on the leading 128 bits after the first (`cofactors2`), applied by
`mulSubMul` in one pass for each number; and half-gcd from `gcdHalf = 1024` limbs, whose base
case up to `hgcdBase = 128` limbs is the same steps with the matrix updated in one pass per entry
(`mulAddMul`); above the base case it runs on the generic layer. At 16384 limbs `gcd` takes
219 ms, 3.61 times `Nat`. `gcdh<T>` sweeps `gcdHalf`.

### Large sizes, squares

From `bench ksqr toomsqr fftsqr autosqr 512 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-24 (`d813acd`, loops aligned).

| op | 512 | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ksqr` | 60.4 µs (2.03) | 185 µs (2.45) | 561 µs (2.62) | 1.06 ms (2.94) | 1.70 ms (3.33) | 5.12 ms (4.30) | 15.5 ms (6.25) | 46.5 ms (7.88) | 140 ms (11.48) |
| `toomsqr` | 60.7 µs (2.03) | 169 µs (2.23) | 486 µs (2.31) | 849 µs (2.56) | 1.23 ms (2.75) | 3.33 ms (3.11) | 8.70 ms (3.95) | 23.0 ms (4.32) | 59.3 ms (4.86) |
| `fftsqr` | 177 µs (5.94) | 383 µs (5.05) | 566 µs (2.68) | 815 µs (2.45) | 1.21 ms (2.71) | 2.36 ms (2.21) | 5.29 ms (2.40) | 12.0 ms (2.25) | 26.7 ms (2.19) |
| `autosqr` | 59.8 µs (2.00) | 167 µs (2.20) | 482 µs (2.28) | 812 µs (2.45) | 1.21 ms (2.69) | 2.35 ms (2.18) | 5.28 ms (2.40) | 11.9 ms (2.23) | 26.6 ms (2.18) |

**Tuning.**

- `fftK` comes from a sweep of `fft4` to `fft11` at 1024 to 65536 limbs per operand: the best
  number of pieces `K` has `K² / T` between 8 and 32 for `T` limbs in all, and the least `k` with
  `4ᵏ ≥ 10 T` is within 6% of the best everywhere (at 4096 limbs per operand, `k = 9` where 8 is
  best). For squares (`fsq6` to `fsq11`) it is the best from 8192 limbs and within 4% below.
- Toom-4 and Toom-4 by 3 beat Toom-3 by 5–9% from 1024 limbs, more above (the FFT takes over
  there); `toom4Threshold` between 384 and 1000 limbs makes no difference beyond ±2%, and is 600.
- Toom-6 beats Toom-4 by 3–8% from 1536 limbs, with `toom6Threshold` from 1000 to 2200 limbs
  within ±1% of each other; it is 1000.
- With Toom-6, the FFT ties `toom` at 4096 limbs per operand, balanced, but passes `toom2` at 3072
  by 1536, hence `fftThreshold = 4096` limbs in the larger operand and `fftThresholdUnbal = 3072`
  when the operands differ by `3 : 2` or more (it was 3072 for both with Toom-4, and 5120 limbs
  in all before).
- With `S` limbs in the smaller operand, below 384, `mulToom` is the schoolbook method, about
  3.5 µs per limb of `S` at 4096 limbs in the other and 14 µs at 16384, while the FFT costs what
  its total does (0.9 ms, 3.6 ms). They cross at `S` ≈ 260 for 4096 and 16384 limbs and 326 for
  65536 (`fftbS`, `toombS`), hence `fftMinSmall = 320`.
- Unbalanced products are split when the larger operand has at least twice the limbs of the
  smaller, which has at least `chunkMinSmall = 96`: pieces of the size of the smaller, each by
  `mulBal`. With 1536 limbs or more in the smaller operand, one FFT on the whole product beats
  one per piece by 10–20% (`autobS` against `fftbS`), and they tie at 1024: hence
  `chunkMaxSmall = 1024` when the larger operand is in the range of the FFT.
- The Toom-3 square passes `ksqr` at 600 to 768 limbs (2–3% slower at 512, 6–14% faster from
  1024), hence `toom3SqrThreshold = 600`; the Toom-4 square adds 6–10% at 1024, 1536, 3072 and
  4096 limbs with a threshold of 700 or 1000, and is 1000. `fftsqr` passes `toomsqr` at 2816
  limbs, hence `sqrFFTThreshold = 2816` (it was 2048, against `ksqr`).
- The Toom-6 square gains 0–5% on the Toom-4 square (3% at 2048 limbs, 5% at 4096), with
  `toom6SqrThreshold` from 1200 to 2400 within noise; it is 1200, and `sqrFFTThreshold` stays.
- A product whose larger operand has twice the limbs of the smaller is always unbalanced for the
  FFT, which wins those from `fftThresholdUnbal = 3072` limbs: the pieces of `mulChunked` beyond
  `chunkMaxSmall` stop there (4000 by 1700 limbs 1.41 → 1.15 ms).

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
