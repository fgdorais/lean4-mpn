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
  `85c955d`. Tables of 2026-10-24 at `59eb90e` (history below).

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
| `add` | 0.42 | 0.53 | 0.49 | 0.55 | 0.56 | 0.57 | 0.59 | 0.62 | 0.65 | 0.69 | 0.73 | 0.79 | 0.89 | 0.98 | 0.93 | 0.99 | 1.11 |
| `sub` | 0.51 | 0.48 | 0.52 | 0.48 | 0.52 | 0.52 | 0.54 | 0.54 | 0.58 | 0.59 | 0.62 | 0.74 | 0.85 | 0.98 | 1.00 | 1.07 | 1.30 |
| `shl` | 0.33 | 0.43 | 0.44 | 0.43 | 0.45 | 0.44 | 0.46 | 0.49 | 0.53 | 0.56 | 0.62 | 0.66 | 0.75 | 0.85 | 0.69 | 0.86 | 1.06 |
| `shr` | 3.68 | 0.44 | 0.44 | 0.43 | 0.45 | 0.45 | 0.46 | 0.47 | 0.50 | 0.52 | 0.57 | 0.62 | 0.71 | 0.81 | 0.73 | 0.81 | 1.02 |
| `div1` | 3.62 | 0.47 | 0.48 | 0.51 | 0.53 | 0.58 | 0.68 | 0.76 | 0.90 | 1.00 | 1.17 | 1.29 | 1.44 | 1.53 | 1.49 | 1.57 | 1.71 |
| `div` | 1.07 | 2.38 | 2.22 | 2.20 | 2.26 | 2.31 | 2.33 | 2.42 | 2.50 | 2.71 | 3.09 | 3.09 | 3.20 | 3.33 | 3.28 | 3.47 | 4.05 |
| `sbdiv` | 0.67 | 2.02 | 1.92 | 1.90 | 2.01 | 2.07 | 2.09 | 2.24 | 2.38 | 2.62 | 3.04 | 2.97 | 3.10 | 3.34 | 3.27 | 3.47 | 4.29 |
| `sqrt` | 5.23 | 0.42 | 1.61 | 1.40 | 2.08 | 2.20 | 2.85 | 2.94 | 3.06 | 2.38 | 2.12 | 1.85 | 1.21 | 1.04 | 0.63 | 0.47 | 0.35 |
| `mul1` | 0.25 | 0.29 | 0.27 | 0.29 | 0.31 | 0.30 | 0.32 | 0.34 | 0.37 | 0.39 | 0.43 | 0.48 | 0.55 | 0.65 | 0.63 | 0.70 | 0.78 |
| `addmul1` | 0.21 | 0.20 | 0.20 | 0.20 | 0.21 | 0.23 | 0.23 | 0.21 | 0.24 | 0.25 | 0.29 | 0.31 | 0.38 | 0.44 | 0.41 | 0.45 | 0.53 |
| `mul` | 0.37 | 0.42 | 0.48 | 0.52 | 0.59 | 0.68 | 0.89 | 1.01 | 1.31 | 1.56 | 1.97 | 2.48 | 2.79 | 3.42 | 4.17 | 4.74 | 7.42 |
| `sqr` | 0.30 | 0.45 | 0.50 | 0.52 | 0.59 | 0.64 | 0.74 | 0.78 | 0.94 | 1.08 | 1.29 | 1.46 | 1.69 | 1.95 | 2.33 | 2.58 | 3.95 |
| `comba` | 0.76 | 1.34 | 1.93 | 2.36 | 3.17 | 3.82 | 4.72 | 4.98 | 5.38 | 5.36 | 5.22 | 5.11 | 4.85 | 4.89 | 5.09 | 5.21 | 6.92 |
| `kara` | 0.39 | 0.46 | 0.51 | 0.56 | 0.62 | 0.70 | 0.91 | 1.04 | 1.33 | 1.57 | 1.98 | 2.12 | 2.30 | 2.39 | 2.60 | 2.62 | 3.15 |
| `ksqr` | 0.31 | 0.47 | 0.50 | 0.55 | 0.61 | 0.66 | 0.74 | 0.79 | 0.95 | 1.08 | 1.29 | 1.49 | 1.52 | 1.70 | 1.75 | 1.85 | 2.27 |
| `mulref` | 0.21 | 0.32 | 0.49 | 0.66 | 1.15 | 1.65 | 2.65 | 3.46 | 5.01 | 6.55 | 8.16 | 9.50 | 11.06 | 12.65 | 15.46 | 17.20 | 27.02 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 61.7 ns | 63.2 ns | 65.6 ns | 66.3 ns | 68 ns | 69.5 ns | 71.8 ns | 75.4 ns | 81.1 ns | 87.8 ns | 99.2 ns | 113 ns | 140 ns | 170 ns | 224 ns | 272 ns | 482 ns |
| `sub` | 61.6 ns | 65 ns | 64 ns | 64.9 ns | 70.6 ns | 70.2 ns | 74.2 ns | 78.4 ns | 86.9 ns | 95.4 ns | 108 ns | 125 ns | 159 ns | 198 ns | 264 ns | 322 ns | 581 ns |
| `shl` | 46.8 ns | 47.6 ns | 48.8 ns | 48.5 ns | 50 ns | 50.1 ns | 51.9 ns | 56.1 ns | 59.5 ns | 64.4 ns | 74.3 ns | 82 ns | 99 ns | 121 ns | 154 ns | 201 ns | 342 ns |
| `shr` | 48.2 ns | 47.9 ns | 49.3 ns | 49.2 ns | 50.4 ns | 50.8 ns | 52.5 ns | 54.4 ns | 58.5 ns | 63.3 ns | 71.9 ns | 80 ns | 97.3 ns | 117 ns | 147 ns | 190 ns | 319 ns |
| `div1` | 54 ns | 56.8 ns | 59.9 ns | 63.5 ns | 68.1 ns | 76.6 ns | 96.9 ns | 118 ns | 158 ns | 198 ns | 281 ns | 365 ns | 530 ns | 700 ns | 1.03 µs | 1.36 µs | 2.7 µs |
| `div` | 131 ns | 300 ns | 313 ns | 336 ns | 379 ns | 409 ns | 529 ns | 687 ns | 1.04 µs | 1.54 µs | 2.88 µs | 4.66 µs | 9.46 µs | 16.1 µs | 33.5 µs | 57.9 µs | 207 µs |
| `sbdiv` | 80.8 ns | 250 ns | 269 ns | 291 ns | 334 ns | 367 ns | 479 ns | 640 ns | 990 ns | 1.49 µs | 2.83 µs | 4.49 µs | 9.22 µs | 16.1 µs | 33.4 µs | 57.9 µs | 220 µs |
| `sqrt` | 485 ns | 491 ns | 1.98 µs | 1.98 µs | 3.8 µs | 4.44 µs | 6.02 µs | 6.76 µs | 8.13 µs | 8.35 µs | 11 µs | 11.7 µs | 15.1 µs | 18 µs | 25.2 µs | 33.1 µs | 77.8 µs |
| `mul1` | 43.9 ns | 44.6 ns | 45.8 ns | 46.1 ns | 48.4 ns | 48.3 ns | 51.3 ns | 55 ns | 62.6 ns | 67.7 ns | 79.1 ns | 92.3 ns | 117 ns | 154 ns | 202 ns | 256 ns | 451 ns |
| `addmul1` | 49.9 ns | 45.7 ns | 47.5 ns | 47 ns | 48.7 ns | 50.1 ns | 54.7 ns | 57 ns | 62.9 ns | 69.9 ns | 84.3 ns | 99.4 ns | 134 ns | 169 ns | 230 ns | 283 ns | 522 ns |
| `mul` | 55.7 ns | 56.9 ns | 61.7 ns | 69.1 ns | 84.2 ns | 106 ns | 174 ns | 258 ns | 495 ns | 833 ns | 1.83 µs | 3.49 µs | 7.45 µs | 13.8 µs | 31.1 µs | 55.4 µs | 222 µs |
| `sqr` | 55.7 ns | 59.8 ns | 64.5 ns | 68.9 ns | 83.1 ns | 98.6 ns | 143 ns | 201 ns | 359 ns | 574 ns | 1.2 µs | 2.08 µs | 4.55 µs | 7.9 µs | 17.3 µs | 30.2 µs | 117 µs |
| `comba` | 114 ns | 181 ns | 247 ns | 314 ns | 454 ns | 604 ns | 925 ns | 1.27 µs | 2.03 µs | 2.86 µs | 4.84 µs | 7.15 µs | 12.9 µs | 19.9 µs | 37.8 µs | 60.9 µs | 207 µs |
| `kara` | 58.7 ns | 61.9 ns | 65.4 ns | 73.7 ns | 89.1 ns | 110 ns | 179 ns | 263 ns | 501 ns | 838 ns | 1.84 µs | 2.97 µs | 6.11 µs | 9.64 µs | 19.4 µs | 30.6 µs | 94.2 µs |
| `ksqr` | 58.5 ns | 61.9 ns | 65 ns | 72 ns | 86.7 ns | 103 ns | 146 ns | 204 ns | 363 ns | 577 ns | 1.2 µs | 2.08 µs | 4.1 µs | 6.85 µs | 13 µs | 21.7 µs | 67.2 µs |
| `mulref` | 31.8 ns | 43.8 ns | 63.6 ns | 88.5 ns | 166 ns | 261 ns | 522 ns | 882 ns | 1.89 µs | 3.5 µs | 7.58 µs | 13.3 µs | 29.3 µs | 51.5 µs | 115 µs | 203 µs | 808 µs |

### Large sizes

The tables above stop at 512 limbs, below the reach of `mulToom`. These are from
`bench kara toom kara2 toom2 512 768 1024 1536 2048 4096`, the fastest of three runs, on
2026-10-24 (`59eb90e`). The sizes are those of the larger operand.

| op | 512 | 768 | 1024 | 1536 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `kara` | 95.3 µs (3.19) | 185 µs (3.52) | 291 µs (3.84) | 562 µs (3.99) | 880 µs (4.11) | 2.66 ms (5.15) |
| `toom` | 90.4 µs (3.02) | 167 µs (3.19) | 252 µs (3.32) | 454 µs (3.22) | 692 µs (3.20) | 1.79 ms (3.48) |
| `kara2` | 113 µs (5.54) | 252 µs (7.08) | 448 µs (8.04) | 1.01 ms (9.90) | 1.79 ms (11.78) | 7.10 ms (18.83) |
| `toom2` | 111 µs (5.44) | 129 µs (3.62) | 209 µs (3.75) | 398 µs (3.90) | 630 µs (4.14) | 1.54 ms (3.95) |

The ratio to `Nat` is in parentheses. `mulKaratsuba` splits both operands at half the larger
one, which needs the smaller one to be longer than that half, so on `n` by `n / 2` limbs it is
`mulBasecase`, and its ratio grows with the size. Toom-3 by 2 and Toom-4 by 2 keep it near 4. At
512 by 256 limbs `toom2` is still `mulKaratsuba`, so still `mulBasecase`.

### Large sizes, multiplication

From `bench toom fft auto toom2 fft2 mulmod 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-24 (`59eb90e`). `mulmod` is the product modulo `β^n - 1` of
two operands of `n` limbs, against the whole product on the `Nat` side.

| op | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `toom` | 252 µs (3.32) | 692 µs (3.20) | 1.21 ms (3.31) | 1.79 ms (3.47) | 4.87 ms (4.09) | 12.4 ms (4.68) | 32.8 ms (5.09) | 81.6 ms (6.09) |
| `fft` | 561 µs (7.38) | 862 µs (4.09) | 1.28 ms (3.84) | 1.84 ms (4.09) | 3.63 ms (3.36) | 8.11 ms (3.64) | 18.2 ms (3.39) | 40.5 ms (3.00) |
| `auto` | 252 µs (3.31) | 685 µs (3.23) | 1.20 ms (3.60) | 1.84 ms (4.08) | 3.63 ms (3.36) | 8.08 ms (3.64) | 18.3 ms (3.41) | 40.9 ms (3.05) |
| `toom2` | 207 µs (3.70) | 626 µs (4.12) | 990 µs (4.02) | 1.54 ms (4.60) | 3.97 ms (5.17) | 10.8 ms (6.32) | 27.3 ms (7.00) | 70.6 ms (7.29) |
| `fft2` | 324 µs (5.80) | 699 µs (4.60) | 947 µs (3.83) | 1.28 ms (3.82) | 2.71 ms (3.53) | 6.06 ms (3.54) | 13.2 ms (3.38) | 32.0 ms (3.30) |
| `mulmod` | 249 µs (3.27) | 544 µs (2.58) | 677 µs (2.04) | 836 µs (1.85) | 1.86 ms (1.72) | 3.65 ms (1.64) | 8.14 ms (1.52) | 18.3 ms (1.37) |

### Unbalanced products

`MPN.mul`, ratio to `Nat` only, the fastest of three runs, on 2026-10-24 (`59eb90e`): `auto2`,
`auto4`, `auto8` for `n` by `n / 2`, `n / 4`, `n / 8` limbs, and `autobS` for `n` by `S` limbs.

| n | `auto` | `auto2` | `auto4` | `auto8` | `b64` | `b128` | `b256` | `b320` | `b512` | `b1024` | `b2048` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.64 | 2.81 | 2.70 | 1.91 |  |  |  |  |  |  |  |
| 512 | 3.02 | 3.09 | 2.80 | 2.74 |  |  |  |  |  |  |  |
| 1024 | 3.31 | 3.27 | 3.06 | 2.80 | 2.75 | 2.84 | 3.07 | 3.19 | 3.27 | 3.29 | 3.33 |
| 2048 | 3.18 | 3.36 | 3.24 | 3.04 |  |  |  |  |  |  |  |
| 3072 | 3.33 | 3.83 | 3.27 | 3.27 |  |  |  |  |  |  |  |
| 4096 | 3.57 | 3.84 | 4.11 | 3.25 | 2.73 | 2.84 | 3.09 | 3.16 | 3.30 | 4.03 | 3.84 |
| 6144 | 3.01 | 3.73 | 4.30 | 3.23 |  |  |  |  |  |  |  |
| 8192 | 2.82 | 3.52 | 3.71 | 3.49 |  |  |  |  |  |  |  |
| 16384 | 2.95 | 3.55 | 3.56 | 3.26 | 2.71 | 2.82 | 3.07 | 3.18 | 3.25 | 3.37 | 3.26 |
| 32768 | 2.84 | 3.38 | 3.35 | 3.07 |  |  |  |  |  |  |  |
| 65536 | 3.02 | 3.30 | 3.25 | 3.41 | 2.85 | 2.84 | 3.07 | 3.21 | 3.25 | 3.98 | 3.67 |

Before the split, the products whose smaller operand was below the Toom shapes went to the
schoolbook method: 5–6 times `Nat` at `n` by 256 or 320 limbs, 10.8 at 1536 by 384. The cells
left above 4, 4096 by 1024 (4.03–4.11) and 6144 by 1536 (4.30), are where the FFT and the Toom
methods tie.

### Large sizes, division

From `bench sbdiv div sqrt 512 1024 2048 4096 8192 16384`, the fastest of three runs, on
2026-10-24 (`59eb90e`). The sizes are those of the divisor (`div`, `sbdiv`: `2 n` by `n` limbs)
or of the operand (`sqrt`).

| op | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
|---|---:|---:|---:|---:|---:|---:|
| `sbdiv` | 220 µs (4.27) | 859 µs (5.69) | 3.40 ms (8.40) | 13.9 ms (13.24) | 55.4 ms (23.57) | 221 ms (38.43) |
| `div` | 209 µs (4.07) | 638 µs (4.23) | 1.84 ms (4.77) | 5.25 ms (5.36) | 14.3 ms (6.59) | 36.6 ms (6.38) |
| `sqrt` | 78.1 µs (0.35) | 217 µs (0.26) | 636 µs (0.26) | 1.84 ms (0.27) | 5.07 ms (0.30) | 13.1 ms (0.32) |

The ratio to `Nat` is in parentheses; for `sqrt` it is to Lean's `Nat.sqrt`, not to GMP. The
divide-and-conquer division costs `O(M(n) log n)`, and its ratio grows slowly with the size, where
GMP switches to division by Newton's iteration.

### Large sizes, squares

From `bench ksqr toomsqr fftsqr autosqr 512 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-24 (`59eb90e`).

| op | 512 | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ksqr` | 67.8 µs (2.28) | 206 µs (2.73) | 625 µs (2.92) | 1.17 ms (3.25) | 1.90 ms (3.73) | 5.72 ms (4.85) | 17.2 ms (6.94) | 51.7 ms (8.81) | 155 ms (12.81) |
| `toomsqr` | 67.4 µs (2.26) | 183 µs (2.43) | 528 µs (2.51) | 929 µs (2.82) | 1.34 ms (3.00) | 3.57 ms (3.34) | 9.42 ms (4.28) | 25.1 ms (4.72) | 63.5 ms (5.25) |
| `fftsqr` | 185 µs (6.23) | 399 µs (5.28) | 597 µs (2.84) | 869 µs (2.63) | 1.27 ms (2.85) | 2.54 ms (2.37) | 5.68 ms (2.58) | 12.9 ms (2.42) | 28.9 ms (2.37) |
| `autosqr` | 67.5 µs (2.27) | 184 µs (2.44) | 531 µs (2.53) | 869 µs (2.63) | 1.27 ms (2.84) | 2.53 ms (2.36) | 5.69 ms (2.59) | 13.0 ms (2.44) | 28.9 ms (2.37) |

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
| 2026-10-24 | `59eb90e` | all tables regenerated (five runs of the default sizes, three of each large-size section) | within ±3% of the rows measured with each change; `mul` 2.98–4.09 times `Nat` from 1024 limbs (`auto`), `sqr` 2.0–2.7, `div` 4.07–6.59 from 512 |
