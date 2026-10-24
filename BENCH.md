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
  `85c955d`. 2026-10-22, with squaring (history below).

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1`, on `USlice`s with `USize` indices |
| `shl`, `shr` | `MPN.lshift`, `MPN.rshift` | `n` limbs, by 13 bits | one pass, `USize` indices; `Nat`'s `<<<` and `>>>` |
| `div1` | `MPN.divRem1` | `n` limbs by a limb | one pass from the top, `UInt64.div2` (128 by 64 bits) per limb |
| `div` | `MPN.Num.divMod` | `2 n` by `n` limbs | divide and conquer (`divNorm`) from `dcThreshold = 512` limbs in the divisor, schoolbook below; `Nat` computes the quotient only |
| `sbdiv` | `MPN.divRem` | `2 n` by `n` limbs | schoolbook (Algorithm D), normalized |
| `sqrt` | `MPN.sqrtRem` | `n` limbs | Zimmermann's Karatsuba square root on `MPN.Num`; `Nat.sqrt` is Lean's Newton iteration on `Nat`, not GMP's `mpz_sqrt` |
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
| `add` | 0.45 | 0.57 | 0.50 | 0.58 | 0.61 | 0.62 | 0.64 | 0.66 | 0.70 | 0.73 | 0.78 | 0.83 | 0.93 | 1.01 | 0.95 | 1.00 | 1.13 |
| `sub` | 0.56 | 0.48 | 0.55 | 0.51 | 0.51 | 0.53 | 0.55 | 0.53 | 0.56 | 0.55 | 0.60 | 0.72 | 0.85 | 0.96 | 1.06 | 1.03 | 1.28 |
| `shl` | 0.30 | 0.41 | 0.41 | 0.41 | 0.44 | 0.43 | 0.46 | 0.48 | 0.50 | 0.54 | 0.59 | 0.64 | 0.77 | 0.90 | 0.71 | 0.85 | 1.05 |
| `shr` | 3.46 | 0.41 | 0.42 | 0.43 | 0.44 | 0.44 | 0.46 | 0.45 | 0.49 | 0.50 | 0.55 | 0.61 | 0.70 | 0.80 | 0.63 | 0.83 | 0.92 |
| `div1` | 3.02 | 0.40 | 0.42 | 0.46 | 0.50 | 0.55 | 0.66 | 0.74 | 0.89 | 0.98 | 1.14 | 1.26 | 1.40 | 1.49 | 1.46 | 1.53 | 1.64 |
| `div` | 1.04 | 2.43 | 2.29 | 2.26 | 2.32 | 2.42 | 2.48 | 2.47 | 2.52 | 2.71 | 3.14 | 3.01 | 3.19 | 3.33 | 3.26 | 3.49 | 4.04 |
| `sbdiv` | 0.67 | 1.95 | 1.90 | 1.90 | 1.97 | 2.10 | 2.23 | 2.29 | 2.40 | 2.64 | 3.08 | 2.99 | 3.15 | 3.33 | 3.28 | 3.47 | 4.28 |
| `sqrt` | 5.05 | 0.41 | 1.60 | 1.39 | 1.99 | 2.15 | 2.78 | 2.97 | 3.07 | 2.35 | 2.10 | 1.86 | 1.21 | 1.02 | 0.62 | 0.46 | 0.33 |
| `mul1` | 0.26 | 0.30 | 0.27 | 0.30 | 0.32 | 0.32 | 0.34 | 0.36 | 0.39 | 0.41 | 0.45 | 0.49 | 0.56 | 0.66 | 0.62 | 0.70 | 0.79 |
| `addmul1` | 0.19 | 0.19 | 0.19 | 0.21 | 0.20 | 0.23 | 0.22 | 0.22 | 0.25 | 0.26 | 0.30 | 0.33 | 0.40 | 0.44 | 0.43 | 0.44 | 0.54 |
| `mul` | 0.41 | 0.44 | 0.50 | 0.54 | 0.60 | 0.70 | 0.90 | 1.04 | 1.32 | 1.57 | 1.97 | 2.49 | 2.81 | 3.44 | 4.24 | 4.80 | 7.47 |
| `sqr` | 0.31 | 0.44 | 0.52 | 0.53 | 0.59 | 0.64 | 0.71 | 0.77 | 0.88 | 0.98 | 1.19 | 1.28 | 1.54 | 1.77 | 2.14 | 2.39 | 3.75 |
| `comba` | 0.75 | 1.25 | 1.86 | 2.25 | 3.10 | 3.84 | 4.66 | 5.04 | 5.36 | 5.32 | 5.13 | 5.10 | 4.77 | 4.82 | 4.99 | 5.19 | 6.89 |
| `kara` | 0.41 | 0.44 | 0.51 | 0.54 | 0.60 | 0.70 | 0.91 | 1.04 | 1.33 | 1.57 | 1.97 | 2.12 | 2.33 | 2.42 | 2.60 | 2.60 | 3.16 |
| `ksqr` | 0.34 | 0.49 | 0.57 | 0.58 | 0.63 | 0.69 | 0.75 | 0.79 | 0.89 | 0.98 | 1.17 | 1.29 | 1.36 | 1.51 | 1.57 | 1.62 | 1.99 |
| `mulref` | 0.23 | 0.33 | 0.51 | 0.68 | 1.18 | 1.68 | 2.69 | 3.53 | 5.05 | 6.59 | 8.20 | 9.43 | 11.01 | 12.85 | 15.44 | 17.44 | 27.03 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 63.6 ns | 67.9 ns | 69 ns | 69.8 ns | 73.5 ns | 73.9 ns | 77.1 ns | 80 ns | 87.2 ns | 93.2 ns | 105 ns | 118 ns | 146 ns | 174 ns | 228 ns | 274 ns | 485 ns |
| `sub` | 66.9 ns | 67 ns | 67.6 ns | 69.4 ns | 72.4 ns | 73.1 ns | 75.9 ns | 80.8 ns | 87.8 ns | 95.2 ns | 110 ns | 126 ns | 159 ns | 194 ns | 261 ns | 321 ns | 581 ns |
| `shl` | 41.8 ns | 44.6 ns | 45.3 ns | 45.7 ns | 47.9 ns | 47.9 ns | 50.6 ns | 53.4 ns | 57 ns | 61.9 ns | 70.7 ns | 80.3 ns | 101 ns | 127 ns | 158 ns | 201 ns | 345 ns |
| `shr` | 46 ns | 46.4 ns | 48.4 ns | 49.1 ns | 50.5 ns | 50.3 ns | 52.5 ns | 53.9 ns | 58 ns | 60.9 ns | 69.5 ns | 79 ns | 96 ns | 117 ns | 144 ns | 188 ns | 313 ns |
| `div1` | 42.6 ns | 48.4 ns | 51.1 ns | 55.6 ns | 62.3 ns | 70.9 ns | 91.9 ns | 112 ns | 152 ns | 192 ns | 271 ns | 354 ns | 514 ns | 676 ns | 994 ns | 1.31 µs | 2.59 µs |
| `div` | 127 ns | 309 ns | 325 ns | 346 ns | 392 ns | 428 ns | 548 ns | 698 ns | 1.05 µs | 1.55 µs | 2.92 µs | 4.58 µs | 9.5 µs | 16.2 µs | 33.6 µs | 58.2 µs | 208 µs |
| `sbdiv` | 82.3 ns | 251 ns | 270 ns | 290 ns | 333 ns | 376 ns | 494 ns | 649 ns | 1 µs | 1.51 µs | 2.86 µs | 4.52 µs | 9.42 µs | 16.2 µs | 33.5 µs | 58 µs | 220 µs |
| `sqrt` | 492 ns | 492 ns | 2.03 µs | 2.03 µs | 3.83 µs | 4.53 µs | 6.09 µs | 6.87 µs | 8.3 µs | 8.33 µs | 11 µs | 11.8 µs | 15.1 µs | 17.7 µs | 24.7 µs | 32.1 µs | 74.3 µs |
| `mul1` | 45.1 ns | 45.3 ns | 46.4 ns | 46.2 ns | 48.9 ns | 49 ns | 53.3 ns | 56.4 ns | 62.9 ns | 68.5 ns | 79.7 ns | 91.8 ns | 117 ns | 153 ns | 199 ns | 253 ns | 450 ns |
| `addmul1` | 44.4 ns | 44.2 ns | 45.8 ns | 47.5 ns | 47.5 ns | 48.8 ns | 51.6 ns | 55.8 ns | 62.5 ns | 69.2 ns | 83.6 ns | 99.7 ns | 134 ns | 167 ns | 226 ns | 281 ns | 522 ns |
| `mul` | 58 ns | 60 ns | 63.4 ns | 71.9 ns | 85.5 ns | 109 ns | 175 ns | 259 ns | 498 ns | 841 ns | 1.83 µs | 3.48 µs | 7.48 µs | 13.9 µs | 31.7 µs | 56.2 µs | 224 µs |
| `sqr` | 55.9 ns | 59.9 ns | 66.4 ns | 69.8 ns | 83.1 ns | 99.6 ns | 138 ns | 193 ns | 328 ns | 524 ns | 1.1 µs | 1.81 µs | 4.1 µs | 7.11 µs | 15.9 µs | 28 µs | 111 µs |
| `comba` | 106 ns | 169 ns | 236 ns | 295 ns | 440 ns | 595 ns | 909 ns | 1.26 µs | 2.01 µs | 2.84 µs | 4.77 µs | 7.14 µs | 12.7 µs | 19.6 µs | 37.3 µs | 60.7 µs | 206 µs |
| `kara` | 58.1 ns | 59.7 ns | 65.4 ns | 70.7 ns | 85.8 ns | 109 ns | 178 ns | 262 ns | 501 ns | 839 ns | 1.83 µs | 2.99 µs | 6.22 µs | 9.75 µs | 19.4 µs | 30.7 µs | 94.7 µs |
| `ksqr` | 63.2 ns | 66.7 ns | 71.9 ns | 77.1 ns | 89.5 ns | 108 ns | 147 ns | 200 ns | 333 ns | 523 ns | 1.08 µs | 1.8 µs | 3.63 µs | 6.05 µs | 11.7 µs | 19 µs | 59.2 µs |
| `mulref` | 32.4 ns | 44.6 ns | 64.7 ns | 89.3 ns | 168 ns | 262 ns | 524 ns | 885 ns | 1.9 µs | 3.52 µs | 7.62 µs | 13.3 µs | 29.4 µs | 51.8 µs | 115 µs | 204 µs | 811 µs |

### Large sizes

The tables above stop at 512 limbs, below the reach of `mulToom`. These are from
`bench kara toom kara2 toom2 512 768 1024 1536 2048 4096`, the fastest of three runs, on
2026-10-23. The sizes are those of the larger operand.

| op | 512 | 768 | 1024 | 1536 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `kara` | 94.8 µs (3.16) | 186 µs (3.54) | 292 µs (3.84) | 564 µs (4.00) | 882 µs (4.12) | 2.66 ms (5.14) |
| `toom` | 90.4 µs (3.01) | 172 µs (3.28) | 269 µs (3.54) | 482 µs (3.42) | 775 µs (3.59) | 2.10 ms (4.09) |
| `kara2` | 113 µs (5.51) | 253 µs (7.07) | 449 µs (8.03) | 1.01 ms (9.90) | 1.79 ms (11.78) | 7.10 ms (18.78) |
| `toom2` | 111 µs (5.41) | 131 µs (3.66) | 210 µs (3.76) | 398 µs (3.90) | 660 µs (4.34) | 1.56 ms (4.00) |

The ratio to `Nat` is in parentheses. `mulKaratsuba` splits both operands at half the larger
one, which needs the smaller one to be longer than that half, so on `n` by `n / 2` limbs it is
`mulBasecase`, and its ratio grows with the size. Toom-3 by 2 and Toom-4 by 2 keep it near 4. At
512 by 256 limbs `toom2` is still `mulKaratsuba`, so still `mulBasecase`.

### Large sizes, multiplication

From `bench toom fft auto toom2 fft2 1024 2048 3072 4096 8192 16384 32768 65536`, the fastest of
three runs, on 2026-10-23, with Toom-6.

| op | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `toom` | 251 µs (3.33) | 689 µs (3.19) | 1.20 ms (3.31) | 1.78 ms (3.48) | 4.88 ms (4.14) | 12.3 ms (4.66) | 32.7 ms (5.10) | 81.3 ms (6.07) |
| `fft` | 551 µs (7.30) | 853 µs (4.06) | 1.27 ms (3.83) | 1.82 ms (4.05) | 3.61 ms (3.37) | 8.03 ms (3.63) | 18.2 ms (3.43) | 40.3 ms (3.03) |
| `auto` | 250 µs (3.31) | 684 µs (3.24) | 1.19 ms (3.60) | 1.82 ms (4.06) | 3.62 ms (3.35) | 8.08 ms (3.64) | 18.2 ms (3.41) | 40.4 ms (3.04) |
| `toom2` | 205 µs (3.69) | 618 µs (4.09) | 980 µs (3.98) | 1.54 ms (4.61) | 3.95 ms (5.19) | 10.7 ms (6.33) | 27.2 ms (7.01) | 70.6 ms (7.32) |
| `fft2` | 318 µs (5.72) | 691 µs (4.55) | 939 µs (3.77) | 1.27 ms (3.80) | 2.69 ms (3.51) | 6.01 ms (3.54) | 13.2 ms (3.38) | 31.6 ms (3.27) |

### Unbalanced products

`MPN.mul`, ratio to `Nat` only, the fastest of three runs, on 2026-10-23 before Toom-6: `auto2`,
`auto4`, `auto8` for `n` by `n / 2`, `n / 4`, `n / 8` limbs, and `autobS` for `n` by `S` limbs.
With Toom-6 and the new FFT thresholds, `auto2`, `auto4` and `auto8` stay within 2.7–3.7 but for
4096 by 1024 (4.12) and 6144 by 1536 (4.27), where the FFT and the Toom methods tie.

| n | `auto` | `auto2` | `auto4` | `auto8` | `b64` | `b128` | `b256` | `b320` | `b512` | `b1024` | `b2048` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.65 | 2.80 | 2.68 | 1.89 | | | | | | | |
| 512 | 3.02 | 3.08 | 2.83 | 2.74 | | | | | | | |
| 1024 | 3.35 | 3.24 | 3.07 | 2.85 | 2.74 | 2.85 | 3.11 | 3.18 | 3.27 | 3.32 | 3.33 |
| 2048 | 3.24 | 3.35 | 3.25 | 3.07 | | | | | | | |
| 3072 | 3.49 | 3.80 | 3.25 | 3.30 | | | | | | | |
| 4096 | 3.52 | 3.79 | 3.98 | 3.25 | 2.70 | 2.85 | 3.11 | 3.15 | 3.25 | 3.98 | 3.83 |
| 6144 | 2.98 | 3.69 | 4.27 | 3.17 | | | | | | | |
| 8192 | 2.82 | 3.49 | 3.67 | 3.46 | | | | | | | |
| 16384 | 2.95 | 3.50 | 3.53 | 3.24 | 2.70 | 2.85 | 3.10 | 3.17 | 3.26 | 3.37 | 3.25 |
| 32768 | 2.83 | 3.35 | 3.34 | 3.06 | | | | | | | |
| 65536 | 3.01 | 3.24 | 3.21 | 3.37 | 2.82 | 2.84 | 3.09 | 3.18 | 3.24 | 3.97 | 3.70 |

Before the split, the products whose smaller operand was below the Toom shapes went to the
schoolbook method: 5–6 times `Nat` at `n` by 256 or 320 limbs, 10.8 at 1536 by 384. The one
cell left above 4, 6144 by 1536, is as fast either way.

### Large sizes, division

From `bench sbdiv div sqrt 512 1024 2048 4096 8192`, the fastest of three runs, on 2026-10-24
(after `ef5cd91`). The
sizes are those of the divisor (`div`, `sbdiv`: `2 n` by `n` limbs) or of the operand (`sqrt`).

| op | 512 | 1024 | 2048 | 4096 | 8192 |
|---|---:|---:|---:|---:|---:|
| `sbdiv` | 221 µs (4.29) | 862 µs (5.67) | 3.41 ms (8.38) | 13.9 ms (13.11) | 55.6 ms (23.36) |
| `div` | 209 µs (4.06) | 642 µs (4.22) | 1.84 ms (4.73) | 5.27 ms (5.33) | 14.5 ms (6.07) |
| `sqrt` | 75.2 µs (0.33) | 206 µs (0.24) | 609 µs (0.24) | 1.78 ms (0.26) | 5.01 ms (0.29) |

The ratio to `Nat` is in parentheses; for `sqrt` it is to Lean's `Nat.sqrt`, not to GMP. The
divide-and-conquer division costs `O(M(n) log n)`, and its ratio grows slowly with the size, where
GMP switches to division by Newton's iteration.

### Large sizes, squares

From `bench ksqr toomsqr fftsqr autosqr 512 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-23.

| op | 512 | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ksqr` | 61 µs (2.05) | 186 µs (2.44) | 569 µs (2.63) | 1.07 ms (2.93) | 1.72 ms (3.31) | 5.17 ms (4.34) | 15.6 ms (6.22) | 47.0 ms (7.93) | 142 ms (11.54) |
| `toomsqr` | 61 µs (2.04) | 170 µs (2.24) | 486 µs (2.29) | 865 µs (2.60) | 1.30 ms (2.88) | 3.64 ms (3.37) | 9.65 ms (4.35) | 26.5 ms (4.95) | 69.4 ms (5.64) |
| `fftsqr` | 177 µs (5.88) | 383 µs (5.03) | 573 µs (2.70) | 823 µs (2.47) | 1.22 ms (2.71) | 2.38 ms (2.20) | 5.36 ms (2.41) | 12.0 ms (2.24) | 26.9 ms (2.19) |
| `autosqr` | 61 µs (2.01) | 169 µs (2.21) | 485 µs (2.28) | 823 µs (2.46) | 1.22 ms (2.71) | 2.38 ms (2.20) | 5.36 ms (2.41) | 12.0 ms (2.23) | 26.9 ms (2.19) |

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
