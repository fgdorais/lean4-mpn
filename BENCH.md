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
  `49cf1b1`, C compiled with `-falign-loops=64` (lakefile). Tables of 2026-10-25 at `5b34dcf`
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
| `add` | 0.44 | 0.56 | 0.50 | 0.56 | 0.57 | 0.58 | 0.60 | 0.62 | 0.67 | 0.69 | 0.74 | 0.80 | 0.89 | 0.98 | 0.94 | 0.99 | 1.11 |
| `sub` | 0.52 | 0.46 | 0.55 | 0.47 | 0.48 | 0.51 | 0.54 | 0.55 | 0.55 | 0.60 | 0.63 | 0.74 | 0.84 | 0.97 | 1.02 | 1.09 | 1.29 |
| `shl` | 0.33 | 0.43 | 0.44 | 0.45 | 0.45 | 0.45 | 0.47 | 0.48 | 0.51 | 0.55 | 0.59 | 0.63 | 0.73 | 0.83 | 0.67 | 0.91 | 1.09 |
| `shr` | 3.62 | 0.43 | 0.46 | 0.47 | 0.46 | 0.48 | 0.51 | 0.52 | 0.53 | 0.56 | 0.60 | 0.65 | 0.75 | 0.85 | 0.68 | 0.89 | 1.03 |
| `div1` | 3.05 | 0.45 | 0.47 | 0.49 | 0.51 | 0.57 | 0.66 | 0.76 | 0.92 | 1.02 | 1.17 | 1.30 | 1.44 | 1.52 | 1.48 | 1.60 | 1.70 |
| `div` | 1.09 | 2.31 | 2.25 | 2.23 | 2.31 | 2.37 | 2.36 | 2.43 | 2.48 | 2.70 | 3.10 | 3.01 | 3.17 | 3.33 | 3.27 | 3.45 | 3.91 |
| `sbdiv` | 0.72 | 2.02 | 1.92 | 1.92 | 2.01 | 2.12 | 2.22 | 2.28 | 2.37 | 2.61 | 3.06 | 2.95 | 3.12 | 3.32 | 3.27 | 3.45 | 4.26 |
| `sqrt` | 5.30 | 0.42 | 1.51 | 1.30 | 1.84 | 2.00 | 2.57 | 2.70 | 2.75 | 2.10 | 1.88 | 1.67 | 1.10 | 0.92 | 0.58 | 0.43 | 0.32 |
| `gcd` | 0.90 | 1.49 | 3.32 | 2.38 | 2.33 | 2.74 | 2.91 | 2.65 | 2.76 | 2.73 | 2.82 | 2.82 | 2.91 | 2.94 | 3.04 | 2.99 | 2.44 |
| `str` | 2.98 | 0.06 | 0.04 | 0.04 | 0.05 | 0.05 | 0.04 | 0.04 | 0.04 | 0.04 | 0.05 | 0.05 | 0.04 | 0.04 | 0.03 | 0.03 | 0.02 |
| `parse` | 1.03 | 0.14 | 0.09 | 0.08 | 0.07 | 0.07 | 0.06 | 0.06 | 0.06 | 0.05 | 0.05 | 0.05 | 0.05 | 0.05 | 0.04 | 0.04 | 0.07 |
| `mul1` | 0.26 | 0.30 | 0.29 | 0.32 | 0.33 | 0.33 | 0.36 | 0.37 | 0.38 | 0.42 | 0.46 | 0.50 | 0.56 | 0.66 | 0.57 | 0.69 | 0.79 |
| `addmul1` | 0.19 | 0.19 | 0.19 | 0.19 | 0.20 | 0.23 | 0.22 | 0.22 | 0.24 | 0.26 | 0.28 | 0.33 | 0.38 | 0.46 | 0.46 | 0.46 | 0.52 |
| `mul` | 0.39 | 0.42 | 0.49 | 0.53 | 0.60 | 0.69 | 0.89 | 1.02 | 1.30 | 1.53 | 1.95 | 2.29 | 2.78 | 3.38 | 4.12 | 4.69 | 7.37 |
| `sqr` | 0.33 | 0.48 | 0.55 | 0.56 | 0.61 | 0.68 | 0.73 | 0.77 | 0.86 | 0.93 | 1.12 | 1.23 | 1.49 | 1.74 | 2.08 | 2.36 | 3.74 |
| `comba` | 0.80 | 1.33 | 1.96 | 2.40 | 3.26 | 4.08 | 4.81 | 5.10 | 5.36 | 5.25 | 5.20 | 5.06 | 4.81 | 4.91 | 5.02 | 5.17 | 6.90 |
| `kara` | 0.44 | 0.49 | 0.57 | 0.59 | 0.65 | 0.74 | 0.94 | 1.04 | 1.32 | 1.54 | 1.96 | 2.08 | 2.29 | 2.38 | 2.56 | 2.59 | 3.11 |
| `ksqr` | 0.33 | 0.48 | 0.54 | 0.56 | 0.62 | 0.67 | 0.74 | 0.76 | 0.87 | 0.94 | 1.11 | 1.25 | 1.33 | 1.47 | 1.54 | 1.61 | 2.00 |
| `mulref` | 0.23 | 0.33 | 0.51 | 0.69 | 1.20 | 1.71 | 2.73 | 3.49 | 5.04 | 6.45 | 8.14 | 9.17 | 11.02 | 12.74 | 15.19 | 17.29 | 27.00 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 63.5 ns | 65.8 ns | 67 ns | 67.8 ns | 68.9 ns | 70 ns | 72.4 ns | 75.1 ns | 82 ns | 88.1 ns | 98.7 ns | 113 ns | 140 ns | 169 ns | 224 ns | 270 ns | 479 ns |
| `sub` | 62.8 ns | 63.8 ns | 68.1 ns | 64.6 ns | 67.8 ns | 70.3 ns | 75.2 ns | 81.2 ns | 88.2 ns | 97.1 ns | 111 ns | 128 ns | 158 ns | 198 ns | 264 ns | 323 ns | 580 ns |
| `shl` | 47.5 ns | 47.9 ns | 49.3 ns | 50.4 ns | 50.9 ns | 50.3 ns | 53.1 ns | 55.1 ns | 58.9 ns | 63.8 ns | 71.3 ns | 79.8 ns | 98 ns | 120 ns | 154 ns | 200 ns | 344 ns |
| `shr` | 48.1 ns | 48.2 ns | 51.1 ns | 52.9 ns | 52.4 ns | 54.4 ns | 57.2 ns | 59.3 ns | 64.3 ns | 67.7 ns | 75.1 ns | 83.6 ns | 101 ns | 122 ns | 156 ns | 202 ns | 346 ns |
| `div1` | 47.2 ns | 53.9 ns | 57.8 ns | 61.2 ns | 65.7 ns | 76.4 ns | 93.9 ns | 117 ns | 160 ns | 199 ns | 280 ns | 364 ns | 526 ns | 690 ns | 1.02 µs | 1.35 µs | 2.67 µs |
| `div` | 130 ns | 298 ns | 317 ns | 346 ns | 388 ns | 417 ns | 529 ns | 688 ns | 1.04 µs | 1.54 µs | 2.87 µs | 4.54 µs | 9.44 µs | 16.1 µs | 33.4 µs | 57.6 µs | 201 µs |
| `sbdiv` | 84 ns | 256 ns | 271 ns | 292 ns | 335 ns | 371 ns | 486 ns | 642 ns | 990 ns | 1.49 µs | 2.84 µs | 4.49 µs | 9.27 µs | 16 µs | 33.4 µs | 57.6 µs | 219 µs |
| `sqrt` | 492 ns | 490 ns | 1.86 µs | 1.84 µs | 3.44 µs | 4.07 µs | 5.49 µs | 6.12 µs | 7.32 µs | 7.38 µs | 9.76 µs | 10.5 µs | 13.6 µs | 16 µs | 23.1 µs | 29.9 µs | 71 µs |
| `gcd` | 96.8 ns | 265 ns | 1.26 µs | 1.32 µs | 2.13 µs | 3.53 µs | 5.68 µs | 7.07 µs | 11.8 µs | 16.5 µs | 27.9 µs | 40 µs | 70.9 µs | 108 µs | 203 µs | 317 µs | 972 µs |
| `str` | 105 ns | 405 ns | 546 ns | 737 ns | 1.37 µs | 1.83 µs | 2.37 µs | 3.68 µs | 6.14 µs | 9.38 µs | 17 µs | 25.3 µs | 37.3 µs | 57.4 µs | 86.1 µs | 143 µs | 374 µs |
| `parse` | 265 ns | 569 ns | 768 ns | 971 ns | 1.39 µs | 1.8 µs | 2.66 µs | 3.53 µs | 5.28 µs | 7.09 µs | 10.8 µs | 14.7 µs | 23.2 µs | 32.6 µs | 54.3 µs | 79.6 µs | 394 µs |
| `mul1` | 46 ns | 46.8 ns | 49.1 ns | 49.1 ns | 51.1 ns | 52.9 ns | 56.5 ns | 59.8 ns | 66.4 ns | 72.8 ns | 83.9 ns | 96.4 ns | 119 ns | 153 ns | 201 ns | 254 ns | 453 ns |
| `addmul1` | 44.9 ns | 45.1 ns | 46.1 ns | 46.5 ns | 48.2 ns | 49.7 ns | 53.4 ns | 56.3 ns | 62.1 ns | 69.7 ns | 84 ns | 99.4 ns | 134 ns | 173 ns | 230 ns | 280 ns | 519 ns |
| `mul` | 55.9 ns | 58 ns | 62.4 ns | 69.6 ns | 85.1 ns | 107 ns | 174 ns | 258 ns | 495 ns | 833 ns | 1.82 µs | 3.27 µs | 7.43 µs | 13.7 µs | 31.1 µs | 55.3 µs | 221 µs |
| `sqr` | 59.8 ns | 65.5 ns | 69.2 ns | 73.2 ns | 86.5 ns | 105 ns | 144 ns | 195 ns | 327 ns | 509 ns | 1.04 µs | 1.79 µs | 3.99 µs | 7.01 µs | 15.7 µs | 27.9 µs | 111 µs |
| `comba` | 115 ns | 183 ns | 251 ns | 319 ns | 463 ns | 632 ns | 948 ns | 1.3 µs | 2.03 µs | 2.89 µs | 4.85 µs | 7.24 µs | 12.9 µs | 19.9 µs | 37.8 µs | 61 µs | 207 µs |
| `kara` | 63.3 ns | 67.1 ns | 72 ns | 77.3 ns | 92.9 ns | 114 ns | 182 ns | 265 ns | 502 ns | 838 ns | 1.83 µs | 2.97 µs | 6.08 µs | 9.61 µs | 19.3 µs | 30.3 µs | 93.2 µs |
| `ksqr` | 60.6 ns | 65.9 ns | 69 ns | 74 ns | 87.7 ns | 104 ns | 144 ns | 195 ns | 329 ns | 509 ns | 1.04 µs | 1.79 µs | 3.59 µs | 6 µs | 11.6 µs | 19 µs | 59.3 µs |
| `mulref` | 32.9 ns | 45.8 ns | 65.3 ns | 91.4 ns | 170 ns | 265 ns | 529 ns | 891 ns | 1.91 µs | 3.51 µs | 7.6 µs | 13.3 µs | 29.3 µs | 51.6 µs | 115 µs | 204 µs | 810 µs |

### Large sizes

The tables above stop at 512 limbs, below the reach of `mulToom`. These are from
`bench kara toom kara2 toom2 512 768 1024 1536 2048 4096`, the fastest of three runs, on
2026-10-25 (`5b34dcf`). The sizes are those of the larger operand.

| op | 512 | 768 | 1024 | 1536 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `kara` | 95.6 µs (3.18) | 185 µs (3.52) | 290 µs (3.82) | 561 µs (3.95) | 882 µs (4.12) | 2.66 ms (5.19) |
| `toom` | 90.2 µs (3.00) | 166 µs (3.16) | 252 µs (3.32) | 449 µs (3.18) | 691 µs (3.21) | 1.79 ms (3.47) |
| `kara2` | 112 µs (5.49) | 251 µs (7.01) | 446 µs (7.99) | 1 ms (9.71) | 1.78 ms (11.71) | 7.07 ms (18.75) |
| `toom2` | 111 µs (5.44) | 128 µs (3.58) | 209 µs (3.75) | 396 µs (3.84) | 627 µs (4.12) | 1.54 ms (4.08) |

The ratio to `Nat` is in parentheses. `mulKaratsuba` splits both operands at half the larger
one, which needs the smaller one to be longer than that half, so on `n` by `n / 2` limbs it is
`mulBasecase`, and its ratio grows with the size. Toom-3 by 2 and Toom-4 by 2 keep it near 4. At
512 by 256 limbs `toom2` is still `mulKaratsuba`, so still `mulBasecase`.

### Large sizes, multiplication

From `bench toom fft auto toom2 fft2 mulmod 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-25 (`5b34dcf`). `mulmod` is the product
modulo `β^n - 1` of two operands of `n` limbs, against the whole product on the `Nat` side.

| op | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `toom` | 252 µs (3.32) | 688 µs (3.19) | 1.2 ms (3.29) | 1.79 ms (3.46) | 4.88 ms (4.10) | 12.3 ms (4.62) | 32.8 ms (5.08) | 81.4 ms (6.07) |
| `fft` | 559 µs (7.38) | 863 µs (4.07) | 1.28 ms (3.84) | 1.84 ms (4.08) | 3.62 ms (3.35) | 8.09 ms (3.63) | 18.2 ms (3.40) | 40.4 ms (3.01) |
| `auto` | 252 µs (3.31) | 687 µs (3.26) | 1.2 ms (3.60) | 1.84 ms (4.07) | 3.63 ms (3.36) | 8.08 ms (3.62) | 18.2 ms (3.38) | 40.5 ms (3.02) |
| `toom2` | 206 µs (3.69) | 623 µs (4.10) | 987 µs (4.00) | 1.54 ms (4.60) | 3.98 ms (5.18) | 10.8 ms (6.35) | 27.3 ms (7.00) | 70.9 ms (7.32) |
| `fft2` | 322 µs (5.77) | 703 µs (4.62) | 948 µs (3.82) | 1.28 ms (3.81) | 2.7 ms (3.52) | 6.05 ms (3.54) | 13.2 ms (3.38) | 31.7 ms (3.26) |
| `mulmod` | 247 µs (3.25) | 540 µs (2.56) | 674 µs (2.02) | 833 µs (1.84) | 1.85 ms (1.71) | 3.66 ms (1.65) | 8.15 ms (1.52) | 18.2 ms (1.36) |

### Unbalanced products

`MPN.mul`, ratio to `Nat` only, the fastest of three runs, on 2026-10-25 (`5b34dcf`): `auto2`,
`auto4`, `auto8` for `n` by `n / 2`, `n / 4`, `n / 8` limbs, and `autobS` for `n` by `S` limbs.

| n | `auto` | `auto2` | `auto4` | `auto8` | `b64` | `b128` | `b256` | `b320` | `b512` | `b1024` | `b2048` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.63 | 2.79 | 2.68 | 1.89 |  |  |  |  |  |  |  |
| 512 | 3.01 | 3.08 | 2.81 | 2.69 |  |  |  |  |  |  |  |
| 1024 | 3.32 | 3.26 | 3.05 | 2.90 | 2.71 | 2.82 | 3.08 | 3.15 | 3.26 | 3.33 | 3.36 |
| 2048 | 3.21 | 3.32 | 3.26 | 3.14 |  |  |  |  |  |  |  |
| 3072 | 3.30 | 3.83 | 3.23 | 3.35 |  |  |  |  |  |  |  |
| 4096 | 3.56 | 3.81 | 4.02 | 3.24 | 2.69 | 2.83 | 3.08 | 3.15 | 3.28 | 4.02 | 3.83 |
| 6144 | 3.00 | 3.71 | 4.29 | 3.21 |  |  |  |  |  |  |  |
| 8192 | 2.80 | 3.51 | 3.80 | 3.48 |  |  |  |  |  |  |  |
| 16384 | 2.94 | 3.54 | 3.57 | 3.26 | 2.69 | 2.82 | 3.06 | 3.15 | 3.25 | 3.37 | 3.28 |
| 32768 | 2.82 | 3.37 | 3.35 | 3.06 |  |  |  |  |  |  |  |
| 65536 | 3.03 | 3.29 | 3.25 | 3.41 | 2.80 | 2.83 | 3.06 | 3.17 | 3.25 | 4.00 | 3.68 |

Before the split, the products whose smaller operand was below the Toom shapes went to the
schoolbook method: 5–6 times `Nat` at `n` by 256 or 320 limbs, 10.8 at 1536 by 384. The cells
left above 4, 4096 by 1024 (4.02) and 6144 by 1536 (4.29), are where the FFT and the Toom
methods tie.

### Large sizes, division

From `bench sbdiv div sqrt 512 1024 2048 4096 8192 16384`, the fastest of three runs, on
2026-10-25 (`5b34dcf`). The sizes are those of the divisor (`div`, `sbdiv`:
`2 n` by `n` limbs) or of the operand (`sqrt`).

| op | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
|---|---:|---:|---:|---:|---:|---:|
| `sbdiv` | 220 µs (4.26) | 860 µs (5.66) | 3.4 ms (8.37) | 13.9 ms (13.11) | 55.3 ms (23.53) | 221 ms (38.43) |
| `div` | 204 µs (3.95) | 616 µs (4.05) | 1.78 ms (4.59) | 5.06 ms (5.16) | 14 ms (6.45) | 35.7 ms (6.19) |
| `sqrt` | 72.4 µs (0.32) | 202 µs (0.24) | 596 µs (0.24) | 1.73 ms (0.26) | 4.84 ms (0.29) | 12.4 ms (0.30) |

The ratio to `Nat` is in parentheses; for `sqrt` it is to Lean's `Nat.sqrt`, not to GMP. The
divide-and-conquer division costs `O(M(n) log n)`, and its ratio grows slowly with the size, where
GMP switches to division by Newton's iteration.

### Large sizes, gcd and decimal strings

From `bench gcd str parse 512 1024 2048 4096 8192`, the fastest of three runs, on 2026-10-25
(`5b34dcf`). `str` and `parse` compare with Lean's `Nat.repr` and `String.toNat?`, which are
written in Lean, not with GMP's `mpz_get_str` and `mpz_set_str`; `gcd` compares with `Nat.gcd`,
GMP's `mpz_gcd`.

| op | 512 | 1024 | 2048 | 4096 | 8192 |
|---|---:|---:|---:|---:|---:|
| `gcd` | 979 µs (2.44) | 3.29 ms (2.55) | 10.1 ms (2.84) | 29.6 ms (3.13) | 79.7 ms (3.27) |
| `str` | 375 µs (0.02) | 1.06 ms (0.01) | 2.96 ms (0.01) | 8.28 ms (0.01) | 22.5 ms (0.01) |
| `parse` | 396 µs (0.07) | 920 µs (0.05) | 2.23 ms (0.04) | 5.42 ms (0.03) | 13.4 ms (0.02) |

`gcd` is Lehmer's algorithm with steps of about 62 bits, like GMP's: two runs of Euclid's steps on
the leading words, the second on the leading 128 bits after the first (`cofactors2`), applied by
`mulSubMul` in one pass for each number; and half-gcd from `gcdHalf = 1024` limbs, whose base
case up to `hgcdBase = 128` limbs is the same steps with the matrix updated in one pass per entry
(`mulAddMul`); above the base case it runs on the generic layer. At 16384 limbs `gcd` takes
216 ms, 3.57 times `Nat`. `gcdh<T>` sweeps `gcdHalf`.

### Large sizes, squares

From `bench ksqr toomsqr fftsqr autosqr 512 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-10-25 (`5b34dcf`).

| op | 512 | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ksqr` | 59.9 µs (2.01) | 183 µs (2.42) | 559 µs (2.61) | 1.05 ms (2.91) | 1.69 ms (3.30) | 5.1 ms (4.32) | 15.4 ms (6.21) | 46.4 ms (7.90) | 139 ms (10.53) |
| `toomsqr` | 60 µs (2.01) | 166 µs (2.20) | 481 µs (2.29) | 840 µs (2.55) | 1.23 ms (2.75) | 3.31 ms (3.06) | 8.61 ms (3.91) | 22.9 ms (4.32) | 58.9 ms (4.43) |
| `fftsqr` | 182 µs (6.11) | 394 µs (5.22) | 581 µs (2.77) | 831 µs (2.51) | 1.24 ms (2.78) | 2.39 ms (2.23) | 5.39 ms (2.45) | 12 ms (2.26) | 26.7 ms (2.01) |
| `autosqr` | 59.3 µs (1.98) | 166 µs (2.20) | 481 µs (2.29) | 831 µs (2.51) | 1.24 ms (2.77) | 2.39 ms (2.23) | 5.38 ms (2.46) | 12 ms (2.26) | 26.8 ms (2.02) |

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
| 2026-10-24 | `e985b32`+ | all tables regenerated (five runs of the default sizes, three of each large-size section) after the gcd work and the split into `main`, `main32` and `main64` | `gcd` 2.37 at 4 limbs, 2.32 at 6, 2.79 at 8 (were 2.89, 2.64, 3.19: the two-word gcd ends each run of Lehmer's steps); the large sizes within 1% of `d813acd`; `add`, `sub`, `shl` 3–10 ns slower at every size with code unchanged since `d813acd` (ratios 0.51 → 0.57 at 4 limbs), likely code layout |
| 2026-10-25 | `4af732e`+ | lean4-scalar-arrays `85c955d` → `49cf1b1` (opaque array types, the array `foldInPlace` dropped, `ensureExclusive` public): `foldUInPlaceThen` calls `ensureExclusive` instead of `ensureExclusiveUnsafe`; tables not regenerated (they are at `85c955d`) | from three runs of `bench --no-nat` on 10 operations at 1 to 256 limbs, within ±2% from 64 limbs and within a few ns below (`sub` 9 ns faster at 1 to 4 limbs, `sqr` 9 ns slower at 1) |
| 2026-10-25 | `5b34dcf`+ | all tables regenerated on lean4-scalar-arrays `49cf1b1` (five runs of the default sizes, three of each large-size section) | within 8% of `e985b32` everywhere except the squares at 65536 limbs, where only `Nat` moved (`autosqr` 2.20 → 2.02 with the same 26.7 ms) |
| 2026-10-25 | `140f314`+ | Karatsuba's middle term in one pass (`karatsubaMid`, from `main32`'s `addDiffInto`): limb `r[k + i] + t[i] - z₀[i] - z₂[i]` with a carry between `-2` and `1` (its high word from `UInt64.addDiffh`, a `__uint128_t` sum), written into `t` with lean4-scalar-arrays' slice fold, then copied into `r` with `copySlice`; it replaces two `subInto` and an `addInto`, for `mulKaratsuba` and `sqrKaratsuba` | from three alternating runs against `5b34dcf`: `kara` 5–7% faster from 128 to 4096 limbs (1024: 287 → 266 µs), `ksqr` 4–7%, `toom`, `toomsqr`, `auto`, `autosqr` 3–7% from 128 to 2048 limbs; unchanged at 4096, where the FFT takes over. Tables not regenerated |
