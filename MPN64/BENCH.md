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

Arguments select operations and sizes, for example `bench mul kara 4 16`, and `--no-nat` skips
`Nat`, and the conversions of the operands to it, for a profiler. Pinning the process to one core with `taskset` makes the results steadier.
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
- **Machine:** AMD Ryzen 5 5600X (Zen 3), Linux 7.2, Lean `v4.36.0-rc2`, lean4-scalar-arrays
  `fe6af25`, C compiled with `-falign-loops=64` (`-falign-loops=32` for the shared `MPN`; see the
  lakefile). Tables of 2026-11-08 at `b0a1b55`, the fastest of five runs (three for the large
  sizes) over the rows whose spread is within ±2% (history below).

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

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.26 | 0.32 | 0.30 | 0.35 | 0.36 | 0.37 | 0.24 | 0.39 | 0.44 | 0.47 | 0.51 | 0.57 | 0.68 | 0.79 | 0.75 | 0.81 | 0.98 |
| `sub` | 0.33 | 0.29 | 0.35 | 0.33 | 0.34 | 0.35 | 0.37 | 0.36 | 0.39 | 0.42 | 0.46 | 0.56 | 0.66 | 0.78 | 0.81 | 0.95 | 1.15 |
| `shl` | 0.30 | 0.39 | 0.38 | 0.39 | 0.40 | 0.40 | 0.40 | 0.40 | 0.41 | 0.41 | 0.43 | 0.44 | 0.48 | 0.54 | 0.47 | 0.47 | 0.60 |
| `shr` | 2.22 | 0.37 | 0.38 | 0.39 | 0.40 | 0.41 | 0.44 | 0.40 | 0.40 | 0.41 | 0.42 | 0.44 | 0.48 | 0.53 | 0.46 | 0.50 | 0.59 |
| `div1` | 3.23 | 0.44 | 0.46 | 0.46 | 0.53 | 0.55 | 0.60 | 0.68 | 0.71 | 0.75 | 0.84 | 0.88 | 0.96 | 0.99 | 0.95 | 0.99 | 1.05 |
| `div` | 0.74 | 1.15 | 1.20 | 1.60 | 1.75 | 1.63 | 1.81 | 2.15 | 2.19 | 2.27 | 2.42 | 2.40 | 2.34 | 2.43 | 2.37 | 2.86 | 2.92 |
| `divmod` | 0.75 | 1.18 | 1.24 | 1.62 | 1.78 | 1.60 | 1.80 | 2.17 | 2.22 | 2.28 | 2.41 | 2.42 | 2.35 | 2.45 | 2.38 | 2.87 | 2.92 |
| `sbdiv` | 0.60 | 1.12 | 1.13 | 1.52 | 1.66 | 1.55 | 1.75 | 2.09 | 2.14 | 2.24 | 2.41 | 2.38 | 2.33 | 2.42 | 2.37 | 2.50 | 3.04 |
| `sqrt` | 1.84 | 0.35 | 1.00 | 0.87 | 1.03 | 1.22 | 1.36 | 1.54 | 1.49 | 1.12 | 1.02 | 0.95 | 0.63 | 0.57 | 0.37 | 0.28 | 0.23 |
| `gcd` | 0.97 | 1.59 | 2.37 | 1.90 | 1.81 | 1.96 | 2.09 | 1.96 | 2.00 | 1.95 | 1.96 | 1.92 | 1.93 | 1.90 | 1.92 | 1.91 | 1.48 |
| `str` | 2.11 | 0.05 | 0.04 | 0.04 | 0.04 | 0.04 | 0.03 | 0.03 | 0.03 | 0.03 | 0.04 | 0.04 | 0.03 | 0.03 | 0.02 | 0.02 | 0.01 |
| `parse` | 1.05 | 0.14 | 0.09 | 0.08 | 0.07 | 0.07 | 0.06 | 0.06 | 0.06 | 0.05 | 0.05 | 0.05 | 0.05 | 0.05 | 0.04 | 0.04 | 0.04 |
| `mul1` | 0.27 | 0.31 | 0.28 | 0.32 | 0.34 | 0.34 | 0.35 | 0.36 | 0.39 | 0.41 | 0.45 | 0.50 | 0.56 | 0.66 | 0.60 | 0.68 | 0.78 |
| `addmul1` | 0.18 | 0.19 | 0.19 | 0.20 | 0.20 | 0.22 | 0.22 | 0.21 | 0.25 | 0.26 | 0.17 | 0.20 | 0.25 | 0.31 | 0.28 | 0.34 | 0.41 |
| `mul` | 0.39 | 0.47 | 0.52 | 0.56 | 0.65 | 0.71 | 0.82 | 0.87 | 1.16 | 1.38 | 1.68 | 1.96 | 2.27 | 2.72 | 3.26 | 3.67 | 5.73 |
| `sqr` | 0.32 | 0.45 | 0.52 | 0.56 | 0.59 | 0.65 | 0.71 | 0.66 | 0.83 | 0.91 | 1.05 | 1.21 | 1.41 | 1.66 | 2.03 | 2.34 | 3.75 |
| `kara` | 0.66 | 0.42 | 0.80 | 0.82 | 0.85 | 0.90 | 1.02 | 1.02 | 1.25 | 1.26 | 1.72 | 1.81 | 1.92 | 1.95 | 2.14 | 2.11 | 2.54 |
| `ksqr` | 0.42 | 0.57 | 0.66 | 0.69 | 0.73 | 0.77 | 0.81 | 0.81 | 0.87 | 0.94 | 1.07 | 1.21 | 1.20 | 1.33 | 1.36 | 1.44 | 1.73 |
| `mulref` | 0.22 | 0.32 | 0.45 | 0.58 | 0.90 | 1.32 | 2.03 | 2.47 | 3.55 | 4.71 | 5.87 | 6.80 | 7.85 | 9.05 | 11.04 | 12.37 | 19.37 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 37.5 ns | 38.6 ns | 40.7 ns | 42.4 ns | 43.2 ns | 44.5 ns | 47 ns | 47.8 ns | 54.2 ns | 60.8 ns | 70.7 ns | 82.2 ns | 109 ns | 139 ns | 194 ns | 237 ns | 437 ns |
| `sub` | 40.3 ns | 41.5 ns | 43 ns | 44.9 ns | 47.4 ns | 48.5 ns | 51.6 ns | 54.1 ns | 59.2 ns | 65.9 ns | 80.1 ns | 96.4 ns | 130 ns | 168 ns | 233 ns | 293 ns | 545 ns |
| `shl` | 42.6 ns | 43 ns | 42.9 ns | 43.9 ns | 44.7 ns | 44.3 ns | 44.9 ns | 46.2 ns | 47.3 ns | 49.2 ns | 53.9 ns | 57.3 ns | 66.7 ns | 78.9 ns | 96.5 ns | 116 ns | 199 ns |
| `shr` | 30.6 ns | 42.4 ns | 44.1 ns | 44.8 ns | 46.4 ns | 47.7 ns | 51.1 ns | 47.2 ns | 48.6 ns | 50.9 ns | 54.7 ns | 59.1 ns | 68.7 ns | 80.3 ns | 97.7 ns | 117 ns | 199 ns |
| `div1` | 51 ns | 53.9 ns | 57.5 ns | 59 ns | 68.7 ns | 74.1 ns | 85.8 ns | 108 ns | 125 ns | 148 ns | 203 ns | 251 ns | 356 ns | 455 ns | 656 ns | 859 ns | 1.67 µs |
| `div` | 90.9 ns | 151 ns | 172 ns | 250 ns | 299 ns | 295 ns | 409 ns | 614 ns | 922 ns | 1.31 µs | 2.26 µs | 3.65 µs | 6.96 µs | 11.8 µs | 24.2 µs | 47.7 µs | 150 µs |
| `divmod` | 92.6 ns | 155 ns | 178 ns | 253 ns | 302 ns | 290 ns | 408 ns | 622 ns | 935 ns | 1.32 µs | 2.25 µs | 3.68 µs | 6.97 µs | 11.9 µs | 24.3 µs | 47.9 µs | 150 µs |
| `sbdiv` | 74.4 ns | 147 ns | 161 ns | 236 ns | 283 ns | 286 ns | 400 ns | 599 ns | 905 ns | 1.29 µs | 2.25 µs | 3.64 µs | 6.97 µs | 11.8 µs | 24.2 µs | 41.7 µs | 156 µs |
| `sqrt` | 167 ns | 404 ns | 1.24 µs | 1.23 µs | 1.94 µs | 2.5 µs | 2.97 µs | 3.52 µs | 3.99 µs | 3.96 µs | 5.36 µs | 5.99 µs | 7.83 µs | 9.79 µs | 14.6 µs | 19.9 µs | 50.8 µs |
| `gcd` | 106 ns | 285 ns | 905 ns | 1.06 µs | 1.66 µs | 2.53 µs | 4.1 µs | 5.23 µs | 8.58 µs | 11.8 µs | 19.5 µs | 27.5 µs | 47.2 µs | 70.1 µs | 129 µs | 202 µs | 594 µs |
| `str` | 79 ns | 338 ns | 482 ns | 630 ns | 1.21 µs | 1.52 µs | 2.04 µs | 3.03 µs | 4.74 µs | 7.01 µs | 13.3 µs | 19.4 µs | 29.4 µs | 43.4 µs | 66.4 µs | 108 µs | 282 µs |
| `parse` | 256 ns | 588 ns | 788 ns | 996 ns | 1.42 µs | 1.82 µs | 2.7 µs | 3.58 µs | 5.34 µs | 7.16 µs | 11 µs | 14.9 µs | 23.3 µs | 32.9 µs | 54.4 µs | 79.2 µs | 210 µs |
| `mul1` | 47.2 ns | 48.1 ns | 48.5 ns | 49.6 ns | 51.6 ns | 53.3 ns | 54.9 ns | 58.3 ns | 65 ns | 71.1 ns | 82 ns | 96.4 ns | 120 ns | 156 ns | 203 ns | 254 ns | 457 ns |
| `addmul1` | 43.5 ns | 44.5 ns | 45.9 ns | 45.5 ns | 46.4 ns | 48 ns | 52.3 ns | 54.8 ns | 61.9 ns | 68.5 ns | 83 ns | 98.5 ns | 130 ns | 166 ns | 223 ns | 280 ns | 500 ns |
| `mul` | 57.4 ns | 62.9 ns | 66.1 ns | 74.2 ns | 91.9 ns | 111 ns | 160 ns | 234 ns | 454 ns | 753 ns | 1.59 µs | 2.78 µs | 6.14 µs | 11 µs | 24.5 µs | 43.3 µs | 172 µs |
| `sqr` | 59 ns | 63.4 ns | 66.6 ns | 73.8 ns | 83.7 ns | 101 ns | 140 ns | 194 ns | 321 ns | 493 ns | 986 ns | 1.71 µs | 3.77 µs | 6.7 µs | 15.2 µs | 27.4 µs | 111 µs |
| `kara` | 95.5 ns | 98.8 ns | 102 ns | 108 ns | 121 ns | 142 ns | 200 ns | 270 ns | 490 ns | 790 ns | 1.63 µs | 2.57 µs | 5.19 µs | 8.03 µs | 16.1 µs | 24.9 µs | 76.5 µs |
| `ksqr` | 78.3 ns | 80.5 ns | 83.9 ns | 89.9 ns | 103 ns | 120 ns | 158 ns | 210 ns | 337 ns | 510 ns | 1.01 µs | 1.72 µs | 3.26 µs | 5.44 µs | 10.1 µs | 16.8 µs | 51.5 µs |
| `mulref` | 32.8 ns | 43.2 ns | 57.6 ns | 76.2 ns | 127 ns | 206 ns | 396 ns | 660 ns | 1.39 µs | 2.57 µs | 5.55 µs | 9.65 µs | 21.2 µs | 37.1 µs | 82.9 µs | 146 µs | 581 µs |

### Large sizes

The tables above stop at 512 limbs, below the reach of `mulToom`. These are from
`bench kara toom kara2 toom2 512 768 1024 1536 2048 4096`, the fastest of three runs, on
2026-11-08 (`b0a1b55`). The sizes are those of the larger operand.

| op | 512 | 768 | 1024 | 1536 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `kara` | 76.7 µs (2.56) | 151 µs (2.87) | 233 µs (3.06) | 457 µs (3.22) | 707 µs (3.30) | 2.14 ms (4.15) |
| `toom` | 75.3 µs (2.50) | 136 µs (2.58) | 207 µs (2.72) | 366 µs (2.60) | 544 µs (2.54) | 1.46 ms (2.85) |
| `kara2` | 87.1 µs (4.27) | 194 µs (5.43) | 345 µs (6.15) | 773 µs (7.58) | 1.38 ms (9.08) | 5.59 ms (14.91) |
| `toom2` | 54.2 µs (2.64) | 99.3 µs (2.77) | 157 µs (2.80) | 295 µs (2.89) | 447 µs (2.94) | 1.2 ms (3.55) |

The ratio to `Nat` is in parentheses. `mulKaratsuba` splits both operands at half the larger
one, which needs the smaller one to be longer than that half, so on `n` by `n / 2` limbs it is
`mulBasecase`, and its ratio grows with the size. Toom-3 by 2 and Toom-4 by 2 keep it near 3. At
512 by 256 limbs `toom2` is still `mulKaratsuba`, so still `mulBasecase`.

### Large sizes, multiplication

From `bench toom fft auto toom2 fft2 mulmod 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-11-08 (`b0a1b55`). `mulmod` is the product
modulo `β^n - 1` of two operands of `n` limbs, against the whole product on the `Nat` side.

| op | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `toom` | 207 µs (2.72) | 544 µs (2.54) | 971 µs (2.69) | 1.46 ms (2.85) | 3.75 ms (2.84) | 9.48 ms (3.43) | 24.5 ms (3.76) | 61.1 ms (4.53) |
| `fft` | 542 µs (7.12) | 824 µs (3.89) | 1.19 ms (3.56) | 1.77 ms (3.92) | 3.3 ms (3.03) | 7.41 ms (3.32) | 16.1 ms (2.99) | 36 ms (2.90) |
| `auto` | 205 µs (2.69) | 543 µs (2.54) | 971 µs (2.90) | 1.46 ms (3.21) | 3.31 ms (3.04) | 7.41 ms (3.31) | 16.1 ms (2.99) | 36 ms (2.67) |
| `toom2` | 157 µs (2.80) | 447 µs (2.94) | 799 µs (3.21) | 1.2 ms (3.55) | 3.27 ms (4.23) | 8.55 ms (4.97) | 21.6 ms (5.50) | 55.9 ms (5.72) |
| `fft2` | 309 µs (5.49) | 675 µs (4.41) | 898 µs (3.59) | 1.19 ms (3.54) | 2.52 ms (3.26) | 5.36 ms (3.12) | 11.7 ms (2.96) | 27.6 ms (2.82) |
| `mulmod` | 230 µs (3.00) | 511 µs (2.38) | 633 µs (1.88) | 779 µs (1.71) | 1.74 ms (1.60) | 3.32 ms (1.48) | 7.44 ms (1.38) | 16.2 ms (1.30) |

### Unbalanced products

`MPN.mul`, ratio to `Nat` only, the fastest of three runs, on 2026-11-08 (`b0a1b55`): `auto2`,
`auto4`, `auto8` for `n` by `n / 2`, `n / 4`, `n / 8` limbs, and `autobS` for `n` by `S` limbs.

| n | `auto` | `auto2` | `auto4` | `auto8` | `b64` | `b128` | `b256` | `b320` | `b512` | `b1024` | `b2048` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 2.12 | 2.26 | 2.08 | 1.51 |  |  |  |  |  |  |  |
| 512 | 2.50 | 2.46 | 2.31 | 2.11 |  |  |  |  |  |  |  |
| 1024 | 2.69 | 2.70 | 2.49 | 2.30 | 2.11 | 2.30 | 2.49 | 2.58 | 2.69 | 2.73 | 2.73 |
| 2048 | 2.51 | 2.74 | 2.71 | 2.49 |  |  |  |  |  |  |  |
| 3072 | 2.66 | 2.94 | 2.65 | 2.72 |  |  |  |  |  |  |  |
| 4096 | 2.83 | 3.24 | 3.11 | 2.71 | 2.10 | 2.30 | 2.48 | 2.57 | 2.71 | 3.12 | 3.26 |
| 6144 | 2.80 | 3.54 | 4.13 | 2.60 |  |  |  |  |  |  |  |
| 8192 | 2.57 | 3.29 | 3.50 | 2.85 |  |  |  |  |  |  |  |
| 16384 | 2.63 | 3.16 | 3.23 | 2.95 | 2.09 | 2.31 | 2.46 | 2.59 | 2.71 | 2.89 | 2.97 |
| 32768 | 2.47 | 2.98 | 3.06 | 2.79 |  |  |  |  |  |  |  |
| 65536 | 2.67 | 2.81 | 2.87 | 2.97 | 2.08 | 2.30 | 2.46 | 2.59 | 2.71 | 2.89 | 3.28 |

Before the split, the products whose smaller operand was below the Toom shapes went to the
schoolbook method: 5–6 times `Nat` at `n` by 256 or 320 limbs, 10.8 at 1536 by 384. The cell
left above 4, 6144 by 1536 (4.13), is where the FFT and the Toom methods tie.

### Large sizes, division

From `bench sbdiv div sqrt 512 1024 2048 4096 8192 16384`, the fastest of three runs, on
2026-11-08 (`b0a1b55`). The sizes are those of the divisor (`div`, `sbdiv`:
`2 n` by `n` limbs) or of the operand (`sqrt`).

| op | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
|---|---:|---:|---:|---:|---:|---:|
| `sbdiv` | 156 µs (3.02) | 605 µs (3.95) | 2.39 ms (5.97) | 9.96 ms (9.40) | 37.7 ms (16.04) | 151 ms (26.49) |
| `div` | 151 µs (2.93) | 465 µs (3.06) | 1.37 ms (3.51) | 3.62 ms (3.66) | 7.87 ms (3.61) | 16.6 ms (2.91) |
| `sqrt` | 51.4 µs (0.23) | 154 µs (0.18) | 463 µs (0.19) | 1.37 ms (0.20) | 3.85 ms (0.23) | 10.1 ms (0.24) |

The ratio to `Nat` is in parentheses; for `sqrt` it is to Lean's `Nat.sqrt`, not to GMP. `div`
is divide and conquer up to `divQMu = 4096` divisor limbs, whose `O(M(n) log n)` makes its ratio
grow with the size, and from there Barrett's division by the reciprocal of the top half of the
divisor, as GMP's, which brings it back to 2.9 at 16384 limbs.

### Large sizes, gcd and decimal strings

From `bench gcd str parse 512 1024 2048 4096 8192`, the fastest of three runs, on 2026-11-08
(`b0a1b55`). `str` and `parse` compare with Lean's `Nat.repr` and `String.toNat?`, which are
written in Lean, not with GMP's `mpz_get_str` and `mpz_set_str`; `gcd` compares with `Nat.gcd`,
GMP's `mpz_gcd`.

| op | 512 | 1024 | 2048 | 4096 | 8192 |
|---|---:|---:|---:|---:|---:|
| `gcd` | 609 µs (1.51) | 1.96 ms (1.51) | 6.53 ms (1.82) | 19.3 ms (2.04) | 54.8 ms (2.24) |
| `str` | 283 µs (0.01) | 792 µs (0.01) | 2.22 ms (0.01) | 6.16 ms (0.01) | 16.8 ms (0.00) |
| `parse` | 212 µs (0.04) | 628 µs (0.04) | 1.91 ms (0.03) | 4.62 ms (0.02) | 11.2 ms (0.01) |

`gcd` is Lehmer's algorithm with steps of about 62 bits, like GMP's: two runs of Euclid's steps on
the leading words, the second on the leading 128 bits after the first (`cofactors2`), applied by
`mulSubMul` in one pass for each number; and from `gcdHalf = 1536` limbs half-gcd of the top
third of the limbs, as GMP's `mpn_gcd`, whose base case up to `hgcdBase = 128` limbs is the same
steps with the matrix updated in one pass per entry (`mulAddMul`); above the base case it runs on
the generic layer. At 16384 limbs `gcd` takes 151 ms, 2.51 times `Nat`. `gcdh<T>` sweeps `gcdHalf`.

### Large sizes, squares

From `bench ksqr toomsqr fftsqr autosqr 512 1024 2048 3072 4096 8192 16384 32768 65536`, the
fastest of three runs, on 2026-11-08 (`b0a1b55`).

| op | 512 | 1024 | 2048 | 3072 | 4096 | 8192 | 16384 | 32768 | 65536 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ksqr` | 52.8 µs (1.77) | 159 µs (2.09) | 484 µs (2.23) | 890 µs (2.45) | 1.47 ms (3.03) | 4.42 ms (3.43) | 13.3 ms (4.82) | 40.4 ms (6.80) | 121 ms (9.10) |
| `toomsqr` | 52.9 µs (1.78) | 151 µs (1.99) | 417 µs (1.98) | 692 µs (2.09) | 1.08 ms (2.40) | 2.81 ms (2.63) | 7.36 ms (3.33) | 18.3 ms (3.43) | 46.2 ms (3.45) |
| `fftsqr` | 173 µs (5.79) | 379 µs (5.00) | 556 µs (2.64) | 782 µs (2.36) | 1.19 ms (2.66) | 2.25 ms (2.08) | 5.08 ms (2.30) | 11.2 ms (2.09) | 25 ms (1.87) |
| `autosqr` | 52.4 µs (1.76) | 149 µs (1.96) | 416 µs (1.97) | 684 µs (2.07) | 1.08 ms (2.41) | 2.26 ms (2.11) | 5.12 ms (2.32) | 11.1 ms (2.08) | 25 ms (1.84) |

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
