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
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass, `USize` indices |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass, `USize` indices |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1` with a continuation, `USize` indices |
| `kara` | `MPN.mulKaratsuba` | `n` by `n` limbs | Karatsuba from 64 limbs (`karatsubaThreshold`), `mulBasecase` below |
| `toom` | `MPN.mulToom` | `n` by `n` limbs | Toom-3 from 384 limbs (`toom3Threshold`), `mulKaratsuba` below |
| `kara2` | `MPN.mulKaratsuba` | `n` by `n / 2` limbs | as `kara` |
| `toom2` | `MPN.mulToom` | `n` by `n / 2` limbs | Toom-3 by 2 or Toom-4 by 2 from 384 limbs in the smaller operand, `mulKaratsuba` below |
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
