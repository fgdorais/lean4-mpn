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
  `85c955d`. 2026-10-22, with one exclusivity check per loop (history below).

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1`, on `USlice`s with `USize` indices |
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass, `USize` indices |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass, `USize` indices |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1` with a continuation, `USize` indices |
| `kara` | `MPN.mulKaratsuba` | `n` by `n` limbs | Karatsuba from 64 limbs (`karatsubaThreshold`), `mulBasecase` below |
| `comba` | `MPN.mulComba` | `n` by `n` limbs | schoolbook by columns into a three-word accumulator, `USize` indices |
| `mulref` | `Bench.refMul` | `n` by `n` limbs | schoolbook by rows, a hand-written loop with `Nat` indices and the arithmetic of `addMul1`; not part of the library, kept as a control since its code does not change |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.44 | 0.53 | 0.49 | 0.53 | 0.56 | 0.56 | 0.59 | 0.61 | 0.67 | 0.69 | 0.75 | 0.80 | 0.89 | 1.00 | 0.95 | 0.97 | 1.16 |
| `sub` | 0.53 | 0.46 | 0.52 | 0.46 | 0.50 | 0.50 | 0.55 | 0.54 | 0.54 | 0.58 | 0.69 | 0.71 | 0.86 | 0.96 | 1.01 | 1.05 | 1.29 |
| `mul1` | 0.27 | 0.30 | 0.28 | 0.31 | 0.32 | 0.32 | 0.34 | 0.34 | 0.38 | 0.41 | 0.45 | 0.49 | 0.56 | 0.66 | 0.59 | 0.66 | 0.79 |
| `addmul1` | 0.19 | 0.20 | 0.19 | 0.20 | 0.20 | 0.23 | 0.23 | 0.23 | 0.24 | 0.26 | 0.27 | 0.31 | 0.38 | 0.44 | 0.47 | 0.45 | 0.53 |
| `mul` | 0.38 | 0.41 | 0.51 | 0.52 | 0.59 | 0.69 | 0.89 | 1.00 | 1.32 | 1.56 | 1.95 | 2.48 | 2.80 | 3.42 | 4.24 | 4.80 | 7.47 |
| `comba` | 0.74 | 1.22 | 1.82 | 2.26 | 3.08 | 3.73 | 4.80 | 4.84 | 5.42 | 5.41 | 5.11 | 5.16 | 4.81 | 4.93 | 5.14 | 5.21 | 6.97 |
| `kara` | 0.42 | 0.44 | 0.54 | 0.55 | 0.62 | 0.70 | 0.91 | 1.03 | 1.32 | 1.54 | 1.96 | 2.12 | 2.29 | 2.40 | 2.60 | 2.62 | 3.15 |
| `mulref` | 0.22 | 0.31 | 0.49 | 0.66 | 1.15 | 1.63 | 2.65 | 3.46 | 5.00 | 6.54 | 8.14 | 9.43 | 10.93 | 12.77 | 15.39 | 17.29 | 27.00 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 62 ns | 64.4 ns | 66.7 ns | 66 ns | 69.3 ns | 69.4 ns | 73.6 ns | 76.7 ns | 85.1 ns | 89.3 ns | 104 ns | 116 ns | 144 ns | 174 ns | 227 ns | 274 ns | 485 ns |
| `sub` | 63.1 ns | 65 ns | 64.7 ns | 65.3 ns | 69.8 ns | 69.1 ns | 77.6 ns | 80.4 ns | 88.4 ns | 96.6 ns | 112 ns | 128 ns | 160 ns | 196 ns | 264 ns | 322 ns | 583 ns |
| `mul1` | 47.1 ns | 47.9 ns | 48.8 ns | 49.4 ns | 51 ns | 51.6 ns | 54.7 ns | 57.2 ns | 65 ns | 71.2 ns | 84 ns | 95.2 ns | 120 ns | 156 ns | 202 ns | 255 ns | 454 ns |
| `addmul1` | 44.8 ns | 45 ns | 45.9 ns | 47.2 ns | 48 ns | 49.7 ns | 53.1 ns | 56.9 ns | 63.9 ns | 71 ns | 85 ns | 101 ns | 137 ns | 167 ns | 231 ns | 292 ns | 523 ns |
| `mul` | 56.3 ns | 57.5 ns | 65.7 ns | 69.6 ns | 85.8 ns | 110 ns | 175 ns | 258 ns | 500 ns | 841 ns | 1.83 µs | 3.49 µs | 7.48 µs | 13.8 µs | 31.7 µs | 56.2 µs | 224 µs |
| `comba` | 109 ns | 175 ns | 239 ns | 305 ns | 449 ns | 600 ns | 946 ns | 1.25 µs | 2.06 µs | 2.94 µs | 4.79 µs | 7.27 µs | 12.9 µs | 19.8 µs | 38.4 µs | 61.5 µs | 209 µs |
| `kara` | 61.8 ns | 62.8 ns | 70.1 ns | 74.1 ns | 89.5 ns | 112 ns | 180 ns | 264 ns | 503 ns | 838 ns | 1.84 µs | 2.99 µs | 6.13 µs | 9.73 µs | 19.4 µs | 30.7 µs | 94.4 µs |
| `mulref` | 32.8 ns | 43.7 ns | 64.6 ns | 88.8 ns | 167 ns | 261 ns | 523 ns | 885 ns | 1.9 µs | 3.54 µs | 7.6 µs | 13.3 µs | 29.3 µs | 51.7 µs | 115 µs | 204 µs | 810 µs |

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
