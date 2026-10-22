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
  `85c955d`. 2026-10-22, with `USize` multiplication (history below).

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1`, on `USlice`s with `USize` indices |
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass, `USize` indices |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass, `USize` indices |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1`, `USize` indices |
| `comba` | `MPN.mulComba` | `n` by `n` limbs | schoolbook by columns into a three-word accumulator, `USize` indices |
| `mulref` | `Bench.refMul` | `n` by `n` limbs | schoolbook by rows, a hand-written loop with `Nat` indices and the arithmetic of `addMul1`; not part of the library, kept as a control since its code does not change |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 128 | 256 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.44 | 0.52 | 0.46 | 0.54 | 0.58 | 0.58 | 0.62 | 0.65 | 0.72 | 0.76 | 0.85 | 0.94 | 1.21 | 1.26 |
| `sub` | 0.52 | 0.46 | 0.52 | 0.47 | 0.51 | 0.51 | 0.56 | 0.53 | 0.58 | 0.62 | 0.71 | 0.84 | 1.11 | 1.30 |
| `mul1` | 0.26 | 0.29 | 0.26 | 0.30 | 0.32 | 0.33 | 0.36 | 0.38 | 0.42 | 0.46 | 0.52 | 0.61 | 0.78 | 0.87 |
| `addmul1` | 0.20 | 0.20 | 0.19 | 0.20 | 0.22 | 0.24 | 0.24 | 0.24 | 0.28 | 0.31 | 0.36 | 0.43 | 0.55 | 0.59 |
| `mul` | 0.45 | 0.57 | 0.79 | 0.92 | 1.29 | 1.58 | 1.92 | 2.20 | 2.75 | 3.07 | 3.56 | 4.12 | 5.14 | 6.72 |
| `comba` | 0.78 | 1.26 | 1.85 | 2.29 | 3.08 | 3.72 | 4.60 | 5.04 | 5.39 | 5.21 | 5.11 | 5.11 | 4.88 | 5.21 |
| `mulref` | 0.22 | 0.32 | 0.51 | 0.68 | 1.19 | 1.70 | 2.72 | 3.55 | 5.05 | 6.63 | 8.18 | 9.50 | 12.77 | 17.44 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 128 | 256 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 60.6 ns | 62.3 ns | 64.3 ns | 65.8 ns | 69.8 ns | 69.6 ns | 74.4 ns | 78.9 ns | 88.9 ns | 96.8 ns | 114 ns | 135 ns | 208 ns | 344 ns |
| `sub` | 62.1 ns | 63.8 ns | 66 ns | 65.8 ns | 71.8 ns | 72.1 ns | 78.8 ns | 83.6 ns | 92.9 ns | 104 ns | 124 ns | 151 ns | 233 ns | 393 ns |
| `mul1` | 44.9 ns | 45.1 ns | 46.3 ns | 47.5 ns | 49.7 ns | 51.8 ns | 55.7 ns | 59.3 ns | 68.8 ns | 76.9 ns | 92 ns | 115 ns | 181 ns | 311 ns |
| `addmul1` | 45.2 ns | 46.4 ns | 46 ns | 47.4 ns | 50 ns | 51.4 ns | 56 ns | 61.6 ns | 71.2 ns | 81.1 ns | 101 ns | 127 ns | 208 ns | 369 ns |
| `mul` | 63.2 ns | 77.5 ns | 99.9 ns | 120 ns | 180 ns | 243 ns | 375 ns | 549 ns | 1.03 µs | 1.64 µs | 3.3 µs | 5.77 µs | 20.7 µs | 78.6 µs |
| `comba` | 111 ns | 172 ns | 235 ns | 298 ns | 431 ns | 573 ns | 887 ns | 1.26 µs | 2.02 µs | 2.79 µs | 4.75 µs | 7.16 µs | 19.7 µs | 60.9 µs |
| `mulref` | 31.6 ns | 43.5 ns | 64.6 ns | 88.3 ns | 167 ns | 262 ns | 524 ns | 883 ns | 1.9 µs | 3.54 µs | 7.6 µs | 13.3 µs | 51.6 µs | 204 µs |

## History

Times are the fastest of five runs, in the format of the tables above.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-22 | `5c419ae` | baseline: verified `add`/`sub`, `mul1`/`addMul1`, `mulBasecase` and `mulComba` on `UInt64` limbs, plain `Nat`-indexed loops | `mul` 184 ns at 4 limbs, 1.34 µs at 16, 17.7 µs at 64; `comba` 372 ns, 1.94 µs, 16.0 µs; `mulref` 92.2 ns, 887 ns, 13.2 µs |
| 2026-10-22 | `b13f8e6`+ | `add`/`sub` on `USlice`: `USize` indices, `uget`/`uset` without bounds checks; Lean `v4.36.0-rc1` (other rows within ±4%) | `add` 86.4 → 65.5 ns at 4 limbs, 130 → 80.2 ns at 16, 312 → 138 ns at 64, 1.01 µs → 346 ns at 256; `sub` likewise (−20%, −35%, −54%, −63%) |
| 2026-10-22 | `6c5e6dc`+ | `mul1`, `addMul1`, `mulBasecase` and `mulComba` on `USlice` with `USize` indices (`mulref` unchanged, ±1%) | `mul` 188 → 121 ns at 4 limbs, 1.35 µs → 551 ns at 16, 17.7 → 5.77 µs at 64, 264 → 79.1 µs at 256; `comba` 352 → 304 ns, 1.86 → 1.27 µs, 15.8 → 7.16 µs, 193 → 61.5 µs; `mul1`/`addmul1` −12–16% at 4 limbs, −58–68% from 64 |
