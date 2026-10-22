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
  `85c955d`. 2026-10-22, with the `USize` add/sub (history below).

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1`, on `USlice`s with `USize` indices |
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1` |
| `comba` | `MPN.mulComba` | `n` by `n` limbs | schoolbook by columns into a three-word accumulator |
| `mulref` | `Bench.refMul` | `n` by `n` limbs | schoolbook by rows, a hand-written loop with the arithmetic of `addMul1`; not part of the library, the target for its loops |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 128 | 256 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.42 | 0.53 | 0.48 | 0.54 | 0.58 | 0.58 | 0.61 | 0.66 | 0.71 | 0.75 | 0.84 | 0.95 | 1.21 | 1.21 |
| `sub` | 0.52 | 0.46 | 0.53 | 0.48 | 0.52 | 0.52 | 0.56 | 0.58 | 0.59 | 0.65 | 0.72 | 0.82 | 1.16 | 1.31 |
| `mul1` | 0.27 | 0.34 | 0.32 | 0.37 | 0.43 | 0.46 | 0.56 | 0.65 | 0.84 | 0.97 | 1.24 | 1.48 | 2.25 | 2.74 |
| `addmul1` | 0.19 | 0.22 | 0.22 | 0.23 | 0.27 | 0.33 | 0.38 | 0.42 | 0.57 | 0.65 | 0.86 | 0.98 | 1.47 | 1.71 |
| `mul` | 0.45 | 0.70 | 1.06 | 1.45 | 2.18 | 3.02 | 4.39 | 5.40 | 7.60 | 9.17 | 10.97 | 12.64 | 16.77 | 22.56 |
| `comba` | 0.82 | 1.42 | 2.15 | 2.71 | 3.84 | 4.79 | 6.44 | 7.47 | 9.03 | 9.79 | 10.62 | 11.21 | 13.24 | 16.50 |
| `mulref` | 0.23 | 0.33 | 0.51 | 0.69 | 1.19 | 1.70 | 2.68 | 3.53 | 5.01 | 6.65 | 8.17 | 9.43 | 12.84 | 17.44 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 128 | 256 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 59.5 ns | 61.7 ns | 64 ns | 64.2 ns | 69.7 ns | 69.3 ns | 73.8 ns | 79.9 ns | 87.6 ns | 97.1 ns | 113 ns | 137 ns | 208 ns | 345 ns |
| `sub` | 62.1 ns | 63.3 ns | 64.1 ns | 65.7 ns | 71.9 ns | 71.1 ns | 76.8 ns | 82.4 ns | 92.8 ns | 106 ns | 124 ns | 147 ns | 229 ns | 388 ns |
| `mul1` | 47.4 ns | 51.9 ns | 54.3 ns | 57.6 ns | 66.1 ns | 70.7 ns | 87.1 ns | 102 ns | 135 ns | 163 ns | 222 ns | 280 ns | 517 ns | 980 ns |
| `addmul1` | 44.3 ns | 49.9 ns | 52.4 ns | 54.7 ns | 62.9 ns | 70.2 ns | 88 ns | 104 ns | 143 ns | 177 ns | 241 ns | 306 ns | 562 ns | 1.07 µs |
| `mul` | 63.8 ns | 93.9 ns | 133 ns | 188 ns | 305 ns | 465 ns | 847 ns | 1.35 µs | 2.88 µs | 4.89 µs | 10.2 µs | 17.7 µs | 67.6 µs | 264 µs |
| `comba` | 117 ns | 192 ns | 271 ns | 352 ns | 538 ns | 747 ns | 1.25 µs | 1.86 µs | 3.43 µs | 5.23 µs | 9.86 µs | 15.8 µs | 53.1 µs | 193 µs |
| `mulref` | 33.5 ns | 44.5 ns | 65.4 ns | 89.6 ns | 167 ns | 262 ns | 523 ns | 883 ns | 1.9 µs | 3.54 µs | 7.6 µs | 13.3 µs | 51.6 µs | 204 µs |

## History

Times are the fastest of five runs, in the format of the tables above.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-22 | `5c419ae` | baseline: verified `add`/`sub`, `mul1`/`addMul1`, `mulBasecase` and `mulComba` on `UInt64` limbs, plain `Nat`-indexed loops | `mul` 184 ns at 4 limbs, 1.34 µs at 16, 17.7 µs at 64; `comba` 372 ns, 1.94 µs, 16.0 µs; `mulref` 92.2 ns, 887 ns, 13.2 µs |
| 2026-10-22 | `b13f8e6`+ | `add`/`sub` on `USlice`: `USize` indices, `uget`/`uset` without bounds checks; Lean `v4.36.0-rc1` (other rows within ±4%) | `add` 86.4 → 65.5 ns at 4 limbs, 130 → 80.2 ns at 16, 312 → 138 ns at 64, 1.01 µs → 346 ns at 256; `sub` likewise (−20%, −35%, −54%, −63%) |
