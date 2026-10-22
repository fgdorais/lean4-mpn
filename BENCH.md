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
- **Machine:** AMD Ryzen 5 5600X (Zen 3), Linux 7.1, Lean `v4.35.0`, lean4-scalar-arrays
  `3addfc4`. Commit `5c419ae`, 2026-10-22.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs (`sub`: `n + 1` and `n`) | `addN`/`subN`, then `add1`/`sub1` |
| `mul1` | `MPN.mul1` | `n` limbs times a limb | one pass |
| `addmul1` | `MPN.addMul1` | `n` limbs times a limb, added to `n` limbs | one pass |
| `mul` | `MPN.mulBasecase` | `n` by `n` limbs | schoolbook by rows: `mul1`, then `addMul1` |
| `comba` | `MPN.mulComba` | `n` by `n` limbs | schoolbook by columns into a three-word accumulator |
| `mulref` | `Bench.refMul` | `n` by `n` limbs | schoolbook by rows, a hand-written loop with the arithmetic of `addMul1`; not part of the library, the target for its loops |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 128 | 256 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.51 | 0.67 | 0.59 | 0.71 | 0.77 | 0.83 | 0.95 | 1.06 | 1.33 | 1.49 | 1.86 | 2.17 | 3.13 | 3.29 |
| `sub` | 0.63 | 0.57 | 0.64 | 0.62 | 0.68 | 0.72 | 0.83 | 0.87 | 1.04 | 1.29 | 1.60 | 1.95 | 2.78 | 3.30 |
| `mul1` | 0.27 | 0.32 | 0.31 | 0.35 | 0.41 | 0.45 | 0.53 | 0.62 | 0.81 | 0.95 | 1.23 | 1.46 | 2.22 | 2.46 |
| `addmul1` | 0.21 | 0.22 | 0.22 | 0.24 | 0.28 | 0.35 | 0.37 | 0.41 | 0.56 | 0.65 | 0.85 | 1.01 | 1.49 | 1.73 |
| `mul` | 0.44 | 0.71 | 1.05 | 1.40 | 2.11 | 2.86 | 4.26 | 5.28 | 7.65 | 9.00 | 11.04 | 12.55 | 16.56 | 22.37 |
| `comba` | 0.82 | 1.46 | 2.17 | 2.84 | 3.87 | 4.90 | 6.49 | 7.67 | 9.13 | 9.80 | 10.70 | 11.35 | 13.19 | 16.41 |
| `mulref` | 0.25 | 0.34 | 0.54 | 0.70 | 1.22 | 1.72 | 2.70 | 3.49 | 5.00 | 6.56 | 8.14 | 9.36 | 12.78 | 17.35 |

Time of MPN:

| op | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 128 | 256 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 74.9 ns | 79.8 ns | 83.9 ns | 86.4 ns | 92.9 ns | 101 ns | 115 ns | 130 ns | 165 ns | 194 ns | 253 ns | 312 ns | 545 ns | 1.01 µs |
| `sub` | 76.3 ns | 79.5 ns | 82.3 ns | 84.5 ns | 94.9 ns | 99.4 ns | 115 ns | 132 ns | 168 ns | 198 ns | 262 ns | 325 ns | 570 ns | 1.06 µs |
| `mul1` | 47.9 ns | 50.5 ns | 54.1 ns | 55.7 ns | 63.7 ns | 71.2 ns | 84.3 ns | 99.9 ns | 134 ns | 163 ns | 222 ns | 279 ns | 516 ns | 978 ns |
| `addmul1` | 47.6 ns | 51.2 ns | 54.5 ns | 58.4 ns | 65.4 ns | 74.2 ns | 89.5 ns | 105 ns | 145 ns | 177 ns | 242 ns | 308 ns | 563 ns | 1.07 µs |
| `mul` | 65.5 ns | 96.8 ns | 133 ns | 184 ns | 299 ns | 446 ns | 831 ns | 1.34 µs | 2.89 µs | 4.84 µs | 10.3 µs | 17.7 µs | 67.4 µs | 264 µs |
| `comba` | 122 ns | 200 ns | 276 ns | 372 ns | 546 ns | 759 ns | 1.26 µs | 1.94 µs | 3.45 µs | 5.27 µs | 9.96 µs | 16 µs | 53.3 µs | 192 µs |
| `mulref` | 36.7 ns | 46.3 ns | 68.8 ns | 92.2 ns | 172 ns | 267 ns | 526 ns | 887 ns | 1.9 µs | 3.54 µs | 7.58 µs | 13.2 µs | 51.5 µs | 203 µs |

## History

Times are the fastest of five runs, in the format of the tables above.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-22 | `5c419ae` | baseline: verified `add`/`sub`, `mul1`/`addMul1`, `mulBasecase` and `mulComba` on `UInt64` limbs, plain `Nat`-indexed loops | `mul` 184 ns at 4 limbs, 1.34 µs at 16, 17.7 µs at 64; `comba` 372 ns, 1.94 µs, 16.0 µs; `mulref` 92.2 ns, 887 ns, 13.2 µs |
