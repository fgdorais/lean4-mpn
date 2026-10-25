# Benchmarks: `main32` and `main64`

The two libraries side by side, at the same sizes in bits, each against Lean's `Nat` (GMP). Each
branch has its own BENCH.md with its full tables and history; this file compares them.

## Summary

- **Products and squares** (`mul`, `sqr`, the whole dispatcher): `main64` is 2.0–2.5 times
  faster from 8 to 32 limbs of 64 bits, 1.4–1.8 from 64 limbs on. At 4096 limbs `main64` is 3.6
  times `Nat` and `main32` 5.4.
- **Division** `2n` by `n`: 1.5–2.7 times faster from 8 limbs, though `main64` computes the
  remainder as well; `main64` stays within 4.8 times `Nat`, `main32` reaches 8.2.
- **Greatest common divisor**: 1.2–2.8 times faster; `main64` 2.4–3.1 times `Nat` from 4 limbs,
  `main32` 3.3–6.8.
- **Square root**: `main32`'s Newton iteration is faster below 64 limbs, `main64`'s Zimmermann
  square root 1.5–3.4 times faster from 128 limbs (both against Lean's `Nat.sqrt`, not GMP).
- **Decimal strings**: 1.3–2.1 times faster from 16 limbs, both far ahead of Lean's `Nat.repr`
  and `String.toNat?`.
- **Linear passes** (`add`, `sub`, `mul1`, `shr`): within about 15% of each other below 32 limbs;
  from 64 limbs `main64` is 1.2–1.5 times faster on `add` and `mul1`, 1.0–1.5 on `sub` (noisy),
  level on `shr`.

## How to read the tables

- **Sizes** are in limbs of 64 bits: a column `k` is `64 k` bits, `k` limbs on `main64` and `2 k`
  limbs on `main32`.
- **The ratio to `Nat`** is the time of the library over the time of the same operation on `Nat`
  in the same benchmark process, so below 1 is faster than `Nat`.
- **The speed-up** is the ratio of `main32` over the ratio of `main64`: how many times faster
  `main64` is, each measured against `Nat` in its own process. The same `Nat` operation ran up to
  a third faster in `main32`'s binary than in `main64`'s below 64 limbs, which is where the code
  lands rather than either library, so a quotient of raw times would be off by that much.
  Below 64 limbs, read the speed-ups as ±20%.
- **One limb** (the column `1`) is not comparable: `main64` has one limb against `Nat`'s unboxed
  values below `2⁶³`, `main32` two limbs above them, and `main32`'s `gcd`, `sqrt`, `str` and
  `parse` go through `MPN.Nat`, whose word fast path covers that size.
- **The operations** are each branch's closest to one another:

| op | `main32` | `main64` | notes |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` | `MPN.add`, `MPN.sub` | `n` and `n` limbs, the result allocated |
| `mul1` | `mul1` | `MPN.mul1` | `n` limbs times a limb |
| `mul` | `mul` (`mulLimbs`) | `MPN.mul` (bench `auto`) | `n` by `n` limbs, all algorithms |
| `sqr` | `sqr` | `MPN.sqr` (bench `autosqr`) | `n` limbs |
| `shr` | `shiftRight` by 37 | `MPN.rshift` by 13 | `n` limbs |
| `div` | `div`, the quotient | `Num.divMod`, quotient and remainder | `2n` by `n` limbs |
| `gcd` | `MPN.Nat.gcd` (bench `bgcd`) | `Num.gcd` | `n` and `n` limbs |
| `sqrt` | `MPN.Nat.sqrt` (bench `bsqrt`) | `sqrtRem` | `n` limbs; `Nat` side: Lean's `Nat.sqrt` |
| `str` | `toString` (bench `btostr`) | `Num.toDecimal` | `Nat` side: Lean's `Nat.repr` |
| `parse` | `MPN.Nat.ofString?` (bench `bofstr`) | `Num.ofDecimal?` | `Nat` side: `String.toNat?` |

## Results

The fastest of three runs of each, on 2026-10-25: `main32` at `e8b34d7`, `main64` at `5b34dcf`,
lean4-scalar-arrays `49cf1b1`, Lean `v4.36.0-rc1`, AMD Ryzen 5 5600X (Zen 3), Linux 7.1, each
pinned to one core.

Ratio to `Nat`, `main32`:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.48 | 0.50 | 0.49 | 0.53 | 0.60 | 0.74 | 1.02 | 1.35 | 1.17 | 1.41 | 1.55 | 1.60 | 1.72 |
| `sub` | 0.54 | 0.52 | 0.54 | 0.51 | 0.59 | 0.74 | 0.78 | 1.34 | 1.16 | 1.51 | 1.55 | 1.66 | 1.53 |
| `mul1` | 0.29 | 0.29 | 0.28 | 0.32 | 0.37 | 0.49 | 0.67 | 0.99 | 1.03 | 1.21 | 1.33 | 1.37 | 1.46 |
| `mul` | 0.55 | 0.55 | 1.16 | 1.82 | 2.43 | 3.12 | 3.67 | 3.96 | 4.14 | 4.47 | 4.89 | 4.81 | 5.35 |
| `sqr` | 0.51 | 0.52 | 0.86 | 1.61 | 1.91 | 2.12 | 2.25 | 2.42 | 2.55 | 2.93 | 3.26 | 3.26 | 3.70 |
| `shr` | 0.90 | 0.47 | 0.48 | 0.50 | 0.51 | 0.57 | 0.66 | 0.91 | 0.78 | 1.04 | 1.15 | 1.20 | 1.29 |
| `div` | 1.85 | 2.38 | 2.73 | 3.43 | 4.77 | 6.47 | 8.21 | 7.62 | 6.67 | 6.46 | 6.29 | 7.00 | 7.52 |
| `gcd` | 1.60 | 4.08 | 3.48 | 3.34 | 3.43 | 3.61 | 3.90 | 4.38 | 4.62 | 4.08 | 4.50 | 6.16 | 6.80 |
| `sqrt` | 1.06 | 0.35 | 0.83 | 1.56 | 2.09 | 1.61 | 2.01 | 1.37 | 1.19 | 0.93 | 0.81 | 0.79 | 0.73 |
| `str` | 0.84 | 0.06 | 0.05 | 0.05 | 0.05 | 0.06 | 0.06 | 0.05 | 0.04 | 0.03 | 0.02 | 0.02 | 0.01 |
| `parse` | 0.98 | 0.18 | 0.11 | 0.09 | 0.09 | 0.08 | 0.08 | 0.09 | 0.09 | 0.10 | 0.08 | 0.05 | 0.04 |

Ratio to `Nat`, `main64`:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 0.44 | 0.56 | 0.56 | 0.58 | 0.62 | 0.70 | 0.80 | 1.00 | 0.99 | 1.11 | 1.17 | 1.12 | 1.27 |
| `sub` | 0.53 | 0.46 | 0.47 | 0.51 | 0.53 | 0.55 | 0.69 | 0.92 | 1.14 | 1.29 | 1.42 | 1.47 | 1.51 |
| `mul1` | 0.25 | 0.31 | 0.32 | 0.34 | 0.37 | 0.40 | 0.49 | 0.66 | 0.69 | 0.78 | 0.88 | 0.90 | 0.95 |
| `mul` | 0.43 | 0.49 | 0.61 | 0.76 | 1.06 | 1.56 | 2.08 | 2.39 | 2.60 | 2.98 | 3.31 | 3.23 | 3.57 |
| `sqr` | 0.34 | 0.48 | 0.58 | 0.71 | 0.77 | 0.95 | 1.26 | 1.49 | 1.62 | 1.98 | 2.19 | 2.29 | 2.43 |
| `shr` | 3.57 | 0.44 | 0.45 | 0.47 | 0.51 | 0.56 | 0.66 | 0.85 | 0.78 | 0.99 | 1.17 | 1.21 | 1.26 |
| `div` | 1.08 | 2.34 | 2.23 | 2.36 | 2.45 | 2.71 | 3.01 | 3.33 | 3.44 | 3.91 | 4.03 | 4.56 | 4.79 |
| `gcd` | 0.89 | 1.48 | 2.38 | 2.74 | 2.67 | 2.73 | 2.83 | 2.97 | 3.00 | 2.44 | 2.58 | 2.87 | 3.13 |
| `sqrt` | 5.30 | 0.42 | 1.29 | 1.94 | 2.65 | 2.06 | 1.66 | 0.92 | 0.42 | 0.32 | 0.24 | 0.24 | 0.26 |
| `str` | 3.03 | 0.06 | 0.04 | 0.04 | 0.04 | 0.04 | 0.05 | 0.04 | 0.03 | 0.02 | 0.01 | 0.01 | 0.01 |
| `parse` | 1.03 | 0.14 | 0.08 | 0.07 | 0.06 | 0.05 | 0.05 | 0.05 | 0.04 | 0.07 | 0.05 | 0.04 | 0.03 |

Speed-up of `main64` over `main32` (ratio of `main32` / ratio of `main64`):

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 1.08 | 0.90 | 0.87 | 0.91 | 0.95 | 1.07 | 1.28 | 1.35 | 1.18 | 1.27 | 1.33 | 1.43 | 1.36 |
| `sub` | 1.02 | 1.14 | 1.14 | 1.00 | 1.13 | 1.34 | 1.13 | 1.45 | 1.02 | 1.17 | 1.09 | 1.13 | 1.01 |
| `mul1` | 1.13 | 0.94 | 0.90 | 0.94 | 1.01 | 1.21 | 1.36 | 1.50 | 1.49 | 1.55 | 1.52 | 1.53 | 1.53 |
| `mul` | 1.27 | 1.13 | 1.90 | 2.40 | 2.29 | 2.01 | 1.76 | 1.65 | 1.59 | 1.50 | 1.48 | 1.49 | 1.50 |
| `sqr` | 1.50 | 1.09 | 1.49 | 2.26 | 2.48 | 2.24 | 1.79 | 1.63 | 1.57 | 1.48 | 1.49 | 1.42 | 1.52 |
| `shr` | 0.25 | 1.08 | 1.07 | 1.04 | 1.00 | 1.02 | 1.01 | 1.08 | 1.00 | 1.04 | 0.98 | 1.00 | 1.02 |
| `div` | 1.71 | 1.02 | 1.23 | 1.45 | 1.94 | 2.39 | 2.73 | 2.29 | 1.94 | 1.65 | 1.56 | 1.54 | 1.57 |
| `gcd` | 1.79 | 2.76 | 1.46 | 1.22 | 1.28 | 1.32 | 1.38 | 1.47 | 1.54 | 1.67 | 1.75 | 2.14 | 2.17 |
| `sqrt` | 0.20 | 0.83 | 0.65 | 0.80 | 0.79 | 0.78 | 1.21 | 1.48 | 2.81 | 2.92 | 3.44 | 3.32 | 2.87 |
| `str` | 0.28 | 1.02 | 1.11 | 1.02 | 1.28 | 1.37 | 1.27 | 1.45 | 1.54 | 1.60 | 1.56 | 1.54 | 1.52 |
| `parse` | 0.95 | 1.29 | 1.35 | 1.39 | 1.46 | 1.54 | 1.64 | 1.82 | 2.13 | 1.33 | 1.37 | 1.36 | 1.39 |

## Running

On each branch, build the benchmark (`lake build bench`) and run, from its checkout:

```sh
# main32: k limbs of 64 bits are 2 k limbs of 32 bits; bsqrt's operand is already 2 n limbs
for i in 1 2 3; do
  taskset -c 2 .lake/build/bin/bench add sub mul1 mul sqr shr div bgcd btostr bofstr \
    2 4 8 16 32 64 128 256 512 1024 2048 4096 8192
  taskset -c 2 .lake/build/bin/bench bsqrt 1 2 4 8 16 32 64 128 256 512 1024 2048 4096
done > main32.txt
# main64
for i in 1 2 3; do
  taskset -c 2 .lake/build/bin/bench add sub mul1 auto autosqr shr div gcd str parse sqrt \
    1 2 4 8 16 32 64 128 256 512 1024 2048 4096
done > main64.txt
```

then, on `main`, with the two files in `bench/`:

```sh
scripts/compare_md.py bench/main32.txt bench/main64.txt   # the tables above
```

The raw outputs of the runs above are [bench/main32.txt](bench/main32.txt) and
[bench/main64.txt](bench/main64.txt).
