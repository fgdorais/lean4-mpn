# Benchmarks

This file tracks the performance of the library against Lean's `Nat`, which is backed by GMP. The
tables come from `lake exe bench` and are regenerated after each change that affects speed, and
the history at the end records what changed and by how much.

## Running

```sh
lake build bench                      # `lake build` alone does not rebuild it
taskset -c 2 .lake/build/bin/bench > bench.txt
taskset -c 2 .lake/build/bin/bench badd bsub bmul bdiv bgcd bshl bshr bsqrt btostr bofstr \
  1 2 4 8 16 32 64 128 256 512 1024 >> bench.txt
scripts/bench_md.py bench.txt         # the two tables below
```

Arguments select operations and sizes, and `--no-nat` skips `Nat`, for a profiler. Pinning the
process to one core with `taskset` makes the results steadier; differences below about 5% are
noise.

## How to read the tables

- **Sizes** are in 32-bit limbs. A row of 256 limbs is about 8,200 bits, or 2,500 decimal digits.
- **The `Nat` column** is Lean's `Nat`: GMP with 64-bit limbs and assembly, behind a wrapper that
  copies operands and results. Below about 64 limbs that wrapper dominates, which is why the
  library is often faster there. A ratio is `Bignum / Nat`, so below 1 means faster than `Nat`.
- **One limb** compares an array with `Nat`'s unboxed small values, which need no allocation. The
  limb-level operations always allocate an array, so their 1-limb ratios are high. `BigNat` has a
  word fast path for values below `2⁶⁴`, which is what its 1- and 2-limb rows measure.
- **Results are checked in O(1)** on both sides, so the time is the operation alone. (Before
  `15534f8`, `BigNat` results were hashed, which inflated the large `b*` rows 2–4×.)
- **Machine:** AMD Ryzen 5 5600X (Zen 3), Linux 7.1, Lean `v4.36.0-rc1`, lean4-scalar-arrays
  `8ae4933`. Commit `df788df`, 2026-10-15.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | schoolbook, Karatsuba from 72, Toom-3 from 488 |
| `sqr` | `sqr` | `n` limbs | schoolbook, Karatsuba from 116, Toom-3 from 804 |
| `div` | `divMod` | `2n` by `n` limbs | `divRem1`, `divRem2`, Algorithm D, Burnikel–Ziegler from 176 |
| `shr` | `shiftRight` by 37 bits | `n` limbs | one pass in place |
| `badd` … `bdiv` | `BigNat` `+ - * /` | as above (`bdiv`: `2n` by `n`) | word fast path, then as above |
| `bgcd` | `BigNat.gcd` | `n` and `n` limbs | Lehmer with word cofactors, Euclid on words |
| `bshl`, `bshr` | `BigNat` `<<<`, `>>>` 37 | `n` limbs | one pass in place |
| `bsqrt` | `BigNat.sqrt` | `2n` limbs | Newton at growing precision |
| `btostr` | `toString` | `n` limbs | chunks of 9 digits, `divRem1` by `10⁹` |
| `bofstr` | `BigNat.ofString?` | the digits of `n` limbs | a fold over the characters, 9 digits per chunk |

## Current results

Ratio Bignum / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 4.28 | 0.48 | 0.49 | 0.48 | 0.53 | 0.58 | 0.75 | 1.04 | 1.49 | 1.34 | 1.85 | 1.91 | 1.76 |
| `sub` | 6.43 | 0.68 | 0.67 | 0.66 | 0.64 | 0.72 | 0.91 | 0.97 | 1.70 | 1.51 | 1.93 | 2.14 | 1.89 |
| `mul1` | 2.98 | 0.26 | 0.27 | 0.27 | 0.30 | 0.35 | 0.48 | 0.70 | 1.04 | 1.09 | 1.30 | 1.47 | 1.51 |
| `mul` | 3.45 | 0.58 | 0.67 | 1.29 | 2.23 | 3.58 | 5.36 | 6.22 | 6.81 | 6.89 | 7.79 | 9.23 | 9.17 |
| `sqr` | 3.59 | 0.57 | 0.66 | 1.28 | 2.10 | 2.74 | 3.39 | 4.02 | 4.38 | 4.56 | 5.32 | 6.15 | 6.50 |
| `div` | 4.10 | 1.23 | 2.14 | 2.23 | 2.61 | 3.31 | 3.87 | 4.63 | 4.72 | 4.49 | 4.58 | 4.60 | 5.29 |
| `shr` | 2.29 | 1.54 | 0.88 | 0.85 | 0.86 | 0.90 | 0.92 | 0.95 | 1.15 | 0.88 | 1.17 | 1.28 | 1.24 |
| `badd` | 1.68 | 1.13 | 0.82 | 0.80 | 0.85 | 0.90 | 0.99 | 1.31 | 1.69 | 1.58 | 1.79 |  |  |
| `bsub` | 1.71 | 1.32 | 1.04 | 1.01 | 0.96 | 1.06 | 1.24 | 1.21 | 1.99 | 1.74 | 2.04 |  |  |
| `bmul` | 1.62 | 1.20 | 0.92 | 1.54 | 2.41 | 3.71 | 5.38 | 6.25 | 6.67 | 6.85 | 7.79 |  |  |
| `bdiv` | 1.67 | 4.09 | 3.44 | 4.14 | 4.96 | 7.01 | 9.50 | 12.15 | 11.84 | 10.60 | 10.79 |  |  |
| `bgcd` | 0.45 | 1.33 | 17.64 | 13.44 | 14.71 | 14.34 | 13.34 | 12.96 | 12.45 | 11.51 | 9.17 |  |  |
| `bshl` | 0.82 | 1.04 | 0.79 | 0.76 | 0.76 | 0.83 | 0.89 | 0.98 | 1.26 | 0.96 | 1.35 |  |  |
| `bshr` | 1.51 | 0.41 | 0.82 | 0.80 | 0.82 | 0.83 | 0.91 | 0.97 | 1.14 | 0.92 | 1.18 |  |  |
| `bsqrt` | 1.05 | 0.72 | 1.59 | 2.76 | 3.66 | 3.09 | 3.94 | 3.03 | 3.62 | 2.28 | 2.07 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 36.3 ns | 38.7 ns | 39.8 ns | 39.9 ns | 43.2 ns | 48.8 ns | 67.1 ns | 108 ns | 199 ns | 361 ns | 696 ns | 1.35 µs | 2.68 µs |
| `sub` | 57.2 ns | 58.8 ns | 58.2 ns | 57.4 ns | 63.7 ns | 67.9 ns | 89.4 ns | 140 ns | 242 ns | 431 ns | 817 ns | 1.58 µs | 3.13 µs |
| `mul1` | 29.7 ns | 30.5 ns | 32.2 ns | 31.9 ns | 35 ns | 43.3 ns | 63.3 ns | 107 ns | 201 ns | 366 ns | 702 ns | 1.36 µs | 2.68 µs |
| `mul` | 34.8 ns | 47.3 ns | 66.4 ns | 125 ns | 267 ns | 762 ns | 2.66 µs | 8.52 µs | 27.1 µs | 80.6 µs | 233 µs | 700 µs | 1.98 ms |
| `sqr` | 37.7 ns | 46.4 ns | 65.5 ns | 124 ns | 254 ns | 584 ns | 1.68 µs | 5.51 µs | 17.4 µs | 53.3 µs | 158 µs | 461 µs | 1.39 ms |
| `div` | 70.6 ns | 161 ns | 405 ns | 536 ns | 868 ns | 1.9 µs | 5.23 µs | 17.7 µs | 58 µs | 177 µs | 550 µs | 1.61 ms | 4.77 ms |
| `shr` | 18.9 ns | 63.6 ns | 65.9 ns | 65.8 ns | 66.7 ns | 70 ns | 74.4 ns | 89.1 ns | 126 ns | 197 ns | 343 ns | 609 ns | 1.22 µs |
| `badd` | 15.8 ns | 92.7 ns | 67 ns | 66.8 ns | 70.3 ns | 76.8 ns | 94.7 ns | 138 ns | 228 ns | 386 ns | 725 ns |  |  |
| `bsub` | 18 ns | 116 ns | 91.3 ns | 89.8 ns | 97.8 ns | 101 ns | 125 ns | 176 ns | 278 ns | 467 ns | 857 ns |  |  |
| `bmul` | 17.7 ns | 98.4 ns | 91.8 ns | 150 ns | 292 ns | 790 ns | 2.68 µs | 8.56 µs | 26.7 µs | 80.8 µs | 233 µs |  |  |
| `bdiv` | 17.9 ns | 201 ns | 336 ns | 459 ns | 769 ns | 1.76 µs | 5.08 µs | 17.5 µs | 57.4 µs | 176 µs | 545 µs |  |  |
| `bgcd` | 47.4 ns | 78.7 ns | 3.07 µs | 7.82 µs | 17.8 µs | 38.3 µs | 81.9 µs | 184 µs | 457 µs | 1.22 ms | 3.65 ms |  |  |
| `bshl` | 78.6 ns | 79 ns | 61.7 ns | 60.8 ns | 61.8 ns | 66 ns | 72.9 ns | 92.5 ns | 139 ns | 213 ns | 398 ns |  |  |
| `bshr` | 17.7 ns | 17.7 ns | 63 ns | 63.3 ns | 64.2 ns | 66.1 ns | 74.4 ns | 90.7 ns | 125 ns | 196 ns | 341 ns |  |  |
| `bsqrt` | 98.4 ns | 960 ns | 2.26 µs | 4.25 µs | 7.29 µs | 10.7 µs | 22.2 µs | 61.6 µs | 234 µs | 553 µs | 1.65 ms |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication and squaring** are 5–9× behind from 64 limbs up. That is mostly structural:
  32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no 64 × 64 →
  128-bit multiply. Algorithm thresholds are close to GMP's in bits.
- **Division** follows multiplication, 4–5× behind; small `BigNat` divisions still pay a fixed
  cost (normalization, several arrays) that `Nat` doesn't.
- **`gcd`** is 9–18× behind from 4 limbs: each Lehmer step allocates; see TODO.
- **`sqrt`** is 1.6–4× behind; **decimal strings** are 10–25× faster than `Nat`, whose conversions
  work digit by digit.

## History

Notable changes in performance, newest first. Times are for the sizes shown, on the machine
above; ratios before `15534f8` for `BigNat` rows were inflated by the hashing check.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-15 | `df788df` | `sqrt` by Newton at growing precision | `bsqrt` 256: 786 → 233 µs; 1024: 8.47 → 1.65 ms |
| 2026-10-15 | `6e8a664` | division by two limbs in one pass (`divRem2`) | `bdiv` 2: 315 → 206 ns |
| 2026-10-15 | `5fdaca4` | `trim` without a closure; quotient-only `div` | `bdiv` 2: 428 → 315 ns; `badd` 4–64: −6–15% |
| 2026-10-15 | `34de09a` | `shiftLeft` in one pass, carries off the chain | `bshl` 1024: 796 → 408 ns |
| 2026-10-15 | `15534f8` | benchmark: O(1) result checks | measurement only |
| 2026-10-15 | `c57b9ee` | `shiftRight` in one pass | `shr` 1024: 1.89 → 0.34 µs |
| 2026-10-15 | `2c415c5` | normalized remainder shifted back, not divided | `div` 64–1024: −1–4% |
| 2026-10-15 | `18ce057` | decimal strings in chunks of 9 digits | `btostr`, `bofstr` 10–20× faster than `Nat` |
| 2026-10-15 | `3f867cb` | loop guards against a literal, not `USize.size` | small products −11–15% |
| 2026-10-15 | `65f660d` | Burnikel–Ziegler division from 176 limbs | `div` 4096: 17× → 5× behind `Nat` |
| 2026-10-15 | `6773e3e` | Knuth's correction of the quotient estimate | no add-backs (42% of limbs at 256) |
| 2026-10-15 | `1e02669` | schoolbook square in one final pass | faster than `mul` from 16 limbs |
| 2026-10-15 | `4b77886` | no result pairs in the row loops | fewer allocations per row |
| 2026-10-15 | `77ac72d` | in-place Algorithm D with `subMul1` | 270 → 34 allocations for 32 ÷ 16 limbs |
| 2026-10-14 | `89fcd6b` | word carries, hoisted slice fields | `add` 1.6× faster |
| 2026-10-14 | `680e200` | compiled loops on `foldInPlace` | one exclusivity check per loop |

To add an entry: rerun the affected operations before and after (`git stash` makes the "before"
easy), add a row here, and regenerate the tables when the change is broad.
