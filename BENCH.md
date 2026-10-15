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
  `8ae4933`. Commit `fd1829d`, 2026-10-15.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | Comba schoolbook, Karatsuba from 72, Toom-3 from 576 |
| `sqr` | `sqr` | `n` limbs | Comba square, Karatsuba from 112, Toom-3 from 892 |
| `div` | `divMod` | `2n` by `n` limbs | `divRem1`, `divRem2`, Algorithm D, Burnikel–Ziegler from 144 |
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
| `add` | 4.40 | 0.41 | 0.46 | 0.46 | 0.45 | 0.59 | 0.70 | 0.97 | 1.45 | 1.38 | 1.80 | 1.86 | 1.74 |
| `sub` | 6.31 | 0.51 | 0.49 | 0.62 | 0.57 | 0.51 | 0.67 | 1.00 | 1.69 | 1.35 | 1.80 | 1.86 | 1.75 |
| `mul1` | 3.10 | 0.23 | 0.24 | 0.24 | 0.28 | 0.31 | 0.43 | 0.66 | 0.99 | 1.07 | 1.22 | 1.39 | 1.45 |
| `mul` | 3.58 | 0.46 | 0.49 | 1.01 | 1.47 | 2.52 | 4.11 | 5.07 | 5.50 | 5.83 | 6.61 | 7.92 | 7.82 |
| `sqr` | 3.81 | 0.47 | 0.58 | 1.01 | 1.81 | 2.38 | 3.25 | 4.00 | 4.39 | 4.58 | 5.34 | 6.16 | 6.56 |
| `div` | 4.16 | 1.13 | 1.87 | 1.93 | 2.55 | 3.29 | 3.92 | 4.79 | 4.57 | 4.19 | 4.11 | 4.09 | 4.68 |
| `shr` | 1.88 | 1.31 | 0.54 | 0.62 | 0.70 | 0.75 | 0.78 | 0.81 | 1.04 | 0.96 | 0.87 | 1.12 | 1.16 |
| `badd` | 1.78 | 1.07 | 0.73 | 0.72 | 0.77 | 0.82 | 0.96 | 1.23 | 1.59 | 1.54 | 1.79 |  |  |
| `bsub` | 1.96 | 1.27 | 0.99 | 1.00 | 0.92 | 1.06 | 1.21 | 1.17 | 1.96 | 1.72 | 2.03 |  |  |
| `bmul` | 1.79 | 1.16 | 0.85 | 1.39 | 2.15 | 3.07 | 4.35 | 5.13 | 5.55 | 5.81 | 6.76 |  |  |
| `bdiv` | 1.81 | 4.30 | 3.55 | 4.10 | 4.96 | 7.00 | 9.64 | 12.57 | 11.51 | 9.88 | 9.70 |  |  |
| `bgcd` | 0.45 | 1.33 | 17.80 | 13.30 | 14.51 | 14.27 | 13.42 | 13.03 | 12.56 | 11.60 | 9.27 |  |  |
| `bshl` | 0.80 | 1.13 | 0.80 | 0.77 | 0.81 | 0.84 | 0.90 | 1.03 | 1.25 | 0.97 | 1.41 |  |  |
| `bshr` | 1.78 | 0.40 | 0.83 | 0.82 | 0.84 | 0.86 | 0.91 | 0.98 | 1.14 | 0.92 | 1.22 |  |  |
| `bsqrt` | 1.06 | 0.72 | 1.54 | 2.63 | 3.53 | 2.96 | 3.92 | 3.07 | 3.55 | 2.17 | 1.89 |  |  |
| `btostr` | 0.90 | 0.86 | 0.06 | 0.04 | 0.04 | 0.05 | 0.06 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.26 | 1.00 | 0.20 | 0.12 | 0.10 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 36.3 ns | 38.7 ns | 39.8 ns | 40.7 ns | 44.4 ns | 52.5 ns | 69.3 ns | 111 ns | 199 ns | 360 ns | 697 ns | 1.35 µs | 2.68 µs |
| `sub` | 54.9 ns | 54.6 ns | 53.8 ns | 55.6 ns | 59.6 ns | 64.4 ns | 87.6 ns | 137 ns | 237 ns | 428 ns | 813 ns | 1.58 µs | 3.12 µs |
| `mul1` | 31 ns | 31.2 ns | 32 ns | 32.7 ns | 37.1 ns | 45.2 ns | 64.2 ns | 103 ns | 194 ns | 358 ns | 688 ns | 1.34 µs | 2.65 µs |
| `mul` | 34.3 ns | 43.8 ns | 55.8 ns | 96.2 ns | 211 ns | 623 ns | 2.16 µs | 7.05 µs | 22 µs | 68.2 µs | 199 µs | 602 µs | 1.69 ms |
| `sqr` | 38.5 ns | 45 ns | 61.2 ns | 103 ns | 217 ns | 577 ns | 1.69 µs | 5.52 µs | 17.4 µs | 53.6 µs | 159 µs | 466 µs | 1.41 ms |
| `div` | 71.6 ns | 170 ns | 382 ns | 516 ns | 846 ns | 1.88 µs | 5.33 µs | 18.3 µs | 56.2 µs | 165 µs | 493 µs | 1.43 ms | 4.21 ms |
| `shr` | 19.5 ns | 54.3 ns | 57.7 ns | 59.3 ns | 58.9 ns | 61.5 ns | 67 ns | 83 ns | 117 ns | 191 ns | 334 ns | 601 ns | 1.21 µs |
| `badd` | 14.7 ns | 90.9 ns | 62.2 ns | 63.3 ns | 66.6 ns | 73.4 ns | 90.7 ns | 132 ns | 220 ns | 381 ns | 723 ns |  |  |
| `bsub` | 17 ns | 111 ns | 86.8 ns | 88.9 ns | 93.9 ns | 98.4 ns | 119 ns | 173 ns | 273 ns | 466 ns | 853 ns |  |  |
| `bmul` | 15.9 ns | 95.7 ns | 84 ns | 128 ns | 249 ns | 659 ns | 2.21 µs | 7.08 µs | 22.2 µs | 68.5 µs | 202 µs |  |  |
| `bdiv` | 16.1 ns | 203 ns | 340 ns | 463 ns | 774 ns | 1.77 µs | 5.16 µs | 18.1 µs | 55.8 µs | 164 µs | 493 µs |  |  |
| `bgcd` | 47.7 ns | 78.7 ns | 3.08 µs | 7.77 µs | 17.7 µs | 38.1 µs | 82 µs | 185 µs | 461 µs | 1.23 ms | 3.68 ms |  |  |
| `bshl` | 75.2 ns | 82.6 ns | 59.1 ns | 57.8 ns | 60.2 ns | 63.7 ns | 70.4 ns | 88.8 ns | 133 ns | 211 ns | 395 ns |  |  |
| `bshr` | 16.3 ns | 16.3 ns | 60.9 ns | 61.6 ns | 63 ns | 66.5 ns | 72.7 ns | 88.2 ns | 124 ns | 194 ns | 338 ns |  |  |
| `bsqrt` | 98.8 ns | 968 ns | 2.29 µs | 4.31 µs | 7.38 µs | 10.7 µs | 22.4 µs | 62.6 µs | 229 µs | 524 µs | 1.5 ms |  |  |
| `btostr` | 25.7 ns | 30.3 ns | 410 ns | 793 ns | 1.81 µs | 4.59 µs | 13 µs | 40.6 µs | 140 µs | 518 µs | 1.98 ms |  |  |
| `bofstr` | 323 ns | 479 ns | 783 ns | 1.38 µs | 2.65 µs | 5.33 µs | 11.2 µs | 25 µs | 62 µs | 172 µs | 526 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication and squaring** are 4–8× behind from 64 limbs up. That is mostly structural:
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
| 2026-10-15 | `fd1829d` | schoolbook product by columns (Comba); thresholds retuned | `mul` 64: 2.66 → 2.17 µs; 4096: 1.98 → 1.69 ms; `div` 1024: 550 → 493 µs |
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
