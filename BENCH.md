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
  `8ae4933`. Commit `8ed7b6d`, 2026-10-15.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | Comba schoolbook, Karatsuba from 64, Toom-3 from 480 |
| `sqr` | `sqr` | `n` limbs | Comba square, Karatsuba from 96, Toom-3 from 720 |
| `div` | `divMod` | `2n` by `n` limbs | `divRem1`, `divRem2`, Algorithm D, Burnikel–Ziegler from 128 |
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
| `add` | 4.43 | 0.49 | 0.51 | 0.51 | 0.53 | 0.59 | 0.78 | 1.06 | 1.47 | 1.34 | 1.84 | 1.90 | 1.77 |
| `sub` | 6.00 | 0.60 | 0.58 | 0.59 | 0.54 | 0.61 | 0.86 | 0.92 | 1.72 | 1.50 | 1.97 | 1.87 | 1.90 |
| `mul1` | 3.27 | 0.28 | 0.29 | 0.29 | 0.32 | 0.37 | 0.49 | 0.68 | 1.01 | 1.10 | 1.29 | 1.46 | 1.46 |
| `mul` | 3.89 | 0.55 | 0.54 | 1.03 | 1.79 | 2.92 | 4.37 | 5.09 | 5.54 | 5.83 | 6.67 | 7.94 | 8.06 |
| `sqr` | 3.85 | 0.51 | 0.51 | 0.83 | 1.39 | 1.90 | 2.55 | 3.11 | 3.41 | 3.61 | 4.34 | 4.99 | 5.37 |
| `div` | 4.08 | 1.35 | 2.12 | 2.21 | 2.61 | 3.34 | 3.93 | 4.76 | 4.59 | 4.19 | 4.11 | 4.10 | 4.67 |
| `shr` | 1.91 | 1.31 | 0.76 | 0.73 | 0.76 | 0.78 | 0.86 | 0.90 | 1.06 | 0.99 | 1.14 | 1.20 | 1.25 |
| `badd` | 1.69 | 1.16 | 0.76 | 0.75 | 0.75 | 0.86 | 0.86 | 1.20 | 1.58 | 1.49 | 1.79 |  |  |
| `bsub` | 1.92 | 1.27 | 0.97 | 0.77 | 0.82 | 0.89 | 0.98 | 1.14 | 1.94 | 1.58 | 1.89 |  |  |
| `bmul` | 1.76 | 1.06 | 0.75 | 1.26 | 1.97 | 2.92 | 4.31 | 5.18 | 5.47 | 5.83 | 6.78 |  |  |
| `bdiv` | 1.80 | 4.09 | 3.01 | 3.87 | 4.34 | 6.48 | 9.16 | 12.43 | 11.48 | 9.82 | 9.51 |  |  |
| `bgcd` | 0.45 | 1.32 | 17.64 | 13.51 | 14.71 | 14.42 | 13.55 | 13.17 | 12.60 | 11.70 | 9.27 |  |  |
| `bshl` | 0.65 | 0.81 | 0.60 | 0.58 | 0.64 | 0.67 | 0.74 | 1.01 | 1.23 | 1.05 | 1.33 |  |  |
| `bshr` | 1.77 | 0.40 | 0.69 | 0.65 | 0.66 | 0.67 | 0.67 | 0.87 | 1.11 | 0.88 | 1.04 |  |  |
| `bsqrt` | 1.05 | 0.71 | 1.62 | 2.77 | 3.69 | 3.06 | 3.98 | 3.05 | 3.55 | 2.16 | 1.87 |  |  |
| `btostr` | 0.94 | 0.83 | 0.06 | 0.05 | 0.04 | 0.05 | 0.06 | 0.07 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.21 | 1.02 | 0.20 | 0.12 | 0.10 | 0.09 | 0.08 | 0.09 | 0.09 | 0.09 | 0.09 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 36.5 ns | 38.8 ns | 40.9 ns | 41.2 ns | 43 ns | 49.4 ns | 71.3 ns | 110 ns | 197 ns | 359 ns | 694 ns | 1.34 µs | 2.67 µs |
| `sub` | 52.1 ns | 52.4 ns | 51.7 ns | 51.9 ns | 57.5 ns | 61.2 ns | 86.4 ns | 137 ns | 238 ns | 426 ns | 813 ns | 1.58 µs | 3.15 µs |
| `mul1` | 32.7 ns | 33 ns | 33.8 ns | 34.5 ns | 37.5 ns | 44.8 ns | 64.3 ns | 103 ns | 195 ns | 356 ns | 688 ns | 1.34 µs | 2.64 µs |
| `mul` | 37.2 ns | 44.6 ns | 56.3 ns | 95.9 ns | 210 ns | 621 ns | 2.17 µs | 7.02 µs | 22.1 µs | 68.2 µs | 200 µs | 602 µs | 1.7 ms |
| `sqr` | 38.5 ns | 41.8 ns | 52.2 ns | 81.3 ns | 167 ns | 410 ns | 1.27 µs | 4.26 µs | 13.6 µs | 42.2 µs | 129 µs | 375 µs | 1.15 ms |
| `div` | 70.1 ns | 175 ns | 405 ns | 549 ns | 867 ns | 1.92 µs | 5.35 µs | 18.2 µs | 56.4 µs | 165 µs | 493 µs | 1.43 ms | 4.24 ms |
| `shr` | 19.9 ns | 55.1 ns | 56.4 ns | 56.2 ns | 58.8 ns | 61 ns | 69.8 ns | 81.1 ns | 116 ns | 189 ns | 332 ns | 599 ns | 1.21 µs |
| `badd` | 14 ns | 95.6 ns | 62.3 ns | 65 ns | 65.3 ns | 76.2 ns | 92.3 ns | 132 ns | 219 ns | 380 ns | 720 ns |  |  |
| `bsub` | 16.7 ns | 109 ns | 83 ns | 83.5 ns | 94.7 ns | 95.9 ns | 119 ns | 169 ns | 269 ns | 464 ns | 851 ns |  |  |
| `bmul` | 15.7 ns | 91.9 ns | 79 ns | 120 ns | 234 ns | 648 ns | 2.21 µs | 7.1 µs | 22.2 µs | 68.2 µs | 202 µs |  |  |
| `bdiv` | 16 ns | 203 ns | 349 ns | 468 ns | 776 ns | 1.77 µs | 5.14 µs | 17.9 µs | 55.7 µs | 163 µs | 487 µs |  |  |
| `bgcd` | 47.3 ns | 78.9 ns | 3.07 µs | 7.85 µs | 17.8 µs | 38.5 µs | 82.8 µs | 187 µs | 465 µs | 1.24 ms | 3.69 ms |  |  |
| `bshl` | 73.7 ns | 74 ns | 59.7 ns | 58.9 ns | 66.4 ns | 71.5 ns | 79.4 ns | 93.2 ns | 134 ns | 210 ns | 393 ns |  |  |
| `bshr` | 16.2 ns | 16.2 ns | 60.9 ns | 61.9 ns | 63.6 ns | 67.4 ns | 71.2 ns | 89 ns | 123 ns | 194 ns | 337 ns |  |  |
| `bsqrt` | 97.3 ns | 957 ns | 2.3 µs | 4.32 µs | 7.45 µs | 10.8 µs | 22.6 µs | 62.8 µs | 229 µs | 525 µs | 1.5 ms |  |  |
| `btostr` | 27.4 ns | 30.5 ns | 413 ns | 798 ns | 1.82 µs | 4.6 µs | 13 µs | 40.4 µs | 140 µs | 518 µs | 1.98 ms |  |  |
| `bofstr` | 344 ns | 485 ns | 793 ns | 1.38 µs | 2.69 µs | 5.34 µs | 11 µs | 24.5 µs | 61.3 µs | 169 µs | 520 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4–8× behind from 64 limbs up, **squaring** 2.5–5×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits.
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
| 2026-10-16 | `a46c179` | Toom-3's exact divisions without the divider; Toom-3 thresholds retuned | `mul` 2048: 589 → 540 µs; 4096: 1.65 → 1.54 ms; `sqr` 4096: 1.08 → 0.97 ms |
| 2026-10-15 | `8bcb570` | Karatsuba's middle term in one pass (`addDiffInto`) | `mul` 1024: 201 → 193 µs; `sqr` 256: 13.6 → 12.9 µs; 4096: 1.15 → 1.09 ms |
| 2026-10-15 | `8ed7b6d` | Comba squaring; thresholds retuned | `sqr` 64: 1.69 → 1.27 µs; 256: 17.4 → 13.6 µs; 4096: 1.41 → 1.15 ms |
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
