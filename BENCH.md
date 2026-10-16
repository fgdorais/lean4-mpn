# Benchmarks

This file tracks the performance of the library against Lean's `Nat`, which is backed by GMP. The
tables come from `lake exe bench` and are regenerated after each change that affects speed, and
the history at the end records what changed and by how much.

## Running

```sh
lake build bench                      # `lake build` alone does not rebuild it
taskset -c 2 .lake/build/bin/bench > bench.txt
taskset -c 2 .lake/build/bin/bench badd bsub bmul bdiv bgcd bshl bshr bsqrt btostr bofstr \
  btonat bofnat 1 2 4 8 16 32 64 128 256 512 1024 >> bench.txt
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
  `8ae4933`. Commit `4b92572`, 2026-10-16.

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
| `btonat` | `BigNat.toNat` | `n` limbs | by halves, joined with shifts; `Nat` column: `x + 1` |
| `bofnat` | `BigNat.ofNat` | `n` limbs | by halves, then 64 bits at a time; `Nat` column: `x + 1` |

## Current results

Ratio Bignum / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 5.45 | 0.54 | 0.54 | 0.54 | 0.58 | 0.67 | 0.80 | 1.11 | 1.53 | 1.36 | 1.68 | 1.85 | 1.77 |
| `sub` | 5.76 | 0.58 | 0.57 | 0.56 | 0.55 | 0.66 | 0.85 | 0.85 | 1.74 | 1.39 | 1.91 | 1.97 | 2.18 |
| `mul1` | 3.12 | 0.27 | 0.27 | 0.28 | 0.30 | 0.36 | 0.49 | 0.69 | 1.05 | 1.02 | 1.30 | 1.43 | 1.49 |
| `mul` | 3.79 | 0.54 | 0.56 | 1.01 | 1.79 | 2.93 | 4.33 | 5.05 | 5.53 | 5.52 | 6.23 | 7.26 | 7.42 |
| `sqr` | 3.83 | 0.55 | 0.53 | 0.87 | 1.42 | 1.88 | 2.46 | 2.95 | 3.21 | 3.32 | 3.89 | 4.51 | 4.57 |
| `div` | 4.01 | 1.24 | 2.07 | 2.11 | 2.64 | 3.39 | 4.03 | 4.88 | 4.75 | 4.27 | 4.12 | 4.05 | 4.56 |
| `badd` | 1.70 | 1.26 | 0.91 | 0.86 | 0.91 | 0.96 | 1.08 | 1.38 | 1.71 | 1.46 | 1.78 |  |  |
| `bsub` | 1.84 | 1.11 | 0.92 | 0.89 | 0.84 | 0.95 | 1.16 | 1.21 | 1.94 | 1.53 | 2.00 |  |  |
| `bmul` | 1.80 | 1.15 | 0.80 | 1.30 | 2.03 | 2.83 | 4.24 | 5.03 | 5.47 | 5.54 | 6.25 |  |  |
| `bdiv` | 1.82 | 3.92 | 3.45 | 3.96 | 4.97 | 7.10 | 9.87 | 12.66 | 11.99 | 10.12 | 9.82 |  |  |
| `bgcd` | 0.45 | 1.32 | 17.33 | 13.06 | 14.46 | 14.16 | 13.30 | 12.89 | 12.49 | 11.51 | 9.32 |  |  |
| `bshl` | 0.76 | 0.97 | 0.78 | 0.76 | 0.78 | 0.81 | 0.89 | 1.07 | 1.33 | 0.95 | 1.27 |  |  |
| `bshr` | 1.72 | 0.38 | 0.81 | 0.79 | 0.80 | 0.82 | 0.81 | 0.92 | 1.14 | 0.84 | 1.09 |  |  |
| `bsqrt` | 1.04 | 0.71 | 1.59 | 2.81 | 3.77 | 3.15 | 4.02 | 3.15 | 3.66 | 2.24 | 1.94 |  |  |
| `btostr` | 0.92 | 0.83 | 0.05 | 0.04 | 0.05 | 0.05 | 0.06 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.22 | 0.98 | 0.19 | 0.11 | 0.09 | 0.09 | 0.08 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.00 | 0.77 | 2.19 | 5.09 | 10.76 | 23.88 | 47.23 | 92.68 | 166.67 | 200.43 | 294.10 |  |  |
| `bofnat` | 1.58 | 0.60 | 1.17 | 2.93 | 6.93 | 14.02 | 27.56 | 55.12 | 95.14 | 120.09 | 178.50 |  |  |
| `shr` | 2.27 | 1.30 | 0.70 | 0.60 | 0.69 | 0.70 | 0.61 | 0.80 | 1.10 | 0.92 | 0.87 | 1.08 | 1.18 |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 44.6 ns | 43.8 ns | 44.3 ns | 45.9 ns | 49.4 ns | 58.9 ns | 74.1 ns | 118 ns | 209 ns | 367 ns | 697 ns | 1.34 µs | 2.68 µs |
| `sub` | 51 ns | 51.5 ns | 50.7 ns | 51.6 ns | 56.7 ns | 62.5 ns | 86.1 ns | 140 ns | 245 ns | 433 ns | 813 ns | 1.57 µs | 3.14 µs |
| `mul1` | 30.5 ns | 31.1 ns | 32.1 ns | 32.9 ns | 35.8 ns | 44 ns | 64.6 ns | 106 ns | 203 ns | 366 ns | 697 ns | 1.35 µs | 2.66 µs |
| `mul` | 34.4 ns | 43.2 ns | 55.2 ns | 93.8 ns | 210 ns | 627 ns | 2.19 µs | 6.97 µs | 21.9 µs | 64.6 µs | 188 µs | 551 µs | 1.55 ms |
| `sqr` | 39.1 ns | 44.7 ns | 53.2 ns | 82 ns | 167 ns | 406 ns | 1.25 µs | 4.04 µs | 12.7 µs | 38.9 µs | 116 µs | 338 µs | 956 µs |
| `div` | 68.9 ns | 163 ns | 385 ns | 515 ns | 861 ns | 1.92 µs | 5.36 µs | 18.5 µs | 58.4 µs | 168 µs | 494 µs | 1.41 ms | 4.01 ms |
| `badd` | 14.1 ns | 102 ns | 73.1 ns | 72.4 ns | 75.5 ns | 83 ns | 98.4 ns | 143 ns | 231 ns | 389 ns | 720 ns |  |  |
| `bsub` | 16.4 ns | 98.1 ns | 80.9 ns | 81.2 ns | 87.8 ns | 89.9 ns | 115 ns | 168 ns | 272 ns | 461 ns | 843 ns |  |  |
| `bmul` | 16.4 ns | 92.9 ns | 80 ns | 121 ns | 238 ns | 647 ns | 2.21 µs | 6.99 µs | 21.7 µs | 64.8 µs | 187 µs |  |  |
| `bdiv` | 16.2 ns | 184 ns | 328 ns | 444 ns | 770 ns | 1.79 µs | 5.23 µs | 18.1 µs | 57.8 µs | 167 µs | 496 µs |  |  |
| `bgcd` | 47.2 ns | 77.5 ns | 2.98 µs | 7.64 µs | 17.5 µs | 37.8 µs | 81.5 µs | 183 µs | 457 µs | 1.22 ms | 3.7 ms |  |  |
| `bshl` | 71 ns | 71.3 ns | 57.8 ns | 56.8 ns | 58.4 ns | 61.7 ns | 70.3 ns | 92.6 ns | 141 ns | 216 ns | 396 ns |  |  |
| `bshr` | 15.7 ns | 15.7 ns | 59.6 ns | 59.8 ns | 60.7 ns | 63 ns | 68.5 ns | 86.8 ns | 125 ns | 194 ns | 338 ns |  |  |
| `bsqrt` | 100 ns | 943 ns | 2.28 µs | 4.35 µs | 7.54 µs | 10.9 µs | 22.7 µs | 64 µs | 234 µs | 541 µs | 1.53 ms |  |  |
| `btostr` | 26.4 ns | 30.3 ns | 393 ns | 779 ns | 1.82 µs | 4.59 µs | 12.8 µs | 40.3 µs | 139 µs | 518 µs | 1.99 ms |  |  |
| `bofstr` | 313 ns | 448 ns | 733 ns | 1.29 µs | 2.53 µs | 5.11 µs | 10.5 µs | 23.4 µs | 59.1 µs | 166 µs | 512 µs |  |  |
| `btonat` | 9.98 ns | 87.9 ns | 248 ns | 590 ns | 1.28 µs | 2.77 µs | 5.62 µs | 11.4 µs | 23 µs | 46.9 µs | 94.7 µs |  |  |
| `bofnat` | 16.8 ns | 67.8 ns | 132 ns | 340 ns | 832 ns | 1.64 µs | 3.28 µs | 6.78 µs | 13.7 µs | 28.1 µs | 57.3 µs |  |  |
| `shr` | 18.6 ns | 53.8 ns | 54.3 ns | 54.5 ns | 55.3 ns | 58.1 ns | 65.4 ns | 82.3 ns | 124 ns | 190 ns | 330 ns | 595 ns | 1.19 µs |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4–7.5× behind from 64 limbs up, **squaring** 2.5–4.6×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits.
- **Division** follows multiplication, 4–5× behind; small `BigNat` divisions still pay a fixed
  cost (normalization, several arrays) that `Nat` doesn't.
- **`gcd`** is 9–18× behind from 4 limbs: each Lehmer step allocates; see TODO.
- **`sqrt`** is 1.6–4× behind; **decimal strings** are 10–25× faster than `Nat`, whose conversions
  work digit by digit.
- **Conversions to and from `Nat`** cost about one operation on `Nat` (some 40 ns) per two
  limbs, against one linear pass for `Nat` itself; they are a boundary, not arithmetic.

## History

Notable changes in performance, newest first. Times are for the sizes shown, on the machine
above; ratios before `15534f8` for `BigNat` rows were inflated by the hashing check.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-16 | (uncommitted) | normalized dividend divided in place; `BigNat` divided by a word without its array | `bdiv` 2: 192 → 170 ns; 4: 337 → 275 ns; 16: 799 → 707 ns |
| 2026-10-16 | `7932eaf` | sums and products of two words that overflow, without arrays per word | `badd` 2: 95 → 34 ns; `bmul` 2: 92 → 50 ns |
| 2026-10-16 | `4b92572` | conversions to and from `Nat` by halves | `btonat` 4096: 6.14 → 0.39 ms; `bofnat` 4096: 2.23 → 0.24 ms; 64: 4.59 → 3.31 µs |
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
