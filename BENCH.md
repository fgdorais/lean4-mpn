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
noise. Below 64 limbs, changing the library moves the code of both columns in the binary, and
either side can shift by 5–20% from that alone (the `Nat` column too), so compare the times of
the same column across runs rather than the ratios.

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
| `mul` | `mulLimbs` | `n` by `n` limbs | Comba schoolbook, Karatsuba from 64, Toom-3 from 480; Toom-3 by 2 from 160 between 4:3 and 15:8, Toom-4 by 2 from 192 up to 2:1 |
| `sqr` | `sqr` | `n` limbs | Comba square, Karatsuba from 96, Toom-3 from 720 |
| `div` | `div`, the quotient | `2n` by `n` limbs | `divRem1`, `divRem2`, Algorithm D, Burnikel–Ziegler from 176 |
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
| `add` | 5.29 | 0.57 | 0.58 | 0.57 | 0.62 | 0.67 | 0.83 | 1.12 | 1.51 | 1.36 | 1.69 | 1.84 | 1.80 |
| `sub` | 5.71 | 0.61 | 0.62 | 0.65 | 0.59 | 0.71 | 0.85 | 0.91 | 1.73 | 1.42 | 1.94 | 1.98 | 2.22 |
| `mul1` | 3.22 | 0.26 | 0.28 | 0.27 | 0.31 | 0.36 | 0.49 | 0.70 | 1.03 | 1.05 | 1.35 | 1.45 | 1.52 |
| `mul` | 3.88 | 0.61 | 0.61 | 1.06 | 1.83 | 2.86 | 4.19 | 4.86 | 5.20 | 5.13 | 5.78 | 6.48 | 6.56 |
| `sqr` | 3.92 | 0.53 | 0.53 | 0.89 | 1.44 | 1.91 | 2.52 | 2.99 | 3.22 | 3.35 | 3.87 | 4.59 | 4.66 |
| `div` | 4.84 | 2.81 | 2.26 | 2.66 | 3.35 | 5.16 | 7.41 | 10.00 | 9.51 | 8.26 | 8.09 | 7.88 | 8.94 |
| `shr` | 2.03 | 1.29 | 0.73 | 0.72 | 0.75 | 0.74 | 0.79 | 0.88 | 1.10 | 0.92 | 1.08 | 1.07 | 1.19 |
| `badd` | 1.74 | 0.37 | 0.84 | 0.82 | 0.87 | 0.92 | 1.06 | 1.30 | 1.65 | 1.39 | 1.79 |  |  |
| `bsub` | 1.88 | 1.28 | 0.99 | 0.99 | 0.94 | 1.05 | 1.16 | 1.23 | 1.96 | 1.57 | 2.04 |  |  |
| `bmul` | 1.73 | 0.60 | 0.87 | 1.34 | 2.03 | 2.94 | 4.26 | 4.88 | 5.19 | 5.12 | 5.78 |  |  |
| `bdiv` | 1.71 | 1.97 | 2.51 | 2.83 | 3.44 | 5.24 | 7.46 | 10.07 | 9.55 | 8.42 | 8.12 |  |  |
| `bgcd` | 0.45 | 1.32 | 4.09 | 3.54 | 3.41 | 3.66 | 3.81 | 4.07 | 4.43 | 4.63 | 4.09 |  |  |
| `bshl` | 0.75 | 0.98 | 0.83 | 0.74 | 0.76 | 0.76 | 0.84 | 1.00 | 1.27 | 0.93 | 1.27 |  |  |
| `bshr` | 1.53 | 0.36 | 0.86 | 0.84 | 0.87 | 0.87 | 0.93 | 0.99 | 1.18 | 0.87 | 1.07 |  |  |
| `bsqrt` | 1.05 | 0.39 | 0.89 | 1.64 | 2.12 | 1.66 | 2.17 | 1.59 | 1.45 | 1.16 | 1.02 |  |  |
| `btostr` | 0.93 | 0.84 | 0.06 | 0.04 | 0.04 | 0.05 | 0.06 | 0.07 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.23 | 0.97 | 0.19 | 0.11 | 0.09 | 0.08 | 0.08 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.07 | 0.79 | 2.26 | 5.22 | 11.40 | 24.05 | 47.63 | 93.44 | 161.27 | 202.16 | 295.08 |  |  |
| `bofnat` | 1.68 | 0.60 | 1.14 | 2.88 | 7.27 | 14.14 | 27.88 | 55.82 | 97.18 | 121.46 | 177.23 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 43.5 ns | 45.5 ns | 46.6 ns | 46.7 ns | 50.3 ns | 56.1 ns | 73.6 ns | 115 ns | 201 ns | 361 ns | 700 ns | 1.35 µs | 2.72 µs |
| `sub` | 50.8 ns | 51.8 ns | 52.1 ns | 55.6 ns | 62.8 ns | 65.9 ns | 84.3 ns | 138 ns | 239 ns | 423 ns | 813 ns | 1.58 µs | 3.17 µs |
| `mul1` | 30.2 ns | 30.7 ns | 32.7 ns | 31.8 ns | 36.5 ns | 44.1 ns | 65.8 ns | 107 ns | 200 ns | 378 ns | 725 ns | 1.37 µs | 2.72 µs |
| `mul` | 38.1 ns | 49.3 ns | 59.7 ns | 99.9 ns | 214 ns | 606 ns | 2.09 µs | 6.66 µs | 20.8 µs | 60.5 µs | 174 µs | 493 µs | 1.39 ms |
| `sqr` | 40 ns | 43.6 ns | 52.9 ns | 83.4 ns | 170 ns | 409 ns | 1.25 µs | 4.1 µs | 12.8 µs | 39.5 µs | 118 µs | 346 µs | 974 µs |
| `div` | 46.4 ns | 135 ns | 217 ns | 303 ns | 523 ns | 1.3 µs | 3.95 µs | 14.4 µs | 46.2 µs | 138 µs | 412 µs | 1.19 ms | 3.46 ms |
| `shr` | 19.9 ns | 53.7 ns | 54 ns | 54.4 ns | 56.6 ns | 57.8 ns | 64.4 ns | 80.6 ns | 119 ns | 189 ns | 335 ns | 606 ns | 1.21 µs |
| `badd` | 14.4 ns | 30.1 ns | 67.9 ns | 68.4 ns | 71.9 ns | 78.2 ns | 95.8 ns | 137 ns | 223 ns | 381 ns | 723 ns |  |  |
| `bsub` | 16.8 ns | 109 ns | 83.3 ns | 85 ns | 98.3 ns | 96.8 ns | 115 ns | 170 ns | 270 ns | 461 ns | 848 ns |  |  |
| `bmul` | 15.8 ns | 48.5 ns | 84.2 ns | 124 ns | 238 ns | 621 ns | 2.11 µs | 6.69 µs | 20.7 µs | 60.4 µs | 174 µs |  |  |
| `bdiv` | 15.2 ns | 92.6 ns | 242 ns | 326 ns | 543 ns | 1.33 µs | 3.99 µs | 14.5 µs | 46.5 µs | 139 µs | 411 µs |  |  |
| `bgcd` | 47.3 ns | 78.1 ns | 708 ns | 2.08 µs | 4.19 µs | 9.81 µs | 23.3 µs | 58.2 µs | 164 µs | 491 µs | 1.63 ms |  |  |
| `bshl` | 72.4 ns | 73.8 ns | 63 ns | 56.8 ns | 57.9 ns | 59.4 ns | 67.5 ns | 87.9 ns | 137 ns | 214 ns | 400 ns |  |  |
| `bshr` | 15 ns | 15 ns | 64.3 ns | 65.2 ns | 66.7 ns | 68.9 ns | 74.9 ns | 91.6 ns | 129 ns | 201 ns | 347 ns |  |  |
| `bsqrt` | 98.4 ns | 529 ns | 1.26 µs | 2.54 µs | 4.26 µs | 5.72 µs | 12.2 µs | 32.5 µs | 93.5 µs | 280 µs | 809 µs |  |  |
| `btostr` | 26.7 ns | 30.8 ns | 412 ns | 796 ns | 1.83 µs | 4.6 µs | 12.8 µs | 40.4 µs | 140 µs | 518 µs | 2 ms |  |  |
| `bofstr` | 314 ns | 447 ns | 752 ns | 1.31 µs | 2.56 µs | 5.12 µs | 10.7 µs | 23.8 µs | 59.8 µs | 167 µs | 516 µs |  |  |
| `btonat` | 10.9 ns | 88.8 ns | 255 ns | 600 ns | 1.3 µs | 2.79 µs | 5.62 µs | 11.4 µs | 22.9 µs | 46.9 µs | 95.9 µs |  |  |
| `bofnat` | 17.5 ns | 68.1 ns | 129 ns | 331 ns | 829 ns | 1.64 µs | 3.29 µs | 6.81 µs | 13.8 µs | 28.3 µs | 57.6 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.1–2.2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4.2–6.6× behind from 64 limbs up, **squaring** 2.5–4.7×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits.
- **Division** is 7.4–10× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.4 of its
  own. Small `BigNat` divisions still pay a fixed cost (normalization, several arrays): 1.8–3.4×
  from 2 to 16 limbs. Division by a word of two limbs costs about 15 ns per limb, 8× GMP's.
- **`gcd`** is 3.4–4.6× behind from 4 limbs, Lehmer with word cofactors and both new numbers in
  one pass; GMP's subquadratic `hgcd` would show from a few hundred limbs.
- **`sqrt`** is 1.1–2.2× behind from 8 limbs, and faster up to 4; **decimal strings** are 10–20×
  faster than `Nat`, whose conversions work digit by digit.
- **Conversions to and from `Nat`** cost about one operation on `Nat` (some 40 ns) per two
  limbs, against one linear pass for `Nat` itself; they are a boundary, not arithmetic.

## History

Notable changes in performance, newest first. Times are for the sizes shown, on the machine
above; ratios before `15534f8` for `BigNat` rows were inflated by the hashing check.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-16 | `1371203` | Comba's columns from 32 limbs add whole products and count the wraps of one sum (`colLoopW`) | `mul` 64–256 limbs −5%, 1024: 188 → 174 µs, 4096: 1.55 → 1.39 ms; `div` 1024–4096 −4 to −7% |
| 2026-10-16 | `5306ce2` | Division by two limbs normalizes the dividend on the fly instead of a shifted copy (`divRem2`, `div2`) | `BigNat` divided by `10¹⁸` (no bench row): 5 limbs 180 → 149 ns; 8: 210 → 188 ns; 16: 312 → 294 ns; even from 64 |
| 2026-10-16 | `d7a26f5` | `gcd`: both new numbers of a Lehmer step in one pass (`mulSubMul₂`) from 32 limbs | `bgcd` 64 limbs: 24.9 → 23.5 µs; 256: 202 → 164 µs; 1024: 2.30 → 1.62 ms (5.8 → 4.1× `Nat`) |
| 2026-10-16 | `0824595` | Toom-4 by 2 for operands between 15:8 and 2:1, from 192 limbs | `1000 × 512`: 132 → 125 µs; `2000 × 1024`: 382 → 357 µs; `3900 × 2048`: 1062 → 988 µs |
| 2026-10-16 | `05083fa` | Toom-3 splits at a third of the longer operand when it fits the shorter | `1280 × 1024`: 298 → 244 µs; `1365 × 1024`: 326 → 257 µs; `2560 × 1024`: 603 → 494 µs |
| 2026-10-16 | `85166c7` | Toom-3 by 2 (`toom32`) between 4:3 and 2:1 | `1536 × 1024`: 406 → 247 µs; `3072 × 1024`: 814 → 495 µs; `768 × 512`: 132 → 88 µs |
| 2026-10-16 | `13709c1` | Lehmer's word steps: one division, Jebelean's condition, unboxed cofactors | `bgcd` 4: 0.93 → 0.70 µs; 16: 5.5 → 4.3 µs; 64: 30 → 25 µs |
| 2026-10-16 | `5029210` | up to 4 limbs by a 2-limb word on words alone (`divRem128`), quotient-only `div2` | `bdiv` 2: 159 → 86 ns; `div` 2: 151 → 137 ns |
| 2026-10-16 | `d7c6bf5` | Lehmer steps in one pass per number (`mulSubMul`), determinant on `Nat` | `bgcd` 4: 3.10 → 0.91 µs; 64: 82 → 30 µs; 1024: 3.8 → 2.3 ms |
| 2026-10-16 | `3841f4b` | `sqrt`: one Newton step and a square, not a second division | `bsqrt` 4: 1.85 → 1.32 µs; 256: 182 → 96 µs; 1024: 1.22 → 0.84 ms |
| 2026-10-16 | `889f498` | divide-and-conquer steps write the remainder, quotient and `R₁` with copies instead of passes | `div` 512: 149 → 141 µs; 1024: 451 → 427 µs; 4096: 3.83 → 3.65 ms |
| 2026-10-16 | `b2f548e` | Algorithm D in one array, quotient limbs in the freed limbs, no pairs per step | `div` 16: 659 → 541 ns; 64: 4.54 → 4.05 µs; 176: 28.2 → 26.5 µs |
| 2026-10-16 | `f3363a7` | divide-and-conquer division from 176 limbs (128) | `div` 128: 17.6 → 15.6 µs; 256: 56.1 → 51.1 µs; `bsqrt` 256: 227 → 212 µs |
| 2026-10-16 | `3cd490f` | `subMul1` with a biased borrow, one operation less on its chain | `div` 64: 4.88 → 4.53 µs; 96: 10.3 → 9.44 µs; 256: 57.1 → 55.3 µs |
| 2026-10-16 | `17e329b` | benchmark: `div` times the quotient alone on both sides | measurement only: its `Nat` column was two divisions, `/` and `%`, which halved the ratios (128 limbs: 4.9× → 12.2×) |
| 2026-10-16 | `ddfac06` | normalized dividend divided in place; `BigNat` divided by a word without its array | `bdiv` 2: 192 → 170 ns; 4: 337 → 275 ns; 16: 799 → 707 ns |
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
