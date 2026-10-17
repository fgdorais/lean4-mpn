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
| `add` | 5.29 | 0.57 | 0.58 | 0.43 | 0.55 | 0.58 | 0.75 | 1.03 | 1.47 | 1.37 | 1.58 | 1.72 | 1.74 |
| `sub` | 5.86 | 0.55 | 0.58 | 0.60 | 0.57 | 0.69 | 0.84 | 0.86 | 1.65 | 1.41 | 1.80 | 1.88 | 2.10 |
| `mul1` | 3.19 | 0.23 | 0.28 | 0.25 | 0.30 | 0.36 | 0.45 | 0.57 | 0.99 | 0.94 | 1.27 | 1.32 | 1.44 |
| `mul` | 3.78 | 0.54 | 0.56 | 0.84 | 1.58 | 2.68 | 4.16 | 5.12 | 5.44 | 5.53 | 6.27 | 7.19 | 7.31 |
| `sqr` | 3.97 | 0.63 | 0.63 | 0.89 | 1.45 | 1.76 | 2.41 | 3.02 | 3.22 | 3.36 | 3.99 | 4.61 | 4.71 |
| `div` | 4.34 | 2.80 | 2.21 | 2.68 | 3.39 | 5.08 | 7.15 | 10.07 | 9.71 | 8.61 | 8.50 | 8.48 | 9.51 |
| `shr` | 1.99 | 1.20 | 0.59 | 0.63 | 0.67 | 0.68 | 0.72 | 0.80 | 1.06 | 0.83 | 0.96 | 1.06 | 1.10 |
| `badd` | 1.73 | 0.37 | 0.43 | 0.43 | 0.82 | 0.85 | 0.78 | 1.00 | 1.50 | 1.38 | 1.56 |  |  |
| `bsub` | 1.88 | 1.21 | 0.86 | 0.77 | 0.85 | 1.03 | 0.99 | 1.11 | 1.63 | 1.49 | 1.68 |  |  |
| `bmul` | 1.84 | 0.57 | 0.75 | 1.20 | 1.66 | 2.46 | 4.04 | 5.05 | 5.26 | 5.53 | 6.39 |  |  |
| `bdiv` | 1.70 | 1.77 | 2.37 | 2.89 | 3.44 | 4.36 | 6.92 | 10.00 | 9.69 | 8.56 | 8.45 |  |  |
| `bgcd` | 0.43 | 1.32 | 3.91 | 3.55 | 3.42 | 3.63 | 3.72 | 3.98 | 4.40 | 4.60 | 4.06 |  |  |
| `bshl` | 0.75 | 0.51 | 0.78 | 0.73 | 0.73 | 0.75 | 0.62 | 0.76 | 1.04 | 0.83 | 0.96 |  |  |
| `bshr` | 1.72 | 0.36 | 0.61 | 0.58 | 0.47 | 0.78 | 0.68 | 0.80 | 1.01 | 0.78 | 0.82 |  |  |
| `bsqrt` | 1.06 | 0.35 | 0.82 | 1.55 | 1.99 | 1.62 | 2.17 | 1.60 | 1.48 | 1.16 | 1.06 |  |  |
| `btostr` | 0.98 | 0.90 | 0.06 | 0.05 | 0.05 | 0.05 | 0.06 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.32 | 1.01 | 0.20 | 0.12 | 0.10 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.00 | 1.34 | 2.12 | 4.09 | 9.85 | 21.27 | 38.07 | 67.24 | 122.99 | 176.47 | 233.66 |  |  |
| `bofnat` | 1.81 | 0.59 | 0.89 | 2.56 | 5.89 | 10.92 | 22.62 | 38.57 | 78.77 | 98.97 | 148.00 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 43.6 ns | 45.4 ns | 46.4 ns | 46.5 ns | 49.4 ns | 56.3 ns | 74.2 ns | 115 ns | 203 ns | 365 ns | 701 ns | 1.35 µs | 2.71 µs |
| `sub` | 50.9 ns | 51.6 ns | 51.5 ns | 52.3 ns | 60.8 ns | 66.9 ns | 85.8 ns | 136 ns | 234 ns | 423 ns | 808 ns | 1.57 µs | 3.13 µs |
| `mul1` | 30 ns | 31.1 ns | 32.8 ns | 32.4 ns | 35.3 ns | 44.6 ns | 66 ns | 106 ns | 199 ns | 360 ns | 718 ns | 1.36 µs | 2.66 µs |
| `mul` | 36.1 ns | 44.7 ns | 55.9 ns | 95.6 ns | 209 ns | 621 ns | 2.19 µs | 7.01 µs | 21.8 µs | 65.2 µs | 188 µs | 543 µs | 1.55 ms |
| `sqr` | 40.9 ns | 51.8 ns | 63.2 ns | 92 ns | 178 ns | 422 ns | 1.27 µs | 4.14 µs | 12.9 µs | 39.6 µs | 119 µs | 347 µs | 984 µs |
| `div` | 41.7 ns | 142 ns | 221 ns | 305 ns | 526 ns | 1.31 µs | 4.02 µs | 14.6 µs | 47.3 µs | 142 µs | 430 µs | 1.28 ms | 3.71 ms |
| `shr` | 19.1 ns | 53.2 ns | 54.7 ns | 54.1 ns | 55.3 ns | 57.6 ns | 65.3 ns | 80.7 ns | 120 ns | 189 ns | 334 ns | 601 ns | 1.2 µs |
| `badd` | 14.3 ns | 30.2 ns | 66.6 ns | 65.5 ns | 69.8 ns | 76.4 ns | 94.7 ns | 136 ns | 223 ns | 382 ns | 721 ns |  |  |
| `bsub` | 16.4 ns | 105 ns | 84.3 ns | 84.9 ns | 91.5 ns | 98.8 ns | 116 ns | 169 ns | 266 ns | 459 ns | 842 ns |  |  |
| `bmul` | 16.4 ns | 47.7 ns | 82.1 ns | 122 ns | 240 ns | 652 ns | 2.22 µs | 7.02 µs | 21.9 µs | 65.2 µs | 191 µs |  |  |
| `bdiv` | 15.1 ns | 88.7 ns | 256 ns | 344 ns | 560 ns | 1.34 µs | 4.03 µs | 14.6 µs | 47.2 µs | 143 µs | 430 µs |  |  |
| `bgcd` | 47.4 ns | 78.6 ns | 685 ns | 2.08 µs | 4.14 µs | 9.7 µs | 22.7 µs | 56.5 µs | 162 µs | 488 µs | 1.61 ms |  |  |
| `bshl` | 73.8 ns | 73.9 ns | 61.7 ns | 58.7 ns | 59.9 ns | 63.3 ns | 70.2 ns | 88.4 ns | 134 ns | 212 ns | 395 ns |  |  |
| `bshr` | 15.7 ns | 15.7 ns | 61.9 ns | 61.9 ns | 64.6 ns | 66.5 ns | 72.5 ns | 88.6 ns | 127 ns | 197 ns | 340 ns |  |  |
| `bsqrt` | 98.1 ns | 517 ns | 1.28 µs | 2.58 µs | 4.31 µs | 5.83 µs | 12.3 µs | 32.7 µs | 95.3 µs | 284 µs | 838 µs |  |  |
| `btostr` | 30.4 ns | 32.3 ns | 441 ns | 868 ns | 1.93 µs | 4.76 µs | 13.2 µs | 41 µs | 141 µs | 520 µs | 1.99 ms |  |  |
| `bofstr` | 336 ns | 475 ns | 773 ns | 1.36 µs | 2.67 µs | 5.18 µs | 10.8 µs | 24 µs | 60.2 µs | 167 µs | 518 µs |  |  |
| `btonat` | 9.59 ns | 175 ns | 273 ns | 621 ns | 1.31 µs | 2.85 µs | 5.71 µs | 11.7 µs | 23 µs | 48 µs | 95.8 µs |  |  |
| `bofnat` | 18.5 ns | 93.3 ns | 131 ns | 335 ns | 837 ns | 1.67 µs | 3.37 µs | 7.02 µs | 14.1 µs | 28.9 µs | 59.2 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.1–2.2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4.2–7.3× behind from 64 limbs up, **squaring** 2.4–4.7×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits.
- **Division** is 7–10× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.3 of its
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
| 2026-10-16 | (uncommitted) | Comba's columns from 32 limbs add whole products and count the wraps of one sum (`colLoopW`) | `mul` 64–256 limbs −5%, 1024: 188 → 174 µs, 4096: 1.55 → 1.39 ms; `div` 1024–4096 −4 to −7% |
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
