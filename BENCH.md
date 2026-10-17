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
| `add` | 5.35 | 0.55 | 0.55 | 0.54 | 0.58 | 0.63 | 0.79 | 1.06 | 1.46 | 1.33 | 1.68 | 1.86 | 1.74 |
| `sub` | 5.71 | 0.59 | 0.60 | 0.63 | 0.58 | 0.68 | 0.86 | 0.88 | 1.69 | 1.41 | 1.91 | 1.96 | 2.19 |
| `mul1` | 3.27 | 0.26 | 0.27 | 0.27 | 0.29 | 0.35 | 0.49 | 0.69 | 1.03 | 0.99 | 1.33 | 1.46 | 1.52 |
| `mul` | 3.53 | 0.54 | 0.57 | 1.02 | 1.76 | 2.74 | 4.06 | 4.87 | 5.16 | 5.12 | 5.82 | 6.42 | 6.51 |
| `sqr` | 4.11 | 0.52 | 0.54 | 0.87 | 1.44 | 1.92 | 2.46 | 2.98 | 3.22 | 3.37 | 3.93 | 4.58 | 4.67 |
| `div` | 4.66 | 2.16 | 2.27 | 2.57 | 3.28 | 5.06 | 7.36 | 10.00 | 9.57 | 8.30 | 8.09 | 7.88 | 8.91 |
| `shr` | 2.18 | 1.33 | 0.78 | 0.76 | 0.79 | 0.79 | 0.82 | 0.92 | 1.02 | 0.95 | 1.10 | 1.20 | 1.14 |
| `badd` | 1.73 | 0.36 | 0.83 | 0.80 | 0.86 | 0.92 | 1.03 | 1.25 | 1.60 | 1.40 | 1.76 |  |  |
| `bsub` | 1.89 | 1.30 | 1.04 | 1.02 | 0.96 | 1.11 | 1.24 | 1.27 | 1.94 | 1.57 | 2.02 |  |  |
| `bmul` | 1.72 | 0.58 | 0.83 | 1.30 | 2.04 | 2.88 | 4.12 | 4.86 | 5.21 | 5.15 | 5.77 |  |  |
| `bdiv` | 1.70 | 1.96 | 2.58 | 2.84 | 3.46 | 5.26 | 7.57 | 10.00 | 9.55 | 8.31 | 8.09 |  |  |
| `bgcd` | 0.45 | 1.30 | 4.10 | 3.63 | 3.46 | 3.68 | 3.81 | 4.05 | 4.42 | 4.62 | 4.09 |  |  |
| `bshl` | 0.83 | 1.11 | 0.89 | 0.83 | 0.86 | 0.89 | 0.95 | 1.07 | 1.26 | 0.92 | 1.27 |  |  |
| `bshr` | 1.70 | 0.38 | 0.91 | 0.88 | 0.89 | 0.91 | 0.90 | 0.99 | 1.15 | 0.85 | 1.11 |  |  |
| `bsqrt` | 1.06 | 0.40 | 0.90 | 1.61 | 2.10 | 1.66 | 2.17 | 1.59 | 1.45 | 1.15 | 1.02 |  |  |
| `btostr` | 0.92 | 0.85 | 0.05 | 0.04 | 0.04 | 0.05 | 0.06 | 0.07 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.50 | 1.05 | 0.19 | 0.11 | 0.09 | 0.08 | 0.08 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.07 | 0.77 | 2.22 | 5.33 | 11.98 | 25.98 | 49.08 | 94.35 | 166.43 | 197.92 | 292.71 |  |  |
| `bofnat` | 2.03 | 0.60 | 1.12 | 2.86 | 7.33 | 14.41 | 28.74 | 57.10 | 98.63 | 122.50 | 182.98 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 44.1 ns | 45.6 ns | 46.3 ns | 46.5 ns | 49.4 ns | 56 ns | 74 ns | 115 ns | 203 ns | 363 ns | 704 ns | 1.35 µs | 2.7 µs |
| `sub` | 50.9 ns | 51.9 ns | 52 ns | 55.7 ns | 61.6 ns | 63 ns | 83.8 ns | 135 ns | 233 ns | 423 ns | 812 ns | 1.58 µs | 3.15 µs |
| `mul1` | 30.5 ns | 31.1 ns | 32.6 ns | 32.3 ns | 35.3 ns | 43.8 ns | 66.2 ns | 107 ns | 200 ns | 361 ns | 725 ns | 1.38 µs | 2.76 µs |
| `mul` | 35.2 ns | 44.2 ns | 55.6 ns | 94.9 ns | 208 ns | 586 ns | 2.06 µs | 6.67 µs | 20.6 µs | 60.4 µs | 174 µs | 488 µs | 1.38 ms |
| `sqr` | 39.3 ns | 42.9 ns | 53.1 ns | 81.9 ns | 169 ns | 410 ns | 1.25 µs | 4.08 µs | 12.8 µs | 39.4 µs | 119 µs | 346 µs | 975 µs |
| `div` | 41.5 ns | 103 ns | 217 ns | 298 ns | 515 ns | 1.29 µs | 3.95 µs | 14.4 µs | 46.4 µs | 137 µs | 410 µs | 1.19 ms | 3.44 ms |
| `shr` | 19.9 ns | 54.2 ns | 58 ns | 58.2 ns | 59.9 ns | 62.7 ns | 68.4 ns | 84.5 ns | 123 ns | 195 ns | 339 ns | 608 ns | 1.21 µs |
| `badd` | 14.3 ns | 30.1 ns | 71.3 ns | 70.1 ns | 74.7 ns | 82.4 ns | 96.4 ns | 136 ns | 223 ns | 382 ns | 723 ns |  |  |
| `bsub` | 16.8 ns | 115 ns | 91.4 ns | 92.2 ns | 103 ns | 104 ns | 123 ns | 177 ns | 273 ns | 466 ns | 853 ns |  |  |
| `bmul` | 15.7 ns | 48.4 ns | 81.6 ns | 124 ns | 243 ns | 616 ns | 2.1 µs | 6.66 µs | 20.7 µs | 60.3 µs | 173 µs |  |  |
| `bdiv` | 15.1 ns | 94.7 ns | 249 ns | 329 ns | 546 ns | 1.33 µs | 4.04 µs | 14.4 µs | 46.4 µs | 138 µs | 412 µs |  |  |
| `bgcd` | 47.2 ns | 77.7 ns | 710 ns | 2.11 µs | 4.19 µs | 9.82 µs | 23.3 µs | 57.5 µs | 164 µs | 494 µs | 1.64 ms |  |  |
| `bshl` | 78.1 ns | 82.5 ns | 65.9 ns | 62.9 ns | 65.2 ns | 68.7 ns | 75.5 ns | 94 ns | 135 ns | 212 ns | 397 ns |  |  |
| `bshr` | 15.5 ns | 15.5 ns | 68.7 ns | 68.5 ns | 68.9 ns | 73.2 ns | 76.1 ns | 92.7 ns | 130 ns | 200 ns | 345 ns |  |  |
| `bsqrt` | 98.9 ns | 543 ns | 1.32 µs | 2.59 µs | 4.34 µs | 5.81 µs | 12.3 µs | 32.6 µs | 93.4 µs | 280 µs | 811 µs |  |  |
| `btostr` | 26 ns | 31.5 ns | 399 ns | 791 ns | 1.82 µs | 4.56 µs | 12.9 µs | 40.3 µs | 140 µs | 517 µs | 1.99 ms |  |  |
| `bofstr` | 350 ns | 490 ns | 780 ns | 1.34 µs | 2.57 µs | 5.15 µs | 10.7 µs | 23.7 µs | 59.4 µs | 166 µs | 514 µs |  |  |
| `btonat` | 10.2 ns | 88.9 ns | 253 ns | 624 ns | 1.39 µs | 3.04 µs | 5.84 µs | 11.7 µs | 23.3 µs | 47.5 µs | 96.3 µs |  |  |
| `bofnat` | 21.1 ns | 68.8 ns | 130 ns | 335 ns | 850 ns | 1.7 µs | 3.42 µs | 7.08 µs | 14.4 µs | 29.4 µs | 60.2 µs |  |  |

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
  from 2 to 16 limbs. Division by a word of two limbs costs about 6.5 ns per limb, 3.6× GMP's
  at 256 limbs and even with it at 5.
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
| 2026-10-16 | `7ecbcb9` | Division by two limbs with Möller and Granlund's 3-by-2 step and a precomputed reciprocal, checked without branches (`div32Step`) | `BigNat` divided by `10¹⁸` (no bench row): 5 limbs 149 → 108 ns, 16: 294 → 177 ns, 64: 974 → 494 ns, 256: 3.81 → 1.75 µs (8.2 → 3.6× `Nat`) |
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
