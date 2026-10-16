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
| `add` | 5.31 | 0.56 | 0.57 | 0.56 | 0.60 | 0.66 | 0.81 | 1.10 | 1.50 | 1.34 | 1.68 | 1.85 | 1.77 |
| `sub` | 6.38 | 0.66 | 0.63 | 0.62 | 0.61 | 0.69 | 0.88 | 0.89 | 1.69 | 1.42 | 1.89 | 1.97 | 2.23 |
| `mul1` | 3.12 | 0.28 | 0.29 | 0.32 | 0.33 | 0.38 | 0.49 | 0.70 | 1.04 | 1.01 | 1.31 | 1.49 | 1.45 |
| `mul` | 3.75 | 0.55 | 0.56 | 1.02 | 1.77 | 2.92 | 4.38 | 5.08 | 5.45 | 5.53 | 6.28 | 7.12 | 7.30 |
| `sqr` | 3.87 | 0.54 | 0.55 | 0.90 | 1.42 | 1.94 | 2.56 | 3.00 | 3.24 | 3.36 | 4.01 | 4.65 | 4.68 |
| `div` | 4.46 | 2.91 | 2.19 | 2.78 | 3.44 | 5.14 | 7.51 | 10.14 | 9.71 | 8.55 | 8.48 | 8.34 | 9.48 |
| `shr` | 2.24 | 1.31 | 0.73 | 0.71 | 0.73 | 0.75 | 0.81 | 0.88 | 1.10 | 0.91 | 1.10 | 1.19 | 1.23 |
| `badd` | 1.72 | 0.37 | 0.84 | 0.81 | 0.86 | 0.90 | 1.05 | 1.31 | 1.64 | 1.40 | 1.79 |  |  |
| `bsub` | 1.84 | 1.19 | 0.93 | 0.90 | 0.87 | 0.99 | 1.15 | 1.22 | 1.91 | 1.55 | 2.00 |  |  |
| `bmul` | 1.77 | 0.59 | 0.77 | 1.23 | 1.95 | 3.02 | 4.43 | 5.13 | 5.42 | 5.53 | 6.32 |  |  |
| `bdiv` | 1.72 | 1.85 | 2.53 | 3.05 | 3.58 | 5.32 | 7.54 | 10.21 | 9.73 | 8.61 | 8.46 |  |  |
| `bgcd` | 0.45 | 1.33 | 4.12 | 3.61 | 3.52 | 3.78 | 4.07 | 4.65 | 5.50 | 6.16 | 5.78 |  |  |
| `bshl` | 0.73 | 0.94 | 0.76 | 0.72 | 0.74 | 0.76 | 0.83 | 0.97 | 1.21 | 0.93 | 1.25 |  |  |
| `bshr` | 1.70 | 0.37 | 0.78 | 0.78 | 0.79 | 0.81 | 0.86 | 0.94 | 1.14 | 0.85 | 1.10 |  |  |
| `bsqrt` | 1.04 | 0.39 | 0.89 | 1.63 | 2.12 | 1.68 | 2.18 | 1.61 | 1.48 | 1.18 | 1.06 |  |  |
| `btostr` | 0.92 | 0.85 | 0.06 | 0.05 | 0.05 | 0.05 | 0.06 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.24 | 1.01 | 0.19 | 0.11 | 0.09 | 0.08 | 0.08 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.18 | 0.78 | 2.25 | 5.17 | 11.03 | 23.71 | 46.64 | 91.13 | 163.77 | 199.57 | 289.54 |  |  |
| `bofnat` | 2.01 | 0.59 | 1.15 | 2.89 | 7.18 | 13.90 | 28.07 | 57.82 | 100.72 | 122.41 | 177.54 |  |  |

Time of Bignum:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 43.5 ns | 45.2 ns | 46.1 ns | 46.8 ns | 49.8 ns | 55.9 ns | 73.6 ns | 116 ns | 201 ns | 361 ns | 698 ns | 1.34 µs | 2.71 µs |
| `sub` | 55.3 ns | 56.1 ns | 53.7 ns | 54.2 ns | 61.9 ns | 64.8 ns | 87 ns | 138 ns | 235 ns | 422 ns | 809 ns | 1.57 µs | 3.15 µs |
| `mul1` | 31.1 ns | 31.7 ns | 34 ns | 37.5 ns | 39.4 ns | 45.8 ns | 65.3 ns | 106 ns | 200 ns | 364 ns | 710 ns | 1.41 µs | 2.59 µs |
| `mul` | 36 ns | 44.8 ns | 55.8 ns | 97 ns | 209 ns | 623 ns | 2.17 µs | 6.96 µs | 21.7 µs | 64.7 µs | 187 µs | 542 µs | 1.54 ms |
| `sqr` | 39.5 ns | 44.2 ns | 56 ns | 87.2 ns | 173 ns | 418 ns | 1.27 µs | 4.11 µs | 12.9 µs | 39.7 µs | 119 µs | 348 µs | 978 µs |
| `div` | 42.6 ns | 138 ns | 214 ns | 306 ns | 529 ns | 1.31 µs | 3.99 µs | 14.5 µs | 47.1 µs | 142 µs | 429 µs | 1.26 ms | 3.66 ms |
| `shr` | 18.4 ns | 53.9 ns | 54.7 ns | 54.7 ns | 55.5 ns | 58.2 ns | 65.2 ns | 80.7 ns | 120 ns | 189 ns | 334 ns | 600 ns | 1.2 µs |
| `badd` | 14.2 ns | 30.2 ns | 67.7 ns | 67.5 ns | 70.7 ns | 77 ns | 93.6 ns | 136 ns | 222 ns | 379 ns | 721 ns |  |  |
| `bsub` | 16 ns | 102 ns | 82.6 ns | 81.8 ns | 89.2 ns | 92.5 ns | 115 ns | 169 ns | 268 ns | 457 ns | 850 ns |  |  |
| `bmul` | 15.8 ns | 47.8 ns | 76.5 ns | 116 ns | 230 ns | 644 ns | 2.19 µs | 6.98 µs | 21.7 µs | 65.2 µs | 189 µs |  |  |
| `bdiv` | 15.4 ns | 87.4 ns | 248 ns | 336 ns | 555 ns | 1.34 µs | 4.01 µs | 14.6 µs | 47.1 µs | 142 µs | 428 µs |  |  |
| `bgcd` | 47.4 ns | 78.3 ns | 709 ns | 2.1 µs | 4.3 µs | 10.1 µs | 24.9 µs | 66.1 µs | 202 µs | 653 µs | 2.3 ms |  |  |
| `bshl` | 69.9 ns | 71.7 ns | 58.2 ns | 55.8 ns | 57.3 ns | 59.8 ns | 67.1 ns | 85.7 ns | 130 ns | 208 ns | 390 ns |  |  |
| `bshr` | 15.5 ns | 15.5 ns | 59.5 ns | 60.2 ns | 61.4 ns | 64 ns | 70 ns | 86.9 ns | 124 ns | 193 ns | 338 ns |  |  |
| `bsqrt` | 98 ns | 523 ns | 1.26 µs | 2.55 µs | 4.28 µs | 5.79 µs | 12.3 µs | 32.9 µs | 95.3 µs | 284 µs | 840 µs |  |  |
| `btostr` | 27 ns | 31.6 ns | 413 ns | 822 ns | 1.88 µs | 4.69 µs | 13.1 µs | 40.8 µs | 141 µs | 517 µs | 1.99 ms |  |  |
| `bofstr` | 338 ns | 463 ns | 760 ns | 1.32 µs | 2.62 µs | 5.15 µs | 10.6 µs | 23.7 µs | 59.8 µs | 166 µs | 515 µs |  |  |
| `btonat` | 11.3 ns | 89.4 ns | 254 ns | 600 ns | 1.28 µs | 2.75 µs | 5.55 µs | 11.3 µs | 22.6 µs | 46.3 µs | 94.1 µs |  |  |
| `bofnat` | 20.5 ns | 68.6 ns | 133 ns | 341 ns | 833 ns | 1.71 µs | 3.34 µs | 7.17 µs | 13.9 µs | 28.4 µs | 57.7 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.1–2.2× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4.4–7.3× behind from 64 limbs up, **squaring** 2.6–4.7×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits.
- **Division** is 7.5–10× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.3 of its
  own. Small `BigNat` divisions still pay a fixed cost (normalization, several arrays): 1.9–3.6×
  from 2 to 16 limbs.
- **`gcd`** is 3.5–6.2× behind from 4 limbs, Lehmer with word cofactors; GMP's subquadratic
  `hgcd` shows from a few hundred limbs.
- **`sqrt`** is 1.1–2.2× behind from 8 limbs, and faster up to 4; **decimal strings** are 10–20×
  faster than `Nat`, whose conversions work digit by digit.
- **Conversions to and from `Nat`** cost about one operation on `Nat` (some 40 ns) per two
  limbs, against one linear pass for `Nat` itself; they are a boundary, not arithmetic.

## History

Notable changes in performance, newest first. Times are for the sizes shown, on the machine
above; ratios before `15534f8` for `BigNat` rows were inflated by the hashing check.

| date | commit | change | effect |
|---|---|---|---|
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
