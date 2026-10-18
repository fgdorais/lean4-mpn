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
noise. Each time is the median of five trials, and the last two columns, `±MPN` and `±Nat`, are
the spread of those trials (sample standard deviation over mean, from `Batteries.RunningStats`):
usually ±0.1–2%, the noise within one run. Between builds the noise is larger: below 64 limbs,
changing the library moves the code of both columns in the binary, and either side can shift by
5–20% from that alone (the `Nat` column too), so compare the times of the same column across runs
rather than the ratios.

## How to read the tables

- **Sizes** are in 32-bit limbs. A row of 256 limbs is about 8,200 bits, or 2,500 decimal digits.
- **The `Nat` column** is Lean's `Nat`: GMP with 64-bit limbs and assembly, behind a wrapper that
  copies operands and results. Below about 64 limbs that wrapper dominates, which is why the
  library is often faster there. A ratio is `MPN / Nat`, so below 1 means faster than `Nat`.
- **One limb** compares an array with `Nat`'s unboxed small values, which need no allocation. The
  limb-level operations always allocate an array, so their 1-limb ratios are high. `MPN.Nat` has a
  word fast path for values below `2⁶⁴`, which is what its 1- and 2-limb rows measure.
- **Results are checked in O(1)** on both sides, so the time is the operation alone. (Before
  `15534f8`, `MPN.Nat` results were hashed, which inflated the large `b*` rows 2–4×.)
- **Machine:** AMD Ryzen 5 5600X (Zen 3), Linux 7.1, Lean `v4.36.0-rc1`, lean4-scalar-arrays
  `8ae4933`. Commit `b4e717f`, 2026-10-17.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | Comba schoolbook, Karatsuba from 64, Toom-4 from 416 (Toom-3 from 480 when Toom-4 is set higher); Toom-4 by 3 from 176 between 6:5 and 15:8, Toom-3 by 2 from 128 between 4:3 and 15:8 below that, Toom-4 by 2 from 224 up to 2:1 |
| `sqr` | `sqr` | `n` limbs | Comba square, Karatsuba from 96, Toom-4 from 576 (Toom-3 from 720 when Toom-4 is set higher) |
| `div` | `div`, the quotient | `2n` by `n` limbs | `divRem1`, `divRem2`, Algorithm D, Burnikel–Ziegler from 176 |
| `shr` | `shiftRight` by 37 bits | `n` limbs | one pass in place |
| `badd` … `bdiv` | `MPN.Nat` `+ - * /` | as above (`bdiv`: `2n` by `n`) | word fast path, then as above |
| `bgcd` | `MPN.Nat.gcd` | `n` and `n` limbs | Lehmer with word cofactors, Euclid on words |
| `bshl`, `bshr` | `MPN.Nat` `<<<`, `>>>` 37 | `n` limbs | one pass in place |
| `bsqrt` | `MPN.Nat.sqrt` | `2n` limbs | Newton at growing precision |
| `btostr` | `toString` | `n` limbs | chunks of 9 digits, `divRem1` by `10⁹` |
| `bofstr` | `MPN.Nat.ofString?` | the digits of `n` limbs | a fold over the characters, 9 digits per chunk |
| `btonat` | `MPN.Nat.toNat` | `n` limbs | by halves, joined with shifts; `Nat` column: `x + 1` |
| `bofnat` | `MPN.Nat.ofNat` | `n` limbs | by halves, then 64 bits at a time; `Nat` column: `x + 1` |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 4.79 | 0.49 | 0.46 | 0.39 | 0.50 | 0.54 | 0.64 | 0.87 | 1.30 | 1.16 | 1.39 | 1.43 | 1.55 |
| `sub` | 5.94 | 0.50 | 0.58 | 0.62 | 0.60 | 0.67 | 0.75 | 0.79 | 1.42 | 1.09 | 1.49 | 1.48 | 1.60 |
| `mul1` | 3.17 | 0.22 | 0.28 | 0.29 | 0.32 | 0.37 | 0.49 | 0.64 | 0.96 | 0.97 | 1.09 | 1.26 | 1.34 |
| `mul` | 4.87 | 0.56 | 0.59 | 0.95 | 1.73 | 2.70 | 4.11 | 5.02 | 5.35 | 5.26 | 5.95 | 6.66 | 6.86 |
| `sqr` | 4.26 | 0.53 | 0.55 | 0.87 | 1.31 | 1.78 | 2.35 | 2.89 | 3.12 | 3.25 | 3.84 | 4.41 | 4.48 |
| `div` | 4.31 | 1.97 | 2.26 | 2.63 | 3.00 | 4.48 | 6.29 | 8.34 | 8.52 | 7.93 | 7.91 | 7.88 | 8.91 |
| `shr` | 2.00 | 1.24 | 0.67 | 0.66 | 0.60 | 0.64 | 0.68 | 0.84 | 1.07 | 0.81 | 0.99 | 1.16 | 1.21 |
| `badd` | 1.81 | 0.38 | 0.81 | 0.82 | 0.88 | 0.92 | 1.05 | 1.23 | 1.49 | 1.27 | 1.49 |  |  |
| `bsub` | 1.93 | 1.14 | 1.01 | 0.95 | 0.95 | 1.06 | 1.19 | 1.15 | 1.62 | 1.31 | 1.59 |  |  |
| `bmul` | 1.75 | 0.59 | 0.82 | 1.30 | 1.92 | 2.95 | 4.32 | 5.17 | 5.42 | 5.31 | 5.96 |  |  |
| `bdiv` | 1.72 | 1.89 | 2.66 | 3.23 | 3.65 | 5.08 | 6.55 | 8.34 | 8.53 | 7.89 | 7.88 |  |  |
| `bgcd` | 0.46 | 1.30 | 4.02 | 3.72 | 3.56 | 3.75 | 3.78 | 4.10 | 4.53 | 4.75 | 4.08 |  |  |
| `bshl` | 0.75 | 1.00 | 0.81 | 0.78 | 0.81 | 0.82 | 0.89 | 1.05 | 1.29 | 0.99 | 1.31 |  |  |
| `bshr` | 1.74 | 0.39 | 0.78 | 0.77 | 0.79 | 0.79 | 0.86 | 0.90 | 1.13 | 0.90 | 1.10 |  |  |
| `bsqrt` | 1.06 | 0.39 | 0.91 | 1.67 | 2.15 | 1.67 | 2.10 | 1.44 | 1.34 | 1.09 | 0.98 |  |  |
| `btostr` | 0.91 | 0.85 | 0.06 | 0.05 | 0.04 | 0.05 | 0.06 | 0.08 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.31 | 1.01 | 0.19 | 0.11 | 0.09 | 0.09 | 0.08 | 0.09 | 0.09 | 0.09 | 0.09 |  |  |
| `btonat` | 0.98 | 0.80 | 2.24 | 5.32 | 11.32 | 24.26 | 47.97 | 93.50 | 165.22 | 203.49 | 284.43 |  |  |
| `bofnat` | 1.70 | 0.60 | 1.20 | 2.96 | 7.51 | 15.04 | 29.33 | 58.63 | 104.29 | 131.30 | 183.23 |  |  |

Time of MPN:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 38.4 ns | 40 ns | 40.4 ns | 41.4 ns | 45.2 ns | 51.7 ns | 68.6 ns | 103 ns | 178 ns | 312 ns | 591 ns | 1.13 µs | 2.26 µs |
| `sub` | 51.5 ns | 55.2 ns | 53.2 ns | 55.8 ns | 64.3 ns | 67.6 ns | 85.2 ns | 124 ns | 206 ns | 337 ns | 629 ns | 1.23 µs | 2.33 µs |
| `mul1` | 30.9 ns | 31.7 ns | 32.5 ns | 33.3 ns | 37.3 ns | 45.2 ns | 65.3 ns | 105 ns | 198 ns | 352 ns | 664 ns | 1.27 µs | 2.5 µs |
| `mul` | 44.4 ns | 46.5 ns | 59.2 ns | 98.5 ns | 211 ns | 630 ns | 2.17 µs | 6.93 µs | 21.5 µs | 62.1 µs | 179 µs | 506 µs | 1.44 ms |
| `sqr` | 39.8 ns | 43.1 ns | 53.9 ns | 84.6 ns | 171 ns | 403 ns | 1.24 µs | 3.99 µs | 12.5 µs | 38.3 µs | 114 µs | 332 µs | 936 µs |
| `div` | 41.4 ns | 97.5 ns | 225 ns | 318 ns | 543 ns | 1.24 µs | 3.46 µs | 12.1 µs | 41.4 µs | 130 µs | 400 µs | 1.19 ms | 3.45 ms |
| `shr` | 20.2 ns | 52.5 ns | 53.5 ns | 53.7 ns | 55.2 ns | 56.8 ns | 63.6 ns | 80.6 ns | 121 ns | 192 ns | 335 ns | 601 ns | 1.19 µs |
| `badd` | 14.5 ns | 30.3 ns | 64.6 ns | 66.9 ns | 71.4 ns | 80.5 ns | 93.7 ns | 128 ns | 200 ns | 333 ns | 615 ns |  |  |
| `bsub` | 16.8 ns | 103 ns | 86.3 ns | 85.3 ns | 97.5 ns | 101 ns | 120 ns | 157 ns | 233 ns | 378 ns | 669 ns |  |  |
| `bmul` | 16 ns | 48.1 ns | 80.9 ns | 121 ns | 234 ns | 650 ns | 2.22 µs | 7.13 µs | 21.8 µs | 62.7 µs | 180 µs |  |  |
| `bdiv` | 15.4 ns | 89.2 ns | 254 ns | 349 ns | 573 ns | 1.28 µs | 3.5 µs | 12.1 µs | 41.8 µs | 131 µs | 401 µs |  |  |
| `bgcd` | 47.4 ns | 79 ns | 699 ns | 2.18 µs | 4.34 µs | 10.1 µs | 23.4 µs | 58.7 µs | 167 µs | 504 µs | 1.65 ms |  |  |
| `bshl` | 74.6 ns | 74.9 ns | 61.1 ns | 59.6 ns | 61.3 ns | 64 ns | 73.3 ns | 93.2 ns | 139 ns | 214 ns | 398 ns |  |  |
| `bshr` | 16.3 ns | 16.2 ns | 60.8 ns | 61.1 ns | 61.9 ns | 63.6 ns | 71.6 ns | 87.3 ns | 131 ns | 198 ns | 344 ns |  |  |
| `bsqrt` | 98 ns | 528 ns | 1.29 µs | 2.6 µs | 4.35 µs | 5.81 µs | 11.8 µs | 29.5 µs | 86.6 µs | 264 µs | 782 µs |  |  |
| `btostr` | 26.1 ns | 30.6 ns | 405 ns | 820 ns | 1.81 µs | 4.53 µs | 12.9 µs | 40.4 µs | 140 µs | 522 µs | 1.99 ms |  |  |
| `bofstr` | 319 ns | 466 ns | 760 ns | 1.32 µs | 2.53 µs | 5.12 µs | 10.7 µs | 23.9 µs | 59.4 µs | 163 µs | 493 µs |  |  |
| `btonat` | 9.21 ns | 91 ns | 253 ns | 606 ns | 1.29 µs | 2.79 µs | 5.66 µs | 11.5 µs | 22.8 µs | 46.6 µs | 95 µs |  |  |
| `bofnat` | 17.7 ns | 68.5 ns | 137 ns | 343 ns | 879 ns | 1.76 µs | 3.52 µs | 7.27 µs | 14.6 µs | 30.2 µs | 61.2 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–1.6× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4.1–6.9× behind from 64 limbs up, **squaring** 2.4–4.5×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits.
- **Division** is 6.3–8.9× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.4 of its
  own. Small `MPN.Nat` divisions still pay a fixed cost (normalization, several arrays): 1.9–3.7×
  from 2 to 16 limbs. Division by a word of two limbs costs about 6.5 ns per limb, 3.6× GMP's
  at 256 limbs and even with it at 5.
- **`gcd`** is 3.6–4.8× behind from 4 limbs, Lehmer with word cofactors and both new numbers in
  one pass; GMP's subquadratic `hgcd` would show from a few hundred limbs.
- **`sqrt`** is 1.0–2.2× behind from 8 limbs, even at 1024, and faster up to 4; **decimal
  strings** are 10–20× faster than `Nat`, whose conversions work digit by digit.
- **On an Apple M2** (`b4e717f`), the gaps are wider: the linear operations are within 1.2–2.3×
  from 1024 limbs, multiplication 4.7–8.3× from 64 limbs, squaring 2.2–4.3× and division 5.6–11×.
- **Conversions to and from `Nat`** cost about one operation on `Nat` (some 40 ns) per two
  limbs, against one linear pass for `Nat` itself; they are a boundary, not arithmetic.

## History

Notable changes in performance, newest first. Times are for the sizes shown, on the machine
above; ratios before `15534f8` for `MPN.Nat` rows were inflated by the hashing check.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-17 | `d93bc5f` | Toom-4 and Toom-4 by 3 with natural-number points, from 416 and 176 limbs, with fused `r ∓ a v` passes | `mul` 1024 limbs: 179 → 175 µs, 2048: 505 → 479 µs, 4096: 1.43 → 1.31 ms (−8%); `div` 4096: −2%; shapes near 4:3 6–19% faster (`683 × 512`: 85.0 → 71.4 µs) |
| 2026-10-17 | `f5c9193` | Subtraction adds the complement with `addWithCarryWord`, keeping `1` minus the borrow (`subWithCarryWord`): the compare and flag read of the sign-bit borrow made a longer chain on AArch64 | `sub` 1024 limbs: 602 → 634 ns (+5%), 4096: +4% on Zen 3; on an Apple M2 (bench at `b4e717f`): `sub` 1024 limbs 1.11 µs → 809 ns, 4096: 4.31 → 3.11 µs (1.39×, level with `add`), `bsub` 1024: 1.15 µs → 854 ns. The carry-last steps confirmed on the M2 at `ecc44f7` vs `ac4db80`, 1024 limbs: `mul1` 1.55 µs → 810 ns, `add` 1.06 µs → 780 ns, `div` 591 → 441 µs, `bsqrt` 1.10 ms → 796 µs, `sub` only −11% |
| 2026-10-17 | `87d6d31` | The carry joins last in the steps of subtraction, `subMul1`, Karatsuba's combination, `mulSubMul` and the square's diagonal | `sub` 1024 limbs: 814 → 604 ns (−26%); `div` 64 limbs: 4.10 → 3.46 µs (−16%), 256: −13%, 1024: −6%; `sqr` 4096: −4% |
| 2026-10-17 | `55f00cc` | The carry joins last in `mulAddAdd` and `addWithCarryWord` (the steps of `mul1`, `mulRow` and addition), so that LLVM keeps it off the multiplication | `add` 1024 limbs: 700 → 590 ns (−16%), `mul1` even, on Zen 3; on an Apple M2 (prototype): `mul1` 1.9× and `add` 1.3× faster |
| 2026-10-16 | `7ecbcb9` | Division by two limbs with Möller and Granlund's 3-by-2 step and a precomputed reciprocal, checked without branches (`div32Step`) | `MPN.Nat` divided by `10¹⁸` (no bench row): 5 limbs 149 → 108 ns, 16: 294 → 177 ns, 64: 974 → 494 ns, 256: 3.81 → 1.75 µs (8.2 → 3.6× `Nat`) |
| 2026-10-16 | `1371203` | Comba's columns from 32 limbs add whole products and count the wraps of one sum (`colLoopW`) | `mul` 64–256 limbs −5%, 1024: 188 → 174 µs, 4096: 1.55 → 1.39 ms; `div` 1024–4096 −4 to −7% |
| 2026-10-16 | `5306ce2` | Division by two limbs normalizes the dividend on the fly instead of a shifted copy (`divRem2`, `div2`) | `MPN.Nat` divided by `10¹⁸` (no bench row): 5 limbs 180 → 149 ns; 8: 210 → 188 ns; 16: 312 → 294 ns; even from 64 |
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
| 2026-10-16 | `ddfac06` | normalized dividend divided in place; `MPN.Nat` divided by a word without its array | `bdiv` 2: 192 → 170 ns; 4: 337 → 275 ns; 16: 799 → 707 ns |
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
