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
  `8ae4933`. Commit `7c484a8`, 2026-10-18.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | Comba schoolbook, Karatsuba from 64, Toom-4 from 416 (Toom-3 from 480 when Toom-4 is set higher), Toom-6 from 1344; Toom-4 by 3 from 176 between 6:5 and 15:8, Toom-3 by 2 from 128 between 4:3 and 15:8 below that, Toom-4 by 2 from 224 up to 2:1; the FFT from 32768 (beyond the table) |
| `sqr` | `sqr` | `n` limbs | Comba square, Karatsuba from 96, Toom-4 from 576 (Toom-3 from 720 when Toom-4 is set higher), Toom-6 from 1792, the FFT from 28672 (beyond the table) |
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
| `add` | 4.95 | 0.56 | 0.55 | 0.53 | 0.58 | 0.68 | 0.80 | 1.02 | 1.35 | 1.18 | 1.45 | 1.56 | 1.49 |
| `sub` | 5.96 | 0.63 | 0.59 | 0.58 | 0.55 | 0.68 | 0.81 | 0.76 | 1.40 | 1.13 | 1.47 | 1.52 | 1.69 |
| `mul1` | 3.12 | 0.28 | 0.29 | 0.28 | 0.31 | 0.37 | 0.50 | 0.72 | 1.04 | 1.07 | 1.28 | 1.43 | 1.48 |
| `mul` | 4.33 | 0.64 | 0.65 | 1.10 | 1.89 | 2.80 | 4.22 | 4.81 | 5.12 | 5.09 | 5.55 | 5.81 | 5.38 |
| `sqr` | 4.37 | 0.52 | 0.51 | 0.85 | 1.41 | 1.92 | 2.54 | 3.02 | 3.26 | 3.28 | 3.68 | 4.16 | 3.96 |
| `div` | 4.21 | 2.14 | 2.40 | 2.97 | 3.49 | 4.92 | 6.52 | 8.33 | 8.42 | 7.70 | 7.68 | 7.50 | 8.33 |
| `shr` | 1.79 | 1.33 | 0.80 | 0.77 | 0.79 | 0.81 | 0.84 | 0.90 | 1.13 | 0.92 | 0.98 | 1.11 | 1.15 |
| `badd` | 1.81 | 0.38 | 0.82 | 0.81 | 0.86 | 0.92 | 1.05 | 1.23 | 1.50 | 1.27 | 1.53 |  |  |
| `bsub` | 1.93 | 1.21 | 0.95 | 0.92 | 0.85 | 1.00 | 1.12 | 1.10 | 1.63 | 1.29 | 1.59 |  |  |
| `bmul` | 1.77 | 0.63 | 0.90 | 1.37 | 2.09 | 2.91 | 4.25 | 4.86 | 5.16 | 5.15 | 5.58 |  |  |
| `bdiv` | 1.45 | 1.88 | 2.66 | 3.23 | 3.67 | 5.06 | 6.59 | 8.33 | 8.44 | 7.76 | 7.66 |  |  |
| `bgcd` | 0.46 | 1.32 | 4.23 | 3.84 | 3.73 | 3.90 | 3.99 | 4.23 | 4.62 | 4.80 | 4.16 |  |  |
| `bshl` | 0.79 | 1.15 | 0.81 | 0.83 | 0.86 | 0.89 | 1.02 | 1.05 | 1.25 | 0.98 | 1.28 |  |  |
| `bshr` | 1.72 | 0.41 | 0.94 | 0.92 | 0.89 | 0.93 | 0.96 | 0.98 | 1.13 | 0.90 | 1.11 |  |  |
| `bsqrt` | 1.07 | 0.38 | 0.92 | 1.71 | 2.28 | 1.71 | 2.14 | 1.46 | 1.36 | 1.08 | 0.95 |  |  |
| `btostr` | 0.89 | 0.83 | 0.06 | 0.05 | 0.05 | 0.05 | 0.06 | 0.07 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.37 | 0.98 | 0.19 | 0.11 | 0.09 | 0.08 | 0.08 | 0.09 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.05 | 0.80 | 2.27 | 5.26 | 11.40 | 24.26 | 48.38 | 95.08 | 167.88 | 203.93 | 290.80 |  |  |
| `bofnat` | 1.73 | 0.59 | 1.18 | 2.97 | 7.25 | 14.22 | 28.05 | 56.15 | 102.92 | 124.57 | 180.98 |  |  |

Time of MPN:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 40.6 ns | 43.9 ns | 43.1 ns | 43.1 ns | 46.5 ns | 56.6 ns | 71.1 ns | 105 ns | 179 ns | 313 ns | 598 ns | 1.14 µs | 2.28 µs |
| `sub` | 53.2 ns | 54.5 ns | 51 ns | 50.9 ns | 58.8 ns | 62.6 ns | 79.1 ns | 119 ns | 194 ns | 338 ns | 623 ns | 1.21 µs | 2.4 µs |
| `mul1` | 30.5 ns | 31.7 ns | 33 ns | 32.7 ns | 35.9 ns | 44.6 ns | 64.7 ns | 108 ns | 201 ns | 369 ns | 705 ns | 1.35 µs | 2.65 µs |
| `mul` | 42.3 ns | 51.2 ns | 63.1 ns | 103 ns | 221 ns | 593 ns | 2.08 µs | 6.59 µs | 20.5 µs | 59.6 µs | 167 µs | 441 µs | 1.13 ms |
| `sqr` | 46.3 ns | 41.9 ns | 51.4 ns | 80.4 ns | 166 ns | 411 ns | 1.26 µs | 4.14 µs | 12.9 µs | 39.4 µs | 110 µs | 313 µs | 828 µs |
| `div` | 40.2 ns | 102 ns | 232 ns | 321 ns | 544 ns | 1.24 µs | 3.46 µs | 12 µs | 40.9 µs | 127 µs | 387 µs | 1.14 ms | 3.24 ms |
| `shr` | 19.2 ns | 55.8 ns | 59 ns | 59.2 ns | 60.6 ns | 62.7 ns | 67.4 ns | 82.1 ns | 121 ns | 192 ns | 338 ns | 604 ns | 1.2 µs |
| `badd` | 14.9 ns | 30 ns | 64.1 ns | 65.7 ns | 68.9 ns | 76.6 ns | 92.9 ns | 127 ns | 199 ns | 331 ns | 617 ns |  |  |
| `bsub` | 17.4 ns | 106 ns | 82.6 ns | 82.6 ns | 91.2 ns | 92.8 ns | 111 ns | 155 ns | 226 ns | 371 ns | 664 ns |  |  |
| `bmul` | 16.2 ns | 50.3 ns | 87.1 ns | 126 ns | 245 ns | 620 ns | 2.1 µs | 6.66 µs | 20.6 µs | 60.2 µs | 168 µs |  |  |
| `bdiv` | 14.8 ns | 91.3 ns | 261 ns | 352 ns | 572 ns | 1.28 µs | 3.5 µs | 12 µs | 41 µs | 128 µs | 389 µs |  |  |
| `bgcd` | 47 ns | 78.6 ns | 731 ns | 2.24 µs | 4.55 µs | 10.4 µs | 24.4 µs | 60.1 µs | 170 µs | 514 µs | 1.67 ms |  |  |
| `bshl` | 74.9 ns | 89.3 ns | 61.8 ns | 62.7 ns | 65.9 ns | 68.7 ns | 79.9 ns | 91.2 ns | 134 ns | 212 ns | 397 ns |  |  |
| `bshr` | 17.4 ns | 17.1 ns | 70.4 ns | 70.5 ns | 69.9 ns | 74.9 ns | 77.2 ns | 89.5 ns | 127 ns | 197 ns | 342 ns |  |  |
| `bsqrt` | 98.6 ns | 509 ns | 1.29 µs | 2.72 µs | 4.62 µs | 5.93 µs | 12 µs | 29.8 µs | 87.6 µs | 261 µs | 761 µs |  |  |
| `btostr` | 25.4 ns | 29.8 ns | 404 ns | 840 ns | 1.88 µs | 4.68 µs | 13 µs | 40.4 µs | 140 µs | 518 µs | 1.98 ms |  |  |
| `bofstr` | 318 ns | 454 ns | 739 ns | 1.29 µs | 2.53 µs | 5.11 µs | 10.9 µs | 24.3 µs | 60.7 µs | 167 µs | 512 µs |  |  |
| `btonat` | 10 ns | 91.2 ns | 256 ns | 600 ns | 1.3 µs | 2.79 µs | 5.66 µs | 11.6 µs | 23 µs | 46.7 µs | 94.8 µs |  |  |
| `bofnat` | 17.3 ns | 67.2 ns | 134 ns | 342 ns | 834 ns | 1.65 µs | 3.31 µs | 6.85 µs | 14.1 µs | 28.9 µs | 59 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–1.6× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 4.2–5.8× behind from 64 limbs up, **squaring** 2.5–4.2×. That is mostly
  structural: 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply. Algorithm thresholds are close to GMP's in bits. Beyond the table,
  Toom-6 from 1344 limbs (1792 for squares) and the FFT from 32768 (28672), 29% faster than
  Toom-4 at 65536.
- **Division** is 6.5–8.4× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.4 of its
  own. Small `MPN.Nat` divisions still pay a fixed cost (normalization, several arrays): 1.9–3.7×
  from 2 to 16 limbs. Division by a word of two limbs costs about 6.5 ns per limb, 3.6× GMP's
  at 256 limbs and even with it at 5.
- **`gcd`** is 3.6–4.8× behind from 4 limbs, Lehmer with word cofactors and both new numbers in
  one pass; GMP's subquadratic `hgcd` would show from a few hundred limbs.
- **`sqrt`** is 1.0–2.3× behind from 8 limbs, even at 1024, and faster up to 4; **decimal
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
| 2026-10-18 | `7c484a8` | Toom-6 and Toom-6 squaring, from 1344 and 1792 limbs, proved, with a generated interpolation; the FFT now from 32768 and 28672 | `mul` 4096 limbs: 1.31 → 1.13 ms; `div` 4096: 3.45 ms at `b4e717f` → 3.24 ms; same binary against the old defaults: products 8192 −11%, 16384 −14% (9.07 → 7.76 ms), squares −6% from 6144 limbs; between 1344 and 3776 limbs ±5% |
| 2026-10-18 | `ac005d7` | Schönhage–Strassen FFT modulo `2ᴺ + 1` for products from 18000 limbs and squares from 16000, proved; in-place residue operations (`20ee58d`) | Beyond the table: `65536 × 65536` 64.9 → 46.1 ms (−29%), `32768²` 16.8 → 13.3 ms (−21%); the FFT alone went from 113% to 85% of Toom at 32768 limbs with the in-place operations |
| 2026-10-17 | `0cddf44` | Toom-4 squaring, from 576 limbs | `sqr` 1024 limbs: 116 → 108 µs, 2048: 335 → 307 µs, 4096: 935 → 836 µs (−10%); `bsqrt` 4096: 6.62 → 6.45 ms |
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
