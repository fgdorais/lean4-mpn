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
  `8ae4933`. Commit `4204471`, 2026-10-19.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | schoolbook by rows into wide accumulators (Comba below 16 limbs in all), Karatsuba from 112, Toom-4 from 608 (Toom-3 from 640 when Toom-4 is set higher), Toom-6 from 1792; Toom-4 by 3 from 272 between 6:5 and 15:8, Toom-3 by 2 from 192 between 4:3 and 15:8 below that, Toom-4 by 2 from 304 up to 2:1; the FFT from 36864 (beyond the table) |
| `sqr` | `sqr` | `n` limbs | schoolbook square by rows into wide accumulators (Comba's square below 16 limbs), Karatsuba from 160, Toom-4 from 832 (Toom-3 from 944 when Toom-4 is set higher), Toom-6 from 2496, the FFT from 26624 (beyond the table) |
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
| `add` | 4.86 | 0.52 | 0.53 | 0.51 | 0.55 | 0.60 | 0.74 | 0.95 | 1.30 | 1.19 | 1.44 | 1.56 | 1.49 |
| `sub` | 5.69 | 0.59 | 0.59 | 0.58 | 0.56 | 0.69 | 0.81 | 0.76 | 1.37 | 1.14 | 1.49 | 1.51 | 1.69 |
| `mul1` | 3.00 | 0.27 | 0.28 | 0.28 | 0.30 | 0.36 | 0.49 | 0.70 | 1.07 | 1.05 | 1.33 | 1.44 | 1.49 |
| `mul` | 3.58 | 0.58 | 0.62 | 1.00 | 1.58 | 2.20 | 2.94 | 3.50 | 3.79 | 3.98 | 4.31 | 4.90 | 4.66 |
| `sqr` | 3.87 | 0.51 | 0.55 | 0.87 | 1.37 | 1.63 | 1.87 | 2.05 | 2.25 | 2.38 | 2.85 | 3.08 | 3.18 |
| `div` | 3.99 | 2.06 | 2.20 | 2.77 | 3.32 | 4.80 | 6.47 | 8.26 | 7.60 | 6.52 | 6.40 | 6.13 | 6.86 |
| `shr` | 1.53 | 1.14 | 0.67 | 0.67 | 0.67 | 0.69 | 0.76 | 0.84 | 1.05 | 0.92 | 1.07 | 1.18 | 1.18 |
| `badd` | 1.85 | 0.33 | 0.79 | 0.78 | 0.82 | 0.87 | 0.95 | 1.07 | 1.41 | 1.20 | 1.41 |  |  |
| `bsub` | 1.87 | 1.36 | 0.93 | 0.85 | 0.93 | 0.94 | 1.00 | 1.10 | 1.61 | 1.26 | 1.42 |  |  |
| `bmul` | 1.84 | 0.58 | 0.82 | 1.22 | 1.75 | 2.19 | 2.83 | 3.54 | 3.74 | 3.99 | 4.39 |  |  |
| `bdiv` | 1.83 | 1.76 | 2.48 | 3.20 | 3.22 | 4.54 | 6.42 | 8.26 | 7.62 | 6.55 | 6.34 |  |  |
| `bgcd` | 0.46 | 1.31 | 4.07 | 3.59 | 3.56 | 3.69 | 3.77 | 4.11 | 4.59 | 4.80 | 4.28 |  |  |
| `bshl` | 0.65 | 0.96 | 0.73 | 0.67 | 0.73 | 0.71 | 0.78 | 0.79 | 1.21 | 0.93 | 1.14 |  |  |
| `bshr` | 1.40 | 0.34 | 0.67 | 0.67 | 0.66 | 0.75 | 0.75 | 0.88 | 1.12 | 0.88 | 0.97 |  |  |
| `bsqrt` | 1.09 | 0.40 | 0.90 | 1.61 | 2.14 | 1.62 | 2.00 | 1.35 | 1.19 | 0.89 | 0.79 |  |  |
| `btostr` | 0.90 | 0.80 | 0.06 | 0.04 | 0.04 | 0.05 | 0.06 | 0.07 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.49 | 0.99 | 0.19 | 0.11 | 0.09 | 0.08 | 0.08 | 0.08 | 0.09 | 0.09 | 0.09 |  |  |
| `btonat` | 0.96 | 0.95 | 1.98 | 5.02 | 11.23 | 22.90 | 44.29 | 69.75 | 151.63 | 182.75 | 247.89 |  |  |
| `bofnat` | 1.65 | 0.57 | 1.12 | 2.58 | 7.11 | 14.31 | 24.85 | 51.35 | 92.05 | 110.08 | 153.03 |  |  |

Time of MPN:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 38.8 ns | 40.9 ns | 42.1 ns | 41.8 ns | 44.6 ns | 50.9 ns | 66.6 ns | 100 ns | 174 ns | 307 ns | 591 ns | 1.12 µs | 2.24 µs |
| `sub` | 50.3 ns | 51.2 ns | 50.3 ns | 50.2 ns | 56.6 ns | 61.7 ns | 78.2 ns | 117 ns | 189 ns | 329 ns | 621 ns | 1.19 µs | 2.37 µs |
| `mul1` | 31.2 ns | 31.9 ns | 33.3 ns | 33 ns | 36.2 ns | 44.8 ns | 65.3 ns | 106 ns | 204 ns | 366 ns | 704 ns | 1.35 µs | 2.65 µs |
| `mul` | 34.8 ns | 47.3 ns | 59.1 ns | 94.4 ns | 187 ns | 466 ns | 1.45 µs | 4.79 µs | 15 µs | 46.2 µs | 128 µs | 368 µs | 973 µs |
| `sqr` | 41 ns | 42.4 ns | 52.6 ns | 82.1 ns | 163 ns | 347 ns | 926 ns | 2.81 µs | 8.88 µs | 27.6 µs | 83.7 µs | 229 µs | 667 µs |
| `div` | 40.3 ns | 99.1 ns | 212 ns | 302 ns | 524 ns | 1.21 µs | 3.45 µs | 11.9 µs | 36.7 µs | 107 µs | 322 µs | 919 µs | 2.64 ms |
| `shr` | 19 ns | 53 ns | 52.9 ns | 53.9 ns | 54.1 ns | 56.5 ns | 63.9 ns | 80.5 ns | 119 ns | 186 ns | 331 ns | 597 ns | 1.19 µs |
| `badd` | 14.8 ns | 30.4 ns | 63.3 ns | 64.6 ns | 67.7 ns | 74.1 ns | 89.2 ns | 123 ns | 196 ns | 326 ns | 609 ns |  |  |
| `bsub` | 16.5 ns | 117 ns | 83.6 ns | 83.2 ns | 99.2 ns | 95 ns | 111 ns | 156 ns | 225 ns | 375 ns | 660 ns |  |  |
| `bmul` | 16.7 ns | 52.1 ns | 80.4 ns | 118 ns | 213 ns | 493 ns | 1.47 µs | 4.82 µs | 15.1 µs | 46.3 µs | 132 µs |  |  |
| `bdiv` | 16.5 ns | 92.7 ns | 253 ns | 358 ns | 557 ns | 1.24 µs | 3.54 µs | 11.9 µs | 36.9 µs | 108 µs | 320 µs |  |  |
| `bgcd` | 47 ns | 77.7 ns | 712 ns | 2.11 µs | 4.31 µs | 9.84 µs | 23.1 µs | 58.3 µs | 168 µs | 509 µs | 1.7 ms |  |  |
| `bshl` | 74.4 ns | 74.3 ns | 60.9 ns | 59.3 ns | 60.6 ns | 64.9 ns | 69.7 ns | 87.8 ns | 135 ns | 212 ns | 395 ns |  |  |
| `bshr` | 16.9 ns | 16.8 ns | 60.5 ns | 61.4 ns | 61.9 ns | 64.3 ns | 70.3 ns | 87.8 ns | 126 ns | 194 ns | 338 ns |  |  |
| `bsqrt` | 100 ns | 545 ns | 1.29 µs | 2.55 µs | 4.37 µs | 5.65 µs | 11.3 µs | 27.4 µs | 76.2 µs | 216 µs | 624 µs |  |  |
| `btostr` | 26.5 ns | 50.3 ns | 403 ns | 786 ns | 1.79 µs | 4.49 µs | 12.7 µs | 39.8 µs | 139 µs | 516 µs | 2.1 ms |  |  |
| `bofstr` | 324 ns | 451 ns | 736 ns | 1.26 µs | 2.45 µs | 5 µs | 10.5 µs | 23.4 µs | 59.6 µs | 165 µs | 510 µs |  |  |
| `btonat` | 8.89 ns | 117 ns | 256 ns | 597 ns | 1.28 µs | 2.84 µs | 5.58 µs | 11.3 µs | 23.2 µs | 46.6 µs | 94.2 µs |  |  |
| `bofnat` | 16.8 ns | 71.2 ns | 128 ns | 333 ns | 839 ns | 1.66 µs | 3.33 µs | 6.83 µs | 13.9 µs | 28.4 µs | 58 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–1.6× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 2.9–4.9× behind from 64 limbs up (under 4× to 512 limbs), **squaring**
  1.9–3.2×. 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply; the schoolbook rows make up for part of it by vectorizing, two
  limb products per instruction with SSE2. Beyond the table,
  Toom-6 from 1792 limbs (2496 for squares) and the FFT from 36864 (26624 for squares), 29%
  faster than Toom-4 at 65536.
- **Division** is 6.2–8.0× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.4 of its
  own. Small `MPN.Nat` divisions still pay a fixed cost (normalization, several arrays): 1.9–3.7×
  from 2 to 16 limbs. Division by a word of two limbs costs about 6.5 ns per limb, 3.6× GMP's
  at 256 limbs and even with it at 5.
- **`gcd`** is 3.6–4.7× behind from 4 limbs, Lehmer with word cofactors and both new numbers in
  one pass; GMP's subquadratic `hgcd` would show from a few hundred limbs.
- **`sqrt`** is 1.2–2.1× behind from 8 to 256 limbs, faster from 512 and up to 4; **decimal
  strings** are 10–20× faster than `Nat`, whose conversions work digit by digit.
- **On an Apple M2** (`e0a0473`): the linear operations are within 1.1–2.4× from 1024 limbs,
  multiplication 2.5–5.1× from 64 limbs (1.6–1.85× faster than at `b4e717f`, where it was
  4.7–8.3×), squaring 1.8–3.5× (15–24% faster than at `caab3b6`) and division 5.6–7.6×.
- **Conversions to and from `Nat`** cost about one operation on `Nat` (some 40 ns) per two
  limbs, against one linear pass for `Nat` itself; they are a boundary, not arithmetic.

## History

Notable changes in performance, newest first. Times are for the sizes shown, on the machine
above; ratios before `15534f8` for `MPN.Nat` rows were inflated by the hashing check.

| date | commit | change | effect |
|---|---|---|---|
| 2026-10-19 | `19ef59a` | Decimal strings by divide and conquer on the base-generic layer (`Generic.Radix`): writing from 80 limbs, reading from 1024 | `btostr` 256 limbs: 140 → 82 µs, 512: 518 → 215 µs, 1024: 1.98 ms → 594 µs; `bofstr` 1024: 512 → 489 µs; beyond the table, writing 10× and reading 3.5× faster at 8192 limbs |
| 2026-10-19 | `e7f6adc` | Half-gcd on the base-generic layer (`Generic.HGCD`), from 8192 limbs | Beyond the table: `gcd` 12288 limbs 192 → 157 ms (−19%), 16384: 340 → 242 ms (−29%), 32768: 1.36 → 0.66 s (−52%) |
| 2026-10-19 | `4204471` | Schoolbook squares by rows into wide accumulators: the products below the diagonal by the rows of `rowsMul`, then `2 S + D` and the carries in one pass; proved. Square thresholds re-tuned: Karatsuba from 160 (was 96), Toom-4 832, Toom-6 2496, the FFT 26624 | `sqr` 64 limbs: 1.26 µs → 926 ns (−27%), 256: 12.8 → 8.88 µs, 1024: 109 → 83.7 µs, 4096: 824 → 667 µs (3.94 → 3.18× `Nat`); `bsqrt` 1024: 663 → 624 µs |
| 2026-10-18 | `2c454ec` | Schoolbook products by rows into `UInt64` accumulators, low and high halves of each product into neighboring accumulators and the carries in one pass at the end, so that the rows vectorize; proved. Thresholds re-tuned: Karatsuba from 112 (was 64), Toom-3 640, Toom-4 608, Toom-6 1792, the FFT 36864 | `mul` 64 limbs: 2.08 → 1.45 µs (−30%), 256: 20.5 → 15.1 µs, 1024: 167 → 129 µs, 4096: 1.13 → 0.97 ms (5.38 → 4.58× `Nat`); `div` 4096: 3.24 → 2.66 ms; `bsqrt` 1024: 761 → 663 µs. The kernel alone: 0.58 → 0.45 ns per limb product at 32 limbs, 0.39 → 0.27 at 256 |
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
