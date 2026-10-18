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
  `8ae4933`. Commit `2c454ec`, 2026-10-18.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | schoolbook by rows into wide accumulators (Comba below 16 limbs in all), Karatsuba from 112, Toom-4 from 608 (Toom-3 from 640 when Toom-4 is set higher), Toom-6 from 1792; Toom-4 by 3 from 272 between 6:5 and 15:8, Toom-3 by 2 from 192 between 4:3 and 15:8 below that, Toom-4 by 2 from 304 up to 2:1; the FFT from 36864 (beyond the table) |
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
| `add` | 5.53 | 0.50 | 0.51 | 0.51 | 0.55 | 0.62 | 0.74 | 0.95 | 1.30 | 1.14 | 1.43 | 1.54 | 1.48 |
| `sub` | 5.86 | 0.57 | 0.58 | 0.57 | 0.60 | 0.72 | 0.84 | 0.81 | 1.39 | 1.12 | 1.50 | 1.48 | 1.66 |
| `mul1` | 2.98 | 0.27 | 0.30 | 0.33 | 0.35 | 0.41 | 0.52 | 0.71 | 1.05 | 1.01 | 1.31 | 1.43 | 1.47 |
| `mul` | 3.58 | 0.58 | 0.65 | 1.08 | 1.64 | 2.22 | 2.88 | 3.54 | 3.81 | 3.93 | 4.33 | 4.87 | 4.58 |
| `sqr` | 4.55 | 0.52 | 0.51 | 0.86 | 1.43 | 1.89 | 2.51 | 3.00 | 3.22 | 3.36 | 3.67 | 4.12 | 3.94 |
| `div` | 4.53 | 1.81 | 2.23 | 2.68 | 3.42 | 4.80 | 6.29 | 8.04 | 7.49 | 6.46 | 6.30 | 6.17 | 6.89 |
| `shr` | 1.98 | 1.44 | 0.87 | 0.86 | 0.87 | 0.88 | 0.88 | 0.98 | 1.18 | 0.98 | 1.13 | 1.22 | 1.19 |
| `badd` | 1.86 | 0.36 | 0.82 | 0.80 | 0.71 | 0.75 | 0.86 | 1.03 | 1.42 | 1.22 | 1.37 |  |  |
| `bsub` | 1.96 | 1.17 | 0.82 | 0.82 | 0.88 | 1.01 | 0.99 | 1.06 | 1.58 | 1.23 | 1.41 |  |  |
| `bmul` | 1.68 | 0.46 | 0.77 | 1.09 | 1.77 | 2.23 | 2.85 | 3.49 | 3.69 | 3.95 | 4.30 |  |  |
| `bdiv` | 1.76 | 1.76 | 2.52 | 2.78 | 3.09 | 4.58 | 6.11 | 8.06 | 7.48 | 6.39 | 6.31 |  |  |
| `bgcd` | 0.45 | 1.30 | 4.61 | 3.95 | 3.61 | 3.73 | 3.82 | 4.06 | 4.51 | 4.65 | 4.13 |  |  |
| `bshl` | 0.77 | 0.79 | 0.85 | 0.77 | 0.81 | 0.82 | 0.67 | 0.86 | 1.22 | 0.93 | 1.19 |  |  |
| `bshr` | 1.72 | 0.27 | 0.84 | 0.81 | 0.69 | 0.82 | 0.76 | 0.92 | 1.18 | 0.79 | 0.94 |  |  |
| `bsqrt` | 1.05 | 0.40 | 0.93 | 1.64 | 2.12 | 1.63 | 2.04 | 1.42 | 1.25 | 0.97 | 0.84 |  |  |
| `btostr` | 0.94 | 0.86 | 0.06 | 0.05 | 0.05 | 0.05 | 0.06 | 0.07 | 0.09 | 0.09 | 0.10 |  |  |
| `bofstr` | 2.24 | 0.97 | 0.19 | 0.11 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 | 0.10 |  |  |
| `btonat` | 1.18 | 1.16 | 1.79 | 5.16 | 9.07 | 20.37 | 39.86 | 69.38 | 143.59 | 183.94 | 245.26 |  |  |
| `bofnat` | 1.83 | 0.52 | 1.15 | 2.69 | 6.38 | 12.06 | 23.71 | 44.74 | 88.39 | 103.69 | 153.74 |  |  |

Time of MPN:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 44.6 ns | 40.5 ns | 41.2 ns | 42.7 ns | 45.4 ns | 52.1 ns | 66.7 ns | 102 ns | 175 ns | 308 ns | 586 ns | 1.12 µs | 2.24 µs |
| `sub` | 50.5 ns | 51.3 ns | 50.5 ns | 51.4 ns | 62.2 ns | 67 ns | 83.7 ns | 122 ns | 193 ns | 331 ns | 625 ns | 1.19 µs | 2.38 µs |
| `mul1` | 31 ns | 31.9 ns | 35.4 ns | 39.6 ns | 42.1 ns | 50.7 ns | 71.3 ns | 108 ns | 204 ns | 367 ns | 710 ns | 1.35 µs | 2.64 µs |
| `mul` | 34.8 ns | 47.2 ns | 63 ns | 100 ns | 192 ns | 472 ns | 1.45 µs | 4.85 µs | 15.1 µs | 46.4 µs | 129 µs | 368 µs | 972 µs |
| `sqr` | 48.2 ns | 42.6 ns | 52 ns | 80.6 ns | 167 ns | 408 ns | 1.26 µs | 4.11 µs | 12.8 µs | 38.9 µs | 109 µs | 310 µs | 824 µs |
| `div` | 43 ns | 94 ns | 212 ns | 306 ns | 527 ns | 1.21 µs | 3.33 µs | 11.5 µs | 36.2 µs | 106 µs | 317 µs | 920 µs | 2.66 ms |
| `shr` | 19.6 ns | 59.5 ns | 63.8 ns | 64.3 ns | 64.7 ns | 68.3 ns | 72.3 ns | 86.7 ns | 125 ns | 195 ns | 341 ns | 609 ns | 1.2 µs |
| `badd` | 14.9 ns | 31.5 ns | 66.2 ns | 66.8 ns | 69.4 ns | 73.9 ns | 91.5 ns | 127 ns | 199 ns | 331 ns | 612 ns |  |  |
| `bsub` | 16.9 ns | 102 ns | 81.1 ns | 83.9 ns | 90.5 ns | 94.8 ns | 108 ns | 151 ns | 229 ns | 369 ns | 662 ns |  |  |
| `bmul` | 16.3 ns | 48.7 ns | 86.6 ns | 128 ns | 221 ns | 507 ns | 1.48 µs | 4.81 µs | 15 µs | 46.2 µs | 128 µs |  |  |
| `bdiv` | 15.6 ns | 91.8 ns | 248 ns | 339 ns | 560 ns | 1.24 µs | 3.38 µs | 11.6 µs | 36.2 µs | 106 µs | 317 µs |  |  |
| `bgcd` | 46.6 ns | 77.2 ns | 802 ns | 2.32 µs | 4.4 µs | 10 µs | 23.4 µs | 57.7 µs | 165 µs | 493 µs | 1.64 ms |  |  |
| `bshl` | 77.1 ns | 80.7 ns | 65.4 ns | 63.5 ns | 64.9 ns | 69.2 ns | 71.9 ns | 91.6 ns | 134 ns | 213 ns | 398 ns |  |  |
| `bshr` | 17.1 ns | 17 ns | 67.5 ns | 68.2 ns | 68.7 ns | 72.4 ns | 77.8 ns | 93.8 ns | 133 ns | 203 ns | 345 ns |  |  |
| `bsqrt` | 97.7 ns | 534 ns | 1.31 µs | 2.63 µs | 4.39 µs | 5.77 µs | 11.6 µs | 28.7 µs | 80.3 µs | 232 µs | 663 µs |  |  |
| `btostr` | 27.5 ns | 30.2 ns | 427 ns | 831 ns | 1.87 µs | 4.65 µs | 12.9 µs | 40.4 µs | 140 µs | 518 µs | 1.98 ms |  |  |
| `bofstr` | 316 ns | 452 ns | 735 ns | 1.29 µs | 2.51 µs | 5.08 µs | 10.7 µs | 23.9 µs | 59.8 µs | 167 µs | 512 µs |  |  |
| `btonat` | 11.2 ns | 129 ns | 251 ns | 598 ns | 1.27 µs | 2.75 µs | 5.54 µs | 11.1 µs | 22.4 µs | 45.8 µs | 93.2 µs |  |  |
| `bofnat` | 18.5 ns | 73.2 ns | 133 ns | 334 ns | 830 ns | 1.64 µs | 3.32 µs | 6.8 µs | 13.7 µs | 28.1 µs | 57.5 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates. They stay within 1.2–1.6× at large sizes, where GMP's assembly
  and 64-bit limbs win.
- **Multiplication** is 2.9–4.9× behind from 64 limbs up (under 4× to 512 limbs), **squaring**
  2.5–4.1×. 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply; the schoolbook rows make up for part of it by vectorizing, two
  limb products per instruction with SSE2. Beyond the table,
  Toom-6 from 1792 limbs (also for squares) and the FFT from 36864 (28672 for squares), 29%
  faster than Toom-4 at 65536.
- **Division** is 6.2–8.0× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.4 of its
  own. Small `MPN.Nat` divisions still pay a fixed cost (normalization, several arrays): 1.9–3.7×
  from 2 to 16 limbs. Division by a word of two limbs costs about 6.5 ns per limb, 3.6× GMP's
  at 256 limbs and even with it at 5.
- **`gcd`** is 3.6–4.7× behind from 4 limbs, Lehmer with word cofactors and both new numbers in
  one pass; GMP's subquadratic `hgcd` would show from a few hundred limbs.
- **`sqrt`** is 1.3–2.1× behind from 8 to 256 limbs, faster from 512 and up to 4; **decimal
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
