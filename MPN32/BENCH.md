# Benchmarks

This file tracks the performance of the library against Lean's `Nat`, which is backed by GMP. The
tables come from `lake exe bench` and are regenerated after each change that affects speed, and
the history at the end records what changed and by how much.

## Running

```sh
lake build bench                      # `lake build` alone does not rebuild it
taskset -c 2 .lake/build/bin/bench > bench.txt
taskset -c 2 .lake/build/bin/bench badd bsub bmul bdiv bmod bsqr bpow blcm blog2 bcmp beq bhash \
  bgcd bshl bshr band bor bxor bsqrt btostr bofstr \
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
  `49cf1b1`. Commit `e8b34d7`, 2026-10-25, the fastest of three runs.

### Operations

| op | operation | operands | algorithm |
|---|---|---|---|
| `add`, `sub` | `add`, `sub` on limbs | `n` and `n` limbs | linear, one pass |
| `mul1` | `mul1` | `n` limbs times a limb | linear, one pass |
| `mul` | `mulLimbs` | `n` by `n` limbs | schoolbook by rows into wide accumulators (Comba below 16 limbs in all), Karatsuba from 112, Toom-4 from 608 (Toom-3 from 640 when Toom-4 is set higher), Toom-6 from 1792; Toom-4 by 3 from 272 between 6:5 and 15:8, Toom-3 by 2 from 192 between 4:3 and 15:8 below that, Toom-4 by 2 from 304 up to 2:1; the FFT from 14336 (beyond the table) |
| `sqr` | `sqr` | `n` limbs | schoolbook square by rows into wide accumulators (Comba's square below 16 limbs), Karatsuba from 160, Toom-4 from 832 (Toom-3 from 944 when Toom-4 is set higher), Toom-6 from 2496, the FFT from 12288 (beyond the table) |
| `div` | `div`, the quotient | `2n` by `n` limbs | `divRem1`, `divRem2`, Algorithm D, Burnikel–Ziegler from 176 (`main`'s `NatOps.divNorm`) |
| `div1` | `divRem1` by `0xF1234567` | `n` limbs | from the top limb down, the checked 2-by-1 steps with a reciprocal (`main`'s `WordArray.divRem1W`; always, `div1Recip` = 0, like GMP) |
| `div1u` | `divRem1` by `10⁹` | `n` limbs | as `div1`, by an unnormalized limb, on the dividend shifted in place (`divRem1U`; `div1Unnorm` = 0) |
| `shr` | `shiftRight` by 37 bits | `n` limbs | one pass in place |
| `badd` … `bdiv` | `MPN.Nat` `+ - * /` | as above (`bdiv`: `2n` by `n`) | word fast path, then as above |
| `bmod`, `bsqr`, `bpow` | `MPN.Nat` `%`, `sqr`, `x³` | as `bdiv`, `bmul` | the division, the square, squares and products |
| `blcm`, `blog2` | `MPN.Nat.lcm`, `log2` | `n` limbs | the gcd, a division and a product; the top limb |
| `bcmp`, `beq`, `bhash` | `x < x + 1`, `x = x'` (two copies), `hash` | `n` limbs | every limb compared or hashed |
| `bgcd` | `MPN.Nat.gcd` | `n` and `n` limbs | Lehmer with word cofactors, Euclid on words |
| `bshl`, `bshr` | `MPN.Nat` `<<<`, `>>>` 37 | `n` limbs | one pass in place |
| `band`, `bor`, `bxor` | `MPN.Nat` `&&&`, `\|\|\|`, `^^^` | `n` and `n` limbs | one pass into fresh zeros (`WordArray.bitW`) |
| `bsqrt` | `MPN.Nat.sqrt` | `2n` limbs | Newton at growing precision; Zimmermann from `2n = 80` limbs |
| `btostr` | `toString` | `n` limbs | chunks of 9 digits, `divRem1` by `10⁹` |
| `bofstr` | `MPN.Nat.ofString?` | the digits of `n` limbs | a fold over the characters, 9 digits per chunk |
| `btonat` | `MPN.Nat.toNat` | `n` limbs | by halves, joined with shifts; `Nat` column: `x + 1` |
| `bofnat` | `MPN.Nat.ofNat` | `n` limbs | by halves, then 64 bits at a time; `Nat` column: `x + 1` |

## Current results

Ratio MPN / Nat (below 1 is faster than Nat):

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 4.71 | 0.42 | 0.43 | 0.46 | 0.50 | 0.49 | 0.58 | 0.92 | 1.30 | 1.12 | 1.35 | 1.37 | 1.53 |
| `sub` | 5.16 | 0.51 | 0.49 | 0.48 | 0.48 | 0.58 | 0.69 | 0.74 | 1.34 | 1.13 | 1.36 | 1.56 | 1.60 |
| `mul1` | 3.27 | 0.27 | 0.28 | 0.27 | 0.31 | 0.35 | 0.46 | 0.59 | 0.94 | 0.93 | 1.13 | 1.28 | 1.30 |
| `mul` | 3.67 | 0.47 | 0.56 | 1.11 | 1.60 | 2.24 | 3.00 | 3.12 | 3.97 | 4.19 | 4.47 | 5.07 | 4.86 |
| `sqr` | 3.70 | 0.50 | 0.53 | 0.83 | 1.52 | 1.74 | 1.99 | 2.24 | 2.40 | 2.53 | 2.89 | 3.26 | 3.31 |
| `div` | 5.29 | 1.91 | 1.74 | 2.65 | 3.09 | 4.38 | 6.24 | 8.15 | 7.58 | 6.63 | 6.48 | 6.29 | 6.99 |
| `shr` | 1.55 | 0.75 | 0.39 | 0.30 | 0.40 | 0.41 | 0.49 | 0.58 | 0.89 | 0.82 | 0.87 | 1.00 | 1.06 |
| `badd` | 1.85 | 0.37 | 0.77 | 0.79 | 0.78 | 0.88 | 0.78 | 1.07 | 1.47 | 1.19 | 1.40 |  |  |
| `bsub` | 1.87 | 1.06 | 0.78 | 0.80 | 0.71 | 0.85 | 0.97 | 1.04 | 1.55 | 1.30 | 1.48 |  |  |
| `bmul` | 1.75 | 0.58 | 0.76 | 1.31 | 1.85 | 2.36 | 3.04 | 3.70 | 3.95 | 4.22 | 4.52 |  |  |
| `bdiv` | 1.73 | 1.76 | 2.47 | 2.72 | 3.34 | 4.55 | 6.21 | 8.21 | 7.67 | 6.63 | 6.54 |  |  |
| `bgcd` | 0.62 | 1.61 | 4.01 | 3.47 | 3.27 | 3.54 | 3.71 | 3.99 | 4.43 | 4.65 | 4.06 |  |  |
| `bshl` | 0.62 | 0.67 | 0.65 | 0.62 | 0.66 | 0.50 | 0.67 | 0.80 | 1.15 | 0.93 | 1.16 |  |  |
| `bshr` | 1.70 | 0.35 | 0.43 | 0.37 | 0.42 | 0.41 | 0.48 | 0.67 | 0.93 | 0.75 | 1.00 |  |  |
| `bsqrt` | 1.00 | 0.34 | 0.83 | 1.48 | 2.20 | 1.72 | 1.99 | 1.36 | 1.20 | 0.93 | 0.81 |  |  |
| `btostr` | 0.92 | 0.84 | 0.06 | 0.05 | 0.05 | 0.05 | 0.06 | 0.06 | 0.05 | 0.04 | 0.03 |  |  |
| `bofstr` | 2.15 | 0.98 | 0.19 | 0.11 | 0.10 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 | 0.09 |  |  |
| `btonat` | 0.94 | 0.77 | 1.95 | 4.55 | 9.92 | 21.81 | 45.57 | 73.38 | 144.59 | 182.68 | 247.63 |  |  |
| `bofnat` | 1.46 | 0.59 | 1.08 | 2.93 | 6.69 | 12.52 | 24.93 | 49.02 | 89.81 | 114.23 | 157.33 |  |  |

Time of MPN:

| op | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `add` | 38 ns | 40.7 ns | 41.1 ns | 41.4 ns | 44.8 ns | 52.3 ns | 68 ns | 108 ns | 183 ns | 313 ns | 597 ns | 1.14 µs | 2.28 µs |
| `sub` | 48.2 ns | 48.4 ns | 47.5 ns | 48.8 ns | 55.9 ns | 60 ns | 77.8 ns | 120 ns | 192 ns | 334 ns | 624 ns | 1.2 µs | 2.39 µs |
| `mul1` | 32.7 ns | 32.9 ns | 34.2 ns | 34.7 ns | 38 ns | 46.5 ns | 65.6 ns | 104 ns | 194 ns | 348 ns | 667 ns | 1.27 µs | 2.49 µs |
| `mul` | 36.1 ns | 45.4 ns | 58.1 ns | 112 ns | 218 ns | 522 ns | 1.58 µs | 5.08 µs | 16.2 µs | 49.4 µs | 135 µs | 386 µs | 1.03 ms |
| `sqr` | 40.3 ns | 41.9 ns | 53.1 ns | 82.8 ns | 195 ns | 413 ns | 1.05 µs | 3.09 µs | 9.69 µs | 29.8 µs | 87.4 µs | 245 µs | 695 µs |
| `div` | 54.5 ns | 95.1 ns | 226 ns | 318 ns | 538 ns | 1.23 µs | 3.47 µs | 11.9 µs | 37.3 µs | 110 µs | 329 µs | 950 µs | 2.74 ms |
| `shr` | 15.5 ns | 37.6 ns | 40.1 ns | 36.9 ns | 37.9 ns | 39.8 ns | 45.9 ns | 62.4 ns | 99.1 ns | 169 ns | 315 ns | 583 ns | 1.19 µs |
| `badd` | 15.1 ns | 31 ns | 63.1 ns | 66 ns | 70 ns | 77.4 ns | 92.4 ns | 129 ns | 206 ns | 332 ns | 626 ns |  |  |
| `bsub` | 17.5 ns | 95.9 ns | 76.4 ns | 76.7 ns | 84.6 ns | 87.4 ns | 105 ns | 151 ns | 222 ns | 365 ns | 658 ns |  |  |
| `bmul` | 17.1 ns | 47.9 ns | 83.3 ns | 138 ns | 244 ns | 545 ns | 1.58 µs | 5.1 µs | 15.9 µs | 49.4 µs | 135 µs |  |  |
| `bdiv` | 16.6 ns | 91.8 ns | 249 ns | 343 ns | 564 ns | 1.25 µs | 3.48 µs | 11.9 µs | 37.3 µs | 110 µs | 332 µs |  |  |
| `bgcd` | 65.4 ns | 95.7 ns | 709 ns | 2.04 µs | 3.99 µs | 9.52 µs | 22.8 µs | 56.6 µs | 164 µs | 493 µs | 1.63 ms |  |  |
| `bshl` | 66.2 ns | 67.9 ns | 54.6 ns | 53 ns | 53.8 ns | 56.4 ns | 61.4 ns | 87.2 ns | 128 ns | 203 ns | 386 ns |  |  |
| `bshr` | 16.7 ns | 16.7 ns | 43.9 ns | 44.5 ns | 45.3 ns | 45.1 ns | 52.1 ns | 69.8 ns | 105 ns | 176 ns | 323 ns |  |  |
| `bsqrt` | 99.7 ns | 471 ns | 1.21 µs | 2.44 µs | 4.58 µs | 6.09 µs | 11.4 µs | 27.7 µs | 77 µs | 224 µs | 647 µs |  |  |
| `btostr` | 26.1 ns | 30.3 ns | 412 ns | 832 ns | 1.85 µs | 4.64 µs | 13.1 µs | 32.5 µs | 82.6 µs | 219 µs | 600 µs |  |  |
| `bofstr` | 305 ns | 454 ns | 744 ns | 1.3 µs | 2.79 µs | 5.49 µs | 11.1 µs | 24.2 µs | 60.3 µs | 164 µs | 508 µs |  |  |
| `btonat` | 9.81 ns | 95.7 ns | 248 ns | 591 ns | 1.28 µs | 2.77 µs | 5.56 µs | 11.3 µs | 22.7 µs | 46.4 µs | 94.1 µs |  |  |
| `bofnat` | 16.5 ns | 79.7 ns | 131 ns | 340 ns | 843 ns | 1.69 µs | 3.39 µs | 7.01 µs | 14.1 µs | 28.9 µs | 59 µs |  |  |

## Where it stands

- **Linear operations** (`add`, `sub`, `mul1`, shifts) are faster than `Nat` up to 64–128 limbs,
  where `Nat`'s wrapper dominates, and the shifts up to 256–512. They stay within 1.0–1.6× at
  large sizes, where GMP's assembly and 64-bit limbs win.
- **Multiplication** is 3.0–5.1× behind from 64 limbs up (under 4× to 256 limbs), **squaring**
  2.0–3.3×. 32-bit limbs need 4× as many limb products as GMP's 64-bit limbs, and Lean has no
  64 × 64 → 128-bit multiply; the schoolbook rows make up for part of it by vectorizing, two
  limb products per instruction with SSE2. Beyond the table,
  Toom-6 from 1792 limbs (2496 for squares) and the FFT from 14336 (12288 for squares).
- **Division** is 6.2–8.2× behind from 64 limbs up, about 1.5× multiplication's gap: GMP divides
  `2n` by `n` limbs for about the cost of one `n × n` product, and this library for 2.4 of its
  own. Small `MPN.Nat` divisions still pay a fixed cost (normalization, several arrays): 1.8–3.3×
  from 2 to 16 limbs. Division by a word of two limbs costs about 6.5 ns per limb, 3.6× GMP's
  at 256 limbs and even with it at 5.
- **`gcd`** is 3.3–4.7× behind from 4 limbs, Lehmer with word cofactors and both new numbers in
  one pass; half-gcd (`Generic.HGCD`) takes over from `gcdHalf = 4608` limbs, beyond the table.
- **`sqrt`** is 1.2–2.2× behind from 8 to 256 limbs, faster from 512 and up to 4; **decimal
  strings** are 17–33× faster than `Nat` to write and 5–11× to read from 4 limbs, since `Nat`'s
  conversions work digit by digit.
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
| 2026-11-07 | `043fb75` | Guards on sizes by `main`'s `WordArray.fitsU` instead of `< USize.size`, a comparison with a big number; `log2A` from `main`'s `WordArray.log2A` | From three alternating runs against `4d3f349`, without `Nat`, 2 to 1024 limbs: `shr` −0.4% to −8%, `bshl` −0.4% to −3.8%, `bshr` −5% to +2.4%, `bsqrt` −0.5% to −4.2%, `div`, `bdiv` −1.7% to +3.4%, `blog2`, `band` −1.8% to +2.8% |
| 2026-11-07 | `4d3f349` | `shiftLeft` and `shiftRight` by `main`'s `WordArray.shlBits` and `shrBits`; the unused `shrLimbs` removed | From three alternating runs against `08b891d`, without `Nat`: `shr` +3% to +11%, the same instructions and calls (counted with breakpoints), its loop now starting on a 64-byte line instead of 48 bytes into one (layout); `bshl`, `bshr` 0% to +6%, `bsqrt` −0.3% to +4%, `btostr` −1% to −6% |
| 2026-11-07 | `08b891d` | `land`, `lor`, `xor` from `main`'s `WordArray.landA`, `lorA`, `xorA`, and `ltA` from `main`'s `WordArray.ltAFast`, replacing their own `bitA` and loop | From three alternating runs against `feab648`, without `Nat`, 2 to 1024 limbs: `band` −3% to −11%, `bor` −1% to −5%, `bxor` −4% to +5.5%; `bcmp` −16% at 2 limbs and +13% to +47% from 64, the same instructions as before (the old `ltA` back in place gives the same), whose loop now crosses a 64-byte line: with `-falign-loops=64` it is −3% to 0%, but that flag makes 32-bit `sub` 7–14% and `mul1` 5% slower, so it stays off |
| 2026-11-06 | `c30bc5e` | The normalization before division by blocks (`divModLimbsDC`) by `main`'s `Schoolbook.shlTop` and `shrArr`, shared with the schoolbook division, instead of `mulRow` by `normFactor` and `shiftRight` | From three alternating runs against `dc30925`, without `Nat`, 128 to 16384 limbs: `div`, `bdiv`, `bmod`, `btostr`, `bsqrt` +0.6% to −1.6% |
| 2026-11-06 | `adfb500` | `divRemBasecase` from `main`'s shared `MPN.Div.Basecase` (`Schoolbook.divRemN`): normalized by shifts instead of by `mulRow`, the results copied out by the new `WordArray.extract`, replacing the in-place loop and `divRemBasecaseTop`; `mulRow` only before the division by blocks | From three alternating runs against `d9c0a41`, without `Nat`: `div`, `bdiv`, `bmod` −25% to −33% at 3 limbs, −11% to −22% at 4, −22% to −30% at 8, −8% to −15% at 16, −5% to −10% at 32, −4% to −6% at 64; with aligned builds +0.6% to +0.9% at 256 and 1024 (+1% to +3% with default builds), `bsqrt` −4% to −10% from 4 to 256 limbs, `btostr` −0.5% to −2.5%; `bgcd`, which does not divide by Algorithm D, ±6% (layout) |
| 2026-11-05 | `4143568` | Schoolbook division two quotient limbs per pass (`Schoolbook.divLoop2In`, `div2Rows`, always on 32-bit limbs): the two limbs estimated together by two checked 3-by-2 steps and Knuth's test by the third divisor limb, one multiply-subtract pass of two rows (`subMul2B` in 64-bit words) | From three alternating runs against `8dafb3a`, without `Nat`: `bdiv`, `bmod` −12% to −20% from 16 to 256 limbs, −5% to −10.5% from 512 to 4096, −4.5% to −6% at 8, +2% at 4 |
| 2026-11-01 | `dd67e5e` | Barrett's division with Newton's reciprocal on 32-bit limbs, by the shared wrapped product (`Dispatch.mulModW`, the FFT modulo `β^N - 1`) in `ops32`, from `divQMu = 8192` limbs for the quotient alone and `divMu = 14336` with the remainder (measured crossovers); Barrett only when the quotient is as long as the threshold too | From two alternating runs against `73cccd8`: `bdiv` −20% at 16384 limbs and −33% at 32768, `bmod` −6% and −21%, `btostr` −1.8% to −2.7% at 16384 to 32768 (+23% at 32768 before the rule on the quotient: its top division has a short quotient) |
| 2026-11-01 | `73cccd8` | `trim`, `ofNat` and `lt` from `main`'s `MPN.Trim` (`trimTo 0`, `ofNatW`, `ltWin`), in place of the branch's own fast versions | From three alternating runs against `cdbf580` with `-falign-functions=64 -falign-loops=64` on both builds: `bofnat` +2% to +10% from 256 down to 4 limbs (the shared writer of a `Nat`, two limbs from each word), `badd`, `bsub`, `bmul` −6.5% to +2.2% from 4 to 256 limbs; the default builds showed `bcmp` +10% to +48% and `badd`, `bsub`, `bmul` +4% to +9% at small sizes, which the aligned builds do not (`bcmp` runs the unchanged `ltA`) |
| 2026-11-01 | `cdbf580` | The square root (`Bridge.sqrtZ`, `Bridge.newtonBase`), half-gcd and Lehmer's step through `MPN.Bridge` over `bridge32`, the bridge to `ops32` | From three alternating runs against `0fc1c90` with `-falign-functions=64 -falign-loops=64` on both builds, 16 to 4096 limbs: `bgcd` −1.5% to +0.3%, `bsqrt` +0.4% to +2.4%; the default builds showed `bgcd` +2% to +6% from 64 to 1024 limbs, which the aligned builds do not |
| 2026-11-01 | `2142117` | Division by `MPN.Dispatch.Div`: division by blocks and Barrett's division (once `divModMu` on `ops32`) through `divN` on `ops32B`, a quotient-only path through `divQN` (`divQMu`, never by default), and the square root through `sqrtBy` | Same algorithms at the defaults; `divMod` no longer tests `divMu`. From two alternating runs against `1db0c1c`, 16 to 16384 limbs: `div`, `bdiv`, `bmod` −3% to −5%, `bsqrt`, `btostr` −0.3% to −3.1%, likely mostly layout |
| 2026-11-01 | `01c512a` | The FFT products on `main`'s `FFTCheck` and `fftParams`, calling `FFTOps.fftMulAt` and `fftSqrAt` on the arrays of the slices; the branch's parameter structures and wrappers are gone | From three alternating runs against `3d488d2`, 16384 to 65536 limbs: `mul`, `bmul` +2.3% to +3.1%, `sqr`, `bsqr` −1.5% to −3.0%; both run the same changed path, so likely layout |
| 2026-11-01 | `d4748f9` | The operations of the FFT (`addRange`, `reduce`, `addCoef`, `zeroRange`) from `main`'s generic kernels `MPN.FFT.Kernels`: `reduce` subtracts the halves of a pointwise product in one pass reading both | From three alternating runs against `952606e`: `mul` −1.3% to −2.3%, `sqr` −0.2% to +1.4% from 32768 to 131072 limbs |
| 2026-11-01 | `952606e` | `addMul1`, `addMul1Set`, `addMul1SetPre` and `subMul1` from `main`'s generic passes (`WordArray.addMul1Step`, `subMul1Step`) | Same loops in the generated C. From five alternating runs against `ed6fbd9`: `mul`, `bmul`, `div` +2% to +7% from 8 to 32 limbs, `sqr` −3% to −6%, ±0.5% from 64 limbs; `mul` at 4 limbs (+19%) runs Comba, which this does not touch, so the small sizes move by layout |
| 2026-11-01 | `536c9e2` | The linear operations of the Toom methods (`addInto` to `sum`) from `main`'s generic kernels `MPN.Toom.Kernels`, in place on the windows instead of copies of them | From three alternating runs against `e1a5be6`: `mul`, `sqr`, `bmul`, `bsqr`, `div` −5% to +3% from 64 to 4096 limbs |
| 2026-11-01 | `f045a76`, `main` `baed7bf` | The steps of Zimmermann's square root build `X` and `U` by the new `NatOps.join` (`x βᵏ + y mod βᵏ`, `main`'s `WordArray.joinW`: two copies into one array of zeros) instead of a shift, a cut and an addition | From three alternating runs against `cdbdb43`: `bsqrt` −16% to −18% from 2 to 16 limbs, −13% at 64, −6% at 256, −2% at 1024 |
| 2026-11-01 | `main` `89944f8` | Zimmermann's square root divides by `2t` once per step, for the quotient and the remainder, instead of by `t` and then by 2 | From three alternating runs against `fede64c`: `bsqrt` −12% at 2 limbs, −4% to −12% from 4 to 64, −7% at 256, −2% at 1024 |
| 2026-11-01 | `main` `b766b6f` | Division by an unnormalized limb forms each limb of `a 2ˢ` in the loop (`divLoopSh`), like GMP's `mpn_divrem_1`, instead of shifting `a` first and dividing in place: one pass instead of two | From four alternating runs against `2d81648`: `div1u` −17% at 1 limb, −8% to −12% at 2–4, −1% to −5% from 16; `btostr` −3% to −9% from 4 limbs (chunks by `10⁹`); `div1` −6% to −8% up to 4; `bsqrt` −1% to −3% |
| 2026-11-01 | `61434d2` | The base of Zimmermann's recursion for roots of one limb is `main`'s `sqrt2W` on words (Newton's iteration on limbs from just above the root, like GMP's `mpn_sqrtrem2`), not Newton's iteration on `MPN.Nat` | From five alternating runs against `0e97ab7`, with other jobs running on the machine: `bsqrt` −18% at 2 limbs, −10% to −16% from 4 to 16, −7% at 64, ±2% from 256 |
| 2026-11-01 | `main` `081b691` | `UInt32.log2` and `UInt64.log2` by a binary search (`log2Fast`, `@[csimp]`): five or six shifts and comparisons instead of the runtime's loop over the bits | From three alternating runs against `b4b3bbd`: `blog2` −31% to −52%; `div1u` −4% to −10%; `btostr` −3% to −6%; `bdiv`, `bsqrt` ±4%; `div1` +7% to +16% up to 4 limbs, with the same instruction count (layout) |
| 2026-11-01 | `f761397` | GMP's algorithm choices as the defaults: the reciprocal steps of division by a limb (normalized or not) and of schoolbook division always (`div1Recip`, `div1Unnorm`, `div32Recip` = 0), the square root by Zimmermann's recursion down to one limb (`sqrtZimmermann`, `sqrtBase` = 1); the size crossovers stay as measured | From three alternating runs against `9cc5476`: `div1` +9% to +26% (the steps against the hardware divider of 64 bits by 32); `div1u` +13% to +70%; `btostr` +13% to +32% from 4 limbs (by `10⁹`); `div`, `bdiv` +8% to +16% at 4–16 limbs, ±0.3% from 64; `bsqrt` +249% at 2 limbs, +146% at 4, +54% at 16, +16% at 64, ±0 at 1024 (the base of the recursion is Newton's iteration on `MPN.Nat`, not a word operation like GMP's `sqrtrem2`) |
| 2026-10-31 | `9951fba` | Division by an unnormalized limb can take `main`'s `divRem1U` (the dividend shifted in place and the checked 2-by-1 steps with the reciprocal of the shifted divisor) from `Config.div1Unnorm` limbs, which `lake exe tune` measures; the default never takes it; new row `div1u`, by `10⁹` | `lake exe tune`: the divider wins by 10–20% from 2 to 512 limbs (1709 ns against 1889 ns at 512); the defaults leave the code paths unchanged |
| 2026-10-31 | `cd4d00e` | The thresholds of the schoolbook product and square are `Config.mulRows` (16), `Config.mulCombaW` (32) and `Config.sqrRows` (16), which `lake exe tune` measures (24, 40 and 16 here); the defaults are unchanged | From three alternating runs against `4eb1b32`: `mul`, `sqr`, `bmul`, `bsqr` −13% to +7% up to 8 limbs, the same algorithms (layout), ±2% from 16 |
| 2026-10-31 | `37e0c02` | The thresholds of the square root are `Config.sqrtZimmermann` (40) and `Config.sqrtBase` (16), which `lake exe tune` measures (48 and 31 here); the defaults are unchanged | From three alternating runs against `43e6e47`: `bsqrt` −2.4% to +2.3% |
| 2026-10-31 | `0cff552` | Schoolbook division takes `main`'s checked 3-by-2 steps with the reciprocal (`WordArray.recip32`) from `Config.div32Recip` = 64 limbs of a normalized divisor, where `lake exe tune` finds them winning; main32 never used them before | From three alternating runs against `21801f1`: `div`, `bdiv`, `bmod` −0.5% to −1.7% from 128 limbs, +0.4% to +2% at 16–64 (the test of the size and the normalization) |
| 2026-10-31 | `ffaded1` | The size from which `divRem1` takes `main`'s checked steps with the reciprocal is `Config.div1Recip`, which `lake exe tune` measures; the default, 1000000, never takes them (here the divider wins by 10–20% from 2 to 512 limbs) | From three alternating runs against `18d2419`: `div1` −1% to −11% up to 128 limbs, ±0 from 1024; `btostr` −2% to −4% from 4 limbs; `bmod`, `bdiv` −2% to +2% |
| 2026-10-31 | `0934d5d` | `divRem1` from `main`'s `WordArray.divRem1W` (the loop from the top down over any step, with the new `div2Rem` of a limb: here one division of 64 bits by 32 for the quotient and the remainder), replacing the loop proved through lists; new row `div1`. `main`'s checked 2-by-1 step with the reciprocal stays off: on 32-bit limbs it was 4–16% slower than the divider from 16 limbs | From three alternating runs against `18d2419`: `div1` −9% at 4 limbs, −4% at 16, −1% at 128, ±0 from 512; `btostr` −3% to −6% from 4 limbs |
| 2026-10-31 | `18d2419`, `main` `log2` | `MPN.Nat`'s hash of a large number from its size and its bottom and top limbs, in constant time like `Nat`'s (its low word), instead of every limb; `GNat.log2` of words by `UInt64.log2` instead of `Nat.log2` of a `Nat`, a GMP number from `2⁶³` | `bhash` 0.22–0.23× `Nat` from 2 to 4096 limbs (was 0.21× at 2 limbs up to 71× at 4096); `blog2` at 2 limbs (a word) 74.5 → 24 ns |
| 2026-10-31 | `8b71401` | The comparison of `MPN.Nat` by `main`'s `WordArray.ltW` (`ltA`): from the top limb down by `uget`, one comparison for each equal limb, instead of `getD` of slices and two comparisons | `bcmp` −62% at 4 limbs, −73% at 16, −80% at 256, −81% at 4096: 1.5–3.0× `Nat` (was 2.8–15.6×); `bsub` −18% at 4 and 16 limbs, `bgcd` −9% to −12% to 256; `bsub` +9% and `bgcd` +2% at 4096 |
| 2026-10-31 | `main` `pow` | `GNat.pow` stops at the exponent 1: it squared `x` for an exponent 0 that it then dropped, so `x³` took a square of twice the length that it never used | `bpow` −56% at 2 limbs, −50% at 16, −41% at 256 and 4096; 2.5×, 4.4× and 5.0× `Nat` at 16, 256 and 4096 limbs (was 5.2×, 7.2× and 8.5×) |
| 2026-10-31 | `ca4cc18`+ | New rows `band`, `bor`, `bxor` (`MPN.Nat` `&&&`, `\|\|\|`, `^^^`); against `Nat` they are 0.2–0.8× from 2 to 64 limbs, 1.3–1.8× from 256 (GMP has half as many limbs), 1.7× at one limb (16 against 9 ns) | Measured on the commit before `ca4cc18` with these rows: `bitW` made them 87–88% faster at 16 limbs and 95–97% at 256 and 4096 (65 µs → 2.1–2.5 µs at 4096); the old operations built an array by `ofFn` of `getD` of slices |
| 2026-10-31 | `ca4cc18` | `log2A` from `main`'s `WordArray.log2W` and `land`, `lor`, `xor` (now on arrays) from `WordArray.bitW`, by the new `log2`, `lor` and `xor` of `WordArray` | From three alternating runs against `68afc79`: `bsqrt`, `bgcd`, `bdiv`, `btostr` ±1.7% from 4 to 1024 limbs |
| 2026-10-31 | `cae9cbe` | `shiftLeft` and `shiftRight` from `main`'s `MPN.Shift`: the limbs of the slice shifted into fresh limbs by `WordArray.lshiftW` and `rshiftW` (inlined; `copyW` for whole limbs), read where they are instead of copied first; the guards compare with `2³² − 1` (with `USize.size`, a `Nat` computed at run time, `bshl` was 20% slower at 16 limbs) | From three alternating runs against `6a76c65`: `bshl` −27% at 256 limbs, −41% at 1024, ±1% to 64; `bshr` −11% at 256, −27% at 1024, +5% at 64; `shr` −8.5% at 256, −27% at 1024, +9% to +10% at 16 and 64 (5 ns); `bgcd` ±1%, +3% at 4 limbs |
| 2026-10-31 | `9bd8680` | Decimal strings by divide and conquer from `main`'s `DecChunks.toDecimalWith` and `DecChunks.ofDecimalWith` on `ops32`, which converts slices by copying them | From three alternating runs against `11cd33b`: `btostr` and `bofstr` −1% to +1.3% from 16 to 4096 limbs |
| 2026-10-31 | `82cfdbf` | Decimal strings by chunks of nine digits from `main`'s `MPN.DecChunks` on the instance `dec32` of `DecOps`, with its own unboxed state of reading; the zero test of the chunk loop answers at once on a nonzero top limb (calling `trim` every chunk made `btostr` 4–5% slower at 4 and 16 limbs) | From three alternating runs against `d2c70ca`: `bofstr` −3% to −5% from 1 to 256 limbs, ±0.5% at 1024; `btostr` +0.4% to +2.8% |
| 2026-10-31 | `5a8644e` | Lehmer's step and half-gcd's base case from `main`'s `MPN.LehmerStep` (the checked matrix applied by `mulSubMul`, the matrix products by `mulAddMul`, the base case for any `NatOps`) on the instance `lehmer32` of `LehmerOps`, which gives the leading words, one run of `lehmerSteps` and the check of the cofactors on words (`wmat32`); the matrices are its own structure of unboxed words | From three alternating runs against `995d347`: `bgcd` −5% from 4 to 16 limbs, −2.5% at 64, ±0% at 2 and 256, +3% to +4% from 512 with 0.9% fewer instructions and 2.5% more cycles: built with `-falign-functions=64 -falign-loops=64`, this commit and the previous Lehmer step are both +0.7% at 1024 and −1.9% and −1.3% at 4096, so code layout |
| 2026-10-31 | `2ba3cc3` | Lehmer's step and half-gcd's base case by `main`'s `LinComb.mulSubMul` on `linComb32`, two passes for the two differences; the hand-written `mulSubMul` loops and the fused pass of both differences (`mulSubMul₂LoopU`) go | From three alternating runs against `1195289`: `bgcd` −2% at 64 limbs, −5% at 256, −7% at 1024, −1% at 4096, ±0% at 2 and 16384, +0.5% to +2.7% from 4 to 32 limbs (the fixed cost of the generic pass, under 20 ns) |
| 2026-10-31 | `4e3a76c` | `main`'s `LinCombOps.limb` takes a `USize` index, and `linComb32` reads by `LinComb.limbU` (`uget` against the size as a `USize`) instead of `limbAt`'s `Nat` index; here only half-gcd's matrix products (`mulAddMul`) use it | From three alternating runs against `a2b59af`: `bgcd` −3% at 64 limbs, −4.5% at 256, −1% to −2% from 1024, ±1% below 64 |
| 2026-10-29 | `fc41ac0` | The greatest common divisor from `main`'s `MPN.NatGcd` (`gcd2`, Lehmer's loop, half-gcd's loop, `lcm`, for any limbs) on the instance `gcdLimbs32` of `GcdLimbs`, which gives Lehmer's step, the words of `gcd2` and half-gcd; Lehmer's loop now switches to `gcd2` below `2⁹⁶` at every step, not only at the start | From three alternating runs against `ef05542`: `bgcd` −21% at 1 limb, −16% at 2, −17% at 4, −7% at 8 and 16, ±1% from 64 |
| 2026-10-29 | `288cfce` | `MPN.Nat` is `main`'s `GNat` (`MPN.Natural`: the word fast paths, the dispatch, the instances and their proofs against `Nat`) on the instance `natLimbs32` of `NatLimbs`, which wraps the library's operations on trimmed arrays; the division by a word of two limbs (`divRem128`) moves into the instance's `divW` and `modW` | Against the commit before: most `MPN.Nat` rows −0% to −12%, `bmul` −33% at 2 limbs; `bdiv` +18% at 2 limbs (88 → 104 ns), `bshr` +2–9% at small sizes, `bgcd` +2–4% from 2 to 256 limbs |
| 2026-10-29 | `e6ba33a` | `mulAddMul`, the kernel of the products of the matrices of half-gcd, from `main`'s `MPN.LinComb` over the instance `linComb32` of `LinCombOps` (the steps `mulAddMulStep` and `mulSubMulStep` with their values) | From three alternating runs against the schoolbook commit: `bgcd` −1% to −3% from 4 to 512 limbs, ±1% at 2 and from 2048 |
| 2026-10-29 | `03bda3b` | The schoolbook division from `main`'s `MPN.Div.Schoolbook` (the estimates, `addBack`, `divStepIn`, `divLoopIn`, for any limb width) over `WordArray`, whose instance `wordArray32` gives the multiply-subtract step with the biased borrow of `subMulBiased`; no reciprocal estimate yet (`dv = 0`) | From three alternating runs against `c78eaaf`: `div` −7% to −10% from 4 to 16 limbs, −3% to +5% from 32 to 2048; `bgcd` and `btostr` 0% to +7% at 4 to 64 limbs, ±2% above (layout). With real borrows the step was 16–78% slower from 16 limbs: its carry chain is twice as long |
| 2026-10-28 | `c78eaaf` | The residues modulo `2^(32 n) + 1` from `main`'s `MPN.FFT.Fermat` (incrAt, decrAt, normAt, addModAt, subModAt, mulPow2At and the guarded operations of `winOps32`, for any limb width) over `main`'s classes `WordArray` and `WordFolds`, with the instances `wordArray32` and `wordFolds32` (`foldlInPlace2Then`); the specialized loops are on unboxed `size_t` and `uint32_t` | From three alternating runs against `19c2e69`: `mul` +1.5–2.7% and `sqr` +2.6–3.6% from 16384 to 65536 limbs (the FFT), with the same instruction count (2.8713 against 2.8738 billion for `mul` at 32768 limbs) and 1% more cycles, so code layout; below the FFT unchanged |
| 2026-10-28 | `bf13b6b`+ | Karatsuba and the Toom methods from `main`'s `MPN.Toom` (the methods, the interpolations at natural points, the dispatcher by sizes and shapes, for any limb width) on the instance `toomOps32`, whose operations run the library's kernels on the window, or on a copy of it written back; `mulToomL` and `sqrToomL` replace Toom-3, Toom-4, Toom-6, their squares and Karatsuba (about 2,500 fewer lines); thresholds unchanged (retuning for the new dispatcher gave worse times) | From three alternating runs against `bf13b6b`: `mul` and `bmul` +2–7% from 128 to 16384 limbs, `sqr` 0–6%, `bdiv` −3 to +5%; the square at 128 limbs, the same code, varies 0–6% between builds (layout), and at Toom sizes the squares run 2% more instructions |
| 2026-10-27 | `446d4f6`+ | The products by the FFT from `main`'s `MPN.FFT.Product` (pieces, the load, pointwise, scale and recombination loops, `fftMulAt`, `fftMulModAt`, `fftSqrAt` and their proofs, for any limb width) on the instance `fftOps32` of `FFTOps`, the dispatcher's callback as the pointwise products; `MPN.FFT.Mul` 1658 → 820 lines | From five alternating runs against `446d4f6`: `mul` 16384–65536 limbs +1.0–1.7%, `sqr` ±0.7%; the same instruction count (2.6636 billion for `mul` at 32768 limbs, −0.002%) |
| 2026-10-27 | `a76ba1d`+ | The butterflies and both transforms from `main`'s `MPN.FFT.Windows` (the class `WinOps`, any limb width) on the instance `winOps32`, specialized by the compiler; `MPN.FFT.Transform` 659 → 188 lines | Against `a76ba1d`, fastest of seven: `mul` 16384–65536 limbs +1.7–3.3%, `sqr` +0.3–0.5%, with the same instruction count (2.6636 billion at 32768 limbs, ±5 thousand) and 1–2% more cycles, so code layout; the generated C is the same calls as before |
| 2026-10-26 | `38a3dd2`+ | The FFT from `main64`: one flat array of windows for both transforms (`MPN.FFT.Fermat`, `Transform`, `Mul`, with `MPN.UIntArray` and `MPN.AddSub` on 32-bit limbs), the shared algebra of `main`'s `MPN.FFT.Algebra`, and the pointwise products by the dispatcher through callbacks; it replaces `Mul.Fermat` and `Mul.FFTMul`. `fftK`: the least `k` with `4ᵏ ≥ 5 T` (a sweep of `k = 5…12`, best everywhere from 12288 limbs); `mulFFT` 36864 → 14336, `sqrFFT` 26624 → 12288 (re-tuned) | Beyond the table, against `38a3dd2`, fastest of three: `mul` 16384 limbs 6.34 → 5.76 ms (−9%), 32768: 16.3 → 13.4 ms (−18%), 65536: 38.1 → 29.4 ms (−23%), 131072: −21%; `sqr` 12288: −9%, 16384: 4.46 → 3.80 ms (−15%), 32768: 11.4 → 8.54 ms (−25%), 65536: 25.7 → 18.9 ms (−27%); 8192 and below unchanged |
| 2026-10-26 | `db8a4a9`+ | lean4-scalar-arrays 49cf1b1 → 187dcd4; the array folds of `MPN.FoldInPlace` compile to the library's folds over a `USize` range (`foldlInPlaceRange`, `foldlInPlaceRangeThen`) instead of the slice folds, without converting the bounds to `Nat` | from three alternating runs on the same library: `mul`, `sqr`, `bmul` 6–15% faster from 16 limbs, `div` and `bdiv` up to 6% at 1024; `add` 1–5% faster; `badd`, `bsub` 7–15% slower at 4 to 64 limbs (7–8 ns) and `sub` 9% at 1 limb, with no array copied (gdb on `lean_copy_sarray`), likely code layout |
| 2026-10-25 | `5114449`+ | `gcd2` from `main64`: Euclid's algorithm on pairs of words (steps `a - q b` with `q = ⌊a₁ / (b₁ + 1)⌋`, the products by `mulWide`, the last remainder in words by `rem2`) when both numbers are below `2⁹⁶`, before Lehmer's algorithm (`gcdSmall`) | from three alternating runs: `bgcd` 802 → 466 ns at 3 limbs (−42%), within 2% elsewhere. At 4 limbs it was 3% slower than Lehmer's algorithm, and finishing Lehmer's numbers with it made 5 to 8 limbs 8–16% slower, so it is not used there |
| 2026-10-25 | `5511cea`+ | `sqrt` by `main`'s generic Zimmermann recursion (`NatOps.sqrtRemAux` over `ops32`) from a root of `sqrtZimmermannSize = 40` limbs, with Newton's iteration (`sqrtNewton`) at or below `sqrtBaseSize = 16` limbs; `ops32` squares with `sqrLimbs` | from three alternating runs: `bsqrt` 64: 11.6 → 9.2 µs, 128: 27.9 → 15.4 µs, 256: 78.8 → 33.0 µs, 1024: 641 → 232 µs (0.81 → about 0.29 of `Nat`); within 3% up to 32. Tables not regenerated |
| 2026-10-25 | `307a44c`+ | Division by blocks through `main`'s base-generic `NatOps.divNorm` (from `main64`'s `Num.divNorm`) on `ops32B`, the instance with the schoolbook division at the bottom, in place of `main32`'s own `Div.DC` (deleted, 614 lines); `divDC` unchanged | `div` within ±5% of the table: 256 limbs 37.3 → 39.1 µs (+5%), 1024: 329 → 325 µs, 2048: 950 → 920 µs, 4096: 2.74 → 2.61 ms (−5%); `divDC` not retuned |
| 2026-10-25 | `1861d4d`+ | Half-gcd's base case of word matrices: `main`'s `NatOps.smallBase` with `steps32`, Lehmer's steps applied by `mulSubMul₂` and the matrix updated by the new `mulAddMul` (`a x + b y` in one pass), as on `main64`; `hgcdBase` 64 → 128 and `gcdHalf` 3072 → 1536, from sweeps (base 128 within 1–2% of 256; half-gcd from 1536 limbs 5% faster, 3072: 23%) | `bgcd` 4096 limbs 18.5 → 15.3 ms, 8192: 51.6 → 41.9 ms, 16384: 138 → 115 ms (−17%); 2048: 5.74 → 5.13 ms. With the row below, 31–35% faster from 4096 limbs than at `277bb82`; 3.9–4.7 times `Nat` from 2048 limbs (was 5.2–6.8) |
| 2026-10-25 | `277bb82`+ | Half-gcd's base case of Lehmer's steps up to `hgcdBase = 64` limbs (was 8), from a sweep of base sizes 8 to 256 (64 and 128 within 1%, 256 slower); `gcdHalf` 4608 → 3072, where half-gcd with that base starts to win (2560: +5%, 3072: −5%, 4608: −19%) | Beyond the table: `bgcd` 4096 limbs 22.3 → 18.5 ms (−17%), 8192: 64.9 → 51.6 ms (−20%), 16384: 168 → 138 ms (−18%); 5.2–5.6 times `Nat` from 3072 limbs |
| 2026-10-25 | `0b72bf5` | No change: a sweep of `k = 5…13` pieces for one FFT level (`fftMul`, `fftSqr`) at 8192 to 131072 limbs per operand, to try `main64`'s `fftK` (the least `k` with `4ᵏ ≥ 10 T` in 64-bit limbs, `5 T` here) | `fftK` is within 3% of the best `k` at every size (8192: `k = 7` 3.90 ms against 4.00 at `k = 8`; 65536: `k = 10` 40.5 against 41.2 ms); `main64`'s formula would be 42% slower at 8192 limbs, 11% at 16384, 20% at 32768 and 7% at 131072, so the list-based FFT keeps it |
| 2026-10-25 | `e8b34d7` | the tables regenerated on lean4-scalar-arrays `49cf1b1` (they were at `4204471`, before the generic layer and the port of `foldInPlace`), the fastest of three runs | Against `4204471`: `shr` 1.1–2.2× faster from 2 limbs (opaque array types), `bshr` and `bshl` 10–40% faster, `add` and `sub` 10–20% faster below 64 limbs, `mul1` 10–15% faster from 128 limbs; `mul` 8 limbs 1.00 → 1.11 and `sqr` 16 limbs 1.37 → 1.52 (a fold per row, see the row below); `btostr` from 256 limbs 0.09 → 0.03–0.05 (`19ef59a`) |
| 2026-10-25 | `3a96125` | lean4-scalar-arrays `8ae4933` → `49cf1b1`, which dropped the array `foldInPlace`: `MPN.FoldInPlace` defines it again as the same loop and `@[csimp]` runs the slice fold `foldlInPlaceThen`, whose inner loops compile to the same C; each call converts the slice's `Nat` bounds (about 1.5–2 ns) | From three alternating runs against `94c06d0`: `sqr` 16 limbs 162 → 194 ns (+20%), 64: +10%, 256: +7%; `mul` 16 to 256 limbs +10% (`rowsMul`, a fold per row); `sub` −5 to −13%, `shr` −10 to −35%; `add`, `mul1`, `div`, `bgcd`, `btostr` within ±5%. Tables not regenerated |
| 2026-10-20 | `f81b3d0` | Half-gcd: matrices applied to the low halves only (`applySplit`), with the exact relation `(a, b) = M (x, y)` proved; from 4608 limbs (was 8192) | Beyond the table: `gcd` 8192 limbs 85 → 64 ms (−25%), 12288: 157 → 112 ms, 16384: 242 → 170 ms, 32768: 0.66 → 0.43 s (3.1× faster than Lehmer) |
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
