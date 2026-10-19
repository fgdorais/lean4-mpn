# TODO

The library is verified end to end: every public operation is proved correct against `Nat`, with
no `sorry` and only the standard axioms. What is left is speed, more operations, and an API.
Items are roughly in order of value within each section.

## Performance

Time now goes mostly into the schoolbook product, by columns since `Mul.Comba`: 75–77% of a
product at 1024 and 4096 limbs and 70% of a square, with `perf` (2026-10-16). The linear passes
(`addInto`, `subInto`, `addDiffInto`, Toom-3's evaluations and interpolation) take 14% of a product
and 19% of a square, allocation 2–3%. With 32-bit limbs, a product needs 4× as many limb products
as GMP's, which is most of the gap above 64 limbs; `march = "native"` (see the README) makes
products 5–12% faster with AVX2. What is left for products is mostly the linear passes and
algorithms (below). Since that profile, Toom-4, Toom-4 by 3, Toom-4 squaring (2026-10-17) and the
FFT (2026-10-18) made products 2–8% faster from 1024 limbs, squares 7–10%, and products 29%
faster at 65536 limbs; the profile above predates them.
Division is 2.4 of our own `n × n` products per `2n / n` division, where GMP's is about one, so it
trails by 1.5× multiplication's gap; see BENCH.md for the current numbers.

- [ ] **Quotient-only division** (GMP's `mpn_div_q` with `divappr`): `/` computes the remainder it
  throws away, through the low-half products of Burnikel–Ziegler and Algorithm D's last steps. An
  approximate quotient, off by at most one and then checked, would need high-half products
  (`mulhi` variants of Comba, Karatsuba and Toom-3) and a proof of the error bound: a big project.
  Its profile at 1024 limbs is Comba about 50% and `subMul1` 25%, so faster products help it most.
  Ruled out: two quotient limbs per pass (`submul_2`, whose sums overflow 64 bits with 32-bit
  limbs) and a carry chain under three operations in `subMul1` (LLVM reassociates it).
- [x] **A 3-by-2 division step with a precomputed reciprocal** (GMP's `udiv_qr_3by2`, behind
  `mpn_divrem_2`; `div32Step`): with 32-bit limbs Möller and Granlund's step fits in 64-bit words,
  two products and a few corrections instead of the hardware division of `div2Step`. It checks its
  result exactly (`q D + r = R β + x`, `r < D`), so neither the reciprocal nor the error bound needs
  a proof; a failed check leaves the remainder `D`, after which every check fails, and the division
  tests the last remainder once and redoes the work with `div2Step` if needed, which never happens.
  `MPN.Nat` divided by `10¹⁸`: 6.5 ns per limb instead of 15 (256 limbs: 3.81 → 1.75 µs, 8.2 → 3.6×
  GMP; 5 limbs even with GMP). Branches in the step cost more than the step itself: the compiler
  joins `if`s between pairs, even two component `if`s on the same condition, and boxes the words of
  the pair, an allocation per limb, which held a checked version with branches at 12 ns per limb.
- [ ] **The 3-by-2 step for Algorithm D's quotient estimates** (low value on Zen 3): each
  quotient limb of `divRemBasecase` estimates with a hardware division (`qEstimate`, then
  `qEstimate3`), where GMP's `mpn_sbpi1_div_qr` uses `udiv_qr_3by2`. Profiled on 8 ÷ 4 and 16 ÷ 8
  limbs, that division is 4–6% of the time (in `divStepInFast`, 18–25%), and on Zen 3 a reciprocal
  step costs about as much as the division (see `divRem1`), so a few percent at best, for a
  reciprocal threaded through Algorithm D and its compiled twin. Small divisions spend more on
  allocation (15–25% at 4–8 limbs) and on the `subMul1` pass. Worth it only on CPUs with slow
  64-bit division.
- [x] **Carry chains on ARM** (Apple M2, 2026-10-17): `mul1`, `add` and division ran 1.4–2.1×
  slower on the M2 than on Zen 3 while GMP ran as fast or faster. LLVM put the loop-carried carry
  first in each step's sum, so in `addMul1Fast` the chain per limb was add → `umaddl`
  (multiply-accumulate) → shift, with no unrolling, and on x86 the same order hit every other limb.
  Every carry-chain step now computes the part that does not depend on the carry first and uses it
  twice, for the low word plus the carry and for the carry out (`UInt32.toUInt32_add`), which keeps
  the carry last: one add and one shift per limb on both targets. Prototyped variants, timed on both
  machines, ruled out splitting the sum into 32-bit halves (shifted and extended operands cost a
  cycle each on Apple cores), a carry select for addition, and a 64-bit carry in the folds (no
  faster than a 32-bit one). Zen 3: `add` −16%, `sub` −26%, division −16% at 64 limbs; Apple M2
  (bench at 1024 limbs): `mul1` 1.9×, `add` 1.36×, division 1.34× faster. Subtraction's borrow,
  taken as a sign bit, compiled to a compare and a flag read on AArch64 and barely gained; it now
  adds the complement and keeps `1` minus the borrow (`subWithCarryWord`), the chain of addition:
  `sub` 1.37× and `bsub` 1.35× faster on the M2 at 1024 limbs, level with `add`; +4% on Zen 3.
- [ ] **Toom-3's evaluations and interpolation in fused passes** (3–4% of large products): each
  operand takes ten passes for its three values (`eval1`, `eval2`, `eval3`, two `addLimbs` and
  up to two `mulRow`s each), and the interpolation eight `subVal`s, three `mulRow`s and three exact
  divisions, each pass with its own array. One pass that reads the three parts once and writes the
  three values, prototyped without proofs as a tail-recursive loop over the arrays (like
  `mulSubMul₂`), is 2.7× faster than the three evaluations (`k = 342`: 2.55 → 0.91 µs), which is
  1.7% of a product of 1024 limbs and 2.1% at 4096, since Toom-3 runs only one or two levels; the
  interpolation should give about as much, and `toom32`, `toom42` and `toom3Sqr` share the
  pieces. (Moving it in place, without fusing, was estimated under 1% from the assembly half.) A
  fold over several arrays in lean4-scalar-arrays, checking that they are unshared once instead
  of at each step, would make such passes cheaper still, and `mulSubMul₂` faster below 32 limbs.
- [ ] **A shorter dependency chain in `divRem1`** (for CPUs with slow division; GMP's
  `mpn_div_qr_1n_pi1`): the loop is bound by the latency of one step, about 15 cycles (3.3 ns per
  limb on Zen 3), since each step needs the previous remainder; the rest of the loop (1.4 ns per
  limb) runs in parallel. A precomputed reciprocal (Möller–Granlund's `udiv_qrnnd_preinv`) was
  prototyped and is 3% *slower* there, because Zen 3's divider is fast; it would pay on CPUs with
  slow 64-bit division (Intel before Ice Lake). `div_qr_1n_pi1` keeps a partly reduced two-limb
  remainder and takes the quotient off the chain, about one multiply-add per step. `divRem1` is
  behind division by one limb and `toString`. Measured again with the branch-free, checked form of
  `div32Step` (2026-10-17), in case the first prototype had paid for pairs boxed at a join: 3.17
  ns per limb against 3.31 at 1024 limbs, slower below, before normalizing the operands, which it
  would add. Both steps are a chain of about 14 cycles, so only `div_qr_1n_pi1`, which takes the
  quotient off the chain, could pay here.

Done this round: word carries and hoisted slice fields in the folds; in-place Algorithm D with
`subMul1` (34 allocations per 32 ÷ 16-limb division instead of 270); `foldInPlaceThen`
(lean4-scalar-arrays#22) for `addMul1Set`, `addInto` and `subInto`, which allocate no result pairs;
`toom3Sqr`; guards of the compiled loops against a literal below `2³²` instead of `USize.size`
(11–15% on small products); the schoolbook square in one final pass (`sqrAddDiag`) without row
slices, faster than multiplying from 16 limbs; Knuth's correction of the quotient estimate, which
removed the add-backs (42% of quotient limbs at 256 limbs); the remainder of a normalized division
shifted back instead of divided by a limb; `trim` without a closure (`popWhile`'s predicate was
called through `lean_apply_1`); a quotient-only `div`; division by two limbs in one pass
(`divRem2`); the schoolbook product by columns (Comba, 14–24% from 8 limbs up) and the square
(22–25% from 64 limbs up); Karatsuba's middle term added in one pass over `z₁` with `addDiffInto`,
which keeps a carry between `-2` and `1` as a word plus 2, where two subtractions and an addition
took three passes (the combination 38% faster, products 2–5% faster from 256 limbs up); Toom-3's
exact divisions without the hardware divider, by 2 with `shrLimbs` and by 3 with the inverse of 3
modulo `2³²` (`divExact3`, 2.2× faster than `divRem1`; products 3–8% and squares up to 10% faster
from 576 limbs up, Toom-3 from 480 and 720 limbs instead of 576 and 892); both shifts in one pass
with the slice folds of lean4-scalar-arrays#27 and #28; `push` inline upstream
(lean4-scalar-arrays#24); the conversions to and from `Nat` by halves, joined or split with shifts,
and 64 bits at a time below 64 limbs for `ofNat` (`toNatFast`, `ofNatFast`; 4096 limbs: 6.1 → 0.39
ms and 2.2 → 0.24 ms, still about one operation on `Nat`, some 40 ns, per two limbs); Comba's
columns from 32 limbs as whole products in one sum that counts its wraps (`colLoopW`, an addition
with carry per product, not vectorized but faster than the vectorized halves: products −5% from
64 limbs, −7% at 1024 and −10% at 4096). An earlier try of that loop, when the column loops still
returned pairs, was slower above 32 limbs; with both loops in one function, products below 16
limbs lost 5–8% to the setup of the unrolled loop, so `combaMul` chooses once per product.

Tried without gain: Toom-3's assembly by copies, `c₀` and `c₄` written into place and three
`addInto`s instead of five on a zeroed array (within 1% from 512 to 4096 limbs, where Comba is
72% of a product); Karatsuba into one array, products at an offset with the scratch above (GMP's
style), prototyped without proofs on an offset copy of Comba's kernel: within ±1% of the allocating
version from 128 to 448 limbs, with the combination in two passes or in one fused pass (after saving
the top half of `z₀`, which it overwrites before reading). `perf` attributes 5–11% of a product to
allocation and copies, but mimalloc's small allocations are cheap and an array of products still
needs its evaluation sums as separate arrays (a slice of the scratch array would be shared with the
array being written, and copied). In Comba's column loop, unrolling by two (no change), and
reading `b` reversed so that both operands go forward (the copy costs more than it saves); `divRem1`
on `foldrInPlaceThen` over a copy (the loop is bound by the division, and building the slice costs
10–25 ns per call, 5–12% slower below 16 limbs), which also rules out slices for the per-row folds
(`addMul1Set`, `addInto`, `subInto`), called once per row; passing `subMul1`'s borrow to the end of
the step through `foldInPlaceThen` (the step still returns a pair, and the compiler already reused
the memory of `subMul1`'s); a `USize` twin of `divRem1` (the hardware division hides the loop).
The Karatsuba threshold inside whole products: from 96 × 96 to 4096 × 1024, every value from
48 to 80 is within 1% of the tuned 64 except at `1700 × 1024`, where 48 is 6% slower, and 32 and 40
are 3–29% slower. A build that compiled the library with a stale `mulKaratsuba = 48` once ran
`1700 × 1024` 12% faster with the same algorithm choices; that did not reproduce, so it was likely
code layout. Twins of `ltLoop` and `topSizeLoop` would not show: `lt` runs once or twice per
block of the division, and `topSize` usually stops at the first limb.

## Algorithms

- [x] **Divide-and-conquer division** (`Div.DC`, Burnikel–Ziegler): blocks of half the divisor,
  digits from recursive divisions by its top half and the low-half product, from 176 limbs.
  The gap no longer grows with size: 7.9–8.9× behind `Nat` from 128 to 4096 limbs, measured on
  the quotient alone (an earlier benchmark timed two divisions on the `Nat` side and showed half
  that).
- [x] **Toom-3 by 2** (`toom32`, GMP's `mpn_toom32_mul`): for a longer operand between four
  thirds and twice as long as the shorter, from 128 limbs, it splits them in three and two at a
  third of the longer, where `toom3` split both at a third of the shorter and left a long top part
  in its five products; four products, at the points `0, 1, 2, ∞`. Shapes of 3:2 and 3:1 (which
  halves into 3:2) are 27–39% faster from 512 limbs (`1536 × 1024`: 406 → 247 µs, 8.2 → 5.0×
  GMP). From 160 limbs at first: the tuner found 120, but direct timings were slower until about
  150; after the carry-last steps the tuner finds 128–136 on four machines (Zen 3, an Apple M2,
  two GitHub runners), so 128 since `2f9c5e6`.
- [x] **Toom-4 by 2** (`toom42`, GMP's `mpn_toom42_mul`): for a longer operand between fifteen
  eighths and twice as long, from 224 limbs, it splits it in four and the shorter in two at half
  the shorter; its product has degree four, like Toom-3's, so it shares Toom-3's five points and
  interpolation (`toom3Finish`). 3–7% faster in that band (`2000 × 1024`: 382 → 357 µs,
  `3900 × 2048`: 1062 → 988 µs). Between five thirds and fifteen eighths it is within ±2% of
  `toom32`, and below five thirds slower, so `toom32` keeps those shapes.
- [x] **Toom-4 and Toom-4 by 3** (`Mul.Toom4`; GMP's `mpn_toom44_mul` and `mpn_toom43_mul`):
  seven and six products, with natural-number points `0, 1, …, d - 1, ∞`, so that the
  interpolation (values divided by their point, divided differences, then Horner's rule back to
  the coefficients) only subtracts parts and divides exactly, by `2`, `3`, `4` and `5`
  (`divExactOdd`, which division by `3` now shares). Most of its passes are `r - a v` and the
  evaluations `r + a v`, each in one pass with `subMul1` or `addMul1` (`subMulVal`, `addMulVal`):
  without them, Toom-4 was no faster than Toom-3, as an earlier prototype had found. Toom-4 by 3
  takes the shapes from six fifths to fifteen eighths from 176 limbs, Toom-4 balanced ones from
  416 (`mulToom43`, `mulToom4`, tuned on Zen 3). Shapes near 4:3 are 6–19% faster (`683 × 512`:
  85.0 → 71.4 µs, `2730 × 2048`: 681 → 561 µs); balanced products even to 640 limbs, then
  `1536`: −8.5%, `4096`: 1.43 → 1.31 ms (−8%); division at 4096 limbs −2%. On an Apple M2 the
  unverified prototype gained about as much (Toom-4 3.5–8% from 768 limbs, Toom-4 by 3 6–20%).
- [x] **Toom-4 squaring** (`toom4Sqr`): seven squares with the evaluations and interpolation of
  `toom44`, from 576 limbs (`sqrToom4`, tuned on Zen 3, below Toom-3 squaring's 656–672). `sqr`
  1024 limbs: 116 → 108 µs, 2048: 335 → 307 µs, 4096: 935 → 836 µs (−10%); `bsqrt` 4096: −3%.
- [x] **FFT multiplication and squaring** (`Mul.FFT`, `Mul.Fermat`, `Mul.FFTMul`; GMP's
  `mpn_mul_fft`): Schönhage–Strassen modulo `F = 2ᴺ + 1` with `2ᵏ` pieces, `ω = 2^(2N / 2ᵏ)`, a
  recursive radix-2 transform and pointwise products by the dispatcher, all proved: finite sums
  and the inversion of the transform modulo `F` (the geometric sums of length `2ᵏ` are products of
  factors `1 + x^(2ˢ)`, one of which vanishes, so no division or primality is needed), residues on
  `n + 1` limbs with in-place sums and differences and products by powers of two in two arrays,
  the butterflies by divisibility in `Int`, and `fftMulAt_spec` for the whole product. From
  18000 limbs (`mulFFT`) and 16000 for squares (`sqrFFT`), on Zen 3 (32768 and 28672 since
  Toom-6); `fftK` chooses `k`.
  `65536 × 65536`: 64.9 → 46.1 ms (−29%), squares 44.2 → 31.0 ms. The transforms were first 15
  passes and as many arrays per butterfly; in-place residue operations brought the crossover
  from about 48k to 18k limbs. GMP's `√2` trick does not apply: `n` is set by the size of the
  coefficients, not by the order of the roots.
- [ ] **FFT, next:** the pointwise products of residues modulo `F` by the FFT itself at very large
  sizes (GMP's recursive `mpn_mul_fft`), a fused butterfly (one pass for `a ± 2ˢ b`), and `fftK`
  tuned per machine.
- [x] **Toom-6 and Toom-6 squaring** (`Mul.Toom6`): eleven products at `0, 1, …, 9, ∞`, the
  natural-point interpolation of Toom-4 with divisions by `2` to `9` (`divExactOdd` for any odd
  divisor, by its inverse modulo `2³²`). The interpolation (about a hundred passes) and its proof
  are generated by `scripts/toom_interp.py` from the exact value of each intermediate, one step
  lemma per pass, checked by `lia`; the evaluations are one `addMulVal` pass per part
  (`evalPoly`), proved once for any list of parts and point. Balanced products from 1344 limbs
  (`mulToom6`), squares from 1792 (`sqrToom6`), tuned on Zen 3, which moved the FFT to 32768 and
  28672 (`mulFFT`, `sqrFFT`). Same binary, against Toom-4 and the FFT at their old thresholds:
  products `4096` −9%, `8192` −11%, `16384` −14% (9.07 → 7.76 ms), `1.5·2ᵏ` sizes −2 to −8%;
  squares −6% from 6144 limbs. Between 1344 and 3776 limbs the gain oscillates from −5% to +4%
  (mean −0.7%), with the sizes of the parts against the thresholds below.
- [x] **Schoolbook products by rows** (`Mul.Rows`, `rowsMul`): each row `aᵢ b` adds the low half
  of `aᵢ b_j` and the high half of `aᵢ b_{j-1}` into `UInt64` accumulator `i + j`, one
  `foldInPlaceThen` per row with no carry chain, so LLVM vectorizes it (SSE2 by default); one pass
  at the end propagates the carries. Proved with the value of the wide limbs (`accVal`) and a
  bound of `2³³` per row on each accumulator. A `perf` profile had shown the Comba kernel at 56–76%
  of `mul`, at 2.7 cycles and 12.7 instructions per limb product (4.7 per cycle: instruction
  bound). From 16 limbs in all (Comba below, cheaper to set up). Kernel 0.58 → 0.45 ns per limb
  product at 32 limbs, 0.39 → 0.27 at 256; the multiplier must enter the loop as a `UInt32`, or
  LLVM vectorizes a 64-bit multiply. Re-tuned: Karatsuba from 112 (was 64) and every threshold
  above it higher. `mul` 64 limbs −30%, 1024 −23%, 4096 −14% (4.58× `Nat`); `div` 4096 −18%.
  Squares too (`sqrRowsMul`, 2026-10-19): the rows `aᵢ a[i + 1...]` into accumulators at limb
  `2 i + 1` with the same `addRow`, then `2 S + D` and the carries in one pass, from 16 limbs.
  `sqr` 64 limbs −27%, 256 −31%, 4096 −19% (3.18× `Nat`); Karatsuba squaring from 160, and
  Toom-3 squaring hardly wins any more (Toom-4 squaring from 832). On the M2 (`e0a0473`): `sqr`
  64 limbs −15%, 256 −24%, 4096 −18% (3.52× `Nat`); Karatsuba squaring from 160 as on Zen 3,
  Toom-4 squaring from 960 (flat 960–1056), Toom-3 and Toom-6 squaring never win below their
  caps (944, 3776), FFT squaring from 24576.
- [ ] **Toom-8½, Toom-6 by 5 and the like**: Toom-8 gained 7–11% over Toom-4 in a one-level
  prototype at 6144–16384 limbs, about as much as Toom-6; the generator handles any degree.
  Unbalanced Toom-6 shapes (beyond six fifths) still go to Toom-4 by 3.
- [ ] **The rest of `Nat`:**
  - [x] shifts by bits (`<<<`, `>>>`, `Bits`): one pass each, in place over a copy with
    `foldrInPlaceThen` and `foldlInPlaceThen`, even with `Nat` from 1 to 1024 limbs. The left
    shift computes each carry from its limb alone, so the loop has no dependency chain (36%
    faster than carrying through the sum);
  - [x] bitwise `&&&`, `|||`, `^^^` (limbwise with `ofFn`, then trimmed);
  - [x] `log2`;
  - [x] `pow`, by repeated squaring with `sqr`;
  - [x] `gcd` and `lcm` (`MPN.Nat`): Lehmer's algorithm with single-word cofactors, checked by
    their determinant, and Euclid on words. Each new number is a difference of two multiples,
    computed with a biased carry, and the cofactors stay below `2³¹`, so that their determinant is
    checked on `Nat` without GMP (`lehmerStep`); from 32 limbs, both new numbers come from one pass
    that reads each limb once (`mulSubMul₂`, a tail-recursive loop over both arrays: the pass 17–27%
    faster from 64 limbs, `gcd` 6% at 64 limbs and 30% at 1024), and below, from two folds of
    `mulSubMul`, since the loop's exclusivity checks and extra pair made `gcd` 4–6% slower from 4 to
    16 limbs. The word steps divide once per quotient and stop by Jebelean's condition
    (`lehmerSteps`). Faster than `Nat` on words, 3.6–4.8× behind GMP from 4 to 1024 limbs (from
    9–18×). This is already GMP's `hgcd2` in our limbs (two-limb leading words, one-limb cofactors);
    the next size up, 124-bit words and 62-bit cofactors, would need Euclid in emulated 128-bit
    arithmetic, already 11–21% of the time in 64-bit, for passes that do twice the products for half
    the steps, so it is not worth it. Left: subquadratic `hgcd`, GMP's advantage from a few hundred
    limbs.
  - [x] integer square root: Newton's iteration at growing precision, from the root of the top
    half (`sqrt (n / 4ᵏ)` for `k` a quarter of the bits), which starts within `2ᵏ` above the root;
    one Newton step, which is at least the root by AM-GM, then steps down while `x² > n` with one
    square (`sqrtFix`), where the iteration took a second division to stop. Faster than `Nat` up
    to 4 limbs, 1.0–2.2× behind above (from 1.6–4×).
  - [x] `toString`/`ofString?` (`Decimal`), like GMP's `mpn_get_str`/`mpn_set_str` below their
    thresholds: chunks of nine digits, by `divRem1` by `10⁹` one way and a fold over the
    characters the other. Equal to `Nat.repr` and `String.toNat?`, and 10–20× faster than
    `Nat`'s, which works digit by digit, from 4 limbs up; words go to the runtime's `USize.repr`.
    Both are quadratic: GMP's subquadratic versions (by powers `10^(9·2ᵏ)`) would be next.
    Reading a short number costs 350 ns against 140 ns, mostly in `String.isNat` and the string
    iterator.

## API

- [x] **A `Nat`-like type:** `MPN.Nat`, a word below `2⁶⁴` and trimmed limbs above, with the
  instances, truncated subtraction and the bijection with `Nat`. About 15 ns per operation on
  words, against 9–10 ns for `Nat`, whose small values need no allocation.
- [ ] **The fixed cost of small divisions:** `MPN.Nat.div` takes 86 ns for 4 limbs by 2, 245 ns
  for 8 by 4 and 555 ns for 32 by 16, against 47, 95 and 154 ns for `Nat`. Done: up to four limbs
  by a word of two, the division runs on words alone, with three `div2Step`s after the shift
  (`divRem128`; 159 → 86 ns), and `/` by a word uses `div2`, which allocates no remainder; the
  normalized dividend is divided in place when its top limb is below the divisor's
  (`divRemBasecaseTop`), which saves its copy and one step of Algorithm D (12–22% from 3 to 16
  limbs); an `MPN.Nat` divided by a word goes to `divRem1` or `divRem2` without an array for the
  word (`divRemWord`, 2 limbs 192 → 170 ns; `%` by a word returns the word); Algorithm D works in
  one array, with each quotient limb in the freed top limb of its window, and its compiled step
  allocates no pair (`divLoopIn`, `divStepInFast`; 11–19% from 3 to 64 limbs); division by two
  limbs reads the limbs of the normalized dividend from the dividend as it needs them, instead of
  a shifted copy (`shlLimbU`; `MPN.Nat` divided by `10¹⁸`: 5 limbs 180 → 149 ns, 16 limbs 312 →
  294 ns, even from 64). Left: the 2n ÷ n rows from 8 limbs go through Algorithm D, whose fixed
  cost is the normalization of both operands and their arrays.
- [x] **Words near `2⁶⁴` in `MPN.Nat`:** a sum or product of two words that overflows went
  through `limbsOfWord` and the array functions (about 95 ns). `mulWide` computes the product from
  the four products of halves, and `wideOf` makes the three or four limbs directly: `badd` at 2
  limbs 95 → 34 ns (0.42× `Nat`), `bmul` 92 → 50 ns (0.62×).
- [x] **Per-dependency configuration.** Lake builds a dependency with that dependency's own
  settings; the package's `lakefile.lean` now reads the options of a project's `require` (or
  `-K`): the thresholds, keyed by the fields of `Config`, and `march`, which compiles the C code
  with `-march=<value>` (`native`: 5–12% faster products with AVX2). Keys have no dots, since TOML
  passes a quoted key as one name, and changed options need `lake build -R`.

## Proof engineering

- [ ] **The slice coercion `a ↦ a.toSlice 0 a.size`.** `simp` rewrites the size inside it before
  `toNat_toSlice` can fire, and proofs work around that with `rw [toNat_toSlice]` first or with
  one equation per branch (`divMod_of_topSize_eq_one`). A more general simp lemma for
  `toNat (a.toSlice 0 n)` with `a.size ≤ n` would remove most of these.
- [ ] **Report to Lean:**
  - a private `implemented_by` target attached with a separate `attribute` command is not
    visible to other modules (worked around in lean4-scalar-arrays#14 by making the impls
    public);
  - equation lemmas of a recursive definition whose body contains an `if` on large `UInt64`
    literals make the kernel recurse too deeply (worked around by moving the step out of the
    recursive definition, `Div.Basecase.divStepLimb`);
  - the kernel overflows its recursion depth checking `rfl` between a definition and its own
    unfolding when an argument contains `x * 4294967296` with `x : UInt64` and the body compares
    that argument with a literal (minimal case: `D5 q (wt.toUInt64 * 4294967296) … = (qRef q
    (wt.toUInt64 * 4294967296) …).1 := rfl` with `qRef` an `if r < 4294967296 …`); the same with
    `<<< 32` or a variable in place of the literal is fine (worked around in `qEstimate3`);
  - the compiler replaces a literal `true` with a `decide` that is known to be `true` in that
    branch, such as the condition of an enclosing `if h : … then`, which put an extra `and` with a
    loop-invariant `Nat` comparison in the carry chain of `addAtFast` (seen with the `Bool` carry
    of `UInt32.addWithCarry`, before the fold switched to `addWithCarryWord`).

## Tooling

- [x] **Benchmarks on `main`:** `lake exe bench` times each operation against `Nat` (the limb
  operations by default, `shr` included, and the `MPN.Nat` ones by name, as in BENCH.md);
  `lake exe bench --no-nat mul 256` runs one case alone, for a profiler. Results are checked in
  O(1) on both sides (a hash of an `MPN.Nat` result once cost a pass over its limbs).
- [ ] **Defaults that suit more machines.** `lake exe tune --verbose`, run again on four machines
  after the carry-last steps (2026-10-17: Zen 3, the dev box; an Apple M2; GitHub's EPYC 7763 and
  Xeon 6973P-C), agreed on Toom-3 by 2, Toom-4 by 2 and unbalanced products, whose defaults moved
  to 128, 224 and 128 (`2f9c5e6`). The faster basecases also pulled the M2's thresholds close to
  the others (divide-and-conquer division from 56 to 168 limbs). Still split: `mulKaratsuba`
  (Zen 3 and the EPYC 76–80, the M2 and the Xeon 64; flat within 1% in whole products), `divDC`
  (Zen 3 now 224, the M2 168, the runners 104–136, default 176) and squaring on the M2
  (Karatsuba from about 196 and Toom-3 not below 980, against about 96 and 670–720 on x86), which
  would need defaults per architecture (`mpn_config%` choosing by the build target). With Toom-4
  (2026-10-17, M2 at `ec9d59e`): multiplication agrees (Toom-4 by 3 from 176 on Zen 3 and 192 on
  the M2, Toom-4 from 416 and 480), but squaring does not: on the M2 Karatsuba squaring beats
  Toom-3 squaring to the 972-limb cap and Toom-4 squaring to about 1000–1100, so `sqrToom4 = 576`
  costs it up to 8% between 576 and 1000 limbs. The FFT (2026-10-18, M2 at `8c8f1cf`) crosses
  over at the same size on both machines, flat from 16384 to 18432 limbs: the M2 tunes
  `mulFFT = 18432` (default 18000) and `sqrFFT = 18432` (default 16000, which costs it 1–4% between
  16000 and 18432 limbs, since its squares below are cheaper); with Toom-6 (2026-10-18) the FFT
  crossover moved to 32768 limbs on Zen 3 and on the M2 (`6455f73`), where it is a step: 3.5%
  slower at 30720, 7.5% faster at 32768. On the M2, Toom-6 products win from 1664–1728 limbs
  (flat within 1% from 1600; Zen 3 1344), but Toom-6 squaring never beats Toom-4 squaring up to
  3776 (1.7% behind there; Zen 3 1792), so `sqrToom6 = 1792` costs the M2 2–11% between 1792
  and 3776 limbs; its FFT squares win from 22528 (Zen 3 28672). With the row kernel (M2 at
  `caab3b6`), every product threshold rose more on the M2 than on Zen 3: Karatsuba 128 (Zen 3
  112, flat 104–132), Toom-3 912 (640), Toom-3 by 2 248 (192), Toom-4 by 2 512 (304), Toom-4 by 3
  336 (272), Toom-4 992 (608), Toom-6 3392 (1792), the FFT 32768 (36864), and division by blocks
  from 104 (176). Defaults per architecture will come,
  but after the remaining algorithms are verified, so that the tuning sees all of them.
- [ ] **A raw GMP baseline.** The `Nat` column is Lean's wrapper around GMP, which copies both
  the operand and the result and allocates twice per operation, so below about 64 limbs it
  measures mostly that overhead (we beat it there). Calling `mpn_*` directly needs C, so it
  belongs on the `64bit` branch.
- [x] **Executables initialize all of Lean.** `Config` imports `Lean` (as `meta`) for its
  `mpn_config%` elaborator. A main file that is not a `module` calls the meta initializers of
  everything it imports, so it links and initializes all of Lean: 124 MB and about 20 ms at
  startup. A main file that is a `module` calls only the runtime initializers, which skip `meta`
  imports: `bench` and `tune` are now modules, 3.9 MB each, and the README says so for programs.
- [x] **CI** (`.github/workflows`): `CI` builds the library with warnings as errors, runs
  `lake test` and builds `tune` and `bench` on every push to `main` and every pull request; `Tune`
  runs weekly and on demand and `Bench` on demand (operations and sizes as inputs), each with its
  results in the run's summary. Shared runners are noisy and their machines vary, so these are a
  rough check of the defaults and a sanity check of the speed, not the numbers of BENCH.md.
- [ ] **Decide what to do with the `64bit` branch** (C and GMP experiments, benchmarks), which is
  kept off `main` on purpose.

Profiling notes: `perf record` (without `-g`, which misattributes in these binaries) for where
time goes; `valgrind --tool=callgrind --toggle-collect=<C symbol>` for exact allocation counts
per operation; `gdb` with a breakpoint on `lean_copy_sarray` for unexpected array copies; the
generated C in `.lake/build/ir` to check that a `@[csimp]` twin is really called. `lake build`
does not rebuild `bench` and `tune`. The benchmark's trials (2 ms) are too short to profile: a loop
in a scratch Lake project that requires this one by `path` reuses its build. `perf record` in front
of `taskset` samples only the startup, so pin the whole command or not at all.
