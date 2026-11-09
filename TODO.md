# TODO

Both libraries are verified end to end: every public operation is proved correct against `Nat`,
with no `sorry` and only the standard axioms. What is left is speed, sharing, tuning, more
operations, and tooling. The timings and the history of the changes that affected them are in
[MPN32/BENCH.md](MPN32/BENCH.md) and [MPN64/BENCH.md](MPN64/BENCH.md); what was done before the
two widths moved into one package is in the history of `MPN32/TODO.md`.

## Performance

The target on 64-bit limbs (since 2026-11-09): within 4× of GMP's kernels, the `mpn` column of the
bench, from 16 limbs, and within 4× of `Nat` below, where allocating results is part of Lean's
cost. Against `mpn` (`0987e74`), products are 2.0–3.3×, squares 2.0–3.7×, division 1.5–3.0× from 12
limbs and `gcd` 1.5–2.4×; the items below that are over it come first.

- [ ] **The square root** is 10–27× `mpn_sqrtrem` up to 64 limbs and 3.4–4.3× from 256 on 64-bit
  limbs (6–45× on 32-bit limbs), a gap the `Nat` column hid, since Lean's `Nat.sqrt` is not GMP's.
  Small sizes first: `MPN.W64.sqrtRem` goes through `GNat` (`Bridge.sqrtRem`) and Zimmermann's
  recursion down to one limb (`sqrtBase = 1`), where GMP's base case divides by its own root.
- [ ] **Decimal strings** are 5.7–20× `mpn_set_str` to read and 3.6–6.6× `mpn_get_str` to write on
  64-bit limbs (`MPN.Nat`'s `ofString?` 8–31×, which also checks the string), 12–22× and 7.6–8.7× on
  32-bit limbs; against `Nat` they look fast, since Lean's conversions work digit by digit.
- [ ] **Subtraction on 64-bit limbs** is 4.2–4.3× `mpn_sub` from 128 limbs, where `add` is 3.4–3.6×.
- [ ] **Division on 64-bit limbs**: since `c4bc02b` (Barrett's division by the top half of the
  divisor) `Num.div` runs at 2.3–3.0× `mpn_tdiv_qr` from 1024 limbs (2.9–3.6× `Nat`), worst near
  4096 where the divide-and-conquer division hands over. GMP's division is about 2.1 of its own
  products.
- [ ] **Quotient-only division with an approximate quotient** (GMP's `mpn_div_q` with
  `divappr`): `/` computes, through the low halves of Burnikel–Ziegler's products and Algorithm
  D's last steps, a remainder it throws away. A quotient off by at most one and then checked needs
  high-half products (`mulhi` variants of the base case, Karatsuba and Toom-3) and a proof of the
  error bound: a big project. On 32-bit limbs at 1024 limbs, Comba is about 50% of the time and
  `subMul1` 25%, so faster products help it most. Ruled out on 32-bit limbs: a carry chain under
  three operations in `subMul1` (LLVM reassociates it). Schoolbook division takes two quotient
  limbs per pass since `4143568`, on both widths.
- [ ] **The cost of small divisions**: both widths normalize by shifts in `main`'s
  `Schoolbook.workS`, without copying a normalized divisor (`adfb500`), `/` copies out the quotient
  alone and `%` keeps the remainder in the array of the division (`db395d1`), and `%` by a word
  writes no quotient (`6d99d39`). On 64-bit limbs `MPN.Nat`'s `/` is 1.3–1.7× `Nat` from 2 to 8
  limbs and `%` 1.1–1.6×; what is left of the fixed cost is the array of the division, the shifted
  divisor and the result, and on 64-bit limbs the slice structures of `Num.divModBase`.
- [ ] **Toom-3's evaluations and interpolation in fused passes**, as Toom-4's already are
  (`MPN.Toom.Kernels`): each operand takes ten passes for its three values and the interpolation
  fourteen, each with its own array. A one-pass prototype of the evaluations was 2.7× faster than
  the three passes, about 2% of a product of 1024 to 4096 limbs on 32-bit limbs; the
  interpolation should give about as much, and Toom-3 by 2, Toom-4 by 2 and the Toom-3 square share
  the pieces.
- [ ] **A shorter dependency chain in division by a limb**, for CPUs with slow division (GMP's
  `mpn_div_qr_1n_pi1`, which keeps a partly reduced two-limb remainder and takes the quotient off
  the chain): the loop is bound by the latency of one step, about 14–15 cycles on Zen 3, and a
  precomputed reciprocal alone does not shorten it (3% slower on Zen 3, whose divider is fast).
- [ ] **Small sizes accepted for sharing**: `MPN.W64.sqrtRem` on arrays is 11.5% slower at 4
  limbs, from its conversions through `GNat` (`Bridge.sqrtRem`), and `MPN.W32.ofNat` 2–10% from the
  shared writer of a `Nat` (`WordArray.ofNatW`), against the old two limbs per word of 32-bit
  limbs. 32-bit `add` is 6–10% slower at 4 to 32 limbs on the shared `addW` (`478b578`), about
  3 ns: two folds and their setup, where the old loop copied `a` with a `memcpy` and added `b` in
  place with one fold.

## Algorithms

- [ ] **The FFT, next**: the pointwise products of residues by the FFT itself at very large sizes
  (GMP's recursive `mpn_mul_fft`), a fused butterfly (one pass for `a ± 2ˢ b`), and `fftK` tuned
  per machine.
- [ ] **Toom-8½, Toom-6 by 5 and the like**: the generators (`scripts/toom_interp.py`,
  `scripts/toom_methods.py`) handle any degree, and `newton_schedule` keeps the multipliers below
  the degree. Unbalanced Toom-6 and Toom-8 shapes (beyond six fifths, eight sevenths) still go to
  Toom-4 by 3; on 1:2 shapes Toom-4 by 2 and Toom-3 by 2 tie (±1%) from 1024 to 3072 limbs on
  64-bit limbs, so Toom-6 by 3 looks doubtful. The Toom-8 square loses on 32-bit limbs (its
  default is never there).

## Sharing

- [ ] **What each width keeps**: its `Arch/` kernels, its `Nat` instance (`natLimbs32`,
  `natLimbs64`) and gcd instance, and its decimal chunks. The division by several limbs,
  normalization and dispatch included, is shared since `985e2ce` (`MPN.Div.Driver`); each width
  keeps its divisions by one limb (and two on 32-bit limbs) and the glue to them. `NatOps` on
  arrays is shared since `a84e2ff` (`WordArray.opsA`), on both widths since `4e5e269`.

## Tuning

- [ ] **Defaults for more machines**: the size crossovers of both widths were measured on one
  Zen 3; the choices of algorithm follow GMP's on modern platforms (`div1Recip`, `div1Unnorm`,
  `div32Recip`, `sqrtZimmermann`, `sqrtBase`). Earlier runs on an Apple M2 and GitHub's EPYC 7763
  and Xeon 6973P-C agreed on the unbalanced Toom methods but not on Karatsuba, division by blocks
  and squaring, which would need defaults per architecture (`mpn_config%` choosing by the build
  target); the history is in `MPN32/BENCH.md`. Tuning across machines comes last, once the
  algorithms are in.
- [ ] **The tuners measure one step of a method at a time**, which can disagree with the whole
  dispatcher: on 32-bit limbs `tune32` (2026-11-01) put `mulToom6` at 1024 below `mulToom4` at
  1152, and its whole set was within ±2% of the defaults end to end, so the defaults stayed. Check
  a tuned set end to end (`lake build -R -K …`, then the bench with `--no-nat`) before adopting it.

## Proof engineering

- [ ] **The slice coercion `a ↦ a.toSlice 0 a.size`** on 32-bit limbs: `simp` and `split` rewrite
  inside it before `toNat_toSlice` can fire, so proofs rewrite with `toNat_toSlice` first or prove
  one equation per branch. A simp lemma for `toNat (a.toSlice 0 n)` with `a.size ≤ n` would remove
  most of these.
- [ ] **Report to Lean**:
  - a private `implemented_by` target attached with a separate `attribute` command is not visible
    to other modules (worked around in lean4-scalar-arrays#14 by making the impls public);
  - the equation lemmas of a recursive definition whose body has an `if` on large `UInt64` literals
    make the kernel recurse too deeply (worked around by moving the step out of the recursion);
  - the kernel overflows its recursion depth checking `rfl` between a definition and its
    unfolding when an argument contains `x * 4294967296` with `x : UInt64` and the body compares it
    with a literal, where `<<< 32` is fine;
  - the compiler replaces a literal `true` with a `decide` known to be `true` in that branch, such
    as the condition of an enclosing `if h : … then`, which put a loop-invariant comparison in a
    carry chain;
  - a join point whose branches return a word boxes it, an allocation per step in a loop
    (`ltWin`'s limb on 32-bit limbs, the pairs of `div32Step`).
