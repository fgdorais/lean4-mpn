# TODO

Both libraries are verified end to end: every public operation is proved correct against `Nat`,
with no `sorry` and only the standard axioms. What is left is speed, sharing, tuning, more
operations, and tooling. The timings and the history of the changes that affected them are in
[MPN32/BENCH.md](MPN32/BENCH.md) and [MPN64/BENCH.md](MPN64/BENCH.md); what was done before the
two widths moved into one package is in the history of `MPN32/TODO.md`.

## Performance

- [ ] **Division on 64-bit limbs** is the only operation more than 4× behind GMP: `Num.div` runs
  at 4.2–4.6× from 5632 to 10240 limbs and `Num.divMod` at about 5×, against products at
  1.5–3.2×. Its costs per `n`-limb product `M`: the reciprocal about 2.2 `M`, a Barrett step about
  2 `M`; GMP's division is about 2.1 of its own products, which are 3× faster.
- [ ] **Quotient-only division with an approximate quotient** (GMP's `mpn_div_q` with
  `divappr`): `/` computes, through the low halves of Burnikel–Ziegler's products and Algorithm
  D's last steps, a remainder it throws away. A quotient off by at most one and then checked needs
  high-half products (`mulhi` variants of the base case, Karatsuba and Toom-3) and a proof of the
  error bound: a big project. On 32-bit limbs at 1024 limbs, Comba is about 50% of the time and
  `subMul1` 25%, so faster products help it most. Ruled out on 32-bit limbs: a carry chain under
  three operations in `subMul1` (LLVM reassociates it). Schoolbook division takes two quotient
  limbs per pass since `4143568`, on both widths.
- [ ] **`Num.divMod` on 64-bit limbs by Barrett is bimodal**: from `divMu` (8192 limbs) on, `2 n / n`
  takes either about 1.13 or about 1.36 times the quotient alone, by size (13.2 ms at 8192, 8224 and
  8256 limbs, 11.7 ms at 8200, 8288 and 8320). Both kinds do the same work: the same Barrett blocks,
  FFT parameters and numbers of FFT products, wrapped products, pointwise products and butterflies
  (counted with breakpoints), and glibc's allocation settings don't move it, so it is a memory or
  cache effect in the FFT, not the division.
- [ ] **The cost of small divisions**: since `adfb500` both widths normalize by shifts in `main`'s
  `Schoolbook.divRemN`, without copying a normalized divisor, which took 25–50% off `2 n / n` from
  2 to 8 limbs. On 64-bit limbs `/` is now 1.3–1.8 times `Nat` from 2 to 8 limbs and 2.2–2.3
  times at 16 and 32, where the loop, not its fixed cost, is the gap; what is left of the fixed
  cost is three or four new arrays per division, and on 64-bit limbs the slice structures of
  `Num.divModBase`.
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
- [ ] **Toom-8½, Toom-6 by 5 and the like**: Toom-8 gained 7–11% over Toom-4 in a one-level
  prototype at 6144–16384 limbs on 32-bit limbs, about as much as Toom-6; the generator
  (`scripts/toom_interp.py`, `scripts/toom_methods.py`) handles any degree. Unbalanced Toom-6
  shapes (beyond six fifths) still go to Toom-4 by 3.

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

## Tooling

- [ ] **A raw GMP baseline**: the `Nat` column is Lean's wrapper around GMP, which copies the
  operands and the result and allocates twice per operation, so below about 64 limbs it measures
  mostly that overhead. Calling `mpn_*` directly needs C in the bench executables (never in the
  libraries, which call no GMP).

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
