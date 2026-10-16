# TODO

The library is verified end to end: every public operation is proved correct against `Nat`, with
no `sorry` and only the standard axioms. What is left is speed, more operations, and an API.
Items are roughly in order of value within each section.

## Performance

Time now goes mostly into the schoolbook product, by columns since `Mul.Comba` (about 0.5 ns per
32-bit limb product, vectorized by the C compiler with SSE2); callgrind shows that allocations are a
few percent of a product from 64 limbs up. With 32-bit limbs, a product needs 4× as many limb
products as GMP's, which is most of the gap above 64 limbs.

- [ ] **A shorter dependency chain in `divRem1`** (GMP's `mpn_div_qr_1n_pi1`): the loop is
  bound by the latency of one step, about 15 cycles (3.3 ns per limb on Zen 3), since each step
  needs the previous remainder; the rest of the loop (1.4 ns per limb) runs in parallel. A
  precomputed reciprocal (Möller–Granlund's `udiv_qrnnd_preinv`) was prototyped and is 3% *slower*
  there, because Zen 3's divider is fast; it would pay on CPUs with slow 64-bit division (Intel
  before Ice Lake). `div_qr_1n_pi1` keeps a partly reduced two-limb remainder and takes the
  quotient off the chain, about one multiply-add per step. `divRem1` is behind division by one
  limb and `toString`.
- [x] **The conversions to and from `Nat`** went one limb at a time, multiplying or dividing a
  growing `Nat` at each limb. Their compiled twins (`toNatFast`, `ofNatFast`) split the limbs in
  halves and join or split them with shifts; `ofNat` takes 64 bits at a time below 64 limbs, with
  `toUInt64`. From 4 limbs up, `toNat` is 2.4–16× faster (4096 limbs: 6.1 → 0.39 ms) and `ofNat`
  1.3–9× (4096: 2.2 → 0.24 ms). They are still 2–450× behind a pass over the value, since each
  operation on `Nat` costs about 40 ns; reading GMP's limbs directly would need C.

Done this round: word carries and hoisted slice fields in the folds; in-place Algorithm D with
`subMul1` (34 allocations per 32 ÷ 16-limb division instead of 270); `foldInPlaceThen`
(lean4-scalar-arrays#22) for `addMul1Set`, `addInto` and `subInto`, which allocate no result
pairs; `toom3Sqr`; guards of the compiled loops against a literal below `2³²` instead of
`USize.size` (11–15% on small products); the schoolbook square in one final pass
(`sqrAddDiag`) without row slices, faster than multiplying from 16 limbs; Knuth's correction of
the quotient estimate, which removed the add-backs (42% of quotient limbs at 256 limbs); the
remainder of a normalized division shifted back instead of divided by a limb; `trim` without a
closure (`popWhile`'s predicate was called through `lean_apply_1`); a quotient-only `div`;
division by two limbs in one pass (`divRem2`); the schoolbook product by columns (Comba, 14–24%
from 8 limbs up) and the square (22–25% from 64 limbs up); Karatsuba's middle term added in one
pass over `z₁` with `addDiffInto`, which keeps a carry between `-2` and `1` as a word plus 2, where
two subtractions and an addition took three passes (the combination 38% faster, products 2–5%
faster from 256 limbs up); Toom-3's exact divisions without the hardware divider, by 2 with
`shrLimbs` and by 3 with the inverse of 3 modulo `2³²` (`divExact3`, 2.2× faster than `divRem1`;
products 3–8% and squares up to 10% faster from 576 limbs up, Toom-3 from 480 and 720 limbs
instead of 576 and 892); both shifts in one
pass with the slice folds of lean4-scalar-arrays#27 and #28; `push` inline upstream
(lean4-scalar-arrays#24).

Tried without gain: Karatsuba into one array, products at an offset with the scratch above (GMP's
style), prototyped without proofs on an offset copy of Comba's kernel: within ±1% of the allocating
version from 128 to 448 limbs, with the combination in two passes or in one fused pass (after saving
the top half of `z₀`, which it overwrites before reading). `perf` attributes 5–11% of a product to
allocation and copies, but mimalloc's small allocations are cheap and an array of products still
needs its evaluation sums as separate arrays (a slice of the scratch array would be shared with the
array being written, and copied). In Comba's column loop, unrolling by two (no change), counting the
wraps of one 64-bit sum instead of splitting the halves (faster below 32 limbs, slower above), and
reading `b` reversed so that both operands go forward (the copy costs more than it saves); `divRem1`
on `foldrInPlaceThen` over a copy (the loop is bound by the division, and building the slice costs
10–25 ns per call, 5–12% slower below 16 limbs), which also rules out slices for the per-row folds
(`addMul1Set`, `addInto`, `subInto`), called once per row; passing `subMul1`'s borrow to the end of
the step through `foldInPlaceThen` (the step still returns a pair, and the compiler already reused
the memory of `subMul1`'s); a `USize` twin of `divRem1` (the hardware division hides the loop).
Twins of `ltLoop` and `topSizeLoop` would not show: `lt` runs once or twice per block of the
division, and `topSize` usually stops at the first limb.

## Algorithms

- [x] **Divide-and-conquer division** (`Div.DC`, Burnikel–Ziegler): blocks of half the divisor,
  digits from recursive divisions by its top half and the low-half product, from 128 limbs.
  Division is now about 5× behind `Nat` from 128 limbs up, instead of a gap growing with size
  (17× at 4096 limbs).
- [ ] **Unbalanced Toom** (`toom32`, `toom42`) instead of halving the longer operand.
- [ ] **Toom-4, Toom-6½, Toom-8½**, then FFT multiplication for very large numbers.
- [ ] **The rest of `Nat`:**
  - [x] shifts by bits (`<<<`, `>>>`, `Bits`): one pass each, in place over a copy with
    `foldrInPlaceThen` and `foldlInPlaceThen`, even with `Nat` from 1 to 1024 limbs. The left
    shift computes each carry from its limb alone, so the loop has no dependency chain (36%
    faster than carrying through the sum);
  - [x] bitwise `&&&`, `|||`, `^^^` (limbwise with `ofFn`, then trimmed);
  - [x] `log2`;
  - [x] `pow`, by repeated squaring with `sqr`;
  - [x] `gcd` and `lcm` (`BigNat`): Lehmer's algorithm with single-word cofactors, checked by
    their determinant, and Euclid on words; faster than `Nat` on words, 10–19× behind GMP from 4
    limbs. A fused limb primitive applying the cofactor matrix in one pass (GMP's
    `mpn_hgcd_mul_matrix1_vector`) would remove most of the allocations of a step, and
    double-word leading digits (`hgcd2`) would double the progress per step.
  - [x] integer square root: Newton's iteration at growing precision, from the root of the top
    half (`sqrt (n / 4ᵏ)` for `k` a quarter of the bits), which starts within `2ᵏ` above the root;
    2–4× behind `Nat` (3–12× from a power of two). Stopping one division earlier, with a square
    to check the last step, would save about a third.
  - [x] `toString`/`ofString?` (`Decimal`), like GMP's `mpn_get_str`/`mpn_set_str` below their
    thresholds: chunks of nine digits, by `divRem1` by `10⁹` one way and a fold over the
    characters the other. Equal to `Nat.repr` and `String.toNat?`, and 10–20× faster than
    `Nat`'s, which works digit by digit, from 4 limbs up; words go to the runtime's `USize.repr`.
    Both are quadratic: GMP's subquadratic versions (by powers `10^(9·2ᵏ)`) would be next.
    Reading a short number costs 350 ns against 140 ns, mostly in `String.isNat` and the string
    iterator.

## API

- [x] **A `Nat`-like type:** `BigNat`, a word below `2⁶⁴` and trimmed limbs above, with the
  instances, truncated subtraction and the bijection with `Nat`. About 15 ns per operation on
  words, against 9–10 ns for `Nat`, whose small values need no allocation.
- [ ] **The fixed cost of small divisions:** `BigNat.div` takes 206 ns for a divisor of 2 limbs
  (`divRem2`, one pass like GMP's `mpn_divrem_2`; 428 ns before), 340 ns for 4 limbs and 770 ns
  for 16, against 47, 95 and 154 ns for `Nat`. Above 2 limbs, Algorithm D's steps are half the
  time, each paying the fixed cost of `subMul1` and its result pair; the copy of the normalized
  dividend into `divRemBasecase`'s buffer is another 7%, and could be avoided with a run-time check
  of its top limb against the divisor's.
- [ ] **Words near `2⁶⁴` in `BigNat`:** a sum or product that overflows goes through
  `limbsOfWord` and the array functions (about 100 ns); a direct `64 × 64 → 128` product would
  help `*`.
- [ ] **Per-dependency thresholds.** Lake builds a dependency with that dependency's own
  options, so a downstream project can't tune this library's `Config`. The usual mechanism is
  `require … with …` configuration, which needs a `lakefile.lean`.

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

- [x] **Benchmarks on `main`:** `lake exe bench` times each operation against `Nat`;
  `lake exe bench --no-nat mul 256` runs one case alone, for a profiler. Results are checked in
  O(1) on both sides (a hash of a `BigNat` result once cost a pass over its limbs).
- [ ] **A raw GMP baseline.** The `Nat` column is Lean's wrapper around GMP, which copies both
  the operand and the result and allocates twice per operation, so below about 64 limbs it
  measures mostly that overhead (we beat it there). Calling `mpn_*` directly needs C, so it
  belongs on the `64bit` branch.
- [x] **Executables initialize all of Lean.** `Config` imports `Lean` (as `meta`) for its
  `bignum_config%` elaborator. A main file that is not a `module` calls the meta initializers of
  everything it imports, so it links and initializes all of Lean: 124 MB and about 20 ms at
  startup. A main file that is a `module` calls only the runtime initializers, which skip `meta`
  imports: `bench` and `tune` are now modules, 3.9 MB each, and the README says so for programs.
- [ ] **CI** building and testing every push, and running `tune` occasionally as a rough check
  of the default thresholds (shared runners are noisy).
- [ ] **Decide what to do with the `64bit` branch** (C and GMP experiments, benchmarks), which is
  kept off `main` on purpose.

Profiling notes: `perf record` (without `-g`, which misattributes in these binaries) for where
time goes; `valgrind --tool=callgrind --toggle-collect=<C symbol>` for exact allocation counts
per operation; `gdb` with a breakpoint on `lean_copy_sarray` for unexpected array copies; the
generated C in `.lake/build/ir` to check that a `@[csimp]` twin is really called. `lake build`
does not rebuild `bench` and `tune`.
