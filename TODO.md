# TODO

The library is verified end to end: every public operation is proved correct against `Nat`, with
no `sorry` and only the standard axioms. What is left is speed, more operations, and an API.
Items are roughly in order of value within each section.

## Performance

Time now goes mostly into the schoolbook product, by columns since `Mul.Comba` (about 0.5 ns per
32-bit limb product, vectorized by the C compiler with SSE2): 72% of a product even at 4096 limbs,
with `perf`, after the combinations went to one pass. The rest is a few percent each (Karatsuba's
`addDiffInto`, Toom-3's passes, allocation), which is why the attempts below to move Toom-3 or
Karatsuba in place gained at most 1%. With 32-bit limbs, a product needs 4× as many limb products
as GMP's, which is most of the gap above 64 limbs; `march = "native"` (see the README) makes Comba
7–13% faster with AVX2. What is left for products is algorithmic: unbalanced Toom and Toom-4
below.

- [ ] **Toom-3's interpolation in place** (low value): it makes a fresh array for each of its
  eight `subVal`s and three `mulRow`s, where GMP's `toom_interpolate_5pts` works in place; the
  assembly half, prototyped with copies, gained under 1%, so expect about as much.
- [ ] **A shorter dependency chain in `divRem1`** (for CPUs with slow division; GMP's
  `mpn_div_qr_1n_pi1`): the loop is bound by the latency of one step, about 15 cycles (3.3 ns per
  limb on Zen 3), since each step needs the previous remainder; the rest of the loop (1.4 ns per
  limb) runs in parallel. A precomputed reciprocal (Möller–Granlund's `udiv_qrnnd_preinv`) was
  prototyped and is 3% *slower* there, because Zen 3's divider is fast; it would pay on CPUs with
  slow 64-bit division (Intel before Ice Lake). `div_qr_1n_pi1` keeps a partly reduced two-limb
  remainder and takes the quotient off the chain, about one multiply-add per step. `divRem1` is
  behind division by one limb and `toString`.

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
ms and 2.2 → 0.24 ms, still about one operation on `Nat`, some 40 ns, per two limbs).

Tried without gain: Toom-3's assembly by copies, `c₀` and `c₄` written into place and three
`addInto`s instead of five on a zeroed array (within 1% from 512 to 4096 limbs, where Comba is
72% of a product); Karatsuba into one array, products at an offset with the scratch above (GMP's
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
  digits from recursive divisions by its top half and the low-half product, from 176 limbs.
  Division is now about 5× behind `Nat` from 128 limbs up, instead of a gap growing with size
  (17× at 4096 limbs).
- [x] **Toom-3 by 2** (`toom32`, GMP's `mpn_toom32_mul`): for a longer operand between four
  thirds and twice as long as the shorter, from 160 limbs, it splits them in three and two at a
  third of the longer, where `toom3` split both at a third of the shorter and left a long top part
  in its five products; four products, at the points `0, 1, 2, ∞`. Shapes of 3:2 and 3:1 (which
  halves into 3:2) are 27–39% faster from 512 limbs (`1536 × 1024`: 406 → 247 µs, 8.2 → 5.0×
  GMP). The tuner finds 120, but direct timings are slower until about 150.
- [ ] **Toom-4 by 2 and Toom-4 by 3** (`toom42`, `toom43`) for ratios near 2 and 4:3, where
  halving the longer operand or `toom32` leave pieces of unequal sizes.
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
    their determinant, and Euclid on words. Each new number is a difference of two multiples,
    computed in one pass with a biased carry (`mulSubMul`), and the cofactors stay below `2³¹`, so
    that their determinant is checked on `Nat` without GMP (`lehmerStep`); the word steps divide
    once per quotient and stop by Jebelean's condition (`lehmerSteps`). Faster than `Nat` on
    words, 3.4–6.8× behind GMP from 3 limbs (from 13–20×). This is already GMP's `hgcd2` in our
    limbs (two-limb leading words, one-limb cofactors); the next size up, 124-bit words and 62-bit
    cofactors, would need Euclid in emulated 128-bit arithmetic, already 11–21% of the time in
    64-bit, for passes that do twice the products for half the steps, so it is not worth it.
    Left: both new numbers in one pass (fewer loads and objects, maybe 5–10% up to 64 limbs), and
    subquadratic `hgcd`, GMP's advantage from a few hundred limbs, where the passes are half the
    time.
  - [x] integer square root: Newton's iteration at growing precision, from the root of the top
    half (`sqrt (n / 4ᵏ)` for `k` a quarter of the bits), which starts within `2ᵏ` above the root;
    one Newton step, which is at least the root by AM-GM, then steps down while `x² > n` with one
    square (`sqrtFix`), where the iteration took a second division to stop. Faster than `Nat` up
    to 4 limbs, 1.05–2.25× behind above.
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
- [ ] **The fixed cost of small divisions:** `BigNat.div` takes 86 ns for 4 limbs by 2, 245 ns for 8
  by 4 and 555 ns for 32 by 16, against 47, 95 and 154 ns for `Nat`. Done: up to four limbs by a
  word of two, the division runs on words alone, with three `div2Step`s after the shift
  (`divRem128`; 159 → 86 ns), and `/` by a word uses `div2`, which allocates no remainder; the
  normalized dividend is divided in place when its top limb is below the divisor's
  (`divRemBasecaseTop`), which saves its copy and one step of Algorithm D (12–22% from 3 to 16
  limbs); a `BigNat` divided by a word goes to `divRem1` or `divRem2` without an array for the word
  (`divRemWord`, 2 limbs 192 → 170 ns; `%` by a word returns the word); Algorithm D works in one
  array, with each quotient limb in the freed top limb of its window, and its compiled step
  allocates no pair (`divLoopIn`, `divStepInFast`; 11–19% from 3 to 64 limbs). Left: above four
  limbs, a divisor of two limbs still goes through `divRem2`'s shifted copy of the dividend and its
  slices, which normalizing on the fly in its loop would remove.
- [x] **Words near `2⁶⁴` in `BigNat`:** a sum or product of two words that overflows went
  through `limbsOfWord` and the array functions (about 95 ns). `mulWide` computes the product from
  the four products of halves, and `wideOf` makes the three or four limbs directly: `badd` at 2
  limbs 95 → 34 ns (0.42× `Nat`), `bmul` 92 → 50 ns (0.62×).
- [x] **Per-dependency configuration.** Lake builds a dependency with that dependency's own
  settings; the package's `lakefile.lean` now reads the options of a project's `require` (or
  `-K`): the thresholds, keyed by the fields of `Config`, and `march`, which compiles the C code
  with `-march=<value>` (`native`: 7–13% faster products with AVX2). Keys have no dots, since TOML
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
does not rebuild `bench` and `tune`. The benchmark's trials (2 ms) are too short to profile: a loop
in a scratch Lake project that requires this one by `path` reuses its build. `perf record` in front
of `taskset` samples only the startup, so pin the whole command or not at all.
