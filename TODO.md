# TODO

The library is verified end to end: every public operation is proved correct against `Nat`, with
no `sorry` and only the standard axioms. What is left is speed, more operations, and an API.
Items are roughly in order of value within each section.

## Performance

Time now goes mostly into the schoolbook row loop (`addMul1`, about 0.65 ns per 32-bit limb
product); callgrind shows that allocations are a few percent of a product from 64 limbs up.

- [ ] **Two rows per pass** (GMP's `mpn_addmul_2`): multiply by two limbs at once, with the two
  carries in a `UInt64` accumulator of `foldInPlaceThen`. It halves the loads and stores of the
  destination and the calls per product, and it is how GMP's schoolbook beats a plain
  `addmul_1` loop.
- [ ] **What is left of the Karatsuba and Toom-3 allocations:** about 100 small objects and arrays
  per 256-limb product (slices, `replicate`, and the `++` in `karatsubaCombine`, which copies),
  a few percent; thresholds are 72 and 488 limbs, against about 30 and 100 for 64-bit GMP. The
  arrays are needed results; the `++` copies are about `2 n` limbs per node. A verified
  `mulInto r off a b` with one scratch area, in GMP's style, would remove them.
- [ ] **`divRem1` by a precomputed reciprocal** (GMP's `udiv_qrnnd_preinv`, Möller–Granlund):
  the hardware division is all of its time, about 3.3 ns per limb, 2× behind `Nat` at large
  sizes; a `USize` twin of the loop was tried and changes nothing. It is behind division by one
  limb, the un-normalization of every remainder, Toom-3's exact divisions and, later,
  `toString`.
- [ ] **`toNat` (the conversion to `Nat`)** is `ofLimbs`, which builds the literal `2³²` from a
  string at each limb and multiplies a growing `Nat` each time; a compiled twin (by halves, or
  from GMP's limbs once `Nat` is replaced) would make conversions much cheaper.
- [ ] **`push` is still an out-of-line call** in lean4-scalar-arrays; inlining it upstream like
  `uset` would help every loop that builds an array.

Done this round: word carries and hoisted slice fields in the folds; in-place Algorithm D with
`subMul1` (34 allocations per 32 ÷ 16-limb division instead of 270); `foldInPlaceThen`
(lean4-scalar-arrays#22) for `addMul1Set`, `addInto` and `subInto`, which allocate no result
pairs; `toom3Sqr`; guards of the compiled loops against a literal below `2³²` instead of
`USize.size` (11–15% on small products); the schoolbook square in one final pass
(`sqrAddDiag`) without row slices, faster than multiplying from 16 limbs; Knuth's correction of
the quotient estimate, which removed the add-backs (42% of quotient limbs at 256 limbs).

Tried without gain: passing `subMul1`'s borrow to the end of the step through `foldInPlaceThen`
(the step still returns a pair, and the compiler already reused the memory of `subMul1`'s);
a `USize` twin of `divRem1` (the hardware division hides the loop). Twins of `ltLoop` and
`topSizeLoop` would not show: `lt` runs once or twice per block of the division, and `topSize`
usually stops at the first limb.

## Algorithms

- [x] **Divide-and-conquer division** (`Div.DC`, Burnikel–Ziegler): blocks of half the divisor,
  digits from recursive divisions by its top half and the low-half product, from 176 limbs.
  Division is now about 5× behind `Nat` from 128 limbs up, instead of a gap growing with size
  (17× at 4096 limbs).
- [ ] **Unbalanced Toom** (`toom32`, `toom42`) instead of halving the longer operand.
- [ ] **Toom-4, Toom-6½, Toom-8½**, then FFT multiplication for very large numbers.
- [ ] **The rest of `Nat`:**
  - [ ] shifts by bits (`<<<`, `>>>`);
  - [ ] bitwise `&&&`, `|||`, `^^^`;
  - [ ] `log2`;
  - [ ] `pow`, by repeated squaring with `sqr`;
  - [x] `gcd` and `lcm` (`BigNat`): Lehmer's algorithm with single-word cofactors, checked by
    their determinant, and Euclid on words; faster than `Nat` on words, 13–18× behind GMP from 3
    limbs. A fused limb primitive applying the cofactor matrix in one pass (GMP's
    `mpn_hgcd_mul_matrix1_vector`) would remove most of the allocations of a step, and
    double-word leading digits (`hgcd2`) would double the progress per step.
  - [ ] integer square root;
  - [ ] `toString`/`ofString`, like GMP's `mpn_get_str`/`mpn_set_str`, by dividing by `10⁹`
    with `divRem1`.

## API

- [x] **A `Nat`-like type:** `BigNat`, a word below `2⁶⁴` and trimmed limbs above, with the
  instances, truncated subtraction and the bijection with `Nat`. About 15 ns per operation on
  words, against 9–10 ns for `Nat`, whose small values need no allocation.
- [ ] **The fixed cost of small divisions:** 400 ns to 1 µs for divisors of 2 to 16 limbs, against
  50–160 ns for `Nat`: normalization, several arrays, and the remainder un-normalized even when
  only the quotient is wanted. A quotient-only path and fewer arrays would help `BigNat.div`.
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
  `lake exe bench --no-nat mul 256` runs one case alone, for a profiler.
- [ ] **A raw GMP baseline.** The `Nat` column is Lean's wrapper around GMP, which copies both
  the operand and the result and allocates twice per operation, so below about 64 limbs it
  measures mostly that overhead (we beat it there). Calling `mpn_*` directly needs C, so it
  belongs on the `64bit` branch.
- [ ] **Executables initialize all of Lean.** `Config`'s `bignum_config%` elaborator imports
  `Lean`, so every program that imports `Bignum` spends about 25 ms at startup initializing it.
  Moving the elaborator to its own module would keep it out of programs.
- [ ] **CI** building and testing every push, and running `tune` occasionally as a rough check
  of the default thresholds (shared runners are noisy).
- [ ] **Decide what to do with the `64bit` branch** (C and GMP experiments, benchmarks), which is
  kept off `main` on purpose.

Profiling notes: `perf record` (without `-g`, which misattributes in these binaries) for where
time goes; `valgrind --tool=callgrind --toggle-collect=<C symbol>` for exact allocation counts
per operation; `gdb` with a breakpoint on `lean_copy_sarray` for unexpected array copies; the
generated C in `.lake/build/ir` to check that a `@[csimp]` twin is really called. `lake build`
does not rebuild `bench` and `tune`.
