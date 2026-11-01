/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean
public import MPN.Toom.Ops
public meta import MPN.Toom.Ops
public meta import MPN.ConfigOptions

/-!
# Configuration

`Config` collects the size thresholds, in limbs, at which the arithmetic switches algorithms. The
algorithms take a `Config` as a parameter, and the library's own `MPN.config` is built by
`mpn_config%` from the options `mpn.w32.f`, one for each field `f`, set when the library is
compiled (`MPN.ConfigOptions`). The package's `lakefile.lean` sets them from the options of a
project's `require`, keyed by the fields of `Config` with the prefix `w32_`, for example
`options = { w32_mulKaratsuba = "48" }` (see the README). Options that are not
set keep the defaults of `Config`. Each threshold carries the proof of the condition its algorithm
needs, so an invalid value is rejected when the library is compiled.

The defaults were measured with `lake exe tune` on an AMD Ryzen 5 5600X, except where GMP chooses
an algorithm on modern platforms whatever the size: the reciprocal steps of division and
Zimmermann's square root, which the defaults take always, like GMP. Running `lake exe tune` on the
target machine prints the thresholds for that machine and the options that set them.
-/

namespace MPN.W32

/-- The size thresholds, in limbs, at which the arithmetic switches algorithms. -/
public structure Config extends Toom.Config where
  mulKaratsuba := 112
  four_le_mulKaratsuba := by decide
  mulToom3 := 640
  twelve_le_mulToom3 := by decide
  mulToom32 := 192
  twelve_le_mulToom32 := by decide
  mulToom42 := 304
  twelve_le_mulToom42 := by decide
  mulToom4 := 608
  thirtytwo_le_mulToom4 := by decide
  mulToom43 := 272
  thirtytwo_le_mulToom43 := by decide
  mulToom6 := 1792
  thirtytwo_le_mulToom6 := by decide
  sqrKaratsuba := 160
  four_le_sqrKaratsuba := by decide
  sqrToom3 := 944
  twelve_le_sqrToom3 := by decide
  sqrToom4 := 832
  thirtytwo_le_sqrToom4 := by decide
  sqrToom6 := 2496
  thirtytwo_le_sqrToom6 := by decide
  /--
  The size of the shorter operand from which multiplication uses the FFT when the longer one is
  less than twice as long.
  -/
  mulFFT : Nat := 14336
  /--
  The size of the shorter operand from which multiplication splits a longer operand that is at
  least twice as long, instead of using schoolbook. It only matters above `mulKaratsuba`, since the
  split pays off through Karatsuba on its pieces.
  -/
  mulUnbalanced : Nat := 204
  /--
  The size of both operands together from which the schoolbook product adds rows into wide
  accumulators instead of Comba's method.
  -/
  mulRows : Nat := 16
  /-- The size of the shorter operand from which Comba's method adds whole products in its
  columns. -/
  mulCombaW : Nat := 32
  /-- The size from which the schoolbook square adds rows into wide accumulators instead of Comba's
  method. -/
  sqrRows : Nat := 16
  /-- The size from which squaring uses the schoolbook square instead of multiplying. -/
  sqrBasecase : Nat := 2
  /-- The size from which squaring uses the FFT. -/
  sqrFFT : Nat := 12288
  /-- The size of the divisor from which division computes its quotient in blocks of half the
  divisor, with recursive divisions, instead of one limb at a time. -/
  divDC : Nat := 176
  /-- Blocks of half the divisor need at least `4` limbs, so that the recursion has two. -/
  four_le_divDC : 4 ≤ divDC := by decide
  /-- The size of the divisor from which division uses Barrett's division with Newton's
  reciprocal instead of blocks. -/
  divMu : Nat := 1000000
  /-- The size from which division by a normalized limb takes Möller and Granlund's steps with a
  precomputed reciprocal instead of the hardware divider: always, like GMP's `mpn_divrem_1`. -/
  div1Recip : Nat := 0
  /-- The size of a normalized divisor from which schoolbook division estimates the quotient limbs
  by GMP's 3-by-2 steps with a precomputed reciprocal instead of the hardware divider: always, like
  GMP's `mpn_sbpi1_div_qr`. -/
  div32Recip : Nat := 0
  /-- The size from which division by an unnormalized limb takes the steps with a precomputed
  reciprocal of the divisor normalized by a shift, with the dividend shifted, instead of the
  hardware divider: always, like GMP's `mpn_divrem_1`. -/
  div1Unnorm : Nat := 0
  /-- The size of the root, in limbs, from which the square root uses Zimmermann's recursion
  instead of Newton's iteration: always, like GMP's `mpn_sqrtrem`. -/
  sqrtZimmermann : Nat := 1
  /-- The size of the root, in limbs, at or below which Zimmermann's recursion finishes by Newton's
  iteration: one limb, like GMP's `mpn_sqrtrem`. -/
  sqrtBase : Nat := 1
  /-- The size of the smaller number from which the greatest common divisor uses half-gcd. -/
  gcdHalf : Nat := 1536
  /-- The size from which decimal strings are written by divide and conquer. -/
  strDC : Nat := 80
  /-- The size of the result, in limbs, from which decimal strings are read by divide and
  conquer. -/
  parseDC : Nat := 1024
  deriving Repr

/-- The thresholds of the Karatsuba and Toom methods of `MPN.Toom`, a projection. -/
@[inline] public abbrev Config.toom (cfg : Config) : Toom.Config := cfg.toConfig

-- The options `mpn.w32.f`, one for each threshold `f` of `Config`, with its default.
declare_config_options Config mpn.w32

end MPN.W32
