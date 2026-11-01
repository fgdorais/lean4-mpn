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
`mpn_config%` from the options `mpn.w64.f`, one for each field `f`, set when the library is
compiled (`MPN.ConfigOptions`). The package's `lakefile.lean` sets them from the options of a
project's `require`, keyed by the fields of `Config` with the prefix `w64_`, for example
`options = { w64_mulKaratsuba = "48" }` (see the README). Options that are not
set keep the defaults of `Config`. Each threshold carries the proof of the condition its algorithm
needs, so an invalid value is rejected when the library is compiled.

The defaults were measured on an AMD Ryzen 5 5600X, except where GMP chooses an algorithm on
modern platforms whatever the size: the reciprocal steps of division and Zimmermann's square root,
which the defaults take always, like GMP. `lake exe tune` prints the thresholds for the machine it
runs on and the options that set them.
-/

namespace MPN.W64

/-- The size thresholds, in limbs, at which the arithmetic switches algorithms. -/
public structure Config extends Toom.Config where
  mulKaratsuba := 64
  four_le_mulKaratsuba := by decide
  mulToom3 := 384
  twelve_le_mulToom3 := by decide
  mulToom32 := 176
  twelve_le_mulToom32 := by decide
  mulToom42 := 88
  twelve_le_mulToom42 := by decide
  mulToom4 := 600
  thirtytwo_le_mulToom4 := by decide
  mulToom43 := 600
  thirtytwo_le_mulToom43 := by decide
  mulToom6 := 768
  thirtytwo_le_mulToom6 := by decide
  sqrKaratsuba := 96
  four_le_sqrKaratsuba := by decide
  sqrToom3 := 600
  twelve_le_sqrToom3 := by decide
  sqrToom4 := 1000
  thirtytwo_le_sqrToom4 := by decide
  sqrToom6 := 1152
  thirtytwo_le_sqrToom6 := by decide
  /-- The size of the larger operand from which multiplication uses the FFT. -/
  mulFFT : Nat := 4096
  /--
  The size of the larger operand from which multiplication uses the FFT when the operands differ
  by `3 : 2` or more, where the Toom methods are slower.
  -/
  mulFFTUnbal : Nat := 3072
  /--
  The size of the smaller operand below which multiplication does not use the FFT, whose cost
  follows the total size, where that of schoolbook grows with the smaller operand.
  -/
  mulFFTMin : Nat := 320
  /--
  The size of the smaller operand from which multiplication splits a larger operand that is at
  least twice as long into pieces of the size of the smaller one.
  -/
  mulUnbalanced : Nat := 96
  /-- The pieces need at least one limb. -/
  one_le_mulUnbalanced : 1 ≤ mulUnbalanced := by decide
  /--
  The size of the smaller operand from which multiplication no longer splits the larger operand
  when that one is in the range of the FFT, since one FFT on the whole product is faster.
  -/
  mulChunkMax : Nat := 1024
  /-- The size from which squaring uses the FFT. -/
  sqrFFT : Nat := 2816
  /--
  The size of the divisor from which division computes its quotient in blocks of half the
  divisor, with recursive divisions (Burnikel and Ziegler), instead of the schoolbook method.
  -/
  divDC : Nat := 512
  /--
  The size of the divisor from which division uses Barrett's method with Newton's reciprocal,
  inside divide and conquer (so from `divDC` on).
  -/
  divMu : Nat := 8192
  /--
  The size of the divisor from which the quotient alone (`Num.div`) uses Barrett's method with
  Newton's reciprocal, which then skips the remainder of the last block.
  -/
  divQMu : Nat := 5632
  /--
  The size from which division by a normalized limb takes Möller and Granlund's steps with a
  precomputed reciprocal instead of the hardware divider: always, like GMP's `mpn_divrem_1`.
  -/
  div1Recip : Nat := 0
  /--
  The size from which division by an unnormalized limb takes the steps with a precomputed
  reciprocal of the divisor normalized by a shift, with the dividend shifted, instead of the
  hardware divider: always, like GMP's `mpn_divrem_1`.
  -/
  div1Unnorm : Nat := 0
  /--
  The size of the divisor from which schoolbook division estimates the quotient limbs by GMP's
  3-by-2 step with a precomputed reciprocal instead of the hardware divider: always, like GMP's
  `mpn_sbpi1_div_qr`.
  -/
  div32Recip : Nat := 0
  /--
  The size of the root, in limbs, from which the square root uses Zimmermann's recursion instead
  of Newton's iteration: always, like GMP's `mpn_sqrtrem`.
  -/
  sqrtZimmermann : Nat := 1
  /--
  The size of the root, in limbs, at or below which Zimmermann's recursion finishes by Newton's
  iteration; roots of one limb are by `sqrt2`, which is where GMP's `mpn_sqrtrem` stops.
  -/
  sqrtBase : Nat := 1
  /-- The size of the smaller number from which the greatest common divisor uses half-gcd. -/
  gcdHalf : Nat := 1024
  /-- The size from which decimal strings are written by divide and conquer. -/
  strDC : Nat := 40
  /--
  The size of the result, in limbs, from which decimal strings are read by divide and conquer.
  -/
  parseDC : Nat := 512
  deriving Repr

/-- The thresholds of the Karatsuba and Toom methods of `MPN.Toom`, a projection. -/
@[inline] public abbrev Config.toom (cfg : Config) : Toom.Config := cfg.toConfig

-- The options `mpn.w64.f`, one for each threshold `f` of `Config`, with its default.
declare_config_options Config mpn.w64

end MPN.W64
