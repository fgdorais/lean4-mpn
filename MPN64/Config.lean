/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean
public import MPN.Toom.Ops
public import MPN.Dispatch
public import MPN.Dispatch.Div
public meta import MPN.Toom.Ops
public meta import MPN.Dispatch
public meta import MPN.Dispatch.Div
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
public structure Config extends Dispatch.MulConfig, Dispatch.DivConfig, Dispatch.SqrtConfig where
  mulKaratsuba := 56
  four_le_mulKaratsuba := by decide
  mulToom3 := 368
  twelve_le_mulToom3 := by decide
  mulToom32 := 192
  twelve_le_mulToom32 := by decide
  mulToom42 := 104
  twelve_le_mulToom42 := by decide
  mulToom4 := 512
  thirtytwo_le_mulToom4 := by decide
  mulToom43 := 592
  thirtytwo_le_mulToom43 := by decide
  mulToom6 := 768
  thirtytwo_le_mulToom6 := by decide
  sqrKaratsuba := 88
  four_le_sqrKaratsuba := by decide
  sqrToom3 := 544
  twelve_le_sqrToom3 := by decide
  sqrToom4 := 714
  thirtytwo_le_sqrToom4 := by decide
  sqrToom6 := 1039
  thirtytwo_le_sqrToom6 := by decide
  mulFFT := 6144
  mulFFTUnbal := 4992
  mulFFTMin := 352
  mulUnbalanced := 64
  mulChunkMax := 1536
  sqrFFT := 5120
  fftKFactor := 10
  divDC := 208
  divMu := 8192
  divQMu := 6144
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
  The size of the divisor from which schoolbook division takes two quotient limbs per pass, by one
  multiply-subtract pass with two rows (`Schoolbook.divLoop2In`), as measured on Zen 3: below it,
  the fixed cost of the two-limb estimate outweighs the pass it saves.
  -/
  div2Rows : Nat := 16
  sqrtZimmermann := 1
  sqrtBase := 1
  /-- The size of the smaller number from which the greatest common divisor uses half-gcd. -/
  gcdHalf : Nat := 2560
  /-- The size from which decimal strings are written by divide and conquer. -/
  strDC : Nat := 44
  /--
  The size of the result, in limbs, from which decimal strings are read by divide and conquer.
  -/
  parseDC : Nat := 1536
  deriving Repr

/-- The thresholds of the Karatsuba and Toom methods of `MPN.Toom`, a projection. -/
@[inline] public abbrev Config.toom (cfg : Config) : Toom.Config := cfg.toMulConfig.toConfig

/-- The thresholds of the choice of a product, `MPN.Dispatch`'s. -/
@[inline] public abbrev Config.mul (cfg : Config) : Dispatch.MulConfig := cfg.toMulConfig

-- The options `mpn.w64.f`, one for each threshold `f` of `Config`, with its default.
declare_config_options Config mpn.w64

end MPN.W64
