/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean
public import MPN.Toom.Ops
public meta import MPN.Toom.Ops

/-!
# Configuration

`Config` collects the size thresholds, in limbs, at which the arithmetic switches algorithms. The
algorithms take a `Config` as a parameter, and the library's own `MPN.config` is built by
`mpn_config%` from the `mpn.*` options set when the library is compiled. The package's
`lakefile.lean` sets them from the options of a project's `require`, keyed by the fields of
`Config`, for example `options = { mulKaratsuba = "48" }` (see the README). Options that are not
set keep the defaults of `Config`. Each threshold carries the proof of the condition its algorithm
needs, so an invalid value is rejected when the library is compiled.

The defaults were measured on an AMD Ryzen 5 5600X. `lake exe tune` prints the thresholds for the
machine it runs on and the options that set them.
-/

namespace MPN

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
  divMu : Nat := 10240
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

public meta register_option mpn.mul.karatsubaThreshold : Nat := {
  defValue := ({} : Config).mulKaratsuba
  descr := "the size of the larger operand, in limbs, from which multiplication uses Karatsuba"
}

public meta register_option mpn.mul.toom3Threshold : Nat := {
  defValue := ({} : Config).mulToom3
  descr := "the size of the smaller operand, in limbs, from which multiplication uses Toom-3 \
    and its unbalanced variants"
}

public meta register_option mpn.mul.toom32Threshold : Nat := {
  defValue := ({} : Config).mulToom32
  descr := "the size of the smaller operand, in limbs, from which multiplication uses Toom-3 by 2"
}

public meta register_option mpn.mul.toom42Threshold : Nat := {
  defValue := ({} : Config).mulToom42
  descr := "the size of the smaller operand, in limbs, from which multiplication uses Toom-4 by 2"
}

public meta register_option mpn.mul.toom43Threshold : Nat := {
  defValue := ({} : Config).mulToom43
  descr := "the size of the smaller operand, in limbs, from which multiplication uses Toom-4 by 3"
}

public meta register_option mpn.mul.toom4Threshold : Nat := {
  defValue := ({} : Config).mulToom4
  descr := "the size of the smaller operand, in limbs, from which multiplication uses Toom-4 \
    and Toom-4 by 3"
}

public meta register_option mpn.mul.toom6Threshold : Nat := {
  defValue := ({} : Config).mulToom6
  descr := "the size of the smaller operand, in limbs, from which multiplication uses Toom-6"
}

public meta register_option mpn.mul.fftThreshold : Nat := {
  defValue := ({} : Config).mulFFT
  descr := "the size of the larger operand, in limbs, from which multiplication uses the FFT"
}

public meta register_option mpn.mul.fftUnbalancedThreshold : Nat := {
  defValue := ({} : Config).mulFFTUnbal
  descr := "the size of the larger operand, in limbs, from which multiplication uses the FFT \
    when the operands differ by 3 : 2 or more"
}

public meta register_option mpn.mul.fftMinThreshold : Nat := {
  defValue := ({} : Config).mulFFTMin
  descr := "the size of the smaller operand, in limbs, below which multiplication does not \
    use the FFT"
}

public meta register_option mpn.mul.unbalancedThreshold : Nat := {
  defValue := ({} : Config).mulUnbalanced
  descr := "the size of the smaller operand, in limbs, from which multiplication splits an \
    operand at least twice as long"
}

public meta register_option mpn.mul.unbalancedMaxThreshold : Nat := {
  defValue := ({} : Config).mulChunkMax
  descr := "the size of the smaller operand, in limbs, from which multiplication no longer \
    splits the larger operand in the range of the FFT"
}

public meta register_option mpn.sqr.karatsubaThreshold : Nat := {
  defValue := ({} : Config).sqrKaratsuba
  descr := "the size, in limbs, from which squaring uses Karatsuba"
}

public meta register_option mpn.sqr.toom3Threshold : Nat := {
  defValue := ({} : Config).sqrToom3
  descr := "the size, in limbs, from which squaring uses Toom-3"
}

public meta register_option mpn.sqr.toom4Threshold : Nat := {
  defValue := ({} : Config).sqrToom4
  descr := "the size, in limbs, from which squaring uses Toom-4"
}

public meta register_option mpn.sqr.toom6Threshold : Nat := {
  defValue := ({} : Config).sqrToom6
  descr := "the size, in limbs, from which squaring uses Toom-6"
}

public meta register_option mpn.sqr.fftThreshold : Nat := {
  defValue := ({} : Config).sqrFFT
  descr := "the size, in limbs, from which squaring uses the FFT"
}

public meta register_option mpn.div.dcThreshold : Nat := {
  defValue := ({} : Config).divDC
  descr := "the size of the divisor, in limbs, from which division uses divide and conquer"
}

public meta register_option mpn.div.muThreshold : Nat := {
  defValue := ({} : Config).divMu
  descr := "the size of the divisor, in limbs, from which division uses Barrett's method"
}

public meta register_option mpn.gcd.halfThreshold : Nat := {
  defValue := ({} : Config).gcdHalf
  descr := "the size of the smaller number, in limbs, from which gcd uses half-gcd"
}

public meta register_option mpn.str.dcThreshold : Nat := {
  defValue := ({} : Config).strDC
  descr := "the size, in limbs, from which decimal strings are written by divide and conquer"
}

public meta register_option mpn.str.parseDCThreshold : Nat := {
  defValue := ({} : Config).parseDC
  descr := "the size of the result, in limbs, from which decimal strings are read by divide and \
    conquer"
}

open Lean Elab Term in
/-- The `Config` given by the `mpn.*` options in effect, with defaults from `Config`. -/
elab "mpn_config%" : term => do
  let opts ← getOptions
  let mulKaratsuba := mpn.mul.karatsubaThreshold.get opts
  unless 4 ≤ mulKaratsuba do
    throwError "mpn.mul.karatsubaThreshold must be at least 4, but it is {mulKaratsuba}"
  let mulToom3 := mpn.mul.toom3Threshold.get opts
  unless 12 ≤ mulToom3 do
    throwError "mpn.mul.toom3Threshold must be at least 12, but it is {mulToom3}"
  let mulToom32 := mpn.mul.toom32Threshold.get opts
  unless 12 ≤ mulToom32 do
    throwError "mpn.mul.toom32Threshold must be at least 12, but it is {mulToom32}"
  let mulToom42 := mpn.mul.toom42Threshold.get opts
  unless 12 ≤ mulToom42 do
    throwError "mpn.mul.toom42Threshold must be at least 12, but it is {mulToom42}"
  let mulToom43 := mpn.mul.toom43Threshold.get opts
  unless 32 ≤ mulToom43 do
    throwError "mpn.mul.toom43Threshold must be at least 32, but it is {mulToom43}"
  let mulToom4 := mpn.mul.toom4Threshold.get opts
  unless 32 ≤ mulToom4 do
    throwError "mpn.mul.toom4Threshold must be at least 32, but it is {mulToom4}"
  let mulToom6 := mpn.mul.toom6Threshold.get opts
  unless 32 ≤ mulToom6 do
    throwError "mpn.mul.toom6Threshold must be at least 32, but it is {mulToom6}"
  let mulFFT := mpn.mul.fftThreshold.get opts
  let mulFFTUnbal := mpn.mul.fftUnbalancedThreshold.get opts
  let mulFFTMin := mpn.mul.fftMinThreshold.get opts
  let mulUnbalanced := mpn.mul.unbalancedThreshold.get opts
  unless 1 ≤ mulUnbalanced do
    throwError "mpn.mul.unbalancedThreshold must be at least 1, but it is {mulUnbalanced}"
  let mulChunkMax := mpn.mul.unbalancedMaxThreshold.get opts
  let sqrKaratsuba := mpn.sqr.karatsubaThreshold.get opts
  unless 4 ≤ sqrKaratsuba do
    throwError "mpn.sqr.karatsubaThreshold must be at least 4, but it is {sqrKaratsuba}"
  let sqrToom3 := mpn.sqr.toom3Threshold.get opts
  unless 12 ≤ sqrToom3 do
    throwError "mpn.sqr.toom3Threshold must be at least 12, but it is {sqrToom3}"
  let sqrToom4 := mpn.sqr.toom4Threshold.get opts
  unless 32 ≤ sqrToom4 do
    throwError "mpn.sqr.toom4Threshold must be at least 32, but it is {sqrToom4}"
  let sqrToom6 := mpn.sqr.toom6Threshold.get opts
  unless 32 ≤ sqrToom6 do
    throwError "mpn.sqr.toom6Threshold must be at least 32, but it is {sqrToom6}"
  let sqrFFT := mpn.sqr.fftThreshold.get opts
  let divDC := mpn.div.dcThreshold.get opts
  let divMu := mpn.div.muThreshold.get opts
  let gcdHalf := mpn.gcd.halfThreshold.get opts
  let strDC := mpn.str.dcThreshold.get opts
  let parseDC := mpn.str.parseDCThreshold.get opts
  let mulKaratsubaStx := quote mulKaratsuba
  let mulToom3Stx := quote mulToom3
  let mulToom32Stx := quote mulToom32
  let mulToom42Stx := quote mulToom42
  let mulToom43Stx := quote mulToom43
  let mulToom4Stx := quote mulToom4
  let mulToom6Stx := quote mulToom6
  let mulFFTStx := quote mulFFT
  let mulFFTUnbalStx := quote mulFFTUnbal
  let mulFFTMinStx := quote mulFFTMin
  let mulUnbalancedStx := quote mulUnbalanced
  let mulChunkMaxStx := quote mulChunkMax
  let sqrKaratsubaStx := quote sqrKaratsuba
  let sqrToom3Stx := quote sqrToom3
  let sqrToom4Stx := quote sqrToom4
  let sqrToom6Stx := quote sqrToom6
  let sqrFFTStx := quote sqrFFT
  let divDCStx := quote divDC
  let divMuStx := quote divMu
  let gcdHalfStx := quote gcdHalf
  let strDCStx := quote strDC
  let parseDCStx := quote parseDC
  let stx ← `(({ mulKaratsuba := $mulKaratsubaStx
                 mulToom3 := $mulToom3Stx
                 mulToom32 := $mulToom32Stx
                 mulToom42 := $mulToom42Stx
                 mulToom43 := $mulToom43Stx
                 mulToom4 := $mulToom4Stx
                 mulToom6 := $mulToom6Stx
                 mulFFT := $mulFFTStx
                 mulFFTUnbal := $mulFFTUnbalStx
                 mulFFTMin := $mulFFTMinStx
                 mulUnbalanced := $mulUnbalancedStx
                 mulChunkMax := $mulChunkMaxStx
                 sqrKaratsuba := $sqrKaratsubaStx
                 sqrToom3 := $sqrToom3Stx
                 sqrToom4 := $sqrToom4Stx
                 sqrToom6 := $sqrToom6Stx
                 sqrFFT := $sqrFFTStx
                 divDC := $divDCStx
                 divMu := $divMuStx
                 gcdHalf := $gcdHalfStx
                 strDC := $strDCStx
                 parseDC := $parseDCStx } : Config))
  elabTerm stx (mkConst ``Config)

end MPN
