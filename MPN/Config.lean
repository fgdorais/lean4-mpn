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

The defaults were measured with `lake exe tune` on an AMD Ryzen 5 5600X. Running it on the target
machine prints the thresholds for that machine and the options that set them.
-/

namespace MPN

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

public meta register_option mpn.mul.karatsubaThreshold : Nat := {
  defValue := ({} : Config).mulKaratsuba
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Karatsuba"
}

public meta register_option mpn.mul.toom32Threshold : Nat := {
  defValue := ({} : Config).mulToom32
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-3 by 2 \
    when the longer one is between four thirds and twice as long"
}

public meta register_option mpn.mul.toom42Threshold : Nat := {
  defValue := ({} : Config).mulToom42
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-4 by 2 \
    when the longer one is between fifteen eighths and twice as long"
}

public meta register_option mpn.mul.toom43Threshold : Nat := {
  defValue := ({} : Config).mulToom43
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-4 by 3 \
    when the longer one is between six fifths and fifteen eighths as long"
}

public meta register_option mpn.mul.toom4Threshold : Nat := {
  defValue := ({} : Config).mulToom4
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-4"
}

public meta register_option mpn.mul.toom6Threshold : Nat := {
  defValue := ({} : Config).mulToom6
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-6"
}

public meta register_option mpn.mul.fftThreshold : Nat := {
  defValue := ({} : Config).mulFFT
  descr := "the size of the shorter operand, in limbs, from which multiplication uses the FFT"
}

public meta register_option mpn.mul.toom3Threshold : Nat := {
  defValue := ({} : Config).mulToom3
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-3"
}

public meta register_option mpn.mul.unbalancedThreshold : Nat := {
  defValue := ({} : Config).mulUnbalanced
  descr := "the size of the shorter operand, in limbs, from which multiplication splits a longer \
    operand that is at least twice as long"
}

public meta register_option mpn.sqr.basecaseThreshold : Nat := {
  defValue := ({} : Config).sqrBasecase
  descr := "the size, in limbs, from which squaring uses the schoolbook square instead of \
    multiplying"
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
  descr := "the size of the divisor, in limbs, from which division divides by blocks recursively"
}

public meta register_option mpn.div.muThreshold : Nat := {
  defValue := ({} : Config).divMu
  descr := "the size of the divisor, in limbs, from which division uses Barrett's division with \
    Newton's reciprocal"
}

public meta register_option mpn.gcd.halfThreshold : Nat := {
  defValue := ({} : Config).gcdHalf
  descr := "the size of the smaller number, in limbs, from which the greatest common divisor \
    uses half-gcd"
}

public meta register_option mpn.str.dcThreshold : Nat := {
  defValue := ({} : Config).strDC
  descr := "the size, in limbs, from which decimal strings are written by divide and conquer"
}

public meta register_option mpn.str.parseDCThreshold : Nat := {
  defValue := ({} : Config).parseDC
  descr := "the size, in limbs, from which decimal strings are read by divide and conquer"
}

open Lean Elab Term in
/-- The `Config` given by the `mpn.*` options in effect, with defaults from `Config`. -/
elab "mpn_config%" : term => do
  let opts ← getOptions
  let mulKaratsuba := mpn.mul.karatsubaThreshold.get opts
  unless 4 ≤ mulKaratsuba do
    throwError "mpn.mul.karatsubaThreshold must be at least 4, but it is {mulKaratsuba}"
  let sqrKaratsuba := mpn.sqr.karatsubaThreshold.get opts
  unless 4 ≤ sqrKaratsuba do
    throwError "mpn.sqr.karatsubaThreshold must be at least 4, but it is {sqrKaratsuba}"
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
  unless 4 ≤ divDC do
    throwError "mpn.div.dcThreshold must be at least 4, but it is {divDC}"
  let sqrBasecase := mpn.sqr.basecaseThreshold.get opts
  let mulUnbalanced := mpn.mul.unbalancedThreshold.get opts
  let m := quote mulKaratsuba
  let u := quote mulUnbalanced
  let t := quote mulToom3
  let t₂ := quote mulToom32
  let t₄ := quote mulToom42
  let t₄₃ := quote mulToom43
  let t₄₄ := quote mulToom4
  let t₆ := quote mulToom6
  let f := quote mulFFT
  let b := quote sqrBasecase
  let q := quote sqrKaratsuba
  let st := quote sqrToom3
  let st₄ := quote sqrToom4
  let st₆ := quote sqrToom6
  let sf := quote sqrFFT
  let dc := quote divDC
  let mu := quote divMu
  let gh := quote gcdHalf
  let sd := quote strDC
  let pd := quote parseDC
  let stx ← `(({ mulKaratsuba := $m
                 mulToom3 := $t
                 mulToom32 := $t₂
                 mulToom42 := $t₄
                 mulToom43 := $t₄₃
                 mulToom4 := $t₄₄
                 mulToom6 := $t₆
                 mulFFT := $f
                 mulUnbalanced := $u
                 sqrBasecase := $b
                 sqrKaratsuba := $q
                 sqrToom3 := $st
                 sqrToom4 := $st₄
                 sqrToom6 := $st₆
                 sqrFFT := $sf
                 divDC := $dc
                 divMu := $mu
                 gcdHalf := $gh
                 strDC := $sd
                 parseDC := $pd } : Config))
  elabTerm stx (mkConst ``Config)

end MPN
