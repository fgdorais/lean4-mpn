/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean

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
public structure Config where
  /-- The size of the shorter operand from which multiplication uses Karatsuba. -/
  mulKaratsuba : Nat := 64
  /-- Karatsuba needs at least `4` limbs to make its products smaller. -/
  four_le_mulKaratsuba : 4 ≤ mulKaratsuba := by decide
  /-- The size of the shorter operand from which multiplication uses Toom-3 instead of Karatsuba. -/
  mulToom3 : Nat := 480
  /-- Toom-3 needs at least `12` limbs to make its products smaller. -/
  twelve_le_mulToom3 : 12 ≤ mulToom3 := by decide
  /--
  The size of the shorter operand from which multiplication uses Toom-3 by 2 when the longer one is
  between four thirds and twice as long, instead of Toom-3 or Karatsuba.
  -/
  mulToom32 : Nat := 160
  /-- Toom-3 by 2 needs at least `12` limbs to make its products smaller. -/
  twelve_le_mulToom32 : 12 ≤ mulToom32 := by decide
  /--
  The size of the shorter operand from which multiplication uses Toom-4 by 2 when the longer one is
  between fifteen eighths and twice as long, instead of Toom-3 by 2.
  -/
  mulToom42 : Nat := 192
  /-- Toom-4 by 2 needs at least `12` limbs to make its products smaller. -/
  twelve_le_mulToom42 : 12 ≤ mulToom42 := by decide
  /--
  The size of the shorter operand from which multiplication splits a longer operand that is at
  least twice as long, instead of using schoolbook. It only matters above `mulKaratsuba`, since the
  split pays off through Karatsuba on its pieces.
  -/
  mulUnbalanced : Nat := 96
  /-- The size from which squaring uses the schoolbook square instead of multiplying. -/
  sqrBasecase : Nat := 2
  /-- The size from which squaring uses Karatsuba. -/
  sqrKaratsuba : Nat := 96
  /-- Karatsuba needs at least `4` limbs to make its squares smaller. -/
  four_le_sqrKaratsuba : 4 ≤ sqrKaratsuba := by decide
  /-- The size from which squaring uses Toom-3 instead of Karatsuba. -/
  sqrToom3 : Nat := 720
  /-- Toom-3 needs at least `12` limbs to make its squares smaller. -/
  twelve_le_sqrToom3 : 12 ≤ sqrToom3 := by decide
  /-- The size of the divisor from which division computes its quotient in blocks of half the
  divisor, with recursive divisions, instead of one limb at a time. -/
  divDC : Nat := 176
  /-- Blocks of half the divisor need at least `4` limbs, so that the recursion has two. -/
  four_le_divDC : 4 ≤ divDC := by decide
  deriving Repr

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

public meta register_option mpn.div.dcThreshold : Nat := {
  defValue := ({} : Config).divDC
  descr := "the size of the divisor, in limbs, from which division divides by blocks recursively"
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
  let sqrToom3 := mpn.sqr.toom3Threshold.get opts
  unless 12 ≤ sqrToom3 do
    throwError "mpn.sqr.toom3Threshold must be at least 12, but it is {sqrToom3}"
  let divDC := mpn.div.dcThreshold.get opts
  unless 4 ≤ divDC do
    throwError "mpn.div.dcThreshold must be at least 4, but it is {divDC}"
  let sqrBasecase := mpn.sqr.basecaseThreshold.get opts
  let mulUnbalanced := mpn.mul.unbalancedThreshold.get opts
  let m := quote mulKaratsuba
  let u := quote mulUnbalanced
  let t := quote mulToom3
  let t₂ := quote mulToom32
  let t₄ := quote mulToom42
  let b := quote sqrBasecase
  let q := quote sqrKaratsuba
  let st := quote sqrToom3
  let dc := quote divDC
  let stx ← `(({ mulKaratsuba := $m
                 mulToom3 := $t
                 mulToom32 := $t₂
                 mulToom42 := $t₄
                 mulUnbalanced := $u
                 sqrBasecase := $b
                 sqrKaratsuba := $q
                 sqrToom3 := $st
                 divDC := $dc } : Config))
  elabTerm stx (mkConst ``Config)

end MPN
