/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean

/-!
# Configuration

`Config` collects the size thresholds, in limbs, at which the arithmetic switches algorithms. The
algorithms take a `Config` as a parameter, and the library's own `Bignum.config` is built by
`bignum_config%` from options set when the library is compiled, for example in the `lean_lib`
section of a `lakefile.toml`:

```
leanOptions = { weak.bignum.mul.karatsubaThreshold = 48 }
```

The key must be written bare, not quoted, and the `weak.` prefix is needed because the options are
registered by this library rather than by Lean. Options that are not set keep the defaults of
`Config`. Each threshold carries the proof of the condition its algorithm needs, so an invalid
value is rejected when the library is compiled.

The defaults were measured with `lake exe tune` on an AMD Ryzen 5 5600X. Running it on the target
machine prints the thresholds for that machine and the `leanOptions` line that sets them.
-/

namespace Bignum

/-- The size thresholds, in limbs, at which the arithmetic switches algorithms. -/
public structure Config where
  /-- The size of the shorter operand from which multiplication uses Karatsuba. -/
  mulKaratsuba : Nat := 88
  /-- Karatsuba needs at least `4` limbs to make its products smaller. -/
  four_le_mulKaratsuba : 4 ≤ mulKaratsuba := by decide
  /-- The size of the shorter operand from which multiplication uses Toom-3 instead of Karatsuba. -/
  mulToom3 : Nat := 576
  /-- Toom-3 needs at least `12` limbs to make its products smaller. -/
  twelve_le_mulToom3 : 12 ≤ mulToom3 := by decide
  /--
  The size of the shorter operand from which multiplication splits a longer operand that is at
  least twice as long, instead of using schoolbook. It only matters above `mulKaratsuba`, since the
  split pays off through Karatsuba on its pieces.
  -/
  mulUnbalanced : Nat := 144
  /-- The size from which squaring uses the schoolbook square instead of multiplying. -/
  sqrBasecase : Nat := 48
  /-- The size from which squaring uses Karatsuba. -/
  sqrKaratsuba : Nat := 220
  /-- Karatsuba needs at least `4` limbs to make its squares smaller. -/
  four_le_sqrKaratsuba : 4 ≤ sqrKaratsuba := by decide
  deriving Repr

public meta register_option bignum.mul.karatsubaThreshold : Nat := {
  defValue := ({} : Config).mulKaratsuba
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Karatsuba"
}

public meta register_option bignum.mul.toom3Threshold : Nat := {
  defValue := ({} : Config).mulToom3
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Toom-3"
}

public meta register_option bignum.mul.unbalancedThreshold : Nat := {
  defValue := ({} : Config).mulUnbalanced
  descr := "the size of the shorter operand, in limbs, from which multiplication splits a longer \
    operand that is at least twice as long"
}

public meta register_option bignum.sqr.basecaseThreshold : Nat := {
  defValue := ({} : Config).sqrBasecase
  descr := "the size, in limbs, from which squaring uses the schoolbook square instead of \
    multiplying"
}

public meta register_option bignum.sqr.karatsubaThreshold : Nat := {
  defValue := ({} : Config).sqrKaratsuba
  descr := "the size, in limbs, from which squaring uses Karatsuba"
}

open Lean Elab Term in
/-- The `Config` given by the `bignum.*` options in effect, with defaults from `Config`. -/
elab "bignum_config%" : term => do
  let opts ← getOptions
  let mulKaratsuba := bignum.mul.karatsubaThreshold.get opts
  unless 4 ≤ mulKaratsuba do
    throwError "bignum.mul.karatsubaThreshold must be at least 4, but it is {mulKaratsuba}"
  let sqrKaratsuba := bignum.sqr.karatsubaThreshold.get opts
  unless 4 ≤ sqrKaratsuba do
    throwError "bignum.sqr.karatsubaThreshold must be at least 4, but it is {sqrKaratsuba}"
  let mulToom3 := bignum.mul.toom3Threshold.get opts
  unless 12 ≤ mulToom3 do
    throwError "bignum.mul.toom3Threshold must be at least 12, but it is {mulToom3}"
  let sqrBasecase := bignum.sqr.basecaseThreshold.get opts
  let mulUnbalanced := bignum.mul.unbalancedThreshold.get opts
  let m := quote mulKaratsuba
  let u := quote mulUnbalanced
  let t := quote mulToom3
  let b := quote sqrBasecase
  let q := quote sqrKaratsuba
  let stx ← `(({ mulKaratsuba := $m
                 mulToom3 := $t
                 mulUnbalanced := $u
                 sqrBasecase := $b
                 sqrKaratsuba := $q } : Config))
  elabTerm stx (mkConst ``Config)

end Bignum
