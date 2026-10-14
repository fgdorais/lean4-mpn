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

The defaults were measured on an AMD Ryzen 5 5600X.
-/

namespace Bignum

/-- The size thresholds, in limbs, at which the arithmetic switches algorithms. -/
public structure Config where
  /-- The size of the shorter operand from which multiplication uses Karatsuba. -/
  mulKaratsuba : Nat := 68
  /-- Karatsuba needs at least `4` limbs to make its products smaller. -/
  four_le_mulKaratsuba : 4 ≤ mulKaratsuba := by decide
  /--
  The size of the shorter operand from which multiplication splits a longer operand that is at
  least twice as long, instead of using schoolbook. It only matters above `mulKaratsuba`, since the
  split pays off through Karatsuba on its pieces.
  -/
  mulUnbalanced : Nat := 160
  deriving Repr

public meta register_option bignum.mul.karatsubaThreshold : Nat := {
  defValue := ({} : Config).mulKaratsuba
  descr := "the size of the shorter operand, in limbs, from which multiplication uses Karatsuba"
}

public meta register_option bignum.mul.unbalancedThreshold : Nat := {
  defValue := ({} : Config).mulUnbalanced
  descr := "the size of the shorter operand, in limbs, from which multiplication splits a longer \
    operand that is at least twice as long"
}

open Lean Elab Term in
/-- The `Config` given by the `bignum.*` options in effect, with defaults from `Config`. -/
elab "bignum_config%" : term => do
  let opts ← getOptions
  let mulKaratsuba := bignum.mul.karatsubaThreshold.get opts
  unless 4 ≤ mulKaratsuba do
    throwError "bignum.mul.karatsubaThreshold must be at least 4, but it is {mulKaratsuba}"
  let mulUnbalanced := bignum.mul.unbalancedThreshold.get opts
  let m := quote mulKaratsuba
  let u := quote mulUnbalanced
  let stx ← `(({ mulKaratsuba := $m
                 mulUnbalanced := $u } : Config))
  elabTerm stx (mkConst ``Config)

end Bignum
