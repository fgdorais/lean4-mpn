/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Barrett
public import MPN.Generic.DC
public import MPN.Natural

/-!
# Choosing a division and a square root

The division and the square root of both widths choose their algorithm by the sizes, with the
thresholds of a `DivConfig` and a `SqrtConfig`. Each width normalizes its operands with its own
shifts and calls:

* `divN`, for a divisor of `n` limbs with its top bit set: Barrett's division with Newton's
  reciprocal (`NatOps.divMuW`) from `divMu` limbs, and below the divide-and-conquer division
  (`NatOps.divNorm`, the scheme of Burnikel and Ziegler and of GMP's `mpn_dcpi1_div_qr`), which
  goes down to the schoolbook division of the width below `divDC` limbs;
* `divQN`, the quotient alone: by Barrett's division without the remainder of the last block
  (`NatOps.divQMuW`) from `divQMu` limbs, and otherwise that of `divN`;
* `sqrtBy`, which takes the square root of a large number by the Zimmermann recursion of the
  width when the width says so, and by Newton's iteration (`GNat.sqrtNewton`) otherwise.

Normalization only affects speed: `divN_scaled` gives the quotient and remainder of `a / b` from
those of `a f / b f`.
-/

namespace MPN.Dispatch

/-- The thresholds of the choice of a division. -/
public structure DivConfig where
  /--
  The size of the divisor from which division computes its quotient in blocks of half the
  divisor, with recursive divisions (Burnikel and Ziegler), instead of the schoolbook method.
  -/
  divDC : Nat
  /--
  The size of the divisor from which division uses Barrett's method with Newton's reciprocal,
  inside divide and conquer (so from `divDC` on).
  -/
  divMu : Nat
  /--
  The size of the divisor from which the quotient alone uses Barrett's method with Newton's
  reciprocal, which then skips the remainder of the last block, inside divide and conquer (so
  from `divDC` on).
  -/
  divQMu : Nat
  deriving Repr

/-- The thresholds of the choice of a square root. -/
public structure SqrtConfig where
  /--
  The size of the root, in limbs, from which the square root uses Zimmermann's recursion instead
  of Newton's iteration.
  -/
  sqrtZimmermann : Nat
  /--
  The size of the root, in limbs, at or below which Zimmermann's recursion finishes by Newton's
  iteration.
  -/
  sqrtBase : Nat
  deriving Repr

/-! ## Division -/

section Div

variable {α : Type} (o : NatOps α)

/--
`(U / V, U % V)` for `0 < V < Bⁿ` and `U < V Bᵏ`: by `NatOps.divMuW` from `divMu` limbs, and by
`NatOps.divNorm` with `base` below `divDC` limbs otherwise.
-/
public def divN (c : DivConfig) (base : α → α → α × α) (U V : α) (n k : Nat) : α × α :=
  if c.divMu ≤ n then o.divMuW U V else o.divNorm base c.divDC U V n k

/-- `U / V` as in `divN`: by `NatOps.divQMuW` from `divQMu` limbs. -/
public def divQN (c : DivConfig) (base : α → α → α × α) (U V : α) (n k : Nat) : α :=
  if c.divQMu ≤ n then o.divQMuW U V else (divN o c base U V n k).1

variable {o} {base : α → α → α × α}

public theorem divN_spec (c : DivConfig)
    (hbase : ∀ U V, 0 < o.val V →
      o.val (base U V).1 = o.val U / o.val V ∧ o.val (base U V).2 = o.val U % o.val V)
    {U V : α} {n k : Nat} (hV : 0 < o.val V) (hVn : o.val V < o.B ^ n)
    (hU : o.val U < o.val V * o.B ^ k) :
    o.val (divN o c base U V n k).1 = o.val U / o.val V ∧
      o.val (divN o c base U V n k).2 = o.val U % o.val V := by
  unfold divN
  split
  · exact o.divMuW_spec U V hV
  · exact o.divNorm_spec base hbase c.divDC n k U V hV hVn hU

public theorem divQN_spec (c : DivConfig)
    (hbase : ∀ U V, 0 < o.val V →
      o.val (base U V).1 = o.val U / o.val V ∧ o.val (base U V).2 = o.val U % o.val V)
    {U V : α} {n k : Nat} (hV : 0 < o.val V) (hVn : o.val V < o.B ^ n)
    (hU : o.val U < o.val V * o.B ^ k) :
    o.val (divQN o c base U V n k) = o.val U / o.val V := by
  unfold divQN
  split
  · exact o.divQMuW_spec U V hV
  · exact (divN_spec c hbase hV hVn hU).1

/-- The quotient of `a f / b f` is `a / b`, and the remainder `(a % b) f`. -/
public theorem divN_scaled (c : DivConfig)
    (hbase : ∀ U V, 0 < o.val V →
      o.val (base U V).1 = o.val U / o.val V ∧ o.val (base U V).2 = o.val U % o.val V)
    {U V : α} {n k a b f : Nat} (ha : o.val U = a * f) (hb : o.val V = b * f) (hf : 0 < f)
    (hV : 0 < b) (hVn : o.val V < o.B ^ n) (hU : o.val U < o.val V * o.B ^ k) :
    o.val (divN o c base U V n k).1 = a / b ∧
      o.val (divN o c base U V n k).2 = a % b * f := by
  have h := divN_spec c hbase (by rw [hb]; exact Nat.mul_pos hV hf) hVn hU
  rw [ha, hb, Nat.mul_div_mul_right _ _ hf, Nat.mul_mod_mul_right] at h
  exact h

/-- The quotient of `divQN` on `a f / b f` is `a / b`. -/
public theorem divQN_scaled (c : DivConfig)
    (hbase : ∀ U V, 0 < o.val V →
      o.val (base U V).1 = o.val U / o.val V ∧ o.val (base U V).2 = o.val U % o.val V)
    {U V : α} {n k a b f : Nat} (ha : o.val U = a * f) (hb : o.val V = b * f) (hf : 0 < f)
    (hV : 0 < b) (hVn : o.val V < o.B ^ n) (hU : o.val U < o.val V * o.B ^ k) :
    o.val (divQN o c base U V n k) = a / b := by
  have h := divQN_spec c hbase (by rw [hb]; exact Nat.mul_pos hV hf) hVn hU
  rw [ha, hb, Nat.mul_div_mul_right _ _ hf] at h
  exact h

end Div

/-! ## Square root -/

section Sqrt

variable {A : Type} [C : NatLimbs A]

/--
`⌊√n⌋`: by `go` on the limbs of a large `n` when `use` takes them, and by Newton's iteration
otherwise.
-/
public def sqrtBy (use : A → Bool) (go : (a : A) → C.trimmed a = true ∧ 2 ^ 64 ≤ C.val a → GNat A)
    (n : GNat A) : GNat A :=
  match n with
  | .small _ => GNat.sqrtNewton n
  | .large a h => if use a then go a h else GNat.sqrtNewton n

public theorem toNat_sqrtBy (use : A → Bool)
    (go : (a : A) → C.trimmed a = true ∧ 2 ^ 64 ≤ C.val a → GNat A)
    (hgo : ∀ a h, use a = true → (go a h).toNat = _root_.Nat.sqrt (C.val a)) (n : GNat A) :
    (sqrtBy use go n).toNat = _root_.Nat.sqrt n.toNat := by
  unfold sqrtBy
  split
  · exact GNat.toNat_sqrtNewton _
  · rename_i a h
    split
    · rename_i hu
      exact hgo a h hu
    · exact GNat.toNat_sqrtNewton _

end Sqrt

end MPN.Dispatch
