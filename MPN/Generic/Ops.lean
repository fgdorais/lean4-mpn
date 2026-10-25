/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Whole-number operations at any base

`NatOps α` bundles the operations on numbers represented by `α` that the base-generic algorithms
(`MPN.Generic`) use, each with its specification on values: numbers of `size x` limbs at a base
`B`, with products, sums, differences, comparison, low and high parts, shifts by whole limbs,
powers of `B`, and a slow division to fall back on. Nothing here depends on the width of a limb,
so an algorithm written and proved over `NatOps` serves 32-bit limbs today and 64-bit limbs later
with only a new instance.
-/

namespace MPN

/-- Whole-number operations at base `B` on a representation `α`, with their values. -/
public structure NatOps (α : Type) where
  /-- The base, `2³²` for 32-bit limbs. -/
  B : Nat
  one_lt_B : 1 < B
  /-- The value of a representation. -/
  val : α → Nat
  /-- The number of limbs, an upper bound on the length of the value. -/
  size : α → Nat
  val_lt (x : α) : val x < B ^ size x
  mul : α → α → α
  val_mul (x y : α) : val (mul x y) = val x * val y
  /-- `x²`, which squaring computes faster than `mul x x`. -/
  sqr : α → α
  val_sqr (x : α) : val (sqr x) = val x * val x
  add : α → α → α
  val_add (x y : α) : val (add x y) = val x + val y
  /-- `x - y`, specified when `y ≤ x`. -/
  sub : α → α → α
  val_sub (x y : α) : val y ≤ val x → val (sub x y) = val x - val y
  /-- Whether `x ≤ y`. -/
  le : α → α → Bool
  le_iff (x y : α) : le x y = true ↔ val x ≤ val y
  /-- The low `k` limbs: `x % Bᵏ`. -/
  lo : Nat → α → α
  val_lo (k : Nat) (x : α) : val (lo k x) = val x % B ^ k
  /-- The limbs from `k` on: `x / Bᵏ`. -/
  hi : Nat → α → α
  val_hi (k : Nat) (x : α) : val (hi k x) = val x / B ^ k
  size_hi (k : Nat) (x : α) : size (hi k x) = size x - k
  /-- `x Bᵏ`. -/
  shl : Nat → α → α
  val_shl (k : Nat) (x : α) : val (shl k x) = val x * B ^ k
  /-- `Bᵏ`. -/
  pow : Nat → α
  val_pow (k : Nat) : val (pow k) = B ^ k
  one : α
  val_one : val one = 1
  /-- `(x / y, x % y)` by a slow algorithm, the fallback of the fast ones. -/
  divRem : α → α → α × α
  val_divRem (x y : α) : val y ≠ 0 →
    val (divRem x y).1 = val x / val y ∧ val (divRem x y).2 = val x % val y

end MPN
