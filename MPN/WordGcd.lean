/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# The greatest common divisor on words

Euclid's algorithm on `UInt64` (`wordGcd`), and the runs of Euclid's steps on the leading words of
two numbers that Lehmer's algorithm takes (`lehmerSteps`), with their cofactors. Both libraries
apply the cofactors to their numbers in their own way and check them there, so nothing is proved
about `lehmerSteps`.
-/

namespace MPN

/-- Euclid's algorithm on words. -/
public def wordGcd (a b : UInt64) : UInt64 :=
  if _h : b = 0 then a else wordGcd b (a % b)
termination_by b.toNat
decreasing_by
  have : b.toNat ≠ 0 := fun h' => _h (UInt64.toNat_inj.1 (by simpa using h'))
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (by lia)

public theorem toNat_wordGcd (a b : UInt64) :
    (wordGcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  induction a, b using wordGcd.induct with
  | case1 a => rw [wordGcd]; simp
  | case2 a b h ih =>
    rw [wordGcd, dite_eq_right h, ih, UInt64.toNat_mod, Nat.gcd_comm a.toNat b.toNat,
      Nat.gcd_rec b.toNat a.toNat, Nat.gcd_comm]

/-- The cofactors of a run of Lehmer's steps, as one object with unboxed fields. -/
public structure Cofactors where
  A : Int64
  B : Int64
  C : Int64
  D : Int64

/--
Euclid's algorithm on the leading words `x ≥ y` of two numbers, with the cofactors `A`, `B`, `C`,
`D` of the steps so far, like GMP's `hgcd2` on one word: it stops when the remainder falls below
`2³¹`, half the bits of the words, which keeps the cofactors below `2³¹`, or when Jebelean's
condition fails, which makes the quotients those of the full numbers. A quotient of `1`, the most
common, costs a comparison rather than a division. It computes in `Int64`, since `Int` boxes
values from `2³¹`. Nothing is proved about it: the caller checks the cofactors it returns, and
takes a step of Euclid's algorithm when they do not apply.
-/
public def lehmerSteps (x y A B C D : Int64) : Nat → Cofactors
  | 0 => ⟨A, B, C, D⟩
  | f + 1 =>
    if y < 0x80000000 then ⟨A, B, C, D⟩
    else
      let q : Int64 := if x < y + y then 1 else x / y
      let r := x - q * y
      let C' := A - q * C
      let D' := B - q * D
      -- Jebelean's condition: the quotient is that of the full numbers when the remainder and
      -- the difference of the remainders exceed the cofactors and their differences.
      if r < C'.abs ∨ r < D'.abs ∨ y - r < (C' - C).abs ∨ y - r < (D' - D).abs ∨
          0x80000000 ≤ C'.abs ∨ 0x80000000 ≤ D'.abs then
        ⟨A, B, C, D⟩
      else lehmerSteps y r C D C' D' f

/-- Two words, as one object with unboxed fields. -/
public structure LeadWords where
  x : Int64
  y : Int64

end MPN
