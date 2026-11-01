/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Generic.Ops64
public import MPN.Generic.Sqrt
public import MPN.WordSqrt

/-!
# Square root

The base case of Zimmermann's Karatsuba square root (`Bridge.sqrtZ`, on `ops64`): the root of a
double word, by Newton's iteration on words (`main`'s `sqrt2W`), with its remainder.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Words -/

/-- `⌊√N⌋` of a double word `N = hi β + lo`, by `main`'s `WordArray.sqrt2W`. -/
public def sqrt2 (hi lo : UInt64) : UInt64 := WordArray.sqrt2W UInt64Array hi lo

public theorem toNat_sqrt2 (hi lo : UInt64) :
    (sqrt2 hi lo).toNat = _root_.Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) :=
  WordArray.val_sqrt2W (A := UInt64Array) hi lo

/-! ## The base case -/

/-- The word `x` as an array of one limb. -/
@[inline] public def word (x : UInt64) : UInt64Array := UInt64Array.replicate 1 x

private theorem toNat_word (x : UInt64) : (word x).toNat = x.toNat := by
  simp [word, toNat_eq_valAt]

/-- `(⌊√N⌋, N - ⌊√N⌋²)` for `N` of two limbs, by `sqrt2`: the base case of `sqrtRemAux`. -/
public def sqrtBase (N : UInt64Array) : UInt64Array × UInt64Array :=
  let S := word (sqrt2 (Num.limbAt N 1) (Num.limbAt N 0))
  (S, if fits (N.size + 4) then Num.sub N (Num.sqr S) else ops64.sub N (ops64.mul S S))

public theorem sqrtBase_spec (N : UInt64Array) (hN : N.toNat < (2 ^ 64) ^ (2 * 1)) :
    (sqrtBase N).1.toNat = Nat.sqrt N.toNat ∧
      (sqrtBase N).2.toNat = N.toNat - Nat.sqrt N.toNat * Nat.sqrt N.toNat := by
  -- `N = hi β + lo`, the limbs past the end being zero.
  have hv : N.toNat = (Num.limbAt N 1).toNat * 2 ^ 64 + (Num.limbAt N 0).toNat := by
    rw [Num.limbAt_eq, Num.limbAt_eq, toNat_eq_valAt]
    rw [show (2 ^ 64) ^ (2 * 1) = 2 ^ (64 * 2) by rw [← Nat.pow_mul]] at hN
    rcases Nat.lt_or_ge N.size 3 with h | h
    · rcases Nat.lt_or_ge N.size 2 with h' | h'
      · rcases Nat.lt_or_ge N.size 1 with h'' | h''
        · rw [show N.size = 0 by lia, valAt_zero, getElem!_neg N 1 (by lia),
            getElem!_neg N 0 (by lia)]; rfl
        · rw [show N.size = 1 by lia, valAt_one, getElem!_neg N 1 (by lia)]
          change _ = 0 * 2 ^ 64 + _; lia
      · rw [show N.size = 2 by lia, valAt_succ, valAt_one]; lia
    · -- More limbs, zero above the second since `N < β²`.
      have hsplit := UInt64Array.valAt_add N 0 2 (N.size - 2)
      rw [show 2 + (N.size - 2) = N.size by lia, ← toNat_eq_valAt] at hsplit
      have hlo : N.valAt 0 2 = N[1]!.toNat * 2 ^ 64 + N[0]!.toNat := by
        rw [valAt_succ, valAt_one]; lia
      have hlt := valAt_lt N 0 2
      have : N.valAt (0 + 2) (N.size - 2) = 0 := by
        rcases Nat.eq_zero_or_pos (N.valAt (0 + 2) (N.size - 2)) with e | e
        · exact e
        · have e' : 1 ≤ N.valAt (0 + 2) (N.size - 2) := e
          have := Nat.mul_le_mul_left (2 ^ (64 * 2)) e'
          lia
      rw [toNat_eq_valAt] at hsplit
      rw [hsplit, this, Nat.mul_zero, Nat.add_zero, hlo]
  have hS : (word (sqrt2 (Num.limbAt N 1) (Num.limbAt N 0))).toNat = Nat.sqrt N.toNat := by
    rw [toNat_word, toNat_sqrt2, hv]
  refine ⟨hS, ?_⟩
  simp only [sqrtBase]
  split
  · rename_i hf
    have hU := lt_of_fits hf
    have hSs : (word (sqrt2 (Num.limbAt N 1) (Num.limbAt N 0))).size = 1 := by simp [word]
    have hsq := Num.toNat_sqr (word (sqrt2 (Num.limbAt N 1) (Num.limbAt N 0))) (by lia)
    have hsqs := Num.size_sqr_le (word (sqrt2 (Num.limbAt N 1) (Num.limbAt N 0)))
    rw [Num.toNat_sub _ _ (by rw [hsq, hS]; exact Nat.sqrt_le _) (by lia) (by lia), hsq, hS]
  · show ops64.val (ops64.sub N (ops64.mul _ _)) = _
    rw [ops64.val_sub _ _ (by rw [ops64.val_mul, ops64_val, hS]; exact Nat.sqrt_le _),
      ops64.val_mul, ops64_val, ops64_val, hS]

end MPN.W64
