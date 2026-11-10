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

/--
`(⌊√N⌋, N - ⌊√N⌋²)` of a double word `N = hi β + lo`, the remainder as two words `(lo, hi)`, by
`sqrt2` and one double product (`UInt64.mulh`), subtracted with a borrow.
-/
public def sqrtRem2 (hi lo : UInt64) : UInt64 × UInt64 × UInt64 :=
  let s := sqrt2 hi lo
  let q := s * s
  (s, lo - q, hi - UInt64.mulh s s - (if lo < q then 1 else 0))

public theorem sqrtRem2_spec (hi lo : UInt64) :
    (sqrtRem2 hi lo).1.toNat = Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) ∧
      (sqrtRem2 hi lo).2.1.toNat + 2 ^ 64 * (sqrtRem2 hi lo).2.2.toNat =
        hi.toNat * 2 ^ 64 + lo.toNat -
          Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) * Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) := by
  have hs := toNat_sqrt2 hi lo
  simp only [sqrtRem2]
  refine ⟨hs, ?_⟩
  generalize hN : hi.toNat * 2 ^ 64 + lo.toNat = N at hs
  have hle : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  generalize sqrt2 hi lo = s at hs ⊢
  have hq : (s * s).toNat = s.toNat * s.toNat % 2 ^ 64 := UInt64.toNat_mul ..
  have hm := UInt64.toNat_mulh s s
  rw [hs] at hq hm
  have hd := Nat.div_add_mod (Nat.sqrt N * Nat.sqrt N) (2 ^ 64)
  have hlo := lo.toNat_lt
  have hhi := hi.toNat_lt
  generalize Nat.sqrt N * Nat.sqrt N = P at *
  have hpl : P % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  split
  · rename_i hb
    have hb' : lo.toNat < P % 2 ^ 64 := by rw [← hq]; exact UInt64.lt_iff_toNat_lt.1 hb
    have h1 : (lo - s * s).toNat = lo.toNat + 2 ^ 64 - P % 2 ^ 64 := by
      rw [UInt64.toNat_sub, hq]; rw [Nat.mod_eq_of_lt (by lia)]; lia
    have hge : P / 2 ^ 64 + 1 ≤ hi.toNat := by lia
    have h2 : (hi - UInt64.mulh s s - 1).toNat = hi.toNat - P / 2 ^ 64 - 1 := by
      rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, hm]
      · simp
      · exact UInt64.le_iff_toNat_le.2 (by rw [hm]; lia)
      · apply UInt64.le_iff_toNat_le.2
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by rw [hm]; lia)), hm]
        simp; lia
    rw [h1, h2]; lia
  · rename_i hb
    have hb' : P % 2 ^ 64 ≤ lo.toNat := by
      rw [← hq]; exact UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 hb)
    have h1 : (lo - s * s).toNat = lo.toNat - P % 2 ^ 64 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by rw [hq]; exact hb')), hq]
    have hge : P / 2 ^ 64 ≤ hi.toNat := by lia
    have h2 : (hi - UInt64.mulh s s - 0).toNat = hi.toNat - P / 2 ^ 64 := by
      rw [UInt64.sub_zero, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by rw [hm]; lia)),
        hm]
    rw [h1, h2]; lia

/-! ## The base case -/

/-- The word `x` as an array of one limb. -/
@[inline] public def word (x : UInt64) : UInt64Array := UInt64Array.replicate 1 x

private theorem toNat_word (x : UInt64) : (word x).toNat = x.toNat := by
  simp [word, toNat_eq_valAt]

/-- The two words `lo + β hi` as two limbs. -/
@[inline] public def pair (lo hi : UInt64) : UInt64Array := (UInt64Array.replicate 1 lo).push hi

private theorem toNat_pair (lo hi : UInt64) : (pair lo hi).toNat = lo.toNat + 2 ^ 64 * hi.toNat := by
  rw [pair, toNat_eq_valAt]
  simp [valAt_succ]

/--
`(⌊√N⌋, N - ⌊√N⌋²)` for `N` of two limbs, by `sqrtRem2` on words: the base case of `sqrtRemAux`.
-/
public def sqrtBase (N : UInt64Array) : UInt64Array × UInt64Array :=
  let p := sqrtRem2 (Num.limbAt N 1) (Num.limbAt N 0)
  (word p.1, pair p.2.1 p.2.2)

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
  obtain ⟨h₁, h₂⟩ := sqrtRem2_spec (Num.limbAt N 1) (Num.limbAt N 0)
  rw [← hv] at h₁ h₂
  simp only [sqrtBase]
  exact ⟨by rw [toNat_word, h₁], by rw [toNat_pair, h₂]⟩

end MPN.W64
