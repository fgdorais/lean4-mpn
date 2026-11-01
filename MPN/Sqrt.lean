/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops64
public import MPN.Generic.Sqrt
public import MPN.WordSqrt

/-!
# Square root

`sqrtRem` computes `⌊√a⌋` and the remainder `a - ⌊√a⌋²` by Zimmermann's Karatsuba square root,
like GMP's `mpn_sqrtrem`: `main`'s base-generic `NatOps.sqrtRemAux` on `ops64`, after normalizing
by `4ᶜ`. The base case is a double word, by Newton's iteration on words (`main`'s `sqrt2W`).
-/

open ScalarArray UInt64Array

namespace MPN

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

/-! ## Any number -/

/--
`(⌊√a⌋, a - ⌊√a⌋²)`. The value is normalized by `4ᶜ` to `2 n` limbs with `β^(2n) ≤ 4 N`, the
root of `N` by `sqrtRemAux` with `base` for roots of up to `T` limbs is shifted back by `c` bits,
and the remainder is `a - s²`.
-/
public def sqrtRemWith (base : UInt64Array → UInt64Array × UInt64Array) (T : Nat)
    (a : UInt64Array) : UInt64Array × UInt64Array :=
  let L := MPN.log2 a.toUSlice
  if L = 0 then (Num.low a 1, UInt64Array.replicate 0 0)
  else
    let n := L / 128 + 1
    let c := (128 * n - 1 - L) / 2
    let N := Num.low (Num.shl a (2 * c)) (2 * n)
    let S := Num.shr (Num.fitTo (ops64.sqrtRemAux base T N n).1 n) c
    (S, Num.sub a (Num.sqr S))

/-- `sqrtRemWith` is exact when `base` is on the roots it takes. -/
public theorem toNat_sqrtRemWith (base : UInt64Array → UInt64Array × UInt64Array) (T : Nat)
    (hbase : ∀ N n, 1 ≤ n → (n ≤ T ∨ n ≤ 1) → N.toNat < (2 ^ 64) ^ (2 * n) →
      (2 ^ 64) ^ (2 * n) ≤ 4 * N.toNat →
      (base N).1.toNat = _root_.Nat.sqrt N.toNat ∧
        (base N).2.toNat = N.toNat - _root_.Nat.sqrt N.toNat * _root_.Nat.sqrt N.toNat)
    (a : UInt64Array) (hU : 2 * a.size + 40 < USize.size) :
    (sqrtRemWith base T a).1.toNat = _root_.Nat.sqrt a.toNat ∧
      (sqrtRemWith base T a).2.toNat =
        a.toNat - _root_.Nat.sqrt a.toNat * _root_.Nat.sqrt a.toNat := by
  have ha : a.size < USize.size := by lia
  have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hL : MPN.log2 a.toUSlice = _root_.Nat.log2 a.toNat := by
    rw [log2_eq, toUSlice_toNat a ha]
  unfold sqrtRemWith
  dsimp only
  rw [hL]
  generalize hl : _root_.Nat.log2 a.toNat = L
  split
  · rename_i h0
    -- `a ≤ 1`.
    have ha1 : a.toNat ≤ 1 := by
      by_cases h : a.toNat = 0
      · lia
      · have := Nat.lt_log2_self (n := a.toNat); rw [hl, h0] at this; lia
    have hs : _root_.Nat.sqrt a.toNat = a.toNat := by
      symm; apply eq_sqrt
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> decide
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> decide
    rw [Num.toNat_low _ _ ha, hs, Nat.mod_eq_of_lt (by lia)]
    refine ⟨rfl, ?_⟩
    rw [toNat_eq_valAt]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> simp
  · rename_i h0
    have ha0 : a.toNat ≠ 0 := by intro h; rw [h] at hl; simp at hl; lia
    have hlo : 2 ^ L ≤ a.toNat := by rw [← hl]; exact Nat.log2_self_le ha0
    have hhi : a.toNat < 2 ^ (L + 1) := by rw [← hl]; exact Nat.lt_log2_self
    have hLa : L < 64 * a.size := by
      refine Nat.lt_of_not_le fun h => ?_
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
      lia
    generalize hn : L / 128 + 1 = n
    generalize hc : (128 * n - 1 - L) / 2 = c
    have hLn : L < 128 * n := by lia
    have hc₁ : 128 * n - 2 ≤ L + 2 * c := by lia
    have hc₂ : L + 2 * c + 1 ≤ 128 * n := by lia
    -- The normalized value `N = a 4ᶜ` of `2 n` limbs.
    have hshs : (Num.shl a (2 * c)).size = 2 * c / 64 + a.size + 1 := Num.size_shl ..
    have hshv : (Num.shl a (2 * c)).toNat = a.toNat * 2 ^ (2 * c) :=
      Num.toNat_shl _ _ (by lia)
    have hNlt : a.toNat * 2 ^ (2 * c) < 2 ^ (128 * n) := by
      calc a.toNat * 2 ^ (2 * c) < 2 ^ (L + 1) * 2 ^ (2 * c) :=
            Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2 ^ (L + 2 * c + 1) := by rw [← Nat.pow_add]; congr 1; lia
        _ ≤ 2 ^ (128 * n) := Nat.pow_le_pow_right (by decide) hc₂
    have hNge : 2 ^ (128 * n) ≤ 4 * (a.toNat * 2 ^ (2 * c)) := by
      calc 2 ^ (128 * n) ≤ 2 ^ (L + 2 * c + 2) := Nat.pow_le_pow_right (by decide) (by lia)
        _ = 4 * (2 ^ L * 2 ^ (2 * c)) := by
            rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
        _ ≤ 4 * (a.toNat * 2 ^ (2 * c)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlo)
    have hNs : (Num.low (Num.shl a (2 * c)) (2 * n)).size = 2 * n := by
      rw [Num.size_low _ _ (by lia), hshs]
      lia
    have hNv : (Num.low (Num.shl a (2 * c)) (2 * n)).toNat = a.toNat * 2 ^ (2 * c) := by
      rw [Num.toNat_low _ _ (by lia), hshv, Nat.mod_eq_of_lt (by
        rw [show 64 * (2 * n) = 128 * n by lia]; exact hNlt)]
    obtain ⟨i₃, -⟩ := ops64.sqrtRemAux_spec base T
      (fun N n hn h hlt hge => by
        simp only [ops64_val, show ops64.B = 2 ^ 64 from rfl] at hlt hge ⊢
        exact hbase N n hn h hlt hge)
      ⟨2 ^ 63, by decide⟩ n _ (by lia)
      (by simp only [ops64_val]; rw [hNv, show ops64.B = 2 ^ 64 from rfl, ← Nat.pow_mul,
        show 64 * (2 * n) = 128 * n by lia]; exact hNlt)
      (by simp only [ops64_val]; rw [hNv, show ops64.B = 2 ^ 64 from rfl, ← Nat.pow_mul,
        show 64 * (2 * n) = 128 * n by lia]; exact hNge)
    simp only [ops64_val] at i₃
    rw [hNv] at i₃
    generalize (ops64.sqrtRemAux base T (Num.low (Num.shl a (2 * c)) (2 * n)) n).1 = S₀ at i₃
    -- The root fits in `n` limbs.
    have hrt : Nat.sqrt (a.toNat * 2 ^ (2 * c)) < 2 ^ (64 * n) := by
      apply sqrt_lt_of
      rw [← Nat.pow_add, show 64 * n + 64 * n = 128 * n by lia]; exact hNlt
    obtain ⟨f₁, i₁⟩ := Num.fitTo_spec S₀ n (by rw [i₃]; exact hrt)
    rw [i₃] at f₁
    generalize Num.fitTo S₀ n = S at f₁ i₁
    have i₃ := f₁
    have hSv : (Num.shr S c).toNat = _root_.Nat.sqrt a.toNat := by
      rw [Num.toNat_shr _ _ (by lia), i₃, sqrt_mul_four_pow]
    have hSs : (Num.shr S c).size ≤ n := by rw [Num.size_shr]; lia
    refine ⟨hSv, ?_⟩
    rw [Num.toNat_sub _ _ (by rw [Num.toNat_sqr _ (by lia), hSv]; exact Nat.sqrt_le _) ha
      (by have := Num.size_sqr_le (Num.shr S c); lia), Num.toNat_sqr _ (by lia), hSv]

/-- `(⌊√a⌋, a - ⌊√a⌋²)` by `sqrtRemWith`, down to roots of one limb, by `sqrtBase`. -/
public def sqrtRem (a : UInt64Array) : UInt64Array × UInt64Array := sqrtRemWith sqrtBase 1 a

public theorem toNat_sqrtRem (a : UInt64Array) (hU : 2 * a.size + 40 < USize.size) :
    (sqrtRem a).1.toNat = _root_.Nat.sqrt a.toNat ∧
      (sqrtRem a).2.toNat = a.toNat - _root_.Nat.sqrt a.toNat * _root_.Nat.sqrt a.toNat :=
  toNat_sqrtRemWith sqrtBase 1 (fun N n _ h hlt _ => by
    have : n = 1 := by lia
    subst this
    exact sqrtBase_spec N hlt) a hU

end MPN
