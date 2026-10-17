/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Div.Basecase
public import Bignum.Bits

/-!
# Division by two limbs

`divRem2 a d₁ d₀` divides `a` by the two-limb number `d = d₁ β + d₀`, like GMP's `mpn_divrem_2`:
the divisor is normalized to a word `V = d 2^s` with its top bit set, `a` is shifted left by `s`
bits, and one pass from the top limb down divides the remainder so far, a word below `V`, followed
by the next limb, by `V`. The remainder shifted back is `a % d`.

Each step estimates the quotient limb with `qEstimate3`, from the top three limbs of the window
and both limbs of `V`, which is exact for a divisor of two limbs; `div2Fix` then decreases it while
it is too large, which never happens but needs no proof that it doesn't: the estimate is never too
small, so the loop stops exactly at the quotient. The comparison and the remainder use words only:
`q V = ph β + a₀` against `W = R β + x`.
-/

open ScalarArray

namespace Bignum

/--
Decreases `q` while `q (vt β + vs)` exceeds `R β + x`, then returns `q` with the remainder
`R β + x - q (vt β + vs)`, all in words.
-/
public def div2Fix (vt vs : UInt32) (R : UInt64) (x q : UInt32) : UInt32 × UInt64 :=
  let a := q.toUInt64 * vs.toUInt64
  let ph := q.toUInt64 * vt.toUInt64 + (a >>> 32)
  let a₀ := a.toUInt32
  if q ≠ 0 ∧ (R < ph ∨ (R = ph ∧ x < a₀)) then
    div2Fix vt vs R x (q - 1)
  else
    (q, ((R - ph) <<< 32) + x.toUInt64 - a₀.toUInt64)
termination_by q.toNat
decreasing_by
  rw [UInt32.toNat_sub_of_le _ _ (by
    rw [UInt32.le_iff_toNat_le]
    have : q.toNat ≠ 0 := fun h => ‹q ≠ 0 ∧ _›.1 (UInt32.toNat_inj.1 (by simpa using h))
    simp; omega)]
  have : q.toNat ≠ 0 := fun h => ‹q ≠ 0 ∧ _›.1 (UInt32.toNat_inj.1 (by simpa using h))
  simp; omega

/-- `div2Fix` divides `W = R β + x` by `V = vt β + vs` when it starts at or above the quotient. -/
private theorem div2Fix_spec (vt vs : UInt32) (R : UInt64) (x q : UInt32) (V W : Nat)
    (hV : V = vt.toNat * 2 ^ 32 + vs.toNat) (hW : W = R.toNat * 2 ^ 32 + x.toNat)
    (hVpos : 0 < V) (hq : W / V ≤ q.toNat) :
    (div2Fix vt vs R x q).1.toNat = W / V ∧ (div2Fix vt vs R x q).2.toNat = W % V := by
  induction q using div2Fix.induct vt vs R x with
  | case1 q a ph a₀ hc ih =>
    rw [div2Fix]
    simp only [a, ph, a₀] at hc
    rw [ite_eq_left hc]
    have hq0 : q.toNat ≠ 0 := fun h => hc.1 (UInt32.toNat_inj.1 (by simpa using h))
    have hvt := vt.toNat_lt
    have hvs := vs.toNat_lt
    have hq32 := q.toNat_lt
    have hx := x.toNat_lt
    have hav : (q.toUInt64 * vs.toUInt64).toNat = q.toNat * vs.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide))
    have hqv : (q.toUInt64 * vt.toUInt64).toNat = q.toNat * vt.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvt) (by decide))
    have hle₁ : q.toNat * vt.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hle₂ : q.toNat * vs.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
    have hph : (q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32)).toNat =
        q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hqv, UInt64.toNat_shiftRight, hav]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have ha₀ : ((q.toUInt64 * vs.toUInt64).toUInt32).toNat = q.toNat * vs.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hav]
    -- `q V = ph β + a₀`, and the condition says `W < q V`.
    have hP : q.toNat * V = (q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32) * 2 ^ 32 +
        q.toNat * vs.toNat % 2 ^ 32 := by
      have := Nat.div_add_mod (q.toNat * vs.toNat) (2 ^ 32)
      rw [hV, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc]
      omega
    have hlt : W < q.toNat * V := by
      have h2 := hc.2
      simp only [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, hph, ha₀] at h2
      rcases h2 with h2 | ⟨h2, h3⟩
      · rw [hP, hW]; omega
      · have hR' : R.toNat = q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
          rw [h2, hph]
        rw [hP, hW, hR']; omega
    have hdiv : W / V < q.toNat := (Nat.div_lt_iff_lt_mul hVpos).2 (by
      rw [Nat.mul_comm] at hlt; first | exact hlt | (rw [Nat.mul_comm]; exact hlt))
    apply ih
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp only [UInt32.reduceToNat]
    omega
  | case2 q a ph a₀ hc =>
    rw [div2Fix]
    simp only [a, ph, a₀] at hc
    rw [ite_eq_right hc]
    have hvt := vt.toNat_lt
    have hvs := vs.toNat_lt
    have hq32 := q.toNat_lt
    have hx := x.toNat_lt
    have hR := R.toNat_lt
    have hav : (q.toUInt64 * vs.toUInt64).toNat = q.toNat * vs.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide))
    have hqv : (q.toUInt64 * vt.toUInt64).toNat = q.toNat * vt.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvt) (by decide))
    have hle₁ : q.toNat * vt.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hle₂ : q.toNat * vs.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
    have hph : (q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32)).toNat =
        q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hqv, UInt64.toNat_shiftRight, hav]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have ha₀ : ((q.toUInt64 * vs.toUInt64).toUInt32).toNat = q.toNat * vs.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hav]
    have hP : q.toNat * V = (q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32) * 2 ^ 32 +
        q.toNat * vs.toNat % 2 ^ 32 := by
      have := Nat.div_add_mod (q.toNat * vs.toNat) (2 ^ 32)
      rw [hV, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc]
      omega
    generalize q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 = PH at hph hP
    generalize q.toNat * vs.toNat % 2 ^ 32 = A₀ at ha₀ hP
    have hA₀ : A₀ < 2 ^ 32 := by rw [← ha₀]; exact UInt32.toNat_lt _
    -- Not too large: `q V ≤ W`, so `q` is the quotient.
    have hge : q.toNat * V ≤ W := by
      by_cases hq0 : q = 0
      · rw [hq0, UInt32.toNat_zero, Nat.zero_mul]; exact Nat.zero_le _
      · have h2 : ¬(R < q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32) ∨
            (R = q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32) ∧
              x < (q.toUInt64 * vs.toUInt64).toUInt32)) := fun h => hc ⟨hq0, h⟩
        simp only [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, hph, ha₀, not_or,
          not_and, Nat.not_lt] at h2
        have h3 : PH ≤ R.toNat := h2.1
        rw [hP, hW]
        by_cases he : R.toNat = PH
        · have := h2.2 (UInt64.toNat_inj.1 (by rw [he, hph]))
          omega
        · omega
    have hqq : q.toNat = W / V :=
      Nat.le_antisymm ((Nat.le_div_iff_mul_le hVpos).2 hge) hq
    refine ⟨hqq, ?_⟩
    -- The remainder `W - q V` is below `V < 2⁶⁴`, so the word arithmetic doesn't wrap.
    have hmod : W % V = W - q.toNat * V := by
      rw [hqq, Nat.mod_eq_sub_mul_div, Nat.mul_comm]
    have hrem := Nat.mod_lt W hVpos
    have hV64 : V ≤ 2 ^ 64 := by rw [hV]; omega
    have hRph : PH ≤ R.toNat := by rw [hP, hW] at hge; omega
    rw [hmod]
    rw [hmod, hP, hW] at hrem
    rw [hP, hW]
    rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_shiftLeft,
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hph]; exact hRph), hph,
      UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, ha₀]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega

/--
`min ⌊R / vt⌋ (β - 1)`, the first estimate of a quotient limb (`qEstimate` of the two limbs of
`R`). It tests the high half instead of comparing with `2³²`: the kernel would otherwise unfold
the literal while checking the loop that uses it.
-/
@[inline] public def div2Est (R : UInt64) (vt : UInt32) : UInt32 :=
  let e := R / vt.toUInt64
  if e >>> 32 = 0 then e.toUInt32 else 0xFFFFFFFF

private theorem toNat_div2Est (R : UInt64) (vt : UInt32) :
    (div2Est R vt).toNat = min (R.toNat / vt.toNat) (2 ^ 32 - 1) := by
  have he : (R / vt.toUInt64).toNat = R.toNat / vt.toNat := by
    rw [UInt64.toNat_div, UInt32.toNat_toUInt64]
  unfold div2Est
  simp only
  split
  · rename_i h
    have h' : (R / vt.toUInt64).toNat / 2 ^ 32 = 0 := by
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_shiftRight] at this
      simpa [Nat.shiftRight_eq_div_pow] using this
    rw [he] at h'
    rw [UInt64.toNat_toUInt32, he]
    have : R.toNat / vt.toNat < 2 ^ 32 := by
      rcases Nat.lt_or_ge (R.toNat / vt.toNat) (2 ^ 32) with h'' | h''
      · exact h''
      · have := Nat.div_le_div_right (c := 2 ^ 32) h''; simp at this; omega
    omega
  · rename_i h
    have h' : (R / vt.toUInt64).toNat / 2 ^ 32 ≠ 0 := by
      intro h''
      apply h
      apply UInt64.toNat_inj.1
      rw [UInt64.toNat_shiftRight]
      simpa [Nat.shiftRight_eq_div_pow] using h''
    rw [he] at h'
    have : 2 ^ 32 ≤ R.toNat / vt.toNat := by
      rcases Nat.lt_or_ge (R.toNat / vt.toNat) (2 ^ 32) with h'' | h''
      · exact absurd (Nat.div_eq_of_lt h'') h'
      · exact h''
    simp only [UInt32.reduceToNat]
    omega

/-- One step: the quotient limb and remainder of `R β + x` by `vt β + vs`, for `R < vt β + vs`. -/
@[inline] public def div2Step (vt vs : UInt32) (R : UInt64) (x : UInt32) : UInt32 × UInt64 :=
  let wt := (R >>> 32).toUInt32
  let wn := R.toUInt32
  div2Fix vt vs R x (qEstimate3 (div2Est R vt) wt wn x vt vs)

public theorem div2Step_spec (vt vs : UInt32) (R : UInt64) (x : UInt32) (hvt : 0 < vt.toNat)
    (hR : R.toNat < vt.toNat * 2 ^ 32 + vs.toNat) :
    (div2Step vt vs R x).1.toNat =
        (R.toNat * 2 ^ 32 + x.toNat) / (vt.toNat * 2 ^ 32 + vs.toNat) ∧
      (div2Step vt vs R x).2.toNat =
        (R.toNat * 2 ^ 32 + x.toNat) % (vt.toNat * 2 ^ 32 + vs.toNat) := by
  have hR64 := R.toNat_lt
  have hx := x.toNat_lt
  have hwt : ((R >>> 32).toUInt32).toNat = R.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have hwn : (R.toUInt32).toNat = R.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
  have hRsplit : R.toNat / 2 ^ 32 * 2 ^ 32 + R.toNat % 2 ^ 32 = R.toNat := by
    have := Nat.div_add_mod R.toNat (2 ^ 32); omega
  obtain ⟨V, hVdef⟩ : ∃ V, vt.toNat * 2 ^ 32 + vs.toNat = V := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, R.toNat * 2 ^ 32 + x.toNat = W := ⟨_, rfl⟩
  rw [hVdef] at hR ⊢
  rw [hW]
  have hVpos : 0 < V := by omega
  -- The quotient `Q` is at most both estimates.
  have hQV : W / V * V ≤ W := Nat.div_mul_le_self W V
  have hQβ : W / V < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hVpos]
    have := Nat.mul_le_mul_right (2 ^ 32) (show R.toNat + 1 ≤ V by omega)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm (2 ^ 32) V]
    omega
  have hQ₀ : W / V * vt.toNat ≤ R.toNat := by
    -- `Q vt β ≤ Q V ≤ W < (R + 1) β`.
    have h₁ : W / V * vt.toNat * 2 ^ 32 ≤ W / V * V := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have h₂ : W / V * vt.toNat * 2 ^ 32 < (R.toNat + 1) * 2 ^ 32 := by
      rw [Nat.succ_mul]; omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h₂)
  have hest := toNat_div2Est R vt
  have hle : (div2Est R vt).toNat * vt.toNat ≤
      ((R >>> 32).toUInt32).toNat * 2 ^ 32 + (R.toUInt32).toNat := by
    rw [hwt, hwn, hRsplit, hest]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) (Nat.div_mul_le_self _ _)
  have h₀ : W / V ≤ (div2Est R vt).toNat := by
    rw [hest]
    exact Nat.le_min.2 ⟨(Nat.le_div_iff_mul_le hvt).2 hQ₀, by omega⟩
  have h₁ : W / V * (vt.toNat * 2 ^ 32 + vs.toNat) ≤
      (((R >>> 32).toUInt32).toNat * 2 ^ 32 + (R.toUInt32).toNat) * 2 ^ 32 + x.toNat := by
    rw [hwt, hwn, hRsplit, hW, hVdef]
    exact hQV
  have hq := qEstimate3_ge _ _ _ x vt vs (W / V) hle h₀ h₁
  exact div2Fix_spec vt vs R x _ V W hVdef.symm hW.symm hVpos hq

/-! ## Normalizing on the fly

Limb `k` of `a 2ˢ`, for `s < 32`, is the high word of `(a[k] β + a[k-1]) 2ˢ`, from two limbs of
`a`, so the loop can read the limbs of the normalized dividend from `a` as it needs them, without
a shifted copy.
-/

/-- Digit `j + 1` of `a 2ˢ` in base `β` from digits `j + 1` and `j` of `a`. -/
private theorem shl_digit_succ (a s j : Nat) (hs : s < 32) :
    ((a / 2 ^ (32 * (j + 1)) % 2 ^ 32) * 2 ^ 32 + a / 2 ^ (32 * j) % 2 ^ 32) * 2 ^ s / 2 ^ 32 %
        2 ^ 32 = a * 2 ^ s / 2 ^ (32 * (j + 1)) % 2 ^ 32 := by
  have hB : (0 : Nat) < 2 ^ 32 := by decide
  have hS : 0 < 2 ^ s := Nat.two_pow_pos s
  generalize hc : a / 2 ^ (32 * j) = c
  have h₁ : a / 2 ^ (32 * (j + 1)) = c / 2 ^ 32 := by
    rw [← hc, Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2
  rw [h₁]
  -- The two digits are `c` modulo `β²`, which is all that the digit needs.
  have h₂ : (c / 2 ^ 32 % 2 ^ 32) * 2 ^ 32 + c % 2 ^ 32 = c % (2 ^ 32 * 2 ^ 32) := by
    rw [Nat.mod_mul]; lia
  rw [h₂]
  have h₃ : c % (2 ^ 32 * 2 ^ 32) * 2 ^ s / 2 ^ 32 % 2 ^ 32 = c * 2 ^ s / 2 ^ 32 % 2 ^ 32 := by
    conv => rhs; rw [← Nat.div_add_mod c (2 ^ 32 * 2 ^ 32)]
    generalize c / (2 ^ 32 * 2 ^ 32) = q
    generalize c % (2 ^ 32 * 2 ^ 32) = m
    rw [Nat.add_mul, show 2 ^ 32 * 2 ^ 32 * q * 2 ^ s = 2 ^ 32 * (2 ^ 32 * q * 2 ^ s) by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc], Nat.mul_add_div hB,
      show 2 ^ 32 * q * 2 ^ s = 2 ^ 32 * (q * 2 ^ s) by rw [Nat.mul_assoc], Nat.mul_add_mod]
  rw [h₃]
  -- The limbs of `a` below digit `j` shift into digit `j` only, never past it.
  have h₄ : a * 2 ^ s / 2 ^ (32 * (j + 1)) = c * 2 ^ s / 2 ^ 32 := by
    have hP : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    have ha := Nat.div_add_mod a (2 ^ (32 * j))
    rw [hc] at ha
    have hr := Nat.mod_lt a hP
    generalize a % 2 ^ (32 * j) = r at ha hr
    rw [show 32 * (j + 1) = 32 * j + 32 by lia, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← ha,
      Nat.add_mul, Nat.mul_assoc, Nat.mul_add_div hP]
    have hf : r * 2 ^ s / 2 ^ (32 * j) < 2 ^ s := by
      rw [Nat.div_lt_iff_lt_mul hP]
      rw [Nat.mul_comm (2 ^ s)]
      exact Nat.mul_lt_mul_of_pos_right hr hS
    generalize r * 2 ^ s / 2 ^ (32 * j) = f at hf
    have hsplit : 2 ^ 32 = 2 ^ (32 - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; lia
    have hm : c * 2 ^ s % 2 ^ 32 = c % 2 ^ (32 - s) * 2 ^ s := by
      rw [hsplit, Nat.mul_mod_mul_right]
    have hlt : c % 2 ^ (32 - s) * 2 ^ s + f < 2 ^ 32 := by
      have := Nat.mod_lt c (Nat.two_pow_pos (32 - s))
      have := Nat.mul_le_mul_right (2 ^ s) (show c % 2 ^ (32 - s) + 1 ≤ 2 ^ (32 - s) by lia)
      rw [Nat.add_mul, Nat.one_mul, ← hsplit] at this
      lia
    -- `c 2ˢ = β u + w` with `w + f < β`.
    have hcw := Nat.div_add_mod (c * 2 ^ s) (2 ^ 32)
    rw [hm] at hcw
    conv => lhs; rw [← hcw, Nat.add_assoc, Nat.mul_add_div hB, Nat.div_eq_of_lt hlt, Nat.add_zero]
  rw [h₄]

/-- Digit `j` of `toNat a` in base `β` is its limb `j`, or `0` past its end. -/
private theorem toNat_getD_slice (a : UInt32Array.Slice) (j : Nat) :
    (a.getD j 0).toNat = toNat a / 2 ^ (32 * j) % 2 ^ 32 := by
  rw [getD_eq_getD_toList_copy, toNat_getD_eq]
  rfl

/--
Limb `k` of `a 2ˢ`, for `s < 32`, read from limbs `k` and `k - 1` of the `n` limbs of `arr` from
`st` on: the high word of `(a[k] β + a[k-1]) 2ˢ`, with limbs past either end read as `0`.
-/
@[inline] def shlLimbU (arr : UInt32Array) (st n : USize) (has : arr.size < USize.size)
    (h : st.toNat + n.toNat ≤ arr.size) (s : UInt64) (k : USize) : UInt32 :=
  let hi : UInt32 := if hk : k < n then limbU arr st n has h k (USize.lt_iff_toNat_lt.1 hk) else 0
  let lo : UInt32 :=
    if hk : 0 < k ∧ k - 1 < n then limbU arr st n has h (k - 1) (USize.lt_iff_toNat_lt.1 hk.2)
    else 0
  ((((hi.toUInt64 <<< 32) + lo.toUInt64) <<< s) >>> 32).toUInt32

/-- A limb read by `limbU` from a slice, or `0` past its end, is a digit of its value. -/
private theorem toNat_limbU_or_zero (a : UInt32Array.Slice) (has : a.array.size < USize.size)
    (i : USize) (c : Prop) [Decidable c] (hc : c ↔ i.toNat < a.size)
    (hb : c → i.toNat < a.size.toUSize.toNat) :
    (if h : c then limbU a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) i (hb h)
      else 0).toNat = toNat a / 2 ^ (32 * i.toNat) % 2 ^ 32 := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  by_cases h : c
  · rw [dite_eq_left h, ← toNat_getD_slice, UInt32Array.Slice.getD_eq, dite_eq_left (hc.1 h),
      limbU_eq_getElem _ _ _ _ _ _ _ (a.start + i.toNat)
        (by rw [toNat_toUSize (by lia)])]
    rfl
  · rw [dite_eq_right h, UInt32.toNat_zero]
    have hlt := toNat_lt a
    have : 2 ^ (32 * a.size) ≤ 2 ^ (32 * i.toNat) :=
      Nat.pow_le_pow_right (by decide) (by have := mt hc.2 h; lia)
    rw [Nat.div_eq_of_lt (by lia), Nat.zero_mod]

/-- `0 - 1` wraps to the largest `USize`. -/
private theorem toNat_zero_sub_one : ((0 : USize) - 1).toNat = USize.size - 1 := by
  rw [USize.toNat_sub, USize.toNat_zero, USize.toNat_one, Nat.add_zero]
  exact Nat.mod_eq_of_lt (by have := USize.size_pos; show USize.size - 1 < USize.size; lia)

private theorem toNat_shlLimbU (a : UInt32Array.Slice) (has : a.array.size < USize.size)
    (s : Nat) (hs : s < 32) (k : USize) :
    (shlLimbU a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) s.toUInt64 k).toNat =
      toNat a * 2 ^ s / 2 ^ (32 * k.toNat) % 2 ^ 32 := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  have hn : a.size.toUSize.toNat = a.size := toNat_toUSize (by lia)
  have hhi := toNat_limbU_or_zero a has k (k < a.size.toUSize) (by rw [USize.lt_iff_toNat_lt, hn])
    (fun hk => USize.lt_iff_toNat_lt.1 hk)
  have hlo := toNat_limbU_or_zero a has (k - 1) (0 < k ∧ k - 1 < a.size.toUSize)
    (by
      rw [USize.lt_iff_toNat_lt, USize.lt_iff_toNat_lt, hn]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
      · have : k = 0 := USize.toNat_inj.1 (by simpa using h0)
        subst this
        have := USize.le_size
        rw [toNat_zero_sub_one] at h
        lia
      · simpa using h0)
    (fun hk => USize.lt_iff_toNat_lt.1 hk.2)
  unfold shlLimbU
  simp only at hhi hlo ⊢
  generalize (if h : k < a.size.toUSize then limbU a.array a.start.toUSize a.size.toUSize has
    (limbU_bound a has) k (USize.lt_iff_toNat_lt.1 h) else 0) = hi at hhi ⊢
  generalize (if h : 0 < k ∧ k - 1 < a.size.toUSize then limbU a.array a.start.toUSize
    a.size.toUSize has (limbU_bound a has) (k - 1) (USize.lt_iff_toNat_lt.1 h.2) else 0) = lo
    at hlo ⊢
  -- Limb `k - 1`, which is `0` for `k = 0`.
  have hlo' :
      lo.toNat = if k.toNat = 0 then 0 else toNat a / 2 ^ (32 * (k.toNat - 1)) % 2 ^ 32 := by
    rw [hlo]
    split
    · rename_i h0
      have : k = 0 := USize.toNat_inj.1 (by simpa using h0)
      subst this
      have hlt := toNat_lt a
      have := USize.le_size
      have : 2 ^ (32 * a.size) ≤ 2 ^ (32 * (0 - 1 : USize).toNat) :=
        Nat.pow_le_pow_right (by decide) (by
          rw [toNat_zero_sub_one]; lia)
      rw [Nat.div_eq_of_lt (by lia), Nat.zero_mod]
    · rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; simp; lia), USize.toNat_one]
  have hs64 : s.toUInt64.toNat = s := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by lia)
  have hhiβ := hi.toNat_lt
  have hloβ := lo.toNat_lt
  have hY : ((hi.toUInt64 <<< 32) + lo.toUInt64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    lia
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hY, hs64,
    Nat.mod_eq_of_lt (show s < 64 by lia), Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (UInt64.toNat 32 % 64) = 32 by decide, show (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 by decide,
    Nat.mod_mul_right_div_self, Nat.mod_mod]
  rw [hhi, hlo']
  rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
  · rw [ite_eq_left h0, h0, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.div_one, Nat.add_zero,
      Nat.mul_assoc, Nat.mul_comm (2 ^ 32), ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide),
      Nat.mod_mul_mod]
  · rw [ite_eq_right (by lia)]
    obtain ⟨j, hj⟩ : ∃ j, k.toNat = j + 1 := ⟨k.toNat - 1, by lia⟩
    rw [hj, Nat.add_sub_cancel]
    exact shl_digit_succ _ _ _ hs

/--
The loop of `foldrInPlace` with `div2Step` on the limbs `F k x` of `X`, where `x` is the limb of the
slice at `k`: below index `k` the slice holds `Z`, untouched, above it the quotient `W` of
`⌊X / βᵏ⌋` by `V`, and the carry is the remainder.
-/
private theorem div2_loop (vt vs : UInt32) (V : Nat) (hV : vt.toNat * 2 ^ 32 + vs.toNat = V)
    (hvt : 0 < vt.toNat) (X n : Nat) (Z : List UInt32) (hZ : Z.length = n)
    (F : (k : USize) → k.toNat < n → UInt32 → UInt32)
    (hF : ∀ (k : Nat) (hk : k < n) (hk' : k.toUSize.toNat < n),
      (F k.toUSize hk' (Z[k]'(by lia))).toNat = X / 2 ^ (32 * k) % 2 ^ 32)
    (s : UInt32Array.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n)
    (r : UInt64) (W : List UInt32) (h0 : s.start = 0) (hl : s.array.toList = Z.take k ++ W)
    (hv : ofLimbs W * V + r.toNat = X / 2 ^ (32 * k)) (hr : r.toNat < V) :
    let p := UInt32Array.Slice.foldrInPlace.loop n (fun j hj x r => div2Step vt vs r (F j hj x)) s
      hs k hk r
    ofLimbs p.1.array.toList * V + p.2.toNat = X ∧ p.2.toNat < V := by
  induction k generalizing s r W with
  | zero =>
    simp only [UInt32Array.Slice.foldrInPlace.loop]
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at hv
    rw [hl, List.take_zero, List.nil_append]
    exact ⟨hv, hr⟩
  | succ k ih =>
    rw [UInt32Array.Slice.foldrInPlace.loop]
    have hkZ : k < Z.length := by lia
    have hsa : k < s.array.size := by
      have := s.stop_le_array_size; have := s.size_eq; have := s.start_le_stop; lia
    have hsk : s[k]'(by lia) = Z[k] := by
      have h := List.getElem_of_eq hl (i := k) (by simpa using hsa)
      rw [List.getElem_append_left (by simp; lia), List.getElem_take,
        UInt32Array.getElem_toList] at h
      rw [UInt32Array.Slice.getElem_eq]
      simpa [h0] using h
    have hk' : k.toUSize.toNat < n := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
    have hx : (F k.toUSize hk' (s[k]'(by lia))).toNat = X / 2 ^ (32 * k) % 2 ^ 32 := by
      rw [hsk]; exact hF k (by lia) hk'
    obtain ⟨h₁, h₂⟩ := div2Step_spec vt vs r (F k.toUSize hk' (s[k]'(by lia))) hvt
      (by rw [hV]; exact hr)
    rw [hV] at h₁ h₂
    refine ih _ _ _ _ ((div2Step vt vs r (F k.toUSize hk' (s[k]'(by lia)))).1 :: W) ?_ ?_ ?_ ?_
    · rw [UInt32Array.Slice.start_set, h0]
    · rw [UInt32Array.Slice.array_set, UInt32Array.toList_set, hl, h0, Nat.zero_add,
        List.take_succ_eq_append_getElem hkZ, List.append_assoc,
        List.set_append_right _ _ (by simp; lia)]
      simp [Nat.min_eq_left (Nat.le_of_lt hkZ)]
    · -- `q V + β W V + r' = r β + x + β W V = x + β (W V + r)`, digit `k` and the digits above.
      generalize F k.toUSize hk' (s[k]'(by lia)) = x at hx h₁ h₂ ⊢
      have hsplit : X / 2 ^ (32 * k) = x.toNat + 2 ^ 32 * (X / 2 ^ (32 * (k + 1))) := by
        rw [hx, show 32 * (k + 1) = 32 * k + 32 by lia, Nat.pow_add, ← Nat.div_div_eq_div_mul]
        have := Nat.div_add_mod (X / 2 ^ (32 * k)) (2 ^ 32)
        lia
      rw [ofLimbs_cons, hsplit, ← hv, h₁, h₂]
      have := Nat.div_add_mod (r.toNat * 2 ^ 32 + x.toNat) V
      generalize (r.toNat * 2 ^ 32 + x.toNat) / V = q at *
      generalize (r.toNat * 2 ^ 32 + x.toNat) % V = m at *
      grind
    · rw [h₂]; exact Nat.mod_lt _ (by lia)

/-- The quotient limbs of `x` by `vt β + vs` in place, from the top limb down, and the remainder
shifted right by `s`. -/
def divRem2Limbs (x : UInt32Array) (vt vs : UInt32) (s : UInt64) : UInt32Array × UInt64 :=
  x.toSlice.foldrInPlaceThen (0 : UInt64) (fun _ _ v R => div2Step vt vs R v)
    (fun r R => (r.array, R >>> s))

/--
The quotient limbs of `a 2ˢ` by `vt β + vs` in a new array, from the top limb down, reading the
limbs of `a 2ˢ` from `a` with `shlLimbU`, and the remainder shifted right by `s`.
-/
def divRem2Shl (a : UInt32Array.Slice) (has : a.array.size < USize.size) (vt vs : UInt32)
    (s : UInt64) : UInt32Array × UInt64 :=
  let arr := a.array
  let st := a.start.toUSize
  let n := a.size.toUSize
  (UInt32Array.replicate (a.size + 1) 0).toSlice.foldrInPlaceThen (0 : UInt64)
    (fun k _ _ R => div2Step vt vs R (shlLimbU arr st n has (limbU_bound a has) s k))
    (fun r R => (r.array, R >>> s))

/--
`a / d` as limbs, untrimmed, and `a % d` as a word, for `d = d₁ β + d₀` with `d₁ ≠ 0`, like GMP's
`mpn_divrem_2`. The loop reads the limbs of the normalized dividend from `a` (`divRem2Shl`); a
shifted copy (`divRem2Limbs`) is left for arrays too long for `USize` indices.
-/
public def divRem2 (a : UInt32Array.Slice) (d₁ d₀ : UInt32) : UInt32Array × UInt64 :=
  let s := 31 - d₁.toNat.log2
  let D : UInt64 := ((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< s.toUInt64
  if has : a.array.size < 4294967295 then
    divRem2Shl a (lt_usizeSize has) (D >>> 32).toUInt32 D.toUInt32 s.toUInt64
  else
    divRem2Limbs (shiftLeft a s) (D >>> 32).toUInt32 D.toUInt32 s.toUInt64

/--
`divRem2` without the remainder: the fold ends with the array alone, so that it allocates no pair
and no box for the remainder.
-/
public def div2 (a : UInt32Array.Slice) (d₁ d₀ : UInt32) : UInt32Array :=
  let s := 31 - d₁.toNat.log2
  let D : UInt64 := ((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< s.toUInt64
  if has : a.array.size < 4294967295 then
    let arr := a.array
    let st := a.start.toUSize
    let n := a.size.toUSize
    (UInt32Array.replicate (a.size + 1) 0).toSlice.foldrInPlaceThen (0 : UInt64)
      (fun k _ _ R => div2Step (D >>> 32).toUInt32 D.toUInt32 R
        (shlLimbU arr st n (lt_usizeSize has) (limbU_bound a (lt_usizeSize has)) s.toUInt64 k))
      (fun r _ => r.array)
  else
    (shiftLeft a s).toSlice.foldrInPlaceThen (0 : UInt64)
      (fun _ _ v R => div2Step (D >>> 32).toUInt32 D.toUInt32 R v) (fun r _ => r.array)

public theorem div2_eq (a : UInt32Array.Slice) (d₁ d₀ : UInt32) :
    div2 a d₁ d₀ = (divRem2 a d₁ d₀).1 := by
  unfold div2 divRem2
  split <;> simp only [divRem2Shl, divRem2Limbs, UInt32Array.Slice.foldrInPlaceThen_eq]

/-- `divRem2` divides: `a = q d + r` with `r < d`. -/
public theorem divRem2_spec (a : UInt32Array.Slice) (d₁ d₀ : UInt32) (hd : d₁ ≠ 0) :
    toNat (divRem2 a d₁ d₀).1 * (d₁.toNat * 2 ^ 32 + d₀.toNat) + (divRem2 a d₁ d₀).2.toNat =
        toNat a ∧
      (divRem2 a d₁ d₀).2.toNat < d₁.toNat * 2 ^ 32 + d₀.toNat := by
  simp only [divRem2, divRem2Shl, divRem2Limbs, UInt32Array.Slice.foldrInPlaceThen_eq,
    UInt32Array.Slice.foldrInPlace]
  have hd₁ : d₁.toNat ≠ 0 := fun h => hd (UInt32.toNat_inj.1 (by simpa using h))
  have hd₁β := d₁.toNat_lt
  have hd₀β := d₀.toNat_lt
  have hl : d₁.toNat.log2 < 32 := (Nat.log2_lt hd₁).2 hd₁β
  have hlt := Nat.lt_log2_self (n := d₁.toNat)
  generalize d₁.toNat.log2 = l at hl hlt
  -- `d 2^s < 2^(l + 1) β 2^(31 - l) = 2⁶⁴`.
  have hD64 : (d₁.toNat * 2 ^ 32 + d₀.toNat) * 2 ^ (31 - l) < 2 ^ 64 := by
    have h₁ : d₁.toNat * 2 ^ 32 + d₀.toNat < 2 ^ (l + 1) * 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ 32) (show d₁.toNat + 1 ≤ 2 ^ (l + 1) by lia)
      rw [Nat.succ_mul] at this
      lia
    have h₂ : 2 ^ (l + 1) * 2 ^ 32 * 2 ^ (31 - l) = 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
    rw [← h₂]
    exact Nat.mul_lt_mul_of_pos_right h₁ (Nat.two_pow_pos _)
  have hs64 : (31 - l).toUInt64.toNat = 31 - l := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by lia)
  have hd : ((d₁.toUInt64 <<< 32) + d₀.toUInt64).toNat = d₁.toNat * 2 ^ 32 + d₀.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    lia
  have hD : (((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< (31 - l).toUInt64).toNat =
      (d₁.toNat * 2 ^ 32 + d₀.toNat) * 2 ^ (31 - l) := by
    rw [UInt64.toNat_shiftLeft, hd, hs64, Nat.mod_eq_of_lt (show 31 - l < 64 by lia),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hD64]
  generalize ((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< (31 - l).toUInt64 = D at hD
  obtain ⟨d, hdd⟩ : ∃ d, d₁.toNat * 2 ^ 32 + d₀.toNat = d := ⟨_, rfl⟩
  rw [hdd] at hD hD64 ⊢
  have hdpos : 2 ^ 32 ≤ d := by
    rw [← hdd]
    exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by lia))
  -- `vt β + vs = D`, with `vt ≠ 0`.
  have hvt : ((D >>> 32).toUInt32).toNat = D.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have := D.toNat_lt
    exact Nat.mod_eq_of_lt (by lia)
  have hvs : (D.toUInt32).toNat = D.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
  have hV : ((D >>> 32).toUInt32).toNat * 2 ^ 32 + (D.toUInt32).toNat = D.toNat := by
    rw [hvt, hvs]; exact Nat.div_add_mod' _ _
  have hDge : 2 ^ 32 ≤ D.toNat := by
    rw [hD]; exact Nat.le_trans hdpos (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hvt0 : 0 < ((D >>> 32).toUInt32).toNat := by rw [hvt]; exact Nat.div_pos hDge (by decide)
  -- Both loops end with `Q (d 2ˢ) + R = a 2ˢ` and `R < d 2ˢ`, so `R = (a - Q d) 2ˢ`.
  have hP : 0 < 2 ^ (31 - l) := Nat.two_pow_pos _
  have hR (R : UInt64) : (R >>> (31 - l).toUInt64).toNat = R.toNat / 2 ^ (31 - l) := by
    rw [UInt64.toNat_shiftRight, hs64, Nat.mod_eq_of_lt (show 31 - l < 64 by lia),
      Nat.shiftRight_eq_div_pow]
  have hcore (q : UInt32Array) (R : UInt64)
      (h₁ : ofLimbs q.toList * (d * 2 ^ (31 - l)) + R.toNat = toNat a * 2 ^ (31 - l))
      (h₂ : R.toNat < d * 2 ^ (31 - l)) :
      ofLimbs q.toList * d + (R >>> (31 - l).toUInt64).toNat = toNat a ∧
        (R >>> (31 - l).toUInt64).toNat < d := by
    rw [hR]
    generalize ofLimbs q.toList = Q at h₁ ⊢
    generalize R.toNat = R at h₁ h₂ ⊢
    have hQd : Q * d ≤ toNat a := by
      have : Q * d * 2 ^ (31 - l) ≤ toNat a * 2 ^ (31 - l) := by
        rw [← h₁, Nat.mul_assoc]; lia
      exact Nat.le_of_mul_le_mul_right this hP
    have hRv : R = (toNat a - Q * d) * 2 ^ (31 - l) := by
      rw [Nat.sub_mul, ← h₁, Nat.mul_assoc]; lia
    rw [hRv, Nat.mul_div_cancel _ hP]
    refine ⟨by lia, ?_⟩
    have : (toNat a - Q * d) * 2 ^ (31 - l) < d * 2 ^ (31 - l) := by rw [← hRv]; exact h₂
    exact Nat.lt_of_mul_lt_mul_right this
  have hXlt : toNat a * 2 ^ (31 - l) < 2 ^ (32 * (a.size + 1)) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (Nat.pow_lt_pow_right (by decide) (by lia))
  rw [toNat_toSlice]
  by_cases has : a.array.size < 4294967295
  · -- Normalizing on the fly: the loop reads the limbs of `a 2ˢ` with `shlLimbU`.
    simp only [has, ↓reduceDIte]
    have hsz : a.size + 1 < USize.size := by
      have := USize.le_size; have := a.stop_le_array_size; have := a.size_eq; lia
    have hn : (UInt32Array.replicate (a.size + 1) 0).toSlice.size = a.size + 1 := by simp
    have h := div2_loop (D >>> 32).toUInt32 D.toUInt32 D.toNat hV hvt0 (toNat a * 2 ^ (31 - l))
      _ (List.replicate (a.size + 1) 0) (by rw [hn]; simp)
      (fun k _ _ => shlLimbU a.array a.start.toUSize a.size.toUSize (lt_usizeSize has)
        (limbU_bound a (lt_usizeSize has)) (31 - l).toUInt64 k)
      (fun k hk _ => by
        rw [toNat_shlLimbU a _ (31 - l) (by lia) k.toUSize, toNat_toUSize (by lia)])
      (UInt32Array.replicate (a.size + 1) 0).toSlice rfl _ (Nat.le_refl _) 0 [] (by simp)
      (by rw [List.take_of_length_le (by rw [hn]; simp)]; simp)
      (by rw [hn, Nat.div_eq_of_lt hXlt]; simp) (by simp; lia)
    simp only at h
    rw [hD] at h
    exact hcore _ _ h.1 h.2
  · -- The shifted copy.
    simp only [has, ↓reduceDIte]
    have hx := toNat_shiftLeft a (31 - l)
    rw [toNat_toSlice] at hx
    have h := div2_loop (D >>> 32).toUInt32 D.toUInt32 D.toNat hV hvt0 (toNat a * 2 ^ (31 - l))
      (shiftLeft a (31 - l)).toSlice.size (shiftLeft a (31 - l)).toList (by simp) (fun _ _ v => v)
      (fun k hk _ => by
        rw [← hx, ← toNat_getD_eq, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp at hk; simpa using hk)]
        rfl)
      (shiftLeft a (31 - l)).toSlice rfl _ (Nat.le_refl _) 0 [] (by simp)
      (by rw [List.take_of_length_le (by simp)]; simp)
      (by
        rw [Nat.div_eq_of_lt (by rw [← hx]; simpa using ofLimbs_lt (shiftLeft a (31 - l)).toList)]
        simp)
      (by simp; lia)
    simp only at h
    rw [hD] at h
    exact hcore _ _ h.1 h.2

/-- A number of two limbs is `s₀ + β s₁`. -/
public theorem toNat_of_size_eq_two {s : UInt32Array.Slice} (h : s.size = 2) :
    toNat s = (s.getD 0 0).toNat + 2 ^ 32 * (s.getD 1 0).toNat := by
  rw [toNat, ← List.take_of_length_le (l := s.copy.toList) (i := 2) (by simp [h]),
    ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD, getD_eq_getD_toList_copy,
    getD_eq_getD_toList_copy]
  simp

/-- The limbs of a word, trimmed. -/
public def ofWord64 (w : UInt64) : UInt32Array :=
  trim (((UInt32Array.emptyWithCapacity 2).push w.toUInt32).push (w >>> 32).toUInt32)

@[simp] public theorem toNat_ofWord64 (w : UInt64) : toNat (ofWord64 w) = w.toNat := by
  rw [ofWord64, toNat_trim, toNat_toSlice]
  simp only [UInt32Array.toList_push, UInt32Array.emptyWithCapacity_eq_empty,
    UInt32Array.toList_empty, List.nil_append, List.cons_append, ofLimbs_cons, ofLimbs_nil,
    UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  omega

public theorem isTrimmed_ofWord64 (w : UInt64) : isTrimmed (ofWord64 w) = true := isTrimmed_trim _

end Bignum
