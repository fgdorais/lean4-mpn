/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Basecase
public import MPN.Bits

/-!
# A word divided by two limbs

`div2Step vt vs R x` divides the remainder so far `R`, a word below `V = vt β + vs`, followed by
the limb `x`, by the normalized two-limb divisor `V`: `div2Est` estimates the quotient limb from
the top limbs and `div2Fix` decreases it while it is too large, which never happens but needs no
proof that it doesn't. `MPN.Nat`'s divisions of up to four limbs by a word use it
(`Nat.divRem128L`). In this experiment, the division of arrays by two limbs (`divRem2`) is gone:
those divisors take `main`'s schoolbook division.
-/

open ScalarArray

namespace MPN

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
    simp; lia)]
  have : q.toNat ≠ 0 := fun h => ‹q ≠ 0 ∧ _›.1 (UInt32.toNat_inj.1 (by simpa using h))
  simp; lia

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
      Nat.mul_le_mul (by lia) (by lia)
    have hle₂ : q.toNat * vs.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
    have hph : (q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32)).toNat =
        q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hqv, UInt64.toNat_shiftRight, hav]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by lia)
    have ha₀ : ((q.toUInt64 * vs.toUInt64).toUInt32).toNat = q.toNat * vs.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hav]
    -- `q V = ph β + a₀`, and the condition says `W < q V`.
    have hP : q.toNat * V = (q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32) * 2 ^ 32 +
        q.toNat * vs.toNat % 2 ^ 32 := by
      have := Nat.div_add_mod (q.toNat * vs.toNat) (2 ^ 32)
      rw [hV, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc]
      lia
    have hlt : W < q.toNat * V := by
      have h2 := hc.2
      simp only [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, hph, ha₀] at h2
      rcases h2 with h2 | ⟨h2, h3⟩
      · rw [hP, hW]; lia
      · have hR' : R.toNat = q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
          rw [h2, hph]
        rw [hP, hW, hR']; lia
    have hdiv : W / V < q.toNat := (Nat.div_lt_iff_lt_mul hVpos).2 (by
      rw [Nat.mul_comm] at hlt; first | exact hlt | (rw [Nat.mul_comm]; exact hlt))
    apply ih
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; lia)]
    simp only [UInt32.reduceToNat]
    lia
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
      Nat.mul_le_mul (by lia) (by lia)
    have hle₂ : q.toNat * vs.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
    have hph : (q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32)).toNat =
        q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hqv, UInt64.toNat_shiftRight, hav]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by lia)
    have ha₀ : ((q.toUInt64 * vs.toUInt64).toUInt32).toNat = q.toNat * vs.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hav]
    have hP : q.toNat * V = (q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32) * 2 ^ 32 +
        q.toNat * vs.toNat % 2 ^ 32 := by
      have := Nat.div_add_mod (q.toNat * vs.toNat) (2 ^ 32)
      rw [hV, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc]
      lia
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
          lia
        · lia
    have hqq : q.toNat = W / V :=
      Nat.le_antisymm ((Nat.le_div_iff_mul_le hVpos).2 hge) hq
    refine ⟨hqq, ?_⟩
    -- The remainder `W - q V` is below `V < 2⁶⁴`, so the word arithmetic doesn't wrap.
    have hmod : W % V = W - q.toNat * V := by
      rw [hqq, Nat.mod_eq_sub_mul_div, Nat.mul_comm]
    have hrem := Nat.mod_lt W hVpos
    have hV64 : V ≤ 2 ^ 64 := by rw [hV]; lia
    have hRph : PH ≤ R.toNat := by rw [hP, hW] at hge; lia
    rw [hmod]
    rw [hmod, hP, hW] at hrem
    rw [hP, hW]
    rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_shiftLeft,
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hph]; exact hRph), hph,
      UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, ha₀]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    lia

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
      · have := Nat.div_le_div_right (c := 2 ^ 32) h''; simp at this; lia
    lia
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
    lia

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
    exact Nat.mod_eq_of_lt (by lia)
  have hwn : (R.toUInt32).toNat = R.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
  have hRsplit : R.toNat / 2 ^ 32 * 2 ^ 32 + R.toNat % 2 ^ 32 = R.toNat := by
    have := Nat.div_add_mod R.toNat (2 ^ 32); lia
  obtain ⟨V, hVdef⟩ : ∃ V, vt.toNat * 2 ^ 32 + vs.toNat = V := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, R.toNat * 2 ^ 32 + x.toNat = W := ⟨_, rfl⟩
  rw [hVdef] at hR ⊢
  rw [hW]
  have hVpos : 0 < V := by lia
  -- The quotient `Q` is at most both estimates.
  have hQV : W / V * V ≤ W := Nat.div_mul_le_self W V
  have hQβ : W / V < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hVpos]
    have := Nat.mul_le_mul_right (2 ^ 32) (show R.toNat + 1 ≤ V by lia)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm (2 ^ 32) V]
    lia
  have hQ₀ : W / V * vt.toNat ≤ R.toNat := by
    -- `Q vt β ≤ Q V ≤ W < (R + 1) β`.
    have h₁ : W / V * vt.toNat * 2 ^ 32 ≤ W / V * V := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by lia)
    have h₂ : W / V * vt.toNat * 2 ^ 32 < (R.toNat + 1) * 2 ^ 32 := by
      rw [Nat.succ_mul]; lia
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h₂)
  have hest := toNat_div2Est R vt
  have hle : (div2Est R vt).toNat * vt.toNat ≤
      ((R >>> 32).toUInt32).toNat * 2 ^ 32 + (R.toUInt32).toNat := by
    rw [hwt, hwn, hRsplit, hest]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) (Nat.div_mul_le_self _ _)
  have h₀ : W / V ≤ (div2Est R vt).toNat := by
    rw [hest]
    exact Nat.le_min.2 ⟨(Nat.le_div_iff_mul_le hvt).2 hQ₀, by lia⟩
  have h₁ : W / V * (vt.toNat * 2 ^ 32 + vs.toNat) ≤
      (((R >>> 32).toUInt32).toNat * 2 ^ 32 + (R.toUInt32).toNat) * 2 ^ 32 + x.toNat := by
    rw [hwt, hwn, hRsplit, hW, hVdef]
    exact hQV
  have hq := qEstimate3_ge _ _ _ x vt vs (W / V) hle h₀ h₁
  exact div2Fix_spec vt vs R x _ V W hVdef.symm hW.symm hVpos hq

end MPN
