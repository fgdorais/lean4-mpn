/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Limb
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2

/-!
# Schoolbook division

`divRem` divides by a divisor `v` of `n ≥ 2` limbs by Knuth's Algorithm D, like GMP's schoolbook
division, one quotient limb per step from the top down. At the step for window `i`, the
remainder `R` so far is below `v βⁱ⁺¹`, so the quotient limb is `⌊W / v⌋ < β`, where `W` is the
window of limbs `i` to `i + n` of `R`.

The limb is estimated by `qEst` from the top three limbs of `W` and the top two of `v`, as in
Algorithm D. The step subtracts the estimate times `v` from the window in place, and adds `v` back
while the window is negative (`addBack`). Correctness only needs the estimate never to be too
small, which `qEst_ge` proves; that it is rarely too large, when the top limb of `v` is at least
`β / 2`, is only a matter of speed, and `divRem` normalizes the divisor for it.

The division works in one array, like GMP's and `main`'s (`divLoopIn`): after the step for window
`i`, its remainder is below `v`, so the top limb `i + n` of the window is free, and the step writes
the quotient limb there (`divStepIn`). The multiply-subtract pass is the in-place fold of
`subMul1`, ended by a continuation, so that a step allocates nothing unless the estimate was too
large. At the end the limbs below `n` are the remainder and the limbs from `n` on the quotient.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## The estimate of a quotient limb -/

/--
Whether `q v₂ > r β + w₀` for the word `r`, where `h β + l = q v₂`: a comparison of double words.
-/
@[inline, expose] public def gt2 (h l r w₀ : UInt64) : Bool := r < h || (h == r && w₀ < l)

private theorem gt2_iff (h l r w₀ : UInt64) :
    gt2 h l r w₀ = true ↔ r.toNat * 2 ^ 64 + w₀.toNat < h.toNat * 2 ^ 64 + l.toNat := by
  have := l.toNat_lt; have := w₀.toNat_lt
  simp only [gt2, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  constructor
  · rintro (h₁ | ⟨h₁, h₂⟩)
    · have := Nat.mul_le_mul_right (2 ^ 64) (show r.toNat + 1 ≤ h.toNat from h₁); lia
    · rw [h₁]; lia
  · intro h'
    rcases Nat.lt_trichotomy r.toNat h.toNat with h₁ | h₁ | h₁
    · exact .inl h₁
    · exact .inr ⟨h₁.symm, by rw [h₁] at h'; lia⟩
    · have := Nat.mul_le_mul_right (2 ^ 64) (show h.toNat + 1 ≤ r.toNat from h₁); lia

/--
The estimate of the quotient limb of `w₂ β² + w₁ β + w₀` by `v₁ β + v₂`, from the quotient `q` of
`w₂ β + w₁` by `v₁`, decreased at most twice while `q (v₁ β + v₂)` exceeds the dividend, as in
Algorithm D; `β - 1` when `w₂ ≥ v₁`.
-/
public def qEst (w₂ w₁ w₀ v₁ v₂ : UInt64) : UInt64 :=
  if w₂ < v₁ then
    let q := UInt64.div2 w₂ w₁ v₁
    let r := w₁ - q * v₁
    if gt2 (UInt64.mulh q v₂) (q * v₂) r w₀ then
      let q := q - 1
      let r := r + v₁
      -- `r < v₁` when `r + v₁` overflows, and then `q v₂ < r β`.
      if r < v₁ then q
      else if gt2 (UInt64.mulh q v₂) (q * v₂) r w₀ then q - 1 else q
    else q
  else 0xFFFFFFFFFFFFFFFF

/-- The low and high words of `q v₂`. -/
private theorem mul_words (q v₂ : UInt64) :
    (UInt64.mulh q v₂).toNat * 2 ^ 64 + (q * v₂).toNat = q.toNat * v₂.toNat := by
  rw [UInt64.toNat_mulh, UInt64.toNat_mul]
  have := Nat.div_add_mod (q.toNat * v₂.toNat) (2 ^ 64)
  lia

/-- One correction: when `q (v₁ β + v₂)` exceeds the dividend, every `Q` below it is below `q`. -/
private theorem qEst_dec {Q q r v₁ v₂ W₂ w₀ : Nat}
    (hW : v₁ * q + r = W₂) (hQ : Q * (v₁ * 2 ^ 64 + v₂) ≤ W₂ * 2 ^ 64 + w₀)
    (hgt : r * 2 ^ 64 + w₀ < q * v₂) : Q < q := by
  refine Nat.lt_of_not_le fun hle => ?_
  have := Nat.mul_le_mul_right (v₁ * 2 ^ 64 + v₂) hle
  rw [← hW] at hQ
  have e : q * (v₁ * 2 ^ 64 + v₂) = (v₁ * q) * 2 ^ 64 + q * v₂ := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm q v₁]
  rw [Nat.add_mul] at hQ
  lia

/-- The quotient of the top two limbs by `v₁` is never too small. -/
private theorem qEst_top {Q q r v₁ v₂ W₂ w₀ : Nat} (hW : v₁ * q + r = W₂) (hr : r < v₁)
    (hw₀ : w₀ < 2 ^ 64) (hQ : Q * (v₁ * 2 ^ 64 + v₂) ≤ W₂ * 2 ^ 64 + w₀) : Q ≤ q := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have h₁ := Nat.mul_le_mul_right (v₁ * 2 ^ 64 + v₂) (show q + 1 ≤ Q from hlt)
  have h₂ := Nat.mul_le_mul_right (2 ^ 64) (show r + 1 ≤ v₁ from hr)
  rw [← hW] at hQ
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm q v₁] at h₁
  rw [Nat.add_mul, Nat.one_mul] at h₂
  rw [Nat.add_mul] at hQ
  have := Nat.zero_le (q * v₂)
  lia

/--
The estimate is never too small: every `Q < β` with `Q (v₁ β + v₂) ≤ w₂ β² + w₁ β + w₀` is at most
`qEst w₂ w₁ w₀ v₁ v₂`.
-/
public theorem qEst_ge (w₂ w₁ w₀ v₁ v₂ : UInt64) (Q : Nat) (hQβ : Q < 2 ^ 64)
    (hQ : Q * (v₁.toNat * 2 ^ 64 + v₂.toNat) ≤
      (w₂.toNat * 2 ^ 64 + w₁.toNat) * 2 ^ 64 + w₀.toNat) :
    Q ≤ (qEst w₂ w₁ w₀ v₁ v₂).toNat := by
  rw [qEst]
  split
  · rename_i hw
    have hw' := UInt64.lt_iff_toNat_lt.1 hw
    obtain ⟨hrem, hdq⟩ := UInt64.toNat_div2_rem w₂ w₁ v₁ hw'
    have hr := Nat.mod_lt (w₂.toNat * 2 ^ 64 + w₁.toNat) (show 0 < v₁.toNat by lia)
    rw [← hrem] at hr
    dsimp only
    generalize hq : UInt64.div2 w₂ w₁ v₁ = q at hdq hr ⊢
    generalize hrr : w₁ - q * v₁ = r at hdq hr ⊢
    split
    · rename_i hg
      rw [gt2_iff, mul_words] at hg
      have h₁ := qEst_dec hdq hQ hg
      have hq₁ : (q - 1).toNat = q.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia))]; rfl
      -- `r + v₁` as a word, and whether it overflows.
      have hv := v₁.toNat_lt
      have hrv : (r + v₁).toNat = (r.toNat + v₁.toNat) % 2 ^ 64 := UInt64.toNat_add ..
      split
      · rw [hq₁]; lia
      · rename_i hno
        have hno' : r.toNat + v₁.toNat < 2 ^ 64 := by
          rw [UInt64.lt_iff_toNat_lt, hrv] at hno
          have hr64 := r.toNat_lt
          generalize 2 ^ 64 = M at *
          refine Nat.lt_of_not_le fun hge => hno ?_
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by lia)]
          lia
        rw [Nat.mod_eq_of_lt hno'] at hrv
        split
        · rename_i hg₂
          rw [gt2_iff, mul_words, hrv, hq₁] at hg₂
          have hdq' : v₁.toNat * (q.toNat - 1) + (r.toNat + v₁.toNat) =
              w₂.toNat * 2 ^ 64 + w₁.toNat := by
            rw [Nat.mul_sub, Nat.mul_one]
            have : v₁.toNat ≤ v₁.toNat * q.toNat := Nat.le_mul_of_pos_right _ (by lia)
            lia
          have h₂ := qEst_dec hdq' hQ hg₂
          have hq₂ : (q - 1 - 1).toNat = q.toNat - 1 - 1 := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia)), hq₁]; rfl
          rw [hq₂]; lia
        · rw [hq₁]; lia
    · exact qEst_top hdq hr w₀.toNat_lt hQ
  · simp only [UInt64.reduceToNat]; lia

/-! ## One step -/

/-- The window of `k` limbs of `w` from limb `i`. -/
private theorem win_spec (w : UInt64Array) (i k : USize) (h : i.toNat + k.toNat ≤ w.size)
    (hU : i.toNat + k.toNat < USize.size) :
    (w.uslice i (i + k)).array = w ∧ (w.uslice i (i + k)).start.toNat = i.toNat ∧
      (w.uslice i (i + k)).size.toNat = k.toNat := by
  have hik : (i + k).toNat = i.toNat + k.toNat := USize.toNat_add_of_lt hU
  have hst := uslice_start w i (i + k) (USize.le_iff_toNat_le.2 (by lia)) (by lia)
  have hsp := uslice_stop w i (i + k) (by lia)
  refine ⟨rfl, by rw [hst], ?_⟩
  rw [USlice.toNat_size, hst, hsp]
  lia

/--
Adds `v` back to the window of `k` limbs of `w` from limb `i`, decreasing `q`, while the borrow `b`
out of the window is not zero.
-/
public def addBack (w : UInt64Array) (v : USlice) (i k : USize) (q b : UInt64) :
    UInt64Array × UInt64 :=
  if _h : b ≠ 0 ∧ q ≠ 0 then
    let p := addInto (w.uslice i (i + k)) v 0
    addBack p.1 v i k (q - 1) (b - p.2)
  else (w, q)
termination_by q.toNat
decreasing_by
  have : q.toNat ≠ 0 := fun e => _h.2 (UInt64.toNat_inj.1 (by rw [e]; rfl))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia))]
  simp
  lia

private theorem addBack_spec (w : UInt64Array) (v : USlice) (i k : USize) (q b : UInt64)
    (hk : i.toNat + k.toNat ≤ w.size) (hU : i.toNat + k.toNat < USize.size)
    (hv : v.size ≤ k) (hv₀ : 0 < v.toNat) (W : Nat) (hW : W < 2 ^ (64 * k.toNat))
    (hq : W / v.toNat ≤ q.toNat)
    (hS : w.valAt i.toNat k.toNat + v.toNat * q.toNat = W + 2 ^ (64 * k.toNat) * b.toNat) :
    (addBack w v i k q b).1.size = w.size ∧
      (∀ j, (j < i.toNat ∨ i.toNat + k.toNat ≤ j) → (addBack w v i k q b).1[j]! = w[j]!) ∧
      (addBack w v i k q b).1.valAt i.toNat k.toNat = W % v.toNat ∧
      (addBack w v i k q b).2.toNat = W / v.toNat := by
  induction w, q, b using addBack.induct v i k with
  | case1 w q b h p ih =>
    rw [addBack, dite_eq_left_of_eq_true (eq_true h)]
    obtain ⟨ha, hs, hz⟩ := win_spec w i k hk hU
    have hc : p.1.valAt i.toNat k.toNat + 2 ^ (64 * k.toNat) * p.2.toNat =
        w.valAt i.toNat k.toNat + v.toNat := by
      have := valAt_addInto (w.uslice i (i + k)) v 0 (by
        rw [USize.le_iff_toNat_le, ← USize.le_iff_toNat_le]
        exact USize.le_trans hv (USize.le_iff_toNat_le.2 (by rw [hz]; exact Nat.le_refl _)))
      rw [ha, hs, hz, UInt64.toNat_zero, Nat.add_zero] at this
      exact this
    have hsz : p.1.size = w.size := by simp [p, ha]
    have hun : ∀ j, (j < i.toNat ∨ i.toNat + k.toNat ≤ j) → p.1[j]! = w[j]! := fun j hj =>
      getElem!_addInto _ _ _ _ (by rw [hs, hz]; exact hj)
    have hS' := valAt_lt w i.toNat k.toNat
    have hS'' := valAt_lt p.1 i.toNat k.toNat
    have hq₀ : q.toNat ≠ 0 := fun e => h.2 (UInt64.toNat_inj.1 (by rw [e]; rfl))
    have hb₀ : b.toNat ≠ 0 := fun e => h.1 (UInt64.toNat_inj.1 (by rw [e]; rfl))
    generalize 2 ^ (64 * k.toNat) = P at *
    -- `v q > W` while the borrow is not zero, so `q` stays above the quotient.
    have hvq : W < v.toNat * q.toNat := by
      have := Nat.mul_le_mul_left P (show 1 ≤ b.toNat by lia)
      lia
    have hq' : W / v.toNat ≤ q.toNat - 1 := by
      have := (Nat.div_lt_iff_lt_mul hv₀).2 (by rw [Nat.mul_comm]; exact hvq)
      lia
    -- The carry is at most the borrow, since the window stays a natural number.
    have hcb : p.2.toNat ≤ b.toNat := by
      refine Nat.le_of_not_lt fun hlt => ?_
      have := Nat.mul_le_mul_left P (show b.toNat + 1 ≤ p.2.toNat from hlt)
      have : v.toNat ≤ v.toNat * q.toNat := Nat.le_mul_of_pos_right _ (by lia)
      lia
    have hsub : (b - p.2).toNat = b.toNat - p.2.toNat := UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.2 hcb)
    have hq1 : (q - 1).toNat = q.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia))
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih (by rw [hsz]; exact hk) (by rw [hq1]; exact hq') (by
      rw [hq1, hsub]
      have := Nat.mul_le_mul_left P hcb
      have e₁ : v.toNat * (q.toNat - 1) = v.toNat * q.toNat - v.toNat := by
        rw [Nat.mul_sub, Nat.mul_one]
      have e₂ : P * (b.toNat - p.2.toNat) = P * b.toNat - P * p.2.toNat := Nat.mul_sub ..
      have := Nat.le_mul_of_pos_right v.toNat (show 0 < q.toNat by lia)
      rw [e₁, e₂]
      generalize v.toNat * q.toNat = VQ at *
      generalize P * b.toNat = PB at *
      generalize P * p.2.toNat = PC at *
      lia)
    exact ⟨i₁.trans hsz, fun j hj => (i₂ j hj).trans (hun j hj), i₃, i₄⟩
  | case2 w q b h =>
    rw [addBack, dite_eq_right_of_eq_false (eq_false h)]
    have hS' := valAt_lt w i.toNat k.toNat
    generalize 2 ^ (64 * k.toNat) = P at *
    have hb : b.toNat = 0 := by
      by_cases hb : b = 0
      · rw [hb]; rfl
      · have hq0 : q = 0 := Classical.byContradiction fun hq0 => h ⟨hb, hq0⟩
        rw [hq0, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at hS
        rcases Nat.eq_zero_or_pos b.toNat with h0 | h0
        · exact h0
        · have := Nat.mul_le_mul_left P (show 1 ≤ b.toNat from h0); lia
    rw [hb, Nat.mul_zero, Nat.add_zero] at hS
    have hle : q.toNat ≤ W / v.toNat := (Nat.le_div_iff_mul_le hv₀).2 (by
      rw [Nat.mul_comm]; lia)
    have hqe : q.toNat = W / v.toNat := Nat.le_antisymm hle hq
    refine ⟨rfl, fun _ _ => rfl, ?_, hqe⟩
    have := Nat.div_add_mod W v.toNat
    rw [← hqe] at this
    lia

/-- The top limbs bound the quotient: `Q V ≤ W` gives `Q V₂ ≤ W₃` for the top parts above `P`. -/
private theorem est_bound {Q V W Vlo Wlo V₂ W₃ P : Nat} (hV : V = Vlo + P * V₂)
    (hW : W = Wlo + P * W₃) (hWlo : Wlo < P) (hQ : Q * V ≤ W) : Q * V₂ ≤ W₃ := by
  have h₁ : P * (Q * V₂) ≤ Q * V := by
    rw [hV, Nat.mul_add, Nat.mul_left_comm]; exact Nat.le_add_left _ _
  have h₂ : P * (Q * V₂) < P * (W₃ + 1) := by rw [Nat.mul_add, Nat.mul_one]; lia
  have := Nat.lt_of_mul_lt_mul_left h₂
  lia

/-- Three limbs from `lo`. -/
private theorem valAt_three (a : UInt64Array) (lo : Nat) :
    a.valAt lo 3 = (a[lo + 2]!.toNat * 2 ^ 64 + a[lo + 1]!.toNat) * 2 ^ 64 + a[lo]!.toNat := by
  simp only [valAt_succ, valAt_zero, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
  lia

/-- Two limbs from `lo`. -/
private theorem valAt_two (a : UInt64Array) (lo : Nat) :
    a.valAt lo 2 = a[lo + 1]!.toNat * 2 ^ 64 + a[lo]!.toNat := by
  simp only [valAt_succ, valAt_zero, Nat.mul_zero, Nat.add_zero]
  lia

/-! ## One step -/

/--
One step of the division, without allocating: subtracts `q v`, for the estimate `q`, from limbs
`i` to `i + n - 1` of `w` by the in-place fold, and when the borrow out equals the top limb
`i + n` of the window, which is then the common case of an exact estimate, writes `q` there.
Otherwise the window went negative and `addBack` corrects it. Afterwards limbs `i` to `i + n - 1`
hold the remainder of the window by `v` and limb `i + n` the quotient limb.
-/
public def divStepIn (w : UInt64Array) (v : USlice) (v₁ v₂ : UInt64) (i n : USize) :
    UInt64Array :=
  if h : i.toNat + n.toNat + 1 ≤ w.size ∧ i.toNat + n.toNat + 1 < USize.size ∧ n ≤ v.size then
    let t := i.toNat + n.toNat
    let q := qEst w[t]! w[t - 1]! w[t - 2]! v₁ v₂
    foldUInPlaceThen n (subMul1Step v n h.2.2 q) w i ⟨by lia, by lia⟩ 0 0 fun w' _ b =>
      let top := w'[t]!
      if b = top then w'.set! t q
      else
        let p := addBack (w'.set! t (top - b)) v i (n + 1) q 1
        p.1.set! t p.2
  else w

set_option maxHeartbeats 1000000 in
private theorem divStepIn_spec (w : UInt64Array) (v : USlice) (v₁ v₂ : UInt64) (i n : USize)
    (hn : v.size = n) (hn₂ : 2 ≤ n.toNat) (hk : i.toNat + n.toNat + 1 ≤ w.size)
    (hU : w.size < USize.size) (hv₀ : 0 < v.toNat)
    (hv₁ : v₁ = v.array[v.start.toNat + n.toNat - 1]!)
    (hv₂ : v₂ = v.array[v.start.toNat + n.toNat - 2]!)
    (hW : w.valAt i.toNat (n.toNat + 1) < v.toNat * 2 ^ 64) :
    (divStepIn w v v₁ v₂ i n).size = w.size ∧
      (∀ j, (j < i.toNat ∨ i.toNat + n.toNat + 1 ≤ j) → (divStepIn w v v₁ v₂ i n)[j]! = w[j]!) ∧
      (divStepIn w v v₁ v₂ i n).valAt i.toNat n.toNat =
        w.valAt i.toNat (n.toNat + 1) % v.toNat ∧
      (divStepIn w v v₁ v₂ i n)[i.toNat + n.toNat]!.toNat =
        w.valAt i.toNat (n.toNat + 1) / v.toNat := by
  have hn1 : (n + 1).toNat = n.toNat + 1 :=
    (USize.toNat_add_of_lt (a := n) (b := 1) (by rw [USize.toNat_one]; lia)).trans
      (by rw [USize.toNat_one])
  have hnv : n ≤ v.size := by rw [hn]; exact USize.le_refl _
  have hvlt : v.toNat < 2 ^ (64 * n.toNat) := by
    rw [USlice.toNat_eq_valAt, hn]; exact valAt_lt ..
  rw [divStepIn, dite_eq_left_of_eq_true (eq_true ⟨hk, by lia, hnv⟩)]
  dsimp only
  generalize hWv : w.valAt i.toNat (n.toNat + 1) = W at hW ⊢
  -- The estimate is never too small.
  have hQβ : W / v.toNat < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hv₀).2 (by rw [Nat.mul_comm]; exact hW)
  have hvn : v.toNat = v.array.valAt v.start.toNat (n.toNat - 2) +
      2 ^ (64 * (n.toNat - 2)) * (v₁.toNat * 2 ^ 64 + v₂.toNat) := by
    rw [USlice.toNat_eq_valAt, hn, show n.toNat = n.toNat - 2 + 2 by lia, UInt64Array.valAt_add,
      valAt_two, show v.start.toNat + (n.toNat - 2) + 1 = v.start.toNat + (n.toNat - 2 + 2) - 1 by
        lia, show v.start.toNat + (n.toNat - 2) = v.start.toNat + (n.toNat - 2 + 2) - 2 by lia,
      ← show n.toNat = n.toNat - 2 + 2 by lia, ← hv₁, ← hv₂]
  have hwn : W = w.valAt i.toNat (n.toNat - 2) + 2 ^ (64 * (n.toNat - 2)) *
      ((w[i.toNat + n.toNat]!.toNat * 2 ^ 64 + w[i.toNat + n.toNat - 1]!.toNat) * 2 ^ 64 +
        w[i.toNat + n.toNat - 2]!.toNat) := by
    rw [← hWv, show n.toNat + 1 = n.toNat - 2 + 3 by lia, UInt64Array.valAt_add, valAt_three,
      show i.toNat + (n.toNat - 2) + 2 = i.toNat + n.toNat by lia,
      show i.toNat + (n.toNat - 2) + 1 = i.toNat + n.toNat - 1 by lia,
      show i.toNat + (n.toNat - 2) = i.toNat + n.toNat - 2 by lia]
  have hge := qEst_ge w[i.toNat + n.toNat]! w[i.toNat + n.toNat - 1]! w[i.toNat + n.toNat - 2]!
    v₁ v₂ (W / v.toNat) hQβ (est_bound hvn hwn (valAt_lt ..) (Nat.div_mul_le_self W v.toNat))
  generalize qEst w[i.toNat + n.toNat]! w[i.toNat + n.toNat - 1]! w[i.toNat + n.toNat - 2]!
    v₁ v₂ = q at hge ⊢
  -- The product subtracted from the low `n` limbs of the window.
  have hr : LoopBound w i n := ⟨by lia, by lia⟩
  have hF := subMul1Loop_eq_fold w i v n hnv hr q 0 0
  obtain ⟨f₁, f₂, f₃⟩ := subMul1Loop_spec w i v n hnv hr q 0 0
  rw [hF] at f₁ f₂ f₃
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero] at f₂ f₃
  have hvv : v.array.valAt v.start.toNat n.toNat = v.toNat := by rw [USlice.toNat_eq_valAt, hn]
  rw [hvv] at f₃
  rw [foldUInPlaceThen_eq]
  generalize foldUInPlace n (subMul1Step v n hnv q) w i hr 0 0 = F at f₁ f₂ f₃ ⊢
  have htop : F.1[i.toNat + n.toNat]! = w[i.toNat + n.toNat]! := f₂ _ (.inr (Nat.le_refl _))
  have hWs : W = w.valAt i.toNat n.toNat + 2 ^ (64 * n.toNat) * w[i.toNat + n.toNat]!.toNat := by
    rw [← hWv, UInt64Array.valAt_add, valAt_one]
  have hlow := valAt_lt F.1 i.toNat n.toNat
  -- `q ≥ W / v` bounds the remainder: `W - q v < v` when it is not negative.
  have hdm := Nat.div_add_mod W v.toNat
  have hmod := Nat.mod_lt W hv₀
  have hqv : v.toNat * (W / v.toNat) ≤ v.toNat * q.toNat := Nat.mul_le_mul_left _ hge
  have hti : i.toNat + n.toNat < F.1.size := by rw [f₁]; lia
  split
  · rename_i hb
    -- The estimate was exact: the window is `W - q v`, which is the remainder.
    rw [hb, htop] at f₃
    have hle : q.toNat * v.toNat ≤ W := by rw [hWs]; lia
    have hq : q.toNat = W / v.toNat := Nat.le_antisymm ((Nat.le_div_iff_mul_le hv₀).2 hle) hge
    refine ⟨by rw [size_set!, f₁], fun j hj => ?_, ?_, ?_⟩
    · rw [getElem!_set!_of_ne _ _ (by lia), f₂ j (by lia)]
    · rw [valAt_congr (b := F.1) _ fun j _ hj => getElem!_set!_of_ne _ _ (by lia)]
      rw [hq] at f₃
      rw [Nat.mul_comm] at hdm
      lia
    · rw [getElem!_set!_self _ _ _ hti, hq]
  · rename_i hb
    -- The window went negative: the borrow exceeds the top limb.
    have hbt : w[i.toNat + n.toNat]!.toNat < F.2.toNat := by
      rw [← htop]
      rcases Nat.lt_or_ge F.1[i.toNat + n.toNat]!.toNat F.2.toNat with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_ge F.2.toNat F.1[i.toNat + n.toNat]!.toNat with h' | h'
        · rw [htop] at h'
          have := Nat.mul_le_mul_left (2 ^ (64 * n.toNat))
            (show F.2.toNat + 1 ≤ w[i.toNat + n.toNat]!.toNat from h')
          rw [Nat.mul_add, Nat.mul_one] at this
          lia
        · exact hb (UInt64.toNat_inj.1 (by lia))
    have hsub : (F.1[i.toNat + n.toNat]! - F.2).toNat =
        w[i.toNat + n.toNat]!.toNat + 2 ^ 64 - F.2.toNat := by
      rw [htop, UInt64.toNat_sub]
      have := F.2.toNat_lt
      lia
    have hS : (F.1.set! (i.toNat + n.toNat) (F.1[i.toNat + n.toNat]! - F.2)).valAt i.toNat
        (n.toNat + 1) + v.toNat * q.toNat = W + 2 ^ (64 * (n.toNat + 1)) * (1 : UInt64).toNat := by
      rw [UInt64Array.valAt_add, valAt_one, getElem!_set!_self _ _ _ hti, hsub,
        valAt_congr (b := F.1) _ fun j _ hj => getElem!_set!_of_ne _ _ (by lia), hWs,
        show 64 * (n.toNat + 1) = 64 * n.toNat + 64 by lia, Nat.pow_add, UInt64.toNat_one]
      have := Nat.mul_le_mul_left (2 ^ (64 * n.toNat)) (Nat.le_of_lt hbt)
      rw [Nat.mul_sub, Nat.mul_add]
      have := F.2.toNat_lt
      have := Nat.mul_le_mul_left (2 ^ (64 * n.toNat)) (Nat.le_of_lt this)
      lia
    obtain ⟨a₁, a₂, a₃, a₄⟩ := addBack_spec (F.1.set! (i.toNat + n.toNat)
      (F.1[i.toNat + n.toNat]! - F.2)) v i (n + 1) q 1 (by rw [size_set!, f₁, hn1]; lia)
      (by rw [hn1]; lia) (USize.le_iff_toNat_le.2 (by rw [hn, hn1]; lia)) hv₀ W
      (by rw [hn1, ← hWv]; exact valAt_lt ..) hge (by rw [hn1]; exact hS)
    rw [hn1] at a₂ a₃
    rw [size_set!] at a₁
    have hti' : i.toNat + n.toNat < (addBack (F.1.set! (i.toNat + n.toNat)
        (F.1[i.toNat + n.toNat]! - F.2)) v i (n + 1) q 1).1.size := by rw [a₁, f₁]; lia
    refine ⟨by rw [size_set!, a₁, f₁], fun j hj => ?_, ?_, ?_⟩
    · rw [getElem!_set!_of_ne _ _ (by lia), a₂ j hj, getElem!_set!_of_ne _ _ (by lia),
        f₂ j (by lia)]
    · rw [valAt_congr (b := (addBack (F.1.set! (i.toNat + n.toNat)
        (F.1[i.toNat + n.toNat]! - F.2)) v i (n + 1) q 1).1) _
        fun j _ hj => getElem!_set!_of_ne _ _ (by lia), valAt_mod _ _ (Nat.le_succ n.toNat), a₃,
        Nat.mod_eq_of_lt (by lia)]
    · rw [getElem!_set!_self _ _ _ hti', a₄]


/--
Divides limbs `0` to `i + n - 1` of `w` by `v` of `n` limbs, with the top limbs `v₁` and `v₂`,
from window `i - 1` down to window `0`, in place: the quotient limb of window `j` goes to limb
`j + n`, so that the quotient ends in limbs `n` to `n + i - 1` and the remainder in limbs `0` to
`n - 1`.
-/
public def divLoopIn (w : UInt64Array) (v : USlice) (v₁ v₂ : UInt64) (n i : USize) : UInt64Array :=
  if hi : i = 0 then w
  else divLoopIn (divStepIn w v v₁ v₂ (i - 1) n) v v₁ v₂ n (i - 1)
termination_by i.toNat
decreasing_by
  have := toNat_pred hi
  have : i.toNat ≠ 0 := fun e => hi (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

private theorem divLoopIn_spec (w : UInt64Array) (v : USlice) (v₁ v₂ : UInt64) (n i : USize)
    (hn : v.size = n) (hn₂ : 2 ≤ n.toNat) (hk : i.toNat + n.toNat ≤ w.size)
    (hU : w.size < USize.size) (hv₀ : 0 < v.toNat)
    (hv₁ : v₁ = v.array[v.start.toNat + n.toNat - 1]!)
    (hv₂ : v₂ = v.array[v.start.toNat + n.toNat - 2]!)
    (hR : w.valAt 0 (i.toNat + n.toNat) < v.toNat * 2 ^ (64 * i.toNat)) :
    (divLoopIn w v v₁ v₂ n i).size = w.size ∧
      (∀ j, i.toNat + n.toNat ≤ j → (divLoopIn w v v₁ v₂ n i)[j]! = w[j]!) ∧
      v.toNat * (divLoopIn w v v₁ v₂ n i).valAt n.toNat i.toNat +
          (divLoopIn w v v₁ v₂ n i).valAt 0 n.toNat = w.valAt 0 (i.toNat + n.toNat) ∧
      (divLoopIn w v v₁ v₂ n i).valAt 0 n.toNat < v.toNat := by
  induction w, i using divLoopIn.induct v v₁ v₂ n with
  | case1 w =>
    refine ⟨by simp [divLoopIn], fun _ _ => by simp [divLoopIn], by simp [divLoopIn],
      by simpa [divLoopIn] using hR⟩
  | case2 w i hi ih =>
    rw [divLoopIn, dite_eq_right hi]
    have hp := toNat_pred hi
    have hi₀ : i.toNat ≠ 0 := fun e => hi (USize.toNat_inj.1 (by rw [e]; rfl))
    -- The window `i - 1` of `R`, and the limbs below it.
    have hsplit : w.valAt 0 (i.toNat + n.toNat) = w.valAt 0 (i.toNat - 1) +
        2 ^ (64 * (i.toNat - 1)) * w.valAt (i.toNat - 1) (n.toNat + 1) := by
      rw [show i.toNat + n.toNat = (i.toNat - 1) + (n.toNat + 1) by lia, UInt64Array.valAt_add,
        Nat.zero_add]
    have hlo := valAt_lt w 0 (i.toNat - 1)
    have hWlt : w.valAt (i.toNat - 1) (n.toNat + 1) < v.toNat * 2 ^ 64 := by
      have e : 2 ^ (64 * i.toNat) = 2 ^ (64 * (i.toNat - 1)) * 2 ^ 64 := by
        rw [← Nat.pow_add]; congr 1; lia
      rw [hsplit, e] at hR
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * (i.toNat - 1))) ?_
      rw [Nat.mul_left_comm]
      lia
    obtain ⟨s₁, s₂, s₃, s₄⟩ := divStepIn_spec w v v₁ v₂ (i - 1) n hn hn₂ (by rw [hp]; lia) hU
      hv₀ hv₁ hv₂ (by rw [hp]; exact hWlt)
    rw [hp] at s₂ s₃ s₄
    have hlo' : (divStepIn w v v₁ v₂ (i - 1) n).valAt 0 (i.toNat - 1) =
        w.valAt 0 (i.toNat - 1) :=
      valAt_congr _ fun j _ hj => s₂ j (.inl (by lia))
    have hR' : (divStepIn w v v₁ v₂ (i - 1) n).valAt 0 ((i - 1).toNat + n.toNat) =
        w.valAt 0 (i.toNat - 1) + 2 ^ (64 * (i.toNat - 1)) *
          (w.valAt (i.toNat - 1) (n.toNat + 1) % v.toNat) := by
      rw [hp, UInt64Array.valAt_add, Nat.zero_add, hlo', s₃]
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih (by rw [s₁, hp]; lia) (by rw [s₁]; exact hU) (by
      rw [hR']
      have hm := Nat.mod_lt (w.valAt (i.toNat - 1) (n.toNat + 1)) hv₀
      rw [hp]
      generalize w.valAt (i.toNat - 1) (n.toNat + 1) % v.toNat = r at *
      generalize 2 ^ (64 * (i.toNat - 1)) = P at *
      have := Nat.mul_le_mul_left P (show r + 1 ≤ v.toNat from hm)
      rw [Nat.mul_add, Nat.mul_one] at this
      rw [Nat.mul_comm v.toNat P]
      lia)
    clear ih
    rw [hp] at i₂ i₃ hR'
    have hqtop : (divLoopIn (divStepIn w v v₁ v₂ (i - 1) n) v v₁ v₂ n (i - 1))[
        n.toNat + (i.toNat - 1)]!.toNat = w.valAt (i.toNat - 1) (n.toNat + 1) / v.toNat := by
      rw [i₂ _ (by lia), Nat.add_comm, s₄]
    refine ⟨i₁.trans s₁, fun j hj => ?_, ?_, i₄⟩
    · rw [i₂ j (by lia), s₂ j (.inr (by lia))]
    · have e₁ := UInt64Array.valAt_add (divLoopIn (divStepIn w v v₁ v₂ (i - 1) n) v v₁ v₂ n
        (i - 1)) n.toNat (i.toNat - 1) 1
      rw [Nat.sub_add_cancel (show 1 ≤ i.toNat by lia), valAt_one, hqtop] at e₁
      rw [e₁, hsplit]
      rw [hR'] at i₃
      have := Nat.div_add_mod (w.valAt (i.toNat - 1) (n.toNat + 1)) v.toNat
      generalize (divLoopIn (divStepIn w v v₁ v₂ (i - 1) n) v v₁ v₂ n (i - 1)).valAt n.toNat
        (i.toNat - 1) = Q at *
      generalize (divLoopIn (divStepIn w v v₁ v₂ (i - 1) n) v v₁ v₂ n (i - 1)).valAt 0
        n.toNat = Rn at *
      generalize w.valAt (i.toNat - 1) (n.toNat + 1) / v.toNat = q at *
      generalize w.valAt (i.toNat - 1) (n.toNat + 1) % v.toNat = r at *
      generalize w.valAt (i.toNat - 1) (n.toNat + 1) = W at *
      generalize 2 ^ (64 * (i.toNat - 1)) = P at *
      subst this
      grind


private theorem size_addBack (w : UInt64Array) (v : USlice) (i k : USize) (q b : UInt64) :
    (addBack w v i k q b).1.size = w.size := by
  induction w, q, b using addBack.induct v i k with
  | case1 w q b h p ih =>
    rw [addBack, dite_eq_left_of_eq_true (eq_true h)]
    exact ih.trans (by simp [p]; rfl)
  | case2 w q b h =>
    rw [addBack, dite_eq_right_of_eq_false (eq_false h)]

/-! ## Division -/

/--
Writes the limbs of `a / b` into the first `a.size - b.size + 1` limbs of `q`, and those of `a % b`
into the first `b.size` limbs of `r`, like GMP's `mpn_tdiv_qr`. It requires
`0 < b.size ≤ a.size` and a nonzero top limb of `b`. A divisor of one limb uses `divRem1`; a
longer one is normalized, like in GMP: `a` and `b` are shifted left by the `k` bits that set the
top bit of `b`, which keeps the corrections of the estimates in `divStepIn` rare, and the remainder
is shifted back at the end. The quotient of `a 2ᵏ` by `b 2ᵏ` is `a / b` and the remainder
`(a % b) 2ᵏ`.
-/
public def divRem (q r a b : USlice) : UInt64Array × UInt64Array :=
  if b.size ≤ 1 then
    let p := divRem1 q a b.array[b.start.toNat]!
    (p.1, r.array.set! r.start.toNat p.2)
  else
    let n := b.size
    let k := 63 - (b.array[b.start.toNat + n.toNat - 1]!).log2.toNat
    let v := (shiftLeft (UInt64Array.replicate n.toNat 0).toUSlice b k).1
    let p := shiftLeft (UInt64Array.replicate (a.size.toNat + 1) 0).toUSlice a k
    let w := p.1.set! a.size.toNat p.2
    let res := divLoopIn w v.toUSlice v[n.toNat - 1]! v[n.toNat - 2]! n (a.size + 1 - n)
    ((add1 q (res.uslice n (n + (a.size + 1 - n))) 0).1, shiftRight r (res.uslice 0 n) k)

@[simp] public theorem size_divRem_fst (q r a b : USlice) :
    (divRem q r a b).1.size = q.array.size := by
  rw [divRem]
  split
  · exact size_divRem1 ..
  · exact size_add1 ..

@[simp] public theorem size_divRem_snd (q r a b : USlice) :
    (divRem q r a b).2.size = r.array.size := by
  rw [divRem]
  split
  · simp
  · exact size_shiftRight ..

private theorem _root_.UInt64.toNat_log2 (x : UInt64) :
    x.log2.toNat = _root_.Nat.log2 x.toNat :=
  rfl

/-- `a 2ᵏ`, for `k < 64`, shifted into `len` zero limbs. -/
private theorem shift_fresh (a : USlice) (k len : Nat) (hk : k < 64) (hlen : a.size.toNat ≤ len)
    (hU : len < USize.size) :
    (shiftLeft (UInt64Array.replicate len 0).toUSlice a k).1.size = len ∧
      (shiftLeft (UInt64Array.replicate len 0).toUSlice a k).1.valAt 0 a.size.toNat +
          2 ^ (64 * a.size.toNat) * (shiftLeft (UInt64Array.replicate len 0).toUSlice a k).2.toNat =
        a.toNat * 2 ^ k := by
  have hsz := size_toUSlice (UInt64Array.replicate len 0) (by simp; exact hU)
  simp only [UInt64Array.size_replicate] at hsz
  have h := valAt_shiftLeft (UInt64Array.replicate len 0).toUSlice a k (by
    rw [hsz, Nat.div_eq_of_lt hk]; lia)
  rw [Nat.div_eq_of_lt hk, Nat.zero_add, start_toUSlice, USize.toNat_zero] at h
  exact ⟨by simp, h⟩

/-- The divisor is at least `β^(n-1)` and below `β^(n-1) 2^(log₂ t + 1)`, for its top limb `t`. -/
private theorem top_bounds (b : USlice) (h₀ : 0 < b.size.toNat)
    (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0) :
    2 ^ (64 * (b.size.toNat - 1)) ≤ b.toNat ∧
      b.toNat < 2 ^ (64 * (b.size.toNat - 1)) *
        2 ^ ((b.array[b.start.toNat + b.size.toNat - 1]!).log2.toNat + 1) := by
  have e := UInt64Array.valAt_add b.array b.start.toNat (b.size.toNat - 1) 1
  rw [show b.size.toNat - 1 + 1 = b.size.toNat by lia, valAt_one,
    show b.start.toNat + (b.size.toNat - 1) = b.start.toNat + b.size.toNat - 1 by lia] at e
  rw [USlice.toNat_eq_valAt, e, UInt64.toNat_log2]
  have hlo := valAt_lt b.array b.start.toNat (b.size.toNat - 1)
  have ht' : 1 ≤ (b.array[b.start.toNat + b.size.toNat - 1]!).toNat := by
    refine Nat.pos_of_ne_zero fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl))
  have hlog := Nat.lt_log2_self (n := (b.array[b.start.toNat + b.size.toNat - 1]!).toNat)
  generalize (b.array[b.start.toNat + b.size.toNat - 1]!).toNat = t at *
  generalize b.array.valAt _ _ = L at *
  generalize 2 ^ (64 * (b.size.toNat - 1)) = P at *
  have h₁ := Nat.mul_le_mul_left P ht'
  have h₂ := Nat.mul_le_mul_left P (show t + 1 ≤ 2 ^ (_root_.Nat.log2 t + 1) from hlog)
  rw [Nat.mul_add, Nat.mul_one] at h₂
  constructor <;> lia

private theorem divRem_long (q r a b : USlice) (h₁ : ¬b.size ≤ 1) (hab : b.size ≤ a.size)
    (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem q r a b).1.valAt q.start.toNat (a.size.toNat - b.size.toNat + 1) =
        a.toNat / b.toNat ∧
      (divRem q r a b).2.valAt r.start.toNat b.size.toNat = a.toNat % b.toNat ∧
      (∀ i, (i < q.start.toNat ∨ q.start.toNat + (a.size.toNat - b.size.toNat + 1) ≤ i) →
        (divRem q r a b).1[i]! = q.array[i]!) ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + b.size.toNat ≤ i) →
        (divRem q r a b).2[i]! = r.array[i]!) := by
  have hn₂ : 2 ≤ b.size.toNat := by
    have := fun h => h₁ (USize.le_iff_toNat_le.2 h); rw [USize.toNat_one] at this; lia
  have hab' := USize.le_iff_toNat_le.1 hab
  have hr' := USize.le_iff_toNat_le.1 hr
  have hbU := b.size.toNat_lt_size
  -- The shift and the bounds of `b`.
  generalize hk : 63 - (b.array[b.start.toNat + b.size.toNat - 1]!).log2.toNat = k
  have hlog : (b.array[b.start.toNat + b.size.toNat - 1]!).log2.toNat ≤ 63 := by
    rw [UInt64.toNat_log2]
    have := (b.array[b.start.toNat + b.size.toNat - 1]!).toNat_lt
    have := (Nat.log2_lt (n := (b.array[b.start.toNat + b.size.toNat - 1]!).toNat) (k := 64)
      (fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl)))).2 this
    lia
  have hk64 : k < 64 := by lia
  obtain ⟨hb₁, hb₂⟩ := top_bounds b (by lia) ht
  have hβn : 2 ^ (64 * (b.size.toNat - 1)) * 2 ^ (_root_.Nat.log2
      (b.array[b.start.toNat + b.size.toNat - 1]!).toNat + 1) * 2 ^ k =
      2 ^ (64 * b.size.toNat) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; rw [← UInt64.toNat_log2]; lia
  rw [UInt64.toNat_log2] at hb₂
  have hbk : b.toNat * 2 ^ k < 2 ^ (64 * b.size.toNat) := by
    rw [← hβn]; exact Nat.mul_lt_mul_of_pos_right hb₂ (Nat.two_pow_pos _)
  -- The normalized divisor `v`.
  obtain ⟨v₁, v₂⟩ := shift_fresh b k b.size.toNat hk64 (Nat.le_refl _) hbU
  generalize hv : (shiftLeft (UInt64Array.replicate b.size.toNat 0).toUSlice b k) = pv at v₁ v₂
  have hV : pv.1.valAt 0 b.size.toNat = b.toNat * 2 ^ k := by
    have := valAt_lt pv.1 0 b.size.toNat
    have hc : pv.2.toNat = 0 := by
      rcases Nat.eq_zero_or_pos pv.2.toNat with h | h
      · exact h
      · have := Nat.mul_le_mul_left (2 ^ (64 * b.size.toNat)) h; lia
    rw [hc, Nat.mul_zero, Nat.add_zero] at v₂
    exact v₂
  have hVpos : 0 < b.toNat * 2 ^ k := by
    have := Nat.two_pow_pos (64 * (b.size.toNat - 1))
    exact Nat.mul_pos (by lia) (Nat.two_pow_pos _)
  have hvU : pv.1.toUSlice.size = b.size := by
    apply USize.toNat_inj.1
    rw [size_toUSlice _ (by rw [v₁]; exact hbU), v₁]
  have hvT : pv.1.toUSlice.toNat = b.toNat * 2 ^ k := by
    rw [USlice.toNat_eq_valAt, hvU, start_toUSlice, USize.toNat_zero, array_toUSlice, hV]
  -- The normalized dividend `w`, with one more limb.
  obtain ⟨w₁, w₂⟩ := shift_fresh a k (a.size.toNat + 1) hk64 (by lia) hU
  generalize hp : shiftLeft (UInt64Array.replicate (a.size.toNat + 1) 0).toUSlice a k = pw
    at w₁ w₂
  have hwsz : (pw.1.set! a.size.toNat pw.2).size = a.size.toNat + 1 := by simp [w₁]
  have hW : (pw.1.set! a.size.toNat pw.2).valAt 0 (a.size.toNat + 1) = a.toNat * 2 ^ k := by
    rw [UInt64Array.valAt_add, valAt_one, Nat.zero_add, getElem!_set!_self _ _ _ (by lia),
      valAt_congr (b := pw.1) _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)]
    exact w₂
  -- The loop.
  have hm : (a.size + 1 - b.size).toNat = a.size.toNat + 1 - b.size.toNat := by
    have h1 : (a.size + 1).toNat = a.size.toNat + 1 :=
      (USize.toNat_add_of_lt (a := a.size) (b := 1) (by rw [USize.toNat_one]; lia)).trans
        (by rw [USize.toNat_one])
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [h1]; lia)), h1]
  have hqb : q.start.toNat + q.size.toNat ≤ q.array.size := by
    have := q.toNat_size; have := q.stop_le_size; lia
  have hR : (pw.1.set! a.size.toNat pw.2).valAt 0 ((a.size + 1 - b.size).toNat + b.size.toNat) <
      pv.1.toUSlice.toNat * 2 ^ (64 * (a.size + 1 - b.size).toNat) := by
    rw [hm, show a.size.toNat + 1 - b.size.toNat + b.size.toNat = a.size.toNat + 1 by lia, hW,
      hvT]
    have ha := valAt_lt a.array a.start.toNat a.size.toNat
    rw [← USlice.toNat_eq_valAt] at ha
    have e : 2 ^ (64 * a.size.toNat) = 2 ^ (64 * (b.size.toNat - 1)) *
        2 ^ (64 * (a.size.toNat + 1 - b.size.toNat)) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hle := Nat.mul_le_mul_right (2 ^ (64 * (a.size.toNat + 1 - b.size.toNat))) hb₁
    rw [← e] at hle
    have hlt := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos k)
    rw [Nat.mul_right_comm]
    exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ hle)
  obtain ⟨l₁, l₂, l₄, l₅⟩ := divLoopIn_spec (pw.1.set! a.size.toNat pw.2)
    pv.1.toUSlice (pv.1[b.size.toNat - 1]!) (pv.1[b.size.toNat - 2]!) b.size (a.size + 1 - b.size)
    hvU hn₂ (by rw [hm, hwsz]; lia) (by rw [hwsz]; exact hU) (by rw [hvT]; exact hVpos)
    (by simp) (by simp) hR
  rw [hm, hvT, show a.size.toNat + 1 - b.size.toNat + b.size.toNat = a.size.toNat + 1 by lia,
    hW] at l₄
  rw [hvT] at l₅
  -- Back to `a` and `b`.
  have hQ := Nat.mul_div_mul_right a.toNat b.toNat (Nat.two_pow_pos k)
  have hRm := Nat.mul_mod_mul_right (2 ^ k) a.toNat b.toNat
  rw [← l₄, Nat.mul_add_div hVpos, Nat.div_eq_of_lt l₅, Nat.add_zero] at hQ
  rw [← l₄, Nat.mul_add_mod, Nat.mod_eq_of_lt l₅] at hRm
  generalize hres : divLoopIn (pw.1.set! a.size.toNat pw.2) pv.1.toUSlice
    (pv.1[b.size.toNat - 1]!) (pv.1[b.size.toNat - 2]!) b.size (a.size + 1 - b.size) = res
    at l₁ l₂ l₄ l₅ hQ hRm
  -- The remainder, from limbs `0` to `n - 1`.
  have hsl := win_spec res 0 b.size (by rw [USize.toNat_zero, l₁, hwsz]; lia)
    (by rw [USize.toNat_zero]; lia)
  rw [USize.zero_add] at hsl
  obtain ⟨sa, ss, sz⟩ := hsl
  have hST : (res.uslice 0 b.size).toNat = (a.toNat % b.toNat) * 2 ^ k := by
    rw [USlice.toNat_eq_valAt, sa, ss, sz, USize.toNat_zero, ← hRm]
  have hshr := valAt_shiftRight r (res.uslice 0 b.size) k (by rw [sz]; lia)
  rw [sz, Nat.div_eq_of_lt hk64, Nat.sub_zero, hST, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    at hshr
  -- The quotient, from limbs `n` to `n + m - 1`, copied into `q`.
  obtain ⟨qa, qs, qz⟩ := win_spec res b.size (a.size + 1 - b.size) (by rw [l₁, hwsz, hm]; lia)
    (by rw [hm]; lia)
  rw [hm] at qz
  have hQT : (res.uslice b.size (b.size + (a.size + 1 - b.size))).toNat = a.toNat / b.toNat := by
    rw [USlice.toNat_eq_valAt, qa, qs, qz, hQ]
  have hqm : (res.uslice b.size (b.size + (a.size + 1 - b.size))).size ≤ q.size :=
    USize.le_iff_toNat_le.2 (by rw [qz]; lia)
  have hcp := valAt_add1 q (res.uslice b.size (b.size + (a.size + 1 - b.size))) 0 hqm
  rw [qz, hQT, UInt64.toNat_zero, Nat.add_zero] at hcp
  have hqlt : a.toNat / b.toNat < 2 ^ (64 * (a.size.toNat + 1 - b.size.toNat)) := by
    rw [← hQT, USlice.toNat_eq_valAt, qz]; exact valAt_lt ..
  have hcp' : (add1 q (res.uslice b.size (b.size + (a.size + 1 - b.size))) 0).1.valAt
      q.start.toNat (a.size.toNat + 1 - b.size.toNat) = a.toNat / b.toNat := by
    generalize (add1 _ _ _).1.valAt _ _ = V at hcp ⊢
    generalize (add1 _ _ _).2.toNat = c at hcp
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * (a.size.toNat + 1 - b.size.toNat))) h0; lia
  have hdiv : divRem q r a b = ((add1 q (res.uslice b.size (b.size + (a.size + 1 - b.size)))
      0).1, shiftRight r (res.uslice 0 b.size) k) := by
    rw [divRem, ite_eq_right h₁]
    dsimp only
    rw [hk, hv, hp, hres]
  rw [hdiv, show a.size.toNat - b.size.toNat + 1 = a.size.toNat + 1 - b.size.toNat by lia]
  refine ⟨hcp', hshr, fun i hi => ?_, fun i hi => ?_⟩
  · exact getElem!_add1 _ _ _ _ (by rw [qz]; lia)
  · exact getElem!_shiftRight _ _ _ _ (by rw [sz, Nat.div_eq_of_lt hk64, Nat.sub_zero]; exact hi)

private theorem divRem_short (q r a b : USlice) (h₁ : b.size ≤ 1) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size) :
    (divRem q r a b).1.valAt q.start.toNat (a.size.toNat - b.size.toNat + 1) =
        a.toNat / b.toNat ∧
      (divRem q r a b).2.valAt r.start.toNat b.size.toNat = a.toNat % b.toNat ∧
      (∀ i, (i < q.start.toNat ∨ q.start.toNat + (a.size.toNat - b.size.toNat + 1) ≤ i) →
        (divRem q r a b).1[i]! = q.array[i]!) ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + b.size.toNat ≤ i) →
        (divRem q r a b).2[i]! = r.array[i]!) := by
  have hb1 : b.size.toNat = 1 := by have := USize.le_iff_toNat_le.1 h₁; simp at this; lia
  have hab' := USize.le_iff_toNat_le.1 hab
  have hr' := USize.le_iff_toNat_le.1 hr
  rw [hb1, Nat.add_sub_cancel] at ht
  have hd : 0 < (b.array[b.start.toNat]!).toNat :=
    Nat.pos_of_ne_zero fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl))
  have hbv : b.toNat = (b.array[b.start.toNat]!).toNat := by
    rw [USlice.toNat_eq_valAt, hb1, valAt_one]
  have haq : a.size ≤ q.size := USize.le_iff_toNat_le.2 (by lia)
  have hrs : r.start.toNat < r.array.size := by
    have := r.toNat_size; have := r.stop_le_size; lia
  rw [divRem, ite_eq_left h₁, hb1, show a.size.toNat - 1 + 1 = a.size.toNat by lia, hbv]
  refine ⟨valAt_divRem1 _ _ _ hd haq, ?_, fun i hi => getElem!_divRem1 _ _ _ _ (by
    have := USize.le_iff_toNat_le.1 haq; lia), fun i hi => getElem!_set!_of_ne _ _ (by lia)⟩
  rw [valAt_one, getElem!_set!_self _ _ _ hrs, toNat_divRem1_snd _ _ _ hd haq]

/-- `divRem` writes `a / b` into `q`. -/
public theorem valAt_divRem_fst (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem q r a b).1.valAt q.start.toNat (a.size.toNat - b.size.toNat + 1) =
      a.toNat / b.toNat := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).1
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).1

/-- `divRem` writes `a % b` into `r`. -/
public theorem valAt_divRem_snd (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem q r a b).2.valAt r.start.toNat b.size.toNat = a.toNat % b.toNat := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).2.1
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).2.1

/-- `divRem` leaves the limbs of `q` outside the quotient unchanged. -/
public theorem getElem!_divRem_fst (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) (i : Nat)
    (hi : i < q.start.toNat ∨ q.start.toNat + (a.size.toNat - b.size.toNat + 1) ≤ i) :
    (divRem q r a b).1[i]! = q.array[i]! := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).2.2.1 i hi
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).2.2.1 i hi

/-- `divRem` leaves the limbs of `r` outside the remainder unchanged. -/
public theorem getElem!_divRem_snd (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + b.size.toNat ≤ i) :
    (divRem q r a b).2[i]! = r.array[i]! := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).2.2.2 i hi
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).2.2.2 i hi

end MPN
