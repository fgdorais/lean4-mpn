/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Cmp
public import Bignum.Sub
public import Bignum.Mul.Limb

/-!
# Schoolbook division

`divRemBasecase u v` divides `u` by a divisor `v` of at least two limbs with a nonzero top limb,
by Knuth's Algorithm D, like GMP's schoolbook division. It computes one quotient limb per step,
from the top down. At step `j`, the remainder `r` is below `v βʲ⁺¹`, so the quotient limb is
`⌊W / v⌋ < β` where `W = ⌊r / βʲ⌋` is the window of limbs `j` to `j + n` of `r`.

The quotient limb is estimated from the top two limbs of `W` and the top limb of `v` as
`q̂ = min ⌊(w_n β + w_{n-1}) / v_{n-1}⌋ (β - 1)`, which is never too small. The trial product
`q̂ v` is then compared with `W` and, while it is larger, `q̂` decreases by one and `v` is
subtracted from it. Correctness only needs the estimate not to be too small; when the top limb of
`v` is at least `β / 2`, Knuth shows that it is at most two too large, which keeps the corrections
few. `Div` normalizes the divisor that way before calling `divRemBasecase`.
-/

open ScalarArray

namespace Bignum

/-! ## Arithmetic facts -/

/-- The limbs `j` to `k` of `r` hold `⌊r / βʲ⌋` when `r < βᵏ`. -/
private theorem toNat_window (r : UInt32Array) (j k : Nat) (hjk : j ≤ k)
    (hr : toNat r < 2 ^ (32 * k)) :
    toNat (r.toSlice j k) = toNat r / 2 ^ (32 * j) := by
  rw [toNat_toSlice] at hr ⊢
  have hsplit := ofLimbs_append (r.toList.take j) (r.toList.drop j)
  rw [List.take_append_drop] at hsplit
  have hlow := ofLimbs_take_lt r.toList j
  have hlen : (r.toList.take j).length = j ∨ r.toList.length < j := by
    simp only [List.length_take]; omega
  have hdrop : ofLimbs (r.toList.drop j) = ofLimbs r.toList / 2 ^ (32 * j) := by
    rcases hlen with hl | hl
    · rw [hl] at hsplit
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow,
        Nat.zero_add]
    · rw [List.drop_of_length_le (by omega), ofLimbs_nil]
      have := ofLimbs_lt r.toList
      have : 2 ^ (32 * r.toList.length) ≤ 2 ^ (32 * j) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact (Nat.div_eq_of_lt (by omega)).symm
  have hbound : ofLimbs (r.toList.drop j) < 2 ^ (32 * (k - j)) := by
    rw [hdrop, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rw [show 32 * (k - j) + 32 * j = 32 * k by omega]
    exact hr
  simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
    List.extract_eq_take_drop, ofLimbs_take_of_lt hbound, hdrop]

/-- The limbs `i` and `i + 1` of `r` give `⌊r / βⁱ⌋` when `r < βⁱ⁺²`. -/
private theorem div_eq_two_limbs (r : UInt32Array) (i : Nat) (hr : toNat r < 2 ^ (32 * (i + 2))) :
    toNat r / 2 ^ (32 * i) = (r.toList.getD (i + 1) 0).toNat * 2 ^ 32 +
      (r.toList.getD i 0).toNat := by
  rw [← toNat_window r i (i + 2) (by omega) hr]
  simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
    List.extract_eq_take_drop, show i + 2 - i = 0 + 1 + 1 by omega]
  rw [ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD]
  simp only [List.take_zero, ofLimbs_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.mul_one, Nat.add_zero]
  omega

/-- The quotient estimate is not too small. -/
private theorem le_div_of_estimate {q W V T vt P : Nat} (hq : q * V ≤ W)
    (hW : W < (T + 1) * P) (hV : vt * P ≤ V) (hvt : 0 < vt) : q ≤ T / vt := by
  rw [Nat.le_div_iff_mul_le hvt]
  have h₁ : q * (vt * P) ≤ q * V := Nat.mul_le_mul_left q hV
  have h₂ : q * vt * P < (T + 1) * P := by rw [Nat.mul_assoc]; omega
  have := Nat.lt_of_mul_lt_mul_right h₂
  omega

/-- A divisor with top limb `vt` is at least `vt βⁿ⁻¹`. -/
private theorem top_limb_le (v : UInt32Array.Slice) (hn : 1 ≤ v.size) :
    (v[v.size - 1]'(by omega)).toNat * 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
  have h := ofLimbs_take_add_one v.copy.toList (v.size - 1) (by simp; omega)
  rw [show v.size - 1 + 1 = v.size by omega, List.take_of_length_le (by simp)] at h
  simp only [toNat, h, UInt32Array.getElem_toList, UInt32Array.Slice.getElem_copy]
  rw [Nat.mul_comm]
  omega

/-! ## The quotient estimate -/

/-- `min ⌊(wt β + wn) / vt⌋ (β - 1)`, the estimate of a quotient limb. -/
@[inline, expose] public def qEstimate (wt wn vt : UInt32) : UInt32 :=
  let e : UInt64 := (wt.toUInt64 * 4294967296 + wn.toUInt64) / vt.toUInt64
  if e < 4294967296 then e.toUInt32 else 0xFFFFFFFF

private theorem toNat_qEstimate (wt wn vt : UInt32) :
    (qEstimate wt wn vt).toNat =
      min ((wt.toNat * 2 ^ 32 + wn.toNat) / vt.toNat) (2 ^ 32 - 1) := by
  have hwt := wt.toNat_lt
  have hwn := wn.toNat_lt
  have ht : (wt.toUInt64 * 4294967296 + wn.toUInt64).toNat = wt.toNat * 2 ^ 32 + wn.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]
    omega
  have he : ((wt.toUInt64 * 4294967296 + wn.toUInt64) / vt.toUInt64).toNat =
      (wt.toNat * 2 ^ 32 + wn.toNat) / vt.toNat := by
    rw [UInt64.toNat_div, ht, UInt32.toNat_toUInt64]
  simp only [qEstimate]
  generalize (wt.toUInt64 * 4294967296 + wn.toUInt64) / vt.toUInt64 = e at *
  split
  · rename_i h
    simp only [UInt64.lt_iff_toNat_lt, he, UInt64.reduceToNat] at h
    rw [UInt64.toNat_toUInt32, he]
    omega
  · rename_i h
    simp only [UInt64.lt_iff_toNat_lt, he, UInt64.reduceToNat] at h
    simp only [UInt32.reduceToNat]
    omega

/-! ## The trial product and its correction -/

/-- `v * x` as `v.size + 1` limbs. -/
public def mulRow (v : UInt32Array.Slice) (x : UInt32) : UInt32Array :=
  let p := mul1 v x
  p.1.push p.2

@[simp] public theorem size_mulRow (v : UInt32Array.Slice) (x : UInt32) :
    (mulRow v x).size = v.size + 1 := by
  simp [mulRow]

public theorem toNat_mulRow (v : UInt32Array.Slice) (x : UInt32) :
    toNat (mulRow v x) = toNat v * x.toNat := by
  have := toNat_mul1 v x
  rw [toNat_toSlice] at this ⊢
  rw [mulRow, UInt32Array.toList_push, ofLimbs_concat, UInt32Array.length_toList, size_mul1,
    this]

/--
Decreases the estimate `qh` of `⌊w / v⌋`, subtracting `v` from the trial product `t = qh v` each
time, while `t` is larger than `w`.
-/
def divCorrect (w v : UInt32Array.Slice) (qh : UInt32) (t : UInt32Array) : UInt32 × UInt32Array :=
  if lt w t then
    if h : qh = 0 then (qh, t) else divCorrect w v (qh - 1) (subAt t 0 v).1
  else
    (qh, t)
termination_by qh.toNat
decreasing_by
  have : qh.toNat ≠ 0 := fun h' => h (UInt32.toNat_inj.1 (by simpa using h'))
  rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
  simp
  omega

private theorem divCorrect_spec (w v : UInt32Array.Slice) (qh : UInt32) (t : UInt32Array)
    (hv : 0 < toNat v) (hs : v.size ≤ t.size) (ht : toNat t = qh.toNat * toNat v)
    (hge : toNat w / toNat v ≤ qh.toNat) :
    (divCorrect w v qh t).2.size = t.size ∧
      (divCorrect w v qh t).1.toNat = toNat w / toNat v ∧
      toNat (divCorrect w v qh t).2 = (toNat w / toNat v) * toNat v := by
  induction qh, t using divCorrect.induct w v with
  | case1 t hlt =>
    -- `qh = 0` makes `t = 0`, which cannot exceed `w`.
    rw [lt_iff, ht, UInt32.toNat_zero, Nat.zero_mul] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | case2 qh t hlt h ih =>
    rw [toNat_toSlice, divCorrect]
    simp only [hlt, h, ↓reduceDIte, ↓reduceIte]
    rw [lt_iff, ht] at hlt
    have hqh : qh.toNat ≠ 0 := fun h' => h (UInt32.toNat_inj.1 (by simpa using h'))
    have hq1 : (qh - 1).toNat = qh.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
      simp
    have hfit : 0 + v.size ≤ t.size := by omega
    have hle : 2 ^ (32 * 0) * toNat v ≤ toNat t := by
      rw [ht, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
      exact Nat.le_mul_of_pos_left _ (by omega)
    -- `qh v > w ≥ ⌊w / v⌋ v`, so `qh` is too large and `qh - 1` is not too small.
    have hdiv := Nat.div_mul_le_self (toNat w) (toNat v)
    have hgt : toNat w / toNat v < qh.toNat :=
      Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hdiv hlt)
    have := ih (by rw [size_subAt _ _ _ hfit]; exact hs)
      (by rw [toNat_subAt_of_le _ _ _ hfit hle, ht, hq1, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
          Nat.sub_mul, Nat.one_mul])
      (by rw [hq1]; omega)
    rw [size_subAt _ _ _ hfit, toNat_toSlice] at this
    exact this
  | case3 qh t hlt =>
    rw [toNat_toSlice, divCorrect]
    simp only [hlt, ↓reduceIte, Bool.false_eq_true]
    rw [lt_iff, ht] at hlt
    -- `qh v ≤ w`, so `qh ≤ ⌊w / v⌋`.
    have hle : qh.toNat ≤ toNat w / toNat v := (Nat.le_div_iff_mul_le hv).2 (by omega)
    have heq : qh.toNat = toNat w / toNat v := by omega
    refine ⟨trivial, heq, ?_⟩
    rw [toNat_toSlice] at ht
    rw [ht, heq]

private theorem size_divCorrect (w v : UInt32Array.Slice) (qh : UInt32) (t : UInt32Array)
    (hs : v.size ≤ t.size) : (divCorrect w v qh t).2.size = t.size := by
  induction qh, t using divCorrect.induct w v with
  | case1 t hlt => rw [divCorrect]; simp [hlt]
  | case2 qh t hlt h ih =>
    rw [divCorrect]
    simp only [hlt, h, ↓reduceDIte, ↓reduceIte]
    rw [ih (by rw [size_subAt _ _ _ (by omega)]; exact hs), size_subAt _ _ _ (by omega)]
  | case3 qh t hlt => rw [divCorrect]; simp [hlt]

private theorem size_divCorrect_mulRow (w v : UInt32Array.Slice) (qh : UInt32) :
    (divCorrect w v qh (mulRow v qh)).2.size = v.size + 1 := by
  rw [size_divCorrect _ _ _ _ (by simp), size_mulRow]

/-! ## The main loop -/

/--
One step of the division, at quotient limb `j`: estimates the limb from the window of limbs `j`
to `j + n` of `r`, corrects the estimate, subtracts its multiple of `v` from `r` at limb `j`, and
writes it into `q`.
-/
def divStepLimb (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat) (r q : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) (hq : j < q.size) : UInt32Array × UInt32Array :=
  let qh := qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
    (v[v.size - 1]'(by omega))
  let p := divCorrect (r.toSlice j (j + v.size + 1)) v qh (mulRow v qh)
  ((subAt r j p.2).1, q.set j p.1 hq)

private theorem size_divStepLimb (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat)
    (r q : UInt32Array) (hr : j + v.size + 1 ≤ r.size) (hq : j < q.size) :
    (divStepLimb v hn j r q hr hq).1.size = r.size ∧
      (divStepLimb v hn j r q hr hq).2.size = q.size := by
  refine ⟨?_, by simp [divStepLimb]⟩
  simp only [divStepLimb]
  rw [size_subAt _ _ _ (by rw [UInt32Array.size_toSlice, size_divCorrect_mulRow]; omega)]

private theorem divStepLimb_spec (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) (j : Nat) (r q : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) (hq : j < q.size)
    (hbound : toNat r < toNat v * 2 ^ (32 * (j + 1)))
    (hzj : q.toList[j]'(by simp; omega) = 0) :
    toNat (divStepLimb v hn j r q hr hq).2 * toNat v + toNat (divStepLimb v hn j r q hr hq).1 =
        toNat q * toNat v + toNat r ∧
      toNat (divStepLimb v hn j r q hr hq).1 < toNat v * 2 ^ (32 * j) ∧
      ∀ i (hi : i < j), (divStepLimb v hn j r q hr hq).2.toList[i]'(by
        rw [UInt32Array.length_toList, (size_divStepLimb v hn j r q hr hq).2]; omega) =
          q.toList[i]'(by simp; omega) := by
  have hvt' : 0 < (v[v.size - 1]'(by omega)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by omega)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hV := toNat_lt v
  have htop := top_limb_le v (by omega)
  have hVpos : 0 < toNat v := by
    have : 0 < (v[v.size - 1]'(by omega)).toNat * 2 ^ (32 * (v.size - 1)) :=
      Nat.mul_pos hvt' (Nat.two_pow_pos _)
    omega
  -- `r` fits in the limbs up to `j + n`.
  have hR : toNat r < 2 ^ (32 * (j + v.size + 1)) := by
    have : toNat v * 2 ^ (32 * (j + 1)) ≤ 2 ^ (32 * v.size) * 2 ^ (32 * (j + 1)) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hV)
    rw [← Nat.pow_add, show 32 * v.size + 32 * (j + 1) = 32 * (j + v.size + 1) by omega] at this
    omega
  -- The window `W = ⌊r / βʲ⌋` and its top two limbs.
  have hW := toNat_window r j (j + v.size + 1) (by omega) hR
  have hTw := div_eq_two_limbs r (j + v.size - 1)
    (by rw [show j + v.size - 1 + 2 = j + v.size + 1 by omega]; exact hR)
  rw [show j + v.size - 1 + 1 = j + v.size by omega] at hTw
  have hg₁ : r.toList.getD (j + v.size) 0 = r[j + v.size]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, show j + v.size < r.size by omega]
  have hg₂ : r.toList.getD (j + v.size - 1) 0 = r[j + v.size - 1]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, show j + v.size - 1 < r.size by omega]
  rw [hg₁, hg₂] at hTw
  have hqh := toNat_qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
    (v[v.size - 1]'(by omega))
  -- The true quotient limb `⌊W / v⌋` is below `β` and below the estimate.
  have hWdiv : toNat (r.toSlice j (j + v.size + 1)) / 2 ^ (32 * (v.size - 1)) =
      toNat r / 2 ^ (32 * (j + v.size - 1)) := by
    rw [hW, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2
    omega
  have hWlt : toNat (r.toSlice j (j + v.size + 1)) <
      ((r[j + v.size]'(by omega)).toNat * 2 ^ 32 + (r[j + v.size - 1]'(by omega)).toNat + 1) *
        2 ^ (32 * (v.size - 1)) := by
    rw [← hTw, ← hWdiv, Nat.mul_comm]
    exact Nat.lt_mul_div_succ _ (Nat.two_pow_pos _)
  have hest := le_div_of_estimate (Nat.div_mul_le_self (toNat (r.toSlice j (j + v.size + 1)))
    (toNat v)) hWlt htop hvt'
  have hqlt : toNat (r.toSlice j (j + v.size + 1)) / toNat v < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hVpos, hW, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      Nat.mul_comm (2 ^ 32) (toNat v), Nat.mul_assoc, ← Nat.pow_add,
      show 32 + 32 * j = 32 * (j + 1) by omega]
    exact hbound
  have hge : toNat (r.toSlice j (j + v.size + 1)) / toNat v ≤
      (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
        (v[v.size - 1]'(by omega))).toNat := by
    rw [hqh]
    exact Nat.le_min.2 ⟨hest, Nat.le_pred_of_lt hqlt⟩
  -- The correction ends with the true quotient limb and its multiple of `v`.
  obtain ⟨hs, hq₁, ht₁⟩ := divCorrect_spec (r.toSlice j (j + v.size + 1)) v
    (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
      (v[v.size - 1]'(by omega)))
    (mulRow v (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
      (v[v.size - 1]'(by omega))))
    hVpos (by simp) (by rw [toNat_mulRow, Nat.mul_comm]) hge
  have h₃ : ∀ i (hi : i < j), (divStepLimb v hn j r q hr hq).2.toList[i]'(by
      rw [UInt32Array.length_toList, (size_divStepLimb v hn j r q hr hq).2]; omega) =
        q.toList[i]'(by simp; omega) := by
    intro i hi
    simp only [divStepLimb, UInt32Array.toList_set]
    exact List.getElem_set_ne (by omega) _
  refine ⟨?_, ?_, h₃⟩
  · clear h₃
    simp only [divStepLimb]
    generalize divCorrect (r.toSlice j (j + v.size + 1)) v
      (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
        (v[v.size - 1]'(by omega)))
      (mulRow v (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
        (v[v.size - 1]'(by omega)))) = p at *
    rw [size_mulRow] at hs
    generalize toNat (r.toSlice j (j + v.size + 1)) = W at *
    have hfit : j + p.2.toSlice.size ≤ r.size := by rw [UInt32Array.size_toSlice, hs]; omega
    have hle : 2 ^ (32 * j) * toNat p.2 ≤ toNat r := by
      rw [ht₁, hW]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
        (Nat.mul_div_le _ _)
    have hset := ofLimbs_set q.toList j p.1 (by simp; omega)
    rw [hzj, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hset
    rw [toNat_subAt_of_le _ _ _ hfit hle, toNat_toSlice, toNat_toSlice, UInt32Array.toList_set,
      hset, hq₁, ← toNat_toSlice]
    rw [ht₁] at hle ⊢
    rw [Nat.add_mul, Nat.mul_assoc]
    simp only [toNat_toSlice] at hle ⊢
    omega
  · clear h₃
    simp only [divStepLimb]
    generalize divCorrect (r.toSlice j (j + v.size + 1)) v
      (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
        (v[v.size - 1]'(by omega)))
      (mulRow v (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
        (v[v.size - 1]'(by omega)))) = p at *
    rw [size_mulRow] at hs
    generalize toNat (r.toSlice j (j + v.size + 1)) = W at *
    have hfit : j + p.2.toSlice.size ≤ r.size := by rw [UInt32Array.size_toSlice, hs]; omega
    have hle : 2 ^ (32 * j) * toNat p.2 ≤ toNat r := by
      rw [ht₁, hW]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
        (Nat.mul_div_le _ _)
    rw [toNat_subAt_of_le _ _ _ hfit hle, ht₁]
    -- `r - βʲ q v = βʲ (W mod v) + (r mod βʲ) < βʲ v`.
    have h₁ := Nat.div_add_mod (toNat r) (2 ^ (32 * j))
    have h₂ := Nat.div_add_mod W (toNat v)
    have h₃ := Nat.mod_lt W hVpos
    have h₄ := Nat.mod_lt (toNat r) (Nat.two_pow_pos (32 * j))
    rw [← hW] at h₁
    generalize 2 ^ (32 * j) = P at *
    generalize W / toNat v = qs at *
    generalize W % toNat v = wm at *
    generalize toNat r % P = rm at *
    have : P * (wm + 1) ≤ P * toNat v := Nat.mul_le_mul_left _ h₃
    rw [Nat.mul_comm (toNat v) P]
    rw [← h₁, ← h₂, Nat.mul_add, Nat.mul_comm (toNat v) qs] at hle ⊢
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-- Computes the quotient limbs below `k`, from the top down, with one `divStepLimb` each. -/
def divLoop (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (k : Nat) (r q : UInt32Array)
    (hr : k + v.size ≤ r.size) (hq : k ≤ q.size) : UInt32Array × UInt32Array :=
  if hk : k = 0 then
    (q, r)
  else
    let s := divStepLimb v hn (k - 1) r q (by omega) (by omega)
    divLoop v hn (k - 1) s.1 s.2
      (by rw [(size_divStepLimb v hn (k - 1) r q (by omega) (by omega)).1]; omega)
      (by rw [(size_divStepLimb v hn (k - 1) r q (by omega) (by omega)).2]; omega)
termination_by k

private theorem divLoop_spec (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) (k : Nat) (r q : UInt32Array)
    (hr : k + v.size ≤ r.size) (hq : k ≤ q.size)
    (hbound : toNat r < toNat v * 2 ^ (32 * k))
    (hz : ∀ i (hi : i < k), q.toList[i]'(by simp; omega) = 0) :
    toNat (divLoop v hn k r q hr hq).1 * toNat v + toNat (divLoop v hn k r q hr hq).2 =
        toNat q * toNat v + toNat r ∧
      toNat (divLoop v hn k r q hr hq).2 < toNat v := by
  induction k generalizing r q with
  | zero =>
    simp only [toNat_toSlice] at hbound ⊢
    rw [divLoop]
    simp only [↓reduceDIte]
    exact ⟨trivial, by simpa using hbound⟩
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃⟩ := divStepLimb_spec v hn hvt k r q (by omega) (by omega) hbound
      (hz k (by omega))
    obtain ⟨ih₁, ih₂⟩ := ih _ _ _ _ h₂ (fun i hi => by rw [h₃ i hi]; exact hz i (by omega))
    simp only [toNat_toSlice] at ih₁ ih₂ h₁ ⊢
    rw [divLoop]
    simp only [Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
    exact ⟨by rw [ih₁, h₁], ih₂⟩

/-! ## Schoolbook division -/

/--
`u / v` and `u % v` by Knuth's Algorithm D, for a divisor of at least two limbs, as a quotient of
`max (u.size + 1) v.size - v.size` limbs and a remainder of `max (u.size + 1) v.size` limbs,
untrimmed. It is exact when the top limb of `v` is not zero.
-/
public def divRemBasecase (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  divLoop v hn (max (u.size + 1) v.size - v.size) (copyPadded u (max (u.size + 1) v.size))
    (.replicate (max (u.size + 1) v.size - v.size) 0)
    (by rw [size_copyPadded _ _ (by omega)]; omega) (by simp)

/-- `divRemBasecase` divides: `u = q v + r` with `r < v`. -/
public theorem divRemBasecase_spec (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) :
    toNat (divRemBasecase u v hn).1 * toNat v + toNat (divRemBasecase u v hn).2 = toNat u ∧
      toNat (divRemBasecase u v hn).2 < toNat v := by
  have hvt' : 1 ≤ (v[v.size - 1]'(by omega)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by omega)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have htop := top_limb_le v (by omega)
  have hU := toNat_lt u
  -- `u < β^u.size ≤ β^(N - 1) = β^(n - 1) β^(N - n) ≤ v β^(N - n)`.
  have hbound : toNat u < toNat v * 2 ^ (32 * (max (u.size + 1) v.size - v.size)) := by
    have h₁ : 2 ^ (32 * u.size) ≤
        2 ^ (32 * (v.size - 1)) * 2 ^ (32 * (max (u.size + 1) v.size - v.size)) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h₂ : 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
      have := Nat.mul_le_mul_right (2 ^ (32 * (v.size - 1))) hvt'
      omega
    have := Nat.mul_le_mul_right (2 ^ (32 * (max (u.size + 1) v.size - v.size))) h₂
    omega
  have h := divLoop_spec v hn hvt (max (u.size + 1) v.size - v.size)
    (copyPadded u (max (u.size + 1) v.size)) (.replicate (max (u.size + 1) v.size - v.size) 0)
    (by rw [size_copyPadded _ _ (by omega)]; omega) (by simp)
    (by rw [toNat_copyPadded]; exact hbound) (fun i hi => by simp)
  rw [toNat_copyPadded] at h
  simp only [divRemBasecase]
  rw [toNat_toSlice (UInt32Array.replicate _ 0)] at h
  simpa using h

end Bignum
