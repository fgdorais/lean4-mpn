/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Mul.Limb

/-!
# Schoolbook division

`divRemBasecase u v` divides `u` by a divisor `v` of at least two limbs with a nonzero top limb,
by Knuth's Algorithm D, like GMP's schoolbook division. It computes one quotient limb per step,
from the top down. At step `j`, the remainder `r` is below `v βʲ⁺¹`, so the quotient limb is
`⌊W / v⌋ < β` where `W = ⌊r / βʲ⌋` is the window of limbs `j` to `j + n` of `r`.

The quotient limb is estimated from the top two limbs of `W` and the top limb of `v` as
`q̂ = min ⌊(w_n β + w_{n-1}) / v_{n-1}⌋ (β - 1)`, then corrected at most twice with the next
limbs, as in Knuth's Algorithm D: `q̂` decreases while `q̂ (v_{n-1} β + v_{n-2})` exceeds the top
three limbs of `W`. It is never too small, and when the top limb of `v` is at least `β / 2` it is
at most one too large, which happens with probability about `2 / β`. The step subtracts `q̂ v`
from the window in place with `subMul1`, like GMP's `mpn_submul_1`; the window went negative
exactly when the borrow out of its low `n` limbs exceeds its top limb, and then `v` is added back
and `q̂` decreased. Correctness only needs the estimate not to be too small. `Div` normalizes the
divisor before calling `divRemBasecase`.
-/

open ScalarArray

namespace Bignum

/-! ## Arithmetic facts -/

/-- The limbs `j` to `k` of `r` hold `⌊r / βʲ⌋` when `r < βᵏ`. -/
public theorem toNat_window (r : UInt32Array) (j k : Nat) (hjk : j ≤ k)
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

/-- The limbs `i` to `i + 2` of `r` give `⌊r / βⁱ⌋` when `r < βⁱ⁺³`. -/
private theorem div_eq_three_limbs (r : UInt32Array) (i : Nat)
    (hr : toNat r < 2 ^ (32 * (i + 3))) :
    toNat r / 2 ^ (32 * i) = ((r.toList.getD (i + 2) 0).toNat * 2 ^ 32 +
      (r.toList.getD (i + 1) 0).toNat) * 2 ^ 32 + (r.toList.getD i 0).toNat := by
  rw [← toNat_window r i (i + 3) (by omega) hr]
  simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
    List.extract_eq_take_drop, show i + 3 - i = 0 + 1 + 1 + 1 by omega]
  rw [ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD]
  simp only [List.take_zero, ofLimbs_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.mul_one, Nat.add_zero]
  rw [show 32 * 2 = 32 + 32 by rfl, Nat.pow_add]
  generalize (r.toList[i]?.getD 0).toNat = a
  generalize (r.toList[i + 1]?.getD 0).toNat = b
  generalize (r.toList[i + 2]?.getD 0).toNat = c
  generalize (2 : Nat) ^ 32 = B
  grind

/-- The quotient estimate is not too small. -/
public theorem le_div_of_estimate {q W V T vt P : Nat} (hq : q * V ≤ W)
    (hW : W < (T + 1) * P) (hV : vt * P ≤ V) (hvt : 0 < vt) : q ≤ T / vt := by
  rw [Nat.le_div_iff_mul_le hvt]
  have h₁ : q * (vt * P) ≤ q * V := Nat.mul_le_mul_left q hV
  have h₂ : q * vt * P < (T + 1) * P := by rw [Nat.mul_assoc]; omega
  have := Nat.lt_of_mul_lt_mul_right h₂
  omega

/-- A divisor with top limb `vt` is at least `vt βⁿ⁻¹`. -/
public theorem top_limb_le (v : UInt32Array.Slice) (hn : 1 ≤ v.size) :
    (v[v.size - 1]'(by omega)).toNat * 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
  have h := ofLimbs_take_add_one v.copy.toList (v.size - 1) (by simp; omega)
  rw [show v.size - 1 + 1 = v.size by omega, List.take_of_length_le (by simp)] at h
  simp only [toNat, h, UInt32Array.getElem_toList, UInt32Array.Slice.getElem_copy]
  rw [Nat.mul_comm]
  omega

/-- A divisor with top limbs `vt` and `vs` is at least `(vt β + vs) βⁿ⁻²`. -/
private theorem top_two_limbs_le (v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    ((v[v.size - 1]'(by omega)).toNat * 2 ^ 32 + (v[v.size - 2]'(by omega)).toNat) *
      2 ^ (32 * (v.size - 2)) ≤ toNat v := by
  have h₁ := ofLimbs_take_add_one v.copy.toList (v.size - 1) (by simp; omega)
  have h₂ := ofLimbs_take_add_one v.copy.toList (v.size - 2) (by simp; omega)
  rw [show v.size - 1 + 1 = v.size by omega, List.take_of_length_le (by simp)] at h₁
  rw [show v.size - 2 + 1 = v.size - 1 by omega] at h₂
  simp only [UInt32Array.getElem_toList, UInt32Array.Slice.getElem_copy] at h₁ h₂
  have hpow : 2 ^ (32 * (v.size - 1)) = 2 ^ (32 * (v.size - 2)) * 2 ^ 32 := by
    rw [← Nat.pow_add]; congr 1; omega
  simp only [toNat, h₁, h₂, hpow]
  generalize ofLimbs (v.copy.toList.take (v.size - 2)) = L
  generalize (v[v.size - 1]'(by omega)).toNat = a
  generalize (v[v.size - 2]'(by omega)).toNat = b
  generalize 2 ^ (32 * (v.size - 2)) = P
  generalize (2 : Nat) ^ 32 = B
  rw [Nat.add_mul, Nat.mul_comm (a * B) P, Nat.mul_comm b P, Nat.mul_assoc P, Nat.mul_comm a B]
  have : P * (B * a) = P * B * a := (Nat.mul_assoc _ _ _).symm
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

/--
One correction of the estimate `q` with the next limb `wl` of the window and the second limb `vs`
of the divisor, as in Knuth's Algorithm D: `r` is `wt β + wn - q vt`, and `q` decreases when
`q vs > r β + wl`, which means that `q (vt β + vs)` exceeds the top three limbs of the window.
-/
@[inline, expose] public def qRefine (q : UInt32) (r : UInt64) (wl vt vs : UInt32) :
    UInt32 × UInt64 :=
  if r < 4294967296 then
    if (r <<< 32) + wl.toUInt64 < q.toUInt64 * vs.toUInt64 then (q - 1, r + vt.toUInt64)
    else (q, r)
  else
    (q, r)

/--
The estimate `q` of a quotient limb, from `qEstimate`, corrected twice with `qRefine` using the
next limb `wl` of the window and the second limb `vs` of the divisor. Then it is at most one too
large, and rarely, so that `v` is seldom added back.

It takes `q` as a parameter and computes `wt β` with a shift: when the kernel compares terms that
contain a multiplication by the literal `2³²`, it may unfold it into a recursion on the literal.
-/
@[inline, expose] public def qEstimate3 (q wt wn wl vt vs : UInt32) : UInt32 :=
  let r := ((wt.toUInt64 <<< 32) + wn.toUInt64) - q.toUInt64 * vt.toUInt64
  -- `qRefine` twice, written without the pair, which the compiler would box.
  if r < 4294967296 then
    if (r <<< 32) + wl.toUInt64 < q.toUInt64 * vs.toUInt64 then
      let r' := r + vt.toUInt64
      if r' < 4294967296 then
        if (r' <<< 32) + wl.toUInt64 < (q - 1).toUInt64 * vs.toUInt64 then q - 1 - 1 else q - 1
      else q - 1
    else q
  else q

/-- The arithmetic of one correction, over any base `B`. -/
private theorem refine_arith {q r T qt vt vs wl B : Nat} (hT : q * vt + r = T)
    (hW : qt * (vt * B + vs) ≤ T * B + wl) (hc : r * B + wl < q * vs) :
    qt < q ∧ (q - 1) * vt + (r + vt) = T := by
  have e₁ : q * (vt * B + vs) = q * vt * B + q * vs := by
    rw [Nat.mul_add, Nat.mul_assoc]
  have e₂ : T * B = q * vt * B + r * B := by rw [← hT, Nat.add_mul]
  have hgt : qt * (vt * B + vs) < q * (vt * B + vs) := by omega
  have hq := Nat.lt_of_mul_lt_mul_right hgt
  refine ⟨hq, ?_⟩
  have : vt ≤ q * vt := Nat.le_mul_of_pos_left _ (by omega)
  rw [Nat.sub_mul, Nat.one_mul]
  omega

/-- `qRefine` keeps `q vt + r = T` and never goes below a quotient `qt` with `qt V' ≤ W'`. -/
private theorem qRefine_spec (q : UInt32) (r : UInt64) (wl vt vs : UInt32) (T qt : Nat)
    (hT : q.toNat * vt.toNat + r.toNat = T) (hq : qt ≤ q.toNat)
    (hW : qt * (vt.toNat * 2 ^ 32 + vs.toNat) ≤ T * 2 ^ 32 + wl.toNat) :
    (qRefine q r wl vt vs).1.toNat * vt.toNat + (qRefine q r wl vt vs).2.toNat = T ∧
      qt ≤ (qRefine q r wl vt vs).1.toNat := by
  have hq32 := q.toNat_lt
  have hvt := vt.toNat_lt
  have hvs := vs.toNat_lt
  have hwl := wl.toNat_lt
  have hr64 := r.toNat_lt
  unfold qRefine
  split
  · rename_i hr
    have hr' : r.toNat < 2 ^ 32 := by simpa [UInt64.lt_iff_toNat_lt] using hr
    split
    · rename_i hc
      have hmul : (q.toUInt64 * vs.toUInt64).toNat = q.toNat * vs.toNat := by
        rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
      have hsh : ((r <<< 32) + wl.toUInt64).toNat = r.toNat * 2 ^ 32 + wl.toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
        simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
        have : r.toNat * 2 ^ 32 < 2 ^ 64 := by
          have := Nat.mul_lt_mul_of_pos_right hr' (by decide : 0 < 2 ^ 32)
          simpa using this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hc' : r.toNat * 2 ^ 32 + wl.toNat < q.toNat * vs.toNat := by
        have := UInt64.lt_iff_toNat_lt.1 hc
        rwa [hsh, hmul] at this
      obtain ⟨hgt, hsum⟩ := refine_arith hT hW hc'
      have hq1 : (q - 1).toNat = q.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
        simp
      have hrv : (r + vt.toUInt64).toNat = r.toNat + vt.toNat := by
        rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
        exact Nat.mod_eq_of_lt (by simp; omega)
      exact ⟨by rw [hq1, hrv]; exact hsum, by rw [hq1]; omega⟩
    · exact ⟨hT, hq⟩
  · exact ⟨hT, hq⟩

private theorem toNat_two_words (wt wn : UInt32) :
    (wt.toUInt64 * 4294967296 + wn.toUInt64).toNat = wt.toNat * 2 ^ 32 + wn.toNat := by
  have hwt := wt.toNat_lt
  have hwn := wn.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]
  omega

private theorem toNat_mul_words (x y : UInt32) :
    (x.toUInt64 * y.toUInt64).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt) (by decide)

/--
`qEstimate3` is never too small: it is at least a quotient `qt` that the first estimate `q`
bounds and with `qt (vt β + vs) ≤ (wt β + wn) β + wl`.
-/
private theorem qEstimate3_ge (q wt wn wl vt vs : UInt32) (qt : Nat)
    (hle : q.toNat * vt.toNat ≤ wt.toNat * 2 ^ 32 + wn.toNat) (h₀ : qt ≤ q.toNat)
    (h₁ : qt * (vt.toNat * 2 ^ 32 + vs.toNat) ≤
      (wt.toNat * 2 ^ 32 + wn.toNat) * 2 ^ 32 + wl.toNat) :
    qt ≤ (qEstimate3 q wt wn wl vt vs).toNat := by
  have hT : ((wt.toUInt64 <<< 32) + wn.toUInt64).toNat = wt.toNat * 2 ^ 32 + wn.toNat := by
    have := wt.toNat_lt
    have := wn.toNat_lt
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega
  have hqv : (q.toUInt64 * vt.toUInt64).toNat = q.toNat * vt.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' q.toNat_lt vt.toNat_lt) (by decide)
  have hT₀ : q.toNat * vt.toNat +
      (((wt.toUInt64 <<< 32) + wn.toUInt64) - q.toUInt64 * vt.toUInt64).toNat =
      wt.toNat * 2 ^ 32 + wn.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hT, hqv]; exact hle), hT, hqv]
    exact Nat.add_sub_cancel' hle
  obtain ⟨hT₁, hq₁⟩ := qRefine_spec q _ wl vt vs (wt.toNat * 2 ^ 32 + wn.toNat) qt hT₀ h₀ h₁
  have := (qRefine_spec _ _ wl vt vs _ qt hT₁ hq₁ h₁).2
  -- `qEstimate3` is the two applications of `qRefine`.
  have heq : qEstimate3 q wt wn wl vt vs =
      (qRefine (qRefine q (((wt.toUInt64 <<< 32) + wn.toUInt64) - q.toUInt64 * vt.toUInt64) wl
        vt vs).1 (qRefine q (((wt.toUInt64 <<< 32) + wn.toUInt64) - q.toUInt64 * vt.toUInt64) wl
        vt vs).2 wl vt vs).1 := by
    simp only [qEstimate3, qRefine]
    split
    · split
      · split
        · split <;> rfl
        · rfl
      · rfl
    · rfl
  rw [heq]
  exact this

/-! ## Adding back -/

/--
Adds `v` back into the limbs `j` to `j + n` of `r` and decreases the quotient limb `qh`, after
`subMul1` subtracted too large a multiple of `v`: `e` counts the multiples of `βʲ⁺ⁿ` by which the
window is still negative, and each carry out of the window cancels one.
-/
def divAddBack (v : UInt32Array.Slice) (j : Nat) (r : UInt32Array) (qh e : UInt32)
    (h : j + v.size ≤ r.size) : UInt32Array × UInt32 :=
  if hq : qh = 0 then
    (r, 0)
  else
    let p := addMul1 r j v 1 h
    if e ≤ p.2 then
      (p.1, qh - 1)
    else
      divAddBack v j p.1 (qh - 1) (e - p.2) (by rw [size_addMul1]; exact h)
termination_by qh.toNat
decreasing_by
  have : qh.toNat ≠ 0 := fun h' => hq (UInt32.toNat_inj.1 (by simpa using h'))
  rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
  simp
  omega

/--
The arithmetic of one add-back: the window `r₀ < Q` falls short of `R` by `e Q` with the quotient
limb `q`, and `r₁` with carry `c` is the window plus `P V`, where `P V < Q`.
-/
private theorem addBack_arith {r₀ r₁ c P V Q q R e : Nat} (hr : r₀ < Q) (hPV : P * V < Q)
    (hadd : r₁ + Q * c = r₀ + P * V) (hinv : r₀ + P * (V * q) = R + Q * e) (he : 1 ≤ e)
    (hq : 1 ≤ q) :
    c ≤ 1 ∧ r₁ + P * (V * (q - 1)) + Q * c = R + Q * e ∧ R < P * (V * q) := by
  have hsplit : P * (V * q) = P * (V * (q - 1)) + P * V := by
    rw [← Nat.mul_add, ← Nat.mul_add_one, Nat.sub_add_cancel hq]
  have hQe : Q * 1 ≤ Q * e := Nat.mul_le_mul_left _ he
  refine ⟨?_, by omega, by omega⟩
  have : Q * c < Q * 2 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

private theorem divAddBack_spec (v : UInt32Array.Slice) (j : Nat) (r : UInt32Array)
    (qh e : UInt32) (h : j + v.size ≤ r.size) (R : Nat)
    (hz : ∀ k (hk : k < r.size), j + v.size ≤ k → r[k] = 0) (he : 0 < e.toNat)
    (hinv : toNat r + 2 ^ (32 * j) * (toNat v * qh.toNat) =
      R + 2 ^ (32 * (j + v.size)) * e.toNat) :
    (divAddBack v j r qh e h).1.size = r.size ∧
      toNat (divAddBack v j r qh e h).1 +
          2 ^ (32 * j) * (toNat v * (divAddBack v j r qh e h).2.toNat) = R ∧
      R < 2 ^ (32 * j) * (toNat v * ((divAddBack v j r qh e h).2.toNat + 1)) ∧
      ∀ k (hk : k < (divAddBack v j r qh e h).1.size), j + v.size ≤ k →
        (divAddBack v j r qh e h).1[k] = 0 := by
  have hPV : 2 ^ (32 * j) * toNat v < 2 ^ (32 * (j + v.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_left (toNat_lt v) (Nat.two_pow_pos _)
  induction r, qh, e, h using divAddBack.induct v j with
  | case1 r e h =>
    -- `qh = 0` would make the window `R + e βʲ⁺ⁿ ≥ βʲ⁺ⁿ`, but it is below `βʲ⁺ⁿ`.
    have := toNat_lt_of_zero_from r (j + v.size) hz
    simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hinv
    have : 2 ^ (32 * (j + v.size)) * 1 ≤ 2 ^ (32 * (j + v.size)) * e.toNat :=
      Nat.mul_le_mul_left _ he
    omega
  | case2 r qh e h hq p hle =>
    simp only [p] at hle
    have heq : divAddBack v j r qh e h = ((addMul1 r j v 1 h).1, qh - 1) := by
      rw [divAddBack]
      simp only [hq, ↓reduceDIte, hle, ↓reduceIte]
    rw [heq]
    dsimp only
    have hqpos : 1 ≤ qh.toNat := by
      rcases Nat.eq_zero_or_pos qh.toNat with h' | h'
      · exact absurd (UInt32.toNat_inj.1 (by simpa using h')) hq
      · exact h'
    have hqh : (qh - 1).toNat = qh.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
      simp
    have hadd := toNat_addMul1 r j v 1 h
    simp only [UInt32.toNat_one, Nat.mul_one] at hadd
    obtain ⟨hc, h₁, h₂⟩ := addBack_arith (toNat_lt_of_zero_from r (j + v.size) hz) hPV hadd hinv
      he hqpos
    have hle' := UInt32.le_iff_toNat_le.1 hle
    have hc1 : (addMul1 r j v 1 h).2.toNat = 1 := by omega
    have he1 : e.toNat = 1 := by omega
    rw [hc1, he1] at h₁
    refine ⟨size_addMul1 .., ?_, ?_, fun k hk hjk => ?_⟩
    · rw [hqh]
      omega
    · rw [hqh, Nat.sub_add_cancel hqpos]
      exact h₂
    · have := getElem?_addMul1 r j v 1 h k (by omega)
      rw [getElem?_pos (addMul1 r j v 1 h).1 k hk,
        getElem?_pos r k (by rw [size_addMul1] at hk; exact hk), Option.some.injEq] at this
      rw [this]
      exact hz k _ hjk
  | case3 r qh e h hq p hlt ih =>
    simp only [p] at hlt ih
    have heq : divAddBack v j r qh e h = divAddBack v j (addMul1 r j v 1 h).1 (qh - 1)
        (e - (addMul1 r j v 1 h).2) (by rw [size_addMul1]; exact h) := by
      rw [divAddBack]
      simp only [hq, ↓reduceDIte, hlt, ↓reduceIte]
    rw [heq]
    have hqpos : 1 ≤ qh.toNat := by
      rcases Nat.eq_zero_or_pos qh.toNat with h' | h'
      · exact absurd (UInt32.toNat_inj.1 (by simpa using h')) hq
      · exact h'
    have hqh : (qh - 1).toNat = qh.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
      simp
    have hadd := toNat_addMul1 r j v 1 h
    simp only [UInt32.toNat_one, Nat.mul_one] at hadd
    obtain ⟨hc, h₁, -⟩ := addBack_arith (toNat_lt_of_zero_from r (j + v.size) hz) hPV hadd hinv
      he hqpos
    have hlt' : (addMul1 r j v 1 h).2.toNat < e.toNat :=
      UInt32.lt_iff_toNat_lt.1 (UInt32.not_le.1 hlt)
    have hes : (e - (addMul1 r j v 1 h).2).toNat = e.toNat - (addMul1 r j v 1 h).2.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.2 (by omega))
    obtain ⟨ih₁, ih₂⟩ := ih
      (fun k hk hjk => by
        have := getElem?_addMul1 r j v 1 h k (by omega)
        rw [getElem?_pos (addMul1 r j v 1 h).1 k hk,
          getElem?_pos r k (by rw [size_addMul1] at hk; exact hk), Option.some.injEq] at this
        rw [this]
        exact hz k _ hjk)
      (by rw [hes]; omega)
      (by
        have hm : 2 ^ (32 * (j + v.size)) * (e.toNat - (addMul1 r j v 1 h).2.toNat) =
            2 ^ (32 * (j + v.size)) * e.toNat -
              2 ^ (32 * (j + v.size)) * (addMul1 r j v 1 h).2.toNat :=
          Nat.mul_sub _ _ _
        have : 2 ^ (32 * (j + v.size)) * (addMul1 r j v 1 h).2.toNat ≤
            2 ^ (32 * (j + v.size)) * e.toNat := Nat.mul_le_mul_left _ (by omega)
        rw [hqh, hes, hm]
        omega)
    exact ⟨by rw [ih₁, size_addMul1], ih₂⟩

@[simp] private theorem size_divAddBack (v : UInt32Array.Slice) (j : Nat) (r : UInt32Array)
    (qh e : UInt32) (h : j + v.size ≤ r.size) : (divAddBack v j r qh e h).1.size = r.size := by
  induction r, qh, e, h using divAddBack.induct v j with
  | case1 r e h => rw [divAddBack]; simp
  | case2 r qh e h hq p hle =>
    simp only [p] at hle
    rw [divAddBack]
    simp [hq, hle]
  | case3 r qh e h hq p hlt ih =>
    simp only [p] at hlt ih
    rw [divAddBack]
    simp only [hq, ↓reduceDIte, hlt, ↓reduceIte]
    rw [ih, size_addMul1]

/-! ## The main loop -/

/--
The end of a step, from `p = subMul1 r j v qh`: the borrow `p.2` out of the low `n` limbs of the
window exceeds its top limb exactly when the window went negative, and then `v` is added back.
-/
def divFinish (v : UInt32Array.Slice) (j : Nat) (p : UInt32Array × UInt32) (qh : UInt32)
    (hp : j + v.size + 1 ≤ p.1.size) : UInt32Array × UInt32 :=
  let t := p.1[j + v.size]
  if p.2 ≤ t then
    (p.1.set (j + v.size) (t - p.2), qh)
  else
    divAddBack v j (p.1.set (j + v.size) 0) qh (p.2 - t) (by rw [UInt32Array.size_set]; omega)

/--
One step of the division at quotient limb `j`, which returns the new remainder and the quotient
limb: estimates the limb from the top three limbs of the window of limbs `j` to `j + n` of `r`
and the top two limbs of `v`, subtracts its multiple
of `v` from the window in place, and adds `v` back while the window is negative, which the borrow
out of its low `n` limbs shows when it exceeds the top limb.
-/
def divStepCore (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat) (r : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) : UInt32Array × UInt32 :=
  let qh := qEstimate3 (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
    (v[v.size - 1]'(by omega))) (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
    (r[j + v.size - 2]'(by omega)) (v[v.size - 1]'(by omega)) (v[v.size - 2]'(by omega))
  divFinish v j (subMul1 r j v qh (by omega)) qh (by rw [size_subMul1]; omega)

/-- `divStepCore` with the quotient limb written into `q`. -/
def divStepLimb (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat) (r q : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) (hq : j < q.size) : UInt32Array × UInt32Array :=
  let s := divStepCore v hn j r hr
  (s.1, q.set j s.2 hq)

private theorem size_divStepCore (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat)
    (r : UInt32Array) (hr : j + v.size + 1 ≤ r.size) :
    (divStepCore v hn j r hr).1.size = r.size := by
  simp only [divStepCore, divFinish]
  split <;> simp

private theorem size_divStepLimb (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat)
    (r q : UInt32Array) (hr : j + v.size + 1 ≤ r.size) (hq : j < q.size) :
    (divStepLimb v hn j r q hr hq).1.size = r.size ∧
      (divStepLimb v hn j r q hr hq).2.size = q.size :=
  ⟨size_divStepCore v hn j r hr, by simp [divStepLimb]⟩

/-- `r < P v (q + 1)` when `⌊⌊r / P⌋ / v⌋ ≤ q`. -/
private theorem lt_of_div_div_le {R P V q : Nat} (hP : 0 < P) (hV : 0 < V) (h : R / P / V ≤ q) :
    R < P * (V * (q + 1)) := by
  have h₁ := Nat.lt_mul_div_succ (R / P) hV
  have h₂ : V * (R / P / V + 1) ≤ V * (q + 1) := Nat.mul_le_mul_left _ (by omega)
  have h₃ := Nat.lt_mul_div_succ R hP
  have h₄ : P * (R / P + 1) ≤ P * (V * (q + 1)) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The estimate is not too small: `r < βʲ v (q̂ + 1)`. -/
private theorem lt_of_qEstimate (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) (j : Nat) (r : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) (hbound : toNat r < toNat v * 2 ^ (32 * (j + 1))) :
    toNat r < 2 ^ (32 * j) * (toNat v * ((qEstimate3 (qEstimate (r[j + v.size]'(by omega))
      (r[j + v.size - 1]'(by omega)) (v[v.size - 1]'(by omega))) (r[j + v.size]'(by omega))
      (r[j + v.size - 1]'(by omega)) (r[j + v.size - 2]'(by omega)) (v[v.size - 1]'(by omega))
      (v[v.size - 2]'(by omega))).toNat + 1)) := by
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
  -- The first estimate times the top limb of `v` fits in the top two limbs of the window.
  have hle₀ : (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
      (v[v.size - 1]'(by omega))).toNat * (v[v.size - 1]'(by omega)).toNat ≤
      (r[j + v.size]'(by omega)).toNat * 2 ^ 32 + (r[j + v.size - 1]'(by omega)).toNat := by
    have : (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
        (v[v.size - 1]'(by omega))).toNat ≤ ((r[j + v.size]'(by omega)).toNat * 2 ^ 32 +
          (r[j + v.size - 1]'(by omega)).toNat) / (v[v.size - 1]'(by omega)).toNat := by
      rw [hqh]; exact Nat.min_le_left _ _
    exact Nat.le_trans (Nat.mul_le_mul_right _ this) (Nat.div_mul_le_self _ _)
  -- The top three limbs of the window, `W' = ⌊r / βʲ⁺ⁿ⁻²⌋`, and the top two limbs of `v`.
  have hT3 := div_eq_three_limbs r (j + v.size - 2)
    (by rw [show j + v.size - 2 + 3 = j + v.size + 1 by omega]; exact hR)
  rw [show j + v.size - 2 + 2 = j + v.size by omega,
    show j + v.size - 2 + 1 = j + v.size - 1 by omega, hg₁, hg₂] at hT3
  have hg₃ : r.toList.getD (j + v.size - 2) 0 = r[j + v.size - 2]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, show j + v.size - 2 < r.size by omega]
  rw [hg₃] at hT3
  have hW2 : toNat (r.toSlice j (j + v.size + 1)) / 2 ^ (32 * (v.size - 2)) =
      toNat r / 2 ^ (32 * (j + v.size - 2)) := by
    rw [hW, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2
    omega
  have hWlt3 : toNat (r.toSlice j (j + v.size + 1)) <
      (((r[j + v.size]'(by omega)).toNat * 2 ^ 32 + (r[j + v.size - 1]'(by omega)).toNat) *
        2 ^ 32 + (r[j + v.size - 2]'(by omega)).toNat + 1) * 2 ^ (32 * (v.size - 2)) := by
    rw [← hT3, ← hW2, Nat.mul_comm]
    exact Nat.lt_mul_div_succ _ (Nat.two_pow_pos _)
  have hvt2 : 0 < (v[v.size - 1]'(by omega)).toNat * 2 ^ 32 + (v[v.size - 2]'(by omega)).toNat :=
    Nat.lt_of_lt_of_le (Nat.mul_pos hvt' (Nat.two_pow_pos _)) (Nat.le_add_right _ _)
  have hest3 := le_div_of_estimate (Nat.div_mul_le_self (toNat (r.toSlice j (j + v.size + 1)))
    (toNat v)) hWlt3 (top_two_limbs_le v hn) hvt2
  have h₁ := Nat.le_trans (Nat.mul_le_mul_right _ hest3) (Nat.div_mul_le_self _ _)
  have hge3 := qEstimate3_ge _ _ _ _ _ _ _ hle₀ hge h₁
  rw [hW] at hge3
  exact lt_of_div_div_le (Nat.two_pow_pos _) hVpos hge3

private theorem divFinish_spec (v : UInt32Array.Slice) (j : Nat) (r : UInt32Array)
    (p : UInt32Array × UInt32) (qh : UInt32) (hp : j + v.size + 1 ≤ p.1.size)
    (hsub : toNat p.1 + 2 ^ (32 * j) * (toNat v * qh.toNat) =
      toNat r + 2 ^ (32 * (j + v.size)) * p.2.toNat)
    (hz : ∀ k (hk : k < p.1.size), j + v.size + 1 ≤ k → p.1[k] = 0)
    (hest : toNat r < 2 ^ (32 * j) * (toNat v * (qh.toNat + 1))) :
    toNat (divFinish v j p qh hp).1 +
        2 ^ (32 * j) * (toNat v * (divFinish v j p qh hp).2.toNat) = toNat r ∧
      toNat r < 2 ^ (32 * j) * (toNat v * ((divFinish v j p qh hp).2.toNat + 1)) := by
  have hset (x : UInt32) := ofLimbs_set p.1.toList (j + v.size) x (by simp; omega)
  simp only [UInt32Array.getElem_toList] at hset
  rw [toNat_toSlice] at hsub
  by_cases hle : p.2 ≤ p.1[j + v.size]
  · have heq : divFinish v j p qh hp =
        (p.1.set (j + v.size) (p.1[j + v.size] - p.2), qh) := by
      simp only [divFinish, hle, ↓reduceIte]
    rw [heq]
    dsimp only
    generalize ht : p.1[j + v.size] = t at *
    have hle' := UInt32.le_iff_toNat_le.1 hle
    have hts : (t - p.2).toNat = t.toNat - p.2.toNat := UInt32.toNat_sub_of_le _ _ hle
    have h₁ := hset (t - p.2)
    rw [hts] at h₁
    have hm : 2 ^ (32 * (j + v.size)) * (t.toNat - p.2.toNat) =
        2 ^ (32 * (j + v.size)) * t.toNat - 2 ^ (32 * (j + v.size)) * p.2.toNat :=
      Nat.mul_sub _ _ _
    have : 2 ^ (32 * (j + v.size)) * p.2.toNat ≤ 2 ^ (32 * (j + v.size)) * t.toNat :=
      Nat.mul_le_mul_left _ hle'
    refine ⟨?_, hest⟩
    rw [toNat_toSlice, UInt32Array.toList_set]
    omega
  · have heq : divFinish v j p qh hp = divAddBack v j (p.1.set (j + v.size) 0) qh
        (p.2 - p.1[j + v.size]) (by rw [UInt32Array.size_set]; omega) := by
      simp only [divFinish, hle, ↓reduceIte]
    rw [heq]
    generalize ht : p.1[j + v.size] = t at *
    have hlt' : t.toNat < p.2.toNat := UInt32.lt_iff_toNat_lt.1 (UInt32.not_le.1 hle)
    have hes : (p.2 - t).toNat = p.2.toNat - t.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.2 (by omega))
    have h₁ := hset 0
    rw [UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at h₁
    have hm : 2 ^ (32 * (j + v.size)) * (p.2.toNat - t.toNat) =
        2 ^ (32 * (j + v.size)) * p.2.toNat - 2 ^ (32 * (j + v.size)) * t.toNat :=
      Nat.mul_sub _ _ _
    have : 2 ^ (32 * (j + v.size)) * t.toNat ≤ 2 ^ (32 * (j + v.size)) * p.2.toNat :=
      Nat.mul_le_mul_left _ (by omega)
    obtain ⟨-, h₂, h₃, -⟩ := divAddBack_spec v j (p.1.set (j + v.size) 0) qh (p.2 - t)
      (by rw [UInt32Array.size_set]; omega) (toNat r)
      (fun k hk hjk => by
        rw [UInt32Array.getElem_set]
        split
        · rfl
        · rw [UInt32Array.size_set] at hk
          exact hz k hk (by omega))
      (by rw [hes]; omega)
      (by
        rw [hes, hm, toNat_toSlice, UInt32Array.toList_set]
        omega)
    exact ⟨h₂, h₃⟩

private theorem divStepCore_spec (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) (j : Nat) (r : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) (hbound : toNat r < toNat v * 2 ^ (32 * (j + 1))) :
    toNat (divStepCore v hn j r hr).1 +
        2 ^ (32 * j) * (toNat v * (divStepCore v hn j r hr).2.toNat) = toNat r ∧
      toNat r < 2 ^ (32 * j) * (toNat v * ((divStepCore v hn j r hr).2.toNat + 1)) := by
  have hest := lt_of_qEstimate v hn hvt j r hr hbound
  have hV := toNat_lt v
  -- The limbs of `r` above `j + n` are zero, and `subMul1` leaves them unchanged.
  have hR : toNat r < 2 ^ (32 * (j + v.size + 1)) := by
    have : toNat v * 2 ^ (32 * (j + 1)) ≤ 2 ^ (32 * v.size) * 2 ^ (32 * (j + 1)) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hV)
    rw [← Nat.pow_add, show 32 * v.size + 32 * (j + 1) = 32 * (j + v.size + 1) by omega] at this
    omega
  simp only [divStepCore]
  refine divFinish_spec v j r _ _ _ (toNat_subMul1 r j v _ _) (fun k hk hjk => ?_) hest
  have := getElem?_subMul1 r j v (qEstimate3 (qEstimate (r[j + v.size]'(by omega))
    (r[j + v.size - 1]'(by omega)) (v[v.size - 1]'(by omega))) (r[j + v.size]'(by omega))
    (r[j + v.size - 1]'(by omega)) (r[j + v.size - 2]'(by omega)) (v[v.size - 1]'(by omega))
    (v[v.size - 2]'(by omega))) (by omega) k (by omega)
  rw [size_subMul1] at hk
  rw [getElem?_pos _ k (by rw [size_subMul1]; exact hk), getElem?_pos r k hk,
    Option.some.injEq] at this
  rw [this]
  have := getElem_eq_zero_of_ofLimbs_lt (l := r.toList) (k := k) (by simpa using hk)
    (by rw [← toNat_toSlice]; exact Nat.lt_of_lt_of_le hR (Nat.pow_le_pow_right (by decide)
      (by omega)))
  simpa using this

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
  obtain ⟨h₁, h₂⟩ := divStepCore_spec v hn hvt j r hr hbound
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · simp only [divStepLimb]
    have hset := ofLimbs_set q.toList j (divStepCore v hn j r hr).2 (by simp; omega)
    rw [hzj, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hset
    rw [toNat_toSlice, UInt32Array.toList_set, hset, ← toNat_toSlice]
    generalize toNat (divStepCore v hn j r hr).1 = r' at *
    generalize (divStepCore v hn j r hr).2.toNat = qf at *
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm qf (toNat v)]
    omega
  · simp only [divStepLimb]
    generalize toNat (divStepCore v hn j r hr).1 = r' at *
    generalize (divStepCore v hn j r hr).2.toNat = qf at *
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add] at h₂
    rw [Nat.mul_comm (toNat v)]
    omega
  · simp only [divStepLimb, UInt32Array.toList_set]
    exact List.getElem_set_ne (by omega) _

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
