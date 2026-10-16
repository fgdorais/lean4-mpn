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
and `q̂` decreased. Correctness only needs the estimate not to be too small.

The division works in one array, like GMP's: after step `j`, the window is below `v`, so its top
limb `j + n` is zero, and the step writes the quotient limb there (`divLoopIn`). At the end the
limbs below `n` are the remainder and the limbs from `n` on are the quotient. The compiled step
(`divStepInFast`) ends the fold of `subMul1` with a continuation that finishes the step, so that
it allocates no pair. `Div` normalizes the divisor and the dividend, and divides the latter in
place with `divRemBasecaseTop` when its top limb is below the divisor's, as it is after
normalization.
-/

open ScalarArray

namespace Bignum

/-! ## Arithmetic facts -/

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

public theorem toNat_qEstimate (wt wn vt : UInt32) :
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
public theorem qEstimate3_ge (q wt wn wl vt vs : UInt32) (qt : Nat)
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

private theorem size_divStepCore (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat)
    (r : UInt32Array) (hr : j + v.size + 1 ≤ r.size) :
    (divStepCore v hn j r hr).1.size = r.size := by
  simp only [divStepCore, divFinish]
  split <;> simp

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

/-! ## Framing

A step of the division only touches the window of limbs `j` to `j + n` of `r`. On `W ++ H` with
the window in `W`, it acts on `W` and leaves `H` as it is, which lets the quotient limbs live above
the window, in the limbs that the steps free.
-/

private theorem divAddBack_append (v : UInt32Array.Slice) (j : Nat) (W H : UInt32Array)
    (qh e : UInt32) (h : j + v.size ≤ W.size) (h' : j + v.size ≤ (W ++ H).size) :
    divAddBack v j (W ++ H) qh e h' =
      ((divAddBack v j W qh e h).1 ++ H, (divAddBack v j W qh e h).2) := by
  induction W, qh, e, h using divAddBack.induct v j with
  | case1 W e h =>
    rw [divAddBack, divAddBack]
    simp
  | case2 W qh e h hq p hle =>
    simp only [p] at hle
    rw [divAddBack, divAddBack]
    simp only [hq, ↓reduceDIte, addMul1_append W H j v 1 h, hle, ↓reduceIte]
  | case3 W qh e h hq p hlt ih =>
    simp only [p] at hlt ih
    rw [divAddBack, divAddBack]
    simp only [hq, ↓reduceDIte, addMul1_append W H j v 1 h, hlt, ↓reduceIte]
    exact ih _

private theorem divFinish_append (v : UInt32Array.Slice) (j : Nat) (W H : UInt32Array)
    (c qh : UInt32) (hp : j + v.size + 1 ≤ W.size) (hp' : j + v.size + 1 ≤ (W ++ H).size) :
    divFinish v j (W ++ H, c) qh hp' =
      ((divFinish v j (W, c) qh hp).1 ++ H, (divFinish v j (W, c) qh hp).2) := by
  have hg : (W ++ H)[j + v.size]'(by simp; omega) = W[j + v.size] :=
    UInt32Array.getElem_append_left (by omega)
  simp only [divFinish, hg]
  split
  · simp only [set_append_left W H (j + v.size) _ (by omega)]
  · simp only [set_append_left W H (j + v.size) _ (by omega)]
    exact divAddBack_append v j _ H qh _ (by simp; omega) _

private theorem divStepCore_append (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat)
    (W H : UInt32Array) (hr : j + v.size + 1 ≤ W.size) (hr' : j + v.size + 1 ≤ (W ++ H).size) :
    divStepCore v hn j (W ++ H) hr' =
      ((divStepCore v hn j W hr).1 ++ H, (divStepCore v hn j W hr).2) := by
  have g₀ : (W ++ H)[j + v.size]'(by simp; omega) = W[j + v.size] :=
    UInt32Array.getElem_append_left (by omega)
  have g₁ : (W ++ H)[j + v.size - 1]'(by simp; omega) = W[j + v.size - 1] :=
    UInt32Array.getElem_append_left (by omega)
  have g₂ : (W ++ H)[j + v.size - 2]'(by simp; omega) = W[j + v.size - 2] :=
    UInt32Array.getElem_append_left (by omega)
  simp only [divStepCore, g₀, g₁, g₂, subMul1_append W H j v _ (by omega)]
  exact divFinish_append v j _ H _ _ (by rw [size_subMul1]; omega) _

/-! ## The loop in one array -/

/--
One step of the division at quotient limb `j`, with the quotient limb written into limb `j + n`,
which the step frees: after it, the window is below `v`, so its top limb is zero.
-/
public def divStepIn (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat) (r : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) : UInt32Array :=
  (divStepCore v hn j r hr).1.set (j + v.size) (divStepCore v hn j r hr).2
    (by rw [size_divStepCore]; omega)

@[simp] private theorem size_divStepIn (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat)
    (r : UInt32Array) (hr : j + v.size + 1 ≤ r.size) : (divStepIn v hn j r hr).size = r.size := by
  simp [divStepIn, size_divStepCore]

/-! ### The compiled step

`divStepInFast` subtracts the multiple of `v` with the fold of `subMul1Fast` and ends it with
`foldInPlaceThen`, whose continuation finishes the step and writes the quotient limb, so that a
step allocates no pair. `@[csimp]` makes the compiler use it in place of `divStepIn`; it comes
before `divLoopIn` so that the loop is compiled with it.
-/

/-- The end of a step from the window `r'` and the borrow `b` out of its low `n` limbs. -/
@[inline] def divFinishIn (v : UInt32Array.Slice) (j : Nat) (r' : UInt32Array) (b qh : UInt32)
    (hp : j + v.size + 1 ≤ r'.size) : UInt32Array :=
  let t := r'[j + v.size]
  if b ≤ t then
    r'.set (j + v.size) qh
  else
    let p := divAddBack v j (r'.set (j + v.size) 0) qh (b - t) (by rw [UInt32Array.size_set]; omega)
    p.1.set (j + v.size) p.2 (by rw [size_divAddBack, UInt32Array.size_set]; omega)

/-- `divStepIn` with one fold and no pairs, which the compiler uses in its place. -/
public def divStepInFast (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (j : Nat) (r : UInt32Array)
    (hr : j + v.size + 1 ≤ r.size) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ v.array.size < 4294967295 then
    let qh := qEstimate3 (qEstimate (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
      (v[v.size - 1]'(by omega))) (r[j + v.size]'(by omega)) (r[j + v.size - 1]'(by omega))
      (r[j + v.size - 2]'(by omega)) (v[v.size - 1]'(by omega)) (v[v.size - 2]'(by omega))
    let arr := v.array
    let st := v.start.toUSize
    r.foldInPlaceThen j.toUSize v.size.toUSize 0xFFFFFFFF
      (subMul1Step arr st v.size.toUSize (lt_usizeSize hs.2) (limbU_bound v (lt_usizeSize hs.2)) qh)
      (fun r' h => if hp : j + v.size + 1 ≤ r'.size then divFinishIn v j r' (~~~h) qh hp else r')
      (by
        have := USize.le_size
        have := v.stop_le_array_size
        have := v.start_le_stop
        have := v.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        omega)
  else
    divStepIn v hn j r hr

private theorem set_set_same (r : UInt32Array) (i : Nat) (x y : UInt32) (h : i < r.size) (h') :
    (r.set i x h).set i y h' = r.set i y h := by
  apply UInt32Array.toList_inj.1
  simp [UInt32Array.toList_set, List.set_set]

/-- `divFinishIn` is `divFinish` followed by writing the quotient limb. -/
private theorem divFinishIn_eq (v : UInt32Array.Slice) (j : Nat) (r' : UInt32Array)
    (b qh : UInt32) (hp : j + v.size + 1 ≤ r'.size) :
    divFinishIn v j r' b qh hp = (divFinish v j (r', b) qh hp).1.set (j + v.size)
      (divFinish v j (r', b) qh hp).2 (by
        simp only [divFinish]; split <;> simp <;> omega) := by
  simp only [divFinishIn, divFinish]
  split
  · simp only [set_set_same]
  · rfl

@[csimp] public theorem divStepIn_eq_divStepInFast : @divStepIn = @divStepInFast := by
  funext v hn j r hr
  rw [divStepInFast]
  split
  · rename_i hs
    rw [UInt32Array.foldInPlaceThen_eq, divStepIn]
    simp only [divStepCore]
    have hf : j.toUSize.toNat + v.size.toUSize.toNat ≤ r.size := by
      have := USize.le_size
      have := v.stop_le_array_size
      have := v.start_le_stop
      have := v.size_eq
      rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
      omega
    simp only [subMul1_eq_foldInPlace r j v _ (by omega) hs hf]
    rw [dite_eq_left (by simp; omega), divFinishIn_eq]
  · rfl

/--
The quotient limbs below `k`, from the top down, in one array: the remainder stays in the limbs
below `k + n` and each quotient limb goes into the limb its step frees, so that at the end the
limbs below `n` are the remainder and the limbs from `n` on are the quotient.
-/
def divLoopIn (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (k : Nat) (r : UInt32Array)
    (hr : k + v.size ≤ r.size) : UInt32Array :=
  if hk : k = 0 then
    r
  else
    divLoopIn v hn (k - 1) (divStepIn v hn (k - 1) r (by omega)) (by rw [size_divStepIn]; omega)
termination_by k

/-- An array of `m + 1` limbs with its top limb set is its first `m` limbs and that limb. -/
private theorem set_last_eq_append (r : UInt32Array) (m : Nat) (x : UInt32) (h : m + 1 = r.size) :
    r.set m x (by omega) = r.extract 0 m ++ UInt32Array.mk #[x] := by
  apply UInt32Array.toList_inj.1
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [UInt32Array.toList_set, UInt32Array.toList_append] at h₁ h₂ ⊢
  simp only [List.length_set, UInt32Array.length_toList] at h₁
  by_cases hi : i < m
  · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by simp; omega)]
    simp
  · have him : i = m := by omega
    subst him
    rw [List.getElem_set_self, List.getElem_append_right (by simp; omega)]
    simp

private theorem divLoopIn_spec (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) (k : Nat) (W H : UInt32Array) (hW : W.size = k + v.size)
    (hbound : ofLimbs W.toList < toNat v * 2 ^ (32 * k)) :
    (divLoopIn v hn k (W ++ H) (by simp; omega)).size = W.size + H.size ∧
      ofLimbs ((divLoopIn v hn k (W ++ H) (by simp; omega)).extract 0 v.size).toList < toNat v ∧
      ofLimbs ((divLoopIn v hn k (W ++ H) (by simp; omega)).extract 0 v.size).toList +
          toNat v * ofLimbs ((divLoopIn v hn k (W ++ H) (by simp; omega)).extract v.size
            (W.size + H.size)).toList =
        ofLimbs W.toList + toNat v * 2 ^ (32 * k) * ofLimbs H.toList := by
  induction k generalizing W H with
  | zero =>
    have e : divLoopIn v hn 0 (W ++ H) (by simp; omega) = W ++ H := by
      rw [divLoopIn]; simp
    rw [e]
    simp only [Nat.zero_add] at hW
    have e₀ : (W ++ H).extract 0 v.size = W := by
      rw [← hW]; exact UInt32Array.extract_append_eq_left W H
    have e₁ : (W ++ H).extract v.size (W.size + H.size) = H := by
      rw [← hW]; exact UInt32Array.extract_append_eq_right W H
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at hbound ⊢
    rw [e₀, e₁]
    exact ⟨by simp, hbound, rfl⟩
  | succ k ih =>
    have hr : k + v.size + 1 ≤ W.size := by omega
    -- The step on `W` and its quotient limb.
    obtain ⟨s₁, s₂⟩ := divStepCore_spec v hn hvt k W hr (by rw [toNat_toSlice]; exact hbound)
    generalize hS : divStepCore v hn k W hr = S at s₁ s₂
    simp only [toNat_toSlice] at s₁ s₂
    have hSs : S.1.size = W.size := by rw [← hS, size_divStepCore]
    -- After the step, the window is below `v βᵏ`, so its top limb can go.
    have hlt : ofLimbs S.1.toList < toNat v * 2 ^ (32 * k) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_add] at s₂
      rw [Nat.mul_comm (toNat v)]
      omega
    have hW₁ : ofLimbs (S.1.extract 0 (k + v.size)).toList = ofLimbs S.1.toList := by
      have hv := toNat_lt v
      have : toNat v * 2 ^ (32 * k) ≤ 2 ^ (32 * (k + v.size)) := by
        rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_of_lt hv)
      rw [UInt32Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
      exact ofLimbs_take_of_lt (by omega)
    have hstep : divStepIn v hn k (W ++ H) (by simp; omega) =
        S.1.extract 0 (k + v.size) ++ (UInt32Array.mk #[S.2] ++ H) := by
      rw [divStepIn]
      simp only [divStepCore_append v hn k W H hr, hS]
      rw [set_append_left S.1 H (k + v.size) _ (by omega),
        set_last_eq_append S.1 (k + v.size) S.2 (by omega), UInt32Array.append_assoc]
    have e : divLoopIn v hn (k + 1) (W ++ H) (by simp; omega) =
        divLoopIn v hn k (S.1.extract 0 (k + v.size) ++ (UInt32Array.mk #[S.2] ++ H))
          (by simp; omega) := by
      rw [divLoopIn]
      simp only [Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel, hstep]
    obtain ⟨i₁, i₂, i₃⟩ := ih (S.1.extract 0 (k + v.size)) (UInt32Array.mk #[S.2] ++ H)
      (by simp; omega) (by rw [hW₁]; exact hlt)
    have hsz : (S.1.extract 0 (k + v.size)).size + (UInt32Array.mk #[S.2] ++ H).size =
        W.size + H.size := by
      simp; omega
    simp only [hsz] at i₁ i₃
    have hH : ofLimbs (UInt32Array.mk #[S.2] ++ H).toList =
        S.2.toNat + 2 ^ 32 * ofLimbs H.toList := by
      rw [UInt32Array.toList_append, ofLimbs_append]
      simp
    rw [hW₁, hH] at i₃
    rw [e]
    refine ⟨i₁, i₂, ?_⟩
    rw [i₃, ← s₁, Nat.mul_add 32 k 1, Nat.mul_one, Nat.pow_add]
    generalize ofLimbs S.1.toList = R at *
    generalize S.2.toNat = q at *
    generalize toNat v = V at *
    generalize ofLimbs H.toList = Q at *
    generalize 2 ^ (32 * k) = P at *
    simp only [Nat.mul_add]
    grind

/-! ## Schoolbook division -/

/--
`u / v` and `u % v` by Knuth's Algorithm D, for a divisor of at least two limbs, as a quotient of
`max (u.size + 1) v.size - v.size` limbs and a remainder of `v.size` limbs, untrimmed: `u` is
copied with a zero limb on top, and `divLoopIn` divides the copy in place. It is exact when the top
limb of `v` is not zero.
-/
public def divRemBasecase (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  let a := divLoopIn v hn (max (u.size + 1) v.size - v.size)
    (copyPadded u (max (u.size + 1) v.size)) (by rw [size_copyPadded _ _ (by omega)]; omega)
  (a.extract v.size a.size, a.extract 0 v.size)

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
  have hcs : (copyPadded u (max (u.size + 1) v.size)).size =
      max (u.size + 1) v.size - v.size + v.size := by
    rw [size_copyPadded _ _ (by omega)]; omega
  have hcv : ofLimbs (copyPadded u (max (u.size + 1) v.size)).toList = toNat u := by
    rw [← toNat_toSlice, toNat_copyPadded]
  have hspec := divLoopIn_spec v hn hvt (max (u.size + 1) v.size - v.size)
    (copyPadded u (max (u.size + 1) v.size)) .empty hcs (by rw [hcv]; exact hbound)
  simp only [UInt32Array.append_empty, UInt32Array.size_empty, Nat.add_zero,
    UInt32Array.toList_empty, ofLimbs_nil, Nat.mul_zero, hcv] at hspec
  obtain ⟨h₁, h₂, h₃⟩ := hspec
  simp only [divRemBasecase, toNat_toSlice]
  simp only [h₁]
  refine ⟨?_, h₂⟩
  rw [Nat.mul_comm]
  omega

/--
`divRemBasecase` on an array `r` that already has room for the first step. When the top limb of
`r` is below the top limb of `v`, `r < v βᵏ` with `k = r.size - v.size`, and `divLoopIn` runs on
`r` itself, without the copy and the extra top limb that `divRemBasecase` adds, whose quotient limb
would be zero, and with the quotient limbs in `r`: the result is cut into the quotient, from limb
`n` on, and the remainder, below. A dividend normalized with the divisor's shift has this form:
its top limb is below the factor `2ˢ ≤ 2³¹`, and the divisor's is at least `2³¹`.
-/
public def divRemBasecaseTop (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  if h : v.size ≤ r.size then
    if r[r.size - 1]'(by omega) < v[v.size - 1]'(by omega) then
      let a := divLoopIn v hn (r.size - v.size) r (by omega)
      (a.extract v.size a.size, a.extract 0 v.size)
    else
      divRemBasecase r.toSlice v hn
  else
    divRemBasecase r.toSlice v hn

public theorem divRemBasecaseTop_spec (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) :
    toNat (divRemBasecaseTop r v hn).1 * toNat v + toNat (divRemBasecaseTop r v hn).2 =
        toNat r ∧
      toNat (divRemBasecaseTop r v hn).2 < toNat v := by
  by_cases hs : v.size ≤ r.size
  · by_cases htop : r[r.size - 1]'(by omega) < v[v.size - 1]'(by omega)
    · have e : divRemBasecaseTop r v hn =
          ((divLoopIn v hn (r.size - v.size) r (by omega)).extract v.size
            (divLoopIn v hn (r.size - v.size) r (by omega)).size,
          (divLoopIn v hn (r.size - v.size) r (by omega)).extract 0 v.size) := by
        unfold divRemBasecaseTop
        rw [dite_eq_left hs, ite_eq_left htop]
      rw [e]
      -- `r < βʳ⁻¹ (r_top + 1) ≤ βʳ⁻¹ v_top ≤ v βᵏ`.
      have hbound : toNat r < toNat v * 2 ^ (32 * (r.size - v.size)) := by
        have hsplit := ofLimbs_take_add_one r.toList (r.size - 1) (by simp; omega)
        rw [show r.size - 1 + 1 = r.size by omega, List.take_of_length_le (by simp)] at hsplit
        have hlow := ofLimbs_take_lt r.toList (r.size - 1)
        simp only [UInt32Array.getElem_toList] at hsplit
        have hlt : (r[r.size - 1]'(by omega)).toNat + 1 ≤ (v[v.size - 1]'(by omega)).toNat := by
          rw [UInt32.lt_iff_toNat_lt] at htop
          omega
        have hv := top_limb_le v (by omega)
        have hpow : 2 ^ (32 * (r.size - 1)) =
            2 ^ (32 * (v.size - 1)) * 2 ^ (32 * (r.size - v.size)) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hv' : (v[v.size - 1]'(by omega)).toNat * 2 ^ (32 * (r.size - 1)) ≤
            toNat v * 2 ^ (32 * (r.size - v.size)) := by
          rw [hpow, ← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ hv
        have h₁ := Nat.mul_le_mul_left (2 ^ (32 * (r.size - 1))) hlt
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 ^ (32 * (r.size - 1)))
          (v[v.size - 1]'(by omega)).toNat] at h₁
        rw [toNat_toSlice]
        omega
      have hspec := divLoopIn_spec v hn hvt (r.size - v.size) r .empty (by omega)
        (by rw [toNat_toSlice] at hbound; exact hbound)
      simp only [UInt32Array.append_empty, UInt32Array.size_empty, Nat.add_zero,
        UInt32Array.toList_empty, ofLimbs_nil, Nat.mul_zero] at hspec
      obtain ⟨h₁, h₂, h₃⟩ := hspec
      simp only [toNat_toSlice]
      simp only [h₁]
      refine ⟨?_, h₂⟩
      rw [Nat.mul_comm]
      omega
    · have e : divRemBasecaseTop r v hn = divRemBasecase r.toSlice v hn := by
        unfold divRemBasecaseTop
        rw [dite_eq_left hs, ite_eq_right htop]
      rw [e]
      exact divRemBasecase_spec r.toSlice v hn hvt
  · have e : divRemBasecaseTop r v hn = divRemBasecase r.toSlice v hn := by
      unfold divRemBasecaseTop
      rw [dite_eq_right hs]
    rw [e]
    exact divRemBasecase_spec r.toSlice v hn hvt

end Bignum
