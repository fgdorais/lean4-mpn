/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Mul.Limb
public import MPN32.Basic
public import MPN.Div.Basecase
public import MPN.Div.ByLimb
public import MPN32.Settings

/-!
# Schoolbook division

`divRemBasecase t u v` divides `u` by a divisor `v` of at least two limbs with a nonzero top limb,
by Knuth's Algorithm D, like GMP's schoolbook division, through `main`'s `MPN.Div.Basecase` on
`UInt32Array` (`Schoolbook.divRemN`): `u` and `v` normalized by a shift, then two quotient limbs
per step from the top down, by one pass of two rows, from `config.div2Rows` limbs in the divisor,
in one array, and the remainder shifted back. Its multiply-subtract pass carries the biased borrow
of `subMulBiased`.

The estimate of a quotient limb from the top three limbs of the window and the top two of the
divisor (`qEstimate3`) is the one of `Div.Two`'s division by two limbs.
-/

open ScalarArray

namespace MPN.W32

/-! ## Arithmetic facts -/

/-- A divisor with top limb `vt` is at least `vt βⁿ⁻¹`. -/
public theorem top_limb_le (v : UInt32Array.Slice) (hn : 1 ≤ v.size) :
    (v[v.size - 1]'(by lia)).toNat * 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
  have h := UInt32Array.valAt_add v.array v.start (v.size - 1) 1
  rw [show v.size - 1 + 1 = v.size by lia, UInt32Array.valAt_one,
    ← UInt32Array.Slice.getElem_eq_getElem! v (v.size - 1) (by lia)] at h
  rw [toNat_eq_valAt, h, Nat.mul_comm]
  exact Nat.le_add_left _ _

/-! ## The quotient estimate -/

/-- `min ⌊(wt β + wn) / vt⌋ (β - 1)`, the estimate of a quotient limb. -/
@[inline, expose] public def qEstimate (wt wn vt : UInt32) : UInt32 :=
  let e : UInt64 := (wt.toUInt64 * 4294967296 + wn.toUInt64) / vt.toUInt64
  if e < 4294967296 then e.toUInt32 else 0xFFFFFFFF

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
  have hgt : qt * (vt * B + vs) < q * (vt * B + vs) := by lia
  have hq := Nat.lt_of_mul_lt_mul_right hgt
  refine ⟨hq, ?_⟩
  have : vt ≤ q * vt := Nat.le_mul_of_pos_left _ (by lia)
  rw [Nat.sub_mul, Nat.one_mul]
  lia

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
        rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
      have hc' : r.toNat * 2 ^ 32 + wl.toNat < q.toNat * vs.toNat := by
        have := UInt64.lt_iff_toNat_lt.1 hc
        rwa [hsh, hmul] at this
      obtain ⟨hgt, hsum⟩ := refine_arith hT hW hc'
      have hq1 : (q - 1).toNat = q.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; lia)]
        simp
      have hrv : (r + vt.toUInt64).toNat = r.toNat + vt.toNat := by
        rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
        exact Nat.mod_eq_of_lt (by simp; lia)
      exact ⟨by rw [hq1, hrv]; exact hsum, by rw [hq1]; lia⟩
    · exact ⟨hT, hq⟩
  · exact ⟨hT, hq⟩

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
    lia
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

/-! ## Schoolbook division -/

private theorem toNat_toUSize' {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a := by
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The limbs of a slice whose end `USize` indices reach, as a loop bound. -/
private theorem slice_bound (v : UInt32Array.Slice) (h : v.start + v.size < USize.size) :
    MPN.WordArray.LoopBound v.array v.start.toUSize v.size.toUSize := by
  have := v.stop_le_array_size
  have := v.start_le_stop
  have hs := v.size_eq
  have h₁ : v.start.toUSize.toNat = v.start := toNat_toUSize' (by lia)
  have h₂ : v.size.toUSize.toNat = v.size := toNat_toUSize' (by lia)
  show v.start.toUSize.toNat + v.size.toUSize.toNat ≤ v.array.size ∧
    v.start.toUSize.toNat + v.size.toUSize.toNat < USize.size
  rw [h₁, h₂]
  exact ⟨by lia, by lia⟩

/-- `config.div2Rows` as a `USize`, at most `4294967295`. -/
public def div2RowsU : USize := (min config.div2Rows 4294967295).toUSize

/--
`u / v` and `u % v` by Knuth's Algorithm D, for a divisor of at least two limbs, untrimmed, by
`main`'s `Schoolbook.divRemN`: `u` and `v` normalized by a shift, the quotient limbs from the top
down in one array, from `t` limbs in the divisor by GMP's 3-by-2 steps with the reciprocal
`WordArray.recip32`, checked, and the remainder shifted back. It is exact when the top limb of `v`
is not zero. A dividend of fewer limbs than `v` is its own remainder; were the slices too large for
`USize` indices, which none is, the results would come from the values instead.
-/
public def divRemBasecase (t : USize) (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  if h : v.size ≤ u.size ∧ u.start + u.size + 1 < USize.size ∧ v.start + v.size < USize.size then
    Schoolbook.divRemN t div2RowsU u.array u.start.toUSize u.size.toUSize v.array v.start.toUSize
      v.size.toUSize (slice_bound u (by lia)) (slice_bound v h.2.2)
      (by rw [toNat_toUSize' (by lia)]; exact hn)
      (by rw [toNat_toUSize' (by lia), toNat_toUSize' (by lia)]; exact h.1)
      (by rw [toNat_toUSize' (by lia)]; lia)
  else if u.size < v.size then (.empty, u.copy)
  else (ofNat (toNat u / toNat v), ofNat (toNat u % toNat v))

/-- `divRemBasecase` divides: `u = q v + r` with `r < v`. -/
public theorem divRemBasecase_spec (t : USize) (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemBasecase t u v hn).1 * toNat v + toNat (divRemBasecase t u v hn).2 = toNat u ∧
      toNat (divRemBasecase t u v hn).2 < toNat v := by
  have hvt' : 0 < (v[v.size - 1]'(by lia)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hv₀ : 0 < toNat v := by
    have := top_limb_le v (by lia)
    have := Nat.two_pow_pos (32 * (v.size - 1))
    have := Nat.mul_le_mul_right (2 ^ (32 * (v.size - 1))) hvt'
    lia
  suffices hqr : toNat (divRemBasecase t u v hn).1 = toNat u / toNat v ∧
      toNat (divRemBasecase t u v hn).2 = toNat u % toNat v by
    rw [hqr.1, hqr.2, Nat.mul_comm]
    exact ⟨Nat.div_add_mod .., Nat.mod_lt _ hv₀⟩
  by_cases h : v.size ≤ u.size ∧ u.start + u.size + 1 < USize.size ∧
      v.start + v.size < USize.size
  · rw [divRemBasecase, dite_eq_left h]
    have hus := toNat_toUSize' (a := u.start) (by lia)
    have hum := toNat_toUSize' (a := u.size) (by lia)
    have hvs := toNat_toUSize' (a := v.start) (by lia)
    have hvm := toNat_toUSize' (a := v.size) (by lia)
    obtain ⟨d₁, d₂, d₃, d₄⟩ := Schoolbook.divRemN_spec t div2RowsU u.array u.start.toUSize
      u.size.toUSize v.array v.start.toUSize v.size.toUSize (slice_bound u (by lia))
      (slice_bound v h.2.2) (by rw [hvm]; exact hn) (by rw [hum, hvm]; exact h.1)
      (by rw [hum]; lia) (by
        rw [hvs, hvm]
        intro e
        apply hvt
        rw [UInt32Array.Slice.getElem_eq_getElem!,
          show v.start + (v.size - 1) = v.start + v.size - 1 by lia]
        exact UInt32.toNat_inj.1 e)
    simp only [hus, hum, hvs, hvm] at d₁ d₂ d₃ d₄
    rw [toNat_toSlice, toNat_toSlice, Nat.sub_zero, Nat.sub_zero]
    exact ⟨(congrArg (fun k => LimbArray.valAt _ 0 k) d₁).trans d₂,
      (congrArg (fun k => LimbArray.valAt _ 0 k) d₃).trans d₄⟩
  · rw [divRemBasecase, dite_eq_right h]
    by_cases hlt : u.size < v.size
    · rw [ite_eq_left hlt]
      have hu : toNat u < toNat v := by
        have := toNat_lt u
        have := top_limb_le v (by lia)
        have := Nat.mul_le_mul_right (2 ^ (32 * (v.size - 1))) hvt'
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 32 * u.size ≤ 32 * (v.size - 1)
          by lia)
        lia
      rw [Nat.div_eq_of_lt hu, Nat.mod_eq_of_lt hu]
      exact ⟨toNat_empty, toNat_copy u⟩
    · rw [ite_eq_right hlt]
      exact ⟨toNat_ofNat _, toNat_ofNat _⟩

end MPN.W32
