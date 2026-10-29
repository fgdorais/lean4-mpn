/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Limb
public import MPN.ValAt
public import MPN.Div.Schoolbook

/-!
# Schoolbook division

`divRemBasecase u v` divides `u` by a divisor `v` of at least two limbs with a nonzero top limb,
by Knuth's Algorithm D, like GMP's schoolbook division, through `main`'s `MPN.Div.Schoolbook` on
`UInt32Array` (`divLoopIn`): one quotient limb per step from the top down, in one array, the
remainder in the limbs below `n` and the quotient from limb `n` on. Its multiply-subtract pass
carries the biased borrow of `subMulBiased`. `Div` normalizes the divisor and the dividend, and
divides the latter in place with `divRemBasecaseTop` when its top limb is below the divisor's, as
it is after normalization.

The estimate of a quotient limb from the top three limbs of the window and the top two of the
divisor (`qEstimate3`) is the one of `Div.Two`'s division by two limbs.
-/

open ScalarArray

namespace MPN

/-! ## Arithmetic facts -/

/-- A divisor with top limb `vt` is at least `vt βⁿ⁻¹`. -/
public theorem top_limb_le (v : UInt32Array.Slice) (hn : 1 ≤ v.size) :
    (v[v.size - 1]'(by lia)).toNat * 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
  have h := ofLimbs_take_add_one v.copy.toList (v.size - 1) (by simp; lia)
  rw [show v.size - 1 + 1 = v.size by lia, List.take_of_length_le (by simp)] at h
  simp only [toNat, h, UInt32Array.getElem_toList, UInt32Array.Slice.getElem_copy]
  rw [Nat.mul_comm]
  lia

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

/-! ## The loop in one array -/

/-- The value of a range of limbs, as a list. -/
private theorem ofLimbs_extract (a : UInt32Array) (i j : Nat) :
    ofLimbs (a.extract i j).toList = a.valAt i (j - i) := by
  rw [UInt32Array.toList_extract, List.extract_eq_take_drop, ofLimbs_drop_take]

private theorem toNat_toUSize' {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a := by
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The limbs of `v`, which indices of `USize` reach when the array is within them. -/
private theorem slice_bound (v : UInt32Array.Slice) (h : v.array.usize.toNat = v.array.size) :
    MPN.WordArray.LoopBound v.array v.start.toUSize v.size.toUSize := by
  have := v.array.usize.toNat_lt_size
  have := v.stop_le_array_size
  have := v.start_le_stop
  have hs := v.size_eq
  have h₁ : v.start.toUSize.toNat = v.start := toNat_toUSize' (by lia)
  have h₂ : v.size.toUSize.toNat = v.size := toNat_toUSize' (by lia)
  show v.start.toUSize.toNat + v.size.toUSize.toNat ≤ v.array.size ∧
    v.start.toUSize.toNat + v.size.toUSize.toNat < USize.size
  rw [h₁, h₂]
  exact ⟨by lia, by lia⟩

/--
The quotient limbs below `k`, from the top down, in one array, by `main`'s
`Schoolbook.divLoopIn`: the remainder stays in the limbs below `k + n` and each quotient limb goes
into the limb its step frees, so that at the end the limbs below `n` are the remainder and the
limbs from `n` on are the quotient. Its indices are `USize`s; were an array too large for them,
which none is, the limbs would be written from the values instead (`LimbArray.writeNat`).
-/
def divLoopIn (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (k : Nat) (r : UInt32Array)
    (_hr : k + v.size ≤ r.size) : UInt32Array :=
  if h : r.usize.toNat = r.size ∧ v.array.usize.toNat = v.array.size then
    Schoolbook.divLoopIn r v.array v.start.toUSize v.size.toUSize (slice_bound v h.2)
      (v[v.size - 1]'(by lia)) (v[v.size - 2]'(by lia)) 0 k.toUSize
  else
    LimbArray.writeNat (LimbArray.writeNat r 0 v.size (r.valAt 0 (k + v.size) % toNat v)) v.size k
      (r.valAt 0 (k + v.size) / toNat v)

private theorem divLoopIn_spec (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) (k : Nat) (r : UInt32Array) (hr : r.size = k + v.size)
    (hbound : ofLimbs r.toList < toNat v * 2 ^ (32 * k)) :
    (divLoopIn v hn k r (by lia)).size = r.size ∧
      ofLimbs ((divLoopIn v hn k r (by lia)).extract 0 v.size).toList < toNat v ∧
      ofLimbs ((divLoopIn v hn k r (by lia)).extract 0 v.size).toList +
          toNat v * ofLimbs ((divLoopIn v hn k r (by lia)).extract v.size r.size).toList =
        ofLimbs r.toList := by
  have hvt' : 1 ≤ (v[v.size - 1]'(by lia)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hv₀ : 0 < toNat v := by
    have := top_limb_le v (by lia)
    have := Nat.two_pow_pos (32 * (v.size - 1))
    have := Nat.mul_le_mul_right (2 ^ (32 * (v.size - 1))) hvt'
    lia
  have hR : ofLimbs r.toList = r.valAt 0 (k + v.size) := by
    rw [← toNat_toSlice, toNat_array_eq_valAt, hr]
  rw [ofLimbs_extract, ofLimbs_extract, hR, show r.size - v.size = k by lia, Nat.sub_zero]
  rw [hR] at hbound
  unfold divLoopIn
  split
  · rename_i h
    have hrs := r.usize.toNat_lt_size
    have has := v.array.usize.toNat_lt_size
    have := v.stop_le_array_size
    have := v.start_le_stop
    have hsz := v.size_eq
    have hn' : v.size.toUSize.toNat = v.size := toNat_toUSize' (by lia)
    have hs' : v.start.toUSize.toNat = v.start := toNat_toUSize' (by lia)
    have hk' : k.toUSize.toNat = k := toNat_toUSize' (by lia)
    have hV : toNat v = LimbArray.valAt v.array v.start v.size := toNat_eq_valAt v
    have hb' : LimbArray.valAt r 0 (k + v.size) < toNat v * 2 ^ (32 * k) := hbound
    obtain ⟨s₁, -, s₃, s₄⟩ := Schoolbook.divLoopIn_spec r v.array v.start.toUSize v.size.toUSize
      (slice_bound v h.2) (v[v.size - 1]'(by lia)) (v[v.size - 2]'(by lia)) 0 k.toUSize
      (by rw [hn']; exact hn) (by rw [hn', hk']; change k + v.size ≤ r.size; lia)
      (by change r.size < USize.size; lia) (by rw [hs', hn', ← hV]; exact hv₀)
      (by rw [hs', hn', UInt32Array.Slice.getElem_eq_getElem!]; congr 1; lia)
      (by rw [hs', hn', UInt32Array.Slice.getElem_eq_getElem!]; congr 1; lia)
      (by rw [hs', hn', hk', ← hV]; exact hb')
    simp only [hs', hn', hk', ← hV] at s₃ s₄
    exact ⟨s₁, s₄, by rw [Nat.add_comm]; exact s₃⟩
  · have hm := Nat.mod_lt (r.valAt 0 (k + v.size)) hv₀
    have hvlt : toNat v < 2 ^ (32 * v.size) := by
      rw [toNat_eq_valAt]; exact LimbArray.valAt_lt ..
    have hq : r.valAt 0 (k + v.size) / toNat v < 2 ^ (32 * k) :=
      (Nat.div_lt_iff_lt_mul hv₀).2 (by rw [Nat.mul_comm]; exact hbound)
    have hsz₁ := LimbArray.size_writeNat r 0 v.size (r.valAt 0 (k + v.size) % toNat v)
    have hsz₂ := LimbArray.size_writeNat (LimbArray.writeNat r 0 v.size
      (r.valAt 0 (k + v.size) % toNat v)) v.size k (r.valAt 0 (k + v.size) / toNat v)
    have e₁ : LimbArray.valAt (LimbArray.writeNat (LimbArray.writeNat r 0 v.size
        (r.valAt 0 (k + v.size) % toNat v)) v.size k (r.valAt 0 (k + v.size) / toNat v)) 0 v.size =
        LimbArray.valAt (LimbArray.writeNat r 0 v.size (r.valAt 0 (k + v.size) % toNat v)) 0
          v.size :=
      LimbArray.valAt_congr _ fun i _ hi => LimbArray.get_writeNat _ _ _ _ _ (.inl (by lia))
    have e₂ := LimbArray.valAt_writeNat r 0 v.size (r.valAt 0 (k + v.size) % toNat v)
      (by change 0 + v.size ≤ r.size; lia)
    have e₃ := LimbArray.valAt_writeNat (LimbArray.writeNat r 0 v.size
      (r.valAt 0 (k + v.size) % toNat v)) v.size k (r.valAt 0 (k + v.size) / toNat v)
      (by rw [hsz₁]; change v.size + k ≤ r.size; lia)
    have hlo : (LimbArray.writeNat (LimbArray.writeNat r 0 v.size
        (r.valAt 0 (k + v.size) % toNat v)) v.size k
        (r.valAt 0 (k + v.size) / toNat v)).valAt 0 v.size =
          r.valAt 0 (k + v.size) % toNat v := by
      have := Nat.mod_eq_of_lt (Nat.lt_trans hm hvlt)
      exact e₁.trans (e₂.trans this)
    have hhi : (LimbArray.writeNat (LimbArray.writeNat r 0 v.size
        (r.valAt 0 (k + v.size) % toNat v)) v.size k
        (r.valAt 0 (k + v.size) / toNat v)).valAt v.size k =
          r.valAt 0 (k + v.size) / toNat v :=
      e₃.trans (Nat.mod_eq_of_lt hq)
    have hs : (LimbArray.writeNat (LimbArray.writeNat r 0 v.size
        (r.valAt 0 (k + v.size) % toNat v)) v.size k
        (r.valAt 0 (k + v.size) / toNat v)).size = r.size := hsz₂.trans hsz₁
    refine ⟨hs, ?_, ?_⟩
    · rw [hlo]; exact hm
    · rw [hlo, hhi, Nat.add_comm]
      exact Nat.div_add_mod ..

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
    (copyPadded u (max (u.size + 1) v.size)) (by rw [size_copyPadded _ _ (by lia)]; lia)
  (a.extract v.size a.size, a.extract 0 v.size)

/-- `divRemBasecase` divides: `u = q v + r` with `r < v`. -/
public theorem divRemBasecase_spec (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemBasecase u v hn).1 * toNat v + toNat (divRemBasecase u v hn).2 = toNat u ∧
      toNat (divRemBasecase u v hn).2 < toNat v := by
  have hvt' : 1 ≤ (v[v.size - 1]'(by lia)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have htop := top_limb_le v (by lia)
  have hU := toNat_lt u
  -- `u < β^u.size ≤ β^(N - 1) = β^(n - 1) β^(N - n) ≤ v β^(N - n)`.
  have hbound : toNat u < toNat v * 2 ^ (32 * (max (u.size + 1) v.size - v.size)) := by
    have h₁ : 2 ^ (32 * u.size) ≤
        2 ^ (32 * (v.size - 1)) * 2 ^ (32 * (max (u.size + 1) v.size - v.size)) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by lia)
    have h₂ : 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
      have := Nat.mul_le_mul_right (2 ^ (32 * (v.size - 1))) hvt'
      lia
    have := Nat.mul_le_mul_right (2 ^ (32 * (max (u.size + 1) v.size - v.size))) h₂
    lia
  have hcs : (copyPadded u (max (u.size + 1) v.size)).size =
      max (u.size + 1) v.size - v.size + v.size := by
    rw [size_copyPadded _ _ (by lia)]; lia
  have hcv : ofLimbs (copyPadded u (max (u.size + 1) v.size)).toList = toNat u := by
    rw [← toNat_toSlice, toNat_copyPadded]
  have hspec := divLoopIn_spec v hn hvt (max (u.size + 1) v.size - v.size)
    (copyPadded u (max (u.size + 1) v.size)) hcs (by rw [hcv]; exact hbound)
  rw [hcv] at hspec
  obtain ⟨h₁, h₂, h₃⟩ := hspec
  simp only [divRemBasecase, toNat_toSlice]
  simp only [h₁]
  refine ⟨?_, h₂⟩
  rw [Nat.mul_comm]
  lia

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
    if r[r.size - 1]'(by lia) < v[v.size - 1]'(by lia) then
      let a := divLoopIn v hn (r.size - v.size) r (by lia)
      (a.extract v.size a.size, a.extract 0 v.size)
    else
      divRemBasecase r.toSlice v hn
  else
    divRemBasecase r.toSlice v hn

public theorem divRemBasecaseTop_spec (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemBasecaseTop r v hn).1 * toNat v + toNat (divRemBasecaseTop r v hn).2 =
        toNat r ∧
      toNat (divRemBasecaseTop r v hn).2 < toNat v := by
  by_cases hs : v.size ≤ r.size
  · by_cases htop : r[r.size - 1]'(by lia) < v[v.size - 1]'(by lia)
    · have e : divRemBasecaseTop r v hn =
          ((divLoopIn v hn (r.size - v.size) r (by lia)).extract v.size
            (divLoopIn v hn (r.size - v.size) r (by lia)).size,
          (divLoopIn v hn (r.size - v.size) r (by lia)).extract 0 v.size) := by
        unfold divRemBasecaseTop
        rw [dite_eq_left hs, ite_eq_left htop]
      rw [e]
      -- `r < βʳ⁻¹ (r_top + 1) ≤ βʳ⁻¹ v_top ≤ v βᵏ`.
      have hbound : toNat r < toNat v * 2 ^ (32 * (r.size - v.size)) := by
        have hsplit := ofLimbs_take_add_one r.toList (r.size - 1) (by simp; lia)
        rw [show r.size - 1 + 1 = r.size by lia, List.take_of_length_le (by simp)] at hsplit
        have hlow := ofLimbs_take_lt r.toList (r.size - 1)
        simp only [UInt32Array.getElem_toList] at hsplit
        have hlt : (r[r.size - 1]'(by lia)).toNat + 1 ≤ (v[v.size - 1]'(by lia)).toNat := by
          rw [UInt32.lt_iff_toNat_lt] at htop
          lia
        have hv := top_limb_le v (by lia)
        have hpow : 2 ^ (32 * (r.size - 1)) =
            2 ^ (32 * (v.size - 1)) * 2 ^ (32 * (r.size - v.size)) := by
          rw [← Nat.pow_add]; congr 1; lia
        have hv' : (v[v.size - 1]'(by lia)).toNat * 2 ^ (32 * (r.size - 1)) ≤
            toNat v * 2 ^ (32 * (r.size - v.size)) := by
          rw [hpow, ← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ hv
        have h₁ := Nat.mul_le_mul_left (2 ^ (32 * (r.size - 1))) hlt
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 ^ (32 * (r.size - 1)))
          (v[v.size - 1]'(by lia)).toNat] at h₁
        rw [toNat_toSlice]
        lia
      have hspec := divLoopIn_spec v hn hvt (r.size - v.size) r (by lia)
        (by rw [toNat_toSlice] at hbound; exact hbound)
      obtain ⟨h₁, h₂, h₃⟩ := hspec
      simp only [toNat_toSlice]
      simp only [h₁]
      refine ⟨?_, h₂⟩
      rw [Nat.mul_comm]
      lia
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

end MPN
