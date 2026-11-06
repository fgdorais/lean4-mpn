/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Schoolbook
public import MPN.Div.ByLimb
public import MPN.Shift

/-!
# Schoolbook division with normalization, for limbs of any width

`divRemN t t₂ a ao m b bo n` divides the `m` limbs of `a` from `ao` by the `2 ≤ n ≤ m` limbs of
`b` from `bo`, whose top limb is not zero, like GMP's `mpn_tdiv_qr` below its thresholds of
division by blocks: `a` and `b` are shifted left by the `s` bits that set the top bit of `b`, `a`
into a new array of `m + 1` limbs, which `divLoop2In` divides in place, and `b` into a new array
unless `s = 0`. The quotient and the remainder, shifted back, are copied out of the array of the
division into new arrays of `m + 1 - n` and `n` limbs.
-/

namespace MPN.Schoolbook

open WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

omit F in
/-- Limbs `0` to `n - 1` of new zero limbs, `n ≤ k`, within the bounds of a loop. -/
public theorem zeros_bound {n : USize} {k : Nat} (h : n.toNat ≤ k ∧ k < USize.size) :
    LoopBound (R.zeros k) 0 n :=
  ⟨by rw [R.size_zeros]; simp; lia, by simp; lia⟩

omit R F in
/-- `n - j < n` for `1 ≤ j ≤ n`. -/
public theorem usub_lt {n j : USize} (h₁ : 1 ≤ j.toNat) (h : j.toNat ≤ n.toNat) : n - j < n :=
  USize.lt_iff_toNat_lt.2 (by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 h)]; lia)

omit R F in
/-- Limb `n - j` of a window from `vs`, as an index. -/
public theorem toNat_add_sub {arr : A} {vs n j : USize} (hv : LoopBound arr vs n)
    (h : j.toNat ≤ n.toNat) : (vs + (n - j)).toNat = vs.toNat + n.toNat - j.toNat := by
  have hs : (n - j).toNat = n.toNat - j.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 h)
  rw [USize.toNat_add_of_lt (by rw [hs]; have := hv.2; lia), hs]
  lia

variable (A) in
/--
The division of the `i + n` limbs of `w` by the `n ≥ 2` limbs of `v` from `vs`, normalized, in
place, by `divLoop2In` with the reciprocal of the top limbs of `v` from `t` limbs and two rows
per pass from `t₂` limbs.
-/
@[inline, expose] public def loopN (t t₂ : USize) (w v : A) (vs n : USize) (hv : LoopBound v vs n)
    (hn : 2 ≤ n.toNat) (i : USize) : A :=
  let v₁ := R.uget v (vs + (n - 1)) (hv.uset_bound (usub_lt (by simp) (by simp; lia)))
  let v₂ := R.uget v (vs + (n - 2)) (hv.uset_bound (usub_lt (by rw [toNat_two]; lia)
    (by rw [toNat_two]; lia)))
  let v₃ := if h : 3 ≤ n.toNat then
      R.uget v (vs + (n - 3)) (hv.uset_bound (usub_lt (by rw [toNat_three]; lia)
        (by rw [toNat_three]; lia)))
    else R.zero
  divLoop2In w v vs n hv v₁ v₂ v₃ (divRecip32 A t n v₁ v₂) t₂ i

/-- The quotient of the division in `w`, limbs `n` to `n + k - 1`, copied out. -/
@[inline, expose] public def quotN (w : A) (n k : USize) : A :=
  R.extract w n.toNat (n.toNat + k.toNat)

/-- The remainder of the division in `w`, limbs `0` to `n - 1`, shifted right by `s` bits. -/
@[inline, expose] public def remN (w : A) (n : USize) (s : L) (h : LoopBound w 0 n) (hn : 0 < n) :
    A :=
  if R.isZero s then R.extract w 0 n.toNat
  else (rshiftW (R.zeros n.toNat) 0 w 0 n s (zeros_bound (by have := h.2; simp at this; lia)) h hn).1

/-- The quotient and the remainder of the division in `w`. -/
@[inline, expose] public def resultsN (w : A) (n k : USize) (s : L) (hn : 0 < n) : A × A :=
  if h : LoopBound w 0 n then (quotN w n k, remN w n s h hn) else (w, w)

/--
`divRemN` with the shift `s` that sets the top bit of `b`: `a` copied if `s = 0`, else `a` and `b`
shifted left by `s` bits.
-/
@[inline, expose] public def divRemS (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) (s : Nat) : A × A :=
  let k := m + 1 - n
  let s' := R.ofUSize s.toUSize
  have hn₀ : 0 < n := USize.lt_iff_toNat_lt.2 (by simp; lia)
  if s = 0 then
    resultsN (loopN A t t₂ (copyW (R.zeros (m.toNat + 1)) 0 a ao m (zeros_bound (by lia)) ha) b bo
      n hb hn k) n k s' hn₀
  else
    let p := lshiftW (R.zeros (m.toNat + 1)) 0 a ao m s' (zeros_bound (by lia)) ha
    let v := (lshiftW (R.zeros n.toNat) 0 b bo n s' (zeros_bound (by lia)) hb).1
    resultsN (loopN A t t₂ (R.uset p.1 m p.2 (by rw [size_lshiftW, R.size_zeros]; lia)) v 0 n
      ⟨by rw [size_lshiftW, R.size_zeros]; simp, by simp; lia⟩ hn k) n k s' hn₀

/--
`a / b` and `a % b`, for `a` of `m` limbs from `ao` and `b` of `2 ≤ n ≤ m` limbs from `bo` with a
nonzero top limb: the quotient in `m + 1 - n` limbs and the remainder in `n` limbs.
-/
@[expose] public def divRemN (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) : A × A :=
  divRemS t t₂ a ao m b bo n ha hb hn hnm hU
    (LA.w - 1 - R.log2 (R.uget b (bo + (n - 1)) (hb.uset_bound (usub_lt (by simp) (by simp; lia)))))

/-! ## Proofs -/

omit F in
/-- `extract` copies the `k` limbs of `w` from `i`. -/
public theorem extract_spec (w : A) (i k : Nat) (h : i + k ≤ LA.size w) :
    LA.size (R.extract w i (i + k)) = k ∧
      LimbArray.valAt (R.extract w i (i + k)) 0 k = LimbArray.valAt w i k := by
  have hs : LA.size (R.extract w i (i + k)) = k := by rw [R.size_extract]; lia
  refine ⟨hs, ?_⟩
  have key : ∀ c j, j + c ≤ k → LimbArray.valAt (R.extract w i (i + k)) j c =
      LimbArray.valAt w (i + j) c := by
    intro c
    induction c with
    | zero => intro j _; simp
    | succ c ih =>
      intro j hj
      rw [LimbArray.valAt_succ, LimbArray.valAt_succ, R.get_extract _ _ _ _ (by rw [hs]; lia),
        ih (j + 1) (by lia), Nat.add_assoc]
  have := key k 0 (by lia)
  rwa [Nat.add_zero] at this

omit F in
/-- `quotN` takes limbs `n` to `n + k - 1` of `w`, its top limbs. -/
public theorem quotN_spec (w : A) (n k : USize) (hs : LA.size w = n.toNat + k.toNat) :
    LA.size (quotN w n k) = k.toNat ∧
      LimbArray.valAt (quotN w n k) 0 k.toNat = LimbArray.valAt w n.toNat k.toNat :=
  extract_spec w n.toNat k.toNat (by lia)

/-- `remN` takes limbs `0` to `n - 1` of `w` shifted right by `s` bits. -/
public theorem remN_spec (w : A) (n : USize) (s : L) (h : LoopBound w 0 n) (hn : 0 < n)
    (hs : LA.val s < LA.w) :
    LA.size (remN w n s h hn) = n.toNat ∧
      LimbArray.valAt (remN w n s h hn) 0 n.toNat =
        LimbArray.valAt w 0 n.toNat / 2 ^ LA.val s := by
  have hn' : n.toNat ≤ n.toNat ∧ n.toNat < USize.size := ⟨Nat.le_refl _, n.toNat_lt_size⟩
  rw [remN]
  split
  · rename_i hz
    have := extract_spec w 0 n.toNat (by have := h.1; simp at this; lia)
    rw [Nat.zero_add] at this
    rw [(R.isZero_iff s).1 hz, Nat.pow_zero, Nat.div_one]
    exact this
  · rename_i hz
    have hs₀ : 0 < LA.val s := Nat.pos_of_ne_zero fun e => hz ((R.isZero_iff s).2 e)
    obtain ⟨r₁, -, r₃, r₄⟩ :=
      rshiftW_spec (R.zeros n.toNat) 0 w 0 n s (zeros_bound hn') h hn hs₀ hs
    rw [R.size_zeros] at r₁
    simp only [USize.toNat_zero] at r₃
    refine ⟨r₁, ?_⟩
    rw [← r₃, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt r₄, Nat.add_zero]

/-- `resultsN` takes the quotient and the remainder of the division in `w`. -/
public theorem resultsN_spec (w : A) (n k : USize) (s : L) (hn : 0 < n) (hs : LA.val s < LA.w)
    (hsz : LA.size w = n.toNat + k.toNat) :
    LA.size (resultsN w n k s hn).1 = k.toNat ∧
      LimbArray.valAt (resultsN w n k s hn).1 0 k.toNat = LimbArray.valAt w n.toNat k.toNat ∧
      LA.size (resultsN w n k s hn).2 = n.toNat ∧
      LimbArray.valAt (resultsN w n k s hn).2 0 n.toNat =
        LimbArray.valAt w 0 n.toNat / 2 ^ LA.val s := by
  have h : LoopBound w 0 n := ⟨by simp; lia, by simp; lia⟩
  rw [resultsN, dite_eq_left h]
  obtain ⟨q₁, q₂⟩ := quotN_spec w n k hsz
  obtain ⟨r₁, r₂⟩ := remN_spec w n s h hn hs
  exact ⟨q₁, q₂, r₁, r₂⟩

/-- `loopN` divides like `divLoop2In`. -/
public theorem loopN_spec (t t₂ : USize) (w v : A) (vs n : USize) (hv : LoopBound v vs n)
    (hn : 2 ≤ n.toNat) (i : USize) (hk : i.toNat + n.toNat ≤ LA.size w)
    (hU : LA.size w < USize.size) (hv₀ : 0 < LimbArray.valAt v vs.toNat n.toNat)
    (hR : LimbArray.valAt w 0 (i.toNat + n.toNat) <
      LimbArray.valAt v vs.toNat n.toNat * 2 ^ (LA.w * i.toNat)) :
    LA.size (loopN A t t₂ w v vs n hv hn i) = LA.size w ∧
      LimbArray.valAt v vs.toNat n.toNat *
          LimbArray.valAt (loopN A t t₂ w v vs n hv hn i) n.toNat i.toNat +
          LimbArray.valAt (loopN A t t₂ w v vs n hv hn i) 0 n.toNat =
        LimbArray.valAt w 0 (i.toNat + n.toNat) ∧
      LimbArray.valAt (loopN A t t₂ w v vs n hv hn i) 0 n.toNat <
        LimbArray.valAt v vs.toNat n.toNat := by
  have e₁ := toNat_add_sub hv (j := 1) (by simp; lia)
  have e₂ := toNat_add_sub hv (j := 2) (by rw [toNat_two]; lia)
  have e₃ := fun h3 : 3 ≤ n.toNat => toNat_add_sub hv (j := 3) (by rw [toNat_three]; lia)
  rw [USize.toNat_one] at e₁
  rw [toNat_two] at e₂
  simp only [toNat_three] at e₃
  obtain ⟨l₁, -, l₃, l₄⟩ := divLoop2In_spec w v vs n hv
    (R.uget v (vs + (n - 1)) (hv.uset_bound (usub_lt (by simp) (by simp; lia))))
    (R.uget v (vs + (n - 2)) (hv.uset_bound (usub_lt (by rw [toNat_two]; lia)
      (by rw [toNat_two]; lia))))
    (if h : 3 ≤ n.toNat then
      R.uget v (vs + (n - 3)) (hv.uset_bound (usub_lt (by rw [toNat_three]; lia)
        (by rw [toNat_three]; lia)))
    else R.zero) _ t₂ i hn hk hU hv₀
    (by rw [R.uget_eq, e₁]) (by rw [R.uget_eq, e₂])
    (fun h3 => by rw [dite_eq_left h3, R.uget_eq, e₃ h3]) hR
  exact ⟨l₁, l₃, l₄⟩

/--
The division after the normalization: if `w` holds `X 2ˢ` in `k + n` limbs and `v` holds `Y 2ˢ`
in `n` limbs, with `X < Y βᵏ`, then the quotient is `X / Y` and the remainder `X % Y`.
-/
public theorem coreN_spec (t t₂ : USize) (w v : A) (vs n k : USize) (hv : LoopBound v vs n)
    (hn : 2 ≤ n.toNat) (hn₀ : 0 < n) (s : L) (hs : LA.val s < LA.w) (X Y : Nat)
    (hsz : LA.size w = k.toNat + n.toNat) (hU : LA.size w < USize.size)
    (hV : LimbArray.valAt v vs.toNat n.toNat = Y * 2 ^ LA.val s) (hY : 0 < Y)
    (hW : LimbArray.valAt w 0 (k.toNat + n.toNat) = X * 2 ^ LA.val s)
    (hX : X < Y * 2 ^ (LA.w * k.toNat)) :
    LA.size (resultsN (loopN A t t₂ w v vs n hv hn k) n k s hn₀).1 = k.toNat ∧
      LimbArray.valAt (resultsN (loopN A t t₂ w v vs n hv hn k) n k s hn₀).1 0 k.toNat = X / Y ∧
      LA.size (resultsN (loopN A t t₂ w v vs n hv hn k) n k s hn₀).2 = n.toNat ∧
      LimbArray.valAt (resultsN (loopN A t t₂ w v vs n hv hn k) n k s hn₀).2 0 n.toNat =
        X % Y := by
  have hS := Nat.two_pow_pos (LA.val s)
  have hVpos : 0 < Y * 2 ^ LA.val s := Nat.mul_pos hY hS
  obtain ⟨l₁, l₂, l₃⟩ := loopN_spec t t₂ w v vs n hv hn k (by lia) hU (by rw [hV]; exact hVpos)
    (by
      rw [hW, hV, Nat.mul_right_comm]
      exact Nat.mul_lt_mul_of_pos_right hX hS)
  rw [hV, hW] at l₂
  rw [hV] at l₃
  obtain ⟨r₁, r₂, r₃, r₄⟩ := resultsN_spec (loopN A t t₂ w v vs n hv hn k) n k s hn₀ hs
    (by rw [l₁, hsz, Nat.add_comm])
  have hQ := Nat.mul_div_mul_right X Y hS
  have hR := Nat.mul_mod_mul_right (2 ^ LA.val s) X Y
  rw [← l₂, Nat.mul_add_div hVpos, Nat.div_eq_of_lt l₃, Nat.add_zero] at hQ
  rw [← l₂, Nat.mul_add_mod, Nat.mod_eq_of_lt l₃] at hR
  refine ⟨r₁, by rw [r₂, hQ], r₃, ?_⟩
  rw [r₄, hR, Nat.mul_div_cancel _ hS]

omit R F in
/-- The bounds of a divisor of `n` limbs whose top limb `T ≠ 0` has `⌊log₂ T⌋ = L`. -/
private theorem top_bounds (b : A) (bo n : Nat) (hn : 1 ≤ n)
    (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    2 ^ (LA.w * (n - 1)) ≤ LimbArray.valAt b bo n ∧
      LimbArray.valAt b bo n <
        2 ^ (LA.w * (n - 1)) * 2 ^ ((LA.val (LA.get b (bo + n - 1))).log2 + 1) := by
  have e := LimbArray.valAt_add b bo (n - 1) 1
  rw [show n - 1 + 1 = n by lia, LimbArray.valAt_one,
    show bo + (n - 1) = bo + n - 1 by lia] at e
  rw [e]
  have hlo := LimbArray.valAt_lt b bo (n - 1)
  have hlog := Nat.lt_log2_self (n := LA.val (LA.get b (bo + n - 1)))
  generalize LA.val (LA.get b (bo + n - 1)) = T at *
  generalize LimbArray.valAt b bo (n - 1) = Lo at *
  generalize 2 ^ (LA.w * (n - 1)) = P at *
  have h₁ := Nat.mul_le_mul_left P (show 1 ≤ T by lia)
  have h₂ := Nat.mul_le_mul_left P (show T + 1 ≤ 2 ^ (T.log2 + 1) from hlog)
  rw [Nat.mul_add, Nat.mul_one] at h₂
  constructor <;> lia

omit R F in
/-- New zero limbs with the `m` limbs of `X` written below the top one, which stays `0`. -/
private theorem valAt_top_zero (w : A) (m : Nat)
    (hz : LA.val (LA.get w m) = 0) :
    LimbArray.valAt w 0 (m + 1) = LimbArray.valAt w 0 m := by
  rw [LimbArray.valAt_add, LimbArray.valAt_one, Nat.zero_add, hz, Nat.mul_zero, Nat.add_zero]

/-- `divRemN` divides: the quotient in `m + 1 - n` limbs and the remainder in `n` limbs. -/
public theorem divRemN_spec (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) (htop : LA.val (LA.get b (bo.toNat + n.toNat - 1)) ≠ 0) :
    LA.size (divRemN t t₂ a ao m b bo n ha hb hn hnm hU).1 = m.toNat + 1 - n.toNat ∧
      LimbArray.valAt (divRemN t t₂ a ao m b bo n ha hb hn hnm hU).1 0 (m.toNat + 1 - n.toNat) =
        LimbArray.valAt a ao.toNat m.toNat / LimbArray.valAt b bo.toNat n.toNat ∧
      LA.size (divRemN t t₂ a ao m b bo n ha hb hn hnm hU).2 = n.toNat ∧
      LimbArray.valAt (divRemN t t₂ a ao m b bo n ha hb hn hnm hU).2 0 n.toNat =
        LimbArray.valAt a ao.toNat m.toNat % LimbArray.valAt b bo.toNat n.toNat := by
  have hm1 : (m + 1).toNat = m.toNat + 1 :=
    (USize.toNat_add_of_lt (a := m) (b := 1) (by rw [USize.toNat_one]; lia)).trans
      (by rw [USize.toNat_one])
  have hk : (m + 1 - n).toNat = m.toNat + 1 - n.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hm1]; lia)), hm1]
  have hwU : LA.w < USize.size := by rw [← R.toNat_wU]; exact R.wU.toNat_lt_size
  have hwB : LA.w < 2 ^ LA.w := Nat.lt_two_pow_self
  have htopI := toNat_add_sub hb (j := 1) (by simp; lia)
  rw [USize.toNat_one] at htopI
  -- The top limb `T` of `b`, its `⌊log₂ T⌋ = L` and the shift `S`.
  have hT := LA.val_lt (LA.get b (bo.toNat + n.toNat - 1))
  have hL := (Nat.log2_lt htop).2 hT
  obtain ⟨hb₁, hb₂⟩ := top_bounds b bo.toNat n.toNat (by lia) htop
  generalize hLd : (LA.val (LA.get b (bo.toNat + n.toNat - 1))).log2 = L at hL hb₂
  have hβn : 2 ^ (LA.w * (n.toNat - 1)) * 2 ^ (L + 1) * 2 ^ (LA.w - 1 - L) =
      2 ^ (LA.w * n.toNat) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1
    have : LA.w * n.toNat = LA.w * (n.toNat - 1) + LA.w := by
      rw [← Nat.mul_succ]; congr 1; lia
    lia
  have hbS : LimbArray.valAt b bo.toNat n.toNat * 2 ^ (LA.w - 1 - L) < 2 ^ (LA.w * n.toNat) := by
    rw [← hβn]; exact Nat.mul_lt_mul_of_pos_right hb₂ (Nat.two_pow_pos _)
  have hBpos : 0 < LimbArray.valAt b bo.toNat n.toNat :=
    Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hb₁
  -- The dividend is below `b βᵏ`.
  have hX : LimbArray.valAt a ao.toNat m.toNat <
      LimbArray.valAt b bo.toNat n.toNat * 2 ^ (LA.w * (m + 1 - n).toNat) := by
    have hA := LimbArray.valAt_lt a ao.toNat m.toNat
    have e : 2 ^ (LA.w * m.toNat) =
        2 ^ (LA.w * (n.toNat - 1)) * 2 ^ (LA.w * (m + 1 - n).toNat) := by
      rw [← Nat.pow_add, hk]; congr 1
      rw [← Nat.mul_add]; congr 1; lia
    rw [e] at hA
    exact Nat.lt_of_lt_of_le hA (Nat.mul_le_mul_right _ hb₁)
  have hsv : LA.val (R.ofUSize (LA.w - 1 - L).toUSize) = LA.w - 1 - L := by
    rw [R.val_ofUSize, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia), Nat.mod_eq_of_lt (by lia)]
  have hsz₀ : ∀ k, LA.size (R.zeros k) = k := R.size_zeros
  unfold divRemN
  rw [R.uget_eq, htopI, R.log2_eq, hLd]
  unfold divRemS
  dsimp only
  split
  · -- `b` is normalized: `a` is copied.
    rename_i hS
    have hs₀ : LA.val (R.ofUSize (LA.w - 1 - L).toUSize) = 0 := by rw [hsv, hS]
    obtain ⟨c₁, c₂, c₃⟩ := copyW_spec (R.zeros (m.toNat + 1)) 0 a ao m (zeros_bound (by lia)) ha
    rw [hsz₀] at c₁
    simp only [USize.toNat_zero] at c₂ c₃
    have hW : LimbArray.valAt (copyW (R.zeros (m.toNat + 1)) 0 a ao m (zeros_bound (by lia)) ha) 0
        ((m + 1 - n).toNat + n.toNat) =
        LimbArray.valAt a ao.toNat m.toNat * 2 ^ LA.val (R.ofUSize (LA.w - 1 - L).toUSize) := by
      rw [hs₀, Nat.pow_zero, Nat.mul_one, hk, show m.toNat + 1 - n.toNat + n.toNat =
        m.toNat + 1 by lia, valAt_top_zero _ _ (by rw [c₂ _ (.inr (by lia)), R.val_get_zeros]),
        c₃]
    obtain ⟨r₁, r₂, r₃, r₄⟩ := coreN_spec t t₂ _ b bo n (m + 1 - n) hb hn _ _
      (by rw [hs₀]; exact LA.w_pos)
      (LimbArray.valAt a ao.toNat m.toNat) (LimbArray.valAt b bo.toNat n.toNat)
      (by rw [c₁, hk]; lia) (by rw [c₁]; exact hU)
      (by rw [hs₀, Nat.pow_zero, Nat.mul_one]) hBpos hW hX
    rw [hk] at r₁ r₂
    exact ⟨r₁, r₂, r₃, r₄⟩
  · -- `a` and `b` shifted left by `S` bits.
    rename_i hS
    have hs₀ : 0 < LA.val (R.ofUSize (LA.w - 1 - L).toUSize) := by rw [hsv]; lia
    have hs : LA.val (R.ofUSize (LA.w - 1 - L).toUSize) < LA.w := by rw [hsv]; lia
    obtain ⟨v₁, -, v₃⟩ := lshiftW_spec (R.zeros n.toNat) 0 b bo n
      (R.ofUSize (LA.w - 1 - L).toUSize) (zeros_bound (by lia)) hb hs₀ hs
    obtain ⟨p₁, p₂, p₃⟩ := lshiftW_spec (R.zeros (m.toNat + 1)) 0 a ao m
      (R.ofUSize (LA.w - 1 - L).toUSize) (zeros_bound (by lia)) ha hs₀ hs
    rw [hsz₀] at v₁ p₁
    simp only [USize.toNat_zero] at v₃ p₂ p₃
    rw [hsv] at v₃ p₃
    -- No bits out of the top of `b 2ˢ`.
    have hV : LimbArray.valAt (lshiftW (R.zeros n.toNat) 0 b bo n
        (R.ofUSize (LA.w - 1 - L).toUSize) (zeros_bound (by lia)) hb).1 0 n.toNat =
        LimbArray.valAt b bo.toNat n.toNat * 2 ^ LA.val (R.ofUSize (LA.w - 1 - L).toUSize) := by
      rw [hsv]
      have hc : LA.val (lshiftW (R.zeros n.toNat) 0 b bo n (R.ofUSize (LA.w - 1 - L).toUSize)
          (zeros_bound (by lia)) hb).2 = 0 := by
        rcases Nat.eq_zero_or_pos (LA.val (lshiftW (R.zeros n.toNat) 0 b bo n
          (R.ofUSize (LA.w - 1 - L).toUSize) (zeros_bound (by lia)) hb).2) with h | h
        · exact h
        · have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat)) h; lia
      rw [hc, Nat.mul_zero, Nat.add_zero] at v₃
      exact v₃
    have hW : LimbArray.valAt (R.uset (lshiftW (R.zeros (m.toNat + 1)) 0 a ao m
        (R.ofUSize (LA.w - 1 - L).toUSize) (zeros_bound (by lia)) ha).1 m
        (lshiftW (R.zeros (m.toNat + 1)) 0 a ao m (R.ofUSize (LA.w - 1 - L).toUSize)
          (zeros_bound (by lia)) ha).2 (by rw [p₁]; lia)) 0 ((m + 1 - n).toNat + n.toNat) =
        LimbArray.valAt a ao.toNat m.toNat * 2 ^ LA.val (R.ofUSize (LA.w - 1 - L).toUSize) := by
      rw [hsv, hk, show m.toNat + 1 - n.toNat + n.toNat = m.toNat + 1 by lia,
        LimbArray.valAt_add, LimbArray.valAt_one, Nat.zero_add, R.get_uset,
        valAt_uset_of _ _ _ _ _ _ (.inr (by lia))]
      simp only [↓reduceIte]
      rw [← p₃]
    obtain ⟨r₁, r₂, r₃, r₄⟩ := coreN_spec t t₂ _ _ 0 n (m + 1 - n) _ hn _ _ hs
      (LimbArray.valAt a ao.toNat m.toNat) (LimbArray.valAt b bo.toNat n.toNat)
      (by rw [R.size_uset, p₁, hk]; lia) (by rw [R.size_uset, p₁]; exact hU)
      (by simpa using hV) hBpos hW hX
    rw [hk] at r₁ r₂
    exact ⟨r₁, r₂, r₃, r₄⟩

end MPN.Schoolbook
