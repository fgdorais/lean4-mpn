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

/-! ## Normalization

`shlTop` and `shlFit` shift a dividend and a divisor left by the `s < w` bits that set the top bit
of the divisor, into new arrays, the dividend with one more limb for the bits out of its top;
`shrNew` shifts a remainder back. A shift by `0` is a copy. They serve this division and the
widths' divisions by blocks.
-/

/-- The `m` limbs of `a` from `ao` times `2ˢ`, for `s < w`, in `m + 1` new limbs. -/
@[inline, expose] public def shlTop (a : A) (ao m : USize) (ha : LoopBound a ao m)
    (hU : m.toNat + 1 < USize.size) (s : Nat) : A :=
  if s = 0 then copyW (R.zeros (m.toNat + 1)) 0 a ao m (zeros_bound (by lia)) ha
  else
    let p := lshiftW (R.zeros (m.toNat + 1)) 0 a ao m (R.ofUSize s.toUSize) (zeros_bound (by lia))
      ha
    R.uset p.1 m p.2 (by rw [size_lshiftW, R.size_zeros]; lia)

/-- The `n` limbs of `b` from `bo` times `2ˢ`, for `s < w`, in `n` new limbs, when it fits. -/
@[inline, expose] public def shlFit (b : A) (bo n : USize) (hb : LoopBound b bo n) (s : Nat) : A :=
  if s = 0 then R.extract b bo.toNat (bo.toNat + n.toNat)
  else (lshiftW (R.zeros n.toNat) 0 b bo n (R.ofUSize s.toUSize)
    (zeros_bound ⟨Nat.le_refl _, n.toNat_lt_size⟩) hb).1

/-- `⌊r / 2ˢ⌋` of the `n` limbs of `r` from `ro`, for `s < w`, in `n` new limbs. -/
@[inline, expose] public def shrNew (r : A) (ro n : USize) (hr : LoopBound r ro n) (s : Nat) : A :=
  if h : s = 0 ∨ n = 0 then R.extract r ro.toNat (ro.toNat + n.toNat)
  else (rshiftW (R.zeros n.toNat) 0 r ro n (R.ofUSize s.toUSize)
    (zeros_bound ⟨Nat.le_refl _, n.toNat_lt_size⟩) hr
    (USize.lt_iff_toNat_lt.2 (by
      have : n.toNat ≠ 0 := fun e => h (.inr (USize.toNat_inj.1 (by simpa using e)))
      simp; lia))).1

@[simp] public theorem size_shlFit (b : A) (bo n : USize) (hb : LoopBound b bo n) (s : Nat) :
    LA.size (shlFit b bo n hb s) = n.toNat := by
  rw [shlFit]
  split
  · rw [R.size_extract]; have := hb.1; lia
  · rw [size_lshiftW, R.size_zeros]

omit R F in
/-- The first `n` limbs of an array that `USize` indices reach, as a loop bound. -/
public theorem arr_bound (a : A) {n : Nat} (hn : n ≤ LA.size a) (hU : LA.size a < USize.size) :
    LoopBound a 0 n.toUSize := by
  have : n.toUSize.toNat = n := by rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]
  exact ⟨by rw [this]; simp; lia, by rw [this]; simp; lia⟩

omit R F in
public theorem toNat_toUSize_of_lt {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' h]

/-- `shlTop` on a whole array: `a 2ˢ` in `size a + 1` limbs. -/
@[inline, expose] public def shlArr (a : A) (s : Nat) : A :=
  if h : LA.size a + 1 < USize.size then
    shlTop a 0 (LA.size a).toUSize (arr_bound a (Nat.le_refl _) (by lia))
      (by rw [toNat_toUSize_of_lt (by lia)]; exact h) s
  else a

/-- `shlFit` on the first `n` limbs of an array: `b 2ˢ` in `n` limbs, when it fits. -/
@[inline, expose] public def shlFitArr (b : A) (n s : Nat) : A :=
  if h : n ≤ LA.size b ∧ LA.size b < USize.size then shlFit b 0 n.toUSize (arr_bound b h.1 h.2) s
  else b

/-- `shrNew` on a whole array: `⌊r / 2ˢ⌋` in `size r` limbs. -/
@[inline, expose] public def shrArr (r : A) (s : Nat) : A :=
  if h : LA.size r < USize.size then shrNew r 0 (LA.size r).toUSize (arr_bound r (Nat.le_refl _) h) s
  else r

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

/-- The quotient and the remainder of the division in `w`, shifted back by `s` bits. -/
@[inline, expose] public def resultsN (w : A) (n k : USize) (s : Nat) : A × A :=
  if h : LoopBound w 0 n then (quotN w n k, shrNew w 0 n h s) else (w, w)

/--
`divRemN` with the shift `s` that sets the top bit of `b`: `a` copied if `s = 0`, else `a` and `b`
shifted left by `s` bits.
-/
@[inline, expose] public def divRemS (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (_hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) (s : Nat) : A × A :=
  let k := m + 1 - n
  if s = 0 then resultsN (loopN A t t₂ (shlTop a ao m ha hU s) b bo n hb hn k) n k s
  else
    resultsN (loopN A t t₂ (shlTop a ao m ha hU s) (shlFit b bo n hb s) 0 n
      ⟨by rw [size_shlFit]; simp, by simp [n.toNat_lt_size]⟩ hn k) n k s

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

omit F in
/-- `s < w` as a limb. -/
public theorem val_shift {s : Nat} (hs : s < LA.w) : LA.val (R.ofUSize s.toUSize) = s := by
  have hwU : LA.w < USize.size := by rw [← R.toNat_wU]; exact R.wU.toNat_lt_size
  have hwB : LA.w < 2 ^ LA.w := Nat.lt_two_pow_self
  rw [R.val_ofUSize, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia), Nat.mod_eq_of_lt (by lia)]

/-- `shlTop` holds `a 2ˢ` in `m + 1` limbs. -/
public theorem shlTop_spec (a : A) (ao m : USize) (ha : LoopBound a ao m)
    (hU : m.toNat + 1 < USize.size) (s : Nat) (hs : s < LA.w) :
    LA.size (shlTop a ao m ha hU s) = m.toNat + 1 ∧
      LimbArray.valAt (shlTop a ao m ha hU s) 0 (m.toNat + 1) =
        LimbArray.valAt a ao.toNat m.toNat * 2 ^ s := by
  rw [shlTop]
  split
  · rename_i hS
    obtain ⟨c₁, c₂, c₃⟩ := copyW_spec (R.zeros (m.toNat + 1)) 0 a ao m (zeros_bound (by lia)) ha
    rw [R.size_zeros] at c₁
    simp only [USize.toNat_zero] at c₂ c₃
    refine ⟨c₁, ?_⟩
    rw [hS, Nat.pow_zero, Nat.mul_one, LimbArray.valAt_add, LimbArray.valAt_one, Nat.zero_add,
      c₂ _ (.inr (by lia)), R.val_get_zeros, Nat.mul_zero, Nat.add_zero, c₃]
  · rename_i hS
    have hsv := val_shift (R := R) hs
    obtain ⟨p₁, p₂, p₃⟩ := lshiftW_spec (R.zeros (m.toNat + 1)) 0 a ao m (R.ofUSize s.toUSize)
      (zeros_bound (by lia)) ha (by rw [hsv]; lia) (by rw [hsv]; exact hs)
    rw [R.size_zeros] at p₁
    simp only [USize.toNat_zero] at p₂ p₃
    rw [hsv] at p₃
    refine ⟨by rw [R.size_uset, p₁], ?_⟩
    rw [LimbArray.valAt_add, LimbArray.valAt_one, Nat.zero_add, R.get_uset,
      valAt_uset_of _ _ _ _ _ _ (.inr (by lia))]
    simp only [↓reduceIte]
    rw [← p₃]

/-- `shlFit` holds `b 2ˢ` in `n` limbs when it is below `βⁿ`. -/
public theorem shlFit_spec (b : A) (bo n : USize) (hb : LoopBound b bo n) (s : Nat)
    (hs : s < LA.w) (hfit : LimbArray.valAt b bo.toNat n.toNat * 2 ^ s < 2 ^ (LA.w * n.toNat)) :
    LimbArray.valAt (shlFit b bo n hb s) 0 n.toNat = LimbArray.valAt b bo.toNat n.toNat * 2 ^ s := by
  rw [shlFit]
  split
  · rename_i hS
    rw [hS, Nat.pow_zero, Nat.mul_one]
    exact (extract_spec b bo.toNat n.toNat hb.1).2
  · rename_i hS
    have hsv := val_shift (R := R) hs
    obtain ⟨v₁, -, v₃⟩ := lshiftW_spec (R.zeros n.toNat) 0 b bo n (R.ofUSize s.toUSize)
      (zeros_bound ⟨Nat.le_refl _, n.toNat_lt_size⟩) hb (by rw [hsv]; lia) (by rw [hsv]; exact hs)
    simp only [USize.toNat_zero] at v₃
    rw [hsv] at v₃
    generalize lshiftW (R.zeros n.toNat) 0 b bo n (R.ofUSize s.toUSize) _ hb = p at v₃ ⊢
    rcases Nat.eq_zero_or_pos (LA.val p.2) with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at v₃; exact v₃
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat)) h; lia

/-- `shrNew` holds `⌊r / 2ˢ⌋` in `n` limbs. -/
public theorem shrNew_spec (r : A) (ro n : USize) (hr : LoopBound r ro n) (s : Nat)
    (hs : s < LA.w) :
    LA.size (shrNew r ro n hr s) = n.toNat ∧
      LimbArray.valAt (shrNew r ro n hr s) 0 n.toNat =
        LimbArray.valAt r ro.toNat n.toNat / 2 ^ s := by
  rw [shrNew]
  split
  · rename_i h
    obtain ⟨e₁, e₂⟩ := extract_spec r ro.toNat n.toNat hr.1
    refine ⟨e₁, ?_⟩
    rcases h with h | h
    · rw [h, Nat.pow_zero, Nat.div_one]; exact e₂
    · subst h; simp
  · rename_i h
    have hsv := val_shift (R := R) hs
    have hs₀ : 0 < s := Nat.pos_of_ne_zero fun e => h (.inl e)
    obtain ⟨r₁, -, r₃, r₄⟩ := rshiftW_spec (R.zeros n.toNat) 0 r ro n (R.ofUSize s.toUSize)
      (zeros_bound ⟨Nat.le_refl _, n.toNat_lt_size⟩) hr _ (by rw [hsv]; exact hs₀)
      (by rw [hsv]; exact hs)
    rw [R.size_zeros] at r₁
    simp only [USize.toNat_zero] at r₃
    rw [hsv] at r₃ r₄
    refine ⟨r₁, ?_⟩
    rw [← r₃, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt r₄, Nat.add_zero]

/-- `shlArr` holds `a 2ˢ` in `size a + 1` limbs. -/
public theorem shlArr_spec (a : A) (s : Nat) (hs : s < LA.w) (hU : LA.size a + 1 < USize.size) :
    LA.size (shlArr a s) = LA.size a + 1 ∧
      LimbArray.valAt (shlArr a s) 0 (LA.size (shlArr a s)) =
        LimbArray.valAt a 0 (LA.size a) * 2 ^ s := by
  rw [shlArr, dite_eq_left hU]
  obtain ⟨h₁, h₂⟩ := shlTop_spec a 0 (LA.size a).toUSize (arr_bound a (Nat.le_refl _) (by lia))
    (by rw [toNat_toUSize_of_lt (by lia)]; exact hU) s hs
  simp only [toNat_toUSize_of_lt (show LA.size a < USize.size by lia), USize.toNat_zero] at h₁ h₂
  exact ⟨h₁, by rw [h₁]; exact h₂⟩

/-- `shlFitArr` holds `b 2ˢ` in `n` limbs when it is below `βⁿ`. -/
public theorem shlFitArr_spec (b : A) (n s : Nat) (hs : s < LA.w) (hn : n ≤ LA.size b)
    (hU : LA.size b < USize.size)
    (hfit : LimbArray.valAt b 0 (LA.size b) * 2 ^ s < 2 ^ (LA.w * n)) :
    LA.size (shlFitArr b n s) = n ∧
      LimbArray.valAt (shlFitArr b n s) 0 (LA.size (shlFitArr b n s)) =
        LimbArray.valAt b 0 (LA.size b) * 2 ^ s := by
  rw [shlFitArr, dite_eq_left ⟨hn, hU⟩]
  have hn' := toNat_toUSize_of_lt (show n < USize.size by lia)
  have hB : LimbArray.valAt b 0 (LA.size b) < 2 ^ (LA.w * n) :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hfit
  have hv : LimbArray.valAt b 0 n = LimbArray.valAt b 0 (LA.size b) := by
    rw [LimbArray.valAt_mod _ _ hn, Nat.mod_eq_of_lt hB]
  have h₁ := size_shlFit b 0 n.toUSize (arr_bound b hn hU) s
  have h₂ := shlFit_spec b 0 n.toUSize (arr_bound b hn hU) s hs
    (by rw [USize.toNat_zero, hn', hv]; exact hfit)
  rw [hn'] at h₁
  rw [USize.toNat_zero, hn', hv] at h₂
  exact ⟨h₁, by rw [h₁]; exact h₂⟩

/-- `shrArr` holds `⌊r / 2ˢ⌋` in `size r` limbs. -/
public theorem shrArr_spec (r : A) (s : Nat) (hs : s < LA.w) (hU : LA.size r < USize.size) :
    LA.size (shrArr r s) = LA.size r ∧
      LimbArray.valAt (shrArr r s) 0 (LA.size (shrArr r s)) =
        LimbArray.valAt r 0 (LA.size r) / 2 ^ s := by
  rw [shrArr, dite_eq_left hU]
  obtain ⟨h₁, h₂⟩ := shrNew_spec r 0 (LA.size r).toUSize (arr_bound r (Nat.le_refl _) hU) s hs
  simp only [toNat_toUSize_of_lt hU, USize.toNat_zero] at h₁ h₂
  exact ⟨h₁, by rw [h₁]; exact h₂⟩

/-- `resultsN` takes the quotient and the remainder of the division in `w`. -/
public theorem resultsN_spec (w : A) (n k : USize) (s : Nat) (hs : s < LA.w)
    (hsz : LA.size w = n.toNat + k.toNat) :
    LA.size (resultsN w n k s).1 = k.toNat ∧
      LimbArray.valAt (resultsN w n k s).1 0 k.toNat = LimbArray.valAt w n.toNat k.toNat ∧
      LA.size (resultsN w n k s).2 = n.toNat ∧
      LimbArray.valAt (resultsN w n k s).2 0 n.toNat =
        LimbArray.valAt w 0 n.toNat / 2 ^ s := by
  have h : LoopBound w 0 n := ⟨by simp; lia, by simp [n.toNat_lt_size]⟩
  rw [resultsN, dite_eq_left h]
  obtain ⟨q₁, q₂⟩ := quotN_spec w n k hsz
  obtain ⟨r₁, r₂⟩ := shrNew_spec w 0 n h s hs
  simp only [USize.toNat_zero] at r₂
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
    (hn : 2 ≤ n.toNat) (s : Nat) (hs : s < LA.w) (X Y : Nat)
    (hsz : LA.size w = k.toNat + n.toNat) (hU : LA.size w < USize.size)
    (hV : LimbArray.valAt v vs.toNat n.toNat = Y * 2 ^ s) (hY : 0 < Y)
    (hW : LimbArray.valAt w 0 (k.toNat + n.toNat) = X * 2 ^ s)
    (hX : X < Y * 2 ^ (LA.w * k.toNat)) :
    LA.size (resultsN (loopN A t t₂ w v vs n hv hn k) n k s).1 = k.toNat ∧
      LimbArray.valAt (resultsN (loopN A t t₂ w v vs n hv hn k) n k s).1 0 k.toNat = X / Y ∧
      LA.size (resultsN (loopN A t t₂ w v vs n hv hn k) n k s).2 = n.toNat ∧
      LimbArray.valAt (resultsN (loopN A t t₂ w v vs n hv hn k) n k s).2 0 n.toNat =
        X % Y := by
  have hS := Nat.two_pow_pos s
  have hVpos : 0 < Y * 2 ^ s := Nat.mul_pos hY hS
  obtain ⟨l₁, l₂, l₃⟩ := loopN_spec t t₂ w v vs n hv hn k (by lia) hU (by rw [hV]; exact hVpos)
    (by
      rw [hW, hV, Nat.mul_right_comm]
      exact Nat.mul_lt_mul_of_pos_right hX hS)
  rw [hV, hW] at l₂
  rw [hV] at l₃
  obtain ⟨r₁, r₂, r₃, r₄⟩ := resultsN_spec (loopN A t t₂ w v vs n hv hn k) n k s hs
    (by rw [l₁, hsz, Nat.add_comm])
  have hQ := Nat.mul_div_mul_right X Y hS
  have hR := Nat.mul_mod_mul_right (2 ^ s) X Y
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
  have hs : LA.w - 1 - L < LA.w := by have := LA.w_pos; lia
  unfold divRemN
  rw [R.uget_eq, htopI, R.log2_eq, hLd]
  unfold divRemS
  dsimp only
  obtain ⟨w₁, w₂⟩ := shlTop_spec a ao m ha hU _ hs
  have hW : LimbArray.valAt (shlTop a ao m ha hU (LA.w - 1 - L)) 0 ((m + 1 - n).toNat + n.toNat) =
      LimbArray.valAt a ao.toNat m.toNat * 2 ^ (LA.w - 1 - L) := by
    rw [hk, show m.toNat + 1 - n.toNat + n.toNat = m.toNat + 1 by lia, w₂]
  split
  · -- `b` is normalized: only `a` is copied.
    rename_i hS
    obtain ⟨r₁, r₂, r₃, r₄⟩ := coreN_spec t t₂ _ b bo n (m + 1 - n) hb hn _ hs
      (LimbArray.valAt a ao.toNat m.toNat) (LimbArray.valAt b bo.toNat n.toNat)
      (by rw [w₁, hk]; lia) (by rw [w₁]; exact hU)
      (by rw [hS, Nat.pow_zero, Nat.mul_one]) hBpos hW hX
    rw [hk] at r₁ r₂
    exact ⟨r₁, r₂, r₃, r₄⟩
  · -- `a` and `b` shifted left by `S` bits.
    obtain ⟨r₁, r₂, r₃, r₄⟩ := coreN_spec t t₂ _ _ 0 n (m + 1 - n) _ hn _ hs
      (LimbArray.valAt a ao.toNat m.toNat) (LimbArray.valAt b bo.toNat n.toNat)
      (by rw [w₁, hk]; lia) (by rw [w₁]; exact hU)
      (by simpa using shlFit_spec b bo n hb _ hs hbS) hBpos hW hX
    rw [hk] at r₁ r₂
    exact ⟨r₁, r₂, r₃, r₄⟩

end MPN.Schoolbook
