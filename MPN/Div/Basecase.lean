/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Schoolbook
public import MPN.Div.ByLimb
public import MPN.Trim

/-!
# Schoolbook division with normalization, for limbs of any width

`divRemN t t₂ a ao m b bo n` divides the `m` limbs of `a` from `ao` by the `2 ≤ n ≤ m` limbs of
`b` from `bo`, whose top limb is not zero, like GMP's `mpn_tdiv_qr` below its thresholds of
division by blocks: `a` and `b` are shifted left by the `s` bits that set the top bit of `b`, `a`
into a new array of `m + 1` limbs, which `divLoop2In` divides in place, and `b` into a new array
unless `s = 0`. The quotient and the remainder, shifted back, are copied out of the array of the
division into new arrays of `m + 1 - n` and `n` limbs.

`divQN` copies out the quotient alone, and `modN` copies nothing: it shifts the remainder back in
place (`rshDown`) and drops the quotient limbs above it (`popTo`), so that the array of the
division becomes the remainder.
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
division by blocks of `MPN.Div.Driver`.
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

/-- `shrNew` on a whole array: `⌊r / 2ˢ⌋` in `size r` limbs. -/
@[inline, expose] public def shrArr (r : A) (s : Nat) : A :=
  if h : fitsU (LA.size r) then
    shrNew r 0 (LA.size r).toUSize (arr_bound r (Nat.le_refl _) (lt_of_fitsU h)) s
  else ofNatLen (R := R) (LimbArray.valAt r 0 (LA.size r) / 2 ^ s) (LA.size r)

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

/-- `x` without its limbs from `k` up, by `pop`, in place when `x` is held once. -/
@[expose, specialize] public def popTo (k : Nat) (x : A) : A :=
  if k < LA.size x then popTo k (R.pop x) else x
termination_by LA.size x
decreasing_by rw [R.size_pop]; lia

/--
The remainder of the division in `w`, limbs `0` to `n - 1`, shifted back by `s` bits in place
(`rshDown`), and the quotient above dropped by `popTo`: no new array.
-/
@[inline, expose] public def remN (w : A) (n : USize) (s : Nat) : A :=
  if h : s ≠ 0 ∧ LoopBound w 0 n then
    popTo n.toNat (rshDown A (R.ofUSize s.toUSize) w 0 n h.2 R.zero)
  else popTo n.toNat w

/-- The shift `w - 1 - ⌊log₂ T⌋` that sets the top bit of the top limb `T` of `b`. -/
@[inline, expose] public def shiftN (b : A) (bo n : USize) (hb : LoopBound b bo n)
    (hn : 2 ≤ n.toNat) : Nat :=
  LA.w - 1 - R.log2 (R.uget b (bo + (n - 1)) (hb.uset_bound (usub_lt (by simp) (by simp; lia))))

variable (A) in
/--
The division in place with the shift `s` that sets the top bit of `b`: `a` copied if `s = 0`, else
`a` and `b` shifted left by `s` bits, then divided by `loopN`. The array holds the quotient in
limbs `n` to `m` and the remainder, shifted left by `s` bits, in limbs `0` to `n - 1`.
-/
@[inline, expose] public def workS (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat)
    (hU : m.toNat + 1 < USize.size) (s : Nat) : A :=
  if s = 0 then loopN A t t₂ (shlTop a ao m ha hU s) b bo n hb hn (m + 1 - n)
  else
    loopN A t t₂ (shlTop a ao m ha hU s) (shlFit b bo n hb s) 0 n
      ⟨by rw [size_shlFit]; simp, by simp [n.toNat_lt_size]⟩ hn (m + 1 - n)

/--
`a / b` and `a % b`, for `a` of `m` limbs from `ao` and `b` of `2 ≤ n ≤ m` limbs from `bo` with a
nonzero top limb: the quotient in `m + 1 - n` limbs and the remainder in `n` limbs.
-/
@[expose] public def divRemN (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (_hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) : A × A :=
  let s := shiftN b bo n hb hn
  resultsN (workS A t t₂ a ao m b bo n ha hb hn hU s) n (m + 1 - n) s

/-- `a / b` as in `divRemN`, without the remainder. -/
@[expose] public def divQN (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (_hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) : A :=
  quotN (workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn)) n (m + 1 - n)

/--
`a % b` as in `divRemN`, without the quotient, in the array of the division itself (`remN`), like
GMP's `mpn_tdiv_qr` with its remainder shifted back in place.
-/
@[expose] public def modN (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (_hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) : A :=
  let s := shiftN b bo n hb hn
  remN (workS A t t₂ a ao m b bo n ha hb hn hU s) n s

/-! ## Proofs -/

omit F in
/-- `quotN` takes limbs `n` to `n + k - 1` of `w`, its top limbs. -/
public theorem quotN_spec (w : A) (n k : USize) (hs : LA.size w = n.toNat + k.toNat) :
    LA.size (quotN w n k) = k.toNat ∧
      LimbArray.valAt (quotN w n k) 0 k.toNat = LimbArray.valAt w n.toNat k.toNat :=
  extract_spec w n.toNat k.toNat (by lia)

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
    have hsv := val_ofUSize_lt (R := R) hs
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
    LimbArray.valAt (shlFit b bo n hb s) 0 n.toNat =
      LimbArray.valAt b bo.toNat n.toNat * 2 ^ s := by
  rw [shlFit]
  split
  · rename_i hS
    rw [hS, Nat.pow_zero, Nat.mul_one]
    exact (extract_spec b bo.toNat n.toNat hb.1).2
  · rename_i hS
    have hsv := val_ofUSize_lt (R := R) hs
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
    have hsv := val_ofUSize_lt (R := R) hs
    have hs₀ : 0 < s := Nat.pos_of_ne_zero fun e => h (.inl e)
    obtain ⟨r₁, -, r₃, r₄⟩ := rshiftW_spec (R.zeros n.toNat) 0 r ro n (R.ofUSize s.toUSize)
      (zeros_bound ⟨Nat.le_refl _, n.toNat_lt_size⟩) hr _ (by rw [hsv]; exact hs₀)
      (by rw [hsv]; exact hs)
    rw [R.size_zeros] at r₁
    simp only [USize.toNat_zero] at r₃
    rw [hsv] at r₃ r₄
    refine ⟨r₁, ?_⟩
    rw [← r₃, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt r₄, Nat.add_zero]

/-- `shrArr` holds `⌊r / 2ˢ⌋` in `size r` limbs. -/
public theorem shrArr_spec (r : A) (s : Nat) (hs : s < LA.w) :
    LA.size (shrArr r s) = LA.size r ∧
      LimbArray.valAt (shrArr r s) 0 (LA.size (shrArr r s)) =
        LimbArray.valAt r 0 (LA.size r) / 2 ^ s := by
  by_cases h : fitsU (LA.size r)
  · rw [shrArr, dite_eq_left h]
    have hU := lt_of_fitsU h
    obtain ⟨h₁, h₂⟩ := shrNew_spec r 0 (LA.size r).toUSize (arr_bound r (Nat.le_refl _) hU) s hs
    simp only [toNat_toUSize_of_lt hU, USize.toNat_zero] at h₁ h₂
    exact ⟨h₁, by rw [h₁]; exact h₂⟩
  · rw [shrArr, dite_eq_right h, size_ofNatLen, valAt_ofNatLen,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (LimbArray.valAt_lt ..))]
    exact ⟨rfl, rfl⟩

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
in `n` limbs, with `X < Y βᵏ`, then the array of `loopN` holds the quotient `X / Y` in limbs `n` to
`n + k - 1` and `(X % Y) 2ˢ` in limbs `0` to `n - 1`.
-/
public theorem coreW_spec (t t₂ : USize) (w v : A) (vs n k : USize) (hv : LoopBound v vs n)
    (hn : 2 ≤ n.toNat) (s : Nat) (X Y : Nat)
    (hsz : LA.size w = k.toNat + n.toNat) (hU : LA.size w < USize.size)
    (hV : LimbArray.valAt v vs.toNat n.toNat = Y * 2 ^ s) (hY : 0 < Y)
    (hW : LimbArray.valAt w 0 (k.toNat + n.toNat) = X * 2 ^ s)
    (hX : X < Y * 2 ^ (LA.w * k.toNat)) :
    LA.size (loopN A t t₂ w v vs n hv hn k) = n.toNat + k.toNat ∧
      LimbArray.valAt (loopN A t t₂ w v vs n hv hn k) n.toNat k.toNat = X / Y ∧
      LimbArray.valAt (loopN A t t₂ w v vs n hv hn k) 0 n.toNat = X % Y * 2 ^ s := by
  have hS := Nat.two_pow_pos s
  have hVpos : 0 < Y * 2 ^ s := Nat.mul_pos hY hS
  obtain ⟨l₁, l₂, l₃⟩ := loopN_spec t t₂ w v vs n hv hn k (by lia) hU (by rw [hV]; exact hVpos)
    (by
      rw [hW, hV, Nat.mul_right_comm]
      exact Nat.mul_lt_mul_of_pos_right hX hS)
  rw [hV, hW] at l₂
  rw [hV] at l₃
  have hQ := Nat.mul_div_mul_right X Y hS
  have hR := Nat.mul_mod_mul_right (2 ^ s) X Y
  rw [← l₂, Nat.mul_add_div hVpos, Nat.div_eq_of_lt l₃, Nat.add_zero] at hQ
  rw [← l₂, Nat.mul_add_mod, Nat.mod_eq_of_lt l₃] at hR
  exact ⟨by rw [l₁, hsz, Nat.add_comm], hQ, hR⟩

omit F in
/-- `popTo k` keeps the first `k` limbs, and no more. -/
public theorem popTo_spec (k : Nat) (x : A) :
    LA.size (popTo k x) = min k (LA.size x) ∧
      ∀ i, i < k → LA.get (popTo k x) i = LA.get x i := by
  induction x using popTo.induct (R := R) k with
  | case1 x h ih =>
    rw [popTo, ite_eq_left h]
    obtain ⟨i₁, i₂⟩ := ih
    refine ⟨by rw [i₁, R.size_pop]; lia, fun i hi => ?_⟩
    rw [i₂ i hi]
    rcases Nat.lt_or_ge i (LA.size x - 1) with h' | h'
    · exact R.get_pop x i h'
    · -- `i` is past the limbs of `pop x`, which `k` limbs reach only if `x` has them.
      exfalso
      have := (R.size_pop x)
      lia
  | case2 x h =>
    rw [popTo, ite_eq_right h]
    exact ⟨by lia, fun _ _ => rfl⟩

omit F in
/-- `remN` holds `⌊w / 2ˢ⌋` of limbs `0` to `n - 1` of `w`, in `n` limbs. -/
public theorem remN_spec (w : A) (n : USize) (s : Nat) (hs : s < LA.w)
    (hsz : n.toNat ≤ LA.size w) :
    LA.size (remN w n s) = n.toNat ∧
      LimbArray.valAt (remN w n s) 0 n.toNat = LimbArray.valAt w 0 n.toNat / 2 ^ s := by
  rw [remN]
  split
  · rename_i h
    have hsv := val_ofUSize_lt (R := R) hs
    obtain ⟨d₁, -, d₃⟩ := rshDown_spec (R.ofUSize s.toUSize) (by rw [hsv]; lia)
      (by rw [hsv]; exact hs) w 0 n h.2 R.zero (by rw [R.val_zero]; exact Nat.two_pow_pos _)
    rw [R.val_zero, Nat.zero_mul, Nat.zero_add, hsv, USize.toNat_zero] at d₃
    obtain ⟨p₁, p₂⟩ := popTo_spec n.toNat (rshDown A (R.ofUSize s.toUSize) w 0 n h.2 R.zero)
    refine ⟨by rw [p₁, d₁]; lia, ?_⟩
    rw [← d₃]
    exact LimbArray.valAt_congr _ fun i h₁ h₂ => p₂ _ (by lia)
  · rename_i h
    have hs0 : s = 0 ∨ ¬LoopBound w 0 n := by
      by_cases e : s = 0
      · exact .inl e
      · exact .inr fun hb => h ⟨e, hb⟩
    obtain ⟨p₁, p₂⟩ := popTo_spec n.toNat w
    rcases hs0 with e | hb
    · refine ⟨by rw [p₁]; lia, ?_⟩
      rw [e, Nat.pow_zero, Nat.div_one]
      exact LimbArray.valAt_congr _ fun i h₁ h₂ => p₂ _ (by lia)
    · exact absurd ⟨by simp; lia, by simp [n.toNat_lt_size]⟩ hb

omit R F in
/-- The bounds of a divisor of `n` limbs whose top limb `T ≠ 0` has `⌊log₂ T⌋ = L`. -/
public theorem top_bounds (b : A) (bo n : Nat) (hn : 1 ≤ n)
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
/-- `(m + 1 - n).toNat`, for `n ≤ m` and `m + 1` within `USize`. -/
public theorem toNat_k {m n : USize} (hnm : n.toNat ≤ m.toNat) (hU : m.toNat + 1 < USize.size) :
    (m + 1 - n).toNat = m.toNat + 1 - n.toNat := by
  have hm1 : (m + 1).toNat = m.toNat + 1 :=
    (USize.toNat_add_of_lt (a := m) (b := 1) (by rw [USize.toNat_one]; lia)).trans
      (by rw [USize.toNat_one])
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hm1]; lia)), hm1]

/--
The array of the division, `workS` with the shift `shiftN`, holds `a / b` in limbs `n` to `m` and
`(a % b) 2ˢ` in limbs `0` to `n - 1`, for the shift `s < w`.
-/
public theorem workN_spec (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) (htop : LA.val (LA.get b (bo.toNat + n.toNat - 1)) ≠ 0) :
    shiftN b bo n hb hn < LA.w ∧
      LA.size (workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn)) = m.toNat + 1 ∧
      LimbArray.valAt (workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn)) n.toNat
          (m.toNat + 1 - n.toNat) =
        LimbArray.valAt a ao.toNat m.toNat / LimbArray.valAt b bo.toNat n.toNat ∧
      LimbArray.valAt (workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn)) 0 n.toNat =
        LimbArray.valAt a ao.toNat m.toNat % LimbArray.valAt b bo.toNat n.toNat *
          2 ^ shiftN b bo n hb hn := by
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
  have hsh : shiftN b bo n hb hn = LA.w - 1 - L := by
    unfold shiftN
    rw [R.uget_eq, htopI, R.log2_eq, hLd]
  rw [hsh]
  refine ⟨hs, ?_⟩
  unfold workS
  obtain ⟨w₁, w₂⟩ := shlTop_spec a ao m ha hU _ hs
  have hW : LimbArray.valAt (shlTop a ao m ha hU (LA.w - 1 - L)) 0 ((m + 1 - n).toNat + n.toNat) =
      LimbArray.valAt a ao.toNat m.toNat * 2 ^ (LA.w - 1 - L) := by
    rw [hk, show m.toNat + 1 - n.toNat + n.toNat = m.toNat + 1 by lia, w₂]
  split
  · -- `b` is normalized: only `a` is copied.
    rename_i hS
    obtain ⟨r₁, r₂, r₃⟩ := coreW_spec t t₂ _ b bo n (m + 1 - n) hb hn _
      (LimbArray.valAt a ao.toNat m.toNat) (LimbArray.valAt b bo.toNat n.toNat)
      (by rw [w₁, hk]; lia) (by rw [w₁]; exact hU)
      (by rw [hS, Nat.pow_zero, Nat.mul_one]) hBpos hW hX
    rw [hk] at r₁ r₂
    exact ⟨by rw [r₁]; lia, r₂, r₃⟩
  · -- `a` and `b` shifted left by `S` bits.
    obtain ⟨r₁, r₂, r₃⟩ := coreW_spec t t₂ _ _ 0 n (m + 1 - n) _ hn _
      (LimbArray.valAt a ao.toNat m.toNat) (LimbArray.valAt b bo.toNat n.toNat)
      (by rw [w₁, hk]; lia) (by rw [w₁]; exact hU)
      (by simpa using shlFit_spec b bo n hb _ hs hbS) hBpos hW hX
    rw [hk] at r₁ r₂
    exact ⟨by rw [r₁]; lia, r₂, r₃⟩

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
  obtain ⟨hs, w₁, w₂, w₃⟩ := workN_spec t t₂ a ao m b bo n ha hb hn hnm hU htop
  have hk := toNat_k (m := m) (n := n) hnm hU
  unfold divRemN
  dsimp only
  generalize workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn) = W at *
  generalize shiftN b bo n hb hn = S at *
  obtain ⟨r₁, r₂, r₃, r₄⟩ := resultsN_spec W n (m + 1 - n) S hs (by rw [w₁, hk]; lia)
  rw [hk] at r₁ r₂
  refine ⟨r₁, by rw [r₂, w₂], r₃, ?_⟩
  rw [r₄, w₃, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- `divQN` takes the quotient of `divRemN`. -/
public theorem divQN_spec (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) (htop : LA.val (LA.get b (bo.toNat + n.toNat - 1)) ≠ 0) :
    LA.size (divQN t t₂ a ao m b bo n ha hb hn hnm hU) = m.toNat + 1 - n.toNat ∧
      LimbArray.valAt (divQN t t₂ a ao m b bo n ha hb hn hnm hU) 0 (m.toNat + 1 - n.toNat) =
        LimbArray.valAt a ao.toNat m.toNat / LimbArray.valAt b bo.toNat n.toNat := by
  obtain ⟨-, w₁, w₂, -⟩ := workN_spec t t₂ a ao m b bo n ha hb hn hnm hU htop
  have hk := toNat_k (m := m) (n := n) hnm hU
  unfold divQN
  generalize workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn) = W at *
  obtain ⟨q₁, q₂⟩ := quotN_spec W n (m + 1 - n) (by rw [w₁, hk]; lia)
  rw [hk] at q₁ q₂
  exact ⟨q₁, by rw [q₂, w₂]⟩

/-- `modN` takes the remainder of `divRemN`. -/
public theorem modN_spec (t t₂ : USize) (a : A) (ao m : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao m) (hb : LoopBound b bo n) (hn : 2 ≤ n.toNat) (hnm : n.toNat ≤ m.toNat)
    (hU : m.toNat + 1 < USize.size) (htop : LA.val (LA.get b (bo.toNat + n.toNat - 1)) ≠ 0) :
    LA.size (modN t t₂ a ao m b bo n ha hb hn hnm hU) = n.toNat ∧
      LimbArray.valAt (modN t t₂ a ao m b bo n ha hb hn hnm hU) 0 n.toNat =
        LimbArray.valAt a ao.toNat m.toNat % LimbArray.valAt b bo.toNat n.toNat := by
  obtain ⟨hs, w₁, -, w₃⟩ := workN_spec t t₂ a ao m b bo n ha hb hn hnm hU htop
  unfold modN
  dsimp only
  generalize workS A t t₂ a ao m b bo n ha hb hn hU (shiftN b bo n hb hn) = W at *
  generalize shiftN b bo n hb hn = S at *
  obtain ⟨r₁, r₂⟩ := remN_spec W n S hs (by rw [w₁]; lia)
  refine ⟨r₁, ?_⟩
  rw [r₂, w₃, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

end MPN.Schoolbook
