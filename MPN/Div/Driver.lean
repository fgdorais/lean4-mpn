/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Basecase
public import MPN.Dispatch.Div

/-!
# Division by a divisor of several limbs, for limbs of any width

`divRemG o base toα ofα c t t₂ a ao m b bo n` divides the `m` limbs of `a` from `ao` by the
`n ≥ 2` limbs of `b` from `bo`, whose top limb is not zero, like GMP's `mpn_tdiv_qr` past its
divisors of one or two limbs: a dividend of fewer limbs than the divisor is its own remainder;
below `c.divDC` limbs in the divisor, Algorithm D (`Schoolbook.divRemN`, which normalizes); from
there, the operands are normalized (`Schoolbook.shlTop`, `shlFit`), divided by blocks or by
Barrett's method over the width's `NatOps` (`Dispatch.divN`, with `base` at the bottom, on the
numbers `toα` gives), and the remainder is shifted back (`Schoolbook.shrArr`). `divQG` is the
quotient alone (`Dispatch.divQN`). Past the sizes of the fast paths the results come from the
values, which never happens.
-/

namespace MPN.Div

open WordArray LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L] {α : Type}

variable (A) in
/-- The shift `w - 1 - ⌊log₂ x⌋` that sets the top bit of a nonzero limb `x`. -/
@[inline, expose] public def normBits (x : L) : Nat := LA.w - 1 - R.log2 x

/-- The guards of the fast paths: the windows within their arrays, and their indices words. -/
public abbrev Fits (a : A) (ao m : Nat) (b : A) (bo n : Nat) : Prop :=
  2 ≤ n ∧ ao + m ≤ LA.size a ∧ bo + n ≤ LA.size b ∧ fitsU (ao + m + 1) = true ∧
    fitsU (bo + n) = true

omit R F in
public theorem Fits.bounds {a : A} {ao m : Nat} {b : A} {bo n : Nat} (h : Fits a ao m b bo n) :
    LoopBound a ao.toUSize m.toUSize ∧ LoopBound b bo.toUSize n.toUSize ∧
      ao.toUSize.toNat = ao ∧ m.toUSize.toNat = m ∧ bo.toUSize.toNat = bo ∧
      n.toUSize.toNat = n ∧ m + 1 < USize.size := by
  obtain ⟨-, h₁, h₂, h₃, h₄⟩ := h
  have := lt_of_fitsU h₃
  have := lt_of_fitsU h₄
  exact ⟨win_bound a h₁ (by lia), win_bound b h₂ (by lia), toNat_toUSize_of_lt (by lia),
    toNat_toUSize_of_lt (by lia), toNat_toUSize_of_lt (by lia), toNat_toUSize_of_lt (by lia),
    by lia⟩

/--
`a / b` and `a % b`, for the `m` limbs of `a` from `ao` and the `n ≥ 2` limbs of `b` from `bo`
with a nonzero top limb, untrimmed.
-/
@[expose] public def divRemG (o : NatOps α) (base : α → α → α × α) (toα : A → α) (ofα : α → A)
    (c : Dispatch.DivConfig) (t t₂ : USize) (a : A) (ao m : Nat) (b : A) (bo n : Nat) :
    A × A :=
  if h : Fits a ao m b bo n then
    if hmn : m < n then (R.zeros 0, R.extract a ao (ao + m))
    else if n < c.divDC then
      Schoolbook.divRemN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)
    else
      let s := normBits A (LA.get b (bo + n - 1))
      let p := Dispatch.divN o c base
        (toα (Schoolbook.shlTop a ao.toUSize m.toUSize h.bounds.1
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) s))
        (toα (Schoolbook.shlFit b bo.toUSize n.toUSize h.bounds.2.1 s)) n (m + 1 - n)
      (ofα p.1, Schoolbook.shrArr (ofα p.2) s)
  else
    (ofNatW (R := R) (valAt a ao m / valAt b bo n), ofNatW (R := R) (valAt a ao m % valAt b bo n))

/-- `a / b` as in `divRemG`, without the last remainder from `c.divQMu` limbs. -/
@[expose] public def divQG (o : NatOps α) (base : α → α → α × α) (toα : A → α) (ofα : α → A)
    (c : Dispatch.DivConfig) (t t₂ : USize) (a : A) (ao m : Nat) (b : A) (bo n : Nat) : A :=
  if h : Fits a ao m b bo n then
    if hmn : m < n then R.zeros 0
    else if n < c.divDC then
      Schoolbook.divQN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)
    else
      let s := normBits A (LA.get b (bo + n - 1))
      ofα (Dispatch.divQN o c base
        (toα (Schoolbook.shlTop a ao.toUSize m.toUSize h.bounds.1
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) s))
        (toα (Schoolbook.shlFit b bo.toUSize n.toUSize h.bounds.2.1 s)) n (m + 1 - n))
  else ofNatW (R := R) (valAt a ao m / valAt b bo n)

/--
`a % b` as in `divRemG`, without the quotient below `c.divDC` limbs: Algorithm D in the array of
the division itself (`Schoolbook.modN`), and from there the remainder of `divRemG`.
-/
@[expose] public def divRG (o : NatOps α) (base : α → α → α × α) (toα : A → α) (ofα : α → A)
    (c : Dispatch.DivConfig) (t t₂ : USize) (a : A) (ao m : Nat) (b : A) (bo n : Nat) : A :=
  if h : Fits a ao m b bo n then
    if hmn : m < n then R.extract a ao (ao + m)
    else if n < c.divDC then
      Schoolbook.modN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)
    else (divRemG o base toα ofα c t t₂ a ao m b bo n).2
  else ofNatW (R := R) (valAt a ao m % valAt b bo n)

/-! ## Proofs -/

/-- What `divRemG` needs of the width's numbers: their values, and its `base` dividing. -/
public structure DriverOK (o : NatOps α) (base : α → α → α × α) (toα : A → α) (ofα : α → A) :
    Prop where
  B_eq : o.B = 2 ^ LA.w
  val_toα : ∀ x, o.val (toα x) = valAt x 0 (LA.size x)
  val_ofα : ∀ x, valAt (ofα x) 0 (LA.size (ofα x)) = o.val x
  base_ok : ∀ U V, 0 < o.val V →
    o.val (base U V).1 = o.val U / o.val V ∧ o.val (base U V).2 = o.val U % o.val V

omit F in
/-- The facts about a divisor with a nonzero top limb and its normalizing shift. -/
private theorem norm_facts (b : A) (bo n : Nat) (hn : 1 ≤ n)
    (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    normBits A (LA.get b (bo + n - 1)) < LA.w ∧
      0 < valAt b bo n ∧ 2 ^ (LA.w * (n - 1)) ≤ valAt b bo n ∧
      valAt b bo n * 2 ^ normBits A (LA.get b (bo + n - 1)) < 2 ^ (LA.w * n) := by
  have hT := LA.val_lt (LA.get b (bo + n - 1))
  have hL := (Nat.log2_lt htop).2 hT
  obtain ⟨hb₁, hb₂⟩ := Schoolbook.top_bounds b bo n hn htop
  have hw := LA.w_pos
  rw [normBits, R.log2_eq]
  generalize (LA.val (LA.get b (bo + n - 1))).log2 = Lg at hL hb₂
  have hβn : 2 ^ (LA.w * (n - 1)) * 2 ^ (Lg + 1) * 2 ^ (LA.w - 1 - Lg) = 2 ^ (LA.w * n) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1
    have : LA.w * n = LA.w * (n - 1) + LA.w := by rw [← Nat.mul_succ]; congr 1; lia
    lia
  refine ⟨by lia, Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hb₁, hb₁, ?_⟩
  rw [← hβn]; exact Nat.mul_lt_mul_of_pos_right hb₂ (Nat.two_pow_pos _)

omit R F in
/-- A dividend of `m ≥ n - 1` limbs is below `b βᵏ` for `k = m + 1 - n`. -/
private theorem dividend_lt (a : A) (ao m : Nat) (b : A) (bo n : Nat) (hn : 1 ≤ n)
    (hnm : n ≤ m + 1) (hb : 2 ^ (LA.w * (n - 1)) ≤ valAt b bo n) :
    valAt a ao m < valAt b bo n * 2 ^ (LA.w * (m + 1 - n)) := by
  have hA := valAt_lt a ao m
  have e : 2 ^ (LA.w * m) = 2 ^ (LA.w * (n - 1)) * 2 ^ (LA.w * (m + 1 - n)) := by
    rw [← Nat.pow_add]; congr 1; rw [← Nat.mul_add]; congr 1; lia
  rw [e] at hA
  exact Nat.lt_of_lt_of_le hA (Nat.mul_le_mul_right _ hb)

/-- The normalized operands of the division by blocks. -/
private theorem normed_vals {o : NatOps α} {base : α → α → α × α} {toα : A → α} {ofα : α → A}
    (D : DriverOK o base toα ofα) (a : A) (ao m : Nat) (b : A) (bo n : Nat)
    (h : Fits a ao m b bo n) (hnm : n ≤ m) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    let s := normBits A (LA.get b (bo + n - 1))
    o.val (toα (Schoolbook.shlTop a ao.toUSize m.toUSize h.bounds.1
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) s)) = valAt a ao m * 2 ^ s ∧
      o.val (toα (Schoolbook.shlFit b bo.toUSize n.toUSize h.bounds.2.1 s)) =
        valAt b bo n * 2 ^ s ∧
      s < LA.w ∧ 0 < valAt b bo n ∧
      o.val (toα (Schoolbook.shlFit b bo.toUSize n.toUSize h.bounds.2.1 s)) < o.B ^ n ∧
      o.val (toα (Schoolbook.shlTop a ao.toUSize m.toUSize h.bounds.1
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) s)) <
        o.val (toα (Schoolbook.shlFit b bo.toUSize n.toUSize h.bounds.2.1 s)) *
          o.B ^ (m + 1 - n) := by
  intro s
  obtain ⟨hs, hB, hb₁, hfit⟩ := norm_facts b bo n (by have := h.1; lia) htop
  obtain ⟨-, -, eo, em, ebo, en, -⟩ := h.bounds
  obtain ⟨u₁, u₂⟩ := Schoolbook.shlTop_spec a ao.toUSize m.toUSize h.bounds.1
    (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) s hs
  have v₁ := Schoolbook.size_shlFit b bo.toUSize n.toUSize h.bounds.2.1 s
  have v₂ := Schoolbook.shlFit_spec b bo.toUSize n.toUSize h.bounds.2.1 s hs
    (by rw [ebo, en]; exact hfit)
  simp only [eo, em] at u₁ u₂
  simp only [ebo, en] at v₁ v₂
  have hU : o.val (toα (Schoolbook.shlTop a ao.toUSize m.toUSize h.bounds.1
      (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) s)) = valAt a ao m * 2 ^ s := by
    rw [D.val_toα, u₁]; exact u₂
  have hV : o.val (toα (Schoolbook.shlFit b bo.toUSize n.toUSize h.bounds.2.1 s)) =
      valAt b bo n * 2 ^ s := by
    rw [D.val_toα, v₁]; exact v₂
  refine ⟨hU, hV, hs, hB, ?_, ?_⟩
  · rw [hV, D.B_eq, ← Nat.pow_mul]; exact hfit
  · rw [hU, hV, D.B_eq, ← Nat.pow_mul, Nat.mul_right_comm]
    exact Nat.mul_lt_mul_of_pos_right (dividend_lt a ao m b bo n (by have := h.1; lia) (by lia) hb₁)
      (Nat.two_pow_pos _)

/-- The schoolbook branch on the guarded windows. -/
private theorem school {a : A} {ao m : Nat} {b : A} {bo n : Nat} (t t₂ : USize)
    (h : Fits a ao m b bo n) (hnm : n ≤ m) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    valAt (Schoolbook.divRemN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)).1 0
        (LA.size (Schoolbook.divRemN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize
          h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
          (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)).1) =
        valAt a ao m / valAt b bo n ∧
      valAt (Schoolbook.divRemN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)).2 0
        (LA.size (Schoolbook.divRemN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize
          h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
          (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)).2) =
        valAt a ao m % valAt b bo n := by
  obtain ⟨-, -, eo, em, ebo, en, -⟩ := h.bounds
  obtain ⟨d₁, d₂, d₃, d₄⟩ := Schoolbook.divRemN_spec t t₂ a ao.toUSize m.toUSize b bo.toUSize
    n.toUSize h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
    (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
    (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) (by rw [ebo, en]; exact htop)
  simp only [eo, ebo, em, en] at d₁ d₂ d₃ d₄
  exact ⟨by rw [d₁]; exact d₂, by rw [d₃]; exact d₄⟩

/-- `school` for `Schoolbook.divQN`. -/
private theorem schoolQ {a : A} {ao m : Nat} {b : A} {bo n : Nat} (t t₂ : USize)
    (h : Fits a ao m b bo n) (hnm : n ≤ m) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    valAt (Schoolbook.divQN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)) 0
        (LA.size (Schoolbook.divQN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize
          h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
          (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2))) =
      valAt a ao m / valAt b bo n := by
  obtain ⟨-, -, eo, em, ebo, en, -⟩ := h.bounds
  obtain ⟨d₁, d₂⟩ := Schoolbook.divQN_spec t t₂ a ao.toUSize m.toUSize b bo.toUSize
    n.toUSize h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
    (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
    (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) (by rw [ebo, en]; exact htop)
  simp only [eo, ebo, em, en] at d₁ d₂
  rw [d₁]; exact d₂

/-- `school` for `Schoolbook.modN`. -/
private theorem schoolR {a : A} {ao m : Nat} {b : A} {bo n : Nat} (t t₂ : USize)
    (h : Fits a ao m b bo n) (hnm : n ≤ m) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    valAt (Schoolbook.modN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize h.bounds.1
        h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
        (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
        (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2)) 0
        (LA.size (Schoolbook.modN t t₂ a ao.toUSize m.toUSize b bo.toUSize n.toUSize
          h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
          (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
          (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2))) =
      valAt a ao m % valAt b bo n := by
  obtain ⟨-, -, eo, em, ebo, en, -⟩ := h.bounds
  obtain ⟨d₁, d₂⟩ := Schoolbook.modN_spec t t₂ a ao.toUSize m.toUSize b bo.toUSize
    n.toUSize h.bounds.1 h.bounds.2.1 (by rw [h.bounds.2.2.2.2.2.1]; exact h.1)
    (by rw [h.bounds.2.2.2.2.2.1, h.bounds.2.2.2.1]; lia)
    (by rw [h.bounds.2.2.2.1]; exact h.bounds.2.2.2.2.2.2) (by rw [ebo, en]; exact htop)
  simp only [eo, ebo, em, en] at d₁ d₂
  rw [d₁]; exact d₂

/-- `divRemG` divides. -/
public theorem divRemG_spec {o : NatOps α} {base : α → α → α × α} {toα : A → α} {ofα : α → A}
    (D : DriverOK o base toα ofα) (c : Dispatch.DivConfig) (t t₂ : USize) (a : A) (ao m : Nat)
    (b : A) (bo n : Nat) (hn : 2 ≤ n) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    valAt (divRemG o base toα ofα c t t₂ a ao m b bo n).1 0
        (LA.size (divRemG o base toα ofα c t t₂ a ao m b bo n).1) =
        valAt a ao m / valAt b bo n ∧
      valAt (divRemG o base toα ofα c t t₂ a ao m b bo n).2 0
        (LA.size (divRemG o base toα ofα c t t₂ a ao m b bo n).2) =
        valAt a ao m % valAt b bo n := by
  obtain ⟨hs, hB, hb₁, -⟩ := norm_facts b bo n (by lia) htop
  unfold divRemG
  split
  · rename_i h
    split
    · -- A shorter dividend is its own remainder.
      rename_i hmn
      have hlt : valAt a ao m < valAt b bo n :=
        Nat.lt_of_lt_of_le (valAt_lt a ao m)
          (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by
            have := Nat.mul_le_mul_left LA.w (show m ≤ n - 1 by lia); lia)) hb₁)
      have e := extract_spec a ao m h.2.1
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, R.size_zeros, valAt_zero, e.1]
      exact ⟨rfl, e.2⟩
    · split
      · exact school t t₂ h (by lia) htop
      · rename_i hmn hdc
        dsimp only
        obtain ⟨hU, hV, hs', hB', hVn, hUV⟩ := normed_vals D a ao m b bo n h (by lia) htop
        obtain ⟨r₁, r₂⟩ := Dispatch.divN_scaled c D.base_ok hU hV (Nat.two_pow_pos _) hB'
          hVn hUV
        obtain ⟨-, s₂⟩ := Schoolbook.shrArr_spec (ofα (Dispatch.divN o c base _ _ n
          (m + 1 - n)).2) (normBits A (LA.get b (bo + n - 1))) hs'
        rw [D.val_ofα, r₂, Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at s₂
        exact ⟨by rw [D.val_ofα, r₁], s₂⟩
  · rw [valAt_ofNatW, valAt_ofNatW]
    exact ⟨rfl, rfl⟩

/-- `divQG` is the quotient of `divRemG`. -/
public theorem divQG_spec {o : NatOps α} {base : α → α → α × α} {toα : A → α} {ofα : α → A}
    (D : DriverOK o base toα ofα) (c : Dispatch.DivConfig) (t t₂ : USize) (a : A) (ao m : Nat)
    (b : A) (bo n : Nat) (hn : 2 ≤ n) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    valAt (divQG o base toα ofα c t t₂ a ao m b bo n) 0
        (LA.size (divQG o base toα ofα c t t₂ a ao m b bo n)) =
      valAt a ao m / valAt b bo n := by
  obtain ⟨hs, hB, hb₁, -⟩ := norm_facts b bo n (by lia) htop
  unfold divQG
  split
  · rename_i h
    split
    · rename_i hmn
      have hlt : valAt a ao m < valAt b bo n :=
        Nat.lt_of_lt_of_le (valAt_lt a ao m)
          (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by
            have := Nat.mul_le_mul_left LA.w (show m ≤ n - 1 by lia); lia)) hb₁)
      rw [Nat.div_eq_of_lt hlt, R.size_zeros, valAt_zero]
    · split
      · exact schoolQ t t₂ h (by lia) htop
      · dsimp only
        obtain ⟨hU, hV, -, hB', hVn, hUV⟩ := normed_vals D a ao m b bo n h (by lia) htop
        rw [D.val_ofα]
        exact Dispatch.divQN_scaled c D.base_ok hU hV (Nat.two_pow_pos _) hB' hVn hUV
  · rw [valAt_ofNatW]

/-- `divRG` is the remainder of `divRemG`. -/
public theorem divRG_spec {o : NatOps α} {base : α → α → α × α} {toα : A → α} {ofα : α → A}
    (D : DriverOK o base toα ofα) (c : Dispatch.DivConfig) (t t₂ : USize) (a : A) (ao m : Nat)
    (b : A) (bo n : Nat) (hn : 2 ≤ n) (htop : LA.val (LA.get b (bo + n - 1)) ≠ 0) :
    valAt (divRG o base toα ofα c t t₂ a ao m b bo n) 0
        (LA.size (divRG o base toα ofα c t t₂ a ao m b bo n)) =
      valAt a ao m % valAt b bo n := by
  obtain ⟨hs, hB, hb₁, -⟩ := norm_facts b bo n (by lia) htop
  unfold divRG
  split
  · rename_i h
    split
    · rename_i hmn
      have hlt : valAt a ao m < valAt b bo n :=
        Nat.lt_of_lt_of_le (valAt_lt a ao m)
          (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by
            have := Nat.mul_le_mul_left LA.w (show m ≤ n - 1 by lia); lia)) hb₁)
      have e := extract_spec a ao m h.2.1
      rw [Nat.mod_eq_of_lt hlt, e.1]
      exact e.2
    · split
      · exact schoolR t t₂ h (by lia) htop
      · exact (divRemG_spec D c t t₂ a ao m b bo n hn htop).2
  · rw [valAt_ofNatW]

end MPN.Div
