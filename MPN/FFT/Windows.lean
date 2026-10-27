/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Algebra
public import MPN.LimbArray

/-!
# The transforms over residue operations

The transforms of length `2ᵐ` modulo `F = 2^(w n) + 1`, on `2ᵐ` residues in consecutive windows
of `n + 1` limbs of one array, in place, with one scratch window, for limbs of any width `w`. They
need only three operations on windows, given with their specifications by `WinOps`: the sum and
the difference of two residues and the product of one by a power of two, each into a third
window. The root of unity is `2^σ` with `σ 2ᵐ = 2 w n`, so that `2^(σ 2ᵐ⁻¹) = 2^(w n) ≡ -1`.

* The forward transform, by decimation in frequency, replaces each pair `(x, y)` of the two
  halves by `(x + y, (x - y) 2^(σ j))`, then transforms each half with the root `2^(2 σ)`. It
  leaves `Σᵢ xᵢ 2^(σ i rev p)` at position `p`, where `rev` reverses the `m` bits of `p`.
* The inverse transform, by decimation in time, takes its input in that order: it transforms
  each half, then replaces each pair `(x, y)` by `(x + y 2^(-σ j), x - y 2^(-σ j))`. Since
  `2^(-σ j) ≡ -2^(w n - σ j)`, the multiplications are by powers less than `2^(w n)`, with the
  signs swapped. It leaves `Σₚ uₚ 2^((2 w n - σ) rev p l)` at position `l`.

Composed, with the pointwise products in between, the bit reversals cancel. `main32` and `main64`
instantiate `WinOps` with their residue operations on arrays of 32-bit and 64-bit limbs.
-/

namespace MPN.FFT

/-- The modulus `2^(w n) + 1` of the transforms on `n + 1` limbs of `w` bits. -/
@[expose] public def fermatW (w n : Nat) : Nat := 2 ^ (w * n) + 1

public theorem fermatW_pos (w n : Nat) : 0 < fermatW w n := Nat.succ_pos _

namespace WinOps

/-- The value of the window of `n + 1` limbs at `o`. -/
public abbrev win {A L : Type} [LimbArray A L] (a : A) (n o : Nat) : Nat :=
  LimbArray.valAt a o (n + 1)

/-- A window whose limbs are unchanged keeps its value. -/
public theorem win_congr {A L : Type} [LimbArray A L] {a a' : A} {n o : Nat}
    (h : ∀ i, o ≤ i → i < o + n + 1 → LimbArray.get a' i = LimbArray.get a i) :
    win a' n o = win a n o :=
  LimbArray.valAt_congr _ fun i h₁ h₂ => h i h₁ (by lia)

/-- A window disjoint from the one an operation writes keeps its value. -/
public theorem win_of_untouched {A L : Type} [LimbArray A L] {a a' : A} {n d o : Nat}
    (u : ∀ i, (i < d ∨ d + n + 1 ≤ i) → LimbArray.get a' i = LimbArray.get a i)
    (h : o + n + 1 ≤ d ∨ d + n + 1 ≤ o) : win a' n o = win a n o :=
  win_congr fun i h₁ h₂ => u i (by lia)

end WinOps

/--
The residue operations modulo `2^(w n) + 1` on windows of `n + 1` limbs of arrays of limbs, with
their specifications: each writes the window at `d`, leaves the other limbs as they are, and
reads windows disjoint from it or equal to it.
-/
public class WinOps (A : Type) (L : outParam Type) [LimbArray A L] where
  /-- `(x - y) % F` into the window at `d`: `subMod arr n d x y`. -/
  subMod : A → Nat → Nat → Nat → Nat → A
  /-- `(x + y) % F` into the window at `d`: `addMod arr n d x y`. -/
  addMod : A → Nat → Nat → Nat → Nat → A
  /-- `t 2ᵉ % F` into the window at `d`: `mulPow2 arr n d t e`. -/
  mulPow2 : A → Nat → Nat → Nat → Nat → A
  subMod_spec : ∀ (arr : A) (n d x y : Nat), LimbArray.size arr < USize.size →
    d + n + 1 ≤ LimbArray.size arr → x + n + 1 ≤ LimbArray.size arr →
    y + n + 1 ≤ LimbArray.size arr → 1 ≤ n → (d ≤ x ∨ x + n + 1 ≤ d) → (d ≤ y ∨ y + n + 1 ≤ d) →
    WinOps.win arr n x < fermatW (LimbArray.w A) n →
    WinOps.win arr n y < fermatW (LimbArray.w A) n →
    LimbArray.size (subMod arr n d x y) = LimbArray.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) →
        LimbArray.get (subMod arr n d x y) i = LimbArray.get arr i) ∧
      WinOps.win (subMod arr n d x y) n d =
        (WinOps.win arr n x + fermatW (LimbArray.w A) n - WinOps.win arr n y) %
          fermatW (LimbArray.w A) n
  addMod_spec : ∀ (arr : A) (n d x y : Nat), LimbArray.size arr < USize.size →
    d + n + 1 ≤ LimbArray.size arr → x + n + 1 ≤ LimbArray.size arr →
    y + n + 1 ≤ LimbArray.size arr → 1 ≤ n → (d ≤ x ∨ x + n + 1 ≤ d) → (d ≤ y ∨ y + n + 1 ≤ d) →
    WinOps.win arr n x < fermatW (LimbArray.w A) n →
    WinOps.win arr n y < fermatW (LimbArray.w A) n →
    LimbArray.size (addMod arr n d x y) = LimbArray.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) →
        LimbArray.get (addMod arr n d x y) i = LimbArray.get arr i) ∧
      WinOps.win (addMod arr n d x y) n d =
        (WinOps.win arr n x + WinOps.win arr n y) % fermatW (LimbArray.w A) n
  mulPow2_spec : ∀ (arr : A) (n d t e : Nat), LimbArray.size arr < USize.size →
    d + n + 1 ≤ LimbArray.size arr → t + n + 1 ≤ LimbArray.size arr → 1 ≤ n →
    e < LimbArray.w A * n → e < USize.size → (d + n + 1 ≤ t ∨ t + n + 1 ≤ d) →
    WinOps.win arr n t < fermatW (LimbArray.w A) n →
    LimbArray.size (mulPow2 arr n d t e) = LimbArray.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) →
        LimbArray.get (mulPow2 arr n d t e) i = LimbArray.get arr i) ∧
      WinOps.win (mulPow2 arr n d t e) n d =
        WinOps.win arr n t * 2 ^ e % fermatW (LimbArray.w A) n

/-! ## Windows in blocks -/

public theorem step_le {p q w : Nat} (h : p + 1 ≤ q) : p * w + w ≤ q * w := by
  have := Nat.mul_le_mul_right w h
  rw [Nat.add_mul, Nat.one_mul] at this
  exact this

/-- Distinct windows of a block are disjoint. -/
public theorem win_disj (o n p q : Nat) (h : p ≠ q) :
    o + p * (n + 1) + n + 1 ≤ o + q * (n + 1) ∨ o + q * (n + 1) + n + 1 ≤ o + p * (n + 1) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := step_le (w := n + 1) h; lia
  · have := step_le (w := n + 1) h; lia

/-- A window of a block of `L` windows is within it. -/
public theorem win_in (o n p L : Nat) (h : p < L) : o + p * (n + 1) + n + 1 ≤ o + L * (n + 1) := by
  have := step_le (w := n + 1) h; lia

namespace WinOps

variable {A L : Type} [LA : LimbArray A L] [R : WinOps A L]

/-! ## Butterflies -/

/-- The forward butterfly: `(x, y) ↦ (x + y, (x - y) 2ᵉ)`, through the scratch window `t`. -/
@[expose, specialize] public def fwdBfly (arr : A) (n x y t e : Nat) : A :=
  R.mulPow2 (R.addMod (R.subMod arr n t x y) n x x y) n y t e

/-- Three disjoint windows of `n + 1` limbs within an array whose indices do not overflow. -/
public abbrev Three (arr : A) (n x y t : Nat) : Prop :=
  LA.size arr < USize.size ∧ x + n + 1 ≤ LA.size arr ∧ y + n + 1 ≤ LA.size arr ∧
    t + n + 1 ≤ LA.size arr ∧
    (x + n + 1 ≤ y ∨ y + n + 1 ≤ x) ∧ (x + n + 1 ≤ t ∨ t + n + 1 ≤ x) ∧
    (y + n + 1 ≤ t ∨ t + n + 1 ≤ y)

public theorem fwdBfly_spec (arr : A) (n x y t e : Nat) (h : Three arr n x y t)
    (hn : 1 ≤ n) (he : e < LA.w * n) (heS : e < USize.size)
    (hX : win arr n x < fermatW LA.w n) (hY : win arr n y < fermatW LA.w n) :
    LA.size (R.fwdBfly arr n x y t e) = LA.size arr ∧
      (∀ i, (i < x ∨ x + n + 1 ≤ i) → (i < y ∨ y + n + 1 ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        LA.get (R.fwdBfly arr n x y t e) i = LA.get arr i) ∧
      win (R.fwdBfly arr n x y t e) n x = (win arr n x + win arr n y) % fermatW LA.w n ∧
      win (R.fwdBfly arr n x y t e) n y =
        (win arr n x + fermatW LA.w n - win arr n y) % fermatW LA.w n * 2 ^ e % fermatW LA.w n := by
  obtain ⟨hS, hx, hy, ht, hxy, hxt, hyt⟩ := h
  have hF : 0 < fermatW LA.w n := fermatW_pos LA.w n
  rw [fwdBfly]
  obtain ⟨s₁, u₁, v₁⟩ := R.subMod_spec arr n t x y hS ht hx hy hn (by lia) (by lia) hX hY
  generalize R.subMod arr n t x y = a₁ at *
  have x₁ := win_of_untouched u₁ (o := x) (by lia)
  have y₁ := win_of_untouched u₁ (o := y) (by lia)
  obtain ⟨s₂, u₂, v₂⟩ := R.addMod_spec a₁ n x x y (by lia) (by lia) (by lia) (by lia) hn
    (by lia) (by lia) (by rw [x₁]; exact hX) (by rw [y₁]; exact hY)
  generalize R.addMod a₁ n x x y = a₂ at *
  have t₂ := win_of_untouched u₂ (o := t) (by lia)
  have y₂ := win_of_untouched u₂ (o := y) (by lia)
  obtain ⟨s₃, u₃, v₃⟩ := R.mulPow2_spec a₂ n y t e (by lia) (by lia) (by lia) hn he heS (by lia)
    (by rw [t₂, v₁]; exact Nat.mod_lt _ hF)
  generalize R.mulPow2 a₂ n y t e = a₃ at *
  have x₃ := win_of_untouched u₃ (o := x) (by lia)
  refine ⟨by rw [s₃, s₂, s₁], fun i h₁ h₂ h₃ => by rw [u₃ i h₂, u₂ i h₁, u₁ i h₃], ?_, ?_⟩
  · rw [x₃, v₂, x₁, y₁]
  · rw [v₃, t₂, v₁]

/--
The inverse butterfly: `(x, y) ↦ (x + y, x - y)` for `j = 0`, and otherwise
`(x - y 2ᵉ, x + y 2ᵉ)`, with `2ᵉ ≡ -2^(-σ j)`, through the scratch window `t`.
-/
@[expose, specialize] public def invBfly (arr : A) (n x y t e : Nat) (first : Bool) : A :=
  if first then R.addMod (R.subMod (R.mulPow2 arr n t y 0) n y x t) n x x t
  else R.subMod (R.addMod (R.mulPow2 arr n t y e) n y x t) n x x t

public theorem invBfly_spec (arr : A) (n x y t e : Nat) (first : Bool)
    (h : Three arr n x y t) (hn : 1 ≤ n) (he : e < LA.w * n) (heS : e < USize.size)
    (hX : win arr n x < fermatW LA.w n) (hY : win arr n y < fermatW LA.w n) :
    LA.size (R.invBfly arr n x y t e first) = LA.size arr ∧
      (∀ i, (i < x ∨ x + n + 1 ≤ i) → (i < y ∨ y + n + 1 ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        LA.get (R.invBfly arr n x y t e first) i = LA.get arr i) ∧
      win (R.invBfly arr n x y t e first) n x =
        (if first then (win arr n x + win arr n y) % fermatW LA.w n
        else (win arr n x + fermatW LA.w n - win arr n y * 2 ^ e % fermatW LA.w n) %
          fermatW LA.w n) ∧
      win (R.invBfly arr n x y t e first) n y =
        (if first then (win arr n x + fermatW LA.w n - win arr n y) % fermatW LA.w n
        else (win arr n x + win arr n y * 2 ^ e % fermatW LA.w n) % fermatW LA.w n) := by
  obtain ⟨hS, hx, hy, ht, hxy, hxt, hyt⟩ := h
  have hF : 0 < fermatW LA.w n := fermatW_pos LA.w n
  have hY' : win arr n y % fermatW LA.w n = win arr n y := Nat.mod_eq_of_lt hY
  have e0 : 0 < LA.w * n := by lia
  obtain ⟨s₁, u₁, v₁⟩ := R.mulPow2_spec arr n t y (if first then 0 else e) hS ht hy hn
    (by split <;> lia) (by split <;> lia) (by lia) hY
  have hsplit : R.invBfly arr n x y t e first = if first
      then R.addMod (R.subMod (R.mulPow2 arr n t y (if first then 0 else e)) n y x t) n x x t
      else R.subMod (R.addMod (R.mulPow2 arr n t y (if first then 0 else e)) n y x t) n x x t := by
    rw [invBfly]; split <;> simp_all
  rw [hsplit]
  generalize R.mulPow2 arr n t y (if first then 0 else e) = a₁ at *
  have x₁ := win_of_untouched u₁ (o := x) (by lia)
  have hT : win a₁ n t < fermatW LA.w n := by rw [v₁]; exact Nat.mod_lt _ hF
  cases first with
  | true =>
    simp only [↓reduceIte, Nat.pow_zero, Nat.mul_one, hY'] at v₁ ⊢
    obtain ⟨s₂, u₂, v₂⟩ := R.subMod_spec a₁ n y x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₁]; exact hX) hT
    generalize R.subMod a₁ n y x t = a₂ at *
    have x₂ := win_of_untouched u₂ (o := x) (by lia)
    have t₂ := win_of_untouched u₂ (o := t) (by lia)
    obtain ⟨s₃, u₃, v₃⟩ := R.addMod_spec a₂ n x x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₂, x₁]; exact hX) (by rw [t₂]; exact hT)
    generalize R.addMod a₂ n x x t = a₃ at *
    have y₃ := win_of_untouched u₃ (o := y) (by lia)
    refine ⟨by rw [s₃, s₂, s₁], fun i h₁ h₂ h₃ => by rw [u₃ i h₁, u₂ i h₂, u₁ i h₃], ?_, ?_⟩
    · rw [v₃, x₂, x₁, t₂, v₁]
    · rw [y₃, v₂, x₁, v₁]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at v₁ ⊢
    obtain ⟨s₂, u₂, v₂⟩ := R.addMod_spec a₁ n y x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₁]; exact hX) hT
    generalize R.addMod a₁ n y x t = a₂ at *
    have x₂ := win_of_untouched u₂ (o := x) (by lia)
    have t₂ := win_of_untouched u₂ (o := t) (by lia)
    obtain ⟨s₃, u₃, v₃⟩ := R.subMod_spec a₂ n x x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₂, x₁]; exact hX) (by rw [t₂]; exact hT)
    generalize R.subMod a₂ n x x t = a₃ at *
    have y₃ := win_of_untouched u₃ (o := y) (by lia)
    refine ⟨by rw [s₃, s₂, s₁], fun i h₁ h₂ h₃ => by rw [u₃ i h₁, u₂ i h₂, u₁ i h₃], ?_, ?_⟩
    · rw [v₃, x₂, x₁, t₂, v₁]
    · rw [y₃, v₂, x₁, v₁]

/-! ## Blocks of windows -/

/-- The value of window `p` of the block at `o`, the windows of `n + 1` limbs one after another. -/
public abbrev coef (arr : A) (n o p : Nat) : Nat := win arr n (o + p * (n + 1))

/-- The butterflies of the forward transform, from `j` on, `cnt` of them. -/
@[expose, specialize] public def fwdLoop (n o h σ t : Nat) : A → Nat → Nat → A
  | arr, _, 0 => arr
  | arr, j, cnt + 1 =>
    fwdLoop n o h σ t (R.fwdBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t (σ * j)) (j + 1)
      cnt

/-- The bounds of a block of `L` windows at `o` and of a scratch window at `t`, disjoint from it. -/
public abbrev Block (arr : A) (n o L t : Nat) : Prop :=
  LA.size arr < USize.size ∧ o + L * (n + 1) ≤ LA.size arr ∧ t + n + 1 ≤ LA.size arr ∧
    (t + n + 1 ≤ o ∨ o + L * (n + 1) ≤ t)

set_option maxHeartbeats 400000 in
public theorem fwdLoop_spec (n o h σ t : Nat) (hn : 1 ≤ n) (hσ : σ * h = LA.w * n)
    (hw : LA.w * n < USize.size) (cnt : Nat) :
    ∀ arr j, j + cnt = h → Block arr n o (h + h) t →
      (∀ p < h + h, coef arr n o p < fermatW LA.w n) →
      LA.size (R.fwdLoop n o h σ t arr j cnt) = LA.size arr ∧
      (∀ i, (i < o ∨ o + (h + h) * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        LA.get (R.fwdLoop n o h σ t arr j cnt) i = LA.get arr i) ∧
      (∀ p < h + h, (p < j ∨ (h ≤ p ∧ p < h + j)) →
        coef (R.fwdLoop n o h σ t arr j cnt) n o p = coef arr n o p) ∧
      (∀ p, j ≤ p → p < h →
        coef (R.fwdLoop n o h σ t arr j cnt) n o p =
            (coef arr n o p + coef arr n o (h + p)) % fermatW LA.w n ∧
          coef (R.fwdLoop n o h σ t arr j cnt) n o (h + p) =
            (coef arr n o p + fermatW LA.w n - coef arr n o (h + p)) % fermatW LA.w n *
              2 ^ (σ * p) %
              fermatW LA.w n) := by
  induction cnt with
  | zero =>
    intro arr j hj _ _
    refine ⟨rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun p h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr j hj hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermatW LA.w n := fermatW_pos LA.w n
    have hjh : j < h := by lia
    have hxy := step_le (w := n + 1) (show j + 1 ≤ h + j by lia)
    have hyB := win_in o n (h + j) (h + h) (by lia)
    have hσ₀ : 0 < σ := by
      rcases Nat.eq_zero_or_pos σ with e | e
      · rw [e, Nat.zero_mul] at hσ; have := Nat.mul_pos LA.w_pos hn; lia
      · exact e
    have he : σ * j < LA.w * n := by rw [← hσ]; exact Nat.mul_lt_mul_of_pos_left hjh hσ₀
    obtain ⟨b₁, b₂, b₃, b₄⟩ := R.fwdBfly_spec arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (σ * j) ⟨hS, by lia, by lia, ht, by lia, by lia, by lia⟩ hn he (by lia)
      (hv j (by lia)) (hv (h + j) (by lia))
    rw [fwdLoop]
    generalize R.fwdBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t (σ * j) = a₁ at *
    have hc : ∀ p < h + h, p ≠ j → p ≠ h + j → coef a₁ n o p = coef arr n o p := by
      intro p hp h₁ h₂
      have d₁ := win_disj o n p j h₁
      have d₂ := win_disj o n p (h + j) h₂
      have d₃ := win_in o n p (h + h) hp
      exact win_congr fun i _ _ => b₂ i (by lia) (by lia) (by lia)
    have hv₁ : ∀ p < h + h, coef a₁ n o p < fermatW LA.w n := by
      intro p hp
      by_cases e₁ : p = j
      · subst e₁; show win a₁ n _ < _; rw [b₃]; exact Nat.mod_lt _ hF
      by_cases e₂ : p = h + j
      · subst e₂; show win a₁ n _ < _; rw [b₄]; exact Nat.mod_lt _ hF
      rw [hc p hp e₁ e₂]; exact hv p hp
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih a₁ (j + 1) (by lia) ⟨by lia, by lia, by lia, htd⟩ hv₁
    refine ⟨i₁.trans b₁, fun i h₁ h₂ => ?_, fun p hp hpj => ?_, fun p h₁ h₂ => ?_⟩
    · have d₃ := win_in o n j (h + h) (by lia)
      rw [i₂ i h₁ h₂, b₂ i (by lia) (by lia) h₂]
    · rw [i₃ p hp (by lia), hc p hp (by lia) (by lia)]
    · by_cases e : p = j
      · subst e
        rw [i₃ p (by lia) (by lia), i₃ (h + p) (by lia) (by lia)]
        exact ⟨b₃, b₄⟩
      · obtain ⟨k₁, k₂⟩ := i₄ p (by lia) h₂
        have c₁ := hc p (by lia) e (by lia)
        have c₂ := hc (h + p) (by lia) (by lia) (by lia)
        rw [c₁, c₂] at k₁ k₂
        exact ⟨k₁, k₂⟩

/-! ## The forward transform -/

/--
The forward transform of the block of `2ᵐ` windows at `o`, with the root `2^σ`: the butterflies
of the two halves, then the transforms of each half with the root `2^(2 σ)`.
-/
@[expose, specialize] public def fwd (n t : Nat) : Nat → A → Nat → Nat → A
  | 0, arr, _, _ => arr
  | m + 1, arr, o, σ =>
    let a := R.fwdLoop n o (2 ^ m) σ t arr 0 (2 ^ m)
    let a := fwd n t m a o (2 * σ)
    fwd n t m a (o + 2 ^ m * (n + 1)) (2 * σ)

public theorem fwd_spec (n t : Nat) (hn : 1 ≤ n) (hw : LA.w * n < USize.size) (m : Nat) :
    ∀ arr o σ, σ * 2 ^ m = 2 * (LA.w * n) → Block arr n o (2 ^ m) t →
      (∀ p < 2 ^ m, coef arr n o p < fermatW LA.w n) →
      LA.size (R.fwd n t m arr o σ) = LA.size arr ∧
      (∀ i, (i < o ∨ o + 2 ^ m * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        LA.get (R.fwd n t m arr o σ) i = LA.get arr i) ∧
      (∀ p < 2 ^ m, coef (R.fwd n t m arr o σ) n o p =
        sumRange (fun i => coef arr n o i * 2 ^ (σ * i * rev m p)) (2 ^ m) % fermatW LA.w n) := by
  induction m with
  | zero =>
    intro arr o σ _ _ hv
    refine ⟨rfl, fun _ _ _ => rfl, fun p hp => ?_⟩
    simp only [Nat.pow_zero] at hp
    have : p = 0 := by lia
    subst this
    simp only [fwd, sumRange, Nat.mul_zero, Nat.zero_mul, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (hv 0 (by simp))).symm
  | succ m ih =>
    intro arr o σ hσ hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermatW LA.w n := fermatW_pos LA.w n
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; lia
    rw [h2] at hB htd hv ⊢
    have hσ' : σ * 2 ^ m = LA.w * n := by rw [h2] at hσ; lia
    simp only [fwd]
    -- The butterflies.
    obtain ⟨l₁, l₂, -, l₄⟩ := R.fwdLoop_spec n o (2 ^ m) σ t hn hσ' hw (2 ^ m) arr 0 (by lia)
      ⟨hS, hB, ht, htd⟩ hv
    generalize R.fwdLoop n o (2 ^ m) σ t arr 0 (2 ^ m) = a₁ at *
    have hv₁ : ∀ p < 2 ^ m + 2 ^ m, coef a₁ n o p < fermatW LA.w n := by
      intro p hp
      rcases Nat.lt_or_ge p (2 ^ m) with e | e
      · rw [(l₄ p (by lia) e).1]; exact Nat.mod_lt _ hF
      · obtain ⟨p', rfl⟩ : ∃ p', p = 2 ^ m + p' := ⟨p - 2 ^ m, by lia⟩
        rw [(l₄ p' (by lia) (by lia)).2]; exact Nat.mod_lt _ hF
    -- The first half.
    have hmid := Nat.mul_le_mul_right (n + 1) (show 2 ^ m ≤ 2 ^ m + 2 ^ m by lia)
    obtain ⟨f₁, f₂, f₃⟩ := ih a₁ o (2 * σ) (by rw [Nat.mul_assoc, hσ']) ⟨by lia, by lia, by lia,
      by lia⟩ (fun p hp => hv₁ p (by lia))
    generalize R.fwd n t m a₁ o (2 * σ) = a₂ at *
    -- The second half.
    have hoff : ∀ p, o + 2 ^ m * (n + 1) + p * (n + 1) = o + (2 ^ m + p) * (n + 1) := by
      intro p; rw [Nat.add_mul]; lia
    have hv₂ : ∀ p < 2 ^ m, coef a₂ n (o + 2 ^ m * (n + 1)) p < fermatW LA.w n := by
      intro p hp
      have d := win_in o n (2 ^ m + p) (2 ^ m + 2 ^ m) (by lia)
      show win a₂ n _ < _
      rw [hoff, win_congr fun i _ _ => f₂ i (by lia) (by lia)]
      exact hv₁ _ (by lia)
    obtain ⟨g₁, g₂, g₃⟩ := ih a₂ (o + 2 ^ m * (n + 1)) (2 * σ) (by rw [Nat.mul_assoc, hσ'])
      ⟨by lia, by lia, by lia, by lia⟩ hv₂
    generalize R.fwd n t m a₂ (o + 2 ^ m * (n + 1)) (2 * σ) = a₃ at *
    refine ⟨by rw [g₁, f₁, l₁], fun i h₁ h₂ => ?_, fun p hp => ?_⟩
    · rw [g₂ i (by lia) h₂, f₂ i (by lia) h₂, l₂ i h₁ h₂]
    · rcases Nat.lt_or_ge p (2 ^ m) with e | e
      · -- An even output, from the first half.
        have d := win_in o n p (2 ^ m) e
        show win a₃ n _ = _
        rw [win_congr fun i _ _ => g₂ i (by lia) (by lia)]
        show coef a₂ n o p = _
        rw [f₃ p e, rev_succ_lo m p e]
        rw [sumRange_congr (g := fun i =>
          (coef arr n o i + coef arr n o (2 ^ m + i)) % fermatW LA.w n *
          2 ^ (2 * σ * i * rev m p)) fun i hi => by rw [(l₄ i (by lia) hi).1]]
        exact fwd_even rfl _ σ (2 ^ m) (rev m p) hσ'
      · -- An odd output, from the second half.
        obtain ⟨p', rfl⟩ : ∃ p', p = 2 ^ m + p' := ⟨p - 2 ^ m, by lia⟩
        show win a₃ n _ = _
        rw [← hoff]
        show coef a₃ n (o + 2 ^ m * (n + 1)) p' = _
        rw [g₃ p' (by lia), rev_succ_hi m p']
        rw [sumRange_congr (g := fun i =>
          (coef arr n o i + fermatW LA.w n - coef arr n o (2 ^ m + i)) %
          fermatW LA.w n * 2 ^ (σ * i) % fermatW LA.w n * 2 ^ (2 * σ * i * rev m p')) fun i hi => by
            have d := win_in o n (2 ^ m + i) (2 ^ m + 2 ^ m) (by lia)
            show win a₂ n _ * _ = _
            rw [hoff, win_congr fun k _ _ => f₂ k (by lia) (by lia)]
            show coef a₁ n o (2 ^ m + i) * _ = _
            rw [(l₄ i (by lia) hi).2]]
        exact fwd_odd rfl _ σ (2 ^ m) (rev m p') hσ' fun i hi => Nat.le_of_lt (hv _ (by lia))

/-! ## The inverse transform -/

/-- The butterflies of the inverse transform, from `j` on, `cnt` of them. -/
@[expose, specialize] public def invLoop (n o h σ t : Nat) : A → Nat → Nat → A
  | arr, _, 0 => arr
  | arr, j, cnt + 1 =>
    invLoop n o h σ t (R.invBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (if j = 0 then 0 else LA.w * n - σ * j) (j == 0)) (j + 1) cnt

set_option maxHeartbeats 400000 in
public theorem invLoop_spec (n o h σ t : Nat) (hn : 1 ≤ n) (hσ : σ * h = LA.w * n)
    (hw : LA.w * n < USize.size) (cnt : Nat) :
    ∀ arr j, j + cnt = h → Block arr n o (h + h) t →
      (∀ p < h + h, coef arr n o p < fermatW LA.w n) →
      LA.size (R.invLoop n o h σ t arr j cnt) = LA.size arr ∧
      (∀ i, (i < o ∨ o + (h + h) * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        LA.get (R.invLoop n o h σ t arr j cnt) i = LA.get arr i) ∧
      (∀ p < h + h, (p < j ∨ (h ≤ p ∧ p < h + j)) →
        coef (R.invLoop n o h σ t arr j cnt) n o p = coef arr n o p) ∧
      (∀ p, j ≤ p → p < h →
        coef (R.invLoop n o h σ t arr j cnt) n o p =
            (if (p == 0) = true then (coef arr n o p + coef arr n o (h + p)) % fermatW LA.w n
            else (coef arr n o p + fermatW LA.w n -
              coef arr n o (h + p) * 2 ^ (if p = 0 then 0 else LA.w * n - σ * p) % fermatW LA.w n) %
                fermatW LA.w n) ∧
          coef (R.invLoop n o h σ t arr j cnt) n o (h + p) =
            (if (p == 0) = true then
              (coef arr n o p + fermatW LA.w n - coef arr n o (h + p)) % fermatW LA.w n
            else (coef arr n o p +
              coef arr n o (h + p) * 2 ^ (if p = 0 then 0 else LA.w * n - σ * p) % fermatW LA.w n) %
                fermatW LA.w n)) := by
  induction cnt with
  | zero =>
    intro arr j hj _ _
    refine ⟨rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun p h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr j hj hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermatW LA.w n := fermatW_pos LA.w n
    have hjh : j < h := by lia
    have hxy := step_le (w := n + 1) (show j + 1 ≤ h + j by lia)
    have hyB := win_in o n (h + j) (h + h) (by lia)
    have hσ₀ : 0 < σ := by
      rcases Nat.eq_zero_or_pos σ with e | e
      · rw [e, Nat.zero_mul] at hσ; have := Nat.mul_pos LA.w_pos hn; lia
      · exact e
    have he : (if j = 0 then 0 else LA.w * n - σ * j) < LA.w * n := by
      have := Nat.mul_pos LA.w_pos hn
      split
      · lia
      · have : 0 < σ * j := Nat.mul_pos hσ₀ (by lia)
        lia
    obtain ⟨b₁, b₂, b₃, b₄⟩ := R.invBfly_spec arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (if j = 0 then 0 else LA.w * n - σ * j) (j == 0)
      ⟨hS, by lia, by lia, ht, by lia, by lia, by lia⟩
      hn he (by lia) (hv j (by lia)) (hv (h + j) (by lia))
    rw [invLoop]
    generalize R.invBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (if j = 0 then 0 else LA.w * n - σ * j) (j == 0) = a₁ at *
    have hc : ∀ p < h + h, p ≠ j → p ≠ h + j → coef a₁ n o p = coef arr n o p := by
      intro p hp h₁ h₂
      have d₁ := win_disj o n p j h₁
      have d₂ := win_disj o n p (h + j) h₂
      have d₃ := win_in o n p (h + h) hp
      exact win_congr fun i _ _ => b₂ i (by lia) (by lia) (by lia)
    have hv₁ : ∀ p < h + h, coef a₁ n o p < fermatW LA.w n := by
      intro p hp
      by_cases e₁ : p = j
      · subst e₁; show win a₁ n _ < _; rw [b₃]; split <;> exact Nat.mod_lt _ hF
      by_cases e₂ : p = h + j
      · subst e₂; show win a₁ n _ < _; rw [b₄]; split <;> exact Nat.mod_lt _ hF
      rw [hc p hp e₁ e₂]; exact hv p hp
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih a₁ (j + 1) (by lia) ⟨by lia, by lia, by lia, htd⟩ hv₁
    refine ⟨i₁.trans b₁, fun i h₁ h₂ => ?_, fun p hp hpj => ?_, fun p h₁ h₂ => ?_⟩
    · have d₃ := win_in o n j (h + h) (by lia)
      rw [i₂ i h₁ h₂, b₂ i (by lia) (by lia) h₂]
    · rw [i₃ p hp (by lia), hc p hp (by lia) (by lia)]
    · by_cases e : p = j
      · subst e
        rw [i₃ p (by lia) (by lia), i₃ (h + p) (by lia) (by lia)]
        exact ⟨b₃, b₄⟩
      · obtain ⟨k₁, k₂⟩ := i₄ p (by lia) h₂
        have c₁ := hc p (by lia) e (by lia)
        have c₂ := hc (h + p) (by lia) (by lia) (by lia)
        rw [c₁, c₂] at k₁ k₂
        exact ⟨k₁, k₂⟩

/--
The inverse transform of the block of `2ᵐ` windows at `o`, with the root `2^(2 N - σ)`: the
transforms of each half, then the butterflies.
-/
@[expose, specialize] public def inv (n t : Nat) : Nat → A → Nat → Nat → A
  -- Through `R.invLoop`, which owns the array: returning it directly makes the compiler borrow it,
  -- so that the butterflies after the recursive calls would copy it.
  | 0, arr, o, σ => R.invLoop n o 0 σ t arr 0 0
  | m + 1, arr, o, σ =>
    let a := inv n t m arr o (2 * σ)
    let a := inv n t m a (o + 2 ^ m * (n + 1)) (2 * σ)
    R.invLoop n o (2 ^ m) σ t a 0 (2 ^ m)

set_option maxHeartbeats 400000 in
public theorem inv_spec (n t : Nat) (hn : 1 ≤ n) (hw : LA.w * n < USize.size) (m : Nat) :
    ∀ arr o σ, σ * 2 ^ m = 2 * (LA.w * n) → Block arr n o (2 ^ m) t →
      (∀ p < 2 ^ m, coef arr n o p < fermatW LA.w n) →
      LA.size (R.inv n t m arr o σ) = LA.size arr ∧
      (∀ i, (i < o ∨ o + 2 ^ m * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        LA.get (R.inv n t m arr o σ) i = LA.get arr i) ∧
      (∀ l < 2 ^ m, coef (R.inv n t m arr o σ) n o l =
        sumRange (fun p => coef arr n o p * 2 ^ ((2 * (LA.w * n) - σ) * rev m p * l)) (2 ^ m) %
          fermatW LA.w n) := by
  induction m with
  | zero =>
    intro arr o σ _ _ hv
    refine ⟨rfl, fun _ _ _ => rfl, fun p hp => ?_⟩
    simp only [Nat.pow_zero] at hp
    have : p = 0 := by lia
    subst this
    simp only [inv, invLoop, sumRange, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (hv 0 (by simp))).symm
  | succ m ih =>
    intro arr o σ hσ hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermatW LA.w n := fermatW_pos LA.w n
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; lia
    rw [h2] at hB htd hv ⊢
    have hσ' : σ * 2 ^ m = LA.w * n := by rw [h2] at hσ; lia
    have hm₀ : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    simp only [inv]
    have hmid := Nat.mul_le_mul_right (n + 1) (show 2 ^ m ≤ 2 ^ m + 2 ^ m by lia)
    have hoff : ∀ p, o + 2 ^ m * (n + 1) + p * (n + 1) = o + (2 ^ m + p) * (n + 1) := by
      intro p; rw [Nat.add_mul]; lia
    -- The first half.
    obtain ⟨f₁, f₂, f₃⟩ := ih arr o (2 * σ) (by rw [Nat.mul_assoc, hσ']) ⟨hS, by lia, ht,
      by lia⟩ (fun p hp => hv p (by lia))
    generalize R.inv n t m arr o (2 * σ) = a₁ at *
    -- The second half.
    have hu₁ : ∀ p < 2 ^ m, coef a₁ n (o + 2 ^ m * (n + 1)) p = coef arr n o (2 ^ m + p) := by
      intro p hp
      have d := win_in o n (2 ^ m + p) (2 ^ m + 2 ^ m) (by lia)
      show win a₁ n _ = win arr n _
      rw [hoff, win_congr fun i _ _ => f₂ i (by lia) (by lia)]
    obtain ⟨g₁, g₂, g₃⟩ := ih a₁ (o + 2 ^ m * (n + 1)) (2 * σ) (by rw [Nat.mul_assoc, hσ'])
      ⟨by lia, by lia, by lia, by lia⟩ (fun p hp => by rw [hu₁ p hp]; exact hv _ (by lia))
    generalize R.inv n t m a₁ (o + 2 ^ m * (n + 1)) (2 * σ) = a₂ at *
    -- The halves, as transforms.
    have hA : ∀ l < 2 ^ m, coef a₂ n o l = sumRange (fun p => coef arr n o p *
        2 ^ ((2 * (LA.w * n) - 2 * σ) * rev m p * l)) (2 ^ m) % fermatW LA.w n := by
      intro l hl
      have d := win_in o n l (2 ^ m) hl
      show win a₂ n _ = _
      rw [win_congr fun i _ _ => g₂ i (by lia) (by lia)]
      exact f₃ l hl
    have hBv : ∀ l < 2 ^ m, coef a₂ n o (2 ^ m + l) = sumRange (fun p => coef arr n o (2 ^ m + p) *
        2 ^ ((2 * (LA.w * n) - 2 * σ) * rev m p * l)) (2 ^ m) % fermatW LA.w n := by
      intro l hl
      show win a₂ n _ = _
      rw [← hoff]
      show coef a₂ n (o + 2 ^ m * (n + 1)) l = _
      rw [g₃ l hl]
      exact congrArg (· % fermatW LA.w n) (sumRange_congr fun p hp => by rw [hu₁ p hp])
    have hv₂ : ∀ p < 2 ^ m + 2 ^ m, coef a₂ n o p < fermatW LA.w n := by
      intro p hp
      rcases Nat.lt_or_ge p (2 ^ m) with e | e
      · rw [hA p e]; exact Nat.mod_lt _ hF
      · obtain ⟨p', rfl⟩ : ∃ p', p = 2 ^ m + p' := ⟨p - 2 ^ m, by lia⟩
        rw [hBv p' (by lia)]; exact Nat.mod_lt _ hF
    -- The butterflies.
    obtain ⟨l₁, l₂, -, l₄⟩ := R.invLoop_spec n o (2 ^ m) σ t hn hσ' hw (2 ^ m) a₂ 0 (by lia)
      ⟨by lia, by lia, by lia, htd⟩ hv₂
    generalize R.invLoop n o (2 ^ m) σ t a₂ 0 (2 ^ m) = a₃ at *
    refine ⟨by rw [l₁, g₁, f₁], fun i h₁ h₂ => ?_, fun l hl => ?_⟩
    · rw [l₂ i h₁ h₂, g₂ i (by lia) h₂, f₂ i (by lia) h₂]
    -- Each output is congruent to the sum, and reduced.
    have hσle : σ ≤ σ * 2 ^ m := Nat.le_mul_of_pos_right σ hm₀
    have hτ : 2 * (LA.w * n) - σ + σ = 2 * (LA.w * n) := by lia
    have hτ' : 2 * (LA.w * n) - 2 * σ + 2 * σ = 2 * (LA.w * n) := by lia
    have hsplit : ∀ l', sumRange (fun p => coef arr n o p *
        2 ^ ((2 * (LA.w * n) - σ) * rev (m + 1) p * l')) (2 ^ m + 2 ^ m) =
          sumRange (fun p => coef arr n o p * 2 ^ ((2 * (LA.w * n) - σ) *
          (2 * rev m p) * l')) (2 ^ m) + sumRange (fun p => coef arr n o (2 ^ m + p) *
          2 ^ ((2 * (LA.w * n) - σ) * (2 * rev m p + 1) * l')) (2 ^ m) := by
      intro l'
      rw [sumRange_append]
      congr 1
      · exact sumRange_congr fun p hp => by rw [rev_succ_lo m p hp]
      · exact sumRange_congr fun p hp => by rw [rev_succ_hi m p]
    have hred : ∀ {c S}, c < fermatW LA.w n → MEq (fermatW LA.w n) c S → c = S % fermatW LA.w n :=
      fun hc h => (Nat.mod_eq_of_lt hc).symm.trans h
    have hMA : ∀ l < 2 ^ m, MEq (fermatW LA.w n) (coef a₂ n o l) (sumRange (fun p =>
        coef arr n o p *
        2 ^ ((2 * (LA.w * n) - 2 * σ) * rev m p * l)) (2 ^ m)) := fun l hl => by
      rw [hA l hl]; exact MEq.mod _ _
    have hMB : ∀ l < 2 ^ m, MEq (fermatW LA.w n) (coef a₂ n o (2 ^ m + l)) (sumRange (fun p =>
        coef arr n o (2 ^ m + p) * 2 ^ ((2 * (LA.w * n) - 2 * σ) * rev m p * l)) (2 ^ m)) :=
      fun l hl => by rw [hBv l hl]; exact MEq.mod _ _
    -- The exponent of a twiddle, `τ l ≡ e + N`.
    have hexp : ∀ l₁, l₁ + 1 < 2 ^ m → (2 * (LA.w * n) - σ) * (l₁ + 1) =
        (LA.w * n - σ * (l₁ + 1)) + LA.w * n + 2 * (LA.w * n) * l₁ := by
      intro l₁ hl₁
      have h₁ : σ * (l₁ + 1) ≤ σ * 2 ^ m := Nat.mul_le_mul_left σ (by lia)
      rw [Nat.sub_mul]
      lia
    have hcl : ∀ l < 2 ^ m,
        coef a₃ n o l < fermatW LA.w n ∧ coef a₃ n o (2 ^ m + l) < fermatW LA.w n := by
      intro l hl
      obtain ⟨k₁, k₂⟩ := l₄ l (by lia) hl
      rw [k₁, k₂]
      constructor <;> split <;> exact Nat.mod_lt _ hF
    rcases Nat.lt_or_ge l (2 ^ m) with e | e
    · -- The outputs `l`.
      obtain ⟨k₁, -⟩ := l₄ l (by lia) e
      refine hred (hcl l e).1 ?_
      rw [hsplit l]
      refine MEq.trans ?_ (inv_lo rfl _ (rev m) σ _ _ (2 ^ m) l hτ hτ').symm
      rw [k₁]
      by_cases e₀ : l = 0
      · subst e₀
        simp only [beq_self_eq_true, ↓reduceIte]
        exact inv_first_x (hMA 0 e) (hMB 0 e) _
      · obtain ⟨l₁, rfl⟩ : ∃ l₁, l = l₁ + 1 := ⟨l - 1, by lia⟩
        simp only [show (l₁ + 1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          show l₁ + 1 ≠ 0 by lia]
        exact inv_rest_x rfl (hMA _ e) (hMB _ e) (hexp l₁ e)
    · -- The outputs `2ᵐ + l`.
      obtain ⟨l', rfl⟩ : ∃ l', l = 2 ^ m + l' := ⟨l - 2 ^ m, by lia⟩
      have e' : l' < 2 ^ m := by lia
      obtain ⟨-, k₂⟩ := l₄ l' (by lia) e'
      refine hred (hcl l' e').2 ?_
      rw [hsplit (2 ^ m + l')]
      refine MEq.trans ?_ (inv_hi rfl _ (rev m) σ _ _ (2 ^ m) l' hτ hτ' hσ' hm₀).symm
      rw [k₂]
      by_cases e₀ : l' = 0
      · subst e₀
        simp only [beq_self_eq_true, ↓reduceIte]
        exact inv_first_y rfl (hMA 0 e') (hMB 0 e') (Nat.le_of_lt (hv₂ _ (by lia))) _
      · obtain ⟨l₁, rfl⟩ : ∃ l₁, l' = l₁ + 1 := ⟨l' - 1, by lia⟩
        simp only [show (l₁ + 1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          show l₁ + 1 ≠ 0 by lia]
        exact inv_rest_y rfl (hMA _ e') (hMB _ e') (hexp l₁ e')

end WinOps

end MPN.FFT
