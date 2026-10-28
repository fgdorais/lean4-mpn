/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Ops

/-!
# Karatsuba's method

`mulKaratsuba cfg d o x xo xl y yo yl` writes the `xl + yl` limbs of `x y` into `d` from limb `o`
on, for limbs of any width `w`. For `yl ≤ xl`, it splits both operands at `k = ⌈xl / 2⌉` into
`x = x₀ + 2^(w k) x₁` and `y = y₀ + 2^(w k) y₁`, and computes

* `z₀ = x₀ y₀` into the low `2 k` limbs of the window,
* `z₂ = x₁ y₁` into the limbs above them,
* `(x₀ + x₁) (y₀ + y₁)` into a new array, and adds `z₁ = x₀ y₁ + x₁ y₀`, which is that minus `z₀`
  and `z₂`, to the window from limb `k` on (`ToomOps.mid`),

all three products recursively. Below `cfg.mulKaratsuba` limbs, or when `yl ≤ k`, it is
`ToomOps.mulBase`. `sqrKaratsuba` is the same with three squares, below `cfg.sqrKaratsuba` limbs
`ToomOps.sqrBase`.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : ToomOps A L]

/-- Writes `x y` into the `xl + yl` limbs of `d` from `o` on, by Karatsuba's method. -/
@[expose, specialize] public def mulKaratsuba (cfg : Config) (d : A) (o : Nat) (x : A)
    (xo xl : Nat) (y : A) (yo yl : Nat) : A :=
  if h : cfg.mulKaratsuba ≤ xl ∧ yl ≤ xl ∧ xl - xl / 2 < yl then
    let k := xl - xl / 2
    let sx := R.sum x xo k x (xo + k) (xl - k)
    let sy := R.sum y yo k y (yo + k) (yl - k)
    let d₁ := mulKaratsuba cfg d o x xo k y yo k
    let d₂ := mulKaratsuba cfg d₁ (o + (k + k)) x (xo + k) (xl - k) y (yo + k) (yl - k)
    let z := mulKaratsuba cfg (R.zeros (k + k + 2)) 0 sx 0 (k + 1) sy 0 (k + 1)
    R.mid d₂ o k (xl + yl) z
  else
    R.mulBase d o x xo xl y yo yl
termination_by xl
decreasing_by all_goals have := cfg.four_le_mulKaratsuba; lia

/-- Writes `x²` into the `2 xl` limbs of `d` from `o` on, by Karatsuba's method. -/
@[expose, specialize] public def sqrKaratsuba (cfg : Config) (d : A) (o : Nat) (x : A)
    (xo xl : Nat) : A :=
  if h : cfg.sqrKaratsuba ≤ xl then
    let k := xl - xl / 2
    let sx := R.sum x xo k x (xo + k) (xl - k)
    let d₁ := sqrKaratsuba cfg d o x xo k
    let d₂ := sqrKaratsuba cfg d₁ (o + (k + k)) x (xo + k) (xl - k)
    let z := sqrKaratsuba cfg (R.zeros (k + k + 2)) 0 sx 0 (k + 1)
    R.mid d₂ o k (xl + xl) z
  else
    R.sqrBase d o x xo xl
termination_by xl
decreasing_by all_goals have := cfg.four_le_sqrKaratsuba; lia

/-! ## Correctness -/

/-- The value of `xl` limbs split at `k`. -/
public theorem valAt_split (x : A) (xo xl k : Nat) (hk : k ≤ xl) :
    valAt x xo xl = valAt x xo k + 2 ^ (LA.w * k) * valAt x (xo + k) (xl - k) := by
  conv => lhs; rw [show xl = k + (xl - k) by lia]
  rw [valAt_add]

/--
One step of Karatsuba's method: `z₀` and `z₂` in their windows of `d₂` and the product of the
sums in `z` give `x y` in the window of `n` limbs.
-/
private theorem mid_step (d₂ z : A) (o k n X₀ X₁ Y₀ Y₁ : Nat) (hn : o + n ≤ LA.size d₂)
    (hkn : k + k ≤ n) (h₀ : valAt d₂ o (k + k) = X₀ * Y₀)
    (h₂ : valAt d₂ (o + (k + k)) (n - (k + k)) = X₁ * Y₁)
    (hz : valAt z 0 (k + k + 2) = (X₀ + X₁) * (Y₀ + Y₁))
    (hlt : (X₀ + 2 ^ (LA.w * k) * X₁) * (Y₀ + 2 ^ (LA.w * k) * Y₁) < 2 ^ (LA.w * n)) :
    Writes (R.mid d₂ o k n z) d₂ o n ∧
      valAt (R.mid d₂ o k n z) o n = (X₀ + 2 ^ (LA.w * k) * X₁) * (Y₀ + 2 ^ (LA.w * k) * Y₁) := by
  obtain ⟨m₁, m₂⟩ := R.mid_spec d₂ o k n z hn
  have hprod : (X₀ + 2 ^ (LA.w * k) * X₁) * (Y₀ + 2 ^ (LA.w * k) * Y₁) =
      X₀ * Y₀ + 2 ^ (LA.w * k) * (X₀ * Y₁ + X₁ * Y₀) + 2 ^ (LA.w * (k + k)) * (X₁ * Y₁) := by
    rw [Nat.mul_add LA.w, Nat.pow_add]; grind
  rw [hprod] at hlt ⊢
  refine ⟨m₁, ?_⟩
  rw [← h₀, ← h₂] at hlt ⊢
  exact m₂ _ (by rw [hz, h₀, h₂]; grind) hlt

public theorem mulKaratsuba_spec (cfg : Config) (N : Nat) :
    ∀ (d : A) (o : Nat) (x : A) (xo xl : Nat) (y : A) (yo yl : Nat), xl = N →
      o + (xl + yl) ≤ LA.size d →
      Writes (mulKaratsuba cfg d o x xo xl y yo yl) d o (xl + yl) ∧
        valAt (mulKaratsuba cfg d o x xo xl y yo yl) o (xl + yl) =
          valAt x xo xl * valAt y yo yl := by
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro d o x xo xl y yo yl hN hd
  rw [mulKaratsuba]
  split
  · rename_i h
    obtain ⟨hg, hyx, hky⟩ := h
    have := cfg.four_le_mulKaratsuba
    dsimp only
    generalize hk : xl - xl / 2 = k at *
    have hk₁ : k + 1 < xl := by lia
    have hkx : xl - k ≤ k := by lia
    -- `z₀` and `z₂` into the window.
    obtain ⟨w₁, v₁⟩ := ih k (by lia) d o x xo k y yo k rfl (by lia)
    generalize mulKaratsuba cfg d o x xo k y yo k = d₁ at *
    obtain ⟨w₂, v₂⟩ := ih (xl - k) (by lia) d₁ (o + (k + k)) x (xo + k) (xl - k) y (yo + k)
      (yl - k) rfl (by rw [w₁.1]; lia)
    generalize mulKaratsuba cfg d₁ (o + (k + k)) x (xo + k) (xl - k) y (yo + k) (yl - k) = d₂ at *
    -- The product of the sums.
    obtain ⟨sx₁, sx₂⟩ := R.sum_spec x xo k x (xo + k) (xl - k) hkx
    obtain ⟨sy₁, sy₂⟩ := R.sum_spec y yo k y (yo + k) (yl - k) (by lia)
    generalize R.sum x xo k x (xo + k) (xl - k) = sx at *
    generalize R.sum y yo k y (yo + k) (yl - k) = sy at *
    obtain ⟨-, v₃⟩ := ih (k + 1) (by lia) (R.zeros (k + k + 2)) 0 sx 0 (k + 1) sy 0 (k + 1) rfl
      (by rw [R.size_zeros]; lia)
    rw [show k + 1 + (k + 1) = k + k + 2 by lia, sx₂, sy₂] at v₃
    generalize mulKaratsuba cfg (R.zeros (k + k + 2)) 0 sx 0 (k + 1) sy 0 (k + 1) = z at *
    -- The middle term.
    have hX := valAt_split x xo xl k (by lia)
    have hY := valAt_split y yo yl k (by lia)
    have hlt : valAt x xo xl * valAt y yo yl < 2 ^ (LA.w * (xl + yl)) := by
      rw [Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)
    have h₀ : valAt d₂ o (k + k) = valAt x xo k * valAt y yo k := by
      rw [← v₁]; exact w₂.valAt_eq (by lia)
    rw [hX, hY] at hlt ⊢
    obtain ⟨m₁, m₂⟩ := mid_step d₂ z o k (xl + yl) _ _ _ _ (by rw [w₂.1, w₁.1]; lia) (by lia) h₀
      (by rw [show xl + yl - (k + k) = xl - k + (yl - k) by lia]; exact v₂) v₃ hlt
    exact ⟨m₁.trans ((w₂.mono (by lia) (by lia)).trans (w₁.mono (by lia) (by lia))), m₂⟩
  · exact R.mulBase_spec d o x xo xl y yo yl hd

public theorem sqrKaratsuba_spec (cfg : Config) (N : Nat) :
    ∀ (d : A) (o : Nat) (x : A) (xo xl : Nat), xl = N → o + (xl + xl) ≤ LA.size d →
      Writes (sqrKaratsuba cfg d o x xo xl) d o (xl + xl) ∧
        valAt (sqrKaratsuba cfg d o x xo xl) o (xl + xl) = valAt x xo xl * valAt x xo xl := by
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro d o x xo xl hN hd
  rw [sqrKaratsuba]
  split
  · rename_i hg
    have := cfg.four_le_sqrKaratsuba
    dsimp only
    generalize hk : xl - xl / 2 = k at *
    have hk₁ : k + 1 < xl := by lia
    have hkx : xl - k ≤ k := by lia
    obtain ⟨w₁, v₁⟩ := ih k (by lia) d o x xo k rfl (by lia)
    generalize sqrKaratsuba cfg d o x xo k = d₁ at *
    obtain ⟨w₂, v₂⟩ := ih (xl - k) (by lia) d₁ (o + (k + k)) x (xo + k) (xl - k) rfl
      (by rw [w₁.1]; lia)
    generalize sqrKaratsuba cfg d₁ (o + (k + k)) x (xo + k) (xl - k) = d₂ at *
    obtain ⟨sx₁, sx₂⟩ := R.sum_spec x xo k x (xo + k) (xl - k) hkx
    generalize R.sum x xo k x (xo + k) (xl - k) = sx at *
    obtain ⟨-, v₃⟩ := ih (k + 1) (by lia) (R.zeros (k + k + 2)) 0 sx 0 (k + 1) rfl
      (by rw [R.size_zeros]; lia)
    rw [show k + 1 + (k + 1) = k + k + 2 by lia, sx₂] at v₃
    generalize sqrKaratsuba cfg (R.zeros (k + k + 2)) 0 sx 0 (k + 1) = z at *
    have hX := valAt_split x xo xl k (by lia)
    have hlt : valAt x xo xl * valAt x xo xl < 2 ^ (LA.w * (xl + xl)) := by
      rw [Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)
    have h₀ : valAt d₂ o (k + k) = valAt x xo k * valAt x xo k := by
      rw [← v₁]; exact w₂.valAt_eq (by lia)
    rw [show xl - k + (xl - k) = xl + xl - (k + k) by lia] at v₂ w₂
    rw [hX] at hlt ⊢
    obtain ⟨m₁, m₂⟩ := mid_step d₂ z o k (xl + xl) _ _ _ _ (by rw [w₂.1, w₁.1]; lia) (by lia) h₀
      v₂ v₃ hlt
    exact ⟨m₁.trans ((w₂.mono (by lia) (by lia)).trans (w₁.mono (by lia) (by lia))), m₂⟩
  · exact R.sqrBase_spec d o x xo xl hd

end MPN.Toom
