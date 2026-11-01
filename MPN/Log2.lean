/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Init.Data.UInt.Log2
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2

/-!
# The base-two logarithm of a word

Lean's runtime computes `UInt64.log2` and `UInt32.log2` by a loop over the bits, one step per bit:
63 dependent steps for the largest words. `log2Fast` is a binary search instead, six steps of a
shift and a comparison for 64 bits and five for 32, without a loop, in portable code. `@[csimp]`
makes the compiler use it in place of `log2` in every module that imports this one.
-/

namespace MPN

/-- Halving the search: `log₂ n = log₂ (n / 2ᵏ) + k` when `2ᵏ ≤ n`. -/
public theorem log2_div_add {n k : Nat} (h : 2 ^ k ≤ n) : n.log2 = (n / 2 ^ k).log2 + k := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hm : n / 2 ^ k ≠ 0 := by
    have := (Nat.le_div_iff_mul_le hk).2 (show 1 * 2 ^ k ≤ n by lia); lia
  have hn : n ≠ 0 := by lia
  have h₁ := Nat.log2_self_le hm
  have h₂ := Nat.lt_log2_self (n := n / 2 ^ k)
  refine Nat.le_antisymm ?_ ?_
  · refine Nat.le_of_lt_succ ((Nat.log2_lt hn).2 ?_)
    rw [Nat.succ_eq_add_one, show (n / 2 ^ k).log2 + k + 1 = ((n / 2 ^ k).log2 + 1) + k by lia,
      Nat.pow_add]
    have := Nat.lt_mul_div_succ n hk
    have := Nat.mul_le_mul_left (2 ^ k) (show n / 2 ^ k + 1 ≤ 2 ^ ((n / 2 ^ k).log2 + 1) from h₂)
    rw [Nat.mul_comm (2 ^ k)] at this
    lia
  · refine (Nat.le_log2 hn).2 ?_
    rw [Nat.pow_add]
    calc 2 ^ (n / 2 ^ k).log2 * 2 ^ k ≤ n / 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ h₁
      _ ≤ n := Nat.div_mul_le_self n _

/-- One step of the search: below `2²ᵏ`, the logarithm is found in a value below `2ᵏ`. -/
private theorem log2_step {x k : Nat} (hx : x < 2 ^ (2 * k)) :
    let x' := if x / 2 ^ k ≠ 0 then x / 2 ^ k else x
    let d := if x / 2 ^ k ≠ 0 then k else 0
    x' < 2 ^ k ∧ x.log2 = x'.log2 + d := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases h : x / 2 ^ k ≠ 0
  · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
    refine ⟨(Nat.div_lt_iff_lt_mul hk).2 (by rw [← Nat.pow_add]; rwa [Nat.two_mul] at hx), ?_⟩
    exact log2_div_add (by
      refine Nat.le_of_not_lt fun hlt => h ?_
      exact Nat.div_eq_of_lt hlt)
  · simp only [h, ↓reduceIte, Nat.add_zero, and_true]
    have := (Nat.div_eq_zero_iff_lt hk).1 (by simpa using h)
    exact this

/-- One step of `log2Fast` on 64 bits: the shift `k` if `x` has bits from `k` on, or `0`. -/
@[inline, expose] public def _root_.UInt64.log2Shift (k x : UInt64) : UInt64 :=
  (decide (x >>> k ≠ 0)).toUInt64 * k

private theorem log2Shift_spec64 (k : UInt64) (hk : k.toNat < 64) (x : UInt64)
    (hx : x.toNat < 2 ^ (2 * k.toNat)) :
    (x >>> UInt64.log2Shift k x).toNat < 2 ^ k.toNat ∧
      x.toNat.log2 = (x >>> UInt64.log2Shift k x).toNat.log2 + (UInt64.log2Shift k x).toNat ∧
      (UInt64.log2Shift k x).toNat ≤ k.toNat := by
  obtain ⟨h₁, h₂⟩ := log2_step hx
  have hsh : (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
  have hne : (x >>> k ≠ 0) ↔ x.toNat / 2 ^ k.toNat ≠ 0 := by
    rw [← hsh]
    exact ⟨fun h e => h (UInt64.toNat_inj.1 (by rw [e]; rfl)), fun h e => h (by rw [e]; rfl)⟩
  unfold UInt64.log2Shift
  by_cases h : x.toNat / 2 ^ k.toNat = 0
  · have hd : decide (x >>> k ≠ 0) = false := by simp only [decide_eq_false_iff_not]; exact fun h' => hne.1 h' h
    simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, Nat.add_zero] at h₁ h₂
    rw [hd, show false.toUInt64 * k = 0 by rw [show false.toUInt64 = 0 from rfl, UInt64.zero_mul]]
    have e0 : x >>> (0 : UInt64) = x := UInt64.toNat_inj.1 (by rw [UInt64.toNat_shiftRight]; simp)
    rw [e0]
    exact ⟨h₁, by simp, by simp⟩
  · have hd : decide (x >>> k ≠ 0) = true := by simp only [decide_eq_true_eq]; exact hne.2 h
    simp only [h, ne_eq, not_false_eq_true, ↓reduceIte] at h₁ h₂
    rw [hd, show true.toUInt64 * k = k by rw [show true.toUInt64 = 1 from rfl, UInt64.one_mul], hsh]
    exact ⟨h₁, h₂, Nat.le_refl _⟩

/-- `UInt64.log2` by a binary search, without a branch. -/
@[expose] public def _root_.UInt64.log2Fast (x : UInt64) : UInt64 :=
  let c1 := UInt64.log2Shift 32 x
  let x1 := x >>> c1
  let c2 := UInt64.log2Shift 16 x1
  let x2 := x1 >>> c2
  let c3 := UInt64.log2Shift 8 x2
  let x3 := x2 >>> c3
  let c4 := UInt64.log2Shift 4 x3
  let x4 := x3 >>> c4
  let c5 := UInt64.log2Shift 2 x4
  let x5 := x4 >>> c5
  let c6 := UInt64.log2Shift 1 x5
  c1 + c2 + c3 + c4 + c5 + c6

/-- `log2Fast` is `log2`. -/
public theorem _root_.UInt64.log2Fast_eq (x : UInt64) : x.log2Fast = x.log2 := by
  apply UInt64.toNat_inj.1
  have e : x.log2.toNat = x.toNat.log2 := by rfl
  rw [e]
  unfold UInt64.log2Fast
  dsimp only
  obtain ⟨a1, b1, d1⟩ := log2Shift_spec64 32 (by decide) x (by
    have := x.toNat_lt; simp only [UInt64.reduceToNat] at this ⊢; exact this)
  obtain ⟨a2, b2, d2⟩ := log2Shift_spec64 16 (by decide) (x >>> UInt64.log2Shift 32 x) (by
    have := a1; simp only [UInt64.reduceToNat] at this ⊢; exact this)
  obtain ⟨a3, b3, d3⟩ := log2Shift_spec64 8 (by decide) ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) (by
    have := a2; simp only [UInt64.reduceToNat] at this ⊢; exact this)
  obtain ⟨a4, b4, d4⟩ := log2Shift_spec64 4 (by decide) (((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x))) (by
    have := a3; simp only [UInt64.reduceToNat] at this ⊢; exact this)
  obtain ⟨a5, b5, d5⟩ := log2Shift_spec64 2 (by decide) ((((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x))) >>> UInt64.log2Shift 4 (((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)))) (by
    have := a4; simp only [UInt64.reduceToNat] at this ⊢; exact this)
  obtain ⟨a6, b6, d6⟩ := log2Shift_spec64 1 (by decide) (((((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x))) >>> UInt64.log2Shift 4 (((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)))) >>> UInt64.log2Shift 2 ((((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x))) >>> UInt64.log2Shift 4 (((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x)) >>> UInt64.log2Shift 8 ((x >>> UInt64.log2Shift 32 x) >>> UInt64.log2Shift 16 (x >>> UInt64.log2Shift 32 x))))) (by
    have := a5; simp only [UInt64.reduceToNat] at this ⊢; exact this)
  have hlast : ∀ y : Nat, y < 2 ^ 1 → y.log2 = 0 := fun y hy => by
    rw [Nat.log2_def]; simp; lia
  simp only [UInt64.reduceToNat] at *
  rw [hlast _ a6] at b6
  simp only [UInt64.toNat_add]
  generalize UInt64.log2Shift _ _ = s₁ at *
  lia

@[csimp] public theorem _root_.UInt64.log2_eq_log2Fast : @UInt64.log2 = @UInt64.log2Fast := by
  funext x; exact (UInt64.log2Fast_eq x).symm

/-- One step of `log2Fast` on 32 bits: the shift `k` if `x` has bits from `k` on, or `0`. -/
@[inline, expose] public def _root_.UInt32.log2Shift (k x : UInt32) : UInt32 :=
  (decide (x >>> k ≠ 0)).toUInt32 * k

private theorem log2Shift_spec32 (k : UInt32) (hk : k.toNat < 32) (x : UInt32)
    (hx : x.toNat < 2 ^ (2 * k.toNat)) :
    (x >>> UInt32.log2Shift k x).toNat < 2 ^ k.toNat ∧
      x.toNat.log2 = (x >>> UInt32.log2Shift k x).toNat.log2 + (UInt32.log2Shift k x).toNat ∧
      (UInt32.log2Shift k x).toNat ≤ k.toNat := by
  obtain ⟨h₁, h₂⟩ := log2_step hx
  have hsh : (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
    rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
  have hne : (x >>> k ≠ 0) ↔ x.toNat / 2 ^ k.toNat ≠ 0 := by
    rw [← hsh]
    exact ⟨fun h e => h (UInt32.toNat_inj.1 (by rw [e]; rfl)), fun h e => h (by rw [e]; rfl)⟩
  unfold UInt32.log2Shift
  by_cases h : x.toNat / 2 ^ k.toNat = 0
  · have hd : decide (x >>> k ≠ 0) = false := by simp only [decide_eq_false_iff_not]; exact fun h' => hne.1 h' h
    simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, Nat.add_zero] at h₁ h₂
    rw [hd, show false.toUInt32 * k = 0 by rw [show false.toUInt32 = 0 from rfl, UInt32.zero_mul]]
    have e0 : x >>> (0 : UInt32) = x := UInt32.toNat_inj.1 (by rw [UInt32.toNat_shiftRight]; simp)
    rw [e0]
    exact ⟨h₁, by simp, by simp⟩
  · have hd : decide (x >>> k ≠ 0) = true := by simp only [decide_eq_true_eq]; exact hne.2 h
    simp only [h, ne_eq, not_false_eq_true, ↓reduceIte] at h₁ h₂
    rw [hd, show true.toUInt32 * k = k by rw [show true.toUInt32 = 1 from rfl, UInt32.one_mul], hsh]
    exact ⟨h₁, h₂, Nat.le_refl _⟩

/-- `UInt32.log2` by a binary search, without a branch. -/
@[expose] public def _root_.UInt32.log2Fast (x : UInt32) : UInt32 :=
  let c1 := UInt32.log2Shift 16 x
  let x1 := x >>> c1
  let c2 := UInt32.log2Shift 8 x1
  let x2 := x1 >>> c2
  let c3 := UInt32.log2Shift 4 x2
  let x3 := x2 >>> c3
  let c4 := UInt32.log2Shift 2 x3
  let x4 := x3 >>> c4
  let c5 := UInt32.log2Shift 1 x4
  c1 + c2 + c3 + c4 + c5

/-- `log2Fast` is `log2`. -/
public theorem _root_.UInt32.log2Fast_eq (x : UInt32) : x.log2Fast = x.log2 := by
  apply UInt32.toNat_inj.1
  have e : x.log2.toNat = x.toNat.log2 := by rfl
  rw [e]
  unfold UInt32.log2Fast
  dsimp only
  obtain ⟨a1, b1, d1⟩ := log2Shift_spec32 16 (by decide) x (by
    have := x.toNat_lt; simp only [UInt32.reduceToNat] at this ⊢; exact this)
  obtain ⟨a2, b2, d2⟩ := log2Shift_spec32 8 (by decide) (x >>> UInt32.log2Shift 16 x) (by
    have := a1; simp only [UInt32.reduceToNat] at this ⊢; exact this)
  obtain ⟨a3, b3, d3⟩ := log2Shift_spec32 4 (by decide) ((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x)) (by
    have := a2; simp only [UInt32.reduceToNat] at this ⊢; exact this)
  obtain ⟨a4, b4, d4⟩ := log2Shift_spec32 2 (by decide) (((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x)) >>> UInt32.log2Shift 4 ((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x))) (by
    have := a3; simp only [UInt32.reduceToNat] at this ⊢; exact this)
  obtain ⟨a5, b5, d5⟩ := log2Shift_spec32 1 (by decide) ((((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x)) >>> UInt32.log2Shift 4 ((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x))) >>> UInt32.log2Shift 2 (((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x)) >>> UInt32.log2Shift 4 ((x >>> UInt32.log2Shift 16 x) >>> UInt32.log2Shift 8 (x >>> UInt32.log2Shift 16 x)))) (by
    have := a4; simp only [UInt32.reduceToNat] at this ⊢; exact this)
  have hlast : ∀ y : Nat, y < 2 ^ 1 → y.log2 = 0 := fun y hy => by
    rw [Nat.log2_def]; simp; lia
  simp only [UInt32.reduceToNat] at *
  rw [hlast _ a5] at b5
  simp only [UInt32.toNat_add]
  generalize UInt32.log2Shift _ _ = s₁ at *
  lia

@[csimp] public theorem _root_.UInt32.log2_eq_log2Fast : @UInt32.log2 = @UInt32.log2Fast := by
  funext x; exact (UInt32.log2Fast_eq x).symm

end MPN
