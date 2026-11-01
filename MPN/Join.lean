/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Shift

/-!
# Joining windows of limbs

`joinW k x xo xn y yo yn` is the number `x βᵏ + y mod βᵏ` for the windows `x` of `xn` limbs from
`xo` and `y` of `yn` limbs from `yo`, in an array `z` of `k + xn` zeros: the low `min k yn` limbs of
`y`, then zeros, then the limbs of `x`, by two copies (`copyW`) into one array, instead of a shift,
a cut and an addition, which take three.
-/

namespace MPN.WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-- `min` of `USize`s, on their values. -/
public theorem toNat_minU (a b : USize) : (min a b).toNat = min a.toNat b.toNat := by
  by_cases h : a ≤ b
  · rw [show min a b = a from ite_eq_left h, Nat.min_eq_left (USize.le_iff_toNat_le.1 h)]
  · rw [show min a b = b from ite_eq_right h,
      Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le fun e => h (USize.le_iff_toNat_le.2 e)))]

/-- The bounds of `joinW`: both windows fit, and `z` is `k + xn` zeros. -/
public structure JoinOK (k : USize) (x : A) (xo xn : USize) (y : A) (yo yn : USize) (z : A) :
    Prop where
  hx : LoopBound x xo xn
  hy : LoopBound y yo yn
  hk : k.toNat + xn.toNat < USize.size
  hzs : LA.size z = k.toNat + xn.toNat
  hz0 : ∀ i, LA.val (LA.get z i) = 0

omit R F in
public theorem JoinOK.hz {k : USize} {x : A} {xo xn : USize} {y : A} {yo yn : USize} {z : A}
    (h : JoinOK k x xo xn y yo yn z) : LoopBound z 0 (min k yn) := by
  have := toNat_minU k yn
  have := h.hzs
  refine ⟨?_, ?_⟩ <;> simp only [USize.toNat_zero, Nat.zero_add] <;> lia

omit R F in
public theorem JoinOK.hym {k : USize} {x : A} {xo xn : USize} {y : A} {yo yn : USize} {z : A}
    (h : JoinOK k x xo xn y yo yn z) : LoopBound y yo (min k yn) := by
  have := toNat_minU k yn
  have := h.hy
  exact ⟨by lia, by lia⟩

variable (A) in
/-- `x βᵏ + y mod βᵏ`, in the `k + xn` zeros of `z`, by two copies. -/
@[inline, expose] public def joinW (k : USize) (x : A) (xo xn : USize) (y : A) (yo yn : USize)
    (z : A) (h : JoinOK k x xo xn y yo yn z) : A :=
  let r := copyW z 0 y yo (min k yn) h.hz h.hym
  copyW r k x xo xn ⟨by rw [size_copyW, h.hzs]; lia, by have := h.hk; lia⟩ h.hx

/-- The second copy of `joinW`, on any array that holds the first. -/
private theorem join_aux (k : USize) (x : A) (xo xn : USize) (y : A) (yo yn : USize)
    (z : A) (h : JoinOK k x xo xn y yo yn z) (r₁ : A) (a₁ : LA.size r₁ = k.toNat + xn.toNat)
    (a₂ : ∀ i, (min k yn).toNat ≤ i → LA.val (LA.get r₁ i) = 0)
    (a₃ : LimbArray.valAt r₁ 0 (min k yn).toNat = LimbArray.valAt y yo.toNat (min k yn).toNat)
    (hb : LoopBound r₁ k xn) :
    LA.size (copyW r₁ k x xo xn hb h.hx) = k.toNat + xn.toNat ∧
      LimbArray.valAt (copyW r₁ k x xo xn hb h.hx) 0 (k.toNat + xn.toNat) =
        LimbArray.valAt x xo.toNat xn.toNat * 2 ^ (LA.w * k.toNat) +
          LimbArray.valAt y yo.toNat yn.toNat % 2 ^ (LA.w * k.toNat) := by
  have hm := toNat_minU k yn
  obtain ⟨b₁, b₂, b₃⟩ := copyW_spec r₁ k x xo xn hb h.hx
  generalize copyW r₁ k x xo xn hb h.hx = r₂ at b₁ b₂ b₃ ⊢
  refine ⟨by rw [b₁, a₁], ?_⟩
  rw [LimbArray.valAt_add, Nat.zero_add, b₃]
  -- The low `k` limbs are those of `y`, then zeros.
  have hlow : LimbArray.valAt r₂ 0 k.toNat =
      LimbArray.valAt y yo.toNat yn.toNat % 2 ^ (LA.w * k.toNat) := by
    rw [LimbArray.valAt_congr k.toNat fun i _ hi => b₂ i (.inl (by lia))]
    have hsplit : LimbArray.valAt r₁ 0 k.toNat = LimbArray.valAt r₁ 0 (min k yn).toNat +
        2 ^ (LA.w * (min k yn).toNat) *
          LimbArray.valAt r₁ (min k yn).toNat (k.toNat - (min k yn).toNat) := by
      have := LimbArray.valAt_add r₁ 0 (min k yn).toNat (k.toNat - (min k yn).toNat)
      rwa [Nat.zero_add, show (min k yn).toNat + (k.toNat - (min k yn).toNat) = k.toNat by lia]
        at this
    rw [hsplit, a₃]
    have hz : LimbArray.valAt r₁ (min k yn).toNat (k.toNat - (min k yn).toNat) = 0 :=
      LimbArray.valAt_eq_zero _ fun i h₁ _ => a₂ i h₁
    rw [hz, Nat.mul_zero, Nat.add_zero]
    by_cases hky : k.toNat ≤ yn.toNat
    · rw [show (min k yn).toNat = k.toNat by lia]
      exact LimbArray.valAt_mod y yo.toNat hky
    · rw [show (min k yn).toNat = yn.toNat by lia, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le (LimbArray.valAt_lt ..)
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by lia)))
  rw [hlow, Nat.add_comm, Nat.mul_comm]

public theorem joinW_spec (k : USize) (x : A) (xo xn : USize) (y : A) (yo yn : USize)
    (z : A) (h : JoinOK k x xo xn y yo yn z) :
    LA.size (joinW A k x xo xn y yo yn z h) = k.toNat + xn.toNat ∧
      LimbArray.valAt (joinW A k x xo xn y yo yn z h) 0 (k.toNat + xn.toNat) =
        LimbArray.valAt x xo.toNat xn.toNat * 2 ^ (LA.w * k.toNat) +
          LimbArray.valAt y yo.toNat yn.toNat % 2 ^ (LA.w * k.toNat) := by
  obtain ⟨a₁, a₂, a₃⟩ := copyW_spec z 0 y yo (min k yn) h.hz h.hym
  rw [h.hzs] at a₁
  rw [USize.toNat_zero] at a₂ a₃
  exact join_aux k x xo xn y yo yn z h _ a₁
    (fun i hi => by rw [a₂ i (.inr (by lia))]; exact h.hz0 _) a₃ _

end MPN.WordArray
