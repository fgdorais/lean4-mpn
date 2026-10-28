/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Methods

/-!
# Products and squares by the Toom methods

`mulToom cfg d o a ao al b bo bl` writes the `al + bl` limbs of `a b` into `d` from limb `o` on:
by Toom-6, Toom-4 or Toom-4 by 3 from `cfg.mulToom6` and `cfg.mulToom4` limbs in the smaller
operand, by Toom-3, Toom-3 by 2 or Toom-4 by 2 from `cfg.mulToom3`, `cfg.mulToom32` and
`cfg.mulToom42`, by the shape of the operands, and by `mulKaratsuba` below or otherwise, with the
products of the methods computed recursively. `sqrToom` does the same for squares.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : ToomOps A L]

/-- The least of the thresholds of the Toom methods, from which `mulToom` tries them. -/
@[expose] public def toomMin (cfg : Config) : Nat :=
  min (min (min cfg.mulToom3 cfg.mulToom32) (min cfg.mulToom42 cfg.mulToom43))
    (min cfg.mulToom4 cfg.mulToom6)

public theorem twelve_le_toomMin (cfg : Config) : 12 ≤ toomMin cfg := by
  have := cfg.twelve_le_mulToom3; have := cfg.twelve_le_mulToom32
  have := cfg.twelve_le_mulToom42; have := cfg.thirtytwo_le_mulToom43
  have := cfg.thirtytwo_le_mulToom4; have := cfg.thirtytwo_le_mulToom6
  simp only [toomMin]; lia

/-- `mulToom`, recursively, the methods chosen when `bl ≤ al`. -/
@[expose, specialize] public def mulToomAux (cfg : Config) (d : A) (o : Nat) (a : A) (ao al : Nat)
    (b : A) (bo bl : Nat) : A :=
  let mul : MulFn A (al + bl) := fun d' o' a' ao' al' b' bo' bl' _ =>
    if bl' ≤ al' then mulToomAux cfg d' o' a' ao' al' b' bo' bl'
    else mulToomAux cfg d' o' b' bo' bl' a' ao' al'
  if h : toomMin cfg ≤ bl ∧ bl ≤ al then
    have := Nat.le_trans (twelve_le_toomMin cfg) h.1
    if h₆₆ : cfg.mulToom6 ≤ bl ∧ 5 * ((al + 5) / 6) < bl then
      toom66 d o a ao al b bo bl ((al + 5) / 6) (by
        have := cfg.thirtytwo_le_mulToom6; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₄₄ : cfg.mulToom4 ≤ bl ∧ 3 * ((al + 3) / 4) < bl then
      toom44 d o a ao al b bo bl ((al + 3) / 4) (by
        have := cfg.thirtytwo_le_mulToom4; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₄₃ : cfg.mulToom43 ≤ bl ∧ 2 * ((al + 3) / 4) < bl ∧ bl ≤ 3 * ((al + 3) / 4) then
      toom43 d o a ao al b bo bl ((al + 3) / 4) (by
        have := cfg.thirtytwo_le_mulToom43; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₃₃ : cfg.mulToom3 ≤ bl ∧ 2 * ((al + 2) / 3) < bl then
      toom33 d o a ao al b bo bl ((al + 2) / 3) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₃₂ : cfg.mulToom32 ≤ bl ∧ (al + 2) / 3 < bl ∧ bl ≤ 2 * ((al + 2) / 3) then
      toom32 d o a ao al b bo bl ((al + 2) / 3) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₄₂ : cfg.mulToom42 ≤ bl ∧ (al + 3) / 4 < bl ∧ bl ≤ 2 * ((al + 3) / 4) then
      toom42 d o a ao al b bo bl ((al + 3) / 4) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else
      mulKaratsuba cfg d o a ao al b bo bl
  else
    mulKaratsuba cfg d o a ao al b bo bl
termination_by al + bl
decreasing_by all_goals lia

/-- Writes `a b` into the `al + bl` limbs of `d` from `o`, by the Toom methods. -/
@[expose, specialize] public def mulToom (cfg : Config) (d : A) (o : Nat) (a : A) (ao al : Nat)
    (b : A) (bo bl : Nat) : A :=
  if bl ≤ al then mulToomAux cfg d o a ao al b bo bl else mulToomAux cfg d o b bo bl a ao al

omit R in
/-- A product with the operands swapped. -/
private theorem swap {d d' : A} {o : Nat} {x y : A} {xo xl yo yl : Nat}
    (h : Writes d' d o (yl + xl) ∧ valAt d' o (yl + xl) = valAt y yo yl * valAt x xo xl) :
    Writes d' d o (xl + yl) ∧ valAt d' o (xl + yl) = valAt x xo xl * valAt y yo yl := by
  rw [Nat.add_comm yl, Nat.mul_comm] at h; exact h

private theorem mulToomAux_spec (cfg : Config) : ∀ N (d : A) (o : Nat) (a : A) (ao al : Nat)
    (b : A) (bo bl : Nat), al + bl = N → o + (al + bl) ≤ LA.size d →
    Writes (mulToomAux cfg d o a ao al b bo bl) d o (al + bl) ∧
      valAt (mulToomAux cfg d o a ao al b bo bl) o (al + bl) = valAt a ao al * valAt b bo bl := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro d o a ao al b bo bl hN hd
  have hmul : IsMul (A := A) (N := al + bl) fun d' o' a' ao' al' b' bo' bl' _ =>
      if bl' ≤ al' then mulToomAux cfg d' o' a' ao' al' b' bo' bl'
      else mulToomAux cfg d' o' b' bo' bl' a' ao' al' := by
    intro d' o' a' ao' al' b' bo' bl' h' hd'
    dsimp only
    split
    · exact ih _ (by lia) _ _ _ _ _ _ _ _ rfl hd'
    · exact swap (ih _ (by lia) _ _ _ _ _ _ _ _ rfl (by lia))
  have hk := fun h => mulKaratsuba_spec (A := A) cfg al d o a ao al b bo bl rfl h
  rw [mulToomAux]
  dsimp only
  split
  · split
    · exact toom66_spec _ _ _ _ _ _ _ _ _ _ _ hmul hd
    · split
      · exact toom44_spec _ _ _ _ _ _ _ _ _ _ _ hmul hd
      · split
        · exact toom43_spec _ _ _ _ _ _ _ _ _ _ _ hmul hd
        · split
          · exact toom33_spec _ _ _ _ _ _ _ _ _ _ _ hmul hd
          · split
            · exact toom32_spec _ _ _ _ _ _ _ _ _ _ _ hmul hd
            · split
              · exact toom42_spec _ _ _ _ _ _ _ _ _ _ _ hmul hd
              · exact hk hd
  · exact hk hd

public theorem mulToom_spec (cfg : Config) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (hd : o + (al + bl) ≤ LA.size d) :
    Writes (mulToom cfg d o a ao al b bo bl) d o (al + bl) ∧
      valAt (mulToom cfg d o a ao al b bo bl) o (al + bl) = valAt a ao al * valAt b bo bl := by
  rw [mulToom]
  split
  · exact mulToomAux_spec cfg _ _ _ _ _ _ _ _ _ rfl hd
  · exact swap (mulToomAux_spec cfg _ _ _ _ _ _ _ _ _ rfl (by lia))

/-! ## Squares -/

/-- `sqrToom`, recursively. -/
@[expose, specialize] public def sqrToom (cfg : Config) (d : A) (o : Nat) (a : A)
    (ao al : Nat) : A :=
  let sq : SqrFn A al := fun d' o' a' ao' al' _ => sqrToom cfg d' o' a' ao' al'
  if h : cfg.sqrToom3 ≤ al then
    have := cfg.twelve_le_sqrToom3
    if h₆ : cfg.sqrToom6 ≤ al then
      toom6Sqr d o a ao al ((al + 5) / 6) (by
        have := cfg.thirtytwo_le_sqrToom6; refine ⟨?_, ?_, ?_⟩ <;> lia) sq
    else if h₄ : cfg.sqrToom4 ≤ al then
      toom4Sqr d o a ao al ((al + 3) / 4) (by
        have := cfg.thirtytwo_le_sqrToom4; refine ⟨?_, ?_, ?_⟩ <;> lia) sq
    else
      toom3Sqr d o a ao al ((al + 2) / 3) (by refine ⟨?_, ?_, ?_⟩ <;> lia) sq
  else
    sqrKaratsuba cfg d o a ao al
termination_by al
decreasing_by all_goals lia

private theorem sqrToom_spec' (cfg : Config) : ∀ N (d : A) (o : Nat) (a : A) (ao al : Nat),
    al = N → o + (al + al) ≤ LA.size d →
    Writes (sqrToom cfg d o a ao al) d o (al + al) ∧
      valAt (sqrToom cfg d o a ao al) o (al + al) = valAt a ao al * valAt a ao al := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro d o a ao al hN hd
  have hsq : IsSqr (A := A) (N := al) fun d' o' a' ao' al' _ => sqrToom cfg d' o' a' ao' al' :=
    fun d' o' a' ao' al' h' hd' => ih _ (by lia) _ _ _ _ _ rfl hd'
  rw [sqrToom]
  dsimp only
  split
  · split
    · exact toom6Sqr_spec _ _ _ _ _ _ _ _ hsq hd
    · split
      · exact toom4Sqr_spec _ _ _ _ _ _ _ _ hsq hd
      · exact toom3Sqr_spec _ _ _ _ _ _ _ _ hsq hd
  · exact sqrKaratsuba_spec cfg al d o a ao al rfl hd

public theorem sqrToom_spec (cfg : Config) (d : A) (o : Nat) (a : A) (ao al : Nat)
    (hd : o + (al + al) ≤ LA.size d) :
    Writes (sqrToom cfg d o a ao al) d o (al + al) ∧
      valAt (sqrToom cfg d o a ao al) o (al + al) = valAt a ao al * valAt a ao al :=
  sqrToom_spec' cfg _ _ _ _ _ _ rfl hd

end MPN.Toom
