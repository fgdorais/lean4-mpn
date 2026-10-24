/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Bits

/-!
# Division by a limb

`divRem1 r a d` writes the limbs of `a / d` into `r` and returns `a % d`, like GMP's
`mpn_divrem_1`, from the top limb down: each step divides the remainder so far, followed by the
next limb, by `d` with `UInt64.div2`. The remainder stays below `d`, so this two-limb number is
below `d β` and its quotient fits in a limb.
-/

open ScalarArray UInt64Array

namespace MPN

private theorem ne_zero_toNat {j : USize} (hj : ¬j = 0) : j.toNat ≠ 0 :=
  fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))

/--
Divides `c βʲ` plus limbs `0` to `j - 1` of `a` by `d`, from limb `j - 1` down, writing the
quotient limbs into `arr` from limb `rs` on, and returns the remainder.
-/
public def divRem1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (d : UInt64) (j : USize)
    (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64) : UInt64Array × UInt64 :=
  if hj : j = 0 then (arr, c)
  else
    have hp := toNat_pred hj
    have hj₀ := ne_zero_toNat hj
    have hlt : j - 1 < a.size := by
      have := USize.le_iff_toNat_le.1 ha
      rw [USize.lt_iff_toNat_lt]; lia
    have hi : (rs + (j - 1)).toNat < arr.size := by
      rw [USize.toNat_add_of_lt (by lia), hp]; lia
    let x := a[j - 1]'hlt
    let q := UInt64.div2 c x d
    divRem1Loop (arr.uset (rs + (j - 1)) q hi) rs a d (j - 1) (USize.le_of_lt hlt)
      ⟨by rw [size_uset, hp]; lia, by rw [hp]; lia⟩ (x - q * d)
termination_by j.toNat
decreasing_by have := toNat_pred hj; have := ne_zero_toNat hj; lia

private theorem divRem1Loop_frame (arr : UInt64Array) (rs : USize) (a : USlice) (d : UInt64)
    (j : USize) (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64) :
    (divRem1Loop arr rs a d j ha hr c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) →
        (divRem1Loop arr rs a d j ha hr c).1[i]! = arr[i]!) := by
  induction arr, j, ha, hr, c using divRem1Loop.induct rs a d with
  | case1 arr ha hr c =>
    rw [divRem1Loop]
    simp
  | case2 arr j ha hr c hj hp hj₀ hlt hi x q ih =>
    rw [divRem1Loop, dite_eq_right hj]
    obtain ⟨i₁, i₂⟩ := ih
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by lia), hp]
    rw [hp] at i₂
    simp only [size_uset] at i₁
    refine ⟨i₁, fun i hi' => ?_⟩
    rw [i₂ i (by lia), getElem!_uset]
    simp only [hidx]
    split <;> lia

private theorem divRem1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (d : UInt64)
    (j : USize) (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64)
    (hc : c.toNat < d.toNat) :
    (divRem1Loop arr rs a d j ha hr c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) →
        (divRem1Loop arr rs a d j ha hr c).1[i]! = arr[i]!) ∧
      d.toNat * (divRem1Loop arr rs a d j ha hr c).1.valAt rs.toNat j.toNat +
          (divRem1Loop arr rs a d j ha hr c).2.toNat =
        c.toNat * 2 ^ (64 * j.toNat) + a.array.valAt a.start.toNat j.toNat ∧
      (divRem1Loop arr rs a d j ha hr c).2.toNat < d.toNat := by
  induction arr, j, ha, hr, c using divRem1Loop.induct rs a d with
  | case1 arr ha hr c =>
    rw [divRem1Loop]
    simp [hc]
  | case2 arr j ha hr c hj hp hj₀ hlt hi x q ih =>
    rw [divRem1Loop, dite_eq_right hj]
    dsimp only
    obtain ⟨hrem, hdq⟩ := UInt64.toNat_div2_rem c x d hc
    have hrem' : (x - q * d).toNat < d.toNat := by
      rw [hrem]; exact Nat.mod_lt _ (by lia)
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih hrem'
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by lia), hp]
    rw [hp] at i₂ i₃
    simp only [size_uset] at i₁
    have hout := i₂ (rs.toNat + (j.toNat - 1)) (.inr (Nat.le_refl _))
    rw [getElem!_uset, hidx] at hout
    simp only [↓reduceIte] at hout
    have hlo : (arr.uset (rs + (j - 1)) q hi).valAt rs.toNat (j.toNat - 1) =
        arr.valAt rs.toNat (j.toNat - 1) := valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    refine ⟨i₁, fun i hi' => ?_, ?_, i₄⟩
    · rw [i₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · have e : j.toNat = (j.toNat - 1) + 1 := by lia
      have hx : x = a.array[a.start.toNat + (j.toNat - 1)]! := by
        show a[j - 1]'hlt = _
        rw [USlice.getElem_eq_getElem!, hp]
      rw [e, UInt64Array.valAt_add, UInt64Array.valAt_add, valAt_one, valAt_one, hout, ← hx,
        show 64 * (j.toNat - 1 + 1) = 64 * (j.toNat - 1) + 64 by lia, Nat.pow_add]
      simp only [q] at i₃ hdq ⊢
      generalize (divRem1Loop _ _ _ _ _ _ _ _).1.valAt _ _ = V at *
      generalize (divRem1Loop _ _ _ _ _ _ _ _).2.toNat = r at *
      generalize (x - UInt64.div2 c x d * d).toNat = r₁ at *
      generalize (UInt64.div2 c x d).toNat = q₁ at *
      generalize a.array.valAt _ (j.toNat - 1) = A at *
      generalize 2 ^ (64 * (j.toNat - 1)) = P at *
      grind

/--
Writes the limbs of `a / d` into `r` and returns `a % d`, on the first `min r.size a.size` limbs,
like GMP's `mpn_divrem_1`. It requires `0 < d`.
-/
public def divRem1 (r a : USlice) (d : UInt64) : UInt64Array × UInt64 :=
  divRem1Loop r.array r.start a d (min a.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0

@[simp] public theorem size_divRem1 (r a : USlice) (d : UInt64) :
    (divRem1 r a d).1.size = r.array.size :=
  (divRem1Loop_frame ..).1

/-- `divRem1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_divRem1 (r a : USlice) (d : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (divRem1 r a d).1[i]! = r.array[i]! :=
  (divRem1Loop_frame ..).2 i (by rw [USize.toNat_min]; exact hi)

private theorem divRem1_full (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    d.toNat * (divRem1 r a d).1.valAt r.start.toNat a.size.toNat + (divRem1 r a d).2.toNat =
      a.toNat ∧ (divRem1 r a d).2.toNat < d.toNat := by
  have h := USize.le_iff_toNat_le.1 har
  obtain ⟨-, -, i₃, i₄⟩ := divRem1Loop_spec r.array r.start a d _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 (by rw [UInt64.toNat_zero]; exact hd)
  simp only [USize.toNat_min, show min a.size.toNat r.size.toNat = a.size.toNat by lia,
    UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add] at i₃
  exact ⟨by rw [USlice.toNat_eq_valAt]; exact i₃, i₄⟩

public theorem valAt_divRem1 (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1 r a d).1.valAt r.start.toNat a.size.toNat = a.toNat / d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1_full r a d hd har
  rw [← h₁, Nat.mul_add_div hd, Nat.div_eq_of_lt h₂, Nat.add_zero]

/-- The remainder of `divRem1` is `a % d`. -/
public theorem toNat_divRem1_snd (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1 r a d).2.toNat = a.toNat % d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1_full r a d hd har
  rw [← h₁, Nat.mul_add_mod, Nat.mod_eq_of_lt h₂]

end MPN
