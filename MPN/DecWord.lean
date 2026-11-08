/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Trim
public import MPN.MulLimbW
public import MPN.Div.ByLimb

/-!
# The array operations of decimal strings, for limbs of any width

The operations that `DecOps` asks of a width's arrays, on any `WordArray`: `isZeroA` (by `ltA`),
`divRem1A`, the quotient and the remainder by a limb (by `divRem1W` into new limbs), and `mulAddA`,
`a m + v` (by `mul1W` into new limbs), the arrays trimmed to `k` limbs. Past the sizes of the
fast paths they compute from the values, which never happens.
-/

namespace MPN.WordArray

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

omit F in
/-- Whether `a` is zero, from its top limb down. -/
@[inline, expose] public def isZeroA (a : A) : Bool := !ltA (R.zeros 0) a

omit F in
public theorem isZeroA_iff (a : A) : isZeroA a = true ↔ valAt a 0 (LA.size a) = 0 := by
  rw [isZeroA, Bool.not_eq_true', ← Bool.not_eq_true, ltA_iff, R.size_zeros, valAt_zero]
  lia

variable (A) in
/-- A limb of value `v % 2ʷ`. -/
@[inline, expose] public def limbOf (v : Nat) : L := LA.get (LA.set (R.zeros 1) 0 v) 0

omit F in
public theorem val_limbOf (v : Nat) : LA.val (limbOf A v) = v % 2 ^ LA.w :=
  LA.val_get_set_self _ _ _ (by rw [R.size_zeros]; lia)

omit F in
/-- `a / d` and `a % d`, the quotient trimmed to `k` limbs, by `divRem1W` with the thresholds `t`
and `tu` into new limbs. -/
@[inline, expose] public def divRem1A (k : Nat) (t tu : USize) (a : A) (d : L) : A × L :=
  if h : fitsU (LA.size a) then
    let p := divRem1W A t tu (R.zeros (LA.size a)) 0 a 0 (LA.size a).toUSize
      (zeros_bound' (lt_of_fitsU h)) (full_bound a (lt_of_fitsU h)) d
    (trimTo k p.1, p.2)
  else
    (trimTo k (ofNatW (R := R) (valAt a 0 (LA.size a) / LA.val d)),
      limbOf A (valAt a 0 (LA.size a) % LA.val d))

omit F in
public theorem divRem1A_spec (k : Nat) (t tu : USize) (a : A) (d : L) (hd : 0 < LA.val d) :
    valAt (divRem1A k t tu a d).1 0 (LA.size (divRem1A k t tu a d).1) =
        valAt a 0 (LA.size a) / LA.val d ∧
      LA.val (divRem1A k t tu a d).2 = valAt a 0 (LA.size a) % LA.val d := by
  unfold divRem1A
  split
  · rename_i h
    have hU := lt_of_fitsU h
    have e := toNat_toUSize_of_lt hU
    obtain ⟨d₁, -, d₃, d₄⟩ := divRem1W_spec t tu (R.zeros (LA.size a)) 0 a 0
      (LA.size a).toUSize (zeros_bound' hU) (full_bound a hU) d hd
    simp only [USize.toNat_zero, e] at d₃
    rw [R.size_zeros] at d₁
    dsimp only
    rw [valAt_trimTo, d₁]
    generalize divRem1W A t tu (R.zeros (LA.size a)) 0 a 0 (LA.size a).toUSize
      (zeros_bound' hU) (full_bound a hU) d = q at d₁ d₃ d₄ ⊢
    have hq : valAt a 0 (LA.size a) / LA.val d = valAt q.1 0 (LA.size a) := by
      rw [← d₃, Nat.mul_add_div hd, Nat.div_eq_of_lt d₄, Nat.add_zero]
    have hr : valAt a 0 (LA.size a) % LA.val d = LA.val q.2 := by
      rw [← d₃, Nat.mul_add_mod, Nat.mod_eq_of_lt d₄]
    exact ⟨hq.symm, hr.symm⟩
  · dsimp only
    rw [valAt_trimTo, valAt_ofNatW, val_limbOf, Nat.mod_eq_of_lt]
    · exact ⟨rfl, rfl⟩
    · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_lt (LA.val_lt d))

/-- `a m + v`, trimmed to `k` limbs, by `mul1W` with the carry in `v`, into new limbs. -/
@[inline, expose] public def mulAddA (k : Nat) (a : A) (m v : L) : A :=
  if h : fitsU (LA.size a + 1) then
    let p := mul1W (R.zeros (LA.size a + 1)) 0 a 0 (LA.size a).toUSize m v
      (by
        have := zeros_bound' (R := R) (lt_of_fitsU h)
        exact ⟨by rw [R.size_zeros, toNat_toUSize_of_lt (by have := lt_of_fitsU h; lia)]; simp,
          by rw [toNat_toUSize_of_lt (by have := lt_of_fitsU h; lia)]; have := lt_of_fitsU h
             simp; lia⟩)
      (full_bound a (by have := lt_of_fitsU h; lia))
    trimTo k (R.uset p.1 (LA.size a).toUSize p.2
      (by rw [(mul1W_spec ..).1, R.size_zeros, toNat_toUSize_of_lt (by have := lt_of_fitsU h; lia)]
          lia))
  else trimTo k (ofNatW (R := R) (valAt a 0 (LA.size a) * LA.val m + LA.val v))

public theorem mulAddA_spec (k : Nat) (a : A) (m v : L) :
    valAt (mulAddA k a m v) 0 (LA.size (mulAddA k a m v)) =
      valAt a 0 (LA.size a) * LA.val m + LA.val v := by
  unfold mulAddA
  split
  · rename_i h
    have hU := lt_of_fitsU h
    have e := toNat_toUSize_of_lt (show LA.size a < USize.size by lia)
    obtain ⟨p₁, p₂, p₃⟩ := mul1W_spec (R.zeros (LA.size a + 1)) 0 a 0 (LA.size a).toUSize m v
      ⟨by rw [R.size_zeros, e]; simp, by rw [e]; simp; lia⟩ (full_bound a (by lia))
    simp only [USize.toNat_zero, e] at p₂ p₃
    simp only [R.size_zeros] at p₁
    dsimp only
    rw [valAt_trimTo]
    simp only [R.size_uset, p₁]
    rw [valAt_add, valAt_one, Nat.zero_add, R.get_uset, e]
    simp only [↓reduceIte]
    rw [valAt_uset_of _ _ _ _ _ _ (.inr (by rw [e]; lia))]
    exact p₃
  · rw [valAt_trimTo, valAt_ofNatW]

end MPN.WordArray
