/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Generic.Ops64Base
public import MPN.Generic.DC
public import MPN.Generic.Barrett
public import MPN.Div.Driver

/-!
# Divide-and-conquer division

`Num.divMod a b` and `Num.div a b` are `main`'s `Div.divRemG` and `Div.divQG` (`MPN.Div.Driver`) on
the limbs of `b` up to its top nonzero one, past a divisor of one limb (`divModBase`): the
schoolbook method below `config.divDC` limbs in `b`, and above `main`'s base-generic
divide-and-conquer division (`NatOps.divNorm`, the scheme of Burnikel and Ziegler and of GMP's
`mpn_dcpi1_div_qr`) on `ops64B`, the instance of `NatOps` with the schoolbook division at the
bottom, of the operands shifted left by the bits that set the top bit of `b`, which keeps each
digit's estimate within two of the digit; the remainder is shifted back.
-/

open ScalarArray UInt64Array

namespace MPN.W64.Num

/-- `βˢ - 1`, in `s` limbs. -/
public def allOnes (s : Nat) : UInt64Array := UInt64Array.replicate s 0xFFFFFFFFFFFFFFFF

private theorem valAt_allOnes (s lo m : Nat) (h : lo + m ≤ s) :
    (allOnes s).valAt lo m = 2 ^ (64 * m) - 1 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    have hx : (allOnes s)[lo]!.toNat = 2 ^ 64 - 1 := by
      rw [allOnes, getElem!_eq_getElem!_toArray, toArray_replicate]
      simp [show lo < s by lia]
    rw [valAt_succ, ih (lo + 1) (by lia), hx]
    have := Nat.one_le_two_pow (n := 64 * m)
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_sub, Nat.mul_one]
    lia

public theorem toNat_allOnes (s : Nat) : (allOnes s).toNat = 2 ^ (64 * s) - 1 := by
  rw [toNat_eq_valAt, show (allOnes s).size = s by simp [allOnes]]
  exact valAt_allOnes s 0 s (by lia)

public theorem size_allOnes (s : Nat) : (allOnes s).size = s := by simp [allOnes]

/--
`x` in at most `m` limbs, for `x < βᵐ`: itself when it has no more, its low `m` limbs otherwise
(by `Nat` past the sizes that fit in memory, a branch that cannot run).
-/
public def fitTo (x : UInt64Array) (m : Nat) : UInt64Array :=
  if x.size ≤ m then x else if fits (x.size + 1) then low x m else ofNatN x.toNat m

public theorem fitTo_spec (x : UInt64Array) (m : Nat) (hv : x.toNat < 2 ^ (64 * m)) :
    (fitTo x m).toNat = x.toNat ∧ (fitTo x m).size ≤ m := by
  unfold fitTo
  split
  · exact ⟨rfl, by lia⟩
  · rename_i h
    split
    · rename_i hf
      have := lt_of_fits hf
      rw [toNat_low _ _ (by lia), Nat.mod_eq_of_lt hv, size_low _ _ (by lia)]
      exact ⟨rfl, by lia⟩
    · rw [toNat_ofNatN, Nat.mod_eq_of_lt hv, size_ofNatN]
      exact ⟨rfl, by lia⟩

/-! ## Division -/

/-- `main`'s `Div.divRemG` on `ops64B`: the numbers are the arrays themselves. -/
private theorem driverOK : MPN.Div.DriverOK ops64B divBase64 id id where
  B_eq := rfl
  val_toα _ := rfl
  val_ofα _ := rfl
  base_ok U V h := by
    simp only [ops64B_val] at h ⊢
    exact val_divBase64 U V (by lia)

/-- The top nonzero limb of `b > 0` is limb `⌊log₂ b⌋ / 64`. -/
private theorem top_log2 (b : UInt64Array) (hb : 0 < b.toNat) :
    _root_.Nat.log2 b.toNat / 64 + 1 ≤ b.size ∧
      b.valAt 0 (_root_.Nat.log2 b.toNat / 64 + 1) = b.toNat ∧
      LimbArray.val UInt64Array (LimbArray.get b (0 + (_root_.Nat.log2 b.toNat / 64 + 1) - 1)) ≠
        0 := by
  generalize hl : _root_.Nat.log2 b.toNat = L
  have hb₀ : b.toNat ≠ 0 := by lia
  have hlo : 2 ^ L ≤ b.toNat := by rw [← hl]; exact Nat.log2_self_le hb₀
  have hhi : b.toNat < 2 ^ (L + 1) := by rw [← hl]; exact Nat.lt_log2_self
  have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hup : b.toNat < 2 ^ (64 * (L / 64 + 1)) :=
    Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by lia))
  have hlow : 2 ^ (64 * (L / 64)) ≤ b.toNat :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hlo
  have hnb : L / 64 + 1 ≤ b.size := by
    refine Nat.le_of_not_lt fun h => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 64 * b.size ≤ 64 * (L / 64) by lia)
    lia
  have hv : b.valAt 0 (L / 64 + 1) = b.toNat := by
    rw [valAt_mod _ _ hnb, ← toNat_eq_valAt, Nat.mod_eq_of_lt hup]
  refine ⟨hnb, hv, ?_⟩
  rw [Nat.zero_add, Nat.add_sub_cancel]
  intro h0
  have e := UInt64Array.valAt_add b 0 (L / 64) 1
  rw [valAt_one, Nat.zero_add, hv] at e
  have h0' : (b[L / 64]!).toNat = 0 := h0
  rw [h0'] at e
  have := valAt_lt b 0 (L / 64)
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 64 * (L / 64) ≤ L by lia)
  lia

/--
`(a / b, a % b)`, for `0 < b`: by `divModBase` (`divRem1`) for a divisor of one limb, and otherwise
by `main`'s `Div.divRemG` on the limbs of `b` up to its top nonzero one, which `log2` finds: the
schoolbook division below `config.divDC` limbs, and from there the normalized operands divided on
`ops64B` by the shared dispatch (`Dispatch.divN`: `NatOps.divNorm`, or from `config.divMu` limbs
Barrett's division with Newton's reciprocal).
-/
public def divMod (a b : UInt64Array) : UInt64Array × UInt64Array :=
  let nb := MPN.W64.log2 b.toUSlice / 64 + 1
  if 2 ≤ nb then
    let p := MPN.Div.divRemG ops64B divBase64 id id config.toDivConfig div32RecipU div2RowsU a 0
      a.size b 0 nb
    (fitTo p.1 (a.size + 1), fitTo p.2 (max a.size b.size))
  else divModBase a b

private theorem divMod_dc (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat ∧
      (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size := by
  have hL : MPN.W64.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by
    rw [log2_eq, toUSlice_toNat b (by lia)]
  obtain ⟨hnb, hv, ht⟩ := top_log2 b hb
  unfold divMod
  dsimp only
  rw [hL]
  split
  · rename_i h2
    obtain ⟨d₁, d₂⟩ := MPN.Div.divRemG_spec driverOK config.toDivConfig div32RecipU div2RowsU a
      0 a.size b 0 _ h2 ht
    have hv' : LimbArray.valAt b 0 (_root_.Nat.log2 b.toNat / 64 + 1) = b.toNat := hv
    have ha' : LimbArray.valAt a 0 a.size = a.toNat := (toNat_eq_valAt a).symm
    rw [hv', ha'] at d₁ d₂
    have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hqa : a.toNat / b.toNat < 2 ^ (64 * (a.size + 1)) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia)))
    have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hrb : a.toNat % b.toNat < 2 ^ (64 * max a.size b.size) :=
      Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ hb) hB)
        (Nat.pow_le_pow_right (by decide) (by lia))
    generalize MPN.Div.divRemG ops64B divBase64 id id config.toDivConfig div32RecipU div2RowsU a
      0 a.size b 0 (_root_.Nat.log2 b.toNat / 64 + 1) = p at d₁ d₂
    have e₁ : p.1.toNat = a.toNat / b.toNat := by rw [toNat_eq_valAt]; exact d₁
    have e₂ : p.2.toNat = a.toNat % b.toNat := by rw [toNat_eq_valAt]; exact d₂
    obtain ⟨q₁, q₂⟩ := fitTo_spec p.1 (a.size + 1) (by rw [e₁]; exact hqa)
    obtain ⟨t₁, t₂⟩ := fitTo_spec p.2 (max a.size b.size) (by rw [e₂]; exact hrb)
    exact ⟨by rw [q₁, e₁], by rw [t₁, e₂], q₂, t₂⟩
  · exact divModBase_spec a b hb hU

public theorem toNat_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat :=
  ⟨(divMod_dc a b hb hU).1, (divMod_dc a b hb hU).2.1⟩

public theorem size_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size :=
  (divMod_dc a b hb hU).2.2

/--
`a / b`, for `0 < b`: as `divMod`, by `main`'s `Div.divQG`, from `config.divQMu` limbs of `b` by
Barrett's division of the normalized `a` and `b` without the last remainder when the estimate
decides (`NatOps.divQMuW`).
-/
public def div (a b : UInt64Array) : UInt64Array :=
  let nb := MPN.W64.log2 b.toUSlice / 64 + 1
  if 2 ≤ nb then
    fitTo (MPN.Div.divQG ops64B divBase64 id id config.toDivConfig div32RecipU div2RowsU a 0
      a.size b 0 nb) (a.size + 1)
  else (divModBase a b).1

public theorem toNat_div (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) : (div a b).toNat = a.toNat / b.toNat := by
  have hL : MPN.W64.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by
    rw [log2_eq, toUSlice_toNat b (by lia)]
  obtain ⟨hnb, hv, ht⟩ := top_log2 b hb
  unfold div
  dsimp only
  rw [hL]
  split
  · rename_i h2
    have d := MPN.Div.divQG_spec driverOK config.toDivConfig div32RecipU div2RowsU a 0 a.size b
      0 _ h2 ht
    have hv' : LimbArray.valAt b 0 (_root_.Nat.log2 b.toNat / 64 + 1) = b.toNat := hv
    have ha' : LimbArray.valAt a 0 a.size = a.toNat := (toNat_eq_valAt a).symm
    rw [hv', ha'] at d
    have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hqa : a.toNat / b.toNat < 2 ^ (64 * (a.size + 1)) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia)))
    have e : (MPN.Div.divQG ops64B divBase64 id id config.toDivConfig div32RecipU div2RowsU a 0
        a.size b 0 (_root_.Nat.log2 b.toNat / 64 + 1)).toNat = a.toNat / b.toNat := by
      rw [toNat_eq_valAt]; exact d
    rw [(fitTo_spec _ (a.size + 1) (by rw [e]; exact hqa)).1, e]
  · exact (toNat_divModBase a b hb hU).1

end MPN.W64.Num
