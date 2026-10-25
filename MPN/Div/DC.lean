/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops64Base
public import MPN.Generic.DC

/-!
# Divide-and-conquer division

`Num.divMod a b` divides by the schoolbook method (`divModBase`) below `dcThreshold` limbs in `b`,
and above by `main`'s base-generic divide-and-conquer division (`NatOps.divNorm`, the scheme of
Burnikel and Ziegler and of GMP's `mpn_dcpi1_div_qr`) on `ops64B`, the instance of `NatOps` with
the schoolbook division at the bottom. It normalizes first, shifting `a` and `b` left by the bits
that set the top bit of `b`, which keeps each digit's estimate within two of the digit, and shifts
the remainder back.
-/

open ScalarArray UInt64Array

namespace MPN.Num

/-- The number of limbs of the divisor from which `divMod` divides by divide and conquer. -/
public def dcThreshold : Nat := 512

/-- `βˢ - 1`, in `s` limbs. -/
public def allOnes (s : Nat) : UInt64Array := UInt64Array.replicate s 0xFFFFFFFFFFFFFFFF

private theorem valAt_allOnes (s lo m : Nat) (h : lo + m ≤ s) :
    (allOnes s).valAt lo m = 2 ^ (64 * m) - 1 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    have hx : (allOnes s)[lo]!.toNat = 2 ^ 64 - 1 := by
      rw [allOnes, getElem!_eq_getElem!_data, data_replicate]
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

/--
`(a / b, a % b)`, for `0 < b`: when `b` has at least `dcThreshold` limbs, `a` and `b` are shifted
left by the `c` bits that set the top bit of `b`, divided by `NatOps.divNorm` on `ops64B`, and the
remainder is shifted back; otherwise `divModBase`.
-/
public def divMod (a b : UInt64Array) : UInt64Array × UInt64Array :=
  let L := MPN.log2 b.toUSlice
  let nb := L / 64 + 1
  if dcThreshold ≤ nb ∧ nb ≤ a.size ∧ 8 * a.size + 48 < USize.size then
    let c := 63 - L % 64
    let r := ops64B.divNorm divBase64 dcThreshold (low (shl a c) (a.size + 1)) (low (shl b c) nb)
      nb (a.size + 1 - nb)
    (fitTo r.1 (a.size + 1), fitTo (shr (fitTo r.2 nb) c) (max a.size b.size))
  else divModBase a b

private theorem divMod_dc (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat ∧
      (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size := by
  have hL : MPN.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by
    rw [log2_eq, toUSlice_toNat b (by lia)]
  unfold divMod
  dsimp only
  rw [hL]
  split
  · rename_i h
    generalize hl : _root_.Nat.log2 b.toNat = L at h ⊢
    have hb₀ : b.toNat ≠ 0 := by lia
    have hlo : 2 ^ L ≤ b.toNat := by rw [← hl]; exact Nat.log2_self_le hb₀
    have hhi : b.toNat < 2 ^ (L + 1) := by rw [← hl]; exact Nat.lt_log2_self
    have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hnb : L / 64 + 1 ≤ b.size := by
      refine Nat.le_of_not_lt fun h' => ?_
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 64 * b.size ≤ L by lia)
      lia
    generalize hnb' : L / 64 + 1 = nb at h hnb ⊢
    generalize hc : 63 - L % 64 = c
    have hLc : L + c + 1 = 64 * nb := by lia
    have hc64 : c < 64 := by lia
    -- The normalized divisor.
    have hVlt : b.toNat * 2 ^ c < 2 ^ (64 * nb) :=
      calc b.toNat * 2 ^ c < 2 ^ (L + 1) * 2 ^ c :=
            Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2 ^ (64 * nb) := by rw [← Nat.pow_add, ← hLc]; congr 1; lia
    have hVv : (low (shl b c) nb).toNat = b.toNat * 2 ^ c := by
      rw [toNat_low _ _ (by rw [size_shl]; lia), toNat_shl _ _ (by lia), Nat.mod_eq_of_lt hVlt]
    -- The normalized dividend.
    have hUv : (low (shl a c) (a.size + 1)).toNat = a.toNat * 2 ^ c := by
      rw [toNat_low _ _ (by rw [size_shl]; lia), toNat_shl _ _ (by lia), Nat.mod_eq_of_lt]
      calc a.toNat * 2 ^ c < 2 ^ (64 * a.size) * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia))
              (Nat.two_pow_pos _)
        _ = 2 ^ (64 * (a.size + 1)) := by rw [← Nat.pow_add]; congr 1
    have hUV : (low (shl a c) (a.size + 1)).toNat <
        (low (shl b c) nb).toNat * 2 ^ (64 * (a.size + 1 - nb)) := by
      rw [hUv, hVv, Nat.mul_right_comm]
      apply Nat.mul_lt_mul_of_pos_right _ (Nat.two_pow_pos _)
      calc a.toNat < 2 ^ (64 * a.size) := hA
        _ = 2 ^ (64 * (nb - 1)) * 2 ^ (64 * (a.size + 1 - nb)) := by
            rw [← Nat.pow_add]; congr 1; lia
        _ ≤ b.toNat * 2 ^ (64 * (a.size + 1 - nb)) := by
            apply Nat.mul_le_mul_right
            exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hlo
    have hb₀' : 0 < b.toNat * 2 ^ c := Nat.mul_pos hb (Nat.two_pow_pos _)
    obtain ⟨r₃, r₄⟩ := ops64B.divNorm_spec divBase64
      (fun U V hV => val_divBase64 U V (by simp only [ops64B_val] at hV; lia)) dcThreshold nb
      (a.size + 1 - nb) (low (shl a c) (a.size + 1)) (low (shl b c) nb)
      (by simp only [ops64B_val]; rw [hVv]; exact hb₀')
      (by simp only [ops64B_val, ops64B_B]; rw [hVv, ← Nat.pow_mul]; exact hVlt)
      (by simp only [ops64B_val, ops64B_B]; rw [← Nat.pow_mul]; exact hUV)
    simp only [ops64B_val] at r₃ r₄
    rw [hUv, hVv, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)] at r₃
    rw [hUv, hVv, Nat.mul_mod_mul_right] at r₄
    generalize ops64B.divNorm divBase64 dcThreshold (low (shl a c) (a.size + 1))
      (low (shl b c) nb) nb (a.size + 1 - nb) = r at r₃ r₄
    -- The quotient fits in `a.size + 1` limbs, and the remainder in `nb`, then in `b`'s.
    have hqa : a.toNat / b.toNat < 2 ^ (64 * (a.size + 1)) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia)))
    obtain ⟨q₁, q₂⟩ := fitTo_spec r.1 (a.size + 1) (by rw [r₃]; exact hqa)
    have hrm : a.toNat % b.toNat * 2 ^ c < 2 ^ (64 * nb) :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hb) (Nat.two_pow_pos _))
        (Nat.le_of_lt hVlt)
    obtain ⟨s₁, s₂⟩ := fitTo_spec r.2 nb (by rw [r₄]; exact hrm)
    have hsh : (shr (fitTo r.2 nb) c).toNat = a.toNat % b.toNat := by
      rw [toNat_shr _ _ (by lia), s₁, r₄, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    have hrb : a.toNat % b.toNat < 2 ^ (64 * max a.size b.size) :=
      Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ hb) hB)
        (Nat.pow_le_pow_right (by decide) (by lia))
    obtain ⟨t₁, t₂⟩ := fitTo_spec (shr (fitTo r.2 nb) c) (max a.size b.size) (by rw [hsh]; exact hrb)
    exact ⟨by rw [q₁, r₃], by rw [t₁, hsh], q₂, t₂⟩
  · obtain ⟨d₁, d₂⟩ := toNat_divModBase a b hb hU
    obtain ⟨e₁, e₂⟩ := size_divModBase a b (by lia)
    exact ⟨d₁, d₂, e₁, e₂⟩

public theorem toNat_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat :=
  ⟨(divMod_dc a b hb hU).1, (divMod_dc a b hb hU).2.1⟩

public theorem size_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size :=
  (divMod_dc a b hb hU).2.2

end MPN.Num
