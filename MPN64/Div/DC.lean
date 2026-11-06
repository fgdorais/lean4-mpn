/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Generic.Ops64Base
public import MPN.Generic.DC
public import MPN.Generic.Barrett
public import MPN.Div.Basecase

/-!
# Divide-and-conquer division

`Num.divMod a b` divides by the schoolbook method (`divModBase`) below `config.divDC` limbs in `b`,
and above by `main`'s base-generic divide-and-conquer division (`NatOps.divNorm`, the scheme of
Burnikel and Ziegler and of GMP's `mpn_dcpi1_div_qr`) on `ops64B`, the instance of `NatOps` with
the schoolbook division at the bottom. It normalizes first, shifting `a` and `b` left by the bits
that set the top bit of `b`, which keeps each digit's estimate within two of the digit, and shifts
the remainder back, by `main`'s `Schoolbook.shlArr`, `shlFitArr` and `shrArr`.
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

/-! ## Normalization

By `main`'s `Schoolbook.shlArr`, `shlFitArr` and `shrArr`, here as values.
-/

public theorem shlArr_toNat (a : UInt64Array) (c : Nat) (hc : c < 64)
    (hU : a.size + 1 < USize.size) :
    (Schoolbook.shlArr a c).toNat = a.toNat * 2 ^ c ∧ (Schoolbook.shlArr a c).size = a.size + 1 :=
  have h := Schoolbook.shlArr_spec a c hc hU
  ⟨by rw [toNat_eq_valAt, toNat_eq_valAt]; exact h.2, h.1⟩

public theorem shlFitArr_toNat (b : UInt64Array) (n c : Nat) (hc : c < 64) (hn : n ≤ b.size)
    (hU : b.size < USize.size) (hfit : b.toNat * 2 ^ c < 2 ^ (64 * n)) :
    (Schoolbook.shlFitArr b n c).toNat = b.toNat * 2 ^ c ∧ (Schoolbook.shlFitArr b n c).size = n :=
  have h := Schoolbook.shlFitArr_spec b n c hc hn hU (by rw [toNat_eq_valAt] at hfit; exact hfit)
  ⟨by rw [toNat_eq_valAt, toNat_eq_valAt]; exact h.2, h.1⟩

public theorem shrArr_toNat (r : UInt64Array) (c : Nat) (hc : c < 64) (hU : r.size < USize.size) :
    (Schoolbook.shrArr r c).toNat = r.toNat / 2 ^ c ∧ (Schoolbook.shrArr r c).size = r.size :=
  have h := Schoolbook.shrArr_spec r c hc hU
  ⟨by rw [toNat_eq_valAt, toNat_eq_valAt]; exact h.2, h.1⟩

/-! ## Division -/

/--
`(a / b, a % b)`, for `0 < b`: when `b` has at least `config.divDC` limbs, `a` and `b` are shifted
left by the `c` bits that set the top bit of `b`, divided on `ops64B` by the shared dispatch
(`Dispatch.divN`: `NatOps.divNorm`, or from `config.divMu` limbs Barrett's division with Newton's
reciprocal), and the remainder is shifted back; otherwise `divModBase`.
-/
public def divMod (a b : UInt64Array) : UInt64Array × UInt64Array :=
  let L := MPN.W64.log2 b.toUSlice
  let nb := L / 64 + 1
  if config.divDC ≤ nb ∧ nb ≤ a.size ∧ 8 * a.size + 48 < USize.size then
    let c := 63 - L % 64
    let r := Dispatch.divN ops64B config.toDivConfig divBase64 (Schoolbook.shlArr a c) (Schoolbook.shlFitArr b nb c) nb
      (a.size + 1 - nb)
    (fitTo r.1 (a.size + 1), Schoolbook.shrArr (fitTo r.2 nb) c)
  else divModBase a b

/--
The normalized operands of `divMod` and `div`: `b 2ᶜ` has `nb` limbs, and `a 2ᶜ` is below
`b 2ᶜ βᵏ` for `k = a.size + 1 - nb`.
-/
private theorem normed (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size)
    (hna : _root_.Nat.log2 b.toNat / 64 + 1 ≤ a.size) (h : 8 * a.size + 48 < USize.size) :
    let L := _root_.Nat.log2 b.toNat
    let nb := L / 64 + 1
    let c := 63 - L % 64
    (Schoolbook.shlFitArr b nb c).toNat = b.toNat * 2 ^ c ∧
      (Schoolbook.shlArr a c).toNat = a.toNat * 2 ^ c ∧ b.toNat * 2 ^ c < 2 ^ (64 * nb) ∧
      (Schoolbook.shlArr a c).toNat < (Schoolbook.shlFitArr b nb c).toNat * 2 ^ (64 * (a.size + 1 - nb)) ∧ c < 64 ∧
        nb ≤ b.size := by
  intro L nb c
  have hb₀ : b.toNat ≠ 0 := by lia
  have hlo : 2 ^ L ≤ b.toNat := Nat.log2_self_le hb₀
  have hhi : b.toNat < 2 ^ (L + 1) := Nat.lt_log2_self
  have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hnb : nb ≤ b.size := by
    have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    refine Nat.le_of_not_lt fun h' => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 64 * b.size ≤ L by lia)
    lia
  have hLc : L + c + 1 = 64 * nb := by lia
  have hc64 : c < 64 := by lia
  -- The normalized divisor.
  have hVlt : b.toNat * 2 ^ c < 2 ^ (64 * nb) :=
    calc b.toNat * 2 ^ c < 2 ^ (L + 1) * 2 ^ c :=
          Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
      _ = 2 ^ (64 * nb) := by rw [← Nat.pow_add, ← hLc]; congr 1; lia
  have hVv : (Schoolbook.shlFitArr b nb c).toNat = b.toNat * 2 ^ c :=
    (shlFitArr_toNat b nb c hc64 hnb (by lia) hVlt).1
  -- The normalized dividend.
  have hUv : (Schoolbook.shlArr a c).toNat = a.toNat * 2 ^ c := (shlArr_toNat a c hc64 (by lia)).1
  refine ⟨hVv, hUv, hVlt, ?_, hc64, hnb⟩
  rw [hUv, hVv, Nat.mul_right_comm]
  apply Nat.mul_lt_mul_of_pos_right _ (Nat.two_pow_pos _)
  calc a.toNat < 2 ^ (64 * a.size) := hA
    _ = 2 ^ (64 * (nb - 1)) * 2 ^ (64 * (a.size + 1 - nb)) := by
        rw [← Nat.pow_add]; congr 1; lia
    _ ≤ b.toNat * 2 ^ (64 * (a.size + 1 - nb)) := by
        apply Nat.mul_le_mul_right
        exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hlo

private theorem divMod_dc (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat ∧
      (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size := by
  have hL : MPN.W64.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by
    rw [log2_eq, toUSlice_toNat b (by lia)]
  unfold divMod
  dsimp only
  rw [hL]
  split
  · rename_i h
    obtain ⟨hVv, hUv, hVlt, hUV, hc64, hnb⟩ := normed a b hb hU h.2.1 h.2.2
    have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    generalize _root_.Nat.log2 b.toNat / 64 + 1 = nb at h hVv hUv hVlt hUV hnb ⊢
    generalize 63 - _root_.Nat.log2 b.toNat % 64 = c at hVv hUv hVlt hUV hc64 ⊢
    obtain ⟨r₃, r₄⟩ := Dispatch.divN_scaled (o := ops64B) (n := nb) (k := a.size + 1 - nb)
      config.toDivConfig
      (fun U V hV => val_divBase64 U V (by simp only [ops64B_val] at hV; lia))
      (by simp only [ops64B_val]; exact hUv) (by simp only [ops64B_val]; exact hVv)
      (Nat.two_pow_pos c) hb
      (by simp only [ops64B_val, ops64B_B]; rw [hVv, ← Nat.pow_mul]; exact hVlt)
      (by simp only [ops64B_val, ops64B_B]; rw [← Nat.pow_mul]; exact hUV)
    simp only [ops64B_val] at r₃ r₄
    generalize Dispatch.divN ops64B config.toDivConfig divBase64 (Schoolbook.shlArr a c) (Schoolbook.shlFitArr b nb c) nb
      (a.size + 1 - nb) = r at r₃ r₄
    -- The quotient fits in `a.size + 1` limbs, and the remainder in `nb`, then in `b`'s.
    have hqa : a.toNat / b.toNat < 2 ^ (64 * (a.size + 1)) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia)))
    obtain ⟨q₁, q₂⟩ := fitTo_spec r.1 (a.size + 1) (by rw [r₃]; exact hqa)
    have hrm : a.toNat % b.toNat * 2 ^ c < 2 ^ (64 * nb) :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hb) (Nat.two_pow_pos _))
        (Nat.le_of_lt hVlt)
    obtain ⟨s₁, s₂⟩ := fitTo_spec r.2 nb (by rw [r₄]; exact hrm)
    obtain ⟨u₁, u₂⟩ := shrArr_toNat (fitTo r.2 nb) c hc64 (by lia)
    rw [s₁, r₄, Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at u₁
    exact ⟨by rw [q₁, r₃], u₁, q₂, by rw [u₂]; lia⟩
  · obtain ⟨d₁, d₂⟩ := toNat_divModBase a b hb hU
    obtain ⟨e₁, e₂⟩ := size_divModBase a b hb hU
    exact ⟨d₁, d₂, e₁, e₂⟩

public theorem toNat_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat :=
  ⟨(divMod_dc a b hb hU).1, (divMod_dc a b hb hU).2.1⟩

public theorem size_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size :=
  (divMod_dc a b hb hU).2.2

/--
`a / b`, for `0 < b`: as `divMod`, from `config.divQMu` limbs of `b` by Barrett's division of the
normalized `a` and `b` without the last remainder when the estimate decides (`NatOps.divQMuW`).
-/
public def div (a b : UInt64Array) : UInt64Array :=
  let L := MPN.W64.log2 b.toUSlice
  let nb := L / 64 + 1
  if config.divDC ≤ nb ∧ nb ≤ a.size ∧ 8 * a.size + 48 < USize.size then
    let c := 63 - L % 64
    fitTo (Dispatch.divQN ops64B config.toDivConfig divBase64 (Schoolbook.shlArr a c) (Schoolbook.shlFitArr b nb c) nb
      (a.size + 1 - nb)) (a.size + 1)
  else (divMod a b).1

public theorem toNat_div (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) : (div a b).toNat = a.toNat / b.toNat := by
  have hL : MPN.W64.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by
    rw [log2_eq, toUSlice_toNat b (by lia)]
  unfold div
  dsimp only
  rw [hL]
  split
  · rename_i h
    obtain ⟨hVv, hUv, hVlt, hUV, -, -⟩ := normed a b hb hU h.2.1 h.2.2
    have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    generalize _root_.Nat.log2 b.toNat / 64 + 1 = nb at h hVv hUv hVlt hUV ⊢
    generalize 63 - _root_.Nat.log2 b.toNat % 64 = c at hVv hUv hVlt hUV ⊢
    have hq := Dispatch.divQN_scaled (o := ops64B) (n := nb) (k := a.size + 1 - nb)
      config.toDivConfig
      (fun U V hV => val_divBase64 U V (by simp only [ops64B_val] at hV; lia))
      (by simp only [ops64B_val]; exact hUv) (by simp only [ops64B_val]; exact hVv)
      (Nat.two_pow_pos c) hb
      (by simp only [ops64B_val, ops64B_B]; rw [hVv, ← Nat.pow_mul]; exact hVlt)
      (by simp only [ops64B_val, ops64B_B]; rw [← Nat.pow_mul]; exact hUV)
    simp only [ops64B_val] at hq
    have hqa : a.toNat / b.toNat < 2 ^ (64 * (a.size + 1)) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia)))
    rw [(fitTo_spec _ (a.size + 1) (by rw [hq]; exact hqa)).1, hq]
  · exact (toNat_divMod a b hb hU).1

end MPN.W64.Num
