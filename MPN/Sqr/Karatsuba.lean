/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Karatsuba
public import MPN.Sqr.Basecase

/-!
# Karatsuba squaring

`sqrKaratsuba r a` writes the `2 a.size` limbs of `a * a` into the slice `r`, like
`mulKaratsuba r a a` but with three squares: it splits `a` at `k = ⌈a.size / 2⌉` into
`a = a₀ + 2^(64 k) a₁` and computes `a₀²` and `a₁²` into `r`, and `(a₀ + a₁)²` into a new array,
and adds `2 a₀ a₁`, which is that minus them, to `r` from limb `k` on in one pass
(`karatsubaMid`). Below `cfg.sqrKaratsuba` limbs it is `sqrBasecase`. It requires
`0 < a.size` and `2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

variable (cfg : Config)

/-- The split point of `sqrKaratsuba`, `⌈m / 2⌉`. -/
private theorem toNat_split {cfg : Config} {m : USize} (hm : cfg.sqrKaratsuba ≤ m.toNat) :
    (m - m / 2).toNat = m.toNat - m.toNat / 2 ∧ 4 ≤ m.toNat := by
  have := cfg.four_le_sqrKaratsuba
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have hd : (m / 2).toNat = m.toNat / 2 := by
    rw [USize.toNat_div, USize.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hd]; lia)), hd]
  exact ⟨rfl, by lia⟩

/--
Writes the `2 a.size` limbs of `a * a` into `r`, by Karatsuba's method above
`cfg.sqrKaratsuba` and by `sqrBasecase` below. It requires `0 < a.size` and
`2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def sqrKaratsuba (cfg : Config) (r a : USlice) : UInt64Array :=
  if h : cfg.sqrKaratsuba ≤ a.size.toNat ∧ a.size ≤ r.size ∧ a.size ≤ r.size - a.size then
    let k := a.size - a.size / 2
    let n := a.size + a.size
    let a₀ := a.slice 0 k
    let a₁ := a.slice k a.size
    let sa := sumLimbs a₀ a₁
    let r₁ := sqrKaratsuba cfg (r.slice 0 (k + k)) a₀
    let r₂ := sqrKaratsuba cfg ((r₁.uslice r.start r.stop).slice (k + k) n) a₁
    let t₁ := sqrKaratsuba cfg (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice sa.toUSlice
    karatsubaMid r₂ r.start k n t₁
  else
    sqrBasecase r a
termination_by a.size.toNat
decreasing_by
  all_goals
    obtain ⟨hk, hm⟩ := toNat_split h.1
    have := a.size.toNat_lt_size
  · rw [USlice.size_slice _ (by rw [hk, USize.toNat_zero]; lia) (by rw [hk]; lia), hk,
      USize.toNat_zero]
    lia
  · rw [USlice.size_slice _ (by rw [hk]; lia) (Nat.le_refl _), hk]
    lia
  · have h₀ := USlice.size_slice a (i := 0) (j := a.size - a.size / 2)
      (by rw [hk, USize.toNat_zero]; lia) (by rw [hk]; lia)
    rw [size_toUSlice _ (by rw [size_sumLimbs, h₀, hk, USize.toNat_zero]; lia), size_sumLimbs, h₀,
      hk, USize.toNat_zero]
    lia

/-! ## Correctness -/

private theorem sqrKaratsuba_spec (N : Nat) : ∀ (r a : USlice), a.size.toNat = N →
    (sqrKaratsuba cfg r a).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) →
        (sqrKaratsuba cfg r a)[i]! = r.array[i]!) ∧
      (0 < a.size → 2 * a.size.toNat ≤ r.size.toNat →
        (sqrKaratsuba cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat) := by
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro r a hN
  rw [sqrKaratsuba]
  split
  · rename_i h
    dsimp only
    rw [Nat.two_mul]
    obtain ⟨hg, har, hbr⟩ := h
    obtain ⟨hk, hm32⟩ := toNat_split hg
    have hkb' : (a.size - a.size / 2).toNat < a.size.toNat := by rw [hk]; lia
    have har' := USize.le_iff_toNat_le.1 har
    have hbr' := USize.le_iff_toNat_le.1 hbr
    rw [USize.toNat_sub_of_le _ _ har] at hbr'
    have hrb := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
    generalize a.size - a.size / 2 = k at *
    -- Sizes as `Nat`s.
    have hkk : (k + k).toNat = k.toNat + k.toNat := USize.toNat_add_of_lt (by lia)
    have hn : (a.size + a.size).toNat = a.size.toNat + a.size.toNat :=
      USize.toNat_add_of_lt (by lia)
    have h2 : (2 : USize).toNat = 2 := by
      have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
      rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
    have hk2 : (k + k + 2).toNat = k.toNat + k.toNat + 2 := by
      rw [USize.toNat_add_of_lt (by rw [hkk, h2]; lia), hkk, h2]
    have hnk : (a.size + a.size - k).toNat = a.size.toNat + a.size.toNat - k.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hn]; lia)), hn]
    have hL : (min (a.size + a.size - k) (k + k + 2)).toNat =
        min (a.size.toNat + a.size.toNat - k.toNat) (k.toNat + k.toNat + 2) := by
      rw [USize.toNat_min, hnk, hk2]
    -- The halves.
    obtain ⟨ha₀, ha₁, hA⟩ := toNat_split_slices a (k := k) (by lia)
    -- `z₀` into the low limbs of `r`.
    have hW₀ := r.start_slice (i := 0) (j := k + k) (by rw [USize.toNat_zero]; lia)
      (by rw [hkk]; lia)
    have hW₀' := r.size_slice (i := 0) (j := k + k) (by rw [USize.toNat_zero]; lia)
      (by rw [hkk]; lia)
    rw [USize.toNat_zero, Nat.add_zero] at hW₀
    rw [USize.toNat_zero, Nat.sub_zero, hkk] at hW₀'
    obtain ⟨h1s, h1u, h1v⟩ := ih _ (by rw [← hN, ha₀]; lia) (r.slice 0 (k + k)) (a.slice 0 k) rfl
    rw [USlice.array_slice] at h1s h1u
    rw [hW₀, ha₀, Nat.two_mul] at h1u h1v
    rw [hW₀'] at h1v
    replace h1v := h1v (by rw [USize.lt_iff_toNat_lt, ha₀, USize.toNat_zero]; lia) (by lia)
    generalize sqrKaratsuba cfg (r.slice 0 (k + k)) (a.slice 0 k) = r₁ at *
    -- `z₂` into the limbs above them.
    obtain ⟨hU₁s, hU₁z, hU₁a⟩ := uslice_same r r₁ h1s
    have hW₁ := (r₁.uslice r.start r.stop).start_slice (i := k + k) (j := a.size + a.size)
      (by rw [hkk, hn]; lia) (by rw [hn, hU₁z]; lia)
    have hW₁' := (r₁.uslice r.start r.stop).size_slice (i := k + k) (j := a.size + a.size)
      (by rw [hkk, hn]; lia) (by rw [hn, hU₁z]; lia)
    rw [hU₁s, hkk] at hW₁
    rw [hkk, hn] at hW₁'
    obtain ⟨h2s, h2u, h2v⟩ := ih _ (by rw [← hN, ha₁]; lia)
      ((r₁.uslice r.start r.stop).slice (k + k) (a.size + a.size)) (a.slice k a.size) rfl
    rw [USlice.array_slice, hU₁a, h1s] at h2s
    rw [USlice.array_slice, hU₁a] at h2u
    rw [hW₁, ha₁, Nat.two_mul] at h2u h2v
    rw [hW₁'] at h2v
    replace h2v := h2v (by rw [USize.lt_iff_toNat_lt, ha₁, USize.toNat_zero]; lia) (by lia)
    generalize sqrKaratsuba cfg ((r₁.uslice r.start r.stop).slice (k + k) (a.size + a.size))
      (a.slice k a.size) = r₂ at *
    -- The sums of the halves.
    have hsa := valAt_sumLimbs (a.slice 0 k) (a.slice k a.size)
      (USize.le_iff_toNat_le.2 (by rw [ha₀, ha₁]; lia))
    have hsa' := size_sumLimbs (a.slice 0 k) (a.slice k a.size)
    rw [ha₀] at hsa hsa'
    have hsaU := size_toUSlice _ (by rw [hsa']; lia)
    rw [hsa'] at hsaU
    have hsaN := toUSlice_toNat _ (by rw [hsa']; lia)
    rw [toNat_eq_valAt, hsa', hsa] at hsaN
    generalize sumLimbs (a.slice 0 k) (a.slice k a.size) = sa at *
    -- The product of the sums, in a new array.
    have hT : (UInt64Array.replicate (k + k + 2).toNat 0).size = k.toNat + k.toNat + 2 := by
      simp [hk2]
    have hTU := size_toUSlice _ (by rw [hT]; lia)
    rw [hT] at hTU
    obtain ⟨h3s, -, h3v⟩ := ih _ (by rw [← hN, hsaU]; lia)
      (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice sa.toUSlice rfl
    rw [array_toUSlice, hT] at h3s
    rw [start_toUSlice, USize.toNat_zero, hsaU, hTU, Nat.two_mul] at h3v
    replace h3v := h3v (by rw [USize.lt_iff_toNat_lt, hsaU, USize.toNat_zero]; lia) (by lia)
    rw [hsaN, show k.toNat + 1 + (k.toNat + 1) = k.toNat + k.toNat + 2 by lia] at h3v
    generalize sqrKaratsuba cfg (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
      sa.toUSlice = t₁ at *
    -- The middle term, added to `r` in one pass.
    have hOK : MidOK r₂ r.start k (a.size + a.size) t₁ :=
      ⟨⟨by rw [hn, h2s]; have := hrb.1; lia, by rw [hn]; have := hrb.2; lia⟩, by rw [hn]; lia,
        by rw [hn]; lia, by rw [h3s], by lia⟩
    obtain ⟨m₁, m₂, m₃⟩ := karatsubaMid_spec r₂ r.start k (a.size + a.size) t₁ hOK
    rw [hn] at m₂ m₃
    refine ⟨by rw [m₁, h2s], fun i hi => ?_, fun _ _ => ?_⟩
    · rw [m₂ i (by lia), h2u i (by lia), h1u i (by lia)]
    · -- The names of the values, and the powers of `2⁶⁴` that relate them.
      have hAB : a.toNat * a.toNat < 2 ^ (64 * (a.size.toNat + a.size.toNat)) := by
        rw [USlice.toNat_eq_valAt a, Nat.mul_add, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)
      have hz₀ : r₂.valAt r.start.toNat (k.toNat + k.toNat) = (a.slice 0 k).toNat *
          (a.slice 0 k).toNat := by
        rw [← h1v]; exact valAt_congr _ fun i _ hi => h2u i (by lia)
      rw [show a.size.toNat + a.size.toNat - (k.toNat + k.toNat) =
        a.size.toNat - k.toNat + (a.size.toNat - k.toNat) by lia] at m₃
      rw [h2v, hz₀] at m₃
      generalize hK : k.toNat = K at *
      generalize (a.slice 0 k).toNat = A₀ at *
      generalize (a.slice k a.size).toNat = A₁ at *
      rw [hA] at hAB ⊢
      -- The identity of Karatsuba's method.
      have hring : (A₀ + A₁) * (A₀ + A₁) = A₀ * A₀ + (A₀ * A₁ + A₁ * A₀) + A₁ * A₁ := by grind
      have hprod : (A₀ + 2 ^ (64 * K) * A₁) * (A₀ + 2 ^ (64 * K) * A₁) =
          A₀ * A₀ + 2 ^ (64 * K) * (A₀ * A₁ + A₁ * A₀) +
            2 ^ (64 * (K + K)) * (A₁ * A₁) := by
        rw [show 64 * (K + K) = 64 * K + 64 * K by lia, Nat.pow_add]; grind
      rw [hring] at h3v
      rw [hprod] at hAB ⊢
      exact m₃ _ h3v hAB
  · exact ⟨size_sqrBasecase .., fun i hi => getElem!_sqrBasecase r a i hi,
      fun hb hr => valAt_sqrBasecase r a hb hr⟩

@[simp] public theorem size_sqrKaratsuba (r a : USlice) :
    (sqrKaratsuba cfg r a).size = r.array.size :=
  (sqrKaratsuba_spec cfg _ r a rfl).1

/-- `sqrKaratsuba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqrKaratsuba (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqrKaratsuba cfg r a)[i]! = r.array[i]! :=
  (sqrKaratsuba_spec cfg _ r a rfl).2.1 i hi

public theorem valAt_sqrKaratsuba (r a : USlice) (ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqrKaratsuba cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat :=
  (sqrKaratsuba_spec cfg _ r a rfl).2.2 ha hr

end MPN
