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
from which it subtracts them to get `2 a₀ a₁`, which it adds to `r` from limb `k` on. Below
`sqrKaratsubaThreshold` limbs it is `sqrBasecase`. It requires `0 < a.size` and
`2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

/-- The number of limbs from which `sqrKaratsuba` splits its operand. -/
public def sqrKaratsubaThreshold : USize := 96

/-- The recursion needs at least four limbs, so that `⌈m / 2⌉ + 1 < m`. -/
private theorem four_le_sqrThreshold : 4 ≤ sqrKaratsubaThreshold.toNat := by
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  rw [sqrKaratsubaThreshold, USize.toNat_ofNat,
    Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  decide

/-- The split point of `sqrKaratsuba`, `⌈m / 2⌉`. -/
private theorem toNat_split {m : USize} (h : sqrKaratsubaThreshold ≤ m) :
    (m - m / 2).toNat = m.toNat - m.toNat / 2 ∧ 4 ≤ m.toNat := by
  have hm := USize.le_iff_toNat_le.1 h
  have := four_le_sqrThreshold
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have hd : (m / 2).toNat = m.toNat / 2 := by
    rw [USize.toNat_div, USize.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hd]; lia)), hd]
  exact ⟨rfl, by lia⟩

/--
Writes the `2 a.size` limbs of `a * a` into `r`, by Karatsuba's method above
`sqrKaratsubaThreshold` and by `sqrBasecase` below. It requires `0 < a.size` and
`2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def sqrKaratsuba (r a : USlice) : UInt64Array :=
  if h : sqrKaratsubaThreshold ≤ a.size ∧ a.size ≤ r.size ∧ a.size ≤ r.size - a.size then
    let k := a.size - a.size / 2
    let n := a.size + a.size
    let a₀ := a.slice 0 k
    let a₁ := a.slice k a.size
    let sa := sumLimbs a₀ a₁
    let r₁ := sqrKaratsuba (r.slice 0 (k + k)) a₀
    let r₂ := sqrKaratsuba ((r₁.uslice r.start r.stop).slice (k + k) n) a₁
    let t₁ := sqrKaratsuba (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice sa.toUSlice
    let w := r₂.uslice r.start r.stop
    let t₂ := (subInto t₁.toUSlice (w.slice 0 (k + k))).1
    let t₃ := (subInto t₂.toUSlice (w.slice (k + k) n)).1
    (addInto (w.slice k n) (t₃.toUSlice.slice 0 (min (n - k) (k + k + 2)))).1
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
    (sqrKaratsuba r a).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) →
        (sqrKaratsuba r a)[i]! = r.array[i]!) ∧
      (0 < a.size → 2 * a.size.toNat ≤ r.size.toNat →
        (sqrKaratsuba r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat) := by
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
    generalize sqrKaratsuba (r.slice 0 (k + k)) (a.slice 0 k) = r₁ at *
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
    generalize sqrKaratsuba ((r₁.uslice r.start r.stop).slice (k + k) (a.size + a.size))
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
    generalize sqrKaratsuba (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
      sa.toUSlice = t₁ at *
    -- Subtracting `z₀` and `z₂`, read from `r`.
    obtain ⟨hws, hwz, hwa⟩ := uslice_same r r₂ (h2s)
    have hX₀ := (r₂.uslice r.start r.stop).toNat_slice (i := 0) (j := k + k)
      (by rw [USize.toNat_zero]; lia) (by rw [hkk, hwz]; lia)
    have hX₀' := (r₂.uslice r.start r.stop).size_slice (i := 0) (j := k + k)
      (by rw [USize.toNat_zero]; lia) (by rw [hkk, hwz]; lia)
    rw [hws, hwa, USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hX₀
    rw [USize.toNat_zero, Nat.sub_zero, hkk] at hX₀'
    have hz₀ : r₂.valAt r.start.toNat (k.toNat + k.toNat) = r₁.valAt r.start.toNat
        (k.toNat + k.toNat) := valAt_congr _ fun i _ hi => h2u i (by lia)
    rw [hz₀, h1v] at hX₀
    have ht₁U := size_toUSlice t₁ (by rw [h3s]; lia)
    rw [h3s] at ht₁U
    have hs₂ := valAt_subInto t₁.toUSlice ((r₂.uslice r.start r.stop).slice 0 (k + k)) 0
      (USize.le_iff_toNat_le.2 (by rw [hX₀', ht₁U]; lia))
    rw [start_toUSlice, USize.toNat_zero, ht₁U, array_toUSlice, hX₀, UInt64.toNat_zero,
      Nat.add_zero, h3v] at hs₂
    have ht₂s := size_subInto t₁.toUSlice ((r₂.uslice r.start r.stop).slice 0 (k + k)) 0
    rw [array_toUSlice, h3s] at ht₂s
    generalize subInto t₁.toUSlice ((r₂.uslice r.start r.stop).slice 0 (k + k)) 0 = p₂ at *
    have hX₁ := (r₂.uslice r.start r.stop).toNat_slice (i := k + k) (j := a.size + a.size)
      (by rw [hkk, hn]; lia) (by rw [hn, hwz]; lia)
    have hX₁' := (r₂.uslice r.start r.stop).size_slice (i := k + k) (j := a.size + a.size)
      (by rw [hkk, hn]; lia) (by rw [hn, hwz]; lia)
    rw [hws, hwa, hkk, hn,
      show a.size.toNat + a.size.toNat - (k.toNat + k.toNat) =
        a.size.toNat - k.toNat + (a.size.toNat - k.toNat) by lia, h2v] at hX₁
    rw [hkk, hn] at hX₁'
    have ht₂U := size_toUSlice p₂.1 (by rw [ht₂s]; lia)
    rw [ht₂s] at ht₂U
    have hs₃ := valAt_subInto p₂.1.toUSlice
      ((r₂.uslice r.start r.stop).slice (k + k) (a.size + a.size)) 0
      (USize.le_iff_toNat_le.2 (by rw [hX₁', ht₂U]; lia))
    rw [start_toUSlice, USize.toNat_zero, ht₂U, array_toUSlice, hX₁, UInt64.toNat_zero,
      Nat.add_zero] at hs₃
    have ht₃s := size_subInto p₂.1.toUSlice
      ((r₂.uslice r.start r.stop).slice (k + k) (a.size + a.size)) 0
    rw [array_toUSlice, ht₂s] at ht₃s
    generalize subInto p₂.1.toUSlice
      ((r₂.uslice r.start r.stop).slice (k + k) (a.size + a.size)) 0 = p₃ at *
    -- Adding `z₁` from limb `k` on.
    have ht₃U := size_toUSlice p₃.1 (by rw [ht₃s]; lia)
    rw [ht₃s] at ht₃U
    have hY := p₃.1.toUSlice.toNat_slice (i := 0) (j := min (a.size + a.size - k) (k + k + 2))
      (by rw [USize.toNat_zero]; lia) (by rw [hL, ht₃U]; lia)
    have hY' := p₃.1.toUSlice.size_slice (i := 0) (j := min (a.size + a.size - k) (k + k + 2))
      (by rw [USize.toNat_zero]; lia) (by rw [hL, ht₃U]; lia)
    rw [start_toUSlice, array_toUSlice, USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hL] at hY
    rw [USize.toNat_zero, Nat.sub_zero, hL] at hY'
    have hX₂ := (r₂.uslice r.start r.stop).start_slice (i := k) (j := a.size + a.size)
      (by rw [hn]; lia) (by rw [hn, hwz]; lia)
    have hX₂' := (r₂.uslice r.start r.stop).size_slice (i := k) (j := a.size + a.size)
      (by rw [hn]; lia) (by rw [hn, hwz]; lia)
    rw [hws] at hX₂
    rw [hn] at hX₂'
    have hs₄ := valAt_addInto ((r₂.uslice r.start r.stop).slice k (a.size + a.size))
      (p₃.1.toUSlice.slice 0 (min (a.size + a.size - k) (k + k + 2))) 0
      (USize.le_iff_toNat_le.2 (by rw [hY', hX₂']; lia))
    rw [hX₂, hX₂', USlice.array_slice, hwa, hY, UInt64.toNat_zero, Nat.add_zero] at hs₄
    have h4s := size_addInto ((r₂.uslice r.start r.stop).slice k (a.size + a.size))
      (p₃.1.toUSlice.slice 0 (min (a.size + a.size - k) (k + k + 2))) 0
    have h4u := getElem!_addInto ((r₂.uslice r.start r.stop).slice k (a.size + a.size))
      (p₃.1.toUSlice.slice 0 (min (a.size + a.size - k) (k + k + 2))) 0
    rw [USlice.array_slice, hwa, h2s] at h4s
    rw [hX₂, hX₂', USlice.array_slice, hwa] at h4u
    generalize addInto ((r₂.uslice r.start r.stop).slice k (a.size + a.size))
      (p₃.1.toUSlice.slice 0 (min (a.size + a.size - k) (k + k + 2))) 0 = p₄ at *
    refine ⟨h4s, fun i hi => ?_, fun _ _ => ?_⟩
    · rw [h4u i (by lia), h2u i (by lia), h1u i (by lia)]
    · -- The names of the values, and the powers of `2⁶⁴` that relate them.
      have hAB : a.toNat * a.toNat < 2 ^ (64 * (a.size.toNat + a.size.toNat)) := by
        rw [USlice.toNat_eq_valAt a, Nat.mul_add, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)
      generalize hK : k.toNat = K at *
      generalize hM : a.size.toNat = M at *
      generalize hs₀ : r.start.toNat = s₀ at *
      generalize hA₀ : (a.slice 0 k).toNat = A₀ at *
      generalize hA₁ : (a.slice k a.size).toNat = A₁ at *
      rw [show M - K + (M - K) = M + M - (K + K) by lia] at h2v
      have hv₂ := valAt_lt p₂.1 0 (K + K + 2)
      have hv₃ := valAt_lt p₃.1 0 (K + K + 2)
      rw [hA] at hAB ⊢
      -- The identity of Karatsuba's method.
      have hring : (A₀ + A₁) * (A₀ + A₁) = A₀ * A₀ + A₁ * A₁ + (A₀ * A₁ + A₁ * A₀) := by grind
      have hprod : (A₀ + 2 ^ (64 * K) * A₁) * (A₀ + 2 ^ (64 * K) * A₁) =
          A₀ * A₀ + 2 ^ (64 * K) * (A₀ * A₁ + A₁ * A₀) +
            2 ^ (64 * K) * 2 ^ (64 * K) * (A₁ * A₁) := by grind
      rw [hring] at hs₂
      -- No borrow: `z₁` remains.
      have hz₁ : p₃.1.valAt 0 (K + K + 2) = A₀ * A₁ + A₁ * A₀ :=
        karatsuba_borrows hs₂ hs₃ hv₂ hv₃
      -- `z₁` fits in the limbs from `k` on, so the truncated slice is all of it.
      have hPR : 2 ^ (64 * (M + M)) = 2 ^ (64 * K) * 2 ^ (64 * (M + M - K)) := by
        rw [← Nat.pow_add]; congr 1; lia
      have hZR : A₀ * A₁ + A₁ * A₀ < 2 ^ (64 * (M + M - K)) := by
        have hpos : 0 < 2 ^ (64 * K) := Nat.two_pow_pos _
        rw [hprod, hPR] at hAB
        refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * K)) ?_
        generalize 2 ^ (64 * K) * (A₀ * A₁ + A₁ * A₀) = W at *
        lia
      have hZ : p₃.1.valAt 0 (min (M + M - K) (K + K + 2)) = A₀ * A₁ + A₁ * A₀ := by
        rw [valAt_mod _ _ (Nat.min_le_right ..), hz₁]
        apply Nat.mod_eq_of_lt
        rcases Nat.le_total (M + M - K) (K + K + 2) with hle | hle
        · rw [Nat.min_eq_left hle]; exact hZR
        · rw [Nat.min_eq_right hle, ← hz₁]; exact valAt_lt ..
      rw [hZ] at hs₄
      -- The limbs of `r` from `k` on before the addition: the high half of `z₀`, then `z₂`.
      have hz₀ : r₂.valAt s₀ (K + K) = A₀ * A₀ := by
        rw [← h1v]; exact valAt_congr _ fun i _ hi => h2u i (by lia)
      rw [UInt64Array.valAt_add] at hz₀
      have hhi : r₂.valAt (s₀ + K) (M + M - K) =
          r₂.valAt (s₀ + K) K + 2 ^ (64 * K) * (A₁ * A₁) := by
        rw [show M + M - K = K + (M + M - (K + K)) by lia, UInt64Array.valAt_add,
          show s₀ + K + K = s₀ + (K + K) by lia, h2v]
      rw [hhi] at hs₄
      have hlo : p₄.1.valAt s₀ K = r₂.valAt s₀ K :=
        valAt_congr _ fun i _ hi => h4u i (.inl hi)
      -- The result, and no carry since the product fits.
      rw [show M + M = K + (M + M - K) by lia, UInt64Array.valAt_add, hlo]
      rw [hprod] at hAB ⊢
      rw [hPR] at hAB
      exact karatsuba_combine hz₀ hs₄ hAB
  · exact ⟨size_sqrBasecase .., fun i hi => getElem!_sqrBasecase r a i hi,
      fun hb hr => valAt_sqrBasecase r a hb hr⟩

@[simp] public theorem size_sqrKaratsuba (r a : USlice) :
    (sqrKaratsuba r a).size = r.array.size :=
  (sqrKaratsuba_spec _ r a rfl).1

/-- `sqrKaratsuba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqrKaratsuba (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqrKaratsuba r a)[i]! = r.array[i]! :=
  (sqrKaratsuba_spec _ r a rfl).2.1 i hi

public theorem valAt_sqrKaratsuba (r a : USlice) (ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqrKaratsuba r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat :=
  (sqrKaratsuba_spec _ r a rfl).2.2 ha hr

end MPN
