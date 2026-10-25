/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.AddSub
public import MPN.Mul.Basecase
public import MPN.Mul.KaratsubaMid
public import MPN.Config

/-!
# Karatsuba multiplication

`mulKaratsuba r a b` writes the `a.size + b.size` limbs of `a * b` into the slice `r`, like
`mulBasecase`. For `b.size ≤ a.size`, it splits both operands at `k = ⌈a.size / 2⌉` into
`a = a₀ + 2^(64 k) a₁` and `b = b₀ + 2^(64 k) b₁`, and computes

* `z₀ = a₀ b₀` into the low `2 k` limbs of `r`,
* `z₂ = a₁ b₁` into the limbs of `r` above them,
* `(a₀ + a₁) (b₀ + b₁)` into a new array, and adds `z₁ = a₀ b₁ + a₁ b₀`, which is that minus
  `z₀` and `z₂`, to `r` from limb `k` on in one pass (`karatsubaMid`),

all three products recursively. Below `cfg.mulKaratsuba` limbs, or when `b.size ≤ k`, it is
`mulBasecase`. It requires `0 < b.size` and `a.size + b.size ≤ r.size`, and leaves `r` unchanged
otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

/-- The thresholds of the library, from the `mpn.*` options it is compiled with. -/
public def config : Config := mpn_config%

variable (cfg : Config)

/-! ## Sums of halves -/

/-- `a + b` in a new array of `a.size + 1` limbs, for `b.size ≤ a.size`. -/
public def sumLimbs (a b : USlice) : UInt64Array :=
  let r := UInt64Array.replicate (a.size.toNat + 1) 0
  let p := add (r.uslice 0 a.size) a b
  p.1.set! a.size.toNat p.2

public theorem size_sumLimbs (a b : USlice) : (sumLimbs a b).size = a.size.toNat + 1 := by
  simp [sumLimbs, uslice]

/-- The window `[r.start, r.stop)` of an array of the same size as `r`'s, such as a result. -/
public theorem uslice_same (r : USlice) (arr : UInt64Array) (h : arr.size = r.array.size) :
    (arr.uslice r.start r.stop).start = r.start ∧ (arr.uslice r.start r.stop).size = r.size ∧
      (arr.uslice r.start r.stop).array = arr := by
  have h₁ := uslice_start arr r.start r.stop r.start_le_stop (h ▸ r.stop_le_size)
  have h₂ := uslice_stop arr r.start r.stop (h ▸ r.stop_le_size)
  exact ⟨h₁, by rw [USlice.size, USlice.size, h₁, h₂], rfl⟩

public theorem valAt_sumLimbs (a b : USlice) (hb : b.size ≤ a.size) :
    (sumLimbs a b).valAt 0 (a.size.toNat + 1) = a.toNat + b.toNat := by
  have hm := a.size.toNat_lt_size
  let R := UInt64Array.replicate (a.size.toNat + 1) 0
  have hR : a.size.toNat ≤ R.size := by simp [R]
  have hs := uslice_start R 0 a.size (USize.le_iff_toNat_le.2 (by simp)) hR
  have ht := uslice_stop R 0 a.size hR
  have hW : (R.uslice 0 a.size).size = a.size := by
    rw [USlice.size, hs, ht, USize.sub_zero]
  have hv := valAt_add (R.uslice 0 a.size) a b 0 hb (by rw [hW]; exact USize.le_refl _)
  rw [hs, USize.toNat_zero, UInt64.toNat_zero, Nat.add_zero] at hv
  have hsz : (add (R.uslice 0 a.size) a b 0).1.size = a.size.toNat + 1 := by
    rw [size_add]; simp [R, uslice]
  show ((add (R.uslice 0 a.size) a b 0).1.set! a.size.toNat
    (add (R.uslice 0 a.size) a b 0).2).valAt 0 (a.size.toNat + 1) = _
  rw [UInt64Array.valAt_add, valAt_one, Nat.zero_add, getElem!_set!_self _ _ _ (by lia), ← hv]
  congr 1
  exact valAt_congr _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)

/-! ## The product -/

/-- The split point of `mulKaratsuba`, `⌈m / 2⌉`. -/
private theorem toNat_split {cfg : Config} {m : USize} (hm : cfg.mulKaratsuba ≤ m.toNat) :
    (m - m / 2).toNat = m.toNat - m.toNat / 2 ∧ 4 ≤ m.toNat := by
  have := cfg.four_le_mulKaratsuba
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have hd : (m / 2).toNat = m.toNat / 2 := by
    rw [USize.toNat_div, USize.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hd]; lia)), hd]
  exact ⟨rfl, by lia⟩

/--
Writes the `a.size + b.size` limbs of `a * b` into `r`, by Karatsuba's method above
`cfg.mulKaratsuba` and by `mulBasecase` below. It requires `0 < b.size` and
`a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def mulKaratsuba (cfg : Config) (r a b : USlice) : UInt64Array :=
  if h : cfg.mulKaratsuba ≤ a.size.toNat ∧ b.size ≤ a.size ∧ a.size - a.size / 2 < b.size ∧
      a.size ≤ r.size ∧ b.size ≤ r.size - a.size then
    let k := a.size - a.size / 2
    let n := a.size + b.size
    let a₀ := a.slice 0 k
    let a₁ := a.slice k a.size
    let b₀ := b.slice 0 k
    let b₁ := b.slice k b.size
    let sa := sumLimbs a₀ a₁
    let sb := sumLimbs b₀ b₁
    let r₁ := mulKaratsuba cfg (r.slice 0 (k + k)) a₀ b₀
    let r₂ := mulKaratsuba cfg ((r₁.uslice r.start r.stop).slice (k + k) n) a₁ b₁
    let t₁ := mulKaratsuba cfg (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice sa.toUSlice
      sb.toUSlice
    karatsubaMid r₂ r.start k n t₁
  else
    mulBasecase r a b
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

/-- `a` split into its low `k` limbs and the limbs above them. -/
public theorem toNat_split_slices (a : USlice) {k : USize} (hk : k.toNat ≤ a.size.toNat) :
    (a.slice 0 k).size.toNat = k.toNat ∧ (a.slice k a.size).size.toNat = a.size.toNat - k.toNat ∧
      a.toNat = (a.slice 0 k).toNat + 2 ^ (64 * k.toNat) * (a.slice k a.size).toNat := by
  have h0 : (0 : USize).toNat = 0 := USize.toNat_zero
  refine ⟨by rw [a.size_slice (by lia) hk, h0]; lia, a.size_slice hk (Nat.le_refl _), ?_⟩
  rw [a.toNat_slice (by lia) hk, a.toNat_slice hk (Nat.le_refl _), USlice.toNat_eq_valAt, h0,
    Nat.add_zero, Nat.sub_zero]
  conv => lhs; rw [show a.size.toNat = k.toNat + (a.size.toNat - k.toNat) by lia]
  rw [UInt64Array.valAt_add]

private theorem mulKaratsuba_spec (N : Nat) : ∀ (r a b : USlice), a.size.toNat = N →
    (mulKaratsuba cfg r a b).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (mulKaratsuba cfg r a b)[i]! = r.array[i]!) ∧
      (0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (mulKaratsuba cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro r a b hN
  rw [mulKaratsuba]
  split
  · rename_i h
    dsimp only
    obtain ⟨hg, hba, hkb, har, hbr⟩ := h
    obtain ⟨hk, hm32⟩ := toNat_split hg
    have hba' := USize.le_iff_toNat_le.1 hba
    have hkb' := USize.lt_iff_toNat_lt.1 hkb
    have har' := USize.le_iff_toNat_le.1 har
    have hbr' := USize.le_iff_toNat_le.1 hbr
    rw [USize.toNat_sub_of_le _ _ har] at hbr'
    have hrb := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
    generalize a.size - a.size / 2 = k at *
    -- Sizes as `Nat`s.
    have hkk : (k + k).toNat = k.toNat + k.toNat := USize.toNat_add_of_lt (by lia)
    have hn : (a.size + b.size).toNat = a.size.toNat + b.size.toNat :=
      USize.toNat_add_of_lt (by lia)
    have h2 : (2 : USize).toNat = 2 := by
      have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
      rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
    have hk2 : (k + k + 2).toNat = k.toNat + k.toNat + 2 := by
      rw [USize.toNat_add_of_lt (by rw [hkk, h2]; lia), hkk, h2]
    have hnk : (a.size + b.size - k).toNat = a.size.toNat + b.size.toNat - k.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hn]; lia)), hn]
    have hL : (min (a.size + b.size - k) (k + k + 2)).toNat =
        min (a.size.toNat + b.size.toNat - k.toNat) (k.toNat + k.toNat + 2) := by
      rw [USize.toNat_min, hnk, hk2]
    -- The halves.
    obtain ⟨ha₀, ha₁, hA⟩ := toNat_split_slices a (k := k) (by lia)
    obtain ⟨hb₀, hb₁, hB⟩ := toNat_split_slices b (k := k) (by lia)
    -- `z₀` into the low limbs of `r`.
    have hW₀ := r.start_slice (i := 0) (j := k + k) (by rw [USize.toNat_zero]; lia)
      (by rw [hkk]; lia)
    have hW₀' := r.size_slice (i := 0) (j := k + k) (by rw [USize.toNat_zero]; lia)
      (by rw [hkk]; lia)
    rw [USize.toNat_zero, Nat.add_zero] at hW₀
    rw [USize.toNat_zero, Nat.sub_zero, hkk] at hW₀'
    obtain ⟨h1s, h1u, h1v⟩ := ih _ (by rw [← hN, ha₀]; lia) (r.slice 0 (k + k)) (a.slice 0 k)
      (b.slice 0 k) rfl
    rw [USlice.array_slice] at h1s h1u
    rw [hW₀, ha₀, hb₀] at h1u h1v
    rw [hW₀'] at h1v
    replace h1v := h1v (by rw [USize.lt_iff_toNat_lt, hb₀, USize.toNat_zero]; lia) (Nat.le_refl _)
    generalize mulKaratsuba cfg (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) = r₁ at *
    -- `z₂` into the limbs above them.
    obtain ⟨hU₁s, hU₁z, hU₁a⟩ := uslice_same r r₁ h1s
    have hW₁ := (r₁.uslice r.start r.stop).start_slice (i := k + k) (j := a.size + b.size)
      (by rw [hkk, hn]; lia) (by rw [hn, hU₁z]; lia)
    have hW₁' := (r₁.uslice r.start r.stop).size_slice (i := k + k) (j := a.size + b.size)
      (by rw [hkk, hn]; lia) (by rw [hn, hU₁z]; lia)
    rw [hU₁s, hkk] at hW₁
    rw [hkk, hn] at hW₁'
    obtain ⟨h2s, h2u, h2v⟩ := ih _ (by rw [← hN, ha₁]; lia)
      ((r₁.uslice r.start r.stop).slice (k + k) (a.size + b.size)) (a.slice k a.size)
      (b.slice k b.size) rfl
    rw [USlice.array_slice, hU₁a, h1s] at h2s
    rw [USlice.array_slice, hU₁a] at h2u
    rw [hW₁, ha₁, hb₁] at h2u h2v
    rw [hW₁'] at h2v
    replace h2v := h2v (by rw [USize.lt_iff_toNat_lt, hb₁, USize.toNat_zero]; lia) (by lia)
    generalize mulKaratsuba cfg ((r₁.uslice r.start r.stop).slice (k + k) (a.size + b.size))
      (a.slice k a.size) (b.slice k b.size) = r₂ at *
    -- The sums of the halves.
    have hsa := valAt_sumLimbs (a.slice 0 k) (a.slice k a.size)
      (USize.le_iff_toNat_le.2 (by rw [ha₀, ha₁]; lia))
    have hsb := valAt_sumLimbs (b.slice 0 k) (b.slice k b.size)
      (USize.le_iff_toNat_le.2 (by rw [hb₀, hb₁]; lia))
    have hsa' := size_sumLimbs (a.slice 0 k) (a.slice k a.size)
    have hsb' := size_sumLimbs (b.slice 0 k) (b.slice k b.size)
    rw [ha₀] at hsa hsa'
    rw [hb₀] at hsb hsb'
    have hsaU := size_toUSlice _ (by rw [hsa']; lia)
    have hsbU := size_toUSlice _ (by rw [hsb']; lia)
    rw [hsa'] at hsaU
    rw [hsb'] at hsbU
    have hsaN := toUSlice_toNat _ (by rw [hsa']; lia)
    have hsbN := toUSlice_toNat _ (by rw [hsb']; lia)
    rw [toNat_eq_valAt, hsa', hsa] at hsaN
    rw [toNat_eq_valAt, hsb', hsb] at hsbN
    generalize sumLimbs (a.slice 0 k) (a.slice k a.size) = sa at *
    generalize sumLimbs (b.slice 0 k) (b.slice k b.size) = sb at *
    -- The product of the sums, in a new array.
    have hT : (UInt64Array.replicate (k + k + 2).toNat 0).size = k.toNat + k.toNat + 2 := by
      simp [hk2]
    have hTU := size_toUSlice _ (by rw [hT]; lia)
    rw [hT] at hTU
    obtain ⟨h3s, -, h3v⟩ := ih _ (by rw [← hN, hsaU]; lia)
      (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice sa.toUSlice sb.toUSlice rfl
    rw [array_toUSlice, hT] at h3s
    rw [start_toUSlice, USize.toNat_zero, hsaU, hsbU, hTU] at h3v
    replace h3v := h3v (by rw [USize.lt_iff_toNat_lt, hsbU, USize.toNat_zero]; lia) (by lia)
    rw [hsaN, hsbN, show k.toNat + 1 + (k.toNat + 1) = k.toNat + k.toNat + 2 by lia] at h3v
    generalize mulKaratsuba cfg (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice sa.toUSlice
      sb.toUSlice = t₁ at *
    -- The middle term, added to `r` in one pass.
    have hOK : MidOK r₂ r.start k (a.size + b.size) t₁ :=
      ⟨⟨by rw [hn, h2s]; have := hrb.1; lia, by rw [hn]; have := hrb.2; lia⟩, by rw [hn]; lia,
        by rw [hn]; lia, by rw [h3s], by lia⟩
    obtain ⟨m₁, m₂, m₃⟩ := karatsubaMid_spec r₂ r.start k (a.size + b.size) t₁ hOK
    rw [hn] at m₂ m₃
    refine ⟨by rw [m₁, h2s], fun i hi => ?_, fun _ _ => ?_⟩
    · rw [m₂ i (by lia), h2u i (by lia), h1u i (by lia)]
    · -- The names of the values, and the powers of `2⁶⁴` that relate them.
      have hAB : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
        rw [USlice.toNat_eq_valAt a, USlice.toNat_eq_valAt b, Nat.mul_add, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)
      have hz₀ : r₂.valAt r.start.toNat (k.toNat + k.toNat) = (a.slice 0 k).toNat *
          (b.slice 0 k).toNat := by
        rw [← h1v]; exact valAt_congr _ fun i _ hi => h2u i (by lia)
      rw [show a.size.toNat + b.size.toNat - (k.toNat + k.toNat) =
        a.size.toNat - k.toNat + (b.size.toNat - k.toNat) by lia] at m₃
      rw [h2v, hz₀] at m₃
      generalize hK : k.toNat = K at *
      generalize (a.slice 0 k).toNat = A₀ at *
      generalize (a.slice k a.size).toNat = A₁ at *
      generalize (b.slice 0 k).toNat = B₀ at *
      generalize (b.slice k b.size).toNat = B₁ at *
      rw [hA, hB] at hAB ⊢
      -- The identity of Karatsuba's method.
      have hring : (A₀ + A₁) * (B₀ + B₁) = A₀ * B₀ + (A₀ * B₁ + A₁ * B₀) + A₁ * B₁ := by grind
      have hprod : (A₀ + 2 ^ (64 * K) * A₁) * (B₀ + 2 ^ (64 * K) * B₁) =
          A₀ * B₀ + 2 ^ (64 * K) * (A₀ * B₁ + A₁ * B₀) +
            2 ^ (64 * (K + K)) * (A₁ * B₁) := by
        rw [show 64 * (K + K) = 64 * K + 64 * K by lia, Nat.pow_add]; grind
      rw [hring] at h3v
      rw [hprod] at hAB ⊢
      exact m₃ _ h3v hAB
  · exact ⟨size_mulBasecase .., fun i hi => getElem!_mulBasecase r a b i hi,
      fun hb hr => valAt_mulBasecase r a b hb hr⟩

@[simp] public theorem size_mulKaratsuba (r a b : USlice) :
    (mulKaratsuba cfg r a b).size = r.array.size :=
  (mulKaratsuba_spec cfg _ r a b rfl).1

/-- `mulKaratsuba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulKaratsuba (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulKaratsuba cfg r a b)[i]! = r.array[i]! :=
  (mulKaratsuba_spec cfg _ r a b rfl).2.1 i hi

public theorem valAt_mulKaratsuba (r a b : USlice) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulKaratsuba cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
      a.toNat * b.toNat :=
  (mulKaratsuba_spec cfg _ r a b rfl).2.2 hb hr

end MPN
