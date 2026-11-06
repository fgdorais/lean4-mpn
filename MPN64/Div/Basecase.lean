/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Div.Limb
public import MPN.Div.Basecase

/-!
# Schoolbook division

`divRem` divides by a divisor `v` of `n ≥ 2` limbs by Knuth's Algorithm D, like GMP's schoolbook
division, through `main`'s `MPN.Div.Basecase` on `UInt64Array` (`Schoolbook.divRemN`): the
dividend and the divisor normalized by a shift, then from the top down, in one array, one quotient
limb per step, or two by one pass of two rows from `config.div2Rows` limbs in the divisor, the
multiply-subtract passes by the in-place folds. From `config.div32Recip` limbs in the divisor, the
estimates are GMP's 3-by-2 step with the precomputed reciprocal `recip32`, checked exactly. The
remainder is shifted back into an array of its own, and the quotient stays in the array of the
division.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## The estimate with a precomputed reciprocal

GMP's schoolbook division estimates each quotient limb without the hardware divider, by Möller
and Granlund's 3-by-2 step (`udiv_qr_3by2`) with the reciprocal `⌊(β³ - 1) / (v₁ β + v₂)⌋ - β`
of the top two limbs of the normalized divisor (`invert_pi1`). `main`'s `qEstR` checks the
quotient and remainder of the step exactly, `q (v₁ β + v₂) + r = w₂ β² + w₁ β + w₀` with
`r < v₁ β + v₂`, by four products off the dependency chain; then `q` is the quotient of the top
three limbs by the top two, which is never too small. Otherwise it takes `qEst`. So neither the
reciprocal nor the error bound of the step needs a proof.
-/

/-- The reciprocal `⌊(β³ - 1) / (d₁ β + d₀)⌋ - β` of a normalized `d₁ β + d₀`, like GMP's
`invert_pi1`, by `main`'s `WordArray.recip32`. -/
@[inline] public def recip32 (d₁ d₀ : UInt64) : UInt64 := WordArray.recip32 UInt64Array d₁ d₀

/-- `config.div32Recip` as a `USize`, at most `2³² - 1`. -/
public def div32RecipU : USize := (min config.div32Recip 4294967295).toUSize

/-- `config.div2Rows` as a `USize`, at most `2³² - 1`. -/
public def div2RowsU : USize := (min config.div2Rows 4294967295).toUSize

/-! ## Division -/

/--
`(a / b, a % b)`, the quotient in `a.size - b.size + 1` limbs and the remainder in `b.size` limbs,
like GMP's `mpn_tdiv_qr`. It requires `0 < b.size ≤ a.size` and a nonzero top limb of `b`. A
divisor of one limb uses `divRem1`; a longer one `main`'s `Schoolbook.divRemN`, which normalizes
it, like GMP: `a` and `b` are shifted left by the `k` bits that set the top bit of `b`, which keeps
the corrections of the estimates rare, and the remainder is shifted back at the end.
-/
public def divRemWith (t : USize) (a b : USlice) : UInt64Array × UInt64Array :=
  if b.size ≤ 1 then
    let p := divRem1 (UInt64Array.replicate a.size.toNat 0).toUSlice a b.array[b.start.toNat]!
    (p.1, UInt64Array.replicate 1 p.2)
  else if h : 2 ≤ b.size.toNat ∧ b.size ≤ a.size ∧ a.size.toNat + 1 < USize.size then
    Schoolbook.divRemN t div2RowsU a.array a.start a.size b.array b.start b.size
      (a.loopBound (USize.le_refl _)) (b.loopBound (USize.le_refl _)) h.1
      (USize.le_iff_toNat_le.1 h.2.1) h.2.2
  else (UInt64Array.replicate 0 0, UInt64Array.replicate 0 0)

/-- `divRemWith` divides, with the sizes of its results. -/
public theorem divRemWith_spec (t : USize) (a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRemWith t a b).1.size = a.size.toNat - b.size.toNat + 1 ∧
      (divRemWith t a b).1.toNat = a.toNat / b.toNat ∧
      (divRemWith t a b).2.size = b.size.toNat ∧
      (divRemWith t a b).2.toNat = a.toNat % b.toNat := by
  have hab' := USize.le_iff_toNat_le.1 hab
  rw [divRemWith]
  split
  · rename_i h₁
    have hb1 : b.size.toNat = 1 := by have := USize.le_iff_toNat_le.1 h₁; simp at this; lia
    rw [hb1, Nat.add_sub_cancel] at ht
    have hd : 0 < (b.array[b.start.toNat]!).toNat :=
      Nat.pos_of_ne_zero fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl))
    have hbv : b.toNat = (b.array[b.start.toNat]!).toNat := by
      rw [USlice.toNat_eq_valAt, hb1, valAt_one]
    have hsz := size_toUSlice (UInt64Array.replicate a.size.toNat 0) (by simp; lia)
    simp only [UInt64Array.size_replicate] at hsz
    have haq : a.size ≤ (UInt64Array.replicate a.size.toNat 0).toUSlice.size :=
      USize.le_iff_toNat_le.2 (by rw [hsz]; exact Nat.le_refl _)
    have e₁ := valAt_divRem1 _ _ _ hd haq
    have e₂ := toNat_divRem1_snd _ _ _ hd haq
    simp only [start_toUSlice, USize.toNat_zero] at e₁
    refine ⟨by simp; lia, ?_, by simp [hb1], ?_⟩
    · rw [toNat_eq_valAt, size_divRem1, array_toUSlice, UInt64Array.size_replicate, e₁, hbv]
    · rw [toNat_eq_valAt, UInt64Array.size_replicate, valAt_one, hbv, ← e₂]
      simp
  · rename_i h₁
    have hn₂ : 2 ≤ b.size.toNat := by
      have := fun h => h₁ (USize.le_iff_toNat_le.2 h); rw [USize.toNat_one] at this; lia
    rw [dite_eq_left ⟨hn₂, hab, hU⟩]
    obtain ⟨d₁, d₂, d₃, d₄⟩ := Schoolbook.divRemN_spec t div2RowsU a.array a.start a.size b.array
      b.start b.size (a.loopBound (USize.le_refl _)) (b.loopBound (USize.le_refl _)) hn₂ hab' hU
      (fun e => ht (UInt64.toNat_inj.1 (by exact e)))
    refine ⟨(show LimbArray.size _ = _ from d₁).trans (by lia), ?_, d₃, ?_⟩
    · rw [toNat_eq_valAt, USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
      exact (congrArg (fun k => LimbArray.valAt _ 0 k) d₁).trans d₂
    · rw [toNat_eq_valAt, USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
      exact (congrArg (fun k => LimbArray.valAt _ 0 k) d₃).trans d₄

/-- `divRemWith` with the 3-by-2 steps with the reciprocal from `config.div32Recip` limbs. -/
public def divRem (a b : USlice) : UInt64Array × UInt64Array :=
  divRemWith div32RecipU a b

/-- `divRem` divides, with the sizes of its results. -/
public theorem divRem_spec (a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem a b).1.size = a.size.toNat - b.size.toNat + 1 ∧
      (divRem a b).1.toNat = a.toNat / b.toNat ∧
      (divRem a b).2.size = b.size.toNat ∧
      (divRem a b).2.toNat = a.toNat % b.toNat :=
  divRemWith_spec _ a b h₀ hab ht hU

end MPN.W64
