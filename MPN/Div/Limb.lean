/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.ByLimb
public import MPN.ValAt
public import MPN.Mul

/-!
# Division by a limb

`divRem1 a d` divides `a` by the limb `d`, like GMP's `mpn_divrem_1`, by `main`'s
`WordArray.divRem1W`: from the top limb down, each step by `UInt32.div2Rem`, one hardware division
of 64 bits by 32, or for a normalized `d` from `config.div1Recip` limbs by Möller and Granlund's
step with a precomputed reciprocal, checked. On Zen 3 the divider always wins, so by default it
never takes the reciprocal, but on a machine with a slower divider `lake exe tune` finds where it
pays.
-/

open ScalarArray

namespace MPN

private theorem div1_bound (a : UInt32Array.Slice) (h : a.start + a.size < USize.size) :
    WordArray.LoopBound (UInt32Array.replicate a.size 0) 0 a.size.toUSize ∧
      WordArray.LoopBound a.array a.start.toUSize a.size.toUSize := by
  have := a.stop_le_array_size
  have := a.size_eq
  have := a.start_le_stop
  have e₁ := toNat_toUSize (show a.size < USize.size by lia)
  have e₂ := toNat_toUSize (show a.start < USize.size by lia)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show (0 : USize).toNat + _ ≤ (UInt32Array.replicate _ 0).size; simp [e₁]
  · simp [e₁]; lia
  · show _ ≤ a.array.size; rw [e₁, e₂]; lia
  · rw [e₁, e₂]; lia

/--
`a / d` and `a % d`, like GMP's `mpn_divrem_1`, as `a.size` limbs and a limb: by
`WordArray.divRem1W`, with the steps with the reciprocal from `t` limbs; on `Nat` were the sizes
not `USize`s, which never happens. It is exact when `d ≠ 0`.
-/
public def divRem1With (t : USize) (a : UInt32Array.Slice) (d : UInt32) : UInt32Array × UInt32 :=
  if h : a.start + a.size < 4294967295 then
    let b := div1_bound a (lt_usizeSize h)
    WordArray.divRem1W UInt32Array t (UInt32Array.replicate a.size 0) 0 a.array
      a.start.toUSize a.size.toUSize b.1 b.2 d
  else (ofNat (toNat a / d.toNat), (toNat a % d.toNat).toUInt32)

/-- `divRem1With` divides: `a = q d + r` with `r < d`. -/
public theorem divRem1With_spec (t : USize) (a : UInt32Array.Slice) (d : UInt32) (hd : d ≠ 0) :
    toNat (divRem1With t a d).1 * d.toNat + (divRem1With t a d).2.toNat = toNat a ∧
      (divRem1With t a d).2.toNat < d.toNat := by
  have hd' : 0 < d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hd
    · exact h
  by_cases h : a.start + a.size < 4294967295
  · have hU := lt_usizeSize h
    have e : divRem1With t a d = WordArray.divRem1W UInt32Array t
        (UInt32Array.replicate a.size 0) 0 a.array a.start.toUSize a.size.toUSize
        (div1_bound a hU).1 (div1_bound a hU).2 d := by
      simp only [divRem1With, h, ↓reduceDIte]
    rw [e]
    have e₁ := toNat_toUSize (show a.size < USize.size by lia)
    have e₂ := toNat_toUSize (show a.start < USize.size by lia)
    obtain ⟨i₁, -, i₃, i₄⟩ := WordArray.divRem1W_spec (A := UInt32Array) t
      (UInt32Array.replicate a.size 0) 0 a.array a.start.toUSize a.size.toUSize
      (div1_bound a hU).1 (div1_bound a hU).2 d hd'
    refine ⟨?_, i₄⟩
    rw [toNat_eq_valAt a, toNat_array_eq_valAt, Nat.mul_comm]
    rw [e₁, e₂, USize.toNat_zero] at i₃
    have hs : (WordArray.divRem1W UInt32Array t (UInt32Array.replicate a.size 0) 0 a.array
        a.start.toUSize a.size.toUSize (div1_bound a hU).1 (div1_bound a hU).2 d).1.size =
        a.size := by
      show LimbArray.size (A := UInt32Array) _ = _; rw [i₁]; exact UInt32Array.size_replicate ..
    rw [hs]
    exact i₃
  · have e : divRem1With t a d = (ofNat (toNat a / d.toNat), (toNat a % d.toNat).toUInt32) := by
      simp only [divRem1With, h, ↓reduceDIte]
    rw [e]
    have hm := Nat.mod_lt (toNat a) hd'
    have := d.toNat_lt
    rw [toNat_toSlice, ← toNat_toSlice, toNat_ofNat, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
    exact ⟨Nat.div_add_mod' .., hm⟩

/-- `config.div1Recip` as a `USize`, at most `4294967295`, which no guarded size reaches. -/
public def div1RecipU : USize := (min config.div1Recip 4294967295).toUSize

/-- `divRem1With` with the steps with the reciprocal from `config.div1Recip` limbs. -/
public def divRem1 (a : UInt32Array.Slice) (d : UInt32) : UInt32Array × UInt32 :=
  divRem1With div1RecipU a d

/-- `divRem1` divides: `a = q d + r` with `r < d`. -/
public theorem divRem1_spec (a : UInt32Array.Slice) (d : UInt32) (hd : d ≠ 0) :
    toNat (divRem1 a d).1 * d.toNat + (divRem1 a d).2.toNat = toNat a ∧
      (divRem1 a d).2.toNat < d.toNat :=
  divRem1With_spec div1RecipU a d hd

end MPN
