/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Div.Limb
public import Bignum.Div.Basecase

/-!
# Division

`divMod a b` is `(a / b, a % b)`, trimmed, with `Nat`'s conventions: `a / 0 = 0` and `a % 0 = a`.
The divisor is first cut to its nonzero limbs. A divisor of one limb uses `divRem1`. A longer one
is normalized, like in GMP: both numbers are multiplied by a power of two `f` that sets the top bit
of the divisor, which keeps the corrections of the quotient estimates in `divRemBasecase` few, and
the remainder is divided by `f` again at the end. Normalization only affects speed: the quotient
of `a f` by `b f` is `a / b` and the remainder `(a % b) f` for any `f ≠ 0`.
-/

open ScalarArray

namespace Bignum

/-! ## The size without trailing zeros -/

/-- The number of limbs of `s` below `i` without the trailing zeros. -/
def topSizeLoop (s : UInt32Array.Slice) : Nat → Nat
  | 0 => 0
  | i + 1 => if s.getD i 0 = 0 then topSizeLoop s i else i + 1

/-- The number of limbs of `s` without its trailing zero limbs. -/
public def topSize (s : UInt32Array.Slice) : Nat := topSizeLoop s s.size

private theorem topSizeLoop_spec (s : UInt32Array.Slice) (i : Nat) :
    topSizeLoop s i ≤ i ∧
      (∀ k, topSizeLoop s i ≤ k → k < i → s.getD k 0 = 0) ∧
      (0 < topSizeLoop s i → s.getD (topSizeLoop s i - 1) 0 ≠ 0) := by
  induction i with
  | zero => simp [topSizeLoop]
  | succ i ih =>
    simp only [topSizeLoop]
    split
    · rename_i h
      refine ⟨by omega, fun k hk hki => ?_, ih.2.2⟩
      by_cases hk' : k = i
      · rw [hk']; exact h
      · exact ih.2.1 k hk (by omega)
    · rename_i h
      exact ⟨Nat.le_refl _, fun k hk hki => by omega, fun _ => h⟩

public theorem topSize_le (s : UInt32Array.Slice) : topSize s ≤ s.size :=
  (topSizeLoop_spec s s.size).1

/-- The top limb below `topSize s` is not zero. -/
public theorem getD_topSize_ne_zero (s : UInt32Array.Slice) (h : 0 < topSize s) :
    s.getD (topSize s - 1) 0 ≠ 0 :=
  (topSizeLoop_spec s s.size).2.2 h

/-- Cutting `s` to `topSize s` limbs keeps its value. -/
public theorem toNat_slice_topSize (s : UInt32Array.Slice) :
    toNat (s.slice 0 (topSize s)) = toNat s := by
  have hle := topSize_le s
  have hz : ∀ k, topSize s ≤ k → k < s.size → s.getD k 0 = 0 := (topSizeLoop_spec s s.size).2.1
  have h := toNat_slice_add_toNat_slice s (topSize s) hle
  have h0 : toNat (s.slice (topSize s) s.size) = 0 := by
    rw [toNat, ofLimbs_eq_zero_iff]
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    simp at hk
    have := hz (topSize s + k) (by omega) (by omega)
    rw [UInt32Array.Slice.getD_eq] at this
    simpa [show topSize s + k < s.size by omega] using this
  rw [h0, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- A number of `topSize s` limbs is below `β ^ topSize s`. -/
public theorem toNat_lt_topSize (s : UInt32Array.Slice) : toNat s < 2 ^ (32 * topSize s) := by
  have := toNat_lt (s.slice 0 (topSize s))
  rw [toNat_slice_topSize, UInt32Array.Slice.size_slice] at this
  have hle := topSize_le s
  rwa [show min (topSize s) s.size - 0 = topSize s by omega] at this

/-! ## Normalized division -/

/-- A power of two that brings the top bit of `vt` to the top of the limb. Never zero. -/
@[expose] public def normFactor (vt : UInt32) : UInt32 :=
  let f := (1 : UInt32) <<< (31 - vt.log2)
  if f = 0 then 1 else f

public theorem normFactor_ne_zero (vt : UInt32) : normFactor vt ≠ 0 := by
  simp only [normFactor]
  split
  · decide
  · assumption

/--
`u / v` and `u % v` for a divisor of at least two limbs with a nonzero top limb, untrimmed:
`u` and `v` are normalized, divided with `divRemBasecase`, and the remainder divided back.
-/
def divModLimbs (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array × UInt32Array :=
  let f := normFactor (v[v.size - 1]'(by omega))
  let vf := mulRow v f
  let v' := vf.toSlice.slice 0 (topSize vf)
  if h : 2 ≤ v'.size then
    let p := divRemBasecase (mulRow u f) v' h
    (p.1, (divRem1 p.2 f).1)
  else
    divRemBasecase u v hn

/-- The top limb of `s` cut to `topSize s` limbs is not zero. -/
private theorem top_slice_topSize_ne_zero (s : UInt32Array.Slice) (h : 0 < topSize s) :
    (s.slice 0 (topSize s))[(s.slice 0 (topSize s)).size - 1]'(by
      simp only [UInt32Array.Slice.size_slice]; have := topSize_le s; omega) ≠ 0 := by
  have hle := topSize_le s
  have := getD_topSize_ne_zero s h
  rw [UInt32Array.Slice.getD_eq] at this
  simp only [show topSize s - 1 < s.size by omega, ↓reduceDIte] at this
  simp only [UInt32Array.Slice.getElem_slice, UInt32Array.Slice.size_slice, Nat.zero_add,
    Nat.min_eq_left hle, Nat.sub_zero]
  exact this

private theorem div_mod_eq {q r N D : Nat} (hD : 0 < D) (h : q * D + r = N) (hr : r < D) :
    q = N / D ∧ r = N % D := by
  have := (Nat.div_mod_unique (a := N) (b := D) (d := q) (c := r) hD).2
    ⟨by rw [Nat.mul_comm D q]; omega, hr⟩
  exact ⟨this.1.symm, this.2.symm⟩

private theorem divModLimbs_spec (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by omega) ≠ 0) :
    toNat (divModLimbs u v hn).1 = toNat u / toNat v ∧
      toNat (divModLimbs u v hn).2 = toNat u % toNat v := by
  have hvt' : 0 < (v[v.size - 1]'(by omega)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by omega)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hVpos : 0 < toNat v := by
    have := toNat_lt_topSize v
    have htop : (v[v.size - 1]'(by omega)).toNat ≤ toNat v := by
      have h := toNat_slice_add_toNat_slice v (v.size - 1) (by omega)
      have : toNat (v.slice (v.size - 1) v.size) = (v[v.size - 1]'(by omega)).toNat := by
        rw [toNat_of_size_eq_one (by simp; omega)]
        simp
      have := Nat.mul_le_mul_right (toNat (v.slice (v.size - 1) v.size))
        (Nat.one_le_two_pow (n := 32 * (v.size - 1)))
      omega
    omega
  rw [toNat_toSlice, toNat_toSlice]
  simp only [divModLimbs]
  split
  · rename_i h
    -- Normalized: `u f = q (v f) + r'` with `r' < v f`, and `r' = r f + rem` with `rem < f`.
    have hf := normFactor_ne_zero (v[v.size - 1]'(by omega))
    have hF : 0 < (normFactor (v[v.size - 1]'(by omega))).toNat := by
      rcases Nat.eq_zero_or_pos (normFactor (v[v.size - 1]'(by omega))).toNat with h | h
      · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hf
      · exact h
    generalize normFactor (v[v.size - 1]'(by omega)) = f at *
    have hv' : toNat ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f))) = toNat v * f.toNat := by
      rw [toNat_slice_topSize, toNat_mulRow]
    have hpos : 0 < topSize (mulRow v f) := by
      simp only [UInt32Array.Slice.size_slice] at h
      omega
    obtain ⟨h₁, h₂⟩ := divRemBasecase_spec (mulRow u f) _ h (top_slice_topSize_ne_zero _ hpos)
    obtain ⟨h₃, h₄⟩ := divRem1_spec (divRemBasecase (mulRow u f)
      ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f))) h).2 f hf
    rw [hv', toNat_mulRow] at h₁
    rw [hv'] at h₂
    simp only [toNat_toSlice] at h₁ h₂ h₃ h₄ ⊢
    obtain ⟨hq, hr⟩ := div_mod_eq (Nat.mul_pos hVpos hF) h₁ h₂
    rw [Nat.mul_div_mul_right _ _ hF] at hq
    rw [Nat.mul_mod_mul_right] at hr
    refine ⟨hq, ?_⟩
    rw [hr] at h₃
    obtain ⟨hr', _⟩ := div_mod_eq hF h₃ h₄
    rw [hr', Nat.mul_div_cancel _ hF]
  · -- The fallback, without normalization.
    obtain ⟨h₁, h₂⟩ := divRemBasecase_spec u v hn hvt
    simp only [toNat_toSlice] at h₁ h₂
    obtain ⟨hq, hr⟩ := div_mod_eq hVpos h₁ h₂
    exact ⟨hq, hr⟩

/-! ## Division -/

/-- `(a / b, a % b)`, trimmed. -/
public def divMod (a b : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  let n := topSize b
  if h₀ : n = 0 then
    (.empty, trim a.copy)
  else if h : n = 1 then
    let p := divRem1 a (b.getD 0 0)
    (trim p.1, trim (UInt32Array.mk #[p.2]))
  else
    let p := divModLimbs a (b.slice 0 n) (by simp; have := topSize_le b; omega)
    (trim p.1, trim p.2)

/-- Divides two numbers, with `a / 0 = 0`. -/
public def div (a b : UInt32Array.Slice) : UInt32Array := (divMod a b).1

/-- The remainder of dividing two numbers, with `a % 0 = a`. -/
public def mod (a b : UInt32Array.Slice) : UInt32Array := (divMod a b).2

private theorem toNat_copy (a : UInt32Array.Slice) : toNat a.copy = toNat a := by
  rw [toNat_toSlice]
  rfl

private theorem divMod_of_topSize_eq_zero (a b : UInt32Array.Slice) (h : topSize b = 0) :
    divMod a b = (.empty, trim a.copy) := by
  simp [divMod, h]

private theorem divMod_of_topSize_eq_one (a b : UInt32Array.Slice) (h : topSize b = 1) :
    divMod a b = (trim (divRem1 a (b.getD 0 0)).1,
      trim (UInt32Array.mk #[(divRem1 a (b.getD 0 0)).2])) := by
  simp [divMod, h]

private theorem divMod_of_two_le_topSize (a b : UInt32Array.Slice) (h : 2 ≤ topSize b) :
    divMod a b = (trim (divModLimbs a (b.slice 0 (topSize b))
        (by simp; have := topSize_le b; omega)).1,
      trim (divModLimbs a (b.slice 0 (topSize b)) (by simp; have := topSize_le b; omega)).2) := by
  simp [divMod, show topSize b ≠ 0 by omega, show topSize b ≠ 1 by omega]

/-- `divMod` divides, with `Nat`'s conventions for a zero divisor. -/
public theorem toNat_divMod (a b : UInt32Array.Slice) :
    toNat (divMod a b).1 = toNat a / toNat b ∧ toNat (divMod a b).2 = toNat a % toNat b := by
  have hb := toNat_slice_topSize b
  have hle := topSize_le b
  rcases Nat.lt_or_ge (topSize b) 2 with h | h
  · rcases Nat.lt_or_ge (topSize b) 1 with h' | h'
    · -- A zero divisor.
      have h₀ : topSize b = 0 := by omega
      have : toNat b = 0 := by
        rw [← hb, toNat_of_size_eq_zero (by simp [h₀])]
      rw [divMod_of_topSize_eq_zero a b h₀, this, Nat.div_zero, Nat.mod_zero]
      exact ⟨rfl, by rw [toNat_trim, toNat_copy]⟩
    · -- A divisor of one limb.
      have h₁ : topSize b = 1 := by omega
      have hd := getD_topSize_ne_zero b (by omega)
      rw [h₁] at hd
      have hb1 : toNat b = (b.getD 0 0).toNat := by
        rw [← hb, toNat_of_size_eq_one (by simp [h₁]; omega)]
        simp [UInt32Array.Slice.getD_eq, show 0 < b.size by omega]
      have hd' : 0 < (b.getD 0 0).toNat := by
        rcases Nat.eq_zero_or_pos (b.getD 0 0).toNat with h | h
        · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hd
        · exact h
      obtain ⟨h₂, h₃⟩ := divRem1_spec a (b.getD 0 0) hd
      obtain ⟨hq, hr⟩ := div_mod_eq hd' h₂ h₃
      rw [divMod_of_topSize_eq_one a b h₁, hb1, toNat_trim, toNat_trim, ← hq, ← hr]
      refine ⟨rfl, ?_⟩
      rw [toNat_toSlice]
      simp
  · -- A divisor of at least two limbs.
    have hs := divModLimbs_spec a (b.slice 0 (topSize b))
      (by simp; omega) (top_slice_topSize_ne_zero b (by omega))
    rw [hb] at hs
    rw [divMod_of_two_le_topSize a b h, toNat_trim, toNat_trim]
    exact hs

/-- Division is `Nat` division. -/
@[simp] public theorem toNat_div (a b : UInt32Array.Slice) : toNat (div a b) = toNat a / toNat b :=
  (toNat_divMod a b).1

/-- The remainder is `Nat`'s remainder. -/
@[simp] public theorem toNat_mod (a b : UInt32Array.Slice) : toNat (mod a b) = toNat a % toNat b :=
  (toNat_divMod a b).2

public theorem isTrimmed_div (a b : UInt32Array.Slice) : isTrimmed (div a b) = true := by
  rw [div]
  rcases Nat.lt_or_ge (topSize b) 2 with h | h
  · rcases Nat.lt_or_ge (topSize b) 1 with h' | h'
    · rw [divMod_of_topSize_eq_zero a b (by omega)]
      exact (isTrimmed_iff _).2 (by simp)
    · rw [divMod_of_topSize_eq_one a b (by omega)]
      exact isTrimmed_trim _
  · rw [divMod_of_two_le_topSize a b h]
    exact isTrimmed_trim _

public theorem isTrimmed_mod (a b : UInt32Array.Slice) : isTrimmed (mod a b) = true := by
  rw [mod]
  rcases Nat.lt_or_ge (topSize b) 2 with h | h
  · rcases Nat.lt_or_ge (topSize b) 1 with h' | h'
    · rw [divMod_of_topSize_eq_zero a b (by omega)]
      exact isTrimmed_trim _
    · rw [divMod_of_topSize_eq_one a b (by omega)]
      exact isTrimmed_trim _
  · rw [divMod_of_two_le_topSize a b h]
    exact isTrimmed_trim _

end Bignum
