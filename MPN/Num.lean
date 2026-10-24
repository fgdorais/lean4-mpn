/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Mul
public import MPN.Div.Basecase

/-!
# Whole arrays as numbers

Each function of `MPN.Num` returns a new array whose value, `UInt64Array.toNat`, is the result of
an operation on the values of its arguments: `add`, `sub`, `mul`, `sqr`, `shl`, `shr`, `low`,
`lt` and `divModBase`, on top of the `mpn` functions. The arrays may have zero limbs on top.
Algorithms with few allocations per call, like the square root and the divide-and-conquer
division (`MPN.Div.DC`), are written with them and proved on `Nat`.
-/

open ScalarArray UInt64Array

namespace MPN.Num

/-! ## Fresh arrays -/

private theorem zeros_spec (n : Nat) (h : n < USize.size) :
    (UInt64Array.replicate n 0).toUSlice.start.toNat = 0 ∧
      (UInt64Array.replicate n 0).toUSlice.size.toNat = n ∧
      (UInt64Array.replicate n 0).toUSlice.array = UInt64Array.replicate n 0 := by
  refine ⟨by simp, ?_, rfl⟩
  have := size_toUSlice (UInt64Array.replicate n 0) (by simp; exact h)
  simpa using this

private theorem toUSlice_spec (a : UInt64Array) (h : a.size < USize.size) :
    a.toUSlice.start.toNat = 0 ∧ a.toUSlice.size.toNat = a.size ∧
      a.toUSlice.toNat = a.toNat :=
  ⟨by simp, size_toUSlice a h, toUSlice_toNat a h⟩

private theorem toNat_set_top (a : UInt64Array) (n : Nat) (c : UInt64) (h : n < a.size)
    (hs : a.size = n + 1) :
    (a.set! n c).toNat = a.valAt 0 n + 2 ^ (64 * n) * c.toNat := by
  rw [toNat_eq_valAt, size_set!, hs, UInt64Array.valAt_add, valAt_one, Nat.zero_add,
    getElem!_set!_self _ _ _ h,
    valAt_congr (b := a) _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)]

/-- No carry out of a value that fits. -/
private theorem no_carry {V P c X : Nat} (h : V + P * c = X) (hX : X < P) : V = X ∧ c = 0 := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp at h; exact ⟨h, rfl⟩
  · have := Nat.mul_le_mul_left P hc; lia

/-- A copy of the limbs of `s`. -/
public def ofSlice (s : USlice) : UInt64Array :=
  (add1 (UInt64Array.replicate s.size.toNat 0).toUSlice s 0).1

public theorem size_ofSlice (s : USlice) : (ofSlice s).size = s.size.toNat := by
  simp [ofSlice]

public theorem toNat_ofSlice (s : USlice) : (ofSlice s).toNat = s.toNat := by
  obtain ⟨z₁, z₂, z₃⟩ := zeros_spec s.size.toNat s.size.toNat_lt_size
  have h := valAt_add1 (UInt64Array.replicate s.size.toNat 0).toUSlice s 0
    (USize.le_iff_toNat_le.2 (by rw [z₂]; exact Nat.le_refl _))
  rw [z₁, UInt64.toNat_zero, Nat.add_zero] at h
  have hlt : s.toNat < 2 ^ (64 * s.size.toNat) := by
    rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
  rw [toNat_eq_valAt, size_ofSlice]
  exact (no_carry h hlt).1

/-! ## Addition and subtraction -/

private def addAux (a b : UInt64Array) : UInt64Array :=
  let p := MPN.add (UInt64Array.replicate (a.size + 1) 0).toUSlice a.toUSlice b.toUSlice
  p.1.set! a.size p.2

private theorem toNat_addAux (a b : UInt64Array) (hba : b.size ≤ a.size)
    (hU : a.size + 1 < USize.size) : (addAux a b).toNat = a.toNat + b.toNat := by
  obtain ⟨z₁, z₂, -⟩ := zeros_spec (a.size + 1) hU
  obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a (by lia)
  obtain ⟨b₁, b₂, b₃⟩ := toUSlice_spec b (by lia)
  have h := valAt_add (UInt64Array.replicate (a.size + 1) 0).toUSlice a.toUSlice b.toUSlice 0
    (USize.le_iff_toNat_le.2 (by rw [a₂, b₂]; exact hba))
    (USize.le_iff_toNat_le.2 (by rw [a₂, z₂]; lia))
  rw [z₁, a₂, a₃, b₃, UInt64.toNat_zero, Nat.add_zero] at h
  rw [addAux, toNat_set_top _ _ _ (by simp) (by simp)]
  exact h

/-- `a + b`, in `max a.size b.size + 1` limbs. -/
public def add (a b : UInt64Array) : UInt64Array :=
  if b.size ≤ a.size then addAux a b else addAux b a

public theorem toNat_add (a b : UInt64Array) (hU : a.size + b.size + 1 < USize.size) :
    (add a b).toNat = a.toNat + b.toNat := by
  rw [add]
  split
  · exact toNat_addAux a b (by lia) (by lia)
  · rw [toNat_addAux b a (by lia) (by lia), Nat.add_comm]

public theorem size_add (a b : UInt64Array) : (add a b).size = max a.size b.size + 1 := by
  rw [add]; split <;> simp [addAux] <;> lia

/-- `a - b`, in `a.size` limbs, for `b ≤ a`. -/
public def sub (a b : UInt64Array) : UInt64Array :=
  let b' := if b.size ≤ a.size then b.toUSlice else b.toUSlice.slice 0 a.usize
  (MPN.sub (UInt64Array.replicate a.size 0).toUSlice a.toUSlice b' 0).1

public theorem size_sub (a b : UInt64Array) : (sub a b).size = a.size := by
  simp [sub]

public theorem toNat_sub (a b : UInt64Array) (hle : b.toNat ≤ a.toNat)
    (ha : a.size < USize.size) (hb : b.size < USize.size) :
    (sub a b).toNat = a.toNat - b.toNat := by
  obtain ⟨z₁, z₂, -⟩ := zeros_spec a.size ha
  obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a ha
  obtain ⟨b₁, b₂, b₃⟩ := toUSlice_spec b hb
  have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hau : a.usize.toNat = a.size := by
    simp [usize, Nat.mod_eq_of_lt ha]
  -- The subtrahend, cut to the size of `a`.
  have hb' : (if b.size ≤ a.size then b.toUSlice else b.toUSlice.slice 0 a.usize).size.toNat ≤
        a.size ∧
      (if b.size ≤ a.size then b.toUSlice else b.toUSlice.slice 0 a.usize).toNat = b.toNat := by
    split
    · exact ⟨by rw [b₂]; assumption, b₃⟩
    · rename_i h
      rw [USlice.size_slice _ (by simp) (by rw [hau, b₂]; lia), USlice.toNat_slice _ (by simp)
        (by rw [hau, b₂]; lia), b₁, hau]
      refine ⟨by simp, ?_⟩
      simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, array_toUSlice]
      rw [valAt_mod _ _ (show a.size ≤ b.size by lia), ← toNat_eq_valAt, Nat.mod_eq_of_lt (by lia)]
  obtain ⟨hs, hv⟩ := hb'
  have h := valAt_sub (UInt64Array.replicate a.size 0).toUSlice a.toUSlice
    (if b.size ≤ a.size then b.toUSlice else b.toUSlice.slice 0 a.usize) 0
    (USize.le_iff_toNat_le.2 (by rw [a₂]; exact hs))
    (USize.le_iff_toNat_le.2 (by rw [a₂, z₂]; exact Nat.le_refl _))
  rw [z₁, a₂, a₃, hv, UInt64.toNat_zero, Nat.add_zero] at h
  have hV := valAt_lt (MPN.sub (UInt64Array.replicate a.size 0).toUSlice a.toUSlice
    (if b.size ≤ a.size then b.toUSlice else b.toUSlice.slice 0 a.usize) 0).1 0 a.size
  rw [sub, toNat_eq_valAt, size_sub', z₂]
  · generalize (MPN.sub _ _ _ _).1.valAt 0 a.size = V at *
    generalize (MPN.sub _ _ _ _).2.toNat = c at *
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc; lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * a.size)) hc; lia
where
  size_sub' : (MPN.sub (UInt64Array.replicate a.size 0).toUSlice a.toUSlice
      (if b.size ≤ a.size then b.toUSlice else b.toUSlice.slice 0 a.usize) 0).1.size =
      (UInt64Array.replicate a.size 0).toUSlice.size.toNat := by
    simp [zeros_spec a.size ha]

/-! ## Products -/

/-- `a b`, in `a.size + b.size` limbs. -/
public def mul (a b : UInt64Array) : UInt64Array :=
  if a.size = 0 ∨ b.size = 0 then UInt64Array.replicate 0 0
  else MPN.mul (UInt64Array.replicate (a.size + b.size) 0).toUSlice a.toUSlice b.toUSlice

public theorem toNat_mul (a b : UInt64Array) (hU : a.size + b.size < USize.size) :
    (mul a b).toNat = a.toNat * b.toNat := by
  rw [mul]
  split
  · rename_i h
    have : a.toNat = 0 ∨ b.toNat = 0 := by
      rcases h with h | h
      · left; rw [toNat_eq_valAt, h, valAt_zero]
      · right; rw [toNat_eq_valAt, h, valAt_zero]
    rcases this with h | h <;> simp [h, toNat_eq_valAt]
  · rename_i h
    obtain ⟨z₁, z₂, -⟩ := zeros_spec (a.size + b.size) hU
    obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a (by lia)
    obtain ⟨b₁, b₂, b₃⟩ := toUSlice_spec b (by lia)
    have hm := valAt_mul (UInt64Array.replicate (a.size + b.size) 0).toUSlice a.toUSlice
      b.toUSlice (USize.lt_iff_toNat_lt.2 (by rw [a₂]; simp; lia))
      (USize.lt_iff_toNat_lt.2 (by rw [b₂]; simp; lia)) (by rw [a₂, b₂, z₂]; exact Nat.le_refl _)
    rw [z₁, a₂, b₂, a₃, b₃] at hm
    rw [toNat_eq_valAt]
    simpa using hm

public theorem size_mul_le (a b : UInt64Array) : (mul a b).size ≤ a.size + b.size := by
  rw [mul]; split <;> simp

/-- `a²`, in `2 a.size` limbs. -/
public def sqr (a : UInt64Array) : UInt64Array :=
  if a.size = 0 then UInt64Array.replicate 0 0
  else MPN.sqr (UInt64Array.replicate (2 * a.size) 0).toUSlice a.toUSlice

public theorem toNat_sqr (a : UInt64Array) (hU : 2 * a.size < USize.size) :
    (sqr a).toNat = a.toNat * a.toNat := by
  rw [sqr]
  split
  · rename_i h
    have : a.toNat = 0 := by rw [toNat_eq_valAt, h, valAt_zero]
    simp [this, toNat_eq_valAt]
  · rename_i h
    obtain ⟨z₁, z₂, -⟩ := zeros_spec (2 * a.size) hU
    obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a (by lia)
    have hm := valAt_sqr (UInt64Array.replicate (2 * a.size) 0).toUSlice a.toUSlice
      (USize.lt_iff_toNat_lt.2 (by rw [a₂]; simp; lia)) (by rw [a₂, z₂]; exact Nat.le_refl _)
    rw [z₁, a₂, a₃] at hm
    rw [toNat_eq_valAt]
    simpa using hm

public theorem size_sqr_le (a : UInt64Array) : (sqr a).size ≤ 2 * a.size := by
  rw [sqr]; split <;> simp

/-! ## Shifts -/

/-- `a 2ᵏ`, in `k / 64 + a.size + 1` limbs. -/
public def shl (a : UInt64Array) (k : Nat) : UInt64Array :=
  let p := shiftLeft (UInt64Array.replicate (k / 64 + a.size + 1) 0).toUSlice a.toUSlice k
  p.1.set! (k / 64 + a.size) p.2

public theorem size_shl (a : UInt64Array) (k : Nat) : (shl a k).size = k / 64 + a.size + 1 := by
  simp [shl]

public theorem toNat_shl (a : UInt64Array) (k : Nat) (hU : k / 64 + a.size + 1 < USize.size) :
    (shl a k).toNat = a.toNat * 2 ^ k := by
  obtain ⟨z₁, z₂, -⟩ := zeros_spec (k / 64 + a.size + 1) hU
  obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a (by lia)
  have h := valAt_shiftLeft (UInt64Array.replicate (k / 64 + a.size + 1) 0).toUSlice a.toUSlice k
    (by rw [a₂, z₂]; lia)
  rw [z₁, a₂, a₃] at h
  rw [shl, toNat_set_top _ _ _ (by simp) (by simp)]
  exact h

/-- `a / 2ᵏ`, in `a.size - k / 64` limbs. -/
public def shr (a : UInt64Array) (k : Nat) : UInt64Array :=
  shiftRight (UInt64Array.replicate (a.size - k / 64) 0).toUSlice a.toUSlice k

public theorem size_shr (a : UInt64Array) (k : Nat) : (shr a k).size = a.size - k / 64 := by
  simp [shr]

public theorem toNat_shr (a : UInt64Array) (k : Nat) (hU : a.size < USize.size) :
    (shr a k).toNat = a.toNat / 2 ^ k := by
  obtain ⟨z₁, z₂, -⟩ := zeros_spec (a.size - k / 64) (by lia)
  obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a hU
  have h := valAt_shiftRight (UInt64Array.replicate (a.size - k / 64) 0).toUSlice a.toUSlice k
    (by rw [a₂, z₂]; exact Nat.le_refl _)
  rw [z₁, a₂, a₃] at h
  rw [toNat_eq_valAt, size_shr]
  exact h

/-! ## Comparison -/

/-- Limb `i` of `a`, or `0` past its end. -/
@[inline] public def limbAt (a : UInt64Array) (i : Nat) : UInt64 :=
  if h : i < a.size then a[i] else 0

public theorem limbAt_eq (a : UInt64Array) (i : Nat) : limbAt a i = a[i]! := by
  unfold limbAt
  split
  · rw [getElem!_eq_getElem]
  · rename_i h; rw [getElem!_neg a i h]; rfl

/-- Whether limbs `0` to `i - 1` of `a` are below those of `b`, comparing from the top down. -/
public def ltLoop (a b : UInt64Array) : Nat → Bool
  | 0 => false
  | i + 1 =>
    let x := limbAt a i
    let y := limbAt b i
    if x < y then true else if y < x then false else ltLoop a b i

private theorem ltLoop_iff (a b : UInt64Array) :
    ∀ i, ltLoop a b i = true ↔ a.valAt 0 i < b.valAt 0 i := by
  intro i
  induction i with
  | zero => simp [ltLoop]
  | succ i ih =>
    have ea := UInt64Array.valAt_add a 0 i 1
    have eb := UInt64Array.valAt_add b 0 i 1
    rw [valAt_one, Nat.zero_add] at ea eb
    rw [ea, eb, ltLoop, ← limbAt_eq, ← limbAt_eq]
    have hla := valAt_lt a 0 i
    have hlb := valAt_lt b 0 i
    generalize a.valAt 0 i = La at *
    generalize b.valAt 0 i = Lb at *
    generalize 2 ^ (64 * i) = P at *
    generalize limbAt a i = x
    generalize limbAt b i = y
    split
    · rename_i h
      rw [UInt64.lt_iff_toNat_lt] at h
      have := Nat.mul_le_mul_left P (show x.toNat + 1 ≤ y.toNat from h)
      rw [Nat.mul_add, Nat.mul_one] at this
      simp only [true_iff]
      lia
    · split
      · rename_i _ h
        rw [UInt64.lt_iff_toNat_lt] at h
        have := Nat.mul_le_mul_left P (show y.toNat + 1 ≤ x.toNat from h)
        rw [Nat.mul_add, Nat.mul_one] at this
        simp only [Bool.false_eq_true, false_iff, Nat.not_lt]
        lia
      · rename_i h₁ h₂
        have e : x = y := by
          rw [UInt64.lt_iff_toNat_lt] at h₁ h₂
          exact UInt64.toNat_inj.1 (by lia)
        rw [ih, e]
        lia

/-- Limbs past the end are zero. -/
private theorem valAt_past (a : UInt64Array) : ∀ k lo, a.size ≤ lo → a.valAt lo k = 0 := by
  intro k
  induction k with
  | zero => intro lo _; simp
  | succ k ih =>
    intro lo h
    rw [valAt_succ, ih (lo + 1) (by lia), getElem!_neg a lo (by lia)]
    rfl

public theorem valAt_ge (a : UInt64Array) (m : Nat) (h : a.size ≤ m) :
    a.valAt 0 m = a.toNat := by
  rw [toNat_eq_valAt, show m = a.size + (m - a.size) by lia, UInt64Array.valAt_add,
    valAt_past a _ (0 + a.size) (by lia), Nat.mul_zero, Nat.add_zero]

/-- Whether `a < b`, comparing limbs from the top down. -/
public def lt (a b : UInt64Array) : Bool := ltLoop a b (max a.size b.size)

public theorem lt_iff (a b : UInt64Array) (_hU : a.size + b.size < USize.size) :
    lt a b = true ↔ a.toNat < b.toNat := by
  rw [lt, ltLoop_iff, valAt_ge a _ (by lia), valAt_ge b _ (by lia)]

/-! ## Division -/

/--
`(a / b, a % b)`, for `0 < b`, by `divRem` on the limbs of `b` up to its top nonzero limb, which
`log2` finds.
-/
public def divModBase (a b : UInt64Array) : UInt64Array × UInt64Array :=
  let nb := MPN.log2 b.toUSlice / 64 + 1
  if a.size < nb then (UInt64Array.replicate 0 0, a)
  else
    divRem (UInt64Array.replicate (a.size - nb + 1) 0).toUSlice
      (UInt64Array.replicate nb 0).toUSlice a.toUSlice (b.toUSlice.slice 0 nb.toUSize)

public theorem size_divModBase (a b : UInt64Array) (hb : b.size < USize.size) :
    (divModBase a b).1.size ≤ a.size + 1 ∧ (divModBase a b).2.size ≤ max a.size b.size := by
  unfold divModBase
  dsimp only
  split
  · simp; lia
  · simp only [size_divRem_fst, size_divRem_snd, array_toUSlice, UInt64Array.size_replicate]
    -- The divisor has at most `b.size` nonzero limbs.
    have h₁ := toUSlice_spec b hb
    rw [log2_eq, h₁.2.2]
    have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    by_cases h0 : b.toNat = 0
    · rw [h0]; simp; lia
    · have := Nat.log2_self_le h0
      have : _root_.Nat.log2 b.toNat < 64 * b.size := by
        refine Nat.lt_of_not_le fun h => ?_
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
        lia
      lia

public theorem toNat_divModBase (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divModBase a b).1.toNat = a.toNat / b.toNat ∧
      (divModBase a b).2.toNat = a.toNat % b.toNat := by
  obtain ⟨b₁, b₂, b₃⟩ := toUSlice_spec b (by lia)
  obtain ⟨a₁, a₂, a₃⟩ := toUSlice_spec a (by lia)
  have hL : MPN.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by rw [log2_eq, b₃]
  generalize hl : _root_.Nat.log2 b.toNat = L at hL
  have hb₀ : b.toNat ≠ 0 := by lia
  have hlo : 2 ^ L ≤ b.toNat := by rw [← hl]; exact Nat.log2_self_le hb₀
  have hhi : b.toNat < 2 ^ (L + 1) := by rw [← hl]; exact Nat.lt_log2_self
  have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hlow : 2 ^ (64 * (L / 64)) ≤ b.toNat :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hlo
  have hup : b.toNat < 2 ^ (64 * (L / 64 + 1)) :=
    Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by lia))
  have hnb : L / 64 + 1 ≤ b.size := by
    refine Nat.le_of_not_lt fun h => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 64 * b.size ≤ 64 * (L / 64) by lia)
    lia
  unfold divModBase
  dsimp only
  rw [hL]
  split
  · rename_i h
    have hlt : a.toNat < b.toNat :=
      Nat.lt_of_lt_of_le hA (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hlow)
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, toNat_eq_valAt]
    simp
  · rename_i h
    -- The divisor without its zero limbs on top.
    have hq : (L / 64 + 1).toUSize.toNat = L / 64 + 1 := USize.toNat_ofNat_of_lt' (by lia)
    have hs : (b.toUSlice.slice 0 (L / 64 + 1).toUSize).size.toNat = L / 64 + 1 := by
      rw [USlice.size_slice _ (by simp) (by rw [hq, b₂]; exact hnb), hq]; rfl
    have hst : (b.toUSlice.slice 0 (L / 64 + 1).toUSize).start.toNat = 0 := by
      rw [USlice.start_slice _ (by simp) (by rw [hq, b₂]; exact hnb), b₁]; rfl
    have hv : (b.toUSlice.slice 0 (L / 64 + 1).toUSize).toNat = b.toNat := by
      rw [USlice.toNat_slice _ (by simp) (by rw [hq, b₂]; exact hnb), b₁, hq]
      simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, array_toUSlice]
      rw [valAt_mod _ _ hnb, ← toNat_eq_valAt, Nat.mod_eq_of_lt hup]
    have ht : (b.toUSlice.slice 0 (L / 64 + 1).toUSize).array[
        (b.toUSlice.slice 0 (L / 64 + 1).toUSize).start.toNat +
          (b.toUSlice.slice 0 (L / 64 + 1).toUSize).size.toNat - 1]! ≠ 0 := by
      rw [hst, hs, USlice.array_slice, array_toUSlice, Nat.zero_add, Nat.add_sub_cancel]
      intro h0
      have e := UInt64Array.valAt_add b 0 (L / 64) 1
      rw [valAt_one, Nat.zero_add, h0, valAt_mod _ _ hnb, ← toNat_eq_valAt,
        Nat.mod_eq_of_lt hup] at e
      have := valAt_lt b 0 (L / 64)
      simp at e
      lia
    obtain ⟨q₁, q₂, -⟩ := zeros_spec (a.size - (L / 64 + 1) + 1) (by lia)
    obtain ⟨r₁, r₂, -⟩ := zeros_spec (L / 64 + 1) (by lia)
    have hpos : 0 < (b.toUSlice.slice 0 (L / 64 + 1).toUSize).size.toNat := by rw [hs]; lia
    have hab : (b.toUSlice.slice 0 (L / 64 + 1).toUSize).size ≤ a.toUSlice.size :=
      USize.le_iff_toNat_le.2 (by rw [hs, a₂]; lia)
    have hq' : a.toUSlice.size.toNat - (b.toUSlice.slice 0 (L / 64 + 1).toUSize).size.toNat + 1 ≤
        (UInt64Array.replicate (a.size - (L / 64 + 1) + 1) 0).toUSlice.size.toNat := by
      rw [a₂, hs, q₂]; exact Nat.le_refl _
    have hr' : (b.toUSlice.slice 0 (L / 64 + 1).toUSize).size ≤
        (UInt64Array.replicate (L / 64 + 1) 0).toUSlice.size :=
      USize.le_iff_toNat_le.2 (by rw [hs, r₂]; exact Nat.le_refl _)
    have hU' : a.toUSlice.size.toNat + 1 < USize.size := by rw [a₂]; lia
    have e₁ := valAt_divRem_fst _ _ _ _ hpos hab ht hq' hr' hU'
    have e₂ := valAt_divRem_snd _ _ _ _ hpos hab ht hq' hr' hU'
    rw [q₁, a₂, hs, a₃, hv] at e₁
    rw [r₁, hs, a₃, hv] at e₂
    refine ⟨?_, ?_⟩
    · rw [toNat_eq_valAt, size_divRem_fst]
      simpa using e₁
    · rw [toNat_eq_valAt, size_divRem_snd]
      simpa using e₂

/-! ## Truncation -/

/-- `a % β^k`, in `min k a.size` limbs. -/
public def low (a : UInt64Array) (k : Nat) : UInt64Array :=
  ofSlice (a.toUSlice.slice 0 (min k a.size).toUSize)

public theorem size_low (a : UInt64Array) (k : Nat) (hU : a.size < USize.size) :
    (low a k).size = min k a.size := by
  obtain ⟨a₁, a₂, -⟩ := toUSlice_spec a hU
  have hm : (min k a.size).toUSize.toNat = min k a.size := USize.toNat_ofNat_of_lt' (by lia)
  rw [low, size_ofSlice, USlice.size_slice _ (by simp) (by rw [hm, a₂]; lia), hm]
  rfl

public theorem toNat_low (a : UInt64Array) (k : Nat) (hU : a.size < USize.size) :
    (low a k).toNat = a.toNat % 2 ^ (64 * k) := by
  obtain ⟨a₁, a₂, -⟩ := toUSlice_spec a hU
  have hm : (min k a.size).toUSize.toNat = min k a.size := USize.toNat_ofNat_of_lt' (by lia)
  rw [low, toNat_ofSlice, USlice.toNat_slice _ (by simp) (by rw [hm, a₂]; lia), hm, a₁]
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, array_toUSlice]
  rw [valAt_mod _ _ (Nat.min_le_right k a.size), ← toNat_eq_valAt]
  have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  by_cases h : k ≤ a.size
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by lia), Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia)))]

end MPN.Num
