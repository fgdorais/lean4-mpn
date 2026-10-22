/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray

/-!
# Comba multiplication

`mulComba r a b` writes the `a.size + b.size` limbs of `a * b` into the slice `r`, like
`mulBasecase`, but scans the products by columns: for each `k` it adds the products
`a[i] * b[k - i]` into a three-word accumulator, writes the low word to limb `k`, and shifts the
accumulator down by a word. It writes each limb of `r` once and never reads `r`. It requires
`a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.

The accumulator cannot overflow while `min a.size b.size < 2 ^ 62`, which `valAt_mulComba`
assumes.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## The column loop -/

/-- One product of `combaColLoop`: adds `x * y` to the accumulator `t₀ + 2⁶⁴ t₁ + 2¹²⁸ t₂`. -/
private theorem comba_step (x y t₀ t₁ t₂ : UInt64)
    (h : t₀.toNat + 2 ^ 64 * t₁.toNat + 2 ^ 128 * t₂.toNat + x.toNat * y.toNat < 2 ^ 192) :
    (t₀ + x * y).toNat + 2 ^ 64 * (t₁ + (x.mulh y + UInt64.addh 0 t₀ (x * y))).toNat +
        2 ^ 128 * (UInt64.addh t₂ t₁ (x.mulh y + UInt64.addh 0 t₀ (x * y))).toNat =
      t₀.toNat + 2 ^ 64 * t₁.toNat + 2 ^ 128 * t₂.toNat + x.toNat * y.toNat := by
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := x.toNat_lt; lia) (by have := y.toNat_lt; lia)
  have := t₀.toNat_lt; have := t₁.toNat_lt; have := t₂.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_zero]
  generalize x.toNat * y.toNat = p at *
  generalize t₀.toNat = t₀ at *
  generalize t₁.toNat = t₁ at *
  generalize t₂.toNat = t₂ at *
  lia

/--
Adds the products `a[i'] * b[k - i']` for `i'` from `i` to `hi - 1` to the accumulator
`t₀ + 2⁶⁴ t₁ + 2¹²⁸ t₂`.
-/
def combaColLoop (a b : USlice) (k hi : USize) (h₁ : hi ≤ a.size) (h₂ : hi.toNat ≤ k.toNat + 1)
    (i : USize) (h₃ : k.toNat < i.toNat + b.size.toNat) (t₀ t₁ t₂ : UInt64) :
    UInt64 × UInt64 × UInt64 :=
  if h : i < hi then
    let x := a[i]'(USize.lt_of_lt_of_le h h₁)
    let y := b[k - i]'(by
      have := USize.lt_iff_toNat_lt.1 h
      rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))]
      lia)
    let p := x * y
    let q := x.mulh y + UInt64.addh 0 t₀ p
    combaColLoop a b k hi h₁ h₂ (i + 1) (by rw [USize.toNat_add_one_of_lt h]; lia) (t₀ + p)
      (t₁ + q) (UInt64.addh t₂ t₁ q)
  else
    (t₀, t₁, t₂)
termination_by hi.toNat - i.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

/-- Limb `i` of `s`, as a number. -/
private def limb (s : USlice) (i : Nat) : Nat := s.array[s.start.toNat + i]!.toNat

private theorem limb_lt (s : USlice) (i : Nat) : limb s i < 2 ^ 64 := by
  rw [limb]; exact UInt64.toNat_lt _

private theorem limb_eq (s : USlice) (i : USize) (h : i < s.size) :
    s[i].toNat = limb s i.toNat := by
  rw [limb, USlice.getElem_eq_getElem!]

/-- The sum of the products `a[i] * b[k - i]` for `i` from `s` to `s + len - 1`. -/
private def colSum (a b : USlice) (k s : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => limb a s * limb b (k - s) + colSum a b k (s + 1) len

private theorem colSum_succ (a b : USlice) (k s len : Nat) :
    colSum a b k s (len + 1) = colSum a b k s len + limb a (s + len) * limb b (k - (s + len)) := by
  induction len generalizing s with
  | zero => simp [colSum]
  | succ len ih =>
    rw [colSum, ih, colSum, Nat.add_assoc, Nat.add_comm 1 len]
    grind

private theorem colSum_le (a b : USlice) (k s len : Nat) :
    colSum a b k s len ≤ len * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) := by
  induction len generalizing s with
  | zero => simp [colSum]
  | succ len ih =>
    have := ih (s + 1)
    have : limb a s * limb b (k - s) ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := limb_lt a s; lia) (by have := limb_lt b (k - s); lia)
    rw [colSum]
    generalize limb a s * limb b (k - s) = p at *
    lia

private theorem combaColLoop_spec (a b : USlice) (k hi : USize) (h₁ : hi ≤ a.size)
    (h₂ : hi.toNat ≤ k.toNat + 1) (i : USize) (h₃ : k.toNat < i.toNat + b.size.toNat)
    (t₀ t₁ t₂ : UInt64)
    (hb : t₀.toNat + 2 ^ 64 * t₁.toNat + 2 ^ 128 * t₂.toNat +
      (hi.toNat - i.toNat) * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) < 2 ^ 192) :
    (combaColLoop a b k hi h₁ h₂ i h₃ t₀ t₁ t₂).1.toNat +
        2 ^ 64 * (combaColLoop a b k hi h₁ h₂ i h₃ t₀ t₁ t₂).2.1.toNat +
        2 ^ 128 * (combaColLoop a b k hi h₁ h₂ i h₃ t₀ t₁ t₂).2.2.toNat =
      t₀.toNat + 2 ^ 64 * t₁.toNat + 2 ^ 128 * t₂.toNat +
        colSum a b k.toNat i.toNat (hi.toNat - i.toNat) := by
  induction i, h₃, t₀, t₁, t₂ using combaColLoop.induct a b k hi h₁ h₂ with
  | case1 i h₃ t₀ t₁ t₂ h x y p q ih =>
    rw [combaColLoop]
    simp only [h, ↓reduceDIte]
    have hlt := USize.lt_iff_toNat_lt.1 h
    have hi₁ := USize.toNat_add_one_of_lt h
    have ha := USize.le_iff_toNat_le.1 h₁
    rw [hi₁] at ih
    have hxy : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := x.toNat_lt; lia) (by have := y.toNat_lt; lia)
    have hstep := comba_step x y t₀ t₁ t₂ (by
      generalize x.toNat * y.toNat = p at *
      have : 1 ≤ hi.toNat - i.toNat := by lia
      generalize hi.toNat - i.toNat = d at *
      lia)
    rw [ih (by
      rw [hstep]
      generalize x.toNat * y.toNat = p at *
      rw [show hi.toNat - i.toNat = hi.toNat - (i.toNat + 1) + 1 by lia, Nat.succ_mul] at hb
      lia), hstep]
    have hki : (k - i).toNat = k.toNat - i.toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
    obtain ⟨len, hlen⟩ : ∃ len, hi.toNat - i.toNat = len + 1 := ⟨hi.toNat - i.toNat - 1, by lia⟩
    rw [hlen, show hi.toNat - (i.toNat + 1) = len by lia, colSum, limb_eq a i, limb_eq b (k - i),
      hki]
    lia
  | case2 i h₃ t₀ t₁ t₂ h =>
    rw [combaColLoop]
    have := USize.lt_iff_toNat_lt (a := i) (b := hi)
    simp [h, show hi.toNat - i.toNat = 0 by lia, colSum]

/-! ## Partial products by columns -/

/-- The value of the low `t` limbs of `b`. -/
private def pre (b : USlice) (t : Nat) : Nat := b.array.valAt b.start.toNat (min t b.size.toNat)

private theorem pre_zero (b : USlice) : pre b 0 = 0 := by
  simp [pre]

private theorem pre_succ (b : USlice) (t : Nat) :
    pre b (t + 1) = pre b t + if t < b.size.toNat then 2 ^ (64 * t) * limb b t else 0 := by
  rw [pre, pre]
  split
  · rw [show min (t + 1) b.size.toNat = t + 1 by lia, show min t b.size.toNat = t by lia,
      UInt64Array.valAt_add, UInt64Array.valAt_one, limb]
  · rw [show min (t + 1) b.size.toNat = b.size.toNat by lia,
      show min t b.size.toNat = b.size.toNat by lia]
    simp

private theorem pre_of_le (b : USlice) (t : Nat) (h : b.size.toNat ≤ t) :
    pre b t = b.toNat := by
  rw [pre, show min t b.size.toNat = b.size.toNat by lia, USlice.toNat_eq_valAt]

/--
The sum of the products `a[i] * b[j] * 2^(64 * (i + j))` with `i < c` and `i + j < k`: the part
of `a * b` below column `k` from the first `c` limbs of `a`.
-/
private def rowsVal (a b : USlice) (k : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => rowsVal a b k c + 2 ^ (64 * c) * (limb a c * pre b (k - c))

/-- The products in column `k` with `i < c`. -/
private def colUpTo (a b : USlice) (k : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 =>
    colUpTo a b k c + if c ≤ k ∧ k - c < b.size.toNat then limb a c * limb b (k - c) else 0

private theorem rowsVal_zero (a b : USlice) (c : Nat) : rowsVal a b 0 c = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => simp [rowsVal, ih, pre_zero]

private theorem rowsVal_succ (a b : USlice) (k c : Nat) :
    rowsVal a b (k + 1) c = rowsVal a b k c + 2 ^ (64 * k) * colUpTo a b k c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [rowsVal, rowsVal, colUpTo, ih]
    by_cases hc : c ≤ k
    · rw [show k + 1 - c = k - c + 1 by lia, pre_succ]
      have hk : 2 ^ (64 * k) = 2 ^ (64 * c) * 2 ^ (64 * (k - c)) := by
        rw [← Nat.pow_add]; congr 1; lia
      split <;> split <;> try lia
      rw [hk]
      generalize rowsVal a b k c = R
      generalize colUpTo a b k c = U
      generalize pre b (k - c) = B
      generalize limb a c = x
      generalize limb b (k - c) = y
      generalize 2 ^ (64 * c) = P
      generalize 2 ^ (64 * (k - c)) = Q
      grind
    · rw [show k + 1 - c = 0 by lia, show k - c = 0 by lia]
      simp only [hc, false_and, ↓reduceIte]
      lia

private theorem colUpTo_eq (a b : USlice) (k c : Nat) (hc : c ≤ a.size.toNat) :
    colUpTo a b k c =
      colSum a b k (k + 1 - b.size.toNat)
        (min c (min (k + 1) a.size.toNat) - (k + 1 - b.size.toNat)) := by
  induction c with
  | zero => simp [colUpTo, colSum]
  | succ c ih =>
    rw [colUpTo, ih (by lia)]
    by_cases h₁ : c ≤ k ∧ k - c < b.size.toNat
    · simp only [h₁, and_self, ↓reduceIte]
      rw [show min (c + 1) (min (k + 1) a.size.toNat) - (k + 1 - b.size.toNat) =
          min c (min (k + 1) a.size.toNat) - (k + 1 - b.size.toNat) + 1 by lia, colSum_succ,
        show k + 1 - b.size.toNat + (min c (min (k + 1) a.size.toNat) - (k + 1 - b.size.toNat)) =
          c by lia]
    · simp only [h₁, ↓reduceIte, Nat.add_zero]
      congr 1
      lia

private theorem rowsVal_full (a b : USlice) (K c : Nat) (h : c + b.size.toNat ≤ K) :
    rowsVal a b K c = a.array.valAt a.start.toNat c * b.toNat := by
  induction c with
  | zero => simp [rowsVal]
  | succ c ih =>
    rw [rowsVal, ih (by lia), pre_of_le b _ (by lia), UInt64Array.valAt_add,
      UInt64Array.valAt_one, ← limb]
    rw [Nat.add_mul, Nat.mul_assoc]

/-! ## The product -/

/-- The first `i` of column `k` with a limb of `b`: `k + 1 - b`, or `0`. -/
@[inline] def colLo (k b : USize) : USize := if b ≤ k + 1 then k + 1 - b else 0

private theorem toNat_colLo {k N : USize} (b : USize) (h : k < N) :
    (colLo k b).toNat = k.toNat + 1 - b.toNat := by
  have h₁ := USize.toNat_add_one_of_lt h
  rw [colLo]
  split
  · rename_i hb
    rw [USize.toNat_sub_of_le _ _ hb, h₁]
  · rename_i hb
    rw [USize.le_iff_toNat_le, h₁] at hb
    rw [USize.toNat_zero]
    lia

private theorem toNat_colHi {k N : USize} (a : USize) (h : k < N) :
    (min (k + 1) a).toNat = min (k.toNat + 1) a.toNat := by
  rw [USize.toNat_min, USize.toNat_add_one_of_lt h]

/--
Writes columns `k` to `N - 1` of `a * b`, where `N = a.size + b.size`, into `arr` from limb
`rs + k` on, with the accumulator `t₀ + 2⁶⁴ t₁` carried in from the columns below.
-/
def combaLoop (arr : UInt64Array) (rs : USize) (a b : USlice) (N : USize)
    (hN : N.toNat = a.size.toNat + b.size.toNat) (hr : LoopBound arr rs N) (k : USize)
    (t₀ t₁ : UInt64) : UInt64Array :=
  if h : k < N then
    let s := combaColLoop a b k (min (k + 1) a.size) (USize.min_le_right ..)
      (by rw [toNat_colHi _ h]; lia) (colLo k b.size)
      (by have := USize.lt_iff_toNat_lt.1 h; rw [toNat_colLo _ h]; lia) t₀ t₁ 0
    combaLoop (arr.uset (rs + k) s.1 (hr.uset_bound h)) rs a b N hN (hr.of_uset ..) (k + 1)
      s.2.1 s.2.2
  else
    arr
termination_by N.toNat - k.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

private theorem combaLoop_spec (arr : UInt64Array) (rs : USize) (a b : USlice) (N : USize)
    (hN : N.toNat = a.size.toNat + b.size.toNat) (hr : LoopBound arr rs N) (k : USize)
    (t₀ t₁ : UInt64) :
    (combaLoop arr rs a b N hN hr k t₀ t₁).size = arr.size ∧
      (∀ i, (i < rs.toNat + k.toNat ∨ rs.toNat + N.toNat ≤ i) →
        (combaLoop arr rs a b N hN hr k t₀ t₁)[i]! = arr[i]!) ∧
      (min a.size.toNat b.size.toNat < 2 ^ 62 → k.toNat ≤ N.toNat →
        arr.valAt rs.toNat k.toNat + 2 ^ (64 * k.toNat) * (t₀.toNat + 2 ^ 64 * t₁.toNat) =
          rowsVal a b k.toNat a.size.toNat →
        t₀.toNat + 2 ^ 64 * t₁.toNat ≤ 2 ^ 65 * min a.size.toNat b.size.toNat →
        (combaLoop arr rs a b N hN hr k t₀ t₁).valAt rs.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  induction arr, hr, k, t₀, t₁ using combaLoop.induct rs a b N hN with
  | case1 arr hr k t₀ t₁ h s ih =>
    rw [combaLoop]
    simp only [h, ↓reduceDIte]
    have hk := USize.lt_iff_toNat_lt.1 h
    have hk₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hlo := toNat_colLo b.size h
    have hhi := toNat_colHi a.size h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hk₁] at ih₂ ih₃
    simp only [size_uset] at ih₁
    refine ⟨ih₁, fun i hi => ?_, fun hmin _ hv hT => ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset, hidx]
      simp only [show ¬(rs.toNat + k.toNat = i) by lia, ↓reduceIte]
    · -- The column has at most `min a.size b.size` products, so the accumulator cannot overflow.
      have hd : min (k.toNat + 1) a.size.toNat - (k.toNat + 1 - b.size.toNat) ≤
          min a.size.toNat b.size.toNat := by lia
      have hcol := colSum_le a b k.toNat (k.toNat + 1 - b.size.toNat)
        (min (k.toNat + 1) a.size.toNat - (k.toNat + 1 - b.size.toNat))
      have hs := combaColLoop_spec a b k (min (k + 1) a.size) (USize.min_le_right ..)
        (by rw [hhi]; lia) (colLo k b.size) (by rw [hlo]; lia) t₀ t₁ 0 (by
          rw [hhi, hlo]
          simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
          generalize min (k.toNat + 1) a.size.toNat - (k.toNat + 1 - b.size.toNat) = d at *
          generalize min a.size.toNat b.size.toNat = M at *
          generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
          lia)
      simp only [hhi, hlo, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at hs
      have hU := colUpTo_eq a b k.toNat a.size.toNat (Nat.le_refl _)
      rw [show min a.size.toNat (min (k.toNat + 1) a.size.toNat) =
        min (k.toNat + 1) a.size.toNat by lia] at hU
      have hR := rowsVal_succ a b k.toNat a.size.toNat
      have hlow : (arr.uset (rs + k) s.1 (hr.uset_bound h)).valAt rs.toNat (k.toNat + 1) =
          arr.valAt rs.toNat k.toNat + 2 ^ (64 * k.toNat) * s.1.toNat := by
        rw [UInt64Array.valAt_add, UInt64Array.valAt_one, getElem!_uset, hidx]
        simp only [↓reduceIte]
        congr 1
        exact UInt64Array.valAt_congr _ fun i _ hi => by
          rw [getElem!_uset, hidx]
          simp only [show ¬(rs.toNat + k.toNat = i) by lia, ↓reduceIte]
      refine ih₃ hmin (by lia) ?_ ?_
      · rw [hlow, hR, hU, ← hv, Nat.mul_succ, Nat.pow_add]
        generalize colSum _ _ _ _ _ = col at *
        generalize s.1.toNat = s₀ at *
        generalize s.2.1.toNat = s₁ at *
        generalize s.2.2.toNat = s₂ at *
        generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
        generalize arr.valAt rs.toNat k.toNat = L at *
        generalize 2 ^ (64 * k.toNat) = P at *
        grind
      · generalize colSum _ _ _ _ _ = col at *
        generalize s.1.toNat = s₀ at *
        generalize s.2.1.toNat = s₁ at *
        generalize s.2.2.toNat = s₂ at *
        generalize min (k.toNat + 1) a.size.toNat - (k.toNat + 1 - b.size.toNat) = d at *
        generalize min a.size.toNat b.size.toNat = M at *
        generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
        lia
  | case2 arr hr k t₀ t₁ h =>
    rw [combaLoop]
    simp only [h, ↓reduceDIte]
    refine ⟨by simp, by simp, fun _ hk hv _ => ?_⟩
    have := USize.lt_iff_toNat_lt (a := k) (b := N)
    have hk' : k.toNat = a.size.toNat + b.size.toNat := by lia
    rw [hk', rowsVal_full a b _ _ (by lia), ← USlice.toNat_eq_valAt] at hv
    have hA := UInt64Array.valAt_lt a.array a.start.toNat a.size.toNat
    have hB := UInt64Array.valAt_lt b.array b.start.toNat b.size.toNat
    rw [← USlice.toNat_eq_valAt] at hA hB
    have hAB : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
      rw [Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt hA hB
    generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
    generalize a.toNat * b.toNat = AB at *
    generalize 2 ^ (64 * (a.size.toNat + b.size.toNat)) = P at *
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; lia
    · have := Nat.le_mul_of_pos_right P hT
      lia

private theorem comba_sum (r a b : USlice) (h : a.size ≤ r.size ∧ b.size ≤ r.size - a.size) :
    (a.size + b.size).toNat = a.size.toNat + b.size.toNat ∧ a.size + b.size ≤ r.size := by
  have h₁ := USize.le_iff_toNat_le.1 h.1
  have h₂ := USize.le_iff_toNat_le.1 h.2
  have := r.size.toNat_lt_size
  rw [USize.toNat_sub_of_le _ _ h.1] at h₂
  have hs : (a.size + b.size).toNat = a.size.toNat + b.size.toNat := USize.toNat_add_of_lt (by lia)
  exact ⟨hs, USize.le_iff_toNat_le.2 (by rw [hs]; lia)⟩

/--
Writes the `a.size + b.size` limbs of `a * b` into `r`, scanning the products by columns. It
requires `a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def mulComba (r a b : USlice) : UInt64Array :=
  if h : a.size ≤ r.size ∧ b.size ≤ r.size - a.size then
    combaLoop r.array r.start a b (a.size + b.size) (comba_sum r a b h).1
      (r.loopBound (comba_sum r a b h).2) 0 0 0
  else
    r.array

@[simp] public theorem size_mulComba (r a b : USlice) :
    (mulComba r a b).size = r.array.size := by
  rw [mulComba]
  split
  · exact (combaLoop_spec ..).1
  · rfl

/-- `mulComba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulComba (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulComba r a b)[i]! = r.array[i]! := by
  rw [mulComba]
  split
  · rename_i h
    exact (combaLoop_spec ..).2.1 i (by rw [USize.toNat_zero, (comba_sum r a b h).1]; lia)
  · rfl

public theorem valAt_mulComba (r a b : USlice) (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat)
    (hN : min a.size.toNat b.size.toNat < 2 ^ 62) :
    (mulComba r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  have h : a.size ≤ r.size ∧ b.size ≤ r.size - a.size := by
    refine ⟨USize.le_iff_toNat_le.2 (by lia), USize.le_iff_toNat_le.2 ?_⟩
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))]
    lia
  rw [mulComba]
  simp only [h, and_self, ↓reduceDIte]
  exact (combaLoop_spec ..).2.2 hN (by rw [USize.toNat_zero]; lia)
    (by simp [rowsVal_zero]) (by simp)

end MPN
