/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray

/-!
# Comba multiplication

`mulComba r off a b` writes the `a.size + b.size` limbs of `a * b` into `r` from limb `off` on,
like `mulBasecase`, but scans the products by columns: for each `k` it adds the products
`a[i] * b[k - i]` into a three-word accumulator, writes the low word to limb `k`, and shifts the
accumulator down by a word. It writes each limb of `r` once and never reads `r`.

The accumulator cannot overflow while `min a.size b.size < 2 ^ 62`, which `valAt_mulComba`
assumes.
-/

open ScalarArray

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
def combaColLoop (a b : UInt64Array.Slice) (k hi : Nat) (h₁ : hi ≤ a.size) (h₂ : hi ≤ k + 1)
    (i : Nat) (h₃ : k < i + b.size) (t₀ t₁ t₂ : UInt64) : UInt64 × UInt64 × UInt64 :=
  if h : i < hi then
    let x := a[i]'(by lia)
    let y := b[k - i]'(by lia)
    let p := x * y
    let q := x.mulh y + UInt64.addh 0 t₀ p
    combaColLoop a b k hi h₁ h₂ (i + 1) (by lia) (t₀ + p) (t₁ + q) (UInt64.addh t₂ t₁ q)
  else
    (t₀, t₁, t₂)

/-- Limb `i` of `s`, as a number. -/
private def limb (s : UInt64Array.Slice) (i : Nat) : Nat := s.array[s.start + i]!.toNat

private theorem limb_lt (s : UInt64Array.Slice) (i : Nat) : limb s i < 2 ^ 64 := by
  rw [limb]; exact UInt64.toNat_lt _

private theorem limb_eq (s : UInt64Array.Slice) (i : Nat) (h : i < s.size) :
    s[i].toNat = limb s i := by
  rw [limb, UInt64Array.Slice.getElem_eq_getElem!]

/-- The sum of the products `a[i] * b[k - i]` for `i` from `s` to `s + len - 1`. -/
private def colSum (a b : UInt64Array.Slice) (k s : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => limb a s * limb b (k - s) + colSum a b k (s + 1) len

private theorem colSum_succ (a b : UInt64Array.Slice) (k s len : Nat) :
    colSum a b k s (len + 1) = colSum a b k s len + limb a (s + len) * limb b (k - (s + len)) := by
  induction len generalizing s with
  | zero => simp [colSum]
  | succ len ih =>
    rw [colSum, ih, colSum, Nat.add_assoc, Nat.add_comm 1 len]
    grind

private theorem colSum_le (a b : UInt64Array.Slice) (k s len : Nat) :
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

private theorem combaColLoop_spec (a b : UInt64Array.Slice) (k hi : Nat) (h₁ : hi ≤ a.size)
    (h₂ : hi ≤ k + 1) (i : Nat) (h₃ : k < i + b.size) (t₀ t₁ t₂ : UInt64)
    (hb : t₀.toNat + 2 ^ 64 * t₁.toNat + 2 ^ 128 * t₂.toNat +
      (hi - i) * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) < 2 ^ 192) :
    (combaColLoop a b k hi h₁ h₂ i h₃ t₀ t₁ t₂).1.toNat +
        2 ^ 64 * (combaColLoop a b k hi h₁ h₂ i h₃ t₀ t₁ t₂).2.1.toNat +
        2 ^ 128 * (combaColLoop a b k hi h₁ h₂ i h₃ t₀ t₁ t₂).2.2.toNat =
      t₀.toNat + 2 ^ 64 * t₁.toNat + 2 ^ 128 * t₂.toNat + colSum a b k i (hi - i) := by
  induction i, h₃, t₀, t₁, t₂ using combaColLoop.induct a b k hi h₁ h₂ with
  | case1 i h₃ t₀ t₁ t₂ h x y p q ih =>
    rw [combaColLoop]
    simp only [h, ↓reduceDIte]
    have hxy : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := x.toNat_lt; lia) (by have := y.toNat_lt; lia)
    have hstep := comba_step x y t₀ t₁ t₂ (by
      generalize x.toNat * y.toNat = p at *
      have : 1 ≤ hi - i := by lia
      generalize hi - i = d at *
      lia)
    rw [ih (by
      rw [hstep]
      generalize x.toNat * y.toNat = p at *
      rw [show hi - i = hi - (i + 1) + 1 by lia, Nat.succ_mul] at hb
      lia), hstep]
    obtain ⟨len, hlen⟩ : ∃ len, hi - i = len + 1 := ⟨hi - i - 1, by lia⟩
    rw [hlen, show hi - (i + 1) = len by lia, colSum, ← limb_eq a i (by lia),
      ← limb_eq b (k - i) (by lia)]
    lia
  | case2 i h₃ t₀ t₁ t₂ h =>
    rw [combaColLoop]
    simp [h, show hi - i = 0 by lia, colSum]

/-! ## Partial products by columns -/

/-- The value of the low `t` limbs of `b`. -/
private def pre (b : UInt64Array.Slice) (t : Nat) : Nat := b.array.valAt b.start (min t b.size)

private theorem pre_zero (b : UInt64Array.Slice) : pre b 0 = 0 := by
  simp [pre]

private theorem pre_succ (b : UInt64Array.Slice) (t : Nat) :
    pre b (t + 1) = pre b t + if t < b.size then 2 ^ (64 * t) * limb b t else 0 := by
  rw [pre, pre]
  split
  · rw [show min (t + 1) b.size = t + 1 by lia, show min t b.size = t by lia,
      UInt64Array.valAt_add, UInt64Array.valAt_one, limb]
  · rw [show min (t + 1) b.size = b.size by lia, show min t b.size = b.size by lia]
    simp

private theorem pre_of_le (b : UInt64Array.Slice) (t : Nat) (h : b.size ≤ t) :
    pre b t = b.toNat := by
  rw [pre, show min t b.size = b.size by lia, UInt64Array.Slice.toNat_eq_valAt]

/--
The sum of the products `a[i] * b[j] * 2^(64 * (i + j))` with `i < c` and `i + j < k`: the part
of `a * b` below column `k` from the first `c` limbs of `a`.
-/
private def rowsVal (a b : UInt64Array.Slice) (k : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => rowsVal a b k c + 2 ^ (64 * c) * (limb a c * pre b (k - c))

/-- The products in column `k` with `i < c`. -/
private def colUpTo (a b : UInt64Array.Slice) (k : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 =>
    colUpTo a b k c + if c ≤ k ∧ k - c < b.size then limb a c * limb b (k - c) else 0

private theorem rowsVal_zero (a b : UInt64Array.Slice) (c : Nat) : rowsVal a b 0 c = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => simp [rowsVal, ih, pre_zero]

private theorem rowsVal_succ (a b : UInt64Array.Slice) (k c : Nat) :
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

private theorem colUpTo_eq (a b : UInt64Array.Slice) (k c : Nat) (hc : c ≤ a.size) :
    colUpTo a b k c =
      colSum a b k (k + 1 - b.size) (min c (min (k + 1) a.size) - (k + 1 - b.size)) := by
  induction c with
  | zero => simp [colUpTo, colSum]
  | succ c ih =>
    rw [colUpTo, ih (by lia)]
    by_cases h₁ : c ≤ k ∧ k - c < b.size
    · simp only [h₁, and_self, ↓reduceIte]
      rw [show min (c + 1) (min (k + 1) a.size) - (k + 1 - b.size) =
          min c (min (k + 1) a.size) - (k + 1 - b.size) + 1 by lia, colSum_succ,
        show k + 1 - b.size + (min c (min (k + 1) a.size) - (k + 1 - b.size)) = c by lia]
    · simp only [h₁, ↓reduceIte, Nat.add_zero]
      congr 1
      lia

private theorem rowsVal_full (a b : UInt64Array.Slice) (K c : Nat) (h : c + b.size ≤ K) :
    rowsVal a b K c = a.array.valAt a.start c * b.toNat := by
  induction c with
  | zero => simp [rowsVal]
  | succ c ih =>
    rw [rowsVal, ih (by lia), pre_of_le b _ (by lia), UInt64Array.valAt_add,
      UInt64Array.valAt_one, ← limb]
    rw [Nat.add_mul, Nat.mul_assoc]

/-! ## The product -/

/--
Writes columns `k` to `a.size + b.size - 1` of `a * b` into `r` from limb `off + k` on, with the
accumulator `t₀ + 2⁶⁴ t₁` carried in from the columns below.
-/
def combaLoop (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (k : Nat) (t₀ t₁ : UInt64) :
    UInt64Array :=
  if k < a.size + b.size then
    let s := combaColLoop a b k (min (k + 1) a.size) (Nat.min_le_right ..) (Nat.min_le_left ..)
      (k + 1 - b.size) (by lia) t₀ t₁ 0
    combaLoop (r.set! (off + k) s.1) off a b (k + 1) s.2.1 s.2.2
  else
    r

/--
Writes the `a.size + b.size` limbs of `a * b` into `r` from limb `off` on, scanning the products
by columns.
-/
public def mulComba (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) : UInt64Array :=
  combaLoop r off a b 0 0 0

private theorem combaLoop_spec (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (k : Nat)
    (t₀ t₁ : UInt64) (hr : off + a.size + b.size ≤ r.size)
    (hN : min a.size b.size < 2 ^ 62) :
    (combaLoop r off a b k t₀ t₁).size = r.size ∧
      (∀ i, (i < off + k ∨ off + a.size + b.size ≤ i) →
        (combaLoop r off a b k t₀ t₁)[i]! = r[i]!) ∧
      (k ≤ a.size + b.size →
        r.valAt off k + 2 ^ (64 * k) * (t₀.toNat + 2 ^ 64 * t₁.toNat) = rowsVal a b k a.size →
        t₀.toNat + 2 ^ 64 * t₁.toNat ≤ 2 ^ 65 * min a.size b.size →
        (combaLoop r off a b k t₀ t₁).valAt off (a.size + b.size) = a.toNat * b.toNat) := by
  induction r, k, t₀, t₁ using combaLoop.induct off a b with
  | case1 r k t₀ t₁ h s ih =>
    rw [combaLoop]
    simp only [h, ↓reduceIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    refine ⟨ih₁, fun i hi => ?_, fun _ hv hT => ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!_of_ne _ _ (by lia)]
    · -- The column has at most `min a.size b.size` products, so the accumulator cannot overflow.
      have hd : min (k + 1) a.size - (k + 1 - b.size) ≤ min a.size b.size := by lia
      have hcol := colSum_le a b k (k + 1 - b.size) (min (k + 1) a.size - (k + 1 - b.size))
      have hs := combaColLoop_spec a b k (min (k + 1) a.size) (Nat.min_le_right ..)
        (Nat.min_le_left ..) (k + 1 - b.size) (by lia) t₀ t₁ 0 (by
          simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
          generalize min (k + 1) a.size - (k + 1 - b.size) = d at *
          generalize min a.size b.size = N at *
          generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
          lia)
      simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at hs
      have hU := colUpTo_eq a b k a.size (Nat.le_refl _)
      rw [show min a.size (min (k + 1) a.size) = min (k + 1) a.size by lia] at hU
      have hR := rowsVal_succ a b k a.size
      have hlow : (r.set! (off + k) s.1).valAt off (k + 1) =
          r.valAt off k + 2 ^ (64 * k) * s.1.toNat := by
        rw [UInt64Array.valAt_add, UInt64Array.valAt_one,
          UInt64Array.getElem!_set!_self _ _ _ (by lia)]
        congr 1
        exact UInt64Array.valAt_congr _ fun i _ hi => UInt64Array.getElem!_set!_of_ne _ _ (by lia)
      refine ih₃ (by lia) ?_ ?_
      · rw [hlow, hR, hU, ← hv, Nat.mul_succ, Nat.pow_add]
        generalize colSum _ _ _ _ _ = col at *
        generalize s.1.toNat = s₀ at *
        generalize s.2.1.toNat = s₁ at *
        generalize s.2.2.toNat = s₂ at *
        generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
        generalize r.valAt off k = L at *
        generalize 2 ^ (64 * k) = P at *
        grind
      · generalize colSum _ _ _ _ _ = col at *
        generalize s.1.toNat = s₀ at *
        generalize s.2.1.toNat = s₁ at *
        generalize s.2.2.toNat = s₂ at *
        generalize min (k + 1) a.size - (k + 1 - b.size) = d at *
        generalize min a.size b.size = N at *
        generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
        lia
  | case2 r k t₀ t₁ h =>
    rw [combaLoop]
    simp only [h, ↓reduceIte]
    refine ⟨by simp, by simp, fun hk hv _ => ?_⟩
    have hk : k = a.size + b.size := by lia
    subst hk
    rw [rowsVal_full a b _ _ (by lia), ← UInt64Array.Slice.toNat_eq_valAt] at hv
    have hA := UInt64Array.valAt_lt a.array a.start a.size
    have hB := UInt64Array.valAt_lt b.array b.start b.size
    rw [← UInt64Array.Slice.toNat_eq_valAt] at hA hB
    have hAB : a.toNat * b.toNat < 2 ^ (64 * (a.size + b.size)) := by
      rw [Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt hA hB
    generalize t₀.toNat + 2 ^ 64 * t₁.toNat = T at *
    generalize a.toNat * b.toNat = AB at *
    generalize 2 ^ (64 * (a.size + b.size)) = P at *
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT; lia
    · have := Nat.le_mul_of_pos_right P hT
      lia

@[simp] public theorem size_mulComba (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (hr : off + a.size + b.size ≤ r.size) (hN : min a.size b.size < 2 ^ 62) :
    (mulComba r off a b).size = r.size :=
  (combaLoop_spec r off a b 0 0 0 hr hN).1

/-- `mulComba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulComba (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (hr : off + a.size + b.size ≤ r.size) (hN : min a.size b.size < 2 ^ 62) (i : Nat)
    (hi : i < off ∨ off + a.size + b.size ≤ i) :
    (mulComba r off a b)[i]! = r[i]! :=
  (combaLoop_spec r off a b 0 0 0 hr hN).2.1 i (by lia)

public theorem valAt_mulComba (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (hr : off + a.size + b.size ≤ r.size) (hN : min a.size b.size < 2 ^ 62) :
    (mulComba r off a b).valAt off (a.size + b.size) = a.toNat * b.toNat :=
  (combaLoop_spec r off a b 0 0 0 hr hN).2.2 (by lia) (by simp [rowsVal_zero]) (by simp)

end MPN
