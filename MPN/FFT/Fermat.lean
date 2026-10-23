/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.AddSub
public import MPN.NatMod

/-!
# Residues modulo `2^(64 n) + 1`

The FFT works modulo the Fermat number `F = 2^(64 n) + 1`, on residues of `n + 1` limbs whose
value is less than `F`, so that the top limb is `0` or `1`, and `1` only for `2^(64 n) ≡ -1`. They
are windows of one flat array: each function takes the array, `n` and the offsets of the windows
it reads and the one it writes, and returns the new array, through `foldUInPlace2`, so that the
array is never shared.

Since `2^(64 n) ≡ -1`, the value `L + 2^(64 n) H` of a window is `L - H` modulo `F`, which is how
the results are reduced: the top limb is subtracted from the others, and when that borrows, `1`
is added, by loops that stop as soon as the carry or the borrow is zero.
-/

open ScalarArray UInt64Array

namespace MPN.FFT

/-- The Fermat modulus `2^(64 n) + 1`. -/
@[expose] public def fermat (n : Nat) : Nat := 2 ^ (64 * n) + 1

/-! ## Increment and decrement -/

private theorem incr_step (x c : UInt64) :
    (x + c).toNat + 2 ^ 64 * (UInt64.addh 0 x c).toNat = x.toNat + c.toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_add, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  lia

private theorem decr_step (x c : UInt64) :
    (x - c).toNat + c.toNat = x.toNat + 2 ^ 64 * (UInt64.subh 0 x c).toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  rw [UInt64.toNat_sub, UInt64.toNat_subh, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  split <;> lia

/-- Adds `c` to limbs `o + j` to `o + len - 1` of `arr`, stopping as soon as the carry is zero. -/
public def incrAt (arr : UInt64Array) (o len : USize) (h : LoopBound arr o len) (j : USize)
    (c : UInt64) : UInt64Array × UInt64 :=
  if c = 0 then
    (arr, 0)
  else if hj : j < len then
    let x := arr.uget (o + j) (h.uset_bound hj)
    incrAt (arr.uset (o + j) (x + c) (h.uset_bound hj)) o len (h.of_uset ..) (j + 1)
      (UInt64.addh 0 x c)
  else
    (arr, c)
termination_by len.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 hj
  rw [USize.toNat_add_one_of_lt hj]
  lia

public theorem incrAt_spec (arr : UInt64Array) (o len : USize) (h : LoopBound arr o len)
    (j : USize) (c : UInt64) :
    (incrAt arr o len h j c).1.size = arr.size ∧
      (∀ i, (i < o.toNat + j.toNat ∨ o.toNat + len.toNat ≤ i) →
        (incrAt arr o len h j c).1[i]! = arr[i]!) ∧
      (incrAt arr o len h j c).1.valAt (o.toNat + j.toNat) (len.toNat - j.toNat) +
          2 ^ (64 * (len.toNat - j.toNat)) * (incrAt arr o len h j c).2.toNat =
        arr.valAt (o.toNat + j.toNat) (len.toNat - j.toNat) + c.toNat := by
  induction arr, h, j, c using incrAt.induct o len with
  | case1 arr h j =>
    rw [incrAt]
    simp
  | case2 arr h j c hc hj x ih =>
    rw [incrAt]
    simp only [hc, hj, ↓reduceIte, ↓reduceDIte]
    have hj' := USize.lt_iff_toNat_lt.1 hj
    have hj₁ := USize.toNat_add_one_of_lt hj
    have hidx := h.toNat_add hj
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (incrAt (arr.uset (o + j) (x + c) (h.uset_bound hj)) o len (h.of_uset ..) (j + 1)
        (UInt64.addh 0 x c)).1[o.toNat + j.toNat]! = x + c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (o + j) (x + c) (h.uset_bound hj)).valAt (o.toNat + (j.toNat + 1))
        (len.toNat - (j.toNat + 1)) =
          arr.valAt (o.toNat + (j.toNat + 1)) (len.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    have hx : x = arr[o.toNat + j.toNat]! := by
      show arr.uget (o + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, len.toNat - j.toNat = k + 1 := ⟨len.toNat - j.toNat - 1, by lia⟩
      rw [show len.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, valAt_succ, valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := incr_step x c
      generalize (incrAt _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (incrAt _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh 0 x c).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case3 arr h j c hc hj =>
    rw [incrAt]
    have : len.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := len); lia
    simp [hc, hj, this]

/--
Subtracts `c` from limbs `o + j` to `o + len - 1` of `arr`, stopping as soon as the borrow is
zero.
-/
public def decrAt (arr : UInt64Array) (o len : USize) (h : LoopBound arr o len) (j : USize)
    (c : UInt64) : UInt64Array × UInt64 :=
  if c = 0 then
    (arr, 0)
  else if hj : j < len then
    let x := arr.uget (o + j) (h.uset_bound hj)
    decrAt (arr.uset (o + j) (x - c) (h.uset_bound hj)) o len (h.of_uset ..) (j + 1)
      (UInt64.subh 0 x c)
  else
    (arr, c)
termination_by len.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 hj
  rw [USize.toNat_add_one_of_lt hj]
  lia

public theorem decrAt_spec (arr : UInt64Array) (o len : USize) (h : LoopBound arr o len)
    (j : USize) (c : UInt64) :
    (decrAt arr o len h j c).1.size = arr.size ∧
      (∀ i, (i < o.toNat + j.toNat ∨ o.toNat + len.toNat ≤ i) →
        (decrAt arr o len h j c).1[i]! = arr[i]!) ∧
      (decrAt arr o len h j c).1.valAt (o.toNat + j.toNat) (len.toNat - j.toNat) + c.toNat =
        arr.valAt (o.toNat + j.toNat) (len.toNat - j.toNat) +
          2 ^ (64 * (len.toNat - j.toNat)) * (decrAt arr o len h j c).2.toNat := by
  induction arr, h, j, c using decrAt.induct o len with
  | case1 arr h j =>
    rw [decrAt]
    simp
  | case2 arr h j c hc hj x ih =>
    rw [decrAt]
    simp only [hc, hj, ↓reduceIte, ↓reduceDIte]
    have hj' := USize.lt_iff_toNat_lt.1 hj
    have hj₁ := USize.toNat_add_one_of_lt hj
    have hidx := h.toNat_add hj
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv : (decrAt (arr.uset (o + j) (x - c) (h.uset_bound hj)) o len (h.of_uset ..) (j + 1)
        (UInt64.subh 0 x c)).1[o.toNat + j.toNat]! = x - c := by
      rw [ih₂ _ (.inl (by lia)), getElem!_uset]
      simp [hidx]
    have hr' : (arr.uset (o + j) (x - c) (h.uset_bound hj)).valAt (o.toNat + (j.toNat + 1))
        (len.toNat - (j.toNat + 1)) =
          arr.valAt (o.toNat + (j.toNat + 1)) (len.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    have hx : x = arr[o.toNat + j.toNat]! := by
      show arr.uget (o + j) _ = _
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, len.toNat - j.toNat = k + 1 := ⟨len.toNat - j.toNat - 1, by lia⟩
      rw [show len.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, valAt_succ, valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := decr_step x c
      generalize (decrAt _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (decrAt _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh 0 x c).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case3 arr h j c hc hj =>
    rw [decrAt]
    have : len.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := len); lia
    simp [hc, hj, this]

/-! ## Windows and steps -/

/-- A window of `n + 1` limbs of `arr` at `o`; the indices of `arr` do not overflow. -/
public abbrev Win (arr : UInt64Array) (n o : USize) : Prop :=
  o.toNat + n.toNat + 1 ≤ arr.size ∧ arr.size < USize.size

public theorem Win.of_size {arr arr' : UInt64Array} {n o : USize} (h : Win arr n o)
    (e : arr'.size = arr.size) : Win arr' n o := by
  simp only [Win, e]; exact h

public theorem Win.succ {arr : UInt64Array} {n o : USize} (h : Win arr n o) :
    (n + 1).toNat = n.toNat + 1 := by
  rw [USize.toNat_add_of_lt (by rw [USize.toNat_one]; lia), USize.toNat_one]

public theorem Win.add {arr : UInt64Array} {n o : USize} (h : Win arr n o) {k : USize}
    (hk : k.toNat ≤ n.toNat) : (o + k).toNat = o.toNat + k.toNat :=
  USize.toNat_add_of_lt (by lia)

/-- Limbs `o` to `o + m - 1` of the window, as a loop bound. -/
public theorem Win.lb {arr : UInt64Array} {n o : USize} (h : Win arr n o) {m : USize}
    (hm : m.toNat ≤ n.toNat + 1) : LoopBound arr o m := by
  constructor <;> lia

/-- Limbs `o + k` to `o + k + m - 1` of the window, as a loop bound. -/
public theorem Win.lbAt {arr : UInt64Array} {n o : USize} (h : Win arr n o) {k m : USize}
    (hk : k.toNat ≤ n.toNat) (hm : k.toNat + m.toNat ≤ n.toNat + 1) : LoopBound arr (o + k) m := by
  have := h.add hk
  constructor <;> lia

/-- The value of a window: its low `n` limbs and its top limb. -/
public theorem valAt_top (a : UInt64Array) (o n : Nat) :
    a.valAt o (n + 1) = a.valAt o n + 2 ^ (64 * n) * a[o + n]!.toNat := by
  rw [UInt64Array.valAt_add, UInt64Array.valAt_one]

private theorem mod_of_eq {R v q F : Nat} (h : R + F * q = v) (hR : R < F) : v % F = R := by
  subst h; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

private theorem two_pow_le (n : Nat) (hn : 1 ≤ n) : 2 ^ 64 ≤ 2 ^ (64 * n) :=
  Nat.pow_le_pow_right (by decide) (by lia)

/-- `x + y` with a carry. -/
@[inline] private def addStep (N : USize) (j : USize) (_ : j < N) (x y c : UInt64) :
    UInt64 × UInt64 :=
  (x + y + c, UInt64.addh (UInt64.addh 0 x y) (x + y) c)

/-- `x - y` with a borrow. -/
@[inline] private def subStep (N : USize) (j : USize) (_ : j < N) (x y c : UInt64) :
    UInt64 × UInt64 :=
  (x - y - c, UInt64.subh (UInt64.subh 0 x y) (x - y) c)

private theorem addStep_law (N : USize) : ∀ j h x y c, True →
    (addStep N j h x y c).1.toNat + 2 ^ 64 * UInt64.toNat (addStep N j h x y c).2 + 0 * x.toNat +
      0 * y.toNat + (fun _ => 0) c = 1 * x.toNat + 1 * y.toNat +
      2 ^ 64 * (fun _ => 0) (addStep N j h x y c).2 + UInt64.toNat c := by
  intro j h x y c _
  have := add_step x y c
  simp only [addStep]
  lia

private theorem subStep_law (N : USize) : ∀ j h x y c, True →
    (subStep N j h x y c).1.toNat + 2 ^ 64 * (fun _ => 0) (subStep N j h x y c).2 + 0 * x.toNat +
      1 * y.toNat + UInt64.toNat c = 1 * x.toNat + 0 * y.toNat +
      2 ^ 64 * UInt64.toNat (subStep N j h x y c).2 + (fun _ => 0) c := by
  intro j h x y c _
  have := sub_step x y c
  simp only [subStep]
  lia

/-- `-y` with a borrow. -/
@[inline] private def negStep (N : USize) (j : USize) (_ : j < N) (_ y c : UInt64) :
    UInt64 × UInt64 :=
  (0 - y - c, UInt64.subh (UInt64.subh 0 0 y) (0 - y) c)

/-- `x` minus a borrow. -/
@[inline] private def decStep (N : USize) (j : USize) (_ : j < N) (x _ c : UInt64) :
    UInt64 × UInt64 :=
  (x - c, UInt64.subh 0 x c)

/-- `x 2ᵇ`, for `0 < b < 64`, with the high bits of the previous limb. -/
@[inline] private def shlStep (N : USize) (b : UInt64) (j : USize) (_ : j < N) (x _ c : UInt64) :
    UInt64 × UInt64 :=
  ((x <<< b) + c, x >>> (64 - b))

private theorem negStep_law (N : USize) : ∀ j h x y c, True →
    (negStep N j h x y c).1.toNat + 2 ^ 64 * (fun _ => 0) (negStep N j h x y c).2 + 0 * x.toNat +
      1 * y.toNat + UInt64.toNat c = 0 * x.toNat + 0 * y.toNat +
      2 ^ 64 * UInt64.toNat (negStep N j h x y c).2 + (fun _ => 0) c := by
  intro j h x y c _
  have := sub_step 0 y c
  simp only [negStep, UInt64.toNat_zero] at this ⊢
  lia

private theorem decStep_law (N : USize) : ∀ j h x y c, True →
    (decStep N j h x y c).1.toNat + 2 ^ 64 * (fun _ => 0) (decStep N j h x y c).2 + 0 * x.toNat +
      0 * y.toNat + UInt64.toNat c = 1 * x.toNat + 0 * y.toNat +
      2 ^ 64 * UInt64.toNat (decStep N j h x y c).2 + (fun _ => 0) c := by
  intro j h x y c _
  have := decr_step x c
  simp only [decStep]
  lia

private theorem shl_step (x c b : UInt64) (hb₀ : 0 < b.toNat) (hb : b.toNat < 64)
    (hc : c.toNat < 2 ^ b.toNat) :
    ((x <<< b) + c).toNat + 2 ^ 64 * (x >>> (64 - b)).toNat = 2 ^ b.toNat * x.toNat + c.toNat ∧
      (x >>> (64 - b)).toNat < 2 ^ b.toNat := by
  have h64b : (64 - b).toNat = 64 - b.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia))]; rfl
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, h64b,
    Nat.mod_eq_of_lt (show b.toNat < 64 from hb), Nat.mod_eq_of_lt (show 64 - b.toNat < 64 by lia),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hPQ : 2 ^ (64 - b.toNat) * 2 ^ b.toNat = 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; lia
  have hx := x.toNat_lt
  have hQ : 0 < 2 ^ (64 - b.toNat) := Nat.two_pow_pos _
  have hdm := Nat.div_add_mod x.toNat (2 ^ (64 - b.toNat))
  have hr := Nat.mod_lt x.toNat hQ
  generalize x.toNat / 2 ^ (64 - b.toNat) = q at *
  generalize x.toNat % 2 ^ (64 - b.toNat) = r at *
  generalize 2 ^ (64 - b.toNat) = Q at *
  generalize 2 ^ b.toNat = P at *
  generalize x.toNat = X at *
  subst hdm
  have hrP : (r + 1) * P ≤ Q * P := Nat.mul_le_mul_right P hr
  have hq : q < P := by
    rcases Nat.lt_or_ge q P with e | e
    · exact e
    · have := Nat.mul_le_mul_left Q e; lia
  have e₁ : (Q * q + r) * P = 2 ^ 64 * q + r * P := by rw [← hPQ]; grind
  rw [e₁, Nat.add_comm (2 ^ 64 * q), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (show r * P < 2 ^ 64 by grind),
    Nat.mod_eq_of_lt (show r * P + c.toNat < 2 ^ 64 by grind)]
  refine ⟨by grind, hq⟩

private theorem shlStep_law (N : USize) (b : UInt64) (hb₀ : 0 < b.toNat) (hb : b.toNat < 64) :
    ∀ j h x y c, (fun c => c.toNat < 2 ^ b.toNat) c →
    (shlStep N b j h x y c).1.toNat + 2 ^ 64 * UInt64.toNat (shlStep N b j h x y c).2 +
      0 * x.toNat + 0 * y.toNat + (fun _ => 0) c = 2 ^ b.toNat * x.toNat + 0 * y.toNat +
      2 ^ 64 * (fun _ => 0) (shlStep N b j h x y c).2 + UInt64.toNat c := by
  intro j h x y c hc
  have := (shl_step x c b hb₀ hb hc).1
  simp only [shlStep]
  lia

private theorem shlStep_inv (N : USize) (b : UInt64) (hb₀ : 0 < b.toNat) (hb : b.toNat < 64) :
    ∀ j h x y c, (fun c => c.toNat < 2 ^ b.toNat) c →
      (fun c => c.toNat < 2 ^ b.toNat) (shlStep N b j h x y c).2 :=
  fun _ _ x _ c hc => (shl_step x c b hb₀ hb hc).2

/-! ## Reduction -/

/--
Reduces the window of `n + 1` limbs at `o` modulo `2^(64 n) + 1`: subtracts its top limb from
the others, and adds `1` back when that borrows.
-/
public def normAt (arr : UInt64Array) (n o : USize) (h : Win arr n o) : UInt64Array :=
  let H := arr.uget (o + n) (by rw [h.add (Nat.le_refl _)]; lia)
  let a := arr.uset (o + n) 0 (by rw [h.add (Nat.le_refl _)]; lia)
  let p := decrAt a o n ((h.of_size (size_uset ..)).lb (by lia)) 0 H
  if p.2 = 0 then p.1
  else (incrAt p.1 o (n + 1) (((h.of_size (size_uset ..)).of_size (decrAt_spec ..).1).lb
    (by rw [h.succ]; exact Nat.le_refl _)) 0 1).1

public theorem normAt_spec (arr : UInt64Array) (n o : USize) (h : Win arr n o)
    (hn : 1 ≤ n.toNat) :
    (normAt arr n o h).size = arr.size ∧
      (∀ i, (i < o.toNat ∨ o.toNat + n.toNat + 1 ≤ i) → (normAt arr n o h)[i]! = arr[i]!) ∧
      (normAt arr n o h).valAt o.toNat (n.toNat + 1) =
        arr.valAt o.toNat (n.toNat + 1) % fermat n.toNat := by
  have hon := h.add (Nat.le_refl _)
  have hidx : (o + n).toNat < arr.size := by rw [hon]; lia
  have hH : arr.uget (o + n) hidx = arr[o.toNat + n.toNat]! := by rw [uget_eq_getElem!, hon]
  have ha₁ : (arr.uset (o + n) 0 hidx).valAt o.toNat n.toNat = arr.valAt o.toNat n.toNat :=
    valAt_uset_of _ _ _ _ _ _ (by rw [hon]; lia)
  have ha₂ : ∀ i, i ≠ o.toNat + n.toNat → (arr.uset (o + n) 0 hidx)[i]! = arr[i]! := by
    intro i hi; rw [getElem!_uset]; simp only [hon]; split <;> lia
  have ha₃ : (arr.uset (o + n) 0 hidx)[o.toNat + n.toNat]! = 0 := by
    rw [getElem!_uset]; simp [hon]
  dsimp only [normAt]
  have hlb : LoopBound (arr.uset (o + n) 0 hidx) o n := (h.of_size (size_uset ..)).lb (by lia)
  obtain ⟨d₁, d₂, d₃⟩ := decrAt_spec (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, size_uset] at d₁ d₂ d₃
  rw [ha₁] at d₃
  have dtop := d₂ (o.toNat + n.toNat) (.inr (Nat.le_refl _))
  rw [ha₃] at dtop
  have hv := valAt_top arr o.toNat n.toNat
  rw [← hH] at hv
  have hD := valAt_lt (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).1
    o.toNat n.toNat
  have hL := valAt_lt arr o.toNat n.toNat
  have hHl := (arr.uget (o + n) hidx).toNat_lt
  have h64 := two_pow_le n.toNat hn
  have hB : 2 ^ (64 * (n.toNat + 1)) = 2 ^ (64 * n.toNat) * 2 ^ 64 := by
    rw [Nat.mul_succ, Nat.pow_add]
  have hc : (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).2.toNat < 2 := by
    rcases Nat.lt_or_ge (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0
      (arr.uget (o + n) hidx)).2.toNat 2 with hc | hc
    · exact hc
    · have := Nat.mul_le_mul_left (2 ^ (64 * n.toNat)) hc; lia
  simp only [fermat]
  split
  · rename_i hc0
    refine ⟨d₁, fun i hi => ?_, ?_⟩
    · rw [d₂ i (by lia), ha₂ i (by lia)]
    · rw [valAt_top, dtop, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
      rw [hc0, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at d₃
      generalize (decrAt _ _ _ _ _ _).1.valAt _ _ = D at *
      generalize 2 ^ (64 * n.toNat) = Bn at *
      generalize (arr.uget (o + n) hidx).toNat = H at *
      generalize arr.valAt o.toNat n.toNat = L at *
      exact (mod_of_eq (q := H) (by rw [hv]; grind) (by lia)).symm
  · rename_i hc0
    have hc1 :
        (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).2.toNat = 1 := by
      have : (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).2.toNat ≠ 0 :=
        fun e => hc0 (UInt64.toNat_inj.1 (by rw [e]; rfl))
      lia
    rw [hc1] at d₃
    have hlb' : LoopBound (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).1 o
        (n + 1) := (h.of_size d₁).lb (by rw [h.succ]; exact Nat.le_refl _)
    obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0
      (arr.uget (o + n) hidx)).1 o (n + 1) hlb' 0 1
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, h.succ, UInt64.toNat_one] at i₁ i₂ i₃
    rw [valAt_top (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).1 o.toNat
      n.toNat, dtop, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at i₃
    generalize incrAt (decrAt (arr.uset (o + n) 0 hidx) o n hlb 0 (arr.uget (o + n) hidx)).1 o
      (n + 1) hlb' 0 1 = q at *
    have hq := valAt_lt q.1 o.toNat (n.toNat + 1)
    refine ⟨i₁.trans d₁, fun i hi => ?_, ?_⟩
    · rw [i₂ i (by lia), d₂ i (by lia), ha₂ i (by lia)]
    · rw [hB] at i₃ hq
      generalize (decrAt _ _ _ _ _ _).1.valAt _ _ = D at *
      generalize 2 ^ (64 * n.toNat) = Bn at *
      generalize (arr.uget (o + n) hidx).toNat = H at *
      generalize arr.valAt o.toNat n.toNat = L at *
      have hc' : q.2.toNat = 0 := by
        rcases Nat.eq_zero_or_pos q.2.toNat with e | e
        · exact e
        · have := Nat.mul_le_mul_left (Bn * 2 ^ 64) e; lia
      rw [hc', Nat.mul_zero, Nat.add_zero] at i₃
      rw [hv]
      obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by lia⟩
      exact (mod_of_eq (q := H') (by grind) (by lia)).symm

/-! ## Addition and subtraction -/

/--
Writes `(x + y) % F` into the window at `d`, for residues `x` and `y` in the windows at `x` and
`y`, which may be the window at `d`.
-/
public def addModAt (arr : UInt64Array) (n d x y : USize) (hd : Win arr n d) (hx : Win arr n x)
    (hy : Win arr n y) : UInt64Array :=
  foldUInPlace2Then (n + 1) (addStep (n + 1)) arr d x y
    (hd.lb (by rw [hd.succ]; exact Nat.le_refl _)) (hx.lb (by rw [hx.succ]; exact Nat.le_refl _))
    (hy.lb (by rw [hy.succ]; exact Nat.le_refl _)) 0 0 fun a ha _ => normAt a n d (hd.of_size ha)

public theorem addModAt_spec (arr : UInt64Array) (n d x y : USize) (hd : Win arr n d)
    (hx : Win arr n x) (hy : Win arr n y) (hn : 1 ≤ n.toNat)
    (hdx : d.toNat ≤ x.toNat ∨ x.toNat + n.toNat + 1 ≤ d.toNat)
    (hdy : d.toNat ≤ y.toNat ∨ y.toNat + n.toNat + 1 ≤ d.toNat)
    (hX : arr.valAt x.toNat (n.toNat + 1) < fermat n.toNat)
    (hY : arr.valAt y.toNat (n.toNat + 1) < fermat n.toNat) :
    (addModAt arr n d x y hd hx hy).size = arr.size ∧
      (∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
        (addModAt arr n d x y hd hx hy)[i]! = arr[i]!) ∧
      (addModAt arr n d x y hd hx hy).valAt d.toNat (n.toNat + 1) =
        (arr.valAt x.toNat (n.toNat + 1) + arr.valAt y.toNat (n.toNat + 1)) % fermat n.toNat := by
  rw [addModAt, foldUInPlace2Then_eq]
  have hs := hd.succ
  have hlb := hd.lb (by rw [hd.succ]; exact Nat.le_refl _)
  have hlx := hx.lb (by rw [hx.succ]; exact Nat.le_refl _)
  have hly := hy.lb (by rw [hy.succ]; exact Nat.le_refl _)
  obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace2_spec (n + 1) (addStep (n + 1)) UInt64.toNat (fun _ => 0)
    0 0 1 1 (fun _ => True) (fun _ _ _ _ _ _ => trivial) (addStep_law _) arr d x y hlb hlx hly
    (by rw [hs]; lia) (by rw [hs]; lia) 0 0 trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, Nat.zero_mul, Nat.mul_zero,
    Nat.one_mul, UInt64.toNat_zero] at f₂ f₃
  obtain ⟨n₁, n₂, n₃⟩ := normAt_spec _ n d (hd.of_size (size_foldUInPlace2 ..)) hn
  refine ⟨n₁.trans f₁, fun i hi => by rw [n₂ i hi, f₂ i (by lia)], ?_⟩
  rw [n₃]
  have hB : 2 ^ (64 * (n.toNat + 1)) = 2 ^ (64 * n.toNat) * 2 ^ 64 := by
    rw [Nat.mul_succ, Nat.pow_add]
  have h64 := two_pow_le n.toNat hn
  have hS := valAt_lt (foldUInPlace2 (n + 1) (addStep (n + 1)) arr d x y hlb hlx hly 0 0).1
    d.toNat (n.toNat + 1)
  rw [hB] at f₃ hS
  simp only [fermat] at hX hY ⊢
  generalize (foldUInPlace2 (n + 1) (addStep (n + 1)) arr d x y hlb hlx hly 0 0).1.valAt _ _ =
    S at *
  generalize (foldUInPlace2 (n + 1) (addStep (n + 1)) arr d x y hlb hlx hly 0 0).2.toNat = c at *
  generalize 2 ^ (64 * n.toNat) = Bn at *
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with e | e
    · exact e
    · have := Nat.mul_le_mul_left (Bn * 2 ^ 64) e; lia
  subst hc
  rw [Nat.mul_zero, Nat.add_zero] at f₃
  rw [f₃]

/--
Writes `(x - y) % F` into the window at `d`, for residues `x` and `y` in the windows at `x` and
`y`, which may be the window at `d`. When `x - y` borrows, its top limb is all ones, and the
residue is its other limbs plus `1`.
-/
public def subModAt (arr : UInt64Array) (n d x y : USize) (hd : Win arr n d) (hx : Win arr n x)
    (hy : Win arr n y) : UInt64Array :=
  foldUInPlace2Then (n + 1) (subStep (n + 1)) arr d x y
    (hd.lb (by rw [hd.succ]; exact Nat.le_refl _)) (hx.lb (by rw [hx.succ]; exact Nat.le_refl _))
    (hy.lb (by rw [hy.succ]; exact Nat.le_refl _)) 0 0 fun a ha c =>
      if c = 0 then a
      else
        have hd' := hd.of_size ha
        (incrAt (a.uset (d + n) 0 (by rw [hd'.add (Nat.le_refl _)]; lia)) d (n + 1)
          ((hd'.of_size (size_uset ..)).lb (by rw [hd.succ]; exact Nat.le_refl _)) 0 1).1

public theorem subModAt_spec (arr : UInt64Array) (n d x y : USize) (hd : Win arr n d)
    (hx : Win arr n x) (hy : Win arr n y) (hn : 1 ≤ n.toNat)
    (hdx : d.toNat ≤ x.toNat ∨ x.toNat + n.toNat + 1 ≤ d.toNat)
    (hdy : d.toNat ≤ y.toNat ∨ y.toNat + n.toNat + 1 ≤ d.toNat)
    (hX : arr.valAt x.toNat (n.toNat + 1) < fermat n.toNat)
    (hY : arr.valAt y.toNat (n.toNat + 1) < fermat n.toNat) :
    (subModAt arr n d x y hd hx hy).size = arr.size ∧
      (∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
        (subModAt arr n d x y hd hx hy)[i]! = arr[i]!) ∧
      (subModAt arr n d x y hd hx hy).valAt d.toNat (n.toNat + 1) =
        (arr.valAt x.toNat (n.toNat + 1) + fermat n.toNat - arr.valAt y.toNat (n.toNat + 1)) %
          fermat n.toNat := by
  rw [subModAt, foldUInPlace2Then_eq]
  have hs := hd.succ
  have hlb := hd.lb (by rw [hd.succ]; exact Nat.le_refl _)
  have hlx := hx.lb (by rw [hx.succ]; exact Nat.le_refl _)
  have hly := hy.lb (by rw [hy.succ]; exact Nat.le_refl _)
  obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace2_spec (n + 1) (subStep (n + 1)) (fun _ => 0) UInt64.toNat
    0 1 1 0 (fun _ => True) (fun _ _ _ _ _ _ => trivial) (subStep_law _) arr d x y hlb hlx hly
    (by rw [hs]; lia) (by rw [hs]; lia) 0 0 trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, Nat.zero_mul, Nat.mul_zero,
    Nat.one_mul, UInt64.toNat_zero] at f₂ f₃
  have hB : 2 ^ (64 * (n.toNat + 1)) = 2 ^ (64 * n.toNat) * 2 ^ 64 := by
    rw [Nat.mul_succ, Nat.pow_add]
  have h64 := two_pow_le n.toNat hn
  have hS := valAt_lt (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0 0).1
    d.toNat (n.toNat + 1)
  rw [hB] at f₃ hS
  simp only [fermat] at hX hY ⊢
  have hc : (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0 0).2.toNat < 2 := by
    rcases Nat.lt_or_ge (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0
      0).2.toNat 2 with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (64 * n.toNat) * 2 ^ 64) e; lia
  split
  · rename_i hc0
    refine ⟨f₁, fun i hi => f₂ i (by lia), ?_⟩
    rw [hc0, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at f₃
    generalize (foldUInPlace2 _ _ _ _ _ _ _ _ _ _ _).1.valAt _ _ = S at *
    generalize 2 ^ (64 * n.toNat) = Bn at *
    exact (mod_of_eq (q := 1) (by lia) (by lia)).symm
  · rename_i hc0
    have hc1 : (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0 0).2.toNat = 1 := by
      have : (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0 0).2.toNat ≠ 0 :=
        fun e => hc0 (UInt64.toNat_inj.1 (by rw [e]; rfl))
      lia
    rw [hc1, Nat.mul_one] at f₃
    have hd' := hd.of_size f₁
    have hon := hd'.add (Nat.le_refl _)
    have hidx : (d + n).toNat < (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0
        0).1.size := by rw [hon]; lia
    have hlb' : LoopBound ((foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0
        0).1.uset (d + n) 0 hidx) d (n + 1) :=
      (hd'.of_size (size_uset ..)).lb (by rw [hd.succ]; exact Nat.le_refl _)
    obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec _ d (n + 1) hlb' 0 1
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, UInt64.toNat_one] at i₁ i₂ i₃
    have hv := valAt_top (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0 0).1
      d.toNat n.toNat
    have hv' := valAt_top ((foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0
        0).1.uset (d + n) 0 hidx) d.toNat n.toNat
    rw [valAt_uset_of _ (d + n) 0 hidx d.toNat n.toNat (by rw [hon]; lia), getElem!_uset] at hv'
    simp only [hon, ↓reduceIte, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at hv'
    rw [hv'] at i₃
    generalize incrAt _ d (n + 1) hlb' 0 1 = q at *
    have hq := valAt_lt q.1 d.toNat (n.toNat + 1)
    refine ⟨i₁.trans (size_uset ..) |>.trans f₁, fun i hi => ?_, ?_⟩
    · rw [i₂ i (by lia), getElem!_uset, ite_eq_right_iff.2 (fun e => by rw [hon] at e; lia),
        f₂ i (by lia)]
    · rw [hB] at hq i₃
      have hL := valAt_lt (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0 0).1
        d.toNat n.toNat
      have ht := (foldUInPlace2 (n + 1) (subStep (n + 1)) arr d x y hlb hlx hly 0
        0).1[d.toNat + n.toNat]!.toNat_lt
      generalize (foldUInPlace2 _ _ _ _ _ _ _ _ _ _ _).1.valAt d.toNat (n.toNat + 1) = S at *
      generalize (foldUInPlace2 _ _ _ _ _ _ _ _ _ _ _).1.valAt d.toNat n.toNat = L at *
      generalize (foldUInPlace2 _ _ _ _ _ _ _ _ _ _ _).1[d.toNat + n.toNat]!.toNat = t at *
      generalize 2 ^ (64 * n.toNat) = Bn at *
      have htop : t = 2 ^ 64 - 1 := by
        rcases Nat.lt_or_ge t (2 ^ 64 - 1) with e | e
        · have := Nat.mul_le_mul_left Bn (show t ≤ 2 ^ 64 - 2 by lia); lia
        · lia
      subst htop
      have hc' : q.2.toNat = 0 := by
        rcases Nat.eq_zero_or_pos q.2.toNat with e | e
        · exact e
        · have := Nat.mul_le_mul_left (Bn * 2 ^ 64) e; lia
      rw [hc', Nat.mul_zero, Nat.add_zero] at i₃
      rw [Nat.mod_eq_of_lt (by lia)]
      lia

/-! ## Multiplication by a power of two -/

private theorem mod_of_eq' {R v q c F : Nat} (h : R + F * q = v + F * c) (hR : R < F) :
    v % F = R := by
  have := congrArg (· % F) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR] at this
  exact this.symm

/-- The value of the two passes of `mulPow2At`. -/
private theorem rot_value {V₁ V₂ Thi Tlo tn c₁ c₂ Pw Pr : Nat} (h₁ : V₁ + Thi = Pw * c₁)
    (h₂ : V₂ + (c₁ + tn) = Tlo + Pr * c₂) :
    V₁ + Pw * V₂ + c₂ + (Pw * Pr + 1) * (Thi + tn * Pw) =
      (Tlo + Pr * Thi + Pw * Pr * tn) * Pw + (Pw * Pr + 1) * c₂ := by
  have := congrArg (Pw * ·) h₂
  grind


private theorem toNat_64 : (64 : USize).toNat = 64 := by
  rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by cases USize.size_eq <;> simp_all [USize.size])]

/--
Writes `t 2ᵉ % F` into the window at `d`, for a residue `t` in the window at `t`, disjoint from
it, and `e < 64 n`. With `e = 64 w + b`, the limbs of `t` above `n - w` wrap around negated, since
`2^(64 n) ≡ -1`: they are subtracted from zero into the low `w` limbs, the others are copied above
them less the borrow and the top limb of `t`, and `1` is added when that borrows. The shift by
`b` bits, when `b ≠ 0`, follows in place, then a reduction.
-/
public def mulPow2At (arr : UInt64Array) (n d t e : USize) (hd : Win arr n d) (ht : Win arr n t)
    (he : e.toNat < 64 * n.toNat) : UInt64Array :=
  have hw : (e / 64).toNat < n.toNat := by rw [USize.toNat_div, toNat_64]; lia
  have hnw : (n - e / 64).toNat = n.toNat - (e / 64).toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
  have htw : (t + (n - e / 64)).toNat = t.toNat + (n.toNat - (e / 64).toNat) := by
    rw [← hnw]; exact ht.add (by rw [hnw]; lia)
  have hlw : LoopBound arr (t + (n - e / 64)) (e / 64) := ⟨by rw [htw]; lia, by rw [htw]; lia⟩
  foldUInPlace2Then (e / 64) (negStep (e / 64)) arr d (t + (n - e / 64)) (t + (n - e / 64))
    (hd.lb (by lia)) hlw hlw 0 0 fun a₁ h₁ c₁ =>
  have hlt : LoopBound a₁ t (n - e / 64) := (ht.of_size h₁).lb (by rw [hnw]; lia)
  foldUInPlace2Then (n - e / 64) (decStep (n - e / 64)) a₁ (d + e / 64) t t
    ((hd.of_size h₁).lbAt (by lia) (by rw [hnw]; lia)) hlt hlt 0
    (c₁ + a₁.uget (t + n) (by rw [(ht.of_size h₁).add (Nat.le_refl _), h₁]; lia)) fun a₂ h₂ c₂ =>
  have hd₂ := hd.of_size (h₂.trans h₁)
  have hd₃ : Win (a₂.uset (d + n) 0 (by rw [hd₂.add (Nat.le_refl _)]; lia)) n d :=
    hd₂.of_size (size_uset ..)
  have hl₃ := hd₃.lb (by rw [hd.succ]; exact Nat.le_refl _)
  have hd₄ := hd₃.of_size (incrAt_spec _ d (n + 1) hl₃ 0 c₂).1
  if e % 64 = 0 then
    (incrAt (a₂.uset (d + n) 0 _) d (n + 1) hl₃ 0 c₂).1
  else
    have hl₄ := hd₄.lb (by rw [hd.succ]; exact Nat.le_refl _)
    foldUInPlace2Then (n + 1) (shlStep (n + 1) (e % 64).toUInt64)
      (incrAt (a₂.uset (d + n) 0 _) d (n + 1) hl₃ 0 c₂).1 d d d hl₄ hl₄ hl₄ 0 0
      fun a₅ h₅ _ => normAt a₅ n d (hd₄.of_size h₅)

/-- The residue of `mulPow2At` before the shift, from the values of its passes. -/
private theorem rot_res {V₁ V₂ Thi Tlo tn c₁ c₂ I c Pw Pr : Nat} (h₁ : V₁ + Thi = Pw * c₁)
    (h₂ : V₂ + (c₁ + tn) = Tlo + Pr * c₂) (hi : I + Pw * Pr * 2 ^ 64 * c = V₁ + Pw * V₂ + c₂)
    (hV₁ : V₁ < Pw) (hV₂ : V₂ < Pr) (htn : tn ≤ 1) (hc₁ : c₁ ≤ 1) (hPr : 2 ^ 64 ≤ Pr) :
    I < Pw * Pr + 1 ∧ I ≤ Pw * Pr ∧ (Tlo + Pr * Thi + Pw * Pr * tn) * Pw % (Pw * Pr + 1) = I := by
  have hc₂ : c₂ ≤ 1 := by
    rcases Nat.lt_or_ge c₂ 2 with h | h
    · lia
    · have := Nat.mul_le_mul_left Pr h; lia
  have hst : V₁ + Pw * V₂ + 1 ≤ Pw * Pr := by
    have := Nat.mul_le_mul_left Pw (show V₂ + 1 ≤ Pr by lia)
    rw [Nat.mul_add, Nat.mul_one] at this
    lia
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · have := Nat.mul_le_mul_left (Pw * Pr * 2 ^ 64) h
      have : Pw * Pr ≤ Pw * Pr * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      lia
  subst hc
  rw [Nat.mul_zero, Nat.add_zero] at hi
  have hI : I ≤ Pw * Pr := by
    rcases Nat.lt_or_ge c₂ 1 with h | h
    · lia
    · rcases Nat.lt_or_ge (V₁ + Pw * V₂) (Pw * Pr) with h' | h'
      · lia
      · lia
  refine ⟨by lia, hI, mod_of_eq' (q := Thi + tn * Pw) (c := c₂) ?_ (by lia)⟩
  rw [hi]
  exact rot_value h₁ h₂

public theorem mulPow2At_spec (arr : UInt64Array) (n d t e : USize) (hd : Win arr n d)
    (ht : Win arr n t) (he : e.toNat < 64 * n.toNat) (hn : 1 ≤ n.toNat)
    (hdt : d.toNat + n.toNat + 1 ≤ t.toNat ∨ t.toNat + n.toNat + 1 ≤ d.toNat)
    (hT : arr.valAt t.toNat (n.toNat + 1) < fermat n.toNat) :
    (mulPow2At arr n d t e hd ht he).size = arr.size ∧
      (∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
        (mulPow2At arr n d t e hd ht he)[i]! = arr[i]!) ∧
      (mulPow2At arr n d t e hd ht he).valAt d.toNat (n.toNat + 1) =
        arr.valAt t.toNat (n.toNat + 1) * 2 ^ e.toNat % fermat n.toNat := by
  have hw : (e / 64).toNat < n.toNat := by rw [USize.toNat_div, toNat_64]; lia
  have hnw : (n - e / 64).toNat = n.toNat - (e / 64).toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
  have htw : (t + (n - e / 64)).toNat = t.toNat + (n.toNat - (e / 64).toNat) := by
    rw [← hnw]; exact ht.add (by rw [hnw]; lia)
  have hdw := hd.add (k := e / 64) (by lia)
  have hlw : LoopBound arr (t + (n - e / 64)) (e / 64) := ⟨by rw [htw]; lia, by rw [htw]; lia⟩
  have hs := hd.succ
  have htn := ht.add (Nat.le_refl _)
  generalize hR : mulPow2At arr n d t e hd ht he = R
  rw [mulPow2At] at hR
  -- The negated limbs.
  obtain ⟨a₁, h₁, c₁, e₁, hR₁⟩ := foldUInPlace2Then_cases hR
  clear hR
  have P₁ := foldUInPlace2_spec (e / 64) (negStep (e / 64)) (fun _ => 0) UInt64.toNat 0 1 0 0
    (fun _ => True) (fun _ _ _ _ _ _ => trivial) (negStep_law _) arr d (t + (n - e / 64))
    (t + (n - e / 64)) (hd.lb (by lia)) hlw hlw (by rw [htw]; lia) (by rw [htw]; lia) 0 0 trivial
  rw [e₁] at P₁
  obtain ⟨-, -, p₁u, p₁v⟩ := P₁
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, htw, Nat.zero_mul, Nat.one_mul,
    Nat.mul_zero, Nat.zero_add, UInt64.toNat_zero] at p₁u p₁v
  -- The other limbs, less the borrow and the top limb.
  obtain ⟨a₂, h₂, c₂, e₂, hR⟩ := foldUInPlace2Then_cases hR₁
  clear hR₁
  have P₂ := foldUInPlace2_spec (n - e / 64) (decStep (n - e / 64)) (fun _ => 0) UInt64.toNat
    0 0 1 0 (fun _ => True) (fun _ _ _ _ _ _ => trivial) (decStep_law _) a₁ (d + e / 64) t t
    ((hd.of_size h₁).lbAt (by lia) (by rw [hnw]; lia)) ((ht.of_size h₁).lb (by rw [hnw]; lia))
    ((ht.of_size h₁).lb (by rw [hnw]; lia)) (by rw [hdw, hnw]; lia) (by rw [hdw, hnw]; lia) 0
    (c₁ + a₁.uget (t + n) (by rw [htn, h₁]; lia)) trivial
  rw [e₂] at P₂
  obtain ⟨-, -, p₂u, p₂v⟩ := P₂
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hdw, hnw, Nat.zero_mul, Nat.one_mul,
    Nat.mul_zero] at p₂u p₂v
  -- The values, as `Nat`s.
  have hidx : (d + n).toNat < a₂.size := by rw [h₂, h₁, hd.add (Nat.le_refl _)]; lia
  have hdn := hd.add (Nat.le_refl _)
  have htv : (a₁.uget (t + n) (by rw [htn, h₁]; lia)).toNat = arr[t.toNat + n.toNat]!.toNat := by
    rw [uget_eq_getElem!, htn, p₁u _ (by lia)]
  have hTv : arr.valAt t.toNat (n.toNat + 1) = arr.valAt t.toNat (n.toNat - (e / 64).toNat) +
      2 ^ (64 * (n.toNat - (e / 64).toNat)) *
        arr.valAt (t.toNat + (n.toNat - (e / 64).toNat)) (e / 64).toNat +
      2 ^ (64 * (e / 64).toNat) * 2 ^ (64 * (n.toNat - (e / 64).toNat)) *
        arr[t.toNat + n.toNat]!.toNat := by
    rw [valAt_top, ← Nat.pow_add, ← Nat.mul_add, show (e / 64).toNat + (n.toNat - (e / 64).toNat) =
      n.toNat by lia, show n.toNat = (n.toNat - (e / 64).toNat) + (e / 64).toNat by lia,
      UInt64Array.valAt_add, show n.toNat - (e / 64).toNat + (e / 64).toNat = n.toNat by lia]
  have hlo : a₁.valAt t.toNat (n.toNat - (e / 64).toNat) =
      arr.valAt t.toNat (n.toNat - (e / 64).toNat) :=
    UInt64Array.valAt_congr _ fun i _ _ => p₁u i (by lia)
  have hV₁ : a₂.valAt d.toNat (e / 64).toNat = a₁.valAt d.toNat (e / 64).toNat :=
    UInt64Array.valAt_congr _ fun i _ _ => p₂u i (by lia)
  have hst : (a₂.uset (d + n) 0 hidx).valAt d.toNat (n.toNat + 1) =
      a₁.valAt d.toNat (e / 64).toNat +
        2 ^ (64 * (e / 64).toNat) * a₂.valAt (d.toNat + (e / 64).toNat)
          (n.toNat - (e / 64).toNat) := by
    rw [valAt_top, getElem!_uset, valAt_uset_of _ _ _ _ _ _ (by rw [hdn]; lia)]
    simp only [hdn, ↓reduceIte, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    rw [show n.toNat = (e / 64).toNat + (n.toNat - (e / 64).toNat) by lia, UInt64Array.valAt_add,
      hV₁, show (e / 64).toNat + (n.toNat - (e / 64).toNat) = n.toNat by lia]
  have hPn : 2 ^ (64 * n.toNat) = 2 ^ (64 * (e / 64).toNat) *
      2 ^ (64 * (n.toNat - (e / 64).toNat)) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hPn₁ : 2 ^ 64 ≤ 2 ^ (64 * (e / 64).toNat) * 2 ^ (64 * (n.toNat - (e / 64).toNat)) := by
    rw [← hPn]; exact two_pow_le _ hn
  have hc₁ : c₁.toNat ≤ 1 := by
    have := valAt_lt a₁ d.toNat (e / 64).toNat
    have := valAt_lt arr (t.toNat + (n.toNat - (e / 64).toNat)) (e / 64).toNat
    rcases Nat.lt_or_ge c₁.toNat 2 with h | h
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * (e / 64).toNat)) h; lia
  have htn₁ : arr[t.toNat + n.toNat]!.toNat ≤ 1 := by
    have hT' := hT
    simp only [fermat] at hT'
    rw [hTv, hPn] at hT'
    rcases Nat.lt_or_ge arr[t.toNat + n.toNat]!.toNat 2 with h | h
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * (e / 64).toNat) *
        2 ^ (64 * (n.toNat - (e / 64).toNat))) h
      lia
  rw [UInt64.toNat_add, htv, Nat.mod_eq_of_lt (by lia), hlo] at p₂v
  have hl₃ : LoopBound (a₂.uset (d + n) 0 hidx) d (n + 1) :=
    ((hd.of_size (h₂.trans h₁)).of_size (size_uset ..)).lb (by rw [hs]; exact Nat.le_refl _)
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, size_uset] at i₁ i₂ i₃
  rw [hst] at i₃
  have hB : 2 ^ (64 * (n.toNat + 1)) = 2 ^ (64 * (e / 64).toNat) *
      2 ^ (64 * (n.toNat - (e / 64).toNat)) * 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hPr : 2 ^ 64 ≤ 2 ^ (64 * (n.toNat - (e / 64).toNat)) := two_pow_le _ (by lia)
  have hV₁l := valAt_lt a₁ d.toNat (e / 64).toNat
  have hV₂l := valAt_lt a₂ (d.toNat + (e / 64).toNat) (n.toNat - (e / 64).toNat)
  have hThl := valAt_lt arr (t.toNat + (n.toNat - (e / 64).toNat)) (e / 64).toNat
  have hTll := valAt_lt arr t.toNat (n.toNat - (e / 64).toNat)
  have hIl := valAt_lt (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1 d.toNat
    (n.toNat + 1)
  have hc₁l := c₁.toNat_lt
  have htnl := (a₁.uget (t + n) (by rw [htn, h₁]; lia)).toNat_lt
  rw [htv] at htnl
  simp only [fermat] at hT ⊢
  rw [hTv, hPn] at hT
  rw [hB] at i₃ hIl
  -- The residue before the shift.
  have hres : (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1.valAt d.toNat
      (n.toNat + 1) < 2 ^ (64 * n.toNat) + 1 ∧
      (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1.valAt d.toNat (n.toNat + 1) ≤
        2 ^ (64 * n.toNat) ∧
      arr.valAt t.toNat (n.toNat + 1) * 2 ^ (64 * (e / 64).toNat) % (2 ^ (64 * n.toNat) + 1) =
        (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1.valAt d.toNat (n.toNat + 1) := by
    rw [hTv, hPn]
    exact rot_res p₁v p₂v i₃ hV₁l hV₂l htn₁ hc₁ hPr
  obtain ⟨r₁, r₂, r₃⟩ := hres
  have hsz : (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1.size = arr.size := by
    rw [i₁, h₂, h₁]
  have hun : ∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
      (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1[i]! = arr[i]! := by
    intro i hi
    rw [i₂ i (by lia), getElem!_uset, ite_eq_right_iff.2 (fun e => by rw [hdn] at e; lia),
      p₂u i (by lia), p₁u i (by lia)]
  have he₆ : e.toNat = 64 * (e / 64).toNat + (e % 64).toNat := by
    rw [USize.toNat_div, USize.toNat_mod, toNat_64]; lia
  dsimp only at hR
  split at hR
  · rename_i h0
    subst hR
    refine ⟨hsz, hun, ?_⟩
    rw [he₆, show (e % 64).toNat = 0 by rw [h0]; rfl, Nat.add_zero]
    exact r₃.symm
  · rename_i h0
    have hb₀ : 0 < (e % 64).toUInt64.toNat := by
      rw [USize.toNat_toUInt64]
      rcases Nat.eq_zero_or_pos (e % 64).toNat with h | h
      · exact absurd (USize.toNat_inj.1 (by rw [h]; rfl)) h0
      · exact h
    have hb : (e % 64).toUInt64.toNat < 64 := by
      rw [USize.toNat_toUInt64, USize.toNat_mod, toNat_64]; exact Nat.mod_lt _ (by decide)
    obtain ⟨a₅, h₅, c₅, e₅, hR₅⟩ := foldUInPlace2Then_cases hR
    clear hR
    have hl₄ : LoopBound (incrAt (a₂.uset (d + n) 0 hidx) d (n + 1) hl₃ 0 c₂).1 d (n + 1) :=
      (hd.of_size hsz).lb (by rw [hs]; exact Nat.le_refl _)
    have P₅ := foldUInPlace2_spec (n + 1) (shlStep (n + 1) (e % 64).toUInt64) UInt64.toNat
      (fun _ => 0) 0 0 (2 ^ (e % 64).toUInt64.toNat) 0
      (fun c => c.toNat < 2 ^ (e % 64).toUInt64.toNat)
      (shlStep_inv _ _ hb₀ hb) (shlStep_law _ _ hb₀ hb) _ d d d hl₄ hl₄ hl₄ (by lia) (by lia) 0 0
      (by simp only [UInt64.toNat_zero]; exact Nat.two_pow_pos _)
    rw [e₅] at P₅
    obtain ⟨-, -, p₅u, p₅v⟩ := P₅
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, Nat.zero_mul, Nat.mul_zero,
      UInt64.toNat_zero] at p₅u p₅v
    subst hR₅
    obtain ⟨n₁, n₂, n₃⟩ := normAt_spec a₅ n d ((hd.of_size hsz).of_size h₅) hn
    refine ⟨n₁.trans (h₅.trans hsz), fun i hi => by rw [n₂ i hi, p₅u i (by lia), hun i hi], ?_⟩
    rw [n₃]
    simp only [fermat]
    have hbb : 2 ^ (e % 64).toUInt64.toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by lia)
    rw [USize.toNat_toUInt64] at hbb p₅v
    have hc₅ : c₅.toNat = 0 := by
      rcases Nat.eq_zero_or_pos c₅.toNat with h | h
      · exact h
      · rw [hB] at p₅v
        have := Nat.mul_le_mul_left (2 ^ (64 * (e / 64).toNat) *
          2 ^ (64 * (n.toNat - (e / 64).toNat)) * 2 ^ 64) h
        have := Nat.mul_le_mul hbb r₂
        rw [hPn] at this
        lia
    rw [hc₅, Nat.mul_zero, Nat.add_zero] at p₅v
    rw [p₅v, he₆, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_mod, ← r₃, Nat.mod_mod, ← Nat.mul_mod,
      Nat.mul_comm]

end MPN.FFT
