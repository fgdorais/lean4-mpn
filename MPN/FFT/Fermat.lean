/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordArray
public import MPN.FFT.Windows

/-!
# Residues modulo `2^(w n) + 1`

The FFT works modulo the Fermat number `F = 2^(w n) + 1`, on residues of `n + 1` limbs of `w` bits
whose value is less than `F`, so that the top limb is `0` or `1`, and `1` only for
`2^(w n) ≡ -1`. They are windows of one flat array: each function takes the array, `n` and the
offsets of the windows it reads and the one it writes, and returns the new array, through the
in-place fold `fold2Then` of `WordFolds`, so that the array is never shared.

Since `2^(w n) ≡ -1`, the value `L + 2^(w n) H` of a window is `L - H` modulo `F`, which is how
the results are reduced: the top limb is subtracted from the others, and when that borrows, `1`
is added, by loops that stop as soon as the carry or the borrow is zero.

The operations with `Nat` offsets, which check their bounds (`subModG`, `addModG`, `mulPow2G`),
are those of `WinOps`, for the transforms.
-/

namespace MPN.FFT

open WordArray

/-! ## Carries -/

private theorem mod_of_eq {R v q F : Nat} (h : R + F * q = v) (hR : R < F) : v % F = R := by
  subst h; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

private theorem mod_of_eq' {R v q c F : Nat} (h : R + F * q = v + F * c) (hR : R < F) :
    v % F = R := by
  have := congrArg (· % F) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR] at this
  exact this.symm

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

omit R in
private theorem two_pow_le (n : Nat) (hn : 1 ≤ n) : 2 ^ LA.w ≤ 2 ^ (LA.w * n) :=
  Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hn)

private theorem shl_step (x c b : L) (hb₀ : 0 < LA.val b) (hb : LA.val b < LA.w)
    (hc : LA.val c < 2 ^ LA.val b) :
    LA.val (R.add (R.shl x b) c) + 2 ^ LA.w * LA.val (R.shr x (R.sub (R.ofUSize R.wU) b)) =
        2 ^ LA.val b * LA.val x + LA.val c ∧
      LA.val (R.shr x (R.sub (R.ofUSize R.wU) b)) < 2 ^ LA.val b := by
  have hwB : LA.w < 2 ^ LA.w := Nat.lt_two_pow_self
  have hBb := LA.val_lt b
  have hwb : LA.val (R.sub (R.ofUSize R.wU) b) = LA.w - LA.val b := by
    rw [R.val_sub, R.val_ofUSize, R.toNat_wU, Nat.mod_eq_of_lt hwB,
      show LA.w + (2 ^ LA.w - LA.val b) = (LA.w - LA.val b) + 2 ^ LA.w * 1 by lia,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by lia)]
  rw [R.val_add, R.val_shl, R.val_shr, hwb, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show LA.w - LA.val b < LA.w by lia)]
  have hPQ : 2 ^ (LA.w - LA.val b) * 2 ^ LA.val b = 2 ^ LA.w := by
    rw [← Nat.pow_add]; congr 1; lia
  have hx := LA.val_lt x
  have hP : 0 < 2 ^ LA.val b := Nat.two_pow_pos _
  have hQ : 0 < 2 ^ (LA.w - LA.val b) := Nat.two_pow_pos _
  rw [← hPQ] at hx ⊢
  have hdm := Nat.div_add_mod (LA.val x) (2 ^ (LA.w - LA.val b))
  have hr := Nat.mod_lt (LA.val x) hQ
  generalize LA.val x / 2 ^ (LA.w - LA.val b) = q at *
  generalize LA.val x % 2 ^ (LA.w - LA.val b) = r at *
  generalize 2 ^ (LA.w - LA.val b) = Q at *
  generalize 2 ^ LA.val b = P at *
  generalize LA.val x = X at *
  generalize LA.val c = C at *
  subst hdm
  have hrP : (r + 1) * P ≤ Q * P := Nat.mul_le_mul_right P hr
  have hq : q < P := by
    rcases Nat.lt_or_ge q P with e | e
    · exact e
    · have := Nat.mul_le_mul_left Q e; lia
  have e₁ : (Q * q + r) * P = Q * P * q + r * P := by grind
  rw [e₁, Nat.add_comm (Q * P * q), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (show r * P < Q * P from Nat.mul_lt_mul_of_pos_right hr hP),
    Nat.mod_eq_of_lt (show r * P + C < Q * P by grind)]
  exact ⟨by grind, hq⟩

/-! ## Increment and decrement -/

/-- Adds `c` to limbs `o + j` to `o + len - 1` of `arr`, stopping as soon as the carry is zero. -/
@[expose, specialize]
public def incrAt (arr : A) (o len : USize) (h : LoopBound arr o len) (j : USize) (c : L) : A × L :=
  if R.isZero c then
    (arr, R.zero)
  else if hj : j < len then
    let x := R.uget arr (o + j) (h.uset_bound hj)
    incrAt (R.uset arr (o + j) (R.add x c) (h.uset_bound hj)) o len (h.of_uset ..) (j + 1)
      (R.addh R.zero x c)
  else
    (arr, c)
termination_by len.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 hj
  rw [USize.toNat_add_one_of_lt hj]
  lia

public theorem incrAt_spec (arr : A) (o len : USize) (h : LoopBound arr o len) (j : USize) (c : L) :
    LA.size (incrAt arr o len h j c).1 = LA.size arr ∧
      (∀ i, (i < o.toNat + j.toNat ∨ o.toNat + len.toNat ≤ i) →
        LA.get (incrAt arr o len h j c).1 i = LA.get arr i) ∧
      LimbArray.valAt (incrAt arr o len h j c).1 (o.toNat + j.toNat) (len.toNat - j.toNat) +
          2 ^ (LA.w * (len.toNat - j.toNat)) * LA.val (incrAt arr o len h j c).2 =
        LimbArray.valAt arr (o.toNat + j.toNat) (len.toNat - j.toNat) + LA.val c := by
  induction arr, h, j, c using incrAt.induct (R := R) o len with
  | case1 arr h j c hc =>
    rw [incrAt]
    simp [hc, R.val_zero, (R.isZero_iff c).1 hc]
  | case2 arr h j c hc hj x ih =>
    rw [incrAt]
    simp only [hc, hj, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    have hj' := USize.lt_iff_toNat_lt.1 hj
    have hj₁ := USize.toNat_add_one_of_lt hj
    have hidx := h.toNat_add hj
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv : LA.get (incrAt (R.uset arr (o + j) (R.add x c) (h.uset_bound hj)) o len (h.of_uset ..)
        (j + 1) (R.addh R.zero x c)).1 (o.toNat + j.toNat) = R.add x c := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hidx]
    have hr' : LimbArray.valAt (R.uset arr (o + j) (R.add x c) (h.uset_bound hj))
        (o.toNat + (j.toNat + 1)) (len.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (o.toNat + (j.toNat + 1)) (len.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    have hx : x = LA.get arr (o.toNat + j.toNat) := by
      show R.uget arr (o + j) _ = _
      rw [R.uget_eq, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, len.toNat - j.toNat = k + 1 := ⟨len.toNat - j.toNat - 1, by lia⟩
      rw [show len.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := incr_step (A := A) x c
      generalize LimbArray.valAt (incrAt (A := A) _ _ _ _ _ _).1 _ _ = V at *
      generalize LA.val (incrAt (A := A) _ _ _ _ _ _).2 = c' at *
      generalize LA.val (R.addh R.zero x c) = c₁ at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize 2 ^ LA.w = B at *
      grind
  | case3 arr h j c hc hj =>
    rw [incrAt]
    have : len.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := len); lia
    simp [hc, hj, this]

/--
Subtracts `c` from limbs `o + j` to `o + len - 1` of `arr`, stopping as soon as the borrow is
zero.
-/
@[expose, specialize]
public def decrAt (arr : A) (o len : USize) (h : LoopBound arr o len) (j : USize) (c : L) : A × L :=
  if R.isZero c then
    (arr, R.zero)
  else if hj : j < len then
    let x := R.uget arr (o + j) (h.uset_bound hj)
    decrAt (R.uset arr (o + j) (R.sub x c) (h.uset_bound hj)) o len (h.of_uset ..) (j + 1)
      (R.subh R.zero x c)
  else
    (arr, c)
termination_by len.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 hj
  rw [USize.toNat_add_one_of_lt hj]
  lia

public theorem decrAt_spec (arr : A) (o len : USize) (h : LoopBound arr o len) (j : USize) (c : L) :
    LA.size (decrAt arr o len h j c).1 = LA.size arr ∧
      (∀ i, (i < o.toNat + j.toNat ∨ o.toNat + len.toNat ≤ i) →
        LA.get (decrAt arr o len h j c).1 i = LA.get arr i) ∧
      LimbArray.valAt (decrAt arr o len h j c).1 (o.toNat + j.toNat) (len.toNat - j.toNat) +
          LA.val c =
        LimbArray.valAt arr (o.toNat + j.toNat) (len.toNat - j.toNat) +
          2 ^ (LA.w * (len.toNat - j.toNat)) * LA.val (decrAt arr o len h j c).2 := by
  induction arr, h, j, c using decrAt.induct (R := R) o len with
  | case1 arr h j c hc =>
    rw [decrAt]
    simp [hc, R.val_zero, (R.isZero_iff c).1 hc]
  | case2 arr h j c hc hj x ih =>
    rw [decrAt]
    simp only [hc, hj, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    have hj' := USize.lt_iff_toNat_lt.1 hj
    have hj₁ := USize.toNat_add_one_of_lt hj
    have hidx := h.toNat_add hj
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv : LA.get (decrAt (R.uset arr (o + j) (R.sub x c) (h.uset_bound hj)) o len (h.of_uset ..)
        (j + 1) (R.subh R.zero x c)).1 (o.toNat + j.toNat) = R.sub x c := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hidx]
    have hr' : LimbArray.valAt (R.uset arr (o + j) (R.sub x c) (h.uset_bound hj))
        (o.toNat + (j.toNat + 1)) (len.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (o.toNat + (j.toNat + 1)) (len.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    have hx : x = LA.get arr (o.toNat + j.toNat) := by
      show R.uget arr (o + j) _ = _
      rw [R.uget_eq, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, len.toNat - j.toNat = k + 1 := ⟨len.toNat - j.toNat - 1, by lia⟩
      rw [show len.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have := decr_step (A := A) x c
      generalize LimbArray.valAt (decrAt (A := A) _ _ _ _ _ _).1 _ _ = V at *
      generalize LA.val (decrAt (A := A) _ _ _ _ _ _).2 = c' at *
      generalize LA.val (R.subh R.zero x c) = c₁ at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize 2 ^ LA.w = B at *
      grind
  | case3 arr h j c hc hj =>
    rw [decrAt]
    have : len.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := len); lia
    simp [hc, hj, this]

/-! ## Windows and steps -/

/-- A window of `n + 1` limbs of `arr` at `o`; the indices of `arr` do not overflow. -/
public abbrev Win (arr : A) (n o : USize) : Prop :=
  o.toNat + n.toNat + 1 ≤ LA.size arr ∧ LA.size arr < USize.size

omit R in
public theorem Win.of_size {arr arr' : A} {n o : USize} (h : Win arr n o)
    (e : LA.size arr' = LA.size arr) : Win arr' n o := by
  simp only [Win, e]; exact h

omit R in
public theorem Win.succ {arr : A} {n o : USize} (h : Win arr n o) :
    (n + 1).toNat = n.toNat + 1 := by
  rw [USize.toNat_add_of_lt (by rw [USize.toNat_one]; lia), USize.toNat_one]

omit R in
public theorem Win.add {arr : A} {n o : USize} (h : Win arr n o) {k : USize}
    (hk : k.toNat ≤ n.toNat) : (o + k).toNat = o.toNat + k.toNat :=
  USize.toNat_add_of_lt (by lia)

omit R in
/-- Limbs `o` to `o + m - 1` of the window, as a loop bound. -/
public theorem Win.lb {arr : A} {n o : USize} (h : Win arr n o) {m : USize}
    (hm : m.toNat ≤ n.toNat + 1) : LoopBound arr o m := by
  constructor <;> lia

omit R in
/-- Limbs `o + k` to `o + k + m - 1` of the window, as a loop bound. -/
public theorem Win.lbAt {arr : A} {n o : USize} (h : Win arr n o) {k m : USize}
    (hk : k.toNat ≤ n.toNat) (hm : k.toNat + m.toNat ≤ n.toNat + 1) : LoopBound arr (o + k) m := by
  have := h.add hk
  constructor <;> lia

omit R in
/-- The value of a window: its low `n` limbs and its top limb. -/
public theorem valAt_top (a : A) (o n : Nat) :
    LimbArray.valAt a o (n + 1) =
      LimbArray.valAt a o n + 2 ^ (LA.w * n) * LA.val (LA.get a (o + n)) := by
  rw [LimbArray.valAt_add, LimbArray.valAt_one]

variable (A) in
/-- `x + y` with a carry. -/
@[inline, expose] public def addStep (N : USize) (j : USize) (_ : j < N) (x y c : L) : L × L :=
  (R.add (R.add x y) c, R.addh (R.addh R.zero x y) (R.add x y) c)

variable (A) in
/-- `x - y` with a borrow. -/
@[inline, expose] public def subStep (N : USize) (j : USize) (_ : j < N) (x y c : L) : L × L :=
  (R.sub (R.sub x y) c, R.subh (R.subh R.zero x y) (R.sub x y) c)

variable (A) in
/-- `-y` with a borrow. -/
@[inline, expose] public def negStep (N : USize) (j : USize) (_ : j < N) (_ y c : L) : L × L :=
  (R.sub (R.sub R.zero y) c, R.subh (R.subh R.zero R.zero y) (R.sub R.zero y) c)

variable (A) in
/-- `x` minus a borrow. -/
@[inline, expose] public def decStep (N : USize) (j : USize) (_ : j < N) (x _ c : L) : L × L :=
  (R.sub x c, R.subh R.zero x c)

variable (A) in
/-- `x 2ᵇ`, for `0 < b < w`, with the high bits of the previous limb. -/
@[inline, expose] public def shlStep (N : USize) (b : L) (j : USize) (_ : j < N) (x _ c : L) :
    L × L :=
  (R.add (R.shl x b) c, R.shr x (R.sub (R.ofUSize R.wU) b))

private theorem addStep_law (N : USize) : ∀ j h x y c, True →
    LA.val (addStep A N j h x y c).1 + 2 ^ LA.w * LA.val (addStep A N j h x y c).2 + 0 * LA.val x +
      0 * LA.val y + (fun _ => 0) c = 1 * LA.val x + 1 * LA.val y +
      2 ^ LA.w * (fun _ => 0) (addStep A N j h x y c).2 + LA.val c := by
  intro j h x y c _
  have := add_step (A := A) x y c
  simp only [addStep]
  lia

private theorem subStep_law (N : USize) : ∀ j h x y c, True →
    LA.val (subStep A N j h x y c).1 + 2 ^ LA.w * (fun _ => 0) (subStep A N j h x y c).2 +
      0 * LA.val x + 1 * LA.val y + LA.val c = 1 * LA.val x + 0 * LA.val y +
      2 ^ LA.w * LA.val (subStep A N j h x y c).2 + (fun _ => 0) c := by
  intro j h x y c _
  have := sub_step (A := A) x y c
  simp only [subStep]
  lia

private theorem negStep_law (N : USize) : ∀ j h x y c, True →
    LA.val (negStep A N j h x y c).1 + 2 ^ LA.w * (fun _ => 0) (negStep A N j h x y c).2 +
      0 * LA.val x + 1 * LA.val y + LA.val c = 0 * LA.val x + 0 * LA.val y +
      2 ^ LA.w * LA.val (negStep A N j h x y c).2 + (fun _ => 0) c := by
  intro j h x y c _
  have := sub_step (A := A) R.zero y c
  simp only [negStep, R.val_zero] at this ⊢
  lia

private theorem decStep_law (N : USize) : ∀ j h x y c, True →
    LA.val (decStep A N j h x y c).1 + 2 ^ LA.w * (fun _ => 0) (decStep A N j h x y c).2 +
      0 * LA.val x + 0 * LA.val y + LA.val c = 1 * LA.val x + 0 * LA.val y +
      2 ^ LA.w * LA.val (decStep A N j h x y c).2 + (fun _ => 0) c := by
  intro j h x y c _
  have := decr_step (A := A) x c
  simp only [decStep]
  lia

private theorem shlStep_law (N : USize) (b : L) (hb₀ : 0 < LA.val b) (hb : LA.val b < LA.w) :
    ∀ j h x y c, (fun c => LA.val c < 2 ^ LA.val b) c →
    LA.val (shlStep A N b j h x y c).1 + 2 ^ LA.w * LA.val (shlStep A N b j h x y c).2 +
      0 * LA.val x + 0 * LA.val y + (fun _ => 0) c = 2 ^ LA.val b * LA.val x + 0 * LA.val y +
      2 ^ LA.w * (fun _ => 0) (shlStep A N b j h x y c).2 + LA.val c := by
  intro j h x y c hc
  have := (shl_step (A := A) x c b hb₀ hb hc).1
  simp only [shlStep]
  lia

private theorem shlStep_inv (N : USize) (b : L) (hb₀ : 0 < LA.val b) (hb : LA.val b < LA.w) :
    ∀ j h x y c, (fun c => LA.val c < 2 ^ LA.val b) c →
      (fun c => LA.val c < 2 ^ LA.val b) (shlStep A N b j h x y c).2 :=
  fun _ _ x _ c hc => (shl_step (A := A) x c b hb₀ hb hc).2

/-- A limb that is not zero, of a value at most `1`, is `1`. -/
private theorem val_eq_one {x : L} (h : ¬R.isZero x = true) (h₁ : LA.val x < 2) : LA.val x = 1 := by
  have : LA.val x ≠ 0 := fun e => h ((R.isZero_iff x).2 e)
  lia

/-! ## Reduction -/

/--
Reduces the window of `n + 1` limbs at `o` modulo `2^(w n) + 1`: subtracts its top limb from the
others, and adds `1` back when that borrows.
-/
@[expose, specialize]
public def normAt (arr : A) (n o : USize) (h : Win arr n o) : A :=
  let H := R.uget arr (o + n) (by rw [h.add (Nat.le_refl _)]; lia)
  let a := R.uset arr (o + n) R.zero (by rw [h.add (Nat.le_refl _)]; lia)
  let p := decrAt a o n ((h.of_size (R.size_uset ..)).lb (by lia)) 0 H
  if R.isZero p.2 then p.1
  else (incrAt p.1 o (n + 1) (((h.of_size (R.size_uset ..)).of_size (decrAt_spec ..).1).lb
    (by rw [h.succ]; exact Nat.le_refl _)) 0 R.one).1

public theorem normAt_spec (arr : A) (n o : USize) (h : Win arr n o) (hn : 1 ≤ n.toNat) :
    LA.size (normAt arr n o h) = LA.size arr ∧
      (∀ i, (i < o.toNat ∨ o.toNat + n.toNat + 1 ≤ i) → LA.get (normAt arr n o h) i = LA.get arr i) ∧
      LimbArray.valAt (normAt arr n o h) o.toNat (n.toNat + 1) =
        LimbArray.valAt arr o.toNat (n.toNat + 1) % fermatW LA.w n.toNat := by
  have hB4 := four_le (R := R)
  have hon := h.add (Nat.le_refl _)
  have hidx : (o + n).toNat < LA.size arr := by rw [hon]; lia
  have hH : R.uget arr (o + n) hidx = LA.get arr (o.toNat + n.toNat) := by rw [R.uget_eq, hon]
  have ha₁ : LimbArray.valAt (R.uset arr (o + n) R.zero hidx) o.toNat n.toNat =
      LimbArray.valAt arr o.toNat n.toNat :=
    valAt_uset_of _ _ _ _ _ _ (by rw [hon]; lia)
  have ha₂ : ∀ i, i ≠ o.toNat + n.toNat →
      LA.get (R.uset arr (o + n) R.zero hidx) i = LA.get arr i := by
    intro i hi; rw [R.get_uset]; simp only [hon]; split <;> lia
  have ha₃ : LA.get (R.uset arr (o + n) R.zero hidx) (o.toNat + n.toNat) = R.zero := by
    rw [R.get_uset]; simp [hon]
  dsimp only [normAt]
  have hlb : LoopBound (R.uset arr (o + n) R.zero hidx) o n :=
    (h.of_size (R.size_uset ..)).lb (by lia)
  obtain ⟨d₁, d₂, d₃⟩ := decrAt_spec (R.uset arr (o + n) R.zero hidx) o n hlb 0
    (R.uget arr (o + n) hidx)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, R.size_uset] at d₁ d₂ d₃
  rw [ha₁] at d₃
  have dtop := d₂ (o.toNat + n.toNat) (.inr (Nat.le_refl _))
  rw [ha₃] at dtop
  have hv := valAt_top arr o.toNat n.toNat
  rw [← hH] at hv
  have hD := LimbArray.valAt_lt (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0
    (R.uget arr (o + n) hidx)).1 o.toNat n.toNat
  have hL := LimbArray.valAt_lt arr o.toNat n.toNat
  have hHl := LA.val_lt (R.uget arr (o + n) hidx)
  have hw := two_pow_le (A := A) n.toNat hn
  have hB : 2 ^ (LA.w * (n.toNat + 1)) = 2 ^ (LA.w * n.toNat) * 2 ^ LA.w := by
    rw [Nat.mul_succ, Nat.pow_add]
  have hc : LA.val (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0
      (R.uget arr (o + n) hidx)).2 < 2 := by
    rcases Nat.lt_or_ge (LA.val (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0
      (R.uget arr (o + n) hidx)).2) 2 with hc | hc
    · exact hc
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat)) hc; lia
  simp only [fermatW]
  split
  · rename_i hc0
    refine ⟨d₁, fun i hi => ?_, ?_⟩
    · rw [d₂ i (by lia), ha₂ i (by lia)]
    · rw [valAt_top, dtop, R.val_zero, Nat.mul_zero, Nat.add_zero]
      rw [(R.isZero_iff _).1 hc0, Nat.mul_zero, Nat.add_zero] at d₃
      generalize LimbArray.valAt (decrAt (A := A) _ _ _ _ _ _).1 _ _ = D at *
      generalize 2 ^ (LA.w * n.toNat) = Bn at *
      generalize LA.val (R.uget arr (o + n) hidx) = H at *
      generalize LimbArray.valAt arr o.toNat n.toNat = L at *
      exact (mod_of_eq (q := H) (by rw [hv]; grind) (by lia)).symm
  · rename_i hc0
    have hc1 := val_eq_one hc0 hc
    rw [hc1] at d₃
    have hlb' : LoopBound (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0
        (R.uget arr (o + n) hidx)).1 o (n + 1) :=
      (h.of_size d₁).lb (by rw [h.succ]; exact Nat.le_refl _)
    obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0
      (R.uget arr (o + n) hidx)).1 o (n + 1) hlb' 0 R.one
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, h.succ, R.val_one] at i₁ i₂ i₃
    rw [valAt_top (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0 (R.uget arr (o + n) hidx)).1
      o.toNat n.toNat, dtop, R.val_zero, Nat.mul_zero, Nat.add_zero] at i₃
    generalize incrAt (decrAt (R.uset arr (o + n) R.zero hidx) o n hlb 0
      (R.uget arr (o + n) hidx)).1 o (n + 1) hlb' 0 R.one = q at *
    have hq := LimbArray.valAt_lt q.1 o.toNat (n.toNat + 1)
    refine ⟨i₁.trans d₁, fun i hi => ?_, ?_⟩
    · rw [i₂ i (by lia), d₂ i (by lia), ha₂ i (by lia)]
    · rw [hB] at i₃ hq
      generalize LimbArray.valAt (decrAt (A := A) _ _ _ _ _ _).1 _ _ = D at *
      generalize 2 ^ (LA.w * n.toNat) = Bn at *
      generalize LA.val (R.uget arr (o + n) hidx) = H at *
      generalize LimbArray.valAt arr o.toNat n.toNat = L at *
      generalize 2 ^ LA.w = B at *
      have hc' : LA.val q.2 = 0 := by
        rcases Nat.eq_zero_or_pos (LA.val q.2) with e | e
        · exact e
        · have := Nat.mul_le_mul_left (Bn * B) e
          have : Bn * 2 ≤ Bn * B := Nat.mul_le_mul_left _ (by lia)
          lia
      rw [hc', Nat.mul_zero, Nat.add_zero] at i₃
      rw [hv]
      obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by lia⟩
      exact (mod_of_eq (q := H') (by grind) (by lia)).symm

/-! ## Addition and subtraction -/

variable [F : WordFolds A L]

/--
Writes `(x + y) % F` into the window at `d`, for residues `x` and `y` in the windows at `x` and
`y`, which may be the window at `d`.
-/
@[expose, specialize]
public def addModAt (arr : A) (n d x y : USize) (hd : Win arr n d) (hx : Win arr n x)
    (hy : Win arr n y) : A :=
  F.fold2Then (n + 1) (addStep A (n + 1)) arr d x y
    (hd.lb (by rw [hd.succ]; exact Nat.le_refl _)) (hx.lb (by rw [hx.succ]; exact Nat.le_refl _))
    (hy.lb (by rw [hy.succ]; exact Nat.le_refl _)) 0 R.zero fun a ha _ =>
      normAt a n d (hd.of_size ha)

public theorem addModAt_spec (arr : A) (n d x y : USize) (hd : Win arr n d)
    (hx : Win arr n x) (hy : Win arr n y) (hn : 1 ≤ n.toNat)
    (hdx : d.toNat ≤ x.toNat ∨ x.toNat + n.toNat + 1 ≤ d.toNat)
    (hdy : d.toNat ≤ y.toNat ∨ y.toNat + n.toNat + 1 ≤ d.toNat)
    (hX : LimbArray.valAt arr x.toNat (n.toNat + 1) < fermatW LA.w n.toNat)
    (hY : LimbArray.valAt arr y.toNat (n.toNat + 1) < fermatW LA.w n.toNat) :
    LA.size (addModAt arr n d x y hd hx hy) = LA.size arr ∧
      (∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
        LA.get (addModAt arr n d x y hd hx hy) i = LA.get arr i) ∧
      LimbArray.valAt (addModAt arr n d x y hd hx hy) d.toNat (n.toNat + 1) =
        (LimbArray.valAt arr x.toNat (n.toNat + 1) + LimbArray.valAt arr y.toNat (n.toNat + 1)) %
          fermatW LA.w n.toNat := by
  have hB4 := four_le (R := R)
  rw [addModAt, fold2Then_eq']
  have hs := hd.succ
  have hlb := hd.lb (by rw [hd.succ]; exact Nat.le_refl _)
  have hlx := hx.lb (by rw [hx.succ]; exact Nat.le_refl _)
  have hly := hy.lb (by rw [hy.succ]; exact Nat.le_refl _)
  obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace2_spec (n + 1) (addStep A (n + 1)) LA.val (fun _ => 0)
    0 0 1 1 (fun _ => True) (fun _ _ _ _ _ _ => trivial) (addStep_law _) arr d x y hlb hlx hly
    (by rw [hs]; lia) (by rw [hs]; lia) 0 R.zero trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, Nat.zero_mul, Nat.mul_zero,
    Nat.one_mul, R.val_zero] at f₂ f₃
  obtain ⟨n₁, n₂, n₃⟩ := normAt_spec _ n d (hd.of_size (size_foldUInPlace2 ..)) hn
  refine ⟨n₁.trans f₁, fun i hi => by rw [n₂ i hi, f₂ i (by lia)], ?_⟩
  rw [n₃]
  have hB : 2 ^ (LA.w * (n.toNat + 1)) = 2 ^ (LA.w * n.toNat) * 2 ^ LA.w := by
    rw [Nat.mul_succ, Nat.pow_add]
  have hw := two_pow_le (A := A) n.toNat hn
  have hS := LimbArray.valAt_lt (foldUInPlace2 (n + 1) (addStep A (n + 1)) arr d x y hlb hlx hly 0
    R.zero).1 d.toNat (n.toNat + 1)
  rw [hB] at f₃ hS
  simp only [fermatW] at hX hY ⊢
  generalize LimbArray.valAt (foldUInPlace2 (n + 1) (addStep A (n + 1)) arr d x y hlb hlx hly 0
    R.zero).1 _ _ = S at *
  generalize LA.val (foldUInPlace2 (n + 1) (addStep A (n + 1)) arr d x y hlb hlx hly 0
    R.zero).2 = c at *
  generalize 2 ^ (LA.w * n.toNat) = Bn at *
  generalize 2 ^ LA.w = B at *
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with e | e
    · exact e
    · have := Nat.mul_le_mul_left (Bn * B) e
      have : Bn * 4 ≤ Bn * B := Nat.mul_le_mul_left _ hB4
      lia
  subst hc
  rw [Nat.mul_zero, Nat.add_zero] at f₃
  rw [f₃]

/--
Writes `(x - y) % F` into the window at `d`, for residues `x` and `y` in the windows at `x` and
`y`, which may be the window at `d`. When `x - y` borrows, its top limb is all ones, and the
residue is its other limbs plus `1`.
-/
@[expose, specialize]
public def subModAt (arr : A) (n d x y : USize) (hd : Win arr n d) (hx : Win arr n x)
    (hy : Win arr n y) : A :=
  F.fold2Then (n + 1) (subStep A (n + 1)) arr d x y
    (hd.lb (by rw [hd.succ]; exact Nat.le_refl _)) (hx.lb (by rw [hx.succ]; exact Nat.le_refl _))
    (hy.lb (by rw [hy.succ]; exact Nat.le_refl _)) 0 R.zero fun a ha c =>
      if R.isZero c then a
      else
        have hd' := hd.of_size ha
        (incrAt (R.uset a (d + n) R.zero (by rw [hd'.add (Nat.le_refl _)]; lia)) d (n + 1)
          ((hd'.of_size (R.size_uset ..)).lb (by rw [hd.succ]; exact Nat.le_refl _)) 0 R.one).1

public theorem subModAt_spec (arr : A) (n d x y : USize) (hd : Win arr n d)
    (hx : Win arr n x) (hy : Win arr n y) (hn : 1 ≤ n.toNat)
    (hdx : d.toNat ≤ x.toNat ∨ x.toNat + n.toNat + 1 ≤ d.toNat)
    (hdy : d.toNat ≤ y.toNat ∨ y.toNat + n.toNat + 1 ≤ d.toNat)
    (hX : LimbArray.valAt arr x.toNat (n.toNat + 1) < fermatW LA.w n.toNat)
    (hY : LimbArray.valAt arr y.toNat (n.toNat + 1) < fermatW LA.w n.toNat) :
    LA.size (subModAt arr n d x y hd hx hy) = LA.size arr ∧
      (∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
        LA.get (subModAt arr n d x y hd hx hy) i = LA.get arr i) ∧
      LimbArray.valAt (subModAt arr n d x y hd hx hy) d.toNat (n.toNat + 1) =
        (LimbArray.valAt arr x.toNat (n.toNat + 1) + fermatW LA.w n.toNat -
          LimbArray.valAt arr y.toNat (n.toNat + 1)) % fermatW LA.w n.toNat := by
  have hB4 := four_le (R := R)
  rw [subModAt, fold2Then_eq']
  have hs := hd.succ
  have hlb := hd.lb (by rw [hd.succ]; exact Nat.le_refl _)
  have hlx := hx.lb (by rw [hx.succ]; exact Nat.le_refl _)
  have hly := hy.lb (by rw [hy.succ]; exact Nat.le_refl _)
  obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace2_spec (n + 1) (subStep A (n + 1)) (fun _ => 0) LA.val
    0 1 1 0 (fun _ => True) (fun _ _ _ _ _ _ => trivial) (subStep_law _) arr d x y hlb hlx hly
    (by rw [hs]; lia) (by rw [hs]; lia) 0 R.zero trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, Nat.zero_mul, Nat.mul_zero,
    Nat.one_mul, R.val_zero] at f₂ f₃
  have hB : 2 ^ (LA.w * (n.toNat + 1)) = 2 ^ (LA.w * n.toNat) * 2 ^ LA.w := by
    rw [Nat.mul_succ, Nat.pow_add]
  have hw := two_pow_le (A := A) n.toNat hn
  have hS := LimbArray.valAt_lt (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
    R.zero).1 d.toNat (n.toNat + 1)
  rw [hB] at f₃ hS
  simp only [fermatW] at hX hY ⊢
  have hc : LA.val (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
      R.zero).2 < 2 := by
    rcases Nat.lt_or_ge (LA.val (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
      R.zero).2) 2 with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat) * 2 ^ LA.w) e
      have : 2 ^ (LA.w * n.toNat) * 2 ≤ 2 ^ (LA.w * n.toNat) * 2 ^ LA.w :=
        Nat.mul_le_mul_left _ (by lia)
      lia
  split
  · rename_i hc0
    refine ⟨f₁, fun i hi => f₂ i (by lia), ?_⟩
    rw [(R.isZero_iff _).1 hc0, Nat.mul_zero, Nat.add_zero] at f₃
    generalize LimbArray.valAt (foldUInPlace2 (A := A) _ _ _ _ _ _ _ _ _ _ _).1 _ _ = S at *
    generalize 2 ^ (LA.w * n.toNat) = Bn at *
    exact (mod_of_eq (q := 1) (by lia) (by lia)).symm
  · rename_i hc0
    have hc1 := val_eq_one hc0 hc
    rw [hc1, Nat.mul_one] at f₃
    have hd' := hd.of_size f₁
    have hon := hd'.add (Nat.le_refl _)
    have hidx : (d + n).toNat < LA.size (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx
        hly 0 R.zero).1 := by rw [hon]; lia
    have hlb' : LoopBound (R.uset (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
        R.zero).1 (d + n) R.zero hidx) d (n + 1) :=
      (hd'.of_size (R.size_uset ..)).lb (by rw [hd.succ]; exact Nat.le_refl _)
    obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec _ d (n + 1) hlb' 0 R.one
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, R.val_one] at i₁ i₂ i₃
    have hv := valAt_top (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
      R.zero).1 d.toNat n.toNat
    have hv' := valAt_top (R.uset (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
        R.zero).1 (d + n) R.zero hidx) d.toNat n.toNat
    rw [valAt_uset_of _ (d + n) R.zero hidx d.toNat n.toNat (by rw [hon]; lia), R.get_uset] at hv'
    simp only [hon, ↓reduceIte, R.val_zero, Nat.mul_zero, Nat.add_zero] at hv'
    rw [hv'] at i₃
    generalize incrAt _ d (n + 1) hlb' 0 R.one = q at *
    have hq := LimbArray.valAt_lt q.1 d.toNat (n.toNat + 1)
    refine ⟨i₁.trans (R.size_uset ..) |>.trans f₁, fun i hi => ?_, ?_⟩
    · rw [i₂ i (by lia), R.get_uset, ite_eq_right_iff.2 (fun e => by rw [hon] at e; lia),
        f₂ i (by lia)]
    · rw [hB] at hq i₃
      have hL := LimbArray.valAt_lt (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly
        0 R.zero).1 d.toNat n.toNat
      have ht := LA.val_lt (LA.get (foldUInPlace2 (n + 1) (subStep A (n + 1)) arr d x y hlb hlx hly 0
        R.zero).1 (d.toNat + n.toNat))
      generalize LimbArray.valAt (foldUInPlace2 (A := A) _ _ _ _ _ _ _ _ _ _ _).1 d.toNat (n.toNat + 1) =
        S at *
      generalize LimbArray.valAt (foldUInPlace2 (A := A) _ _ _ _ _ _ _ _ _ _ _).1 d.toNat n.toNat = L at *
      generalize LA.val (LA.get (foldUInPlace2 (A := A) _ _ _ _ _ _ _ _ _ _ _).1 (d.toNat + n.toNat)) =
        t at *
      generalize 2 ^ (LA.w * n.toNat) = Bn at *
      generalize 2 ^ LA.w = B at *
      have htop : t = B - 1 := by
        rcases Nat.lt_or_ge t (B - 1) with e | e
        · have := Nat.mul_le_mul_left Bn (show t ≤ B - 2 by lia)
          have : Bn * (B - 2) + Bn * 2 = Bn * B := by
            rw [← Nat.mul_add, Nat.sub_add_cancel (by lia)]
          lia
        · lia
      subst htop
      have hc' : LA.val q.2 = 0 := by
        rcases Nat.eq_zero_or_pos (LA.val q.2) with e | e
        · exact e
        · have := Nat.mul_le_mul_left (Bn * B) e
          have : Bn * 2 ≤ Bn * B := Nat.mul_le_mul_left _ (by lia)
          lia
      rw [hc', Nat.mul_zero, Nat.add_zero] at i₃
      have : Bn * (B - 1) + Bn = Bn * B := by
        rw [← Nat.mul_add_one, Nat.sub_add_cancel (by lia)]
      rw [Nat.mod_eq_of_lt (by lia)]
      lia

/-! ## Multiplication by a power of two -/

/-- The value of the two passes of `mulPow2At`. -/
private theorem rot_value {V₁ V₂ Thi Tlo tn c₁ c₂ Pw Pr : Nat} (h₁ : V₁ + Thi = Pw * c₁)
    (h₂ : V₂ + (c₁ + tn) = Tlo + Pr * c₂) :
    V₁ + Pw * V₂ + c₂ + (Pw * Pr + 1) * (Thi + tn * Pw) =
      (Tlo + Pr * Thi + Pw * Pr * tn) * Pw + (Pw * Pr + 1) * c₂ := by
  have := congrArg (Pw * ·) h₂
  grind

/--
Writes `t 2ᵉ % F` into the window at `d`, for a residue `t` in the window at `t`, disjoint from
it, and `e < w n`. With `e = w q + b`, the limbs of `t` above `n - q` wrap around negated, since
`2^(w n) ≡ -1`: they are subtracted from zero into the low `q` limbs, the others are copied above
them less the borrow and the top limb of `t`, and `1` is added when that borrows. The shift by
`b` bits, when `b ≠ 0`, follows in place, then a reduction.
-/
@[expose, specialize]
public def mulPow2At (arr : A) (n d t e : USize) (hd : Win arr n d) (ht : Win arr n t)
    (he : e.toNat < LA.w * n.toNat) : A :=
  have hw : (e / R.wU).toNat < n.toNat := by
    rw [USize.toNat_div, R.toNat_wU]
    exact (Nat.div_lt_iff_lt_mul LA.w_pos).2 (by rw [Nat.mul_comm]; exact he)
  have hnw : (n - e / R.wU).toNat = n.toNat - (e / R.wU).toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
  have htw : (t + (n - e / R.wU)).toNat = t.toNat + (n.toNat - (e / R.wU).toNat) := by
    rw [← hnw]; exact ht.add (by rw [hnw]; lia)
  have hlw : LoopBound arr (t + (n - e / R.wU)) (e / R.wU) :=
    ⟨by rw [htw]; lia, by rw [htw]; lia⟩
  F.fold2Then (e / R.wU) (negStep A (e / R.wU)) arr d (t + (n - e / R.wU)) (t + (n - e / R.wU))
    (hd.lb (by lia)) hlw hlw 0 R.zero fun a₁ h₁ c₁ =>
  have hlt : LoopBound a₁ t (n - e / R.wU) := (ht.of_size h₁).lb (by rw [hnw]; lia)
  F.fold2Then (n - e / R.wU) (decStep A (n - e / R.wU)) a₁ (d + e / R.wU) t t
    ((hd.of_size h₁).lbAt (by lia) (by rw [hnw]; lia)) hlt hlt 0
    (R.add c₁ (R.uget a₁ (t + n) (by rw [(ht.of_size h₁).add (Nat.le_refl _), h₁]; lia)))
    fun a₂ h₂ c₂ =>
  have hd₂ := hd.of_size (h₂.trans h₁)
  have hd₃ : Win (R.uset a₂ (d + n) R.zero (by rw [hd₂.add (Nat.le_refl _)]; lia)) n d :=
    hd₂.of_size (R.size_uset ..)
  have hl₃ := hd₃.lb (by rw [hd.succ]; exact Nat.le_refl _)
  have hd₄ := hd₃.of_size (incrAt_spec _ d (n + 1) hl₃ 0 c₂).1
  if e % R.wU = 0 then
    (incrAt (R.uset a₂ (d + n) R.zero _) d (n + 1) hl₃ 0 c₂).1
  else
    have hl₄ := hd₄.lb (by rw [hd.succ]; exact Nat.le_refl _)
    F.fold2Then (n + 1) (shlStep A (n + 1) (R.ofUSize (e % R.wU)))
      (incrAt (R.uset a₂ (d + n) R.zero _) d (n + 1) hl₃ 0 c₂).1 d d d hl₄ hl₄ hl₄ 0 R.zero
      fun a₅ h₅ _ => normAt a₅ n d (hd₄.of_size h₅)

/-- The residue of `mulPow2At` before the shift, from the values of its passes. -/
private theorem rot_res {V₁ V₂ Thi Tlo tn c₁ c₂ I c Pw Pr B : Nat} (h₁ : V₁ + Thi = Pw * c₁)
    (h₂ : V₂ + (c₁ + tn) = Tlo + Pr * c₂) (hi : I + Pw * Pr * B * c = V₁ + Pw * V₂ + c₂)
    (hV₁ : V₁ < Pw) (hV₂ : V₂ < Pr) (htn : tn ≤ 1) (hc₁ : c₁ ≤ 1) (hB : 2 ≤ B) (hPr : B ≤ Pr) :
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
    · have := Nat.mul_le_mul_left (Pw * Pr * B) h
      have : Pw * Pr * 2 ≤ Pw * Pr * B := Nat.mul_le_mul_left _ hB
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

public theorem mulPow2At_spec (arr : A) (n d t e : USize) (hd : Win arr n d)
    (ht : Win arr n t) (he : e.toNat < LA.w * n.toNat) (hn : 1 ≤ n.toNat)
    (hdt : d.toNat + n.toNat + 1 ≤ t.toNat ∨ t.toNat + n.toNat + 1 ≤ d.toNat)
    (hT : LimbArray.valAt arr t.toNat (n.toNat + 1) < fermatW LA.w n.toNat) :
    LA.size (mulPow2At arr n d t e hd ht he) = LA.size arr ∧
      (∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
        LA.get (mulPow2At arr n d t e hd ht he) i = LA.get arr i) ∧
      LimbArray.valAt (mulPow2At arr n d t e hd ht he) d.toNat (n.toNat + 1) =
        LimbArray.valAt arr t.toNat (n.toNat + 1) * 2 ^ e.toNat % fermatW LA.w n.toNat := by
  have hw : (e / R.wU).toNat < n.toNat := by
    rw [USize.toNat_div, R.toNat_wU]
    exact (Nat.div_lt_iff_lt_mul LA.w_pos).2 (by rw [Nat.mul_comm]; exact he)
  have hnw : (n - e / R.wU).toNat = n.toNat - (e / R.wU).toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
  have htw : (t + (n - e / R.wU)).toNat = t.toNat + (n.toNat - (e / R.wU).toNat) := by
    rw [← hnw]; exact ht.add (by rw [hnw]; lia)
  have hdw := hd.add (k := e / R.wU) (by lia)
  have hlw : LoopBound arr (t + (n - e / R.wU)) (e / R.wU) := ⟨by rw [htw]; lia, by rw [htw]; lia⟩
  have hs := hd.succ
  have htn := ht.add (Nat.le_refl _)
  have hB4 := four_le (R := R)
  generalize hq : (e / R.wU).toNat = q at hw hnw htw hdw
  generalize hG : mulPow2At arr n d t e hd ht he = G
  rw [mulPow2At] at hG
  -- The negated limbs.
  obtain ⟨a₁, h₁, c₁, e₁, hG₁⟩ := fold2Then_cases hG
  clear hG
  have P₁ := foldUInPlace2_spec (e / R.wU) (negStep A (e / R.wU)) (fun _ => 0) LA.val 0 1 0 0
    (fun _ => True) (fun _ _ _ _ _ _ => trivial) (negStep_law _) arr d (t + (n - e / R.wU))
    (t + (n - e / R.wU)) (hd.lb (by lia)) hlw hlw (by rw [htw, hq]; lia) (by rw [htw, hq]; lia) 0
    R.zero trivial
  rw [e₁] at P₁
  obtain ⟨-, -, p₁u, p₁v⟩ := P₁
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, htw, hq, Nat.zero_mul, Nat.one_mul,
    Nat.mul_zero, Nat.zero_add, R.val_zero] at p₁u p₁v
  -- The other limbs, less the borrow and the top limb.
  obtain ⟨a₂, h₂, c₂, e₂, hG⟩ := fold2Then_cases hG₁
  clear hG₁
  have P₂ := foldUInPlace2_spec (n - e / R.wU) (decStep A (n - e / R.wU)) (fun _ => 0) LA.val
    0 0 1 0 (fun _ => True) (fun _ _ _ _ _ _ => trivial) (decStep_law _) a₁ (d + e / R.wU) t t
    ((hd.of_size h₁).lbAt (by lia) (by rw [hnw]; lia)) ((ht.of_size h₁).lb (by rw [hnw]; lia))
    ((ht.of_size h₁).lb (by rw [hnw]; lia)) (by rw [hdw, hnw]; lia) (by rw [hdw, hnw]; lia) 0
    (R.add c₁ (R.uget a₁ (t + n) (by rw [htn, h₁]; lia))) trivial
  rw [e₂] at P₂
  obtain ⟨-, -, p₂u, p₂v⟩ := P₂
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hdw, hnw, Nat.zero_mul, Nat.one_mul,
    Nat.mul_zero] at p₂u p₂v
  -- The values, as `Nat`s.
  have hidx : (d + n).toNat < LA.size a₂ := by rw [h₂, h₁, hd.add (Nat.le_refl _)]; lia
  have hdn := hd.add (Nat.le_refl _)
  have htv : LA.val (R.uget a₁ (t + n) (by rw [htn, h₁]; lia)) =
      LA.val (LA.get arr (t.toNat + n.toNat)) := by
    rw [R.uget_eq, htn, p₁u _ (by lia)]
  have hTv : LimbArray.valAt arr t.toNat (n.toNat + 1) =
      LimbArray.valAt arr t.toNat (n.toNat - q) +
        2 ^ (LA.w * (n.toNat - q)) * LimbArray.valAt arr (t.toNat + (n.toNat - q)) q +
      2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q)) * LA.val (LA.get arr (t.toNat + n.toNat)) := by
    rw [valAt_top, ← Nat.pow_add, ← Nat.mul_add, show q + (n.toNat - q) = n.toNat by lia,
      show n.toNat = (n.toNat - q) + q by lia, LimbArray.valAt_add,
      show n.toNat - q + q = n.toNat by lia]
  have hlo : LimbArray.valAt a₁ t.toNat (n.toNat - q) =
      LimbArray.valAt arr t.toNat (n.toNat - q) :=
    LimbArray.valAt_congr _ fun i _ _ => p₁u i (by lia)
  have hV₁ : LimbArray.valAt a₂ d.toNat q = LimbArray.valAt a₁ d.toNat q :=
    LimbArray.valAt_congr _ fun i _ _ => p₂u i (by lia)
  have hst : LimbArray.valAt (R.uset a₂ (d + n) R.zero hidx) d.toNat (n.toNat + 1) =
      LimbArray.valAt a₁ d.toNat q +
        2 ^ (LA.w * q) * LimbArray.valAt a₂ (d.toNat + q) (n.toNat - q) := by
    rw [valAt_top, R.get_uset, valAt_uset_of _ _ _ _ _ _ (by rw [hdn]; lia)]
    simp only [hdn, ↓reduceIte, R.val_zero, Nat.mul_zero, Nat.add_zero]
    rw [show n.toNat = q + (n.toNat - q) by lia, LimbArray.valAt_add, hV₁,
      show q + (n.toNat - q) = n.toNat by lia]
  have hPn : 2 ^ (LA.w * n.toNat) = 2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q)) := by
    rw [← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' (Nat.le_of_lt hw)]
  have hPn₁ : 2 ^ LA.w ≤ 2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q)) := by
    rw [← hPn]; exact two_pow_le (A := A) _ hn
  have hc₁ : LA.val c₁ ≤ 1 := by
    have := LimbArray.valAt_lt a₁ d.toNat q
    have := LimbArray.valAt_lt arr (t.toNat + (n.toNat - q)) q
    rcases Nat.lt_or_ge (LA.val c₁) 2 with h | h
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * q)) h; lia
  have htn₁ : LA.val (LA.get arr (t.toNat + n.toNat)) ≤ 1 := by
    have hT' := hT
    simp only [fermatW] at hT'
    rw [hTv, hPn] at hT'
    rcases Nat.lt_or_ge (LA.val (LA.get arr (t.toNat + n.toNat))) 2 with h | h
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q))) h
      lia
  rw [R.val_add, htv, Nat.mod_eq_of_lt (by lia), hlo] at p₂v
  have hl₃ : LoopBound (R.uset a₂ (d + n) R.zero hidx) d (n + 1) :=
    ((hd.of_size (h₂.trans h₁)).of_size (R.size_uset ..)).lb (by rw [hs]; exact Nat.le_refl _)
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, R.size_uset] at i₁ i₂ i₃
  rw [hst] at i₃
  have hB : 2 ^ (LA.w * (n.toNat + 1)) = 2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q)) * 2 ^ LA.w := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' (Nat.le_of_lt hw),
      Nat.mul_succ]
  have hPr : 2 ^ LA.w ≤ 2 ^ (LA.w * (n.toNat - q)) := two_pow_le (A := A) _ (by lia)
  have hV₁l := LimbArray.valAt_lt a₁ d.toNat q
  have hV₂l := LimbArray.valAt_lt a₂ (d.toNat + q) (n.toNat - q)
  have hThl := LimbArray.valAt_lt arr (t.toNat + (n.toNat - q)) q
  have hTll := LimbArray.valAt_lt arr t.toNat (n.toNat - q)
  have hIl := LimbArray.valAt_lt (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1
    d.toNat (n.toNat + 1)
  simp only [fermatW] at hT ⊢
  rw [hTv, hPn] at hT
  rw [hB] at i₃ hIl
  -- The residue before the shift.
  have hres : LimbArray.valAt (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1
      d.toNat (n.toNat + 1) < 2 ^ (LA.w * n.toNat) + 1 ∧
      LimbArray.valAt (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1 d.toNat
        (n.toNat + 1) ≤ 2 ^ (LA.w * n.toNat) ∧
      LimbArray.valAt arr t.toNat (n.toNat + 1) * 2 ^ (LA.w * q) % (2 ^ (LA.w * n.toNat) + 1) =
        LimbArray.valAt (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1 d.toNat
          (n.toNat + 1) := by
    rw [hTv, hPn]
    exact rot_res p₁v p₂v i₃ hV₁l hV₂l htn₁ hc₁ (by lia) hPr
  obtain ⟨r₁, r₂, r₃⟩ := hres
  have hsz : LA.size (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1 =
      LA.size arr := by
    rw [i₁, h₂, h₁]
  have hun : ∀ i, (i < d.toNat ∨ d.toNat + n.toNat + 1 ≤ i) →
      LA.get (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1 i = LA.get arr i := by
    intro i hi
    rw [i₂ i (by lia), R.get_uset, ite_eq_right_iff.2 (fun e => by rw [hdn] at e; lia),
      p₂u i (by lia), p₁u i (by lia)]
  have hem : (e % R.wU).toNat = e.toNat % LA.w := by rw [USize.toNat_mod, R.toNat_wU]
  have he₆ : e.toNat = LA.w * q + (e % R.wU).toNat := by
    rw [← hq, USize.toNat_div, R.toNat_wU, hem]; exact (Nat.div_add_mod _ _).symm
  dsimp only at hG
  split at hG
  · rename_i h0
    subst hG
    refine ⟨hsz, hun, ?_⟩
    rw [he₆, show (e % R.wU).toNat = 0 by rw [h0]; rfl, Nat.add_zero]
    exact r₃.symm
  · rename_i h0
    have hbv : LA.val (R.ofUSize (e % R.wU)) = (e % R.wU).toNat := by
      rw [R.val_ofUSize, Nat.mod_eq_of_lt]
      rw [hem]
      exact Nat.lt_trans (Nat.mod_lt _ LA.w_pos) Nat.lt_two_pow_self
    have hb₀ : 0 < LA.val (R.ofUSize (e % R.wU)) := by
      rw [hbv]
      rcases Nat.eq_zero_or_pos (e % R.wU).toNat with h | h
      · exact absurd (USize.toNat_inj.1 (by rw [h]; rfl)) h0
      · exact h
    have hb : LA.val (R.ofUSize (e % R.wU)) < LA.w := by
      rw [hbv, hem]; exact Nat.mod_lt _ LA.w_pos
    obtain ⟨a₅, h₅, c₅, e₅, hG₅⟩ := fold2Then_cases hG
    clear hG
    have hl₄ : LoopBound (incrAt (R.uset a₂ (d + n) R.zero hidx) d (n + 1) hl₃ 0 c₂).1 d (n + 1) :=
      (hd.of_size hsz).lb (by rw [hs]; exact Nat.le_refl _)
    have P₅ := foldUInPlace2_spec (n + 1) (shlStep A (n + 1) (R.ofUSize (e % R.wU))) LA.val
      (fun _ => 0) 0 0 (2 ^ LA.val (R.ofUSize (e % R.wU))) 0
      (fun c => LA.val c < 2 ^ LA.val (R.ofUSize (e % R.wU)))
      (shlStep_inv _ _ hb₀ hb) (shlStep_law _ _ hb₀ hb) _ d d d hl₄ hl₄ hl₄ (by lia) (by lia) 0
      R.zero (by simp only [R.val_zero]; exact Nat.two_pow_pos _)
    rw [e₅] at P₅
    obtain ⟨-, -, p₅u, p₅v⟩ := P₅
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hs, Nat.zero_mul, Nat.mul_zero,
      R.val_zero] at p₅u p₅v
    subst hG₅
    obtain ⟨n₁, n₂, n₃⟩ := normAt_spec a₅ n d ((hd.of_size hsz).of_size h₅) hn
    refine ⟨n₁.trans (h₅.trans hsz), fun i hi => by rw [n₂ i hi, p₅u i (by lia), hun i hi], ?_⟩
    rw [n₃]
    simp only [fermatW]
    rw [hbv] at p₅v hb
    have hbb : 2 ^ (e % R.wU).toNat < 2 ^ LA.w := Nat.pow_lt_pow_right (by decide) hb
    have hc₅ : LA.val c₅ = 0 := by
      rcases Nat.eq_zero_or_pos (LA.val c₅) with h | h
      · exact h
      · rw [hB] at p₅v
        have h₁ := Nat.mul_le_mul_left (2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q)) * 2 ^ LA.w) h
        have h₂ : 2 ^ (e % R.wU).toNat * LimbArray.valAt (incrAt (R.uset a₂ (d + n) R.zero hidx) d
            (n + 1) hl₃ 0 c₂).1 d.toNat (n.toNat + 1) ≤ 2 ^ (e % R.wU).toNat * 2 ^ (LA.w * n.toNat) :=
          Nat.mul_le_mul_left _ r₂
        have h₃ : 2 ^ (e % R.wU).toNat * 2 ^ (LA.w * n.toNat) < 2 ^ LA.w * 2 ^ (LA.w * n.toNat) :=
          Nat.mul_lt_mul_of_pos_right hbb (Nat.two_pow_pos _)
        rw [hPn] at h₂ h₃
        have h₄ : 2 ^ LA.w * (2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q))) =
            2 ^ (LA.w * q) * 2 ^ (LA.w * (n.toNat - q)) * 2 ^ LA.w := Nat.mul_comm _ _
        lia
    rw [hc₅, Nat.mul_zero, Nat.add_zero] at p₅v
    rw [p₅v, he₆, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_mod, ← r₃, Nat.mod_mod, ← Nat.mul_mod,
      Nat.mul_comm]

/-! ## The residue operations of the transforms

The operations above with `Nat` offsets, which check their bounds: the transforms call these, so
that their definitions carry no proofs, and the theorems show that the checks pass.
-/

/-- `(x - y) % F` into the window at `d`. -/
@[expose, specialize]
public def subModG (arr : A) (n d x y : Nat) : A :=
  if h : Win arr n.toUSize d.toUSize ∧ Win arr n.toUSize x.toUSize ∧ Win arr n.toUSize y.toUSize
  then subModAt arr n.toUSize d.toUSize x.toUSize y.toUSize h.1 h.2.1 h.2.2 else arr

/-- `(x + y) % F` into the window at `d`. -/
@[expose, specialize]
public def addModG (arr : A) (n d x y : Nat) : A :=
  if h : Win arr n.toUSize d.toUSize ∧ Win arr n.toUSize x.toUSize ∧ Win arr n.toUSize y.toUSize
  then addModAt arr n.toUSize d.toUSize x.toUSize y.toUSize h.1 h.2.1 h.2.2 else arr

/-- `t 2ᵉ % F` into the window at `d`. -/
@[expose, specialize]
public def mulPow2G (arr : A) (n d t e : Nat) : A :=
  if h : Win arr n.toUSize d.toUSize ∧ Win arr n.toUSize t.toUSize ∧
      e.toUSize.toNat < LA.w * n.toUSize.toNat
  then mulPow2At arr n.toUSize d.toUSize t.toUSize e.toUSize h.1 h.2.1 h.2.2 else arr

private theorem toNat_toUSize {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a := by
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt h]

omit R F in
private theorem win_of {arr : A} {n o : Nat} (hS : LA.size arr < USize.size)
    (h : o + n + 1 ≤ LA.size arr) :
    Win arr n.toUSize o.toUSize ∧ n.toUSize.toNat = n ∧ o.toUSize.toNat = o := by
  have hn := toNat_toUSize (a := n) (by lia)
  have ho := toNat_toUSize (a := o) (by lia)
  exact ⟨⟨by rw [hn, ho]; exact h, hS⟩, hn, ho⟩

public theorem subModG_spec (arr : A) (n d x y : Nat) (hS : LA.size arr < USize.size)
    (hd : d + n + 1 ≤ LA.size arr) (hx : x + n + 1 ≤ LA.size arr) (hy : y + n + 1 ≤ LA.size arr)
    (hn : 1 ≤ n) (hdx : d ≤ x ∨ x + n + 1 ≤ d) (hdy : d ≤ y ∨ y + n + 1 ≤ d)
    (hX : WinOps.win arr n x < fermatW LA.w n) (hY : WinOps.win arr n y < fermatW LA.w n) :
    LA.size (subModG arr n d x y) = LA.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → LA.get (subModG arr n d x y) i = LA.get arr i) ∧
      WinOps.win (subModG arr n d x y) n d =
        (WinOps.win arr n x + fermatW LA.w n - WinOps.win arr n y) % fermatW LA.w n := by
  obtain ⟨wd, hn', hd'⟩ := win_of hS hd
  obtain ⟨wx, -, hx'⟩ := win_of hS hx
  obtain ⟨wy, -, hy'⟩ := win_of hS hy
  rw [subModG, dite_eq_left ⟨wd, wx, wy⟩]
  have := subModAt_spec arr n.toUSize d.toUSize x.toUSize y.toUSize wd wx wy (by lia)
    (by rw [hd', hx', hn']; lia) (by rw [hd', hy', hn']; lia) (by rw [hx', hn']; exact hX)
    (by rw [hy', hn']; exact hY)
  simp only [hn', hd', hx', hy'] at this
  exact this

public theorem addModG_spec (arr : A) (n d x y : Nat) (hS : LA.size arr < USize.size)
    (hd : d + n + 1 ≤ LA.size arr) (hx : x + n + 1 ≤ LA.size arr) (hy : y + n + 1 ≤ LA.size arr)
    (hn : 1 ≤ n) (hdx : d ≤ x ∨ x + n + 1 ≤ d) (hdy : d ≤ y ∨ y + n + 1 ≤ d)
    (hX : WinOps.win arr n x < fermatW LA.w n) (hY : WinOps.win arr n y < fermatW LA.w n) :
    LA.size (addModG arr n d x y) = LA.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → LA.get (addModG arr n d x y) i = LA.get arr i) ∧
      WinOps.win (addModG arr n d x y) n d =
        (WinOps.win arr n x + WinOps.win arr n y) % fermatW LA.w n := by
  obtain ⟨wd, hn', hd'⟩ := win_of hS hd
  obtain ⟨wx, -, hx'⟩ := win_of hS hx
  obtain ⟨wy, -, hy'⟩ := win_of hS hy
  rw [addModG, dite_eq_left ⟨wd, wx, wy⟩]
  have := addModAt_spec arr n.toUSize d.toUSize x.toUSize y.toUSize wd wx wy (by lia)
    (by rw [hd', hx', hn']; lia) (by rw [hd', hy', hn']; lia) (by rw [hx', hn']; exact hX)
    (by rw [hy', hn']; exact hY)
  simp only [hn', hd', hx', hy'] at this
  exact this

public theorem mulPow2G_spec (arr : A) (n d t e : Nat) (hS : LA.size arr < USize.size)
    (hd : d + n + 1 ≤ LA.size arr) (ht : t + n + 1 ≤ LA.size arr) (hn : 1 ≤ n)
    (he : e < LA.w * n) (heS : e < USize.size) (hdt : d + n + 1 ≤ t ∨ t + n + 1 ≤ d)
    (hT : WinOps.win arr n t < fermatW LA.w n) :
    LA.size (mulPow2G arr n d t e) = LA.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → LA.get (mulPow2G arr n d t e) i = LA.get arr i) ∧
      WinOps.win (mulPow2G arr n d t e) n d = WinOps.win arr n t * 2 ^ e % fermatW LA.w n := by
  obtain ⟨wd, hn', hd'⟩ := win_of hS hd
  obtain ⟨wt, -, ht'⟩ := win_of hS ht
  have he' : e.toUSize.toNat = e := toNat_toUSize heS
  rw [mulPow2G, dite_eq_left ⟨wd, wt, by rw [he', hn']; exact he⟩]
  have := mulPow2At_spec arr n.toUSize d.toUSize t.toUSize e.toUSize wd wt
    (by rw [he', hn']; exact he) (by lia) (by rw [hd', ht', hn']; lia) (by rw [ht', hn']; exact hT)
  simp only [hn', hd', ht', he'] at this
  exact this

end MPN.FFT
