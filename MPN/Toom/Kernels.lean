/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.MulLimbW
public import MPN.Bitwise
public import MPN.FFT.Fermat
public import MPN.Toom.Ops
public import MPN.Toom.Mid

/-!
# The kernels of the Toom methods, for limbs of any width

The in-place operations of `ToomOps` on windows `[o, o + len)` of arrays of limbs, over
`WordArray` and `WordFolds`: each checks that its windows fit in `USize` indices, runs one or two
folds over the window written, and otherwise writes the value of its specification with
`LimbArray.writeNat`, which never happens.

* `addIntoK` and `subIntoK` add `S` to `D` and subtract it, a fold over the limbs of `S` (`addC`,
  or `subMulB` by one) and the carry or borrow through the rest of the window (`FFT.incrAt`,
  `FFT.decrAt`);
* `addMulIntoK` and `subMulIntoK` add and subtract `S v`, by `addMul1W` and `subMul1W` and the
  carry or borrow;
* `zeroIntoK` writes zeros.
-/

namespace MPN.WordArray

open Toom LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-! ## Windows -/

/-- Whether the window `[o, o + len)` is in `d`, whose size fits in a `USize`. -/
@[inline, expose] public def winOK (d : A) (o len : Nat) : Bool :=
  decide (o + len ≤ LA.size d) && decide (LA.size d < 4294967295)

private theorem toNat_toUSize' {n : Nat} (h : n < 4294967295) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by have := USize.size_eq; omega)]

omit R F in
/-- The window of a checked `winOK`, as a loop bound. -/
public theorem winOK_spec {d : A} {o len : Nat} (h : winOK d o len = true) :
    o + len ≤ LA.size d ∧ o.toUSize.toNat = o ∧ len.toUSize.toNat = len ∧
      LoopBound d o.toUSize len.toUSize := by
  simp only [winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have e₁ := toNat_toUSize' (n := o) (by lia)
  have e₂ := toNat_toUSize' (n := len) (by lia)
  refine ⟨h.1, e₁, e₂, ?_, ?_⟩
  · rw [e₁, e₂]; exact h.1
  · rw [e₁, e₂]; have := USize.size_eq; omega

omit R F in
/-- A loop bound for the first `n` limbs of a window. -/
private theorem bound_le {d : A} {o len n : USize} (h : LoopBound d o len)
    (hn : n.toNat ≤ len.toNat) : LoopBound d o n := ⟨by have := h.1; lia, by have := h.2; lia⟩

omit R F in
/-- The fallback: the value of the specification, written. -/
private theorem fallback (d : A) (o len v : Nat) (h : o + len ≤ LA.size d)
    (hv : v < 2 ^ (LA.w * len)) :
    Writes (writeNat d o len v) d o len ∧ valAt (writeNat d o len v) o len = v :=
  ⟨writes_writeNat .., by rw [valAt_writeNat _ _ _ _ h]; exact Nat.mod_eq_of_lt hv⟩

/-! ## Adding -/

variable (A) in
/-- The step of `addIntoK`: the limb `z` plus limb `so + j` of `s`, with a carry. -/
@[inline, expose] public def addCStep (s : A) (so n : USize) (hs : LoopBound s so n) (j : USize)
    (h : j < n) (z c : L) : L × L :=
  R.addC z (R.uget s (so + j) (hs.uset_bound h)) c

/-- `D + S` in the window of `D`, for `S` of at most as many limbs: `addInto d o len s so sl`. -/
public def addIntoK (d : A) (o len : Nat) (s : A) (so sl : Nat) : A :=
  if h : winOK d o len = true ∧ winOK s so sl = true ∧ sl ≤ len then
    have hd := winOK_spec h.1
    have hs := winOK_spec h.2.1
    have hsl : sl.toUSize.toNat ≤ len.toUSize.toNat := by rw [hs.2.2.1, hd.2.2.1]; exact h.2.2
    F.foldThen sl.toUSize (addCStep A s so.toUSize sl.toUSize hs.2.2.2) d o.toUSize
      (bound_le hd.2.2.2 hsl) 0 R.zero fun arr ha c =>
        (FFT.incrAt arr o.toUSize len.toUSize (hd.2.2.2.of_size ha) sl.toUSize c).1
  else writeNat d o len (valAt d o len + valAt s so sl)

omit F in
/-- The fold of `addCStep`: the window of `D` plus `S`, below the carry. -/
private theorem addC_fold (s : A) (so n : USize) (hs : LoopBound s so n) (arr : A) (rs : USize)
    (hr : LoopBound arr rs n) :
    LA.size (foldUInPlace n (addCStep A s so n hs) arr rs hr 0 R.zero).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (addCStep A s so n hs) arr rs hr 0 R.zero).1 i = LA.get arr i) ∧
      valAt (foldUInPlace n (addCStep A s so n hs) arr rs hr 0 R.zero).1 rs.toNat n.toNat +
          2 ^ (LA.w * n.toNat) *
            LA.val (foldUInPlace n (addCStep A s so n hs) arr rs hr 0 R.zero).2 =
        valAt arr rs.toNat n.toNat + valAt s so.toNat n.toNat := by
  obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 n (addCStep A s so n hs) s so LA.val (fun _ => 0)
    1 0 0 1 1 (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun j h z c _ => by
      have := R.val_addC z (R.uget s (so + j) (hs.uset_bound h)) c
      rw [congrArg LA.val (show R.uget s (so + j) (hs.uset_bound h) =
        LA.get s (so.toNat + j.toNat) by rw [R.uget_eq, hs.toNat_add h])] at this
      simp only [addCStep]
      lia) arr rs hr 0 R.zero trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.zero_mul,
    Nat.mul_zero, Nat.add_zero, R.val_zero] at i₂ i₃
  exact ⟨i₁, i₂, by lia⟩

omit F in
/--
The carry pass of an addition: a first pass `p` over the low `sl` limbs of the window, whose value
and carry are those of the low part of `D + S`, then `incrAt` through the rest, give `D + S` when
it fits.
-/
private theorem carry_pass (d : A) (o len sl : Nat) (Sv : Nat) (p : A × L) (hsl : sl ≤ len)
    (oU lenU slU : USize) (e₁ : oU.toNat = o) (e₂ : lenU.toNat = len) (e₄ : slU.toNat = sl)
    (a₁ : LA.size p.1 = LA.size d)
    (a₂ : ∀ i, (i < o ∨ o + sl ≤ i) → LA.get p.1 i = LA.get d i)
    (a₃ : valAt p.1 o sl + 2 ^ (LA.w * sl) * LA.val p.2 = valAt d o sl + Sv)
    (hv : valAt d o len + Sv < 2 ^ (LA.w * len)) (hb : LoopBound p.1 oU lenU) :
    Writes (FFT.incrAt p.1 oU lenU hb slU p.2).1 d o len ∧
      valAt (FFT.incrAt p.1 oU lenU hb slU p.2).1 o len = valAt d o len + Sv := by
  obtain ⟨b₁, b₂, b₃⟩ := FFT.incrAt_spec p.1 oU lenU hb slU p.2
  generalize FFT.incrAt p.1 oU lenU hb slU p.2 = q at b₁ b₂ b₃ ⊢
  rw [e₁, e₂, e₄] at b₂ b₃
  refine ⟨⟨by rw [b₁, a₁], fun i hi => by rw [b₂ i (by lia), a₂ i (by lia)]⟩, ?_⟩
  -- The low `sl` limbs, and the rest with the carry.
  have hlow : valAt q.1 o sl = valAt p.1 o sl :=
    valAt_congr _ fun i _ hi => b₂ i (.inl (by lia))
  have hhigh : valAt p.1 (o + sl) (len - sl) = valAt d (o + sl) (len - sl) :=
    valAt_congr _ fun i h₁ _ => a₂ i (.inr (by lia))
  have hsplit : ∀ x : A,
      valAt x o len = valAt x o sl + 2 ^ (LA.w * sl) * valAt x (o + sl) (len - sl) := by
    intro x; rw [← valAt_add, Nat.add_sub_cancel' hsl]
  rw [hsplit q.1, hlow]
  rw [hsplit d] at hv ⊢
  rw [hhigh] at b₃
  have hpow : 2 ^ (LA.w * len) = 2 ^ (LA.w * sl) * 2 ^ (LA.w * (len - sl)) := by
    rw [← Nat.pow_add]; congr 1; rw [← Nat.mul_add, Nat.add_sub_cancel' hsl]
  rw [hpow] at hv
  -- The carry out is zero, since the sum fits.
  generalize valAt q.1 (o + sl) (len - sl) = Qh at b₃ ⊢
  generalize valAt d (o + sl) (len - sl) = Dh at b₃ hv ⊢
  generalize valAt p.1 o sl = Pl at a₃ ⊢
  generalize valAt d o sl = Dl at a₃ hv ⊢
  generalize LA.val q.2 = c₂ at b₃
  generalize LA.val p.2 = c₁ at a₃ b₃
  generalize 2 ^ (LA.w * sl) = P at *
  generalize 2 ^ (LA.w * (len - sl)) = H at *
  have hc₂ : c₂ = 0 := by
    rcases Nat.eq_zero_or_pos c₂ with e | e
    · exact e
    · exfalso
      have : P * H ≤ P * (H * c₂) := Nat.mul_le_mul_left P (Nat.le_mul_of_pos_right H e)
      have : P * (Qh + H * c₂) = P * (Dh + c₁) := by rw [b₃]
      grind
  subst hc₂
  grind

public theorem addIntoK_spec (d : A) (o len : Nat) (s : A) (so sl : Nat)
    (hw : o + len ≤ LA.size d) (hv : valAt d o len + valAt s so sl < 2 ^ (LA.w * len)) :
    Writes (addIntoK d o len s so sl) d o len ∧
      valAt (addIntoK d o len s so sl) o len = valAt d o len + valAt s so sl := by
  unfold addIntoK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    obtain ⟨-, e₃, e₄, hs⟩ := winOK_spec h.2.1
    have hsl := h.2.2
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨a₁, a₂, a₃⟩ := addC_fold s so.toUSize sl.toUSize hs d o.toUSize
      (bound_le hd (by rw [e₄, e₂]; exact hsl))
    simp only [e₁, e₃, e₄] at a₂ a₃
    exact carry_pass d o len sl _ _ hsl _ _ _ e₁ e₂ e₄ a₁ a₂ a₃ hv _
  · exact fallback _ _ _ _ hw hv

omit F in
/--
The borrow pass of a subtraction: a first pass `p` over the low `sl` limbs of the window, whose
value plus `S` is the low part of `D` and the borrow, then `decrAt` through the rest, give `D - S`
when `S ≤ D`.
-/
private theorem borrow_pass (d : A) (o len sl : Nat) (Sv : Nat) (p : A × L) (c : L)
    (hsl : sl ≤ len) (oU lenU slU : USize) (e₁ : oU.toNat = o) (e₂ : lenU.toNat = len)
    (e₄ : slU.toNat = sl) (a₁ : LA.size p.1 = LA.size d)
    (a₂ : ∀ i, (i < o ∨ o + sl ≤ i) → LA.get p.1 i = LA.get d i)
    (a₃ : valAt p.1 o sl + Sv = valAt d o sl + 2 ^ (LA.w * sl) * LA.val c)
    (hv : Sv ≤ valAt d o len) (hb : LoopBound p.1 oU lenU) :
    Writes (FFT.decrAt p.1 oU lenU hb slU c).1 d o len ∧
      valAt (FFT.decrAt p.1 oU lenU hb slU c).1 o len = valAt d o len - Sv := by
  obtain ⟨b₁, b₂, b₃⟩ := FFT.decrAt_spec p.1 oU lenU hb slU c
  generalize FFT.decrAt p.1 oU lenU hb slU c = q at b₁ b₂ b₃ ⊢
  rw [e₁, e₂, e₄] at b₂ b₃
  refine ⟨⟨by rw [b₁, a₁], fun i hi => by rw [b₂ i (by lia), a₂ i (by lia)]⟩, ?_⟩
  have hlow : valAt q.1 o sl = valAt p.1 o sl :=
    valAt_congr _ fun i _ hi => b₂ i (.inl (by lia))
  have hhigh : valAt p.1 (o + sl) (len - sl) = valAt d (o + sl) (len - sl) :=
    valAt_congr _ fun i h₁ _ => a₂ i (.inr (by lia))
  have hsplit : ∀ x : A,
      valAt x o len = valAt x o sl + 2 ^ (LA.w * sl) * valAt x (o + sl) (len - sl) := by
    intro x; rw [← valAt_add, Nat.add_sub_cancel' hsl]
  have hq := valAt_lt q.1 o len
  rw [hsplit q.1, hlow] at hq ⊢
  rw [hsplit d] at hv ⊢
  rw [hhigh] at b₃
  have hpow : 2 ^ (LA.w * len) = 2 ^ (LA.w * sl) * 2 ^ (LA.w * (len - sl)) := by
    rw [← Nat.pow_add]; congr 1; rw [← Nat.mul_add, Nat.add_sub_cancel' hsl]
  rw [hpow] at hq
  generalize valAt q.1 (o + sl) (len - sl) = Qh at b₃ hq ⊢
  generalize valAt d (o + sl) (len - sl) = Dh at b₃ hv ⊢
  generalize valAt p.1 o sl = Pl at a₃ hq ⊢
  generalize valAt d o sl = Dl at a₃ hv ⊢
  generalize LA.val q.2 = c₂ at b₃
  generalize LA.val c = c₁ at a₃ b₃
  generalize 2 ^ (LA.w * sl) = P at *
  generalize 2 ^ (LA.w * (len - sl)) = H at *
  -- The borrow out is zero, since `S ≤ D`.
  have e : Pl + P * Qh + Sv = Dl + P * Dh + P * H * c₂ := by
    have : P * (Qh + c₁) = P * (Dh + H * c₂) := by rw [b₃]
    grind
  have hc₂ : c₂ = 0 := by
    rcases Nat.eq_zero_or_pos c₂ with h | h
    · exact h
    · exfalso
      have : P * H ≤ P * H * c₂ := Nat.le_mul_of_pos_right _ h
      lia
  subst hc₂
  lia

/-! ## Subtracting -/

/-- `D - S` in the window of `D`, for `S` of at most as many limbs: `subInto d o len s so sl`. -/
public def subIntoK (d : A) (o len : Nat) (s : A) (so sl : Nat) : A :=
  if h : winOK d o len = true ∧ winOK s so sl = true ∧ sl ≤ len then
    have hd := winOK_spec h.1
    have hs := winOK_spec h.2.1
    have hsl : sl.toUSize.toNat ≤ len.toUSize.toNat := by rw [hs.2.2.1, hd.2.2.1]; exact h.2.2
    F.foldThen sl.toUSize (subMul1Step A s so.toUSize sl.toUSize hs.2.2.2 R.one) d o.toUSize
      (bound_le hd.2.2.2 hsl) 0 R.b0 fun arr ha c =>
        (FFT.decrAt arr o.toUSize len.toUSize (hd.2.2.2.of_size ha) sl.toUSize (R.unB c)).1
  else writeNat d o len (valAt d o len - valAt s so sl)

public theorem subIntoK_spec (d : A) (o len : Nat) (s : A) (so sl : Nat)
    (hw : o + len ≤ LA.size d) (hv : valAt s so sl ≤ valAt d o len) :
    Writes (subIntoK d o len s so sl) d o len ∧
      valAt (subIntoK d o len s so sl) o len = valAt d o len - valAt s so sl := by
  unfold subIntoK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    obtain ⟨-, e₃, e₄, hs⟩ := winOK_spec h.2.1
    have hsl := h.2.2
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨a₁, a₂, a₃⟩ := subMul1Fold_spec s so.toUSize sl.toUSize hs R.one d o.toUSize
      (bound_le hd (by rw [e₄, e₂]; exact hsl)) 0 R.b0
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₃, e₄, R.val_one, Nat.mul_one,
      R.val_unB_b0] at a₂ a₃
    exact borrow_pass d o len sl _ _ _ hsl _ _ _ e₁ e₂ e₄ a₁ a₂ a₃ hv _
  · exact fallback _ _ _ _ hw (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (valAt_lt ..))

/-! ## Adding and subtracting a multiple -/

/-- `D + S v` in the window of `D`, for a limb `v`: `addMulInto d o len s so sl v`. -/
public def addMulIntoK (d : A) (o len : Nat) (s : A) (so sl v : Nat) : A :=
  if h : winOK d o len = true ∧ winOK s so sl = true ∧ sl ≤ len ∧ v < 2 ^ LA.w ∧ v < 4294967295 then
    have hd := winOK_spec h.1
    have hs := winOK_spec h.2.1
    have hsl : sl.toUSize.toNat ≤ len.toUSize.toNat := by rw [hs.2.2.1, hd.2.2.1]; exact h.2.2.1
    F.foldThen sl.toUSize (addMul1Step A s so.toUSize sl.toUSize hs.2.2.2 (R.ofUSize v.toUSize)) d
      o.toUSize (bound_le hd.2.2.2 hsl) 0 R.zero fun arr ha c =>
        (FFT.incrAt arr o.toUSize len.toUSize (hd.2.2.2.of_size ha) sl.toUSize c).1
  else writeNat d o len (valAt d o len + valAt s so sl * v)

omit F in
/-- A limb `v`, as `ofUSize` of its `USize`. -/
private theorem val_ofUSize_lt {v : Nat} (h : v < 2 ^ LA.w) (h' : v < 4294967295) :
    LA.val (R.ofUSize v.toUSize) = v := by
  have hv : v < USize.size := by have := USize.size_eq; omega
  rw [R.val_ofUSize, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' hv, Nat.mod_eq_of_lt h]

public theorem addMulIntoK_spec (d : A) (o len : Nat) (s : A) (so sl v : Nat)
    (hw : o + len ≤ LA.size d) (hvw : v < 2 ^ LA.w)
    (hv : valAt d o len + valAt s so sl * v < 2 ^ (LA.w * len)) :
    Writes (addMulIntoK d o len s so sl v) d o len ∧
      valAt (addMulIntoK d o len s so sl v) o len = valAt d o len + valAt s so sl * v := by
  unfold addMulIntoK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    obtain ⟨-, e₃, e₄, hs⟩ := winOK_spec h.2.1
    have hsl := h.2.2.1
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨a₁, a₂, a₃⟩ := addMul1Fold_spec s so.toUSize sl.toUSize hs (R.ofUSize v.toUSize) d
      o.toUSize (bound_le hd (by rw [e₄, e₂]; exact hsl)) 0 R.zero
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₃, e₄,
      val_ofUSize_lt hvw h.2.2.2.2,
      R.val_zero] at a₂ a₃
    exact carry_pass d o len sl _ _ hsl _ _ _ e₁ e₂ e₄ a₁ a₂ (by rw [a₃]) hv _
  · exact fallback _ _ _ _ hw hv

/-- `D - S v` in the window of `D`, for a limb `v`: `subMulInto d o len s so sl v`. -/
public def subMulIntoK (d : A) (o len : Nat) (s : A) (so sl v : Nat) : A :=
  if h : winOK d o len = true ∧ winOK s so sl = true ∧ sl ≤ len ∧ v < 2 ^ LA.w ∧ v < 4294967295 then
    have hd := winOK_spec h.1
    have hs := winOK_spec h.2.1
    have hsl : sl.toUSize.toNat ≤ len.toUSize.toNat := by rw [hs.2.2.1, hd.2.2.1]; exact h.2.2.1
    F.foldThen sl.toUSize (subMul1Step A s so.toUSize sl.toUSize hs.2.2.2 (R.ofUSize v.toUSize)) d
      o.toUSize (bound_le hd.2.2.2 hsl) 0 R.b0 fun arr ha c =>
        (FFT.decrAt arr o.toUSize len.toUSize (hd.2.2.2.of_size ha) sl.toUSize (R.unB c)).1
  else writeNat d o len (valAt d o len - valAt s so sl * v)

public theorem subMulIntoK_spec (d : A) (o len : Nat) (s : A) (so sl v : Nat)
    (hw : o + len ≤ LA.size d) (hvw : v < 2 ^ LA.w) (hv : valAt s so sl * v ≤ valAt d o len) :
    Writes (subMulIntoK d o len s so sl v) d o len ∧
      valAt (subMulIntoK d o len s so sl v) o len = valAt d o len - valAt s so sl * v := by
  unfold subMulIntoK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    obtain ⟨-, e₃, e₄, hs⟩ := winOK_spec h.2.1
    have hsl := h.2.2.1
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨a₁, a₂, a₃⟩ := subMul1Fold_spec s so.toUSize sl.toUSize hs (R.ofUSize v.toUSize) d
      o.toUSize (bound_le hd (by rw [e₄, e₂]; exact hsl)) 0 R.b0
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₃, e₄,
      val_ofUSize_lt hvw h.2.2.2.2,
      R.val_unB_b0] at a₂ a₃
    exact borrow_pass d o len sl _ _ _ hsl _ _ _ e₁ e₂ e₄ a₁ a₂ a₃ hv _
  · exact fallback _ _ _ _ hw (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (valAt_lt ..))

/-! ## Zeros -/

variable (A) in
/-- The step of `zeroIntoK`. -/
@[inline, expose] public def zeroStep (n : USize) (j : USize) (_ : j < n) (_z c : L) : L × L :=
  (R.zero, c)

/-- `0` in the window: `zeroInto d o len`. -/
public def zeroIntoK (d : A) (o len : Nat) : A :=
  if h : winOK d o len = true then
    have hd := winOK_spec h
    F.foldThen len.toUSize (zeroStep A len.toUSize) d o.toUSize hd.2.2.2 0 R.zero
      fun arr _ _ => arr
  else writeNat d o len 0

public theorem zeroIntoK_spec (d : A) (o len : Nat) (hw : o + len ≤ LA.size d) :
    Writes (zeroIntoK d o len) d o len ∧ valAt (zeroIntoK d o len) o len = 0 := by
  unfold zeroIntoK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 len.toUSize (zeroStep A len.toUSize) d o.toUSize
      (fun _ => 0) (fun _ => 0) 1 0 0 0 0 (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ => by simp [zeroStep, R.val_zero]) d o.toUSize hd 0 R.zero trivial
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.zero_mul,
      Nat.mul_zero] at i₂ i₃
    rw [e₁, e₂] at i₂ i₃
    exact ⟨⟨i₁, i₂⟩, by lia⟩
  · exact fallback _ _ _ _ hw (Nat.two_pow_pos _)

/-! ## Shifts -/

variable (A) in
/-- The step of `shlTopK`: `z 2ˢ` plus the high bits of the limb below. -/
@[inline, expose] public def shlStep1 (n : USize) (b : L) (j : USize) (_ : j < n) (z c : L) :
    L × L :=
  (R.add (R.shl z b) c, R.shr z (R.sub (R.ofUSize R.wU) b))

omit F in
private theorem val_wm1 : LA.val (R.ofUSize (R.wU - 1) : L) = LA.w - 1 := by
  have hw := R.w_ge
  have hwU : LA.w < USize.size := by rw [← R.toNat_wU]; exact USize.toNat_lt_size _
  rw [R.val_ofUSize, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by
    rw [R.toNat_wU, USize.toNat_one]; lia)), R.toNat_wU, USize.toNat_one,
    Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := LA.w); lia)]

/-- `D 2^(w - 1)`, wrapped: `shlTop d o len`. -/
public def shlTopK (d : A) (o len : Nat) : A :=
  if h : winOK d o len = true then
    have hd := winOK_spec h
    F.foldThen len.toUSize (shlStep1 A len.toUSize (R.ofUSize (R.wU - 1))) d o.toUSize hd.2.2.2 0
      R.zero fun arr _ _ => arr
  else writeNat d o len (valAt d o len * 2 ^ (LA.w - 1) % 2 ^ (LA.w * len))

public theorem shlTopK_spec (d : A) (o len : Nat) (hw : o + len ≤ LA.size d) :
    Writes (shlTopK d o len) d o len ∧
      valAt (shlTopK d o len) o len = valAt d o len * 2 ^ (LA.w - 1) % 2 ^ (LA.w * len) := by
  have hw2 := R.w_ge
  have hs := val_wm1 (R := R)
  unfold shlTopK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 len.toUSize
      (shlStep1 A len.toUSize (R.ofUSize (R.wU - 1))) d o.toUSize LA.val (fun _ => 0) 1 0 0
      (2 ^ (LA.w - 1)) 0 (fun c => LA.val c < 2 ^ (LA.w - 1))
      (fun _ _ z c hc => by
        have := (shl_step z c (R.ofUSize (R.wU - 1)) (by rw [hs]; lia) (by rw [hs]; lia)
          (by rw [hs]; exact hc)).2
        rw [hs] at this; exact this)
      (fun _ _ z c hc => by
        have := (shl_step z c (R.ofUSize (R.wU - 1)) (by rw [hs]; lia) (by rw [hs]; lia)
          (by rw [hs]; exact hc)).1
        rw [hs] at this
        simp only [shlStep1]
        lia) d o.toUSize hd 0 R.zero (by rw [R.val_zero]; exact Nat.two_pow_pos _)
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.zero_mul,
      Nat.mul_zero, R.val_zero, e₁, e₂] at i₂ i₃
    refine ⟨⟨i₁, i₂⟩, ?_⟩
    have hlt := valAt_lt (foldUInPlace len.toUSize (shlStep1 A len.toUSize (R.ofUSize (R.wU - 1)))
      d o.toUSize hd 0 R.zero).1 o len
    rw [Nat.mul_comm (valAt d o len), ← i₃, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · exact fallback _ _ _ _ hw (Nat.mod_lt _ (Nat.two_pow_pos _))

variable (A) in
/--
`D / 2ˢ` in place, from limb `o + j - 1` down: each limb is shifted right by `s` and takes the
low bits of the limb `u` above it, read at the step before, by `sw = w - s`.
-/
@[expose, specialize]
public def shrSelf (d : A) (o : USize) (b bw : L) (j : USize) (hd : LoopBound d o j) (u : L) : A :=
  if hj : j = 0 then d
  else
    have hm := pos_of_ne hj
    let z := R.uget d (o + (j - 1)) (hd.uset_bound (pred_lt' hm))
    shrSelf (R.uset d (o + (j - 1)) (R.add (R.shr z b) (R.shl u bw)) (hd.uset_bound (pred_lt' hm)))
      o b bw (j - 1) ((bound_pred hd hm).of_uset ..) z
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have := USize.lt_iff_toNat_lt.1 (pos_of_ne hj)
  lia

omit F in
public theorem shrSelf_spec (d : A) (o : USize) (b : L) (hb₀ : 0 < LA.val b) (hb : LA.val b < LA.w)
    (j : USize) (hd : LoopBound d o j) (u : L) :
    LA.size (shrSelf A d o b (R.sub (R.ofUSize R.wU) b) j hd u) = LA.size d ∧
      (∀ i, (i < o.toNat ∨ o.toNat + j.toNat ≤ i) →
        LA.get (shrSelf A d o b (R.sub (R.ofUSize R.wU) b) j hd u) i = LA.get d i) ∧
      valAt (shrSelf A d o b (R.sub (R.ofUSize R.wU) b) j hd u) o.toNat j.toNat =
        (valAt d o.toNat j.toNat + 2 ^ (LA.w * j.toNat) * (LA.val u % 2 ^ LA.val b)) /
          2 ^ LA.val b := by
  induction d, j, hd, u using shrSelf.induct A (R := R) o b (R.sub (R.ofUSize R.wU) b) with
  | case1 d hd u =>
    rw [shrSelf, dite_eq_left rfl]
    refine ⟨rfl, fun _ _ => rfl, ?_⟩
    simp only [USize.toNat_zero, valAt_zero, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    exact (Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))).symm
  | case2 d j hd u hj hm z ih =>
    rw [shrSelf, dite_eq_right hj]
    obtain ⟨i₁, i₂, i₃⟩ := ih
    have hp := toNat_pred' hm
    have hj₀ := USize.lt_iff_toNat_lt.1 hm
    have hidx := hd.toNat_add (pred_lt' hm)
    rw [hp] at hidx i₂ i₃
    refine ⟨by rw [i₁, R.size_uset], fun i hi => ?_, ?_⟩
    · rw [i₂ i (by lia), R.get_uset, ite_eq_right (by rw [hidx]; lia)]
    · have hz : LA.val z = LA.val (LA.get d (o.toNat + (j.toNat - 1))) := by
        simp only [z]; rw [R.uget_eq, hidx]
      have htop := i₂ (o.toNat + (j.toNat - 1)) (.inr (Nat.le_refl _))
      rw [R.get_uset, ite_eq_left hidx] at htop
      have hlow : valAt (R.uset d (o + (j - 1))
          (R.add (R.shr z b) (R.shl u (R.sub (R.ofUSize R.wU) b)))
          (hd.uset_bound (pred_lt' hm))) o.toNat (j.toNat - 1) = valAt d o.toNat (j.toNat - 1) :=
        valAt_uset_of _ _ _ _ _ _ (.inr (by rw [hidx]; exact Nat.le_refl _))
      rw [hlow] at i₃
      have hs := shr_step z u b hb₀ hb
      rw [hz] at i₃ hs
      obtain ⟨k, hk⟩ : ∃ k, j.toNat = k + 1 := ⟨j.toNat - 1, by lia⟩
      rw [hk, Nat.add_sub_cancel] at i₃ htop hs
      rw [hk, valAt_add, valAt_add, valAt_one, valAt_one, htop, hs, i₃]
      -- `(V + Bᵏ z + Bᵏ⁺¹ u') / 2ᵇ`, with `z = 2ᵇ (z / 2ᵇ) + z mod 2ᵇ` and `B = 2ᵇ 2^(w - b)`.
      have hB : 2 ^ LA.w = 2 ^ LA.val b * 2 ^ (LA.w - LA.val b) := by
        rw [← Nat.pow_add]; congr 1; lia
      have hzd := Nat.div_add_mod (LA.val (LA.get d (o.toNat + k))) (2 ^ LA.val b)
      have hS : 0 < 2 ^ LA.val b := Nat.two_pow_pos _
      rw [Nat.mul_succ, Nat.pow_add, hB]
      generalize valAt d o.toNat k = V
      generalize LA.val (LA.get d (o.toNat + k)) = Z at hzd
      generalize LA.val u % 2 ^ LA.val b = U
      generalize 2 ^ (LA.w * k) = P
      generalize 2 ^ (LA.w - LA.val b) = Q
      generalize 2 ^ LA.val b = S at hzd hS
      rw [← hzd]
      have e : V + P * (S * (Z / S) + Z % S) + P * (S * Q) * U =
          (V + P * (Z % S)) + S * (P * (Z / S) + P * Q * U) := by grind
      rw [e, Nat.add_mul_div_left _ _ hS]
      grind

omit F in
/-- A shift `0 < s < w`, as `ofUSize` of its `USize`. -/
private theorem val_ofUSize_w {s : Nat} (h : s < LA.w) : LA.val (R.ofUSize s.toUSize : L) = s := by
  have hwU : LA.w < USize.size := by rw [← R.toNat_wU]; exact USize.toNat_lt_size _
  rw [R.val_ofUSize, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia),
    Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := LA.w); lia)]

/-- `D / 2ˢ` for `0 < s < w`, in place: `shr d o len s`. -/
public def shrK (d : A) (o len s : Nat) : A :=
  if h : winOK d o len = true ∧ 0 < s ∧ s < LA.w then
    have hd := winOK_spec h.1
    shrSelf A d o.toUSize (R.ofUSize s.toUSize) (R.sub (R.ofUSize R.wU) (R.ofUSize s.toUSize))
      len.toUSize hd.2.2.2 R.zero
  else writeNat d o len (valAt d o len / 2 ^ s)

omit F in
public theorem shrK_spec (d : A) (o len s : Nat) (hw : o + len ≤ LA.size d) (_hs₀ : 0 < s)
    (_hs : s < LA.w) :
    Writes (shrK d o len s) d o len ∧ valAt (shrK d o len s) o len = valAt d o len / 2 ^ s := by
  unfold shrK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    have hb := val_ofUSize_w (R := R) h.2.2
    obtain ⟨i₁, i₂, i₃⟩ := shrSelf_spec d o.toUSize (R.ofUSize s.toUSize) (by rw [hb]; exact h.2.1)
      (by rw [hb]; exact h.2.2) len.toUSize hd R.zero
    rw [e₁, e₂, hb, R.val_zero, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at i₃
    rw [e₁, e₂] at i₂
    exact ⟨⟨i₁, i₂⟩, i₃⟩
  · exact fallback _ _ _ _ hw (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (valAt_lt ..))

/-! ## Exact division -/

variable (A) in
/-- The inverse of an odd `q` modulo `2ʷ`, by six steps of Newton's iteration from `q`. -/
@[inline, expose] public def invW (q : L) : L :=
  let two := R.add R.one R.one
  let x := R.mul q (R.sub two (R.mul q q))
  let x := R.mul x (R.sub two (R.mul q x))
  let x := R.mul x (R.sub two (R.mul q x))
  let x := R.mul x (R.sub two (R.mul q x))
  let x := R.mul x (R.sub two (R.mul q x))
  R.mul x (R.sub two (R.mul q x))

variable (A) in
/--
The step of `divExactK`, like GMP's `mpn_divexact_1`: the quotient limb `t = (z - c) q⁻¹` and the
carry `⌊t q / β⌋` plus the borrow of `z - c`, with `q t + c = z + β c'`.
-/
@[inline, expose] public def divExactStep (q inv : L) (n : USize) (j : USize) (_ : j < n)
    (z c : L) : L × L :=
  let t := R.mul (R.sub z c) inv
  (t, R.add (R.mulh t q) (R.ofBool (R.ltB z c)))

omit F in
private theorem divExactStep_law (q inv : L) (hinv : LA.val (R.mul q inv) = 1) (n j : USize)
    (h : j < n) (z c : L) :
    LA.val q * LA.val (divExactStep A q inv n j h z c).1 + LA.val c =
      LA.val z + 2 ^ LA.w * LA.val (divExactStep A q inv n j h z c).2 := by
  have hB := four_le (R := R)
  have hq := LA.val_lt q; have hz := LA.val_lt z; have hc := LA.val_lt c
  have ht := LA.val_lt (R.mul (R.sub z c) inv)
  simp only [divExactStep]
  -- `t q ≡ z - c` modulo `β`.
  rw [R.val_mul] at hinv
  have hq₀ : 0 < LA.val q := by
    rcases Nat.eq_zero_or_pos (LA.val q) with e | e
    · rw [e, Nat.zero_mul, Nat.zero_mod] at hinv; exact absurd hinv (by decide)
    · exact e
  have hmod : LA.val (R.mul (R.sub z c) inv) * LA.val q % 2 ^ LA.w = LA.val (R.sub z c) := by
    rw [R.val_mul]
    have e : LA.val (R.sub z c) * LA.val inv % 2 ^ LA.w * LA.val q % 2 ^ LA.w =
        LA.val (R.sub z c) * (LA.val q * LA.val inv) % 2 ^ LA.w := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm (LA.val inv)]
    rw [e, Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt (LA.val_lt _)]
  have hsub := sub_mod_eq (B := 2 ^ LA.w) hz hc
  rw [← R.val_sub] at hsub
  have hh : LA.val (R.mulh (R.mul (R.sub z c) inv) q) < LA.val q := by
    rw [R.val_mulh, Nat.div_lt_iff_lt_mul (by lia), Nat.mul_comm (LA.val q)]
    exact Nat.mul_lt_mul_of_pos_right ht hq₀
  have hb : LA.val (R.ofBool (R.ltB z c) : L) = if LA.val z < LA.val c then 1 else 0 := by
    rw [R.val_ofBool]
    by_cases e : LA.val z < LA.val c
    · rw [ite_eq_left e, ite_eq_left ((R.ltB_iff ..).2 e)]
    · rw [ite_eq_right e, ite_eq_right (fun e' => e ((R.ltB_iff ..).1 e'))]
  rw [R.val_add, hb, R.val_mulh]
  rw [R.val_mulh] at hh
  have hdm := Nat.div_add_mod (LA.val (R.mul (R.sub z c) inv) * LA.val q) (2 ^ LA.w)
  rw [hmod] at hdm
  generalize LA.val (R.mul (R.sub z c) inv) = T at *
  generalize LA.val (R.sub z c) = S at *
  generalize LA.val q = Q at *
  generalize 2 ^ LA.w = B at *
  have : (T * Q / B + if LA.val z < LA.val c then 1 else 0) < B := by split <;> lia
  rw [Nat.mod_eq_of_lt this]
  by_cases e : LA.val z < LA.val c
  · simp only [e, ↓reduceIte] at hsub this ⊢
    grind
  · simp only [e, ↓reduceIte] at hsub this ⊢
    grind

/-- `D / q` in place, exactly, for an odd limb `q` that divides `D`: `divExact d o len q`. -/
public def divExactK (d : A) (o len q : Nat) : A :=
  let qL : L := R.ofUSize q.toUSize
  let inv := invW A qL
  if h : winOK d o len = true ∧ q < 2 ^ LA.w ∧ q < 4294967295 ∧
      R.eqB (R.mul qL inv) R.one = true then
    have hd := winOK_spec h.1
    F.foldThen len.toUSize (divExactStep A qL inv len.toUSize) d o.toUSize hd.2.2.2 0 R.zero
      fun arr _ _ => arr
  else writeNat d o len (valAt d o len / q)

public theorem divExactK_spec (d : A) (o len q : Nat) (hw : o + len ≤ LA.size d) (hq : q % 2 = 1)
    (_hqw : q < 2 ^ LA.w) (hdq : valAt d o len % q = 0) :
    Writes (divExactK d o len q) d o len ∧
      valAt (divExactK d o len q) o len = valAt d o len / q := by
  unfold divExactK
  dsimp only
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    have hqv := val_ofUSize_lt (R := R) h.2.1 h.2.2.1
    have hinv : LA.val (R.mul (R.ofUSize q.toUSize) (invW A (R.ofUSize q.toUSize))) = 1 := by
      have := (R.eqB_iff ..).1 h.2.2.2; rw [this, R.val_one]
    rw [F.foldThen_eq, foldUInPlaceThen]
    have hq₀ : 0 < q := by lia
    obtain ⟨i₁, i₀, i₂, i₃⟩ := foldUInPlace_spec1 len.toUSize
      (divExactStep A (R.ofUSize q.toUSize) (invW A (R.ofUSize q.toUSize)) len.toUSize) d o.toUSize
      (fun _ => 0) LA.val q 0 0 1 0 (fun c => LA.val c < q)
      (fun j h z c hc => by
        have hl := divExactStep_law _ _ hinv len.toUSize j h z c
        rw [hqv] at hl
        have ht := LA.val_lt (divExactStep A (R.ofUSize q.toUSize) (invW A (R.ofUSize q.toUSize))
          len.toUSize j h z c).1
        have h₁ := Nat.mul_le_mul_left q (Nat.succ_le_of_lt ht)
        generalize LA.val (divExactStep A (R.ofUSize q.toUSize) (invW A (R.ofUSize q.toUSize))
          len.toUSize j h z c).1 = T at hl ht h₁
        generalize LA.val (divExactStep A (R.ofUSize q.toUSize) (invW A (R.ofUSize q.toUSize))
          len.toUSize j h z c).2 = C at hl ⊢
        generalize 2 ^ LA.w = B at *
        refine Nat.lt_of_not_le fun hge => ?_
        have h₃ := Nat.mul_le_mul_left B hge
        rw [Nat.mul_succ] at h₁
        grind)
      (fun j h z c _ => by
        have := divExactStep_law _ _ hinv len.toUSize j h z c
        rw [hqv] at this
        lia) d o.toUSize hd 0 R.zero (by rw [R.val_zero]; exact hq₀)
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.zero_mul,
      Nat.mul_zero, R.val_zero, e₁, e₂] at i₀ i₂ i₃
    refine ⟨⟨i₁, i₂⟩, ?_⟩
    -- The carry out is a multiple of `q` below it, so zero.
    generalize valAt (foldUInPlace len.toUSize _ d o.toUSize hd 0 R.zero).1 o len = Q at i₃ ⊢
    generalize LA.val (foldUInPlace len.toUSize _ d o.toUSize hd 0 R.zero).2 = c at i₀ i₃
    have hcop : Nat.Coprime q (2 ^ (LA.w * len)) := by
      apply Nat.Coprime.pow_right
      show Nat.gcd q 2 = 1
      rw [Nat.gcd_comm, Nat.gcd_rec, hq]; rfl
    have hdvd : q ∣ 2 ^ (LA.w * len) * c := by
      have h₁ : q ∣ q * Q := Nat.dvd_mul_right q Q
      rw [i₃] at h₁
      exact (Nat.dvd_add_right (Nat.dvd_of_mod_eq_zero hdq)).1 h₁
    have hc : c = 0 := by
      rcases Nat.eq_zero_or_pos c with e | e
      · exact e
      · exact absurd (Nat.le_of_dvd e (hcop.dvd_of_dvd_mul_left hdvd)) (by lia)
    subst hc
    rw [Nat.mul_zero, Nat.add_zero] at i₃
    rw [← i₃, Nat.mul_div_cancel_left _ hq₀]
  · exact fallback _ _ _ _ hw (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (valAt_lt ..))

/-! ## Sums -/

/-- `x + y` in the `xl + 1` zeros of `z`, for `yl ≤ xl`: `sum x xo xl y yo yl` with `z` of zeros. -/
public def sumK (z x : A) (xo xl : Nat) (y : A) (yo yl : Nat) : A :=
  if h : winOK z 0 (xl + 1) = true ∧ winOK x xo xl = true then
    have hz := winOK_spec h.1
    have hx := winOK_spec h.2
    addIntoK (copyW z 0 x xo.toUSize xl.toUSize
      ⟨by have := hz.1; rw [USize.toNat_zero, hx.2.2.1]; lia,
        by have := hz.2.2.2.2; rw [hz.2.2.1] at this; rw [USize.toNat_zero, hx.2.2.1]; lia⟩
      hx.2.2.2) 0 (xl + 1) y yo yl
  else writeNat z 0 (xl + 1) (valAt x xo xl + valAt y yo yl)

public theorem sumK_spec (z x : A) (xo xl : Nat) (y : A) (yo yl : Nat) (hyl : yl ≤ xl)
    (hzs : LA.size z = xl + 1) (hz0 : ∀ i, LA.val (LA.get z i) = 0) :
    LA.size (sumK z x xo xl y yo yl) = xl + 1 ∧
      valAt (sumK z x xo xl y yo yl) 0 (xl + 1) = valAt x xo xl + valAt y yo yl := by
  have hX := valAt_lt x xo xl
  have hY := valAt_lt y yo yl
  have hfit : valAt x xo xl + valAt y yo yl < 2 ^ (LA.w * (xl + 1)) := by
    have : 2 ^ (LA.w * yl) ≤ 2 ^ (LA.w * xl) := Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left _ hyl)
    have : 2 * 2 ^ (LA.w * xl) ≤ 2 ^ (LA.w * (xl + 1)) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (by have := four_le (R := R); lia)
    lia
  unfold sumK
  split
  · rename_i h
    dsimp only
    obtain ⟨-, -, e₂, -⟩ := winOK_spec h.2
    obtain ⟨c₁, c₂, c₃⟩ := copyW_spec z 0 x xo.toUSize xl.toUSize _ (winOK_spec h.2).2.2.2
    generalize copyW z 0 x xo.toUSize xl.toUSize _ _ = c at c₁ c₂ c₃ ⊢
    rw [USize.toNat_zero, e₂, (winOK_spec h.2).2.1] at c₃
    simp only [USize.toNat_zero, Nat.zero_add, e₂] at c₂
    have hcv : valAt c 0 (xl + 1) = valAt x xo xl := by
      rw [valAt_add, c₃, valAt_one, Nat.zero_add, c₂ xl (.inr (Nat.le_refl _)), hz0, Nat.mul_zero,
        Nat.add_zero]
    obtain ⟨w₁, w₂⟩ := addIntoK_spec c 0 (xl + 1) y yo yl (by rw [c₁, hzs]; lia)
      (by rw [hcv]; exact hfit)
    refine ⟨by rw [w₁.1, c₁, hzs], by rw [w₂, hcv]⟩
  · exact ⟨by rw [size_writeNat, hzs], by rw [valAt_writeNat _ _ _ _ (by rw [hzs]; lia),
      Nat.mod_eq_of_lt hfit]⟩

end MPN.WordArray

namespace MPN.Toom

open LimbArray WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/--
The operations of `ToomOps` that depend on the limbs beyond their word operations: Karatsuba's
middle term and the products below the thresholds, which the branches compute by their own
methods, and the width, at least 32 bits. The rest of `ToomOps` are the kernels of this file.
-/
public class ToomBase (A : Type) (L : outParam Type) [LimbArray A L] where
  /-- The limbs have at least 32 bits, for the multipliers of the interpolations, up to `9¹⁰`. -/
  w_ge : 32 ≤ LimbArray.w A
  /-- Karatsuba's middle term into `d`, from the products in `t`: `mid d o k n t`. -/
  mid : A → Nat → Nat → Nat → A → A
  mid_spec : ∀ (d : A) (o k n : Nat) (t : A), o + n ≤ LimbArray.size d →
    Writes (mid d o k n t) d o n ∧
      ∀ Z₁, valAt t 0 (k + k + 2) = valAt d o (k + k) + Z₁ + valAt d (o + (k + k)) (n - (k + k)) →
        valAt d o (k + k) + 2 ^ (LimbArray.w A * k) * Z₁ +
            2 ^ (LimbArray.w A * (k + k)) * valAt d (o + (k + k)) (n - (k + k)) <
          2 ^ (LimbArray.w A * n) →
        valAt (mid d o k n t) o n = valAt d o (k + k) + 2 ^ (LimbArray.w A * k) * Z₁ +
          2 ^ (LimbArray.w A * (k + k)) * valAt d (o + (k + k)) (n - (k + k))
  /-- `x y` into the `xl + yl` limbs of `d` from `o` on: `mulBase d o x xo xl y yo yl`. -/
  mulBase : A → Nat → A → Nat → Nat → A → Nat → Nat → A
  mulBase_spec : ∀ (d : A) (o : Nat) (x : A) (xo xl : Nat) (y : A) (yo yl : Nat),
    o + (xl + yl) ≤ LimbArray.size d →
    Writes (mulBase d o x xo xl y yo yl) d o (xl + yl) ∧
      valAt (mulBase d o x xo xl y yo yl) o (xl + yl) = valAt x xo xl * valAt y yo yl
  /-- `x²` into the `2 xl` limbs of `d` from `o` on: `sqrBase d o x xo xl`. -/
  sqrBase : A → Nat → A → Nat → Nat → A
  sqrBase_spec : ∀ (d : A) (o : Nat) (x : A) (xo xl : Nat), o + (xl + xl) ≤ LimbArray.size d →
    Writes (sqrBase d o x xo xl) d o (xl + xl) ∧
      valAt (sqrBase d o x xo xl) o (xl + xl) = valAt x xo xl * valAt x xo xl

/-- The operations of the Karatsuba and Toom methods: the kernels of this file and `ToomBase`. -/
public instance toomOpsW [B : ToomBase A L] : ToomOps A L where
  w_ge := B.w_ge
  zeros := R.zeros
  size_zeros := R.size_zeros
  val_get_zeros := R.val_get_zeros
  addInto := addIntoK
  addInto_spec := addIntoK_spec
  subInto := subIntoK
  subInto_spec := subIntoK_spec
  addMulInto := addMulIntoK
  addMulInto_spec := addMulIntoK_spec
  subMulInto := subMulIntoK
  subMulInto_spec := subMulIntoK_spec
  shlTop := shlTopK
  shlTop_spec := shlTopK_spec
  shr := shrK
  shr_spec := shrK_spec
  divExact := divExactK
  divExact_spec := divExactK_spec
  zeroInto := zeroIntoK
  zeroInto_spec := zeroIntoK_spec
  sum x xo xl y yo yl := sumK (R.zeros (xl + 1)) x xo xl y yo yl
  sum_spec x xo xl y yo yl hyl := sumK_spec _ x xo xl y yo yl hyl (R.size_zeros _)
    (R.val_get_zeros _)
  mid := B.mid
  mid_spec := B.mid_spec
  mulBase := B.mulBase
  mulBase_spec := B.mulBase_spec
  sqrBase := B.sqrBase
  sqrBase_spec := B.sqrBase_spec

end MPN.Toom
