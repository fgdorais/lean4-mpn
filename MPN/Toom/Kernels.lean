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
public theorem bound_le {d : A} {o len n : USize} (h : LoopBound d o len)
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

/--
`D - S v` for a limb `v`, with `S` the window of `sl` limbs at `so` of the same array: one pass
of `fold2Then`, which reads `S` from the array it writes, then the borrow propagated.
-/
@[expose, specialize]
public def subMulWinK (d : A) (o len so sl v : Nat) : A :=
  if h : winOK d o len = true ∧ winOK d so sl = true ∧ sl ≤ len ∧ v < 2 ^ LA.w ∧
      v < 4294967295 then
    have hd := winOK_spec h.1
    have hs := winOK_spec h.2.1
    have hsl : sl.toUSize.toNat ≤ len.toUSize.toNat := by rw [hs.2.2.1, hd.2.2.1]; exact h.2.2.1
    F.fold2Then sl.toUSize (fun _ _ z y c => R.subMulB z y (R.ofUSize v.toUSize) c) d o.toUSize
      o.toUSize so.toUSize (bound_le hd.2.2.2 hsl) (bound_le hd.2.2.2 hsl)
      (by rw [hs.2.2.1] at hs; exact ⟨by have := hs.2.2.2.1; lia, hs.2.2.2.2⟩) 0 R.b0
      fun arr ha c =>
        (FFT.decrAt arr o.toUSize len.toUSize (hd.2.2.2.of_size ha) sl.toUSize (R.unB c)).1
  else writeNat d o len (valAt d o len - valAt d so sl * v)

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

public theorem subMulWinK_spec (d : A) (o len so sl v : Nat) (hw : o + len ≤ LA.size d)
    (_hsw : so + sl ≤ LA.size d) (hds : o + len ≤ so ∨ so + sl ≤ o) (hsl : sl ≤ len)
    (hvw : v < 2 ^ LA.w) (hv : valAt d so sl * v ≤ valAt d o len) :
    Writes (subMulWinK d o len so sl v) d o len ∧
      valAt (subMulWinK d o len so sl v) o len = valAt d o len - valAt d so sl * v := by
  unfold subMulWinK
  split
  · rename_i h
    obtain ⟨-, e₁, e₂, hd⟩ := winOK_spec h.1
    obtain ⟨-, e₃, e₄, hs⟩ := winOK_spec h.2.1
    rw [fold2Then_eq']
    obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace2_spec sl.toUSize
      (fun _ _ z y c => R.subMulB z y (R.ofUSize v.toUSize) c) (fun _ => 0)
      (fun c => LA.val (R.unB c)) 0 (LA.val (R.ofUSize v.toUSize : L)) 1 0 (fun _ => True)
      (fun _ _ _ _ _ _ => trivial)
      (fun _ _ z y c _ => by
        have := R.val_subMulB z y (R.ofUSize v.toUSize) c
        lia) d o.toUSize o.toUSize so.toUSize _ _ _ (by lia) (by rw [e₁, e₃, e₄]; lia) 0 R.b0
      trivial
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₃, e₄,
      val_ofUSize_lt hvw h.2.2.2.2, R.val_unB_b0, Nat.zero_mul, Nat.mul_zero, Nat.one_mul]
      at f₂ f₃
    exact borrow_pass d o len sl _ _ _ hsl _ _ _ e₁ e₂ e₄ f₁ f₂ (by rw [Nat.mul_comm] at f₃; lia)
      hv _
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

/-! ## Three windows at once -/

/--
One limb of `Dᵢ - (S + T v)`: `z - (x + y v) - c` modulo `2ʷ` and the borrow out, at most `v + 1`,
where `y` is `0` past the `tl` limbs of `T`.
-/
@[inline, expose] public def lin3Step (s : A) (so to tl n : USize) (hs : LoopBound s so n)
    (ht : LoopBound s to tl) (v : L) (j : USize) (h : j < n) (z c : L) : L × L :=
  let x := R.uget s (so + j) (hs.uset_bound h)
  let y := if h' : j < tl then R.uget s (to + j) (ht.uset_bound h') else R.zero
  let p := R.mulAdd2 y v x c
  let q := R.subC z p.1 R.zero
  (q.1, R.add p.2 q.2)

/-- `FFT.decrAt` from limb `j` of a window given by its `Nat` bounds. -/
@[inline, expose] public def decrWin (d : A) (o len j : Nat) (c : L) : A :=
  if h : winOK d o len = true then
    (FFT.decrAt d o.toUSize len.toUSize (winOK_spec h).2.2.2 j.toUSize c).1
  else d

/-- `Dᵢ - (S + T vᵢ)` in three windows of `d` in one pass, and the three borrows above `S`. -/
public def sub3LinK (d : A) (o₁ o₂ o₃ len : Nat) (s : A) (so sl to tl v₁ v₂ v₃ : Nat) : A :=
  if h : winOK d o₁ len = true ∧ winOK d o₂ len = true ∧ winOK d o₃ len = true ∧
      winOK s so sl = true ∧ winOK s to tl = true ∧ sl ≤ len ∧ tl ≤ sl ∧ v₁ + 1 < 2 ^ LA.w ∧
      v₁ < 4294967295 ∧ v₂ + 1 < 2 ^ LA.w ∧ v₂ < 4294967295 ∧ v₃ + 1 < 2 ^ LA.w ∧
      v₃ < 4294967295 then
    have h₁ := winOK_spec h.1
    have h₂ := winOK_spec h.2.1
    have h₃ := winOK_spec h.2.2.1
    have hs := winOK_spec h.2.2.2.1
    have ht := winOK_spec h.2.2.2.2.1
    have hsl : sl.toUSize.toNat ≤ len.toUSize.toNat := by
      rw [hs.2.2.1, h₁.2.2.1]; exact h.2.2.2.2.2.1
    F.fold3Then sl.toUSize
      (lin3Step s so.toUSize to.toUSize tl.toUSize sl.toUSize hs.2.2.2 ht.2.2.2
        (R.ofUSize v₁.toUSize))
      (lin3Step s so.toUSize to.toUSize tl.toUSize sl.toUSize hs.2.2.2 ht.2.2.2
        (R.ofUSize v₂.toUSize))
      (lin3Step s so.toUSize to.toUSize tl.toUSize sl.toUSize hs.2.2.2 ht.2.2.2
        (R.ofUSize v₃.toUSize))
      d o₁.toUSize o₂.toUSize o₃.toUSize (bound_le h₁.2.2.2 hsl)
      (bound_le h₂.2.2.2 (by rw [h₂.2.2.1, ← h₁.2.2.1]; exact hsl))
      (bound_le h₃.2.2.2 (by rw [h₃.2.2.1, ← h₁.2.2.1]; exact hsl)) 0 R.zero R.zero R.zero
      fun arr _ c₁ c₂ c₃ =>
        decrWin (decrWin (decrWin arr o₁ len sl c₁) o₂ len sl c₂) o₃ len sl c₃
  else
    let S := valAt s so sl
    let T := valAt s to tl
    let d := writeNat d o₁ len (valAt d o₁ len - (S + T * v₁))
    let d := writeNat d o₂ len (valAt d o₂ len - (S + T * v₂))
    writeNat d o₃ len (valAt d o₃ len - (S + T * v₃))

omit F in
/-- The law of `lin3Step`, with its borrow at most `v + 1`. -/
private theorem lin3Step_law (s : A) (so to tl n : USize) (hs : LoopBound s so n)
    (ht : LoopBound s to tl) (v : Nat) (hv : v + 1 < 2 ^ LA.w) (hv' : v < 4294967295) (j : USize)
    (h : j < n) (z c : L) (hc : LA.val c ≤ v + 1) :
    LA.val (lin3Step s so to tl n hs ht (R.ofUSize v.toUSize) j h z c).2 ≤ v + 1 ∧
      LA.val (lin3Step s so to tl n hs ht (R.ofUSize v.toUSize) j h z c).1 +
          (LA.val (LA.get s (so.toNat + j.toNat)) + v *
            (if j.toNat < tl.toNat then LA.val (LA.get s (to.toNat + j.toNat)) else 0)) +
          LA.val c =
        LA.val z + 2 ^ LA.w * LA.val (lin3Step s so to tl n hs ht (R.ofUSize v.toUSize) j h z c).2 := by
  have ev := val_ofUSize_lt (R := R) (v := v) (by lia) hv'
  have hx : R.uget s (so + j) (hs.uset_bound h) = LA.get s (so.toNat + j.toNat) := by
    rw [R.uget_eq, hs.toNat_add h]
  have hy : LA.val (if h' : j < tl then R.uget s (to + j) (ht.uset_bound h') else R.zero) =
      if j.toNat < tl.toNat then LA.val (LA.get s (to.toNat + j.toNat)) else 0 := by
    by_cases h' : j < tl
    · have e := USize.lt_iff_toNat_lt.1 h'
      simp only [h', e, ↓reduceDIte, ↓reduceIte, R.uget_eq, ht.toNat_add h']
    · have e : ¬ j.toNat < tl.toNat := fun e => h' (USize.lt_iff_toNat_lt.2 e)
      simp only [h', e, ↓reduceDIte, ↓reduceIte, R.val_zero]
  simp only [lin3Step]
  rw [← hy, ← hx]
  generalize (if h' : j < tl then R.uget s (to + j) (ht.uset_bound h') else R.zero) = y
  generalize R.uget s (so + j) (hs.uset_bound h) = x
  have m := R.val_mulAdd2 y (R.ofUSize v.toUSize) x c
  generalize R.mulAdd2 y (R.ofUSize v.toUSize) x c = p at m ⊢
  have sc := R.val_subC z p.1 R.zero
  generalize R.subC z p.1 R.zero = q at sc ⊢
  rw [R.val_add]
  rw [R.val_zero, ev] at *
  have hW := R.four_le
  have lx := LA.val_lt x
  have ly := LA.val_lt y
  have lz := LA.val_lt z
  have lp := LA.val_lt p.1
  have lq := LA.val_lt q.1
  generalize 2 ^ LA.w = W at *
  generalize LA.val p.1 = lo at *
  generalize LA.val p.2 = hi at *
  generalize LA.val q.1 = o at *
  generalize LA.val q.2 = bit at *
  have hyv : LA.val y * v + v ≤ W * v := by
    have := Nat.mul_le_mul_right v (show LA.val y + 1 ≤ W by lia)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have hhi : hi ≤ v + 1 :=
    Nat.le_of_mul_le_mul_left (show W * hi ≤ W * (v + 1) by rw [Nat.mul_succ]; lia) (by lia)
  have hbit : bit < 2 := Nat.lt_of_mul_lt_mul_left (show W * bit < W * 2 by lia)
  have hsum : hi + bit ≤ v + 1 := by
    rcases Nat.lt_or_ge hi (v + 1) with e | e
    · lia
    · have e' : hi = v + 1 := by lia
      subst e'
      have : lo = 0 := by rw [Nat.mul_succ] at m; lia
      subst this
      have : bit < 1 := Nat.lt_of_mul_lt_mul_left (show W * bit < W * 1 by lia)
      lia
  rw [Nat.mod_eq_of_lt (by lia : hi + bit < W)]
  refine ⟨hsum, ?_⟩
  rw [Nat.mul_add, Nat.mul_comm v]
  lia

omit F in
/--
The borrow pass of a window, after a first pass over its low `sl` limbs whose value plus `S` is
the low part of `D` and the borrow `c`, and whose high limbs are those of `D`.
-/
private theorem borrow_win (X D : A) (o len sl Sv : Nat) (c : L) (hsl : sl ≤ len)
    (hw : winOK X o len = true)
    (a₃ : valAt X o sl + Sv = valAt D o sl + 2 ^ (LA.w * sl) * LA.val c)
    (hhigh : valAt X (o + sl) (len - sl) = valAt D (o + sl) (len - sl))
    (hv : Sv ≤ valAt D o len) :
    LA.size (decrWin X o len sl c) = LA.size X ∧
      (∀ i, (i < o ∨ o + len ≤ i) → LA.get (decrWin X o len sl c) i = LA.get X i) ∧
      valAt (decrWin X o len sl c) o len = valAt D o len - Sv := by
  obtain ⟨-, e₁, e₂, hb⟩ := winOK_spec hw
  have e₄ : sl.toUSize.toNat = sl := by
    rw [← e₂] at hsl; simp only [winOK, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact toNat_toUSize' (by lia)
  unfold decrWin
  simp only [hw, ↓reduceDIte]
  obtain ⟨b₁, b₂, b₃⟩ := FFT.decrAt_spec X o.toUSize len.toUSize (winOK_spec hw).2.2.2 sl.toUSize c
  generalize FFT.decrAt X o.toUSize len.toUSize (winOK_spec hw).2.2.2 sl.toUSize c = q at b₁ b₂ b₃ ⊢
  rw [e₁, e₂, e₄] at b₂ b₃
  refine ⟨b₁, fun i hi => b₂ i (by lia), ?_⟩
  have hlow : valAt q.1 o sl = valAt X o sl :=
    valAt_congr _ fun i _ hi => b₂ i (.inl (by lia))
  have hsplit : ∀ x : A,
      valAt x o len = valAt x o sl + 2 ^ (LA.w * sl) * valAt x (o + sl) (len - sl) := by
    intro x; rw [← valAt_add, Nat.add_sub_cancel' hsl]
  have hq := valAt_lt q.1 o len
  rw [hsplit q.1, hlow] at hq ⊢
  rw [hsplit D] at hv ⊢
  rw [hhigh] at b₃
  have hpow : 2 ^ (LA.w * len) = 2 ^ (LA.w * sl) * 2 ^ (LA.w * (len - sl)) := by
    rw [← Nat.pow_add]; congr 1; rw [← Nat.mul_add, Nat.add_sub_cancel' hsl]
  rw [hpow] at hq
  generalize valAt q.1 (o + sl) (len - sl) = Qh at b₃ hq ⊢
  generalize valAt D (o + sl) (len - sl) = Dh at b₃ hv ⊢
  generalize valAt X o sl = Pl at a₃ hq ⊢
  generalize valAt D o sl = Dl at a₃ hv ⊢
  generalize LA.val q.2 = c₂ at b₃
  generalize LA.val c = c₁ at a₃ b₃
  generalize 2 ^ (LA.w * sl) = P at *
  generalize 2 ^ (LA.w * (len - sl)) = H at *
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

public theorem sub3LinK_spec (d : A) (o₁ o₂ o₃ len : Nat) (s : A) (so sl to tl v₁ v₂ v₃ : Nat)
    (h₁ : o₁ + len ≤ LA.size d) (h₂ : o₂ + len ≤ LA.size d) (h₃ : o₃ + len ≤ LA.size d)
    (h₁₂ : o₁ + len ≤ o₂) (h₂₃ : o₂ + len ≤ o₃)
    (hb₁ : valAt s so sl + valAt s to tl * v₁ ≤ valAt d o₁ len)
    (hb₂ : valAt s so sl + valAt s to tl * v₂ ≤ valAt d o₂ len)
    (hb₃ : valAt s so sl + valAt s to tl * v₃ ≤ valAt d o₃ len) :
    LA.size (sub3LinK d o₁ o₂ o₃ len s so sl to tl v₁ v₂ v₃) = LA.size d ∧
      (∀ i, (i < o₁ ∨ o₁ + len ≤ i) → (i < o₂ ∨ o₂ + len ≤ i) → (i < o₃ ∨ o₃ + len ≤ i) →
        LA.get (sub3LinK d o₁ o₂ o₃ len s so sl to tl v₁ v₂ v₃) i = LA.get d i) ∧
      valAt (sub3LinK d o₁ o₂ o₃ len s so sl to tl v₁ v₂ v₃) o₁ len =
        valAt d o₁ len - (valAt s so sl + valAt s to tl * v₁) ∧
      valAt (sub3LinK d o₁ o₂ o₃ len s so sl to tl v₁ v₂ v₃) o₂ len =
        valAt d o₂ len - (valAt s so sl + valAt s to tl * v₂) ∧
      valAt (sub3LinK d o₁ o₂ o₃ len s so sl to tl v₁ v₂ v₃) o₃ len =
        valAt d o₃ len - (valAt s so sl + valAt s to tl * v₃) := by
  have hW := R.four_le
  unfold sub3LinK
  split
  · rename_i h
    have k₁ := h.1
    have k₂ := h.2.1
    have k₃ := h.2.2.1
    have ks := h.2.2.2.1
    have kt := h.2.2.2.2.1
    have hsl : sl ≤ len := h.2.2.2.2.2.1
    have htl : tl ≤ sl := h.2.2.2.2.2.2.1
    have hw₁ := h.2.2.2.2.2.2.2.1
    have hw₁' := h.2.2.2.2.2.2.2.2.1
    have hw₂ := h.2.2.2.2.2.2.2.2.2.1
    have hw₂' := h.2.2.2.2.2.2.2.2.2.2.1
    have hw₃ := h.2.2.2.2.2.2.2.2.2.2.2.1
    have hw₃' := h.2.2.2.2.2.2.2.2.2.2.2.2
    obtain ⟨-, e₁, eL, -⟩ := winOK_spec k₁
    obtain ⟨-, e₂, -, -⟩ := winOK_spec k₂
    obtain ⟨-, e₃, -, -⟩ := winOK_spec k₃
    obtain ⟨-, es, esl, -⟩ := winOK_spec ks
    obtain ⟨-, et, etl, -⟩ := winOK_spec kt
    rw [F.fold3Then_eq, foldUInPlace3Then]
    let E : Nat → Nat → Nat := fun v i => LA.val (LA.get s (so.toUSize.toNat + i)) +
      v * (if i < tl.toUSize.toNat then LA.val (LA.get s (to.toUSize.toNat + i)) else 0)
    obtain ⟨f₀, -, -, -, f₁, f₂, f₃, f₄⟩ := foldUInPlace3_spec sl.toUSize _ _ _ (E v₁) (E v₂) (E v₃)
      (fun c => LA.val c) (fun c => LA.val c) (fun c => LA.val c)
      (fun c => LA.val c ≤ v₁ + 1) (fun c => LA.val c ≤ v₂ + 1) (fun c => LA.val c ≤ v₃ + 1)
      (fun j h z c hc => (lin3Step_law s _ _ _ _ _ _ v₁ hw₁ hw₁' j h z c hc).1)
      (fun j h z c hc => (lin3Step_law s _ _ _ _ _ _ v₂ hw₂ hw₂' j h z c hc).1)
      (fun j h z c hc => (lin3Step_law s _ _ _ _ _ _ v₃ hw₃ hw₃' j h z c hc).1)
      (fun j h z c hc => (lin3Step_law s _ _ _ _ _ _ v₁ hw₁ hw₁' j h z c hc).2)
      (fun j h z c hc => (lin3Step_law s _ _ _ _ _ _ v₂ hw₂ hw₂' j h z c hc).2)
      (fun j h z c hc => (lin3Step_law s _ _ _ _ _ _ v₃ hw₃ hw₃' j h z c hc).2)
      d o₁.toUSize o₂.toUSize o₃.toUSize _ _ _ (by rw [e₁, e₂, esl]; lia)
      (by rw [e₁, e₃, esl]; lia) (by rw [e₂, e₃, esl]; lia) 0 R.zero R.zero R.zero
      (by rw [R.val_zero]; lia) (by rw [R.val_zero]; lia) (by rw [R.val_zero]; lia)
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₂, e₃, esl, R.val_zero]
      at f₁ f₂ f₃ f₄
    have hE : ∀ v, wsum LA.w (E v) 0 sl = valAt s so sl + valAt s to tl * v := by
      intro v
      simp only [E]
      rw [wsum_add_mul LA.w (fun i => LA.val (LA.get s (so.toUSize.toNat + i)))
        (fun i => if i < tl.toUSize.toNat then LA.val (LA.get s (to.toUSize.toNat + i)) else 0),
        wsum_get, wsum_pad _ _ _ _ _ (by rw [etl]; lia), es, et, etl, Nat.add_zero, Nat.add_zero,
        Nat.sub_zero, Nat.mul_comm v]
    rw [hE] at f₂ f₃ f₄
    generalize foldUInPlace3 sl.toUSize _ _ _ d o₁.toUSize o₂.toUSize o₃.toUSize _ _ _ 0
      R.zero R.zero R.zero = X at f₀ f₁ f₂ f₃ f₄ ⊢
    have ok : ∀ Y : A, LA.size Y = LA.size d → ∀ o, winOK d o len = true → winOK Y o len = true :=
      fun Y hY o h => by unfold winOK at h ⊢; rw [hY]; exact h
    have hhigh : ∀ o, (o = o₁ ∨ o = o₂ ∨ o = o₃) →
        valAt X.1 (o + sl) (len - sl) = valAt d (o + sl) (len - sl) := by
      intro o ho
      exact valAt_congr _ fun i _ _ => f₁ i (by lia) (by lia) (by lia)
    obtain ⟨y₁, y₂, y₃⟩ := borrow_win X.1 d o₁ len sl _ X.2.1 hsl (ok _ f₀ _ k₁) (by lia)
      (hhigh o₁ (.inl rfl)) hb₁
    generalize decrWin X.1 o₁ len sl X.2.1 = Y₁ at y₁ y₂ y₃ ⊢
    obtain ⟨z₁, z₂, z₃⟩ := borrow_win Y₁ d o₂ len sl _ X.2.2.1 hsl (ok _ (y₁.trans f₀) _ k₂)
      (by rw [show valAt Y₁ o₂ sl = valAt X.1 o₂ sl from
            valAt_congr _ fun i _ _ => y₂ i (by lia)]; lia)
      ((valAt_congr _ fun i _ _ => y₂ i (by lia)).trans (hhigh o₂ (.inr (.inl rfl)))) hb₂
    generalize decrWin Y₁ o₂ len sl X.2.2.1 = Y₂ at z₁ z₂ z₃ ⊢
    obtain ⟨u₁, u₂, u₃⟩ := borrow_win Y₂ d o₃ len sl _ X.2.2.2 hsl
      (ok _ (z₁.trans (y₁.trans f₀)) _ k₃)
      (by rw [show valAt Y₂ o₃ sl = valAt X.1 o₃ sl from
            valAt_congr _ fun i _ _ => (z₂ i (by lia)).trans (y₂ i (by lia))]; lia)
      ((valAt_congr _ fun i _ _ => (z₂ i (by lia)).trans (y₂ i (by lia))).trans
        (hhigh o₃ (.inr (.inr rfl)))) hb₃
    generalize decrWin Y₂ o₃ len sl X.2.2.2 = Y₃ at u₁ u₂ u₃ ⊢
    refine ⟨u₁.trans (z₁.trans (y₁.trans f₀)), fun i hi₁ hi₂ hi₃ => ?_, ?_, ?_, u₃⟩
    · rw [u₂ i hi₃, z₂ i hi₂, y₂ i hi₁, f₁ i (by lia) (by lia) (by lia)]
    · rw [← y₃]
      exact valAt_congr _ fun i _ _ => (u₂ i (by lia)).trans (z₂ i (by lia))
    · rw [← z₃]
      exact valAt_congr _ fun i _ _ => u₂ i (by lia)
  · dsimp only
    have b : ∀ (x : A) o (y : Nat), valAt x o len - y < 2 ^ (LA.w * len) :=
      fun x o y => Nat.lt_of_le_of_lt (Nat.sub_le _ _) (valAt_lt ..)
    obtain ⟨w₁, v₁e⟩ := fallback d o₁ len _ h₁ (b d o₁ (valAt s so sl + valAt s to tl * v₁))
    generalize writeNat d o₁ len _ = D₁ at w₁ v₁e ⊢
    obtain ⟨w₂, v₂e⟩ := fallback D₁ o₂ len _ (by rw [w₁.1]; exact h₂)
      (b D₁ o₂ (valAt s so sl + valAt s to tl * v₂))
    have e₂ : valAt D₁ o₂ len = valAt d o₂ len := w₁.valAt_eq (by lia)
    have e₃ : valAt D₁ o₃ len = valAt d o₃ len := w₁.valAt_eq (by lia)
    generalize writeNat D₁ o₂ len _ = D₂ at w₂ v₂e ⊢
    rw [e₂] at v₂e
    obtain ⟨w₃, v₃e⟩ := fallback D₂ o₃ len _ (by rw [w₂.1, w₁.1]; exact h₃)
      (b D₂ o₃ (valAt s so sl + valAt s to tl * v₃))
    generalize writeNat D₂ o₃ len _ = D₃ at w₃ v₃e ⊢
    rw [w₂.valAt_eq (by lia), e₃] at v₃e
    refine ⟨w₃.1.trans (w₂.1.trans w₁.1), fun i hi₁ hi₂ hi₃ => ?_, ?_, ?_, v₃e⟩
    · rw [w₃.2 i hi₃, w₂.2 i hi₂, w₁.2 i hi₁]
    · rw [w₃.valAt_eq (by lia), w₂.valAt_eq (by lia), v₁e]
    · rw [w₃.valAt_eq (by lia), v₂e]

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
  subMulWin := subMulWinK
  subMulWin_spec d o len so sl v hw hsw hds hsl hvw hv := subMulWinK_spec d o len so sl v hw hsw hds hsl hvw hv
  sub3Lin := sub3LinK
  sub3Lin_spec := sub3LinK_spec
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
