/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Kernels

/-!
# Addition and subtraction over `WordArray`

`addW z zo a ao al b bo bl` writes `A + B` into the `al + 1` limbs of `z` from `zo` on, and
`subW z zo a ao al b bo bl` writes `A - B` into its `al` limbs, for the windows `A` of `al` limbs
of `a` from `ao` and `B` of `bl ≤ al` limbs of `b` from `bo`, like GMP's `mpn_add` and `mpn_sub`:
one pass over the low `bl` limbs reading both windows (`addNStep`, `subNStep`), then one pass over
the rest of `A` with the carry or the borrow (`add1Step`, `sub1Step`), and for `addW` the carry
out into the top limb. Each checks its bounds; otherwise it writes the value of its specification
with `writeNat`, which never happens.
-/

namespace MPN.WordArray

open Toom LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-! ## Bounds -/

private theorem toNat_toUSize₃ {n : Nat} (h : n < 4294967295) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by have := USize.size_eq; lia)]

/-- The bounds of `addW` and `subW` on the arrays they read and write, from their checks. -/
public structure AddOK (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat) : Prop where
  hz : zo + al + 1 ≤ LA.size z
  hzS : LA.size z < 4294967295
  ha : ao + al ≤ LA.size a
  haS : LA.size a < 4294967295
  hb : bo + bl ≤ LA.size b
  hbS : LA.size b < 4294967295
  hba : bl ≤ al

/-- The checks of `addW` and `subW`. -/
@[inline, expose] public def addOK (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : Bool :=
  decide (zo + al + 1 ≤ LA.size z) && decide (LA.size z < 4294967295) &&
    decide (ao + al ≤ LA.size a) && decide (LA.size a < 4294967295) &&
    decide (bo + bl ≤ LA.size b) && decide (LA.size b < 4294967295) && decide (bl ≤ al)

omit R F in
public theorem addOK_spec {z : A} {zo : Nat} {a : A} {ao al : Nat} {b : A} {bo bl : Nat}
    (h : addOK z zo a ao al b bo bl = true) : AddOK z zo a ao al b bo bl := by
  simp only [addOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩

namespace AddOK

variable {z : A} {zo : Nat} {a : A} {ao al : Nat} {b : A} {bo bl : Nat}

omit R F in
public theorem e (h : AddOK z zo a ao al b bo bl) :
    zo.toUSize.toNat = zo ∧ ao.toUSize.toNat = ao ∧ bo.toUSize.toNat = bo ∧
      bl.toUSize.toNat = bl ∧ (zo + bl).toUSize.toNat = zo + bl ∧
      (ao + bl).toUSize.toNat = ao + bl ∧ (al - bl).toUSize.toNat = al - bl ∧
      (zo + al).toUSize.toNat = zo + al := by
  have := h.hz; have := h.hzS; have := h.ha; have := h.haS; have := h.hb; have := h.hbS
  have := h.hba
  exact ⟨toNat_toUSize₃ (by lia), toNat_toUSize₃ (by lia), toNat_toUSize₃ (by lia),
    toNat_toUSize₃ (by lia), toNat_toUSize₃ (by lia), toNat_toUSize₃ (by lia),
    toNat_toUSize₃ (by lia), toNat_toUSize₃ (by lia)⟩

omit R F in
public theorem of_size (h : AddOK z zo a ao al b bo bl) {z' : A} (e : LA.size z' = LA.size z) :
    AddOK z' zo a ao al b bo bl :=
  ⟨by rw [e]; exact h.hz, by rw [e]; exact h.hzS, h.ha, h.haS, h.hb, h.hbS, h.hba⟩

omit R F in
public theorem lbz (h : AddOK z zo a ao al b bo bl) : LoopBound z zo.toUSize bl.toUSize := by
  obtain ⟨e₁, -, -, e₄, -⟩ := h.e
  have := h.hz; have := h.hzS; have := h.hba; have := USize.le_size
  constructor <;> rw [e₁, e₄] <;> lia

omit R F in
public theorem lba (h : AddOK z zo a ao al b bo bl) : LoopBound a ao.toUSize bl.toUSize := by
  obtain ⟨-, e₂, -, e₄, -⟩ := h.e
  have := h.ha; have := h.haS; have := h.hba; have := USize.le_size
  constructor <;> rw [e₂, e₄] <;> lia

omit R F in
public theorem lbb (h : AddOK z zo a ao al b bo bl) : LoopBound b bo.toUSize bl.toUSize := by
  obtain ⟨-, -, e₃, e₄, -⟩ := h.e
  have := h.hb; have := h.hbS; have := USize.le_size
  constructor <;> rw [e₃, e₄] <;> lia

omit R F in
public theorem lbzt (h : AddOK z zo a ao al b bo bl) :
    LoopBound z (zo + bl).toUSize (al - bl).toUSize := by
  obtain ⟨-, -, -, -, e₅, -, e₇, -⟩ := h.e
  have := h.hz; have := h.hzS; have := h.hba; have := USize.le_size
  constructor <;> rw [e₅, e₇] <;> lia

omit R F in
public theorem lbat (h : AddOK z zo a ao al b bo bl) :
    LoopBound a (ao + bl).toUSize (al - bl).toUSize := by
  obtain ⟨-, -, -, -, -, e₆, e₇, -⟩ := h.e
  have := h.ha; have := h.haS; have := h.hba; have := USize.le_size
  constructor <;> rw [e₆, e₇] <;> lia

omit R F in
public theorem top (h : AddOK z zo a ao al b bo bl) : (zo + al).toUSize.toNat < LA.size z := by
  obtain ⟨-, -, -, -, -, -, -, e₈⟩ := h.e
  have := h.hz; rw [e₈]; lia

end AddOK

/-! ## Steps -/

variable (A) in
/-- The step of the first pass of `addW`: limb `ao + j` of `a` plus limb `bo + j` of `b`. -/
@[inline, expose] public def addNStep (a : A) (ao : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao n) (hb : LoopBound b bo n) (j : USize) (h : j < n) (_z c : L) : L × L :=
  R.addC (R.uget a (ao + j) (ha.uset_bound h)) (R.uget b (bo + j) (hb.uset_bound h)) c

variable (A) in
/-- The step of the second pass of `addW`: limb `ao + j` of `a` plus the carry. -/
@[inline, expose] public def add1Step (a : A) (ao n : USize) (ha : LoopBound a ao n) (j : USize)
    (h : j < n) (_z c : L) : L × L :=
  R.addC (R.uget a (ao + j) (ha.uset_bound h)) R.zero c

variable (A) in
/-- The step of the first pass of `subW`: limb `ao + j` of `a` minus limb `bo + j` of `b`. -/
@[inline, expose] public def subNStep (a : A) (ao : USize) (b : A) (bo n : USize)
    (ha : LoopBound a ao n) (hb : LoopBound b bo n) (j : USize) (h : j < n) (_z c : L) : L × L :=
  R.subMulB (R.uget a (ao + j) (ha.uset_bound h)) (R.uget b (bo + j) (hb.uset_bound h)) R.one c

variable (A) in
/-- The step of the second pass of `subW`: limb `ao + j` of `a` minus the borrow. -/
@[inline, expose] public def sub1Step (a : A) (ao n : USize) (ha : LoopBound a ao n) (j : USize)
    (h : j < n) (_z c : L) : L × L :=
  R.subMulB (R.uget a (ao + j) (ha.uset_bound h)) R.zero R.one c

/-! ## Addition -/

/-- The second pass of `addW` and the carry out, on the array of the first pass. -/
@[inline, expose] public def addTail (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (h : AddOK z zo a ao al b bo bl) (c : L) : A :=
  F.foldThen (al - bl).toUSize (add1Step A a (ao + bl).toUSize (al - bl).toUSize h.lbat) z
    (zo + bl).toUSize h.lbzt 0 c fun z₂ e₂ c₂ => R.uset z₂ (zo + al).toUSize c₂ (by
      rw [e₂]; exact h.top)

/-- `A + B` into the `al + 1` limbs of `z` from `zo` on, for `bl ≤ al`. -/
public def addW (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat) : A :=
  if h : addOK z zo a ao al b bo bl = true then
    have hb := addOK_spec h
    F.foldThen bl.toUSize (addNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z
      zo.toUSize hb.lbz 0 R.zero fun z₁ e₁ c => addTail z₁ zo a ao al b bo bl (hb.of_size e₁) c
  else writeNat z zo (al + 1) (valAt a ao al + valAt b bo bl)

omit R F in
/-- The split of a window at `bl`. -/
private theorem split_at (x : A) (o al bl : Nat) (h : bl ≤ al) :
    valAt x o al = valAt x o bl + 2 ^ (LA.w * bl) * valAt x (o + bl) (al - bl) := by
  rw [← valAt_add, Nat.add_sub_cancel' h]

omit R F in
private theorem pow_split (al bl : Nat) (h : bl ≤ al) :
    2 ^ (LA.w * al) = 2 ^ (LA.w * bl) * 2 ^ (LA.w * (al - bl)) := by
  rw [← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' h]

/-- The second pass of `addW`, on any array that holds the first. -/
private theorem addTail_spec (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat)
    (h : AddOK z zo a ao al b bo bl) (c : L) :
    LA.size (addTail z zo a ao al b bo bl h c) = LA.size z ∧
      (∀ i, (i < zo + bl ∨ zo + al + 1 ≤ i) →
        LA.get (addTail z zo a ao al b bo bl h c) i = LA.get z i) ∧
      valAt (addTail z zo a ao al b bo bl h c) (zo + bl) (al - bl + 1) =
        valAt a (ao + bl) (al - bl) + LA.val c := by
  obtain ⟨-, -, -, -, e₅, e₆, e₇, e₈⟩ := h.e
  have hba := h.hba
  unfold addTail
  rw [F.foldThen_eq, foldUInPlaceThen]
  obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace_spec1 (al - bl).toUSize
    (add1Step A a (ao + bl).toUSize (al - bl).toUSize h.lbat) a (ao + bl).toUSize LA.val
    (fun _ => 0) 1 0 0 0 1 (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun j hj z c _ => by
      have e := R.val_addC (R.uget a ((ao + bl).toUSize + j) (h.lbat.uset_bound hj)) R.zero c
      simp only [add1Step, R.uget_eq, R.val_zero, h.lbat.toNat_add hj] at e ⊢
      lia)
    z (zo + bl).toUSize h.lbzt 0 c trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₅, e₆, e₇, Nat.one_mul,
    Nat.zero_mul, Nat.mul_zero] at f₂ f₃
  refine ⟨by rw [R.size_uset, f₁], fun i hi => ?_, ?_⟩
  · rw [R.get_uset, e₈, ite_eq_right_iff.2 (fun e => by lia), f₂ i (by lia)]
  · rw [valAt_add, valAt_one, R.get_uset, e₈, show zo + bl + (al - bl) = zo + al by lia]
    simp only [↓reduceIte]
    rw [valAt_uset_of _ _ _ _ _ _ (by rw [e₈]; lia)]
    lia

public theorem addW_spec (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat)
    (hz : zo + al + 1 ≤ LA.size z) (hba : bl ≤ al) :
    Writes (addW z zo a ao al b bo bl) z zo (al + 1) ∧
      valAt (addW z zo a ao al b bo bl) zo (al + 1) = valAt a ao al + valAt b bo bl := by
  unfold addW
  split
  · rename_i h
    have hb := addOK_spec h
    obtain ⟨e₁, e₂, e₃, e₄, -⟩ := hb.e
    dsimp only
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace_spec2 bl.toUSize
      (addNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) a ao.toUSize b bo.toUSize
      LA.val (fun _ => 0) 1 0 0 0 0 1 1 (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun j hj z c _ => by
        have e := R.val_addC (R.uget a (ao.toUSize + j) (hb.lba.uset_bound hj))
          (R.uget b (bo.toUSize + j) (hb.lbb.uset_bound hj)) c
        simp only [addNStep, R.uget_eq, hb.lba.toNat_add hj, hb.lbb.toNat_add hj] at e ⊢
        lia)
      z zo.toUSize hb.lbz 0 R.zero trivial
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₂, e₃, e₄, Nat.one_mul,
      Nat.zero_mul, Nat.mul_zero, R.val_zero] at f₂ f₃
    obtain ⟨t₁, t₂, t₃⟩ := addTail_spec _ zo a ao al b bo bl (hb.of_size f₁) _
    refine ⟨⟨by rw [t₁, f₁], fun i hi => by rw [t₂ i (by lia), f₂ i (by lia)]⟩, ?_⟩
    -- The window: the low `bl` limbs of the first pass, then the second pass.
    have hlow : valAt (addTail _ zo a ao al b bo bl (hb.of_size f₁) _) zo bl =
        valAt (foldUInPlace bl.toUSize
          (addNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
            R.zero).1 zo bl := valAt_congr _ fun i _ _ => t₂ i (by lia)
    rw [split_at _ zo (al + 1) bl (by lia), show al + 1 - bl = al - bl + 1 by lia, hlow, t₃,
      split_at a ao al bl hba]
    generalize valAt (foldUInPlace bl.toUSize
      (addNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
        R.zero).1 zo bl = V at f₃ ⊢
    generalize LA.val (foldUInPlace bl.toUSize
      (addNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
        R.zero).2 = c at f₃ ⊢
    rw [Nat.mul_add]
    lia
  · refine ⟨writes_writeNat .., ?_⟩
    rw [valAt_writeNat z zo (al + 1) _ hz, Nat.mod_eq_of_lt]
    have := valAt_lt a ao al
    have : valAt b bo bl < 2 ^ (LA.w * al) := Nat.lt_of_lt_of_le (valAt_lt ..)
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hba))
    have := four_le (R := R)
    rw [Nat.mul_succ, Nat.pow_add]
    have := Nat.mul_le_mul_left (2 ^ (LA.w * al)) (show 2 ≤ 2 ^ LA.w by lia)
    lia

@[simp] public theorem size_addW (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : LA.size (addW z zo a ao al b bo bl) = LA.size z := by
  by_cases h : addOK z zo a ao al b bo bl = true
  · have hb := addOK_spec h
    exact (addW_spec z zo a ao al b bo bl hb.hz hb.hba).1.1
  · unfold addW; rw [dite_eq_right h]; exact size_writeNat ..

/-! ## Subtraction -/

/-- The second pass of `subW`, on the array of the first pass. -/
@[inline, expose] public def subTail (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (h : AddOK z zo a ao al b bo bl) (c : L) : A :=
  F.foldThen (al - bl).toUSize (sub1Step A a (ao + bl).toUSize (al - bl).toUSize h.lbat) z
    (zo + bl).toUSize h.lbzt 0 c fun z₂ _ _ => z₂

/-- `A - B` into the `al` limbs of `z` from `zo` on, for `bl ≤ al` and `B ≤ A`. -/
public def subW (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat) : A :=
  if h : addOK z zo a ao al b bo bl = true then
    have hb := addOK_spec h
    F.foldThen bl.toUSize (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z
      zo.toUSize hb.lbz 0 R.b0 fun z₁ e₁ c => subTail z₁ zo a ao al b bo bl (hb.of_size e₁) c
  else writeNat z zo al (valAt a ao al - valAt b bo bl)

/-- The second pass of `subW`, on any array that holds the first. -/
private theorem subTail_spec (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat)
    (h : AddOK z zo a ao al b bo bl) (c : L) :
    ∃ c₂, LA.size (subTail z zo a ao al b bo bl h c) = LA.size z ∧
      (∀ i, (i < zo + bl ∨ zo + al ≤ i) →
        LA.get (subTail z zo a ao al b bo bl h c) i = LA.get z i) ∧
      valAt (subTail z zo a ao al b bo bl h c) (zo + bl) (al - bl) + LA.val (R.unB c) =
        valAt a (ao + bl) (al - bl) + 2 ^ (LA.w * (al - bl)) * c₂ := by
  obtain ⟨-, -, -, -, e₅, e₆, e₇, -⟩ := h.e
  have hba := h.hba
  unfold subTail
  rw [F.foldThen_eq, foldUInPlaceThen]
  obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace_spec1 (al - bl).toUSize
    (sub1Step A a (ao + bl).toUSize (al - bl).toUSize h.lbat) a (ao + bl).toUSize (fun _ => 0)
    (fun c => LA.val (R.unB c)) 1 0 0 0 1 (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun j hj z c _ => by
      have e := R.val_subMulB (R.uget a ((ao + bl).toUSize + j) (h.lbat.uset_bound hj)) R.zero
        R.one c
      simp only [sub1Step, R.uget_eq, R.val_zero, Nat.zero_mul, Nat.add_zero,
        h.lbat.toNat_add hj] at e ⊢
      lia)
    z (zo + bl).toUSize h.lbzt 0 c trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₅, e₆, e₇, Nat.one_mul,
    Nat.zero_mul, Nat.mul_zero] at f₂ f₃
  exact ⟨LA.val (R.unB (foldUInPlace (al - bl).toUSize
    (sub1Step A a (ao + bl).toUSize (al - bl).toUSize h.lbat) z (zo + bl).toUSize h.lbzt 0 c).2),
    f₁, fun i hi => f₂ i (by lia), by lia⟩

public theorem subW_spec (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A) (bo bl : Nat)
    (hz : zo + al ≤ LA.size z) (hba : bl ≤ al) (hle : valAt b bo bl ≤ valAt a ao al) :
    Writes (subW z zo a ao al b bo bl) z zo al ∧
      valAt (subW z zo a ao al b bo bl) zo al = valAt a ao al - valAt b bo bl := by
  unfold subW
  split
  · rename_i h
    have hb := addOK_spec h
    obtain ⟨e₁, e₂, e₃, e₄, -⟩ := hb.e
    dsimp only
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace_spec2 bl.toUSize
      (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) a ao.toUSize b bo.toUSize
      (fun _ => 0) (fun c => LA.val (R.unB c)) 1 0 0 1 0 1 0 (fun _ => True)
      (fun _ _ _ _ _ => trivial)
      (fun j hj z c _ => by
        have e := R.val_subMulB (R.uget a (ao.toUSize + j) (hb.lba.uset_bound hj))
          (R.uget b (bo.toUSize + j) (hb.lbb.uset_bound hj)) R.one c
        simp only [subNStep, R.uget_eq, R.val_one, Nat.mul_one, hb.lba.toNat_add hj,
          hb.lbb.toNat_add hj] at e ⊢
        lia)
      z zo.toUSize hb.lbz 0 R.b0 trivial
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₂, e₃, e₄, Nat.one_mul,
      Nat.zero_mul, Nat.mul_zero, R.val_unB_b0] at f₂ f₃
    obtain ⟨c₂, t₁, t₂, t₃⟩ := subTail_spec _ zo a ao al b bo bl (hb.of_size f₁)
      (foldUInPlace bl.toUSize (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z
        zo.toUSize hb.lbz 0 R.b0).2
    generalize hFc : (foldUInPlace bl.toUSize
      (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
        R.b0).2 = Fc at f₃ t₁ t₂ t₃ ⊢
    refine ⟨⟨by rw [t₁, f₁], fun i hi => by rw [t₂ i (by lia), f₂ i (by lia)]⟩, ?_⟩
    have hlow : valAt (subTail _ zo a ao al b bo bl (hb.of_size f₁) Fc) zo bl =
        valAt (foldUInPlace bl.toUSize
          (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
            R.b0).1 zo bl := valAt_congr _ fun i _ _ => t₂ i (by lia)
    have hV := valAt_lt (subTail _ zo a ao al b bo bl (hb.of_size f₁) Fc) zo al
    rw [split_at _ zo al bl hba, hlow] at hV ⊢
    rw [split_at a ao al bl hba] at hle ⊢
    rw [pow_split al bl hba] at hV
    generalize valAt (subTail _ zo a ao al b bo bl (hb.of_size f₁) Fc) (zo + bl) (al - bl) = V₂
      at t₃ hV ⊢
    generalize valAt (foldUInPlace bl.toUSize
      (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
        R.b0).1 zo bl = V₁ at f₃ hV ⊢
    generalize LA.val (R.unB Fc) = c at f₃ t₃
    have hV₁ := valAt_lt (foldUInPlace bl.toUSize
      (subNStep A a ao.toUSize b bo.toUSize bl.toUSize hb.lba hb.lbb) z zo.toUSize hb.lbz 0
        R.b0).1 zo bl
    -- No borrow out: the difference fits.
    generalize 2 ^ (LA.w * bl) = P at *
    generalize 2 ^ (LA.w * (al - bl)) = Q at *
    generalize valAt a ao bl = Al at *
    generalize valAt a (ao + bl) (al - bl) = Ah at *
    generalize valAt b bo bl = Bv at *
    have hc₂ : c₂ = 0 := by
      rcases Nat.eq_zero_or_pos c₂ with e | e
      · exact e
      · exfalso
        have h₁ : P * Q ≤ P * (Q * c₂) := Nat.mul_le_mul_left P (Nat.le_mul_of_pos_right Q e)
        have h₂ : P * (V₂ + c) = P * (Ah + Q * c₂) := by rw [t₃]
        grind
    subst hc₂
    have h₃ : P * V₂ + P * c = P * Ah := by rw [← Nat.mul_add, t₃, Nat.mul_zero, Nat.add_zero]
    lia
  · refine ⟨writes_writeNat .., ?_⟩
    rw [valAt_writeNat _ _ _ _ hz, Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (valAt_lt ..)

@[simp] public theorem size_subW (z : A) (zo : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : LA.size (subW z zo a ao al b bo bl) = LA.size z := by
  unfold subW
  split
  · dsimp only
    rw [F.foldThen_eq, foldUInPlaceThen]
    unfold subTail
    rw [F.foldThen_eq, foldUInPlaceThen, size_foldUInPlace, size_foldUInPlace]
  · exact size_writeNat ..

end MPN.WordArray
