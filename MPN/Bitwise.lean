/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Shift
public import MPN.LinComb

/-!
# Bits of windows of limbs

`log2W a o n` is `Nat.log2` of the `n` limbs of `a` from `o`, from the top nonzero limb down, which
for trimmed limbs is the top one; `bitW f a b r n` writes `f` of the limbs of `a` and `b`, zero past
their ends (`LinComb.limbU`), into the first `n` limbs of `r`, in one in-place fold: with `f` the
instance's `land`, `lor` or `xor`, the value is the bitwise operation on the values (`valAt_bitW`);
and `ltW a b n` compares, from the top limb down.
-/

namespace MPN

namespace WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-! ## Base-two logarithm -/

omit F in
public theorem pos_of_ne {j : USize} (hj : ¬j = 0) : 0 < j := by
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  rw [USize.lt_iff_toNat_lt]; simp; lia

/-- `Nat.log2` of limbs `o` to `o + j - 1` of `a`, from the top nonzero limb down. -/
@[expose, specialize] public def log2W (a : A) (o j : USize) (h : LoopBound a o j) : Nat :=
  if hj : j = 0 then 0
  else
    let x := R.uget a (o + (j - 1)) (h.uset_bound (pred_lt' (pos_of_ne hj)))
    if R.isZero x then log2W a o (j - 1) (bound_pred h (pos_of_ne hj))
    else LA.w * (j - 1).toNat + R.log2 x
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

/-- `log2` of a value with its top limb `x ≠ 0` above `e` bits. -/
private theorem log2_top {V x e : Nat} (hV : V < 2 ^ e) (hx : x ≠ 0) :
    Nat.log2 (V + 2 ^ e * x) = e + Nat.log2 x := by
  have h₁ := Nat.log2_self_le hx
  have h₂ := Nat.lt_log2_self (n := x)
  have hpos : V + 2 ^ e * x ≠ 0 := by
    have := Nat.two_pow_pos e
    have := Nat.mul_le_mul_left (2 ^ e) (show 1 ≤ x by lia)
    lia
  rw [Nat.log2_eq_iff hpos]
  rw [Nat.pow_add, Nat.add_assoc, Nat.pow_add]
  have h₃ := Nat.mul_le_mul_left (2 ^ e) h₁
  have h₄ := Nat.mul_le_mul_left (2 ^ e) (show x + 1 ≤ 2 ^ (Nat.log2 x + 1) from h₂)
  rw [Nat.pow_add] at h₄
  constructor
  · lia
  · rw [Nat.mul_add, Nat.mul_one] at h₄
    lia

omit F in
public theorem log2W_eq (a : A) (o j : USize) (h : LoopBound a o j) :
    log2W a o j h = Nat.log2 (LimbArray.valAt a o.toNat j.toNat) := by
  induction j, h using log2W.induct (R := R) a o with
  | case1 h =>
    rw [log2W]
    simp
  | case2 j h hj x hx ih =>
    rw [log2W, dite_eq_right hj]
    simp only [x] at hx ⊢
    rw [ite_eq_left hx, ih]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [R.isZero_iff, R.uget_eq, h.toNat_add (pred_lt' (pos_of_ne hj)), hp] at hx
    rw [show j.toNat = (j.toNat - 1) + 1 by lia, LimbArray.valAt_add, LimbArray.valAt_one, hx, hp]
    simp
  | case3 j h hj x hx =>
    rw [log2W, dite_eq_right hj]
    simp only [x] at hx ⊢
    rw [ite_eq_right hx, R.log2_eq]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [R.isZero_iff] at hx
    rw [R.uget_eq, h.toNat_add (pred_lt' (pos_of_ne hj)), hp] at hx ⊢
    rw [show j.toNat = (j.toNat - 1) + 1 by lia, LimbArray.valAt_add, LimbArray.valAt_one,
      show j.toNat - 1 + 1 - 1 = j.toNat - 1 by lia,
      log2_top (LimbArray.valAt_lt ..) hx]

/-! ## Size without the zero limbs on top -/

/-- The number of limbs `o` to `o + j - 1` of `a` without the zero limbs on top, from the top down. -/
@[expose, specialize] public def topLenW (a : A) (o j : USize) (h : LoopBound a o j) : USize :=
  if hj : j = 0 then 0
  else
    let x := R.uget a (o + (j - 1)) (h.uset_bound (pred_lt' (pos_of_ne hj)))
    if R.isZero x then topLenW a o (j - 1) (bound_pred h (pos_of_ne hj)) else j
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

omit F in
/-- `topLenW` is at most `j`, the limbs from it to `j` are zero, and the one below it is not. -/
public theorem topLenW_spec (a : A) (o j : USize) (h : LoopBound a o j) :
    (topLenW a o j h).toNat ≤ j.toNat ∧
      (∀ k, (topLenW a o j h).toNat ≤ k → k < j.toNat → LA.val (LA.get a (o.toNat + k)) = 0) ∧
      (0 < (topLenW a o j h).toNat →
        LA.val (LA.get a (o.toNat + (topLenW a o j h).toNat - 1)) ≠ 0) := by
  induction j, h using topLenW.induct (R := R) a o with
  | case1 h =>
    rw [topLenW]
    simp
  | case2 j h hj x hx ih =>
    rw [topLenW, dite_eq_right hj]
    simp only [x] at hx ⊢
    rw [ite_eq_left hx]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [R.isZero_iff, R.uget_eq, h.toNat_add (pred_lt' (pos_of_ne hj)), hp] at hx
    rw [hp] at ih
    refine ⟨by lia, fun k hk hkj => ?_, ih.2.2⟩
    by_cases e : k = j.toNat - 1
    · rw [e]; exact hx
    · exact ih.2.1 k hk (by lia)
  | case3 j h hj x hx =>
    rw [topLenW, dite_eq_right hj]
    simp only [x] at hx ⊢
    rw [ite_eq_right hx]
    rw [R.isZero_iff, R.uget_eq, h.toNat_add (pred_lt' (pos_of_ne hj)), toNat_pred' (pos_of_ne hj)]
      at hx
    refine ⟨Nat.le_refl _, fun k hk hkj => by lia, fun _ => ?_⟩
    rwa [Nat.add_sub_assoc (by lia)]

/-! ## Comparison -/

/--
Whether `a < b` on limbs `0` to `j - 1`, zero past their ends (`LinComb.limbU`), from the top limb
down, like GMP's `mpn_cmp`: one comparison of limbs for each equal limb, and `ltB` at the first
limb that differs, which on trimmed limbs of different sizes is the top one.
-/
@[expose, specialize] public def ltW (a b : A) (j : USize) : Bool :=
  if hj : j = 0 then false
  else
    let x := LinComb.limbU a (j - 1)
    let y := LinComb.limbU b (j - 1)
    if R.eqB x y then ltW a b (j - 1) else R.ltB x y
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

omit F in
public theorem ltW_iff (hz : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0) (a b : A) (j : USize)
    (ha : LA.size a < USize.size) (hb : LA.size b < USize.size) :
    ltW a b j = true ↔ LimbArray.valAt a 0 j.toNat < LimbArray.valAt b 0 j.toNat := by
  induction j using ltW.induct (R := R) a b with
  | case1 =>
    rw [ltW]
    simp
  | case2 j hj x y he ih =>
    rw [ltW, dite_eq_right hj]
    simp only [x, y] at he ⊢
    rw [ite_eq_left he, ih]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [R.eqB_iff, LinComb.val_limbU hz _ _ ha, LinComb.val_limbU hz _ _ hb, hp] at he
    obtain ⟨m, hm⟩ : ∃ m, j.toNat = m + 1 := ⟨j.toNat - 1, by lia⟩
    simp only [hm, Nat.add_sub_cancel] at he ⊢
    rw [hp, hm, Nat.add_sub_cancel, LimbArray.valAt_add, LimbArray.valAt_add b,
      LimbArray.valAt_one, LimbArray.valAt_one, Nat.zero_add, he]
    lia
  | case3 j hj x y he =>
    rw [ltW, dite_eq_right hj]
    simp only [x, y] at he ⊢
    rw [ite_eq_right he, R.ltB_iff]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [R.eqB_iff, LinComb.val_limbU hz _ _ ha, LinComb.val_limbU hz _ _ hb, hp] at he
    rw [LinComb.val_limbU hz _ _ ha, LinComb.val_limbU hz _ _ hb, hp]
    obtain ⟨m, hm⟩ : ∃ m, j.toNat = m + 1 := ⟨j.toNat - 1, by lia⟩
    simp only [hm, Nat.add_sub_cancel] at he ⊢
    rw [LimbArray.valAt_add, LimbArray.valAt_add b, LimbArray.valAt_one, LimbArray.valAt_one,
      Nat.zero_add]
    have h₁ := LimbArray.valAt_lt a 0 m
    have h₂ := LimbArray.valAt_lt b 0 m
    generalize LimbArray.valAt a 0 m = X at *
    generalize LimbArray.valAt b 0 m = Y at *
    generalize LA.val (LA.get a m) = u at *
    generalize LA.val (LA.get b m) = v at *
    generalize 2 ^ (LA.w * m) = P at *
    constructor
    · intro h
      have := Nat.mul_le_mul_left P (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      lia
    · intro h
      rcases Nat.lt_or_ge u v with e | e
      · exact e
      · have : v < u := by lia
        have := Nat.mul_le_mul_left P (Nat.succ_le_of_lt this)
        rw [Nat.mul_succ] at this
        lia

/-! ## Bitwise operations -/

variable (A) in
/-- The step of `bitW`: `f` of limb `j` of `a` and of `b`, zero past their ends. -/
@[inline, expose] public def bitStep (f : L → L → L) (a b : A) (n : USize) (j : USize)
    (_ : j < n) (_z c : L) : L × L :=
  (f (LinComb.limbU a j) (LinComb.limbU b j), c)

/--
Writes `f` of the limbs of `a` and `b`, zero past their ends, into limbs `0` to `n - 1` of `r`.
-/
@[inline, expose, specialize] public def bitW (f : L → L → L) (a b r : A) (n : USize)
    (hr : LoopBound r 0 n) : A :=
  F.foldThen n (bitStep A f a b n) r 0 hr 0 R.zero fun arr _ _ => arr

omit F in
private theorem bit_spec (f : L → L → L) (a b : A) (n : USize) (arr : A) (hr : LoopBound arr 0 n)
    (j : USize) (c : L) :
    LA.size (foldUInPlace n (bitStep A f a b n) arr 0 hr j c).1 = LA.size arr ∧
      (∀ i, (i < j.toNat ∨ n.toNat ≤ i) →
        LA.get (foldUInPlace n (bitStep A f a b n) arr 0 hr j c).1 i = LA.get arr i) ∧
      (∀ i : USize, j ≤ i → i < n → LA.get (foldUInPlace n (bitStep A f a b n) arr 0 hr j c).1
        i.toNat = f (LinComb.limbU a i) (LinComb.limbU b i)) := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n (bitStep A f a b n) 0 with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx : (0 + j).toNat = j.toNat := by rw [hr.toNat_add h]; simp
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂
    rw [R.size_uset] at ih₁
    refine ⟨ih₁, fun i hi => ?_, fun i hji hin => ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · by_cases e : i = j
      · subst e
        rw [ih₂ _ (.inl (by lia)), R.get_uset, hidx]
        simp [bitStep]
      · exact ih₃ i (by
          rw [USize.le_iff_toNat_le, hj₁]
          have := USize.le_iff_toNat_le.1 hji
          have : i.toNat ≠ j.toNat := fun e' => e (USize.toNat_inj.1 e')
          lia) hin
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    refine ⟨rfl, fun _ _ => rfl, fun i hji hin => ?_⟩
    exact absurd (USize.lt_of_lt_of_le hin (USize.not_lt.1 h |> fun h' => h')) (by
      intro h'; exact absurd (USize.lt_of_le_of_lt hji h') (USize.lt_irrefl _))

@[simp] public theorem size_bitW (f : L → L → L) (a b r : A) (n : USize) (hr : LoopBound r 0 n) :
    LA.size (bitW f a b r n hr) = LA.size r := by
  rw [bitW, F.foldThen_eq, foldUInPlaceThen]
  exact size_foldUInPlace ..

/--
The value of `bitW f` for an `f` whose value is the bitwise operation `op` with `g` on bits:
`op` of the values of `a` and `b` over `n` limbs, which hold them.
-/
public theorem valAt_bitW (f : L → L → L) (op : Nat → Nat → Nat) (g : Bool → Bool → Bool)
    (hf : ∀ x y, LA.val (f x y) = op (LA.val x) (LA.val y))
    (hop : ∀ x y k, (op x y).testBit k = g (x.testBit k) (y.testBit k)) (hg : g false false = false)
    (hz : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0)
    (a b r : A) (n : USize) (hr : LoopBound r 0 n) (ha : LA.size a < USize.size)
    (hb : LA.size b < USize.size) :
    LimbArray.valAt (bitW f a b r n hr) 0 n.toNat =
      op (LimbArray.valAt a 0 n.toNat) (LimbArray.valAt b 0 n.toNat) := by
  obtain ⟨-, -, e₃⟩ := bit_spec f a b n r hr 0 R.zero
  rw [bitW, F.foldThen_eq, foldUInPlaceThen]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [hop]
  by_cases hj : j < LA.w * n.toNat
  · have hw : 0 < LA.w := by have := R.w_ge; lia
    have hq : j / LA.w < n.toNat := by
      rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]; exact hj
    have hqu : (j / LA.w).toUSize.toNat = j / LA.w := by
      rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by have := n.toNat_lt_size; lia)]
    rw [LimbArray.testBit_valAt _ hj, LimbArray.testBit_valAt _ hj, LimbArray.testBit_valAt _ hj,
      ← hqu, e₃ _ (USize.zero_le) (USize.lt_iff_toNat_lt.2 (by rw [hqu]; exact hq)), hf, hop,
      LinComb.val_limbU hz _ _ ha, LinComb.val_limbU hz _ _ hb]
  · have h₁ : 2 ^ (LA.w * n.toNat) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by lia)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (LimbArray.valAt_lt ..) h₁),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (LimbArray.valAt_lt ..) h₁),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (LimbArray.valAt_lt ..) h₁), hg]

/-- `valAt_bitW` with the instance's `land`. -/
public theorem valAt_bitW_land (hz : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0)
    (a b r : A) (n : USize) (hr : LoopBound r 0 n) (ha : LA.size a < USize.size)
    (hb : LA.size b < USize.size) :
    LimbArray.valAt (bitW R.land a b r n hr) 0 n.toNat =
      LimbArray.valAt a 0 n.toNat &&& LimbArray.valAt b 0 n.toNat :=
  valAt_bitW R.land (· &&& ·) (· && ·) R.val_land (fun _ _ _ => Nat.testBit_and ..) rfl hz a b r n
    hr ha hb

/-- `valAt_bitW` with the instance's `lor`. -/
public theorem valAt_bitW_lor (hz : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0)
    (a b r : A) (n : USize) (hr : LoopBound r 0 n) (ha : LA.size a < USize.size)
    (hb : LA.size b < USize.size) :
    LimbArray.valAt (bitW R.lor a b r n hr) 0 n.toNat =
      LimbArray.valAt a 0 n.toNat ||| LimbArray.valAt b 0 n.toNat :=
  valAt_bitW R.lor (· ||| ·) (· || ·) R.val_lor (fun _ _ _ => Nat.testBit_or ..) rfl hz a b r n
    hr ha hb

/-- `valAt_bitW` with the instance's `xor`. -/
public theorem valAt_bitW_xor (hz : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0)
    (a b r : A) (n : USize) (hr : LoopBound r 0 n) (ha : LA.size a < USize.size)
    (hb : LA.size b < USize.size) :
    LimbArray.valAt (bitW R.xor a b r n hr) 0 n.toNat =
      LimbArray.valAt a 0 n.toNat ^^^ LimbArray.valAt b 0 n.toNat :=
  valAt_bitW R.xor (· ^^^ ·) (fun x y => x ^^ y) R.val_xor (fun _ _ _ => Nat.testBit_xor ..) rfl hz
    a b r n hr ha hb

end WordArray

end MPN
