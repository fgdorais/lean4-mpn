/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordArray

/-!
# Shifts of windows of limbs

`lshiftW r ro a ao n s` writes the `n` limbs of `a` from `ao`, shifted left by `0 < s < w` bits,
into `r` from `ro` and returns the bits out of the top, like GMP's `mpn_lshift`; `rshiftW` shifts
right and returns the bits out of the bottom, like `mpn_rshift`; and `copyW` copies, for shifts by
whole limbs. Each is one in-place fold over the window of `r` (`foldThen`), whose step reads `a` by
`uget`; `r` and `a` are different arrays, since a second reference to `r` would copy it.
-/

namespace MPN

namespace WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-- One limb of a left shift: `x 2ᵇ + c` and the bits of `x` above, for `0 < b < w`, `c < 2ᵇ`. -/
public theorem shl_step (x c b : L) (hb₀ : 0 < LA.val b) (hb : LA.val b < LA.w)
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

/-- `w - b` as a limb, for `b < w`. -/
public theorem val_wsub (b : L) (hb : LA.val b < LA.w) :
    LA.val (R.sub (R.ofUSize R.wU) b) = LA.w - LA.val b := by
  have hwB : LA.w < 2 ^ LA.w := Nat.lt_two_pow_self
  rw [R.val_sub, R.val_ofUSize, R.toNat_wU, Nat.mod_eq_of_lt hwB,
    show LA.w + (2 ^ LA.w - LA.val b) = (LA.w - LA.val b) + 2 ^ LA.w * 1 by lia,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by lia)]

/-- One limb of a right shift: `x / 2ᵇ` with the `b` low bits of `y` above, for `0 < b < w`. -/
public theorem shr_step (x y b : L) (hb₀ : 0 < LA.val b) (hb : LA.val b < LA.w) :
    LA.val (R.add (R.shr x b) (R.shl y (R.sub (R.ofUSize R.wU) b))) =
      LA.val x / 2 ^ LA.val b + LA.val y % 2 ^ LA.val b * 2 ^ (LA.w - LA.val b) := by
  have hwb := val_wsub b hb
  rw [R.val_add, R.val_shr, R.val_shl, hwb, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show LA.w - LA.val b < LA.w by lia)]
  have hPQ : 2 ^ LA.val b * 2 ^ (LA.w - LA.val b) = 2 ^ LA.w := by
    rw [← Nat.pow_add]; congr 1; lia
  have hx := LA.val_lt x
  have hy := LA.val_lt y
  have hP : 0 < 2 ^ LA.val b := Nat.two_pow_pos _
  have hQ : 0 < 2 ^ (LA.w - LA.val b) := Nat.two_pow_pos _
  rw [← hPQ] at hx hy ⊢
  -- `y 2^(w - b) mod 2^w` keeps the `b` low bits of `y`.
  have e₁ : LA.val y * 2 ^ (LA.w - LA.val b) % (2 ^ LA.val b * 2 ^ (LA.w - LA.val b)) =
      LA.val y % 2 ^ LA.val b * 2 ^ (LA.w - LA.val b) := by
    rw [Nat.mul_mod_mul_right]
  rw [e₁]
  have hxd : LA.val x / 2 ^ LA.val b < 2 ^ (LA.w - LA.val b) := by
    rw [Nat.div_lt_iff_lt_mul hP, Nat.mul_comm]; exact hx
  have hm := Nat.mod_lt (LA.val y) hP
  apply Nat.mod_eq_of_lt
  have := Nat.mul_le_mul_right (2 ^ (LA.w - LA.val b)) (Nat.succ_le_of_lt hm)
  rw [Nat.succ_mul] at this
  lia

/-- The `b` low bits of `x`. -/
public theorem low_bits (x b : L) (hb : LA.val b < LA.w) :
    LA.val (R.sub x (R.shl (R.shr x b) b)) = LA.val x % 2 ^ LA.val b := by
  have hx := LA.val_lt x
  have hP : 0 < 2 ^ LA.val b := Nat.two_pow_pos _
  have hd := Nat.div_add_mod (LA.val x) (2 ^ LA.val b)
  have hm := Nat.mod_lt (LA.val x) hP
  have hbw : 2 ^ LA.val b ≤ 2 ^ LA.w := Nat.pow_le_pow_right (by decide) (by lia)
  rw [R.val_sub, R.val_shl, R.val_shr, Nat.mod_eq_of_lt hb]
  generalize LA.val x / 2 ^ LA.val b = q at *
  generalize LA.val x % 2 ^ LA.val b = r at *
  generalize 2 ^ LA.val b = P at *
  generalize 2 ^ LA.w = W at *
  rw [← hd] at hx ⊢
  rw [Nat.mod_eq_of_lt (show q * P < W by grind),
    show P * q + r + (W - q * P) = r + W * 1 by grind, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by lia)]

variable [F : WordFolds A L]

/-! ## Left shifts -/

variable (A) in
/-- The step of `lshiftW`: limb `ao + j` of `a` shifted left by `s`, with the bits `c` below. -/
@[inline, expose] public def lshStep (a : A) (ao : USize) (s : L) (n : USize)
    (ha : LoopBound a ao n) (j : USize) (h : j < n) (_z c : L) : L × L :=
  let x := R.uget a (ao + j) (ha.uset_bound h)
  (R.add (R.shl x s) c, R.shr x (R.sub (R.ofUSize R.wU) s))

omit F in
private theorem lsh_spec (a : A) (ao : USize) (s : L) (hs₀ : 0 < LA.val s) (hs : LA.val s < LA.w)
    (n : USize) (ha : LoopBound a ao n) (arr : A) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : L) (hc : LA.val c < 2 ^ LA.val s) :
    LA.size (foldUInPlace n (lshStep A a ao s n ha) arr rs hr j c).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (lshStep A a ao s n ha) arr rs hr j c).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace n (lshStep A a ao s n ha) arr rs hr j c).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (LA.w * (n.toNat - j.toNat)) *
            LA.val (foldUInPlace n (lshStep A a ao s n ha) arr rs hr j c).2 =
        LimbArray.valAt a (ao.toNat + j.toNat) (n.toNat - j.toNat) * 2 ^ LA.val s + LA.val c := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n (lshStep A a ao s n ha) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hx : R.uget a (ao + j) (ha.uset_bound h) = LA.get a (ao.toNat + j.toNat) := by
      rw [R.uget_eq, ha.toNat_add h]
    have hs' := shl_step (R.uget a (ao + j) (ha.uset_bound h)) c s hs₀ hs hc
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih hs'.2
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [R.get_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have hs1 := hs'.1
      simp only [lshStep] at ih₃ hv ⊢
      generalize LimbArray.valAt (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).1 _ _ = V at *
      generalize LA.val (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).2 = c' at *
      generalize LA.val (R.shr (R.uget a (ao + j) _) _) = c₁ at *
      generalize LA.val (R.add (R.shl (R.uget a (ao + j) _) s) c) = o at *
      generalize LimbArray.valAt a _ k = X at *
      generalize LA.val (R.uget a (ao + j) _) = x at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize 2 ^ LA.val s = S at *
      generalize 2 ^ LA.w = W at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

/--
Writes the `n` limbs of `a` from `ao` shifted left by `0 < s < w` bits into `r` from `ro`, and
returns the bits out of the top, like GMP's `mpn_lshift`.
-/
@[expose, specialize] public def lshiftW (r : A) (ro : USize) (a : A) (ao n : USize) (s : L)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) : A × L :=
  F.foldThen n (lshStep A a ao s n ha) r ro hr 0 R.zero fun arr _ c => (arr, c)

public theorem lshiftW_spec (r : A) (ro : USize) (a : A) (ao n : USize) (s : L)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (hs₀ : 0 < LA.val s) (hs : LA.val s < LA.w) :
    LA.size (lshiftW r ro a ao n s hr ha).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (lshiftW r ro a ao n s hr ha).1 i = LA.get r i) ∧
      LimbArray.valAt (lshiftW r ro a ao n s hr ha).1 ro.toNat n.toNat +
          2 ^ (LA.w * n.toNat) * LA.val (lshiftW r ro a ao n s hr ha).2 =
        LimbArray.valAt a ao.toNat n.toNat * 2 ^ LA.val s := by
  rw [lshiftW, F.foldThen_eq]
  have := lsh_spec a ao s hs₀ hs n ha r ro hr 0 R.zero (by rw [R.val_zero]; exact Nat.two_pow_pos _)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, R.val_zero] at this
  exact ⟨this.1, fun i hi => this.2.1 i (by lia), this.2.2⟩

/-! ## Copies -/

variable (A) in
/-- The step of `copyW`: limb `ao + j` of `a`. -/
@[inline, expose] public def cpStep (a : A) (ao n : USize) (ha : LoopBound a ao n) (j : USize)
    (h : j < n) (_z _c : L) : L × L :=
  (R.uget a (ao + j) (ha.uset_bound h), R.zero)

omit F in
private theorem cp_spec (a : A) (ao n : USize) (ha : LoopBound a ao n) (arr : A) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : L) :
    LA.size (foldUInPlace n (cpStep A a ao n ha) arr rs hr j c).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (cpStep A a ao n ha) arr rs hr j c).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace n (cpStep A a ao n ha) arr rs hr j c).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) =
        LimbArray.valAt a (ao.toNat + j.toNat) (n.toNat - j.toNat) := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n (cpStep A a ao n ha) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [R.get_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    simp only [cpStep] at hv ih₁ ih₂ ih₃ ⊢
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      have hv' : LA.val (LA.get (foldUInPlace n (cpStep A a ao n ha)
          (R.uset arr (rs + j) (R.uget a (ao + j) (ha.uset_bound h)) (hr.uset_bound h)) rs
          (hr.of_uset ..) (j + 1) R.zero).1 (rs.toNat + j.toNat)) =
          LA.val (LA.get a (ao.toNat + j.toNat)) := by
        rw [hv, R.uget_eq, ha.toNat_add h]
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, hv', ih₃]
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

/-- Copies the `n` limbs of `a` from `ao` into `r` from `ro`. -/
@[expose, specialize] public def copyW (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) : A :=
  F.foldThen n (cpStep A a ao n ha) r ro hr 0 R.zero fun arr _ _ => arr

public theorem copyW_spec (r : A) (ro : USize) (a : A) (ao n : USize) (hr : LoopBound r ro n)
    (ha : LoopBound a ao n) :
    LA.size (copyW r ro a ao n hr ha) = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (copyW r ro a ao n hr ha) i = LA.get r i) ∧
      LimbArray.valAt (copyW r ro a ao n hr ha) ro.toNat n.toNat =
        LimbArray.valAt a ao.toNat n.toNat := by
  rw [copyW, F.foldThen_eq]
  have := cp_spec a ao n ha r ro hr 0 R.zero
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero] at this
  exact ⟨this.1, fun i hi => this.2.1 i (by lia), this.2.2⟩

/-! ## Right shifts -/

/-- `j + 1 < m` from `j < n < m`, in `USize`. -/
public theorem succ_lt_of_lt_lt {j n m : USize} (h : j < n) (hn : n < m) : j + 1 < m := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_add_one_of_lt h]
  have := USize.lt_iff_toNat_lt.1 h
  have := USize.lt_iff_toNat_lt.1 hn
  lia

variable (A) in
/--
The step of `rshiftW`: limb `ao + j` of `a`, which is `x`, shifted right by `s`, with the low bits
of the limb above, which is the next accumulator.
-/
@[inline, expose] public def rshStep (a : A) (ao : USize) (s : L) (n m : USize) (hnm : n < m)
    (ha : LoopBound a ao m) (j : USize) (h : j < n) (_z x : L) : L × L :=
  let y := R.uget a (ao + (j + 1)) (ha.uset_bound (succ_lt_of_lt_lt h hnm))
  (R.add (R.shr x s) (R.shl y (R.sub (R.ofUSize R.wU) s)), y)

omit F in
private theorem rsh_spec (a : A) (ao : USize) (s : L) (hs₀ : 0 < LA.val s) (hs : LA.val s < LA.w)
    (n m : USize) (hnm : n < m) (ha : LoopBound a ao m) (arr : A) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (x : L) (hj : j ≤ n)
    (hx : x = LA.get a (ao.toNat + j.toNat)) :
    LA.size (foldUInPlace n (rshStep A a ao s n m hnm ha) arr rs hr j x).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (rshStep A a ao s n m hnm ha) arr rs hr j x).1 i = LA.get arr i) ∧
      (foldUInPlace n (rshStep A a ao s n m hnm ha) arr rs hr j x).2 =
        LA.get a (ao.toNat + n.toNat) ∧
      2 ^ LA.val s * LimbArray.valAt (foldUInPlace n (rshStep A a ao s n m hnm ha) arr rs hr j x).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) + LA.val x % 2 ^ LA.val s =
        LimbArray.valAt a (ao.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (LA.w * (n.toNat - j.toNat)) *
            (LA.val (foldUInPlace n (rshStep A a ao s n m hnm ha) arr rs hr j x).2 %
              2 ^ LA.val s) := by
  induction arr, hr, j, x using foldUInPlace.induct (R := R) n (rshStep A a ao s n m hnm ha) rs
    with
  | case1 arr hr j x h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj' := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hy : R.uget a (ao + (j + 1)) (ha.uset_bound (succ_lt_of_lt_lt h hnm)) =
        LA.get a (ao.toNat + (j.toNat + 1)) := by
      rw [R.uget_eq, ha.toNat_add (succ_lt_of_lt_lt h hnm), hj₁]
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih (USize.le_iff_toNat_le.2 (by lia)) (by
      simp only [p, rshStep]; rw [hy, hj₁])
    simp only [p] at ih₁ ih₂ ih₃ ih₄
    rw [hj₁] at ih₂ ih₄
    rw [R.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [R.get_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ih₃, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₄
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, ← hx]
      simp only [rshStep] at ih₄ ⊢
      rw [shr_step _ _ _ hs₀ hs]
      have hW : 2 ^ LA.w = 2 ^ LA.val s * 2 ^ (LA.w - LA.val s) := by
        rw [← Nat.pow_add]; congr 1; lia
      have hdx := Nat.div_add_mod (LA.val x) (2 ^ LA.val s)
      rw [Nat.mul_succ, Nat.pow_add]
      generalize LimbArray.valAt (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).1 _ _ = V at *
      generalize LA.val (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).2 % 2 ^ LA.val s = c' at *
      generalize LimbArray.valAt a _ k = Y at *
      generalize LA.val (R.uget a (ao + (j + 1)) (ha.uset_bound (succ_lt_of_lt_lt h hnm))) = y at *
      generalize LA.val x = X at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize 2 ^ (LA.w - LA.val s) = Q at *
      generalize 2 ^ LA.val s = S at *
      generalize 2 ^ LA.w = W at *
      subst hW
      have hdy := Nat.div_add_mod y S
      generalize y / S = yq at *
      generalize y % S = yr at *
      generalize X / S = xq at *
      generalize X % S = xr at *
      subst hdx hdy
      grind
  | case2 arr hr j x h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have hjn : j = n := by
      have := USize.lt_iff_toNat_lt (a := j) (b := n)
      exact USize.toNat_inj.1 (by have := USize.le_iff_toNat_le.1 hj; lia)
    subst hjn
    simp [hx]

public theorem pred_lt' {m : USize} (hm : 0 < m) : m - 1 < m := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by
    have := USize.lt_iff_toNat_lt.1 hm; simp; lia))]
  have := USize.lt_iff_toNat_lt.1 hm
  simp; lia

public theorem toNat_pred' {m : USize} (hm : 0 < m) : (m - 1).toNat = m.toNat - 1 := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by
    have := USize.lt_iff_toNat_lt.1 hm; simp; lia))]
  simp

omit R F in
public theorem bound_pred {arr : A} {ro m : USize} (hr : LoopBound arr ro m) (hm : 0 < m) :
    LoopBound arr ro (m - 1) := by
  have := toNat_pred' hm
  exact ⟨by lia, by lia⟩

omit R F in
public theorem top_idx {arr : A} {ro m : USize} (hr : LoopBound arr ro m) (hm : 0 < m)
    (arr' : A) (h : LA.size arr' = LA.size arr) : (ro + (m - 1)).toNat < LA.size arr' := by
  rw [h]; exact hr.uset_bound (pred_lt' hm)

/--
Writes the `m > 0` limbs of `a` from `ao` shifted right by `0 < s < w` bits into `r` from `ro`, and
returns the bits out of the bottom, `a mod 2ˢ`, like GMP's `mpn_rshift`, which returns them in the
top bits of a limb instead.
-/
@[expose, specialize] public def rshiftW (r : A) (ro : USize) (a : A) (ao m : USize) (s : L)
    (hr : LoopBound r ro m) (ha : LoopBound a ao m) (hm : 0 < m) : A × L :=
  let x₀ := R.uget a ao (by have := ha.uset_bound hm; simpa using this)
  F.foldThen (m - 1) (rshStep A a ao s (m - 1) m (pred_lt' hm) ha) r ro (bound_pred hr hm) 0 x₀
    fun arr harr x =>
      (R.uset arr (ro + (m - 1)) (R.shr x s) (top_idx hr hm arr harr),
        R.sub x₀ (R.shl (R.shr x₀ s) s))

omit F in
private theorem rsh_fin (r a : A) (ro ao m : USize) (s : L) (hm : 0 < m) (hs : LA.val s < LA.w)
    (q : A × L) (x₀ : L) (f₁ : LA.size q.1 = LA.size r)
    (f₂ : ∀ i, (i < ro.toNat ∨ ro.toNat + (m.toNat - 1) ≤ i) → LA.get q.1 i = LA.get r i)
    (f₃ : q.2 = LA.get a (ao.toNat + (m.toNat - 1)))
    (f₄ : 2 ^ LA.val s * LimbArray.valAt q.1 ro.toNat (m.toNat - 1) + LA.val x₀ % 2 ^ LA.val s =
      LimbArray.valAt a ao.toNat (m.toNat - 1) +
        2 ^ (LA.w * (m.toNat - 1)) * (LA.val q.2 % 2 ^ LA.val s))
    (hidx : (ro + (m - 1)).toNat < LA.size q.1)
    (hti : (ro + (m - 1)).toNat = ro.toNat + (m.toNat - 1)) :
    LA.size (R.uset q.1 (ro + (m - 1)) (R.shr q.2 s) hidx) = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + m.toNat ≤ i) →
        LA.get (R.uset q.1 (ro + (m - 1)) (R.shr q.2 s) hidx) i = LA.get r i) ∧
      2 ^ LA.val s * LimbArray.valAt (R.uset q.1 (ro + (m - 1)) (R.shr q.2 s) hidx) ro.toNat
          m.toNat + LA.val (R.sub x₀ (R.shl (R.shr x₀ s) s)) =
        LimbArray.valAt a ao.toNat m.toNat ∧
      LA.val (R.sub x₀ (R.shl (R.shr x₀ s) s)) < 2 ^ LA.val s := by
  have hm' := USize.lt_iff_toNat_lt.1 hm
  have hP : 0 < 2 ^ LA.val s := Nat.two_pow_pos _
  refine ⟨by rw [R.size_uset, f₁], fun i hi => ?_, ?_, ?_⟩
  · rw [R.get_uset, hti]
    simp only [show ¬(ro.toNat + (m.toNat - 1) = i) by simp at hm'; lia, ↓reduceIte]
    exact f₂ i (by lia)
  · rw [low_bits _ _ hs]
    have hm1 : m.toNat = (m.toNat - 1) + 1 := by simp at hm'; lia
    rw [hm1, LimbArray.valAt_add, LimbArray.valAt_one,
      LimbArray.valAt_add a ao.toNat (m.toNat - 1) 1, LimbArray.valAt_one a, R.get_uset, hti]
    simp only [↓reduceIte]
    rw [valAt_uset_of _ _ _ _ _ _ (by rw [hti]; lia), R.val_shr, Nat.mod_eq_of_lt hs, f₃]
    rw [f₃] at f₄
    have hd := Nat.div_add_mod (LA.val (LA.get a (ao.toNat + (m.toNat - 1)))) (2 ^ LA.val s)
    generalize LimbArray.valAt q.1 ro.toNat (m.toNat - 1) = V at *
    generalize LimbArray.valAt a ao.toNat (m.toNat - 1) = X at *
    generalize LA.val (LA.get a (ao.toNat + (m.toNat - 1))) = t at *
    generalize LA.val x₀ % 2 ^ LA.val s = r₀ at *
    generalize 2 ^ (LA.w * (m.toNat - 1)) = P at *
    generalize 2 ^ LA.val s = S at *
    generalize t / S = tq at *
    generalize t % S = tr at *
    subst hd
    grind
  · rw [low_bits _ _ hs]; exact Nat.mod_lt _ hP

public theorem rshiftW_spec (r : A) (ro : USize) (a : A) (ao m : USize) (s : L)
    (hr : LoopBound r ro m) (ha : LoopBound a ao m) (hm : 0 < m) (hs₀ : 0 < LA.val s)
    (hs : LA.val s < LA.w) :
    LA.size (rshiftW r ro a ao m s hr ha hm).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + m.toNat ≤ i) →
        LA.get (rshiftW r ro a ao m s hr ha hm).1 i = LA.get r i) ∧
      2 ^ LA.val s * LimbArray.valAt (rshiftW r ro a ao m s hr ha hm).1 ro.toNat m.toNat +
          LA.val (rshiftW r ro a ao m s hr ha hm).2 =
        LimbArray.valAt a ao.toNat m.toNat ∧
      LA.val (rshiftW r ro a ao m s hr ha hm).2 < 2 ^ LA.val s := by
  have hp := toNat_pred' hm
  have hx₀ : R.uget a ao (by have := ha.uset_bound hm; simpa using this) = LA.get a ao.toNat :=
    R.uget_eq ..
  obtain ⟨f₁, f₂, f₃, f₄⟩ := rsh_spec a ao s hs₀ hs (m - 1) m (pred_lt' hm) ha r ro
    (bound_pred hr hm) 0 (R.uget a ao (by have := ha.uset_bound hm; simpa using this))
    USize.zero_le (by rw [hx₀]; simp)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hp] at f₂ f₃ f₄
  rw [rshiftW, F.foldThen_eq, foldUInPlaceThen]
  exact rsh_fin r a ro ao m s hm hs _ _ f₁ f₂ f₃ f₄ _
    (by rw [hr.toNat_add (pred_lt' hm), hp])

end WordArray

end MPN
