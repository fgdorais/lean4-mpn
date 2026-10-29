/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordArray

/-!
# Linear combinations of two numbers by limbs

`mulSubMul x y a b` is `a x - b y` and its sign, and `mulAddMul x y a b` is `a x + b y`, for limbs
`a` and `b` below `2ᶜ`, in one pass over the limbs of `x` and `y`: the kernels of Lehmer's step,
like GMP's `mpn_hgcd_mul_matrix1_vector`, and of the products of the matrices of half-gcd. Each
writes a fresh array of `max x.size y.size + 1` limbs by the in-place fold, reading `x` and `y` as
zero past their ends.

The steps of the passes are those of the instance (`LinCombOps`), each with its value: the carry of
`a x - b y` is signed, and the instance carries it in a form of its choice, such as a word in two's
complement or one biased to be a natural number, with its value `sv`, so that the chain from one
limb to the next stays short.
-/

namespace MPN

open WordArray

/--
The steps of the linear combinations of two arrays of limbs by two limbs below `2ᶜ`, with their
values.
-/
public class LinCombOps (A : Type) (L : outParam Type) [LA : LimbArray A L] [R : WordArray A L] where
  /-- The bits `c` of the multipliers. -/
  cb : Nat
  cb_lt : cb < LA.w
  /-- An array of `n` zero limbs. -/
  zeros : Nat → A
  size_zeros : ∀ n, LA.size (zeros n) = n
  /-- Limbs past the end of an array are zero. -/
  val_get_ge : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0
  /-- One limb of `a x + b y`: `maC xᵢ yᵢ a b c`, the low limb of `a xᵢ + b yᵢ + c`, and the
  carry. -/
  maC : L → L → L → L → L → L × L
  /-- The carries of `maC`. -/
  cOK : L → Prop
  cOK_zero : cOK R.zero
  val_maC : ∀ xi yi a b c, LA.val a < 2 ^ cb → LA.val b < 2 ^ cb → cOK c →
    LA.val (maC xi yi a b c).1 + 2 ^ LA.w * LA.val (maC xi yi a b c).2 =
      LA.val a * LA.val xi + LA.val b * LA.val yi + LA.val c ∧ cOK (maC xi yi a b c).2
  /-- One limb of `a x - b y`: `msC xᵢ yᵢ a b h`, the low limb of `a xᵢ - b yᵢ + sv h`, and the
  signed carry, in the carried form. -/
  msC : L → L → L → L → L → L × L
  /-- The value of a carried signed carry. -/
  sv : L → Int
  /-- The carried forms of the signed carries of `msC`. -/
  sOK : L → Prop
  /-- The carried form of `0`. -/
  s0 : L
  sOK_s0 : sOK s0
  sv_s0 : sv s0 = 0
  val_msC : ∀ xi yi a b h, LA.val a < 2 ^ cb → LA.val b < 2 ^ cb → sOK h →
    (LA.val (msC xi yi a b h).1 : Int) + 2 ^ LA.w * sv (msC xi yi a b h).2 =
      LA.val a * LA.val xi - LA.val b * LA.val yi + sv h ∧ sOK (msC xi yi a b h).2
  /-- Whether a carried signed carry is negative. -/
  sNeg : L → Bool
  sNeg_iff : ∀ h, sOK h → (sNeg h = true ↔ sv h < 0)
  /-- A nonnegative carried signed carry as a limb. -/
  sTop : L → L
  val_sTop : ∀ h, sOK h → 0 ≤ sv h → (LA.val (sTop h) : Int) = sv h

namespace LinComb

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]
  [C : LinCombOps A L]

/-- Limb `j` of `x`, of `nx` limbs, or zero past its end. -/
@[inline, expose] public def limbOr (x : A) (nx : USize) (hnx : nx.toNat = LA.size x) (j : USize) :
    L :=
  if h : j < nx then R.uget x j (by rw [← hnx]; exact USize.lt_iff_toNat_lt.1 h) else R.zero

omit F C in
public theorem val_limbOr (x : A) (nx : USize) (hnx : nx.toNat = LA.size x) (j : USize)
    (hz : ∀ i, LA.size x ≤ i → LA.val (LA.get x i) = 0) :
    LA.val (limbOr x nx hnx j) = LA.val (LA.get x j.toNat) := by
  unfold limbOr
  split
  · rw [R.uget_eq]
  · rename_i h
    have : LA.size x ≤ j.toNat := by
      rw [← hnx]; exact Nat.le_of_not_lt fun h' => h (USize.lt_iff_toNat_lt.2 h')
    rw [R.val_zero, hz _ this]

/-- One limb of the pass of `mulSubMul`. -/
@[inline, expose] public def msStep (x y : A) (nx ny : USize) (hnx : nx.toNat = LA.size x)
    (hny : ny.toNat = LA.size y) (a b : L) (n : USize) (j : USize) (_ : j < n) (_z h : L) : L × L :=
  C.msC (limbOr x nx hnx j) (limbOr y ny hny j) a b h

/-- One limb of the pass of `mulAddMul`. -/
@[inline, expose] public def maStep (x y : A) (nx ny : USize) (hnx : nx.toNat = LA.size x)
    (hny : ny.toNat = LA.size y) (a b : L) (n : USize) (j : USize) (_ : j < n) (_z c : L) : L × L :=
  C.maC (limbOr x nx hnx j) (limbOr y ny hny j) a b c

omit F in
public theorem msFold_spec (x y : A) (nx ny : USize) (hnx : nx.toNat = LA.size x)
    (hny : ny.toNat = LA.size y) (a b : L) (ha : LA.val a < 2 ^ C.cb) (hb : LA.val b < 2 ^ C.cb)
    (n : USize) (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (h : L)
    (hs : C.sOK h) :
    LA.size (foldUInPlace n (msStep x y nx ny hnx hny a b n) arr rs hr j h).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (msStep x y nx ny hnx hny a b n) arr rs hr j h).1 i =
          LA.get arr i) ∧
      (LimbArray.valAt (foldUInPlace n (msStep x y nx ny hnx hny a b n) arr rs hr j h).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) : Int) +
          2 ^ (LA.w * (n.toNat - j.toNat)) *
            C.sv (foldUInPlace n (msStep x y nx ny hnx hny a b n) arr rs hr j h).2 =
        LA.val a * LimbArray.valAt x j.toNat (n.toNat - j.toNat) -
          LA.val b * LimbArray.valAt y j.toNat (n.toNat - j.toNat) + C.sv h ∧
      C.sOK (foldUInPlace n (msStep x y nx ny hnx hny a b n) arr rs hr j h).2 := by
  induction arr, hr, j, h using foldUInPlace.induct (R := R) n (msStep x y nx ny hnx hny a b n) rs
    with
  | case1 arr hr j h hj p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ hj]
    have hj' := USize.lt_iff_toNat_lt.1 hj
    have hj₁ := USize.toNat_add_one_of_lt hj
    have hidx := hr.toNat_add hj
    obtain ⟨m₁, m₂⟩ := C.val_msC (limbOr x nx hnx j) (limbOr y ny hny j) a b h ha hb hs
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih m₂
    simp only [p, msStep] at ih₁ ih₂ ih₃ ih₄ ⊢
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [R.get_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_, ih₄⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv,
        ← val_limbOr x nx hnx j (C.val_get_ge x), ← val_limbOr y ny hny j (C.val_get_ge y),
        Nat.mul_succ]
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.pow_add] at ih₃ m₁ ⊢
      generalize LimbArray.valAt (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).1 _ _ = V at *
      generalize C.sv (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).2 = c' at *
      generalize C.sv (C.msC _ _ a b h).2 = c₁ at *
      generalize LA.val (C.msC _ _ a b h).1 = o at *
      generalize LimbArray.valAt x _ k = X at *
      generalize LimbArray.valAt y _ k = Y at *
      generalize LA.val (limbOr x nx hnx j) = xi at *
      generalize LA.val (limbOr y ny hny j) = yi at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize C.sv h = σ at *
      generalize LA.val a = Ai at *
      generalize LA.val b = Bi at *
      generalize 2 ^ LA.w = W at *
      grind
  | case2 arr hr j h hj =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ hj]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    refine ⟨rfl, fun _ _ => rfl, by simp [this], hs⟩

omit F in
public theorem maFold_spec (x y : A) (nx ny : USize) (hnx : nx.toNat = LA.size x)
    (hny : ny.toNat = LA.size y) (a b : L) (ha : LA.val a < 2 ^ C.cb) (hb : LA.val b < 2 ^ C.cb)
    (n : USize) (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (c : L)
    (hc : C.cOK c) :
    LA.size (foldUInPlace n (maStep x y nx ny hnx hny a b n) arr rs hr j c).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (maStep x y nx ny hnx hny a b n) arr rs hr j c).1 i =
          LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace n (maStep x y nx ny hnx hny a b n) arr rs hr j c).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (LA.w * (n.toNat - j.toNat)) *
            LA.val (foldUInPlace n (maStep x y nx ny hnx hny a b n) arr rs hr j c).2 =
        LA.val a * LimbArray.valAt x j.toNat (n.toNat - j.toNat) +
          LA.val b * LimbArray.valAt y j.toNat (n.toNat - j.toNat) + LA.val c ∧
      C.cOK (foldUInPlace n (maStep x y nx ny hnx hny a b n) arr rs hr j c).2 := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n (maStep x y nx ny hnx hny a b n) rs
    with
  | case1 arr hr j c hj p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ hj]
    have hj' := USize.lt_iff_toNat_lt.1 hj
    have hj₁ := USize.toNat_add_one_of_lt hj
    have hidx := hr.toNat_add hj
    obtain ⟨m₁, m₂⟩ := C.val_maC (limbOr x nx hnx j) (limbOr y ny hny j) a b c ha hb hc
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih m₂
    simp only [p, maStep] at ih₁ ih₂ ih₃ ih₄ ⊢
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [R.get_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_, ih₄⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv,
        ← val_limbOr x nx hnx j (C.val_get_ge x), ← val_limbOr y ny hny j (C.val_get_ge y),
        Nat.mul_succ, Nat.pow_add]
      generalize LimbArray.valAt (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).1 _ _ = V at *
      generalize LA.val (foldUInPlace (A := A) (β := L) _ _ _ _ _ _ _).2 = c' at *
      generalize LA.val (C.maC _ _ a b c).2 = c₁ at *
      generalize LA.val (C.maC _ _ a b c).1 = o at *
      generalize LimbArray.valAt x _ k = X at *
      generalize LimbArray.valAt y _ k = Y at *
      generalize LA.val (limbOr x nx hnx j) = xi at *
      generalize LA.val (limbOr y ny hny j) = yi at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize LA.val a = Ai at *
      generalize LA.val b = Bi at *
      generalize 2 ^ LA.w = W at *
      grind
  | case2 arr hr j c hj =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ hj]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    refine ⟨rfl, fun _ _ => rfl, by simp [this], hc⟩

/-! ## The combinations -/

omit R F C in
/-- The value of `x`, whose limbs past its end are zero, over `n ≥ x.size` limbs. -/
private theorem valAt_of_ge (x : A) (n : Nat) (hz : ∀ i, LA.size x ≤ i → LA.val (LA.get x i) = 0)
    (hn : LA.size x ≤ n) : LimbArray.valAt x 0 n = LimbArray.valAt x 0 (LA.size x) := by
  rw [show n = LA.size x + (n - LA.size x) by lia, LimbArray.valAt_add,
    LimbArray.valAt_eq_zero (lo := 0 + LA.size x) _ fun i h₁ _ => hz i (by lia), Nat.mul_zero,
    Nat.add_zero]

omit R F C in
public theorem fits_of {n : Nat} (h : (n + 1).toUSize.toNat = n + 1) :
    n.toUSize.toNat = n ∧ n + 1 < USize.size := by
  have := (n + 1).toUSize.toNat_lt_size
  exact ⟨by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)], by lia⟩

omit F in
public theorem zeros_bound {n : Nat} (h : (n + 1).toUSize.toNat = n + 1) :
    LoopBound (C.zeros (n + 1)) 0 n.toUSize := by
  have := fits_of h
  show (0 : USize).toNat + n.toUSize.toNat ≤ LA.size (C.zeros (n + 1)) ∧
    (0 : USize).toNat + n.toUSize.toNat < USize.size
  rw [C.size_zeros, this.1, USize.toNat_zero]
  exact ⟨by lia, by lia⟩

/--
`a x - b y` for `a, b < 2ᶜ`, in `max x.size y.size + 1` limbs, and whether it is negative, in which
case the limbs mean nothing. Its indices are `USize`s; were an array too large for them, which none
is, the limbs would be written from the value instead.
-/
@[expose, specialize]
public def mulSubMul (x y : A) (a b : L) : A × Bool :=
  let n := max (LA.size x) (LA.size y)
  if h : (n + 1).toUSize.toNat = n + 1 ∧ (LA.size x).toUSize.toNat = LA.size x ∧
      (LA.size y).toUSize.toNat = LA.size y then
    F.foldThen n.toUSize (msStep x y (LA.size x).toUSize (LA.size y).toUSize h.2.1 h.2.2 a b
      n.toUSize) (C.zeros (n + 1)) 0 (zeros_bound h.1) 0 C.s0 fun z hz s =>
        (R.uset z n.toUSize (C.sTop s) (by rw [hz, C.size_zeros, (fits_of h.1).1]; lia), C.sNeg s)
  else
    (LimbArray.writeNat (C.zeros (n + 1)) 0 (n + 1)
        (LA.val a * LimbArray.valAt x 0 (LA.size x) - LA.val b * LimbArray.valAt y 0 (LA.size y)),
      decide (LA.val a * LimbArray.valAt x 0 (LA.size x) <
        LA.val b * LimbArray.valAt y 0 (LA.size y)))

/--
`a x + b y` for `a, b < 2ᶜ`, in `max x.size y.size + 1` limbs, like `mulSubMul`.
-/
@[expose, specialize]
public def mulAddMul (x y : A) (a b : L) : A :=
  let n := max (LA.size x) (LA.size y)
  if h : (n + 1).toUSize.toNat = n + 1 ∧ (LA.size x).toUSize.toNat = LA.size x ∧
      (LA.size y).toUSize.toNat = LA.size y then
    F.foldThen n.toUSize (maStep x y (LA.size x).toUSize (LA.size y).toUSize h.2.1 h.2.2 a b
      n.toUSize) (C.zeros (n + 1)) 0 (zeros_bound h.1) 0 R.zero fun z hz c =>
        R.uset z n.toUSize c (by rw [hz, C.size_zeros, (fits_of h.1).1]; lia)
  else
    LimbArray.writeNat (C.zeros (n + 1)) 0 (n + 1)
      (LA.val a * LimbArray.valAt x 0 (LA.size x) + LA.val b * LimbArray.valAt y 0 (LA.size y))

omit F in
/-- The bound of `a x ± b y` by `2^(w (n + 1))`. -/
private theorem comb_lt (x y : A) (a b : L) (ha : LA.val a < 2 ^ C.cb) (hb : LA.val b < 2 ^ C.cb) :
    LA.val a * LimbArray.valAt x 0 (LA.size x) + LA.val b * LimbArray.valAt y 0 (LA.size y) <
      2 ^ (LA.w * (max (LA.size x) (LA.size y) + 1)) := by
  have hX := LimbArray.valAt_lt x 0 (LA.size x)
  have hY := LimbArray.valAt_lt y 0 (LA.size y)
  have hXn : 2 ^ (LA.w * LA.size x) ≤ 2 ^ (LA.w * max (LA.size x) (LA.size y)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by lia))
  have hYn : 2 ^ (LA.w * LA.size y) ≤ 2 ^ (LA.w * max (LA.size x) (LA.size y)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by lia))
  have hc : 2 ^ C.cb * 2 ≤ 2 ^ LA.w := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) C.cb_lt
  rw [Nat.mul_succ, Nat.pow_add]
  generalize 2 ^ (LA.w * max (LA.size x) (LA.size y)) = P at *
  generalize LimbArray.valAt x 0 (LA.size x) = X at *
  generalize LimbArray.valAt y 0 (LA.size y) = Y at *
  have h₁ : LA.val a * X < 2 ^ C.cb * P := Nat.mul_lt_mul'' ha (by lia)
  have h₂ : LA.val b * Y < 2 ^ C.cb * P := Nat.mul_lt_mul'' hb (by lia)
  have h₄ : 2 ^ C.cb * P * 2 ≤ P * 2 ^ LA.w := by
    rw [Nat.mul_right_comm, Nat.mul_comm P]; exact Nat.mul_le_mul_right P hc
  lia

public theorem mulSubMul_spec (x y : A) (a b : L) (ha : LA.val a < 2 ^ C.cb)
    (hb : LA.val b < 2 ^ C.cb) :
    LA.size (mulSubMul x y a b).1 = max (LA.size x) (LA.size y) + 1 ∧
      ((mulSubMul x y a b).2 = false →
        LimbArray.valAt (mulSubMul x y a b).1 0 (max (LA.size x) (LA.size y) + 1) +
            LA.val b * LimbArray.valAt y 0 (LA.size y) =
          LA.val a * LimbArray.valAt x 0 (LA.size x)) ∧
      ((mulSubMul x y a b).2 = true →
        LA.val a * LimbArray.valAt x 0 (LA.size x) < LA.val b * LimbArray.valAt y 0 (LA.size y)) := by
  generalize hM : mulSubMul x y a b = M
  unfold mulSubMul at hM
  dsimp only at hM
  split at hM
  · rename_i h
    obtain ⟨hn, hU⟩ := fits_of h.1
    obtain ⟨z, f₁, s', e, hM⟩ := foldThen_cases hM
    subst hM
    obtain ⟨-, -, f₃, f₄⟩ := msFold_spec x y _ _ h.2.1 h.2.2 a b ha hb _ (C.zeros _) 0
      (zeros_bound h.1) 0 C.s0 C.sOK_s0
    rw [e] at f₃ f₄
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hn, C.sv_s0, Int.add_zero] at f₃
    rw [valAt_of_ge x _ (C.val_get_ge x) (by lia), valAt_of_ge y _ (C.val_get_ge y) (by lia)] at f₃
    have hsz : LA.size z = max (LA.size x) (LA.size y) + 1 := by rw [f₁, C.size_zeros]
    have hval : LimbArray.valAt (R.uset z (max (LA.size x) (LA.size y)).toUSize (C.sTop s')
        (by rw [hsz, hn]; lia)) 0 (max (LA.size x) (LA.size y) + 1) =
        LimbArray.valAt z 0 (max (LA.size x) (LA.size y)) +
          2 ^ (LA.w * max (LA.size x) (LA.size y)) * LA.val (C.sTop s') := by
      rw [LimbArray.valAt_add, LimbArray.valAt_one, R.get_uset, valAt_uset_of _ _ _ _ _ _
        (by rw [hn]; lia)]
      simp only [hn, Nat.zero_add, ↓reduceIte]
    have hL := LimbArray.valAt_lt z 0 (max (LA.size x) (LA.size y))
    rw [show (2 : Int) ^ (LA.w * max (LA.size x) (LA.size y)) =
      ((2 ^ (LA.w * max (LA.size x) (LA.size y)) : Nat) : Int) by push_cast; rfl] at f₃
    refine ⟨by rw [R.size_uset, hsz], fun hneg => ?_, fun hneg => ?_⟩
    · dsimp only at hneg ⊢
      have hs : 0 ≤ C.sv s' := by
        rcases Int.lt_or_le (C.sv s') 0 with e | e
        · exact absurd ((C.sNeg_iff _ f₄).2 e) (by rw [hneg]; decide)
        · exact e
      have ht := C.val_sTop _ f₄ hs
      rw [hval]
      generalize LimbArray.valAt z 0 _ = V at *
      generalize LA.val (C.sTop s') = T at *
      generalize 2 ^ (LA.w * max (LA.size x) (LA.size y)) = P at *
      generalize LimbArray.valAt x 0 (LA.size x) = X at *
      generalize LimbArray.valAt y 0 (LA.size y) = Y at *
      generalize C.sv s' = σ at *
      subst ht
      have : ((V + P * T : Nat) : Int) + LA.val b * Y = LA.val a * X := by push_cast; lia
      exact_mod_cast this
    · dsimp only at hneg
      have hs := (C.sNeg_iff _ f₄).1 hneg
      generalize LimbArray.valAt z 0 _ = V at *
      generalize 2 ^ (LA.w * max (LA.size x) (LA.size y)) = P at *
      generalize LimbArray.valAt x 0 (LA.size x) = X at *
      generalize LimbArray.valAt y 0 (LA.size y) = Y at *
      generalize C.sv s' = σ at *
      have : (P : Int) * σ ≤ -P := by
        have : σ ≤ -1 := by lia
        have := Int.mul_le_mul_of_nonneg_left this (show (0 : Int) ≤ P by lia)
        lia
      have : (LA.val a * X : Int) < LA.val b * Y := by push_cast at f₃ ⊢; lia
      exact_mod_cast this
  · rename_i h
    subst hM
    have hlt := comb_lt x y a b ha hb
    have hv := LimbArray.valAt_writeNat (C.zeros (max (LA.size x) (LA.size y) + 1)) 0
      (max (LA.size x) (LA.size y) + 1)
      (LA.val a * LimbArray.valAt x 0 (LA.size x) - LA.val b * LimbArray.valAt y 0 (LA.size y))
      (by rw [C.size_zeros]; lia)
    rw [Nat.mod_eq_of_lt (by lia)] at hv
    refine ⟨by rw [LimbArray.size_writeNat, C.size_zeros], fun hneg => ?_, fun hneg => ?_⟩
    · dsimp only at hneg ⊢
      rw [hv]
      have : ¬(LA.val a * LimbArray.valAt x 0 (LA.size x) <
          LA.val b * LimbArray.valAt y 0 (LA.size y)) := by simpa using hneg
      lia
    · simpa using hneg

public theorem mulAddMul_spec (x y : A) (a b : L) (ha : LA.val a < 2 ^ C.cb)
    (hb : LA.val b < 2 ^ C.cb) :
    LA.size (mulAddMul x y a b) = max (LA.size x) (LA.size y) + 1 ∧
      LimbArray.valAt (mulAddMul x y a b) 0 (max (LA.size x) (LA.size y) + 1) =
        LA.val a * LimbArray.valAt x 0 (LA.size x) + LA.val b * LimbArray.valAt y 0 (LA.size y) := by
  generalize hM : mulAddMul x y a b = M
  unfold mulAddMul at hM
  dsimp only at hM
  split at hM
  · rename_i h
    obtain ⟨hn, hU⟩ := fits_of h.1
    obtain ⟨z, f₁, c, e, hM⟩ := foldThen_cases hM
    subst hM
    obtain ⟨-, -, f₃, -⟩ := maFold_spec x y _ _ h.2.1 h.2.2 a b ha hb _ (C.zeros _) 0
      (zeros_bound h.1) 0 R.zero C.cOK_zero
    rw [e] at f₃
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hn, R.val_zero] at f₃
    rw [valAt_of_ge x _ (C.val_get_ge x) (by lia), valAt_of_ge y _ (C.val_get_ge y) (by lia)] at f₃
    have hsz : LA.size z = max (LA.size x) (LA.size y) + 1 := by rw [f₁, C.size_zeros]
    refine ⟨by rw [R.size_uset, hsz], ?_⟩
    rw [LimbArray.valAt_add, LimbArray.valAt_one, R.get_uset, valAt_uset_of _ _ _ _ _ _
      (by rw [hn]; lia)]
    simp only [hn, Nat.zero_add, ↓reduceIte]
    exact f₃
  · subst hM
    have hlt := comb_lt x y a b ha hb
    refine ⟨by rw [LimbArray.size_writeNat, C.size_zeros], ?_⟩
    rw [LimbArray.valAt_writeNat _ _ _ _ (by rw [C.size_zeros]; lia), Nat.mod_eq_of_lt hlt]

end LinComb

end MPN
