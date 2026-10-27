/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Windows
public import MPN.Poly

/-!
# Products by the FFT

Schönhage–Strassen multiplication of `a` by `b` on one flat array, for limbs of any width `w`:
their pieces of `m` limbs are loaded into two blocks of `K = 2ᵏ` windows of `n + 1` limbs,
transformed modulo `F = 2^(w n) + 1` with the root `2^σ`, `σ = 2 w n / K`, multiplied pointwise
and reduced modulo `F`, and transformed back. Divided by `K`, the windows are the coefficients of
the product of the polynomials of the pieces, which are less than `F` when
`K 2^(2 w m) ≤ 2^(w n)`, so they are exact; their sum at `2^(w m)` is `a b`.

The transforms are those of `MPN.FFT.Windows`. The other in-place operations on the flat array,
and on the array of the result, are those of the class `FFTOps`, and the pointwise products are
an argument, so that each branch uses its own multiplication. The operands are ranges of arrays:
`(a, as, al)` is the `al` limbs of `a` from limb `as` on.
-/

namespace MPN.FFT

open LimbArray WinOps

/--
The in-place operations of the products by the FFT beyond the transforms, on arrays of limbs, with
their specifications.
-/
public class FFTOps (A : Type) (L : outParam Type) [LimbArray A L] where
  /-- An array of `n` zero limbs. -/
  zeros : Nat → A
  size_zeros : ∀ n, LimbArray.size (zeros n) = n
  val_get_zeros : ∀ n i, LimbArray.val (A := A) (LimbArray.get (zeros n) i) = 0
  /-- Adds the `slen` limbs of `src` from `so` on to the `len` limbs of `arr` from `o` on. -/
  addRange : A → Nat → Nat → A → Nat → Nat → A
  addRange_spec : ∀ (arr : A) (o len : Nat) (src : A) (so slen : Nat),
    LimbArray.size arr < USize.size → o + len ≤ LimbArray.size arr →
    LimbArray.size src < USize.size → so + slen ≤ LimbArray.size src → slen ≤ len →
    valAt arr o len + valAt src so slen < 2 ^ (LimbArray.w A * len) →
    LimbArray.size (addRange arr o len src so slen) = LimbArray.size arr ∧
      (∀ i, (i < o ∨ o + len ≤ i) →
        LimbArray.get (addRange arr o len src so slen) i = LimbArray.get arr i) ∧
      valAt (addRange arr o len src so slen) o len = valAt arr o len + valAt src so slen
  /-- The residue modulo `2^(w n) + 1` of the `2 n + 2` limbs of `P`, into the window at `d`. -/
  reduce : A → Nat → Nat → A → A
  reduce_spec : ∀ (arr : A) (n d : Nat) (P : A), LimbArray.size arr < USize.size →
    d + n + 1 ≤ LimbArray.size arr → 1 ≤ n → LimbArray.size P = 2 * n + 2 →
    LimbArray.size P < USize.size →
    valAt P 0 (2 * n + 2) ≤ 2 ^ (LimbArray.w A * n) * 2 ^ (LimbArray.w A * n) →
    LimbArray.size (reduce arr n d P) = LimbArray.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → LimbArray.get (reduce arr n d P) i = LimbArray.get arr i) ∧
      win (reduce arr n d P) n d = valAt P 0 (2 * n + 2) % fermatW (LimbArray.w A) n
  /--
  Adds the `len₀` limbs of `src` from `so` on to the region of `T` limbs of `arr` from `o` on,
  from its limb `off` on, with the carry out into the rest of the region.
  -/
  addCoef : A → Nat → Nat → Nat → A → Nat → Nat → A
  addCoef_spec : ∀ (arr : A) (o T off : Nat) (src : A) (so len₀ : Nat),
    LimbArray.size arr < USize.size → o + T ≤ LimbArray.size arr → off ≤ T →
    LimbArray.size src < USize.size → so + len₀ ≤ LimbArray.size src →
    valAt arr o T + 2 ^ (LimbArray.w A * off) * valAt src so len₀ < 2 ^ (LimbArray.w A * T) →
    LimbArray.size (addCoef arr o T off src so len₀) = LimbArray.size arr ∧
      (∀ i, (i < o ∨ o + T ≤ i) →
        LimbArray.get (addCoef arr o T off src so len₀) i = LimbArray.get arr i) ∧
      valAt (addCoef arr o T off src so len₀) o T =
        valAt arr o T + 2 ^ (LimbArray.w A * off) * valAt src so len₀
  /-- Clears the `len` limbs of `arr` from `o` on. -/
  zeroRange : A → Nat → Nat → A
  zeroRange_spec : ∀ (arr : A) (o len : Nat), LimbArray.size arr < USize.size →
    o + len ≤ LimbArray.size arr →
    LimbArray.size (zeroRange arr o len) = LimbArray.size arr ∧
      (∀ i, (i < o ∨ o + len ≤ i) → LimbArray.get (zeroRange arr o len) i = LimbArray.get arr i) ∧
      valAt (zeroRange arr o len) o len = 0

namespace FFTOps

variable {A L : Type} [LA : LimbArray A L]

/-! ## Pieces -/

/-- Piece `i` of the `al` limbs of `a` from `as` on: limbs `i m` to `i m + m - 1`, or fewer. -/
@[expose] public def piece (a : A) (as al m i : Nat) : Nat :=
  valAt a (as + i * m) (min m (al - i * m))

/-- The first `L` pieces. -/
@[expose] public def pieces (a : A) (as al m L : Nat) : List Nat :=
  (List.range L).map (piece a as al m)

public theorem piece_lt (a : A) (as al m i : Nat) : piece a as al m i < 2 ^ (LA.w * m) :=
  Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (Nat.min_le_left _ _)))

private theorem polyVal_pieces_from (a : A) (as al m : Nat) (L : Nat) :
    ∀ i, polyVal (2 ^ (LA.w * m)) ((List.range L).map fun j => piece a as al m (i + j)) =
      valAt a (as + i * m) (min (L * m) (al - i * m)) := by
  induction L with
  | zero => intro i; simp [polyVal]
  | succ L ih =>
    intro i
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyVal]
    have e : ((fun j => piece a as al m (i + j)) ∘ Nat.succ) =
        fun j => piece a as al m ((i + 1) + j) := by
      funext j; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; lia
    rw [e, ih (i + 1), Nat.add_zero, piece]
    -- Split the limbs of the pieces `i` to `i + L` after the first.
    rcases Nat.le_total (al - i * m) m with h | h
    · rw [Nat.min_eq_right h, show al - (i + 1) * m = 0 by rw [Nat.add_mul]; lia,
        Nat.min_zero, valAt_zero, Nat.mul_zero, Nat.add_zero,
        Nat.min_eq_right (show al - i * m ≤ (L + 1) * m by rw [Nat.add_mul]; lia)]
    · rw [Nat.min_eq_left h, show (L + 1) * m = m + L * m by rw [Nat.add_mul]; lia,
        show min (m + L * m) (al - i * m) = m + min (L * m) (al - (i + 1) * m)
          by rw [Nat.add_mul]; lia, valAt_add,
        show as + i * m + m = as + (i + 1) * m by rw [Nat.add_mul]; lia]

/-- The pieces are the digits in base `2^(w m)`. -/
public theorem polyVal_pieces (a : A) (as al m L : Nat) (hL : al ≤ L * m) :
    polyVal (2 ^ (LA.w * m)) (pieces a as al m L) = valAt a as al := by
  have := polyVal_pieces_from a as al m L 0
  simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero, Nat.sub_zero,
    Nat.min_eq_right hL] at this
  rw [pieces, this]

public theorem length_pieces (a : A) (as al m L : Nat) : (pieces a as al m L).length = L := by
  simp [pieces]

public theorem getD_pieces (a : A) (as al m L i : Nat) :
    (pieces a as al m L).getD i 0 = if i < L then piece a as al m i else 0 := by
  rw [pieces, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · rename_i h; simp [h]
  · rename_i h; simp [h]

public theorem piece_eq_zero (a : A) (as al m i : Nat) (h : al ≤ i * m) :
    piece a as al m i = 0 := by
  rw [piece, show al - i * m = 0 by lia, Nat.min_zero, valAt_zero]

section

variable [W : WinOps A L]

/-! ## Scaling -/

/--
Divides windows `l` to `l + cnt - 1` of the block at `o` by `2ᵏ`, modulo `F`: multiplies them by
`2^(w n - k)` into the scratch window `t`, then subtracts that from the zero window `z`, since
`2^(-k) ≡ -2^(w n - k)`.
-/
@[expose, specialize] public def scaleLoop (n o t z k : Nat) : A → Nat → Nat → A
  | arr, _, 0 => arr
  | arr, l, cnt + 1 =>
    scaleLoop n o t z k (W.subMod (W.mulPow2 arr n t (o + l * (n + 1)) (LA.w * n - k)) n
      (o + l * (n + 1)) z t) (l + 1) cnt

public theorem scaleLoop_spec (n o t z k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hw : LA.w * n < USize.size) (cnt : Nat) :
    ∀ arr l, LA.size arr < USize.size → o + (l + cnt) * (n + 1) ≤ LA.size arr →
      t + n + 1 ≤ LA.size arr → z + n + 1 ≤ LA.size arr →
      (t + n + 1 ≤ o + l * (n + 1) ∨ o + (l + cnt) * (n + 1) ≤ t) →
      (z + n + 1 ≤ o + l * (n + 1) ∨ o + (l + cnt) * (n + 1) ≤ z) →
      (t + n + 1 ≤ z ∨ z + n + 1 ≤ t) → win arr n z = 0 →
      (∀ q, l ≤ q → q < l + cnt → coef arr n o q < fermatW LA.w n) →
      LA.size (scaleLoop n o t z k arr l cnt) = LA.size arr ∧
      (∀ j, (j < o + l * (n + 1) ∨ o + (l + cnt) * (n + 1) ≤ j) → (j < t ∨ t + n + 1 ≤ j) →
        LA.get (scaleLoop n o t z k arr l cnt) j = LA.get arr j) ∧
      (∀ q, l ≤ q → q < l + cnt → coef (scaleLoop n o t z k arr l cnt) n o q =
        (fermatW LA.w n - coef arr n o q * 2 ^ (LA.w * n - k) % fermatW LA.w n) %
          fermatW LA.w n) := by
  induction cnt with
  | zero =>
    intro arr l _ _ _ _ _ _ _ _ _
    exact ⟨rfl, fun _ _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr l hS hB ht hz htd hzd htz hz0 hv
    rw [scaleLoop]
    have hF := fermatW_pos LA.w n
    have hwn := Nat.mul_pos LA.w_pos hn
    have hww := Nat.mul_le_mul_right (n + 1) (show l + 1 ≤ l + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hww
    obtain ⟨m₁, m₂, m₃⟩ := W.mulPow2_spec arr n t (o + l * (n + 1)) (LA.w * n - k) hS ht (by lia)
      hn (by lia) (by lia) (by lia) (hv l (Nat.le_refl _) (by lia))
    generalize W.mulPow2 arr n t (o + l * (n + 1)) (LA.w * n - k) = a₁ at *
    have z₁ := win_of_untouched m₂ (o := z) (by lia)
    have x₁ := win_of_untouched m₂ (o := o + l * (n + 1)) (by lia)
    obtain ⟨s₁, s₂, s₃⟩ := W.subMod_spec a₁ n (o + l * (n + 1)) z t (by lia) (by lia) (by lia)
      (by lia) hn (by lia) (by lia) (by rw [z₁, hz0]; exact hF) (by rw [m₃]; exact Nat.mod_lt _ hF)
    generalize W.subMod a₁ n (o + l * (n + 1)) z t = a₂ at *
    have hu : ∀ q, l + 1 ≤ q → q < l + (cnt + 1) → coef a₂ n o q = coef arr n o q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ l + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      show win a₂ n _ = win arr n _
      rw [win_of_untouched s₂ (by lia), win_of_untouched m₂ (by lia)]
    have z₂ := win_of_untouched s₂ (o := z) (by lia)
    obtain ⟨i₁, i₂, i₃⟩ := ih a₂ (l + 1) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) htz
      (by rw [z₂, z₁, hz0]) fun q h₁ h₂ => by rw [hu q h₁ (by lia)]; exact hv q (by lia) (by lia)
    refine ⟨by rw [i₁, s₁, m₁], fun j h₁ h₂ => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by lia) h₂, s₂ j (by lia), m₂ j h₂]
    · by_cases e : q = l
      · subst e
        have : coef (scaleLoop n o t z k a₂ (q + 1) cnt) n o q = coef a₂ n o q :=
          win_congr fun j _ _ => i₂ j (by lia) (by lia)
        rw [this]
        show win a₂ n _ = _
        rw [s₃, z₁, hz0, Nat.zero_add, m₃]
      · rw [i₃ q (by lia) (by lia), hu q (by lia) h₂]


end

variable [R : FFTOps A L]

public theorem valAt_zeros (n lo m : Nat) : valAt (R.zeros n) lo m = 0 :=
  valAt_eq_zero m fun i _ _ => R.val_get_zeros n i

/-! ## Loading the pieces -/

/-- Loads pieces `i` to `i + cnt - 1` into the windows of the block at `o`. -/
@[expose, specialize] public def loadLoop (o n m : Nat) (a : A) (as al : Nat) :
    A → Nat → Nat → A
  | arr, _, 0 => arr
  | arr, i, cnt + 1 =>
    loadLoop o n m a as al (R.addRange arr (o + i * (n + 1)) (n + 1) a (as + min (i * m) al)
      (min m (al - i * m))) (i + 1) cnt

public theorem loadLoop_spec (o n m : Nat) (a : A) (as al : Nat) (hm : m ≤ n + 1)
    (haS : LA.size a < USize.size) (ha : as + al ≤ LA.size a) (cnt : Nat) :
    ∀ arr i, LA.size arr < USize.size → o + (i + cnt) * (n + 1) ≤ LA.size arr →
      (∀ p, i ≤ p → p < i + cnt → coef arr n o p = 0) →
      LA.size (R.loadLoop o n m a as al arr i cnt) = LA.size arr ∧
      (∀ j, (j < o + i * (n + 1) ∨ o + (i + cnt) * (n + 1) ≤ j) →
        LA.get (R.loadLoop o n m a as al arr i cnt) j = LA.get arr j) ∧
      (∀ p, i ≤ p → p < i + cnt →
        coef (R.loadLoop o n m a as al arr i cnt) n o p = piece a as al m p) := by
  induction cnt with
  | zero => intro arr i _ _ _; exact ⟨rfl, fun _ _ => rfl, fun p h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr i hS hB hz
    have hw := Nat.mul_le_mul_right (n + 1) (show i + 1 ≤ i + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    have hpc : valAt a (as + min (i * m) al) (min m (al - i * m)) = piece a as al m i := by
      rw [piece]
      rcases Nat.le_total (i * m) al with h | h
      · rw [Nat.min_eq_left h]
      · rw [show al - i * m = 0 by lia, Nat.min_zero, valAt_zero, valAt_zero]
    have h₀ := hz i (Nat.le_refl _) (by lia)
    have hX : 2 ^ (LA.w * m) ≤ 2 ^ (LA.w * (n + 1)) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hm)
    have hlt := piece_lt a as al m i
    simp only [coef, win] at h₀
    obtain ⟨a₁, a₂, a₃⟩ := R.addRange_spec arr (o + i * (n + 1)) (n + 1) a (as + min (i * m) al)
      (min m (al - i * m)) hS (by lia) haS (by lia) (by lia) (by rw [h₀, hpc]; lia)
    rw [loadLoop]
    generalize R.addRange arr (o + i * (n + 1)) (n + 1) a (as + min (i * m) al)
      (min m (al - i * m)) = q at *
    obtain ⟨i₁, i₂, i₃⟩ := ih q (i + 1) (by lia) (by rw [a₁]; lia) fun p h₁ h₂ => by
      have d := Nat.mul_le_mul_right (n + 1) h₁
      rw [Nat.add_mul, Nat.one_mul] at d
      rw [← hz p (by lia) (by lia)]
      exact win_congr fun j _ _ => a₂ j (by lia)
    have hq : coef q n o i = piece a as al m i := by
      simp only [coef, win]
      rw [a₃, h₀, hpc, Nat.zero_add]
    refine ⟨i₁.trans a₁, fun j hj => ?_, fun p h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), a₂ j (by lia)]
    · by_cases e : p = i
      · subst e
        rw [← hq]
        have d := Nat.mul_le_mul_right (n + 1) (Nat.le_refl (p + 1))
        exact win_congr fun j _ _ => i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia)
      · exact i₃ p (by lia) (by lia)

/-! ## Pointwise products -/

/--
`mulP P arr x y n` is the product of the windows of `n + 1` limbs at `x` and `y` of `arr`, on
`2 n + 2` limbs, possibly in the array `P` of that size.
-/
public def IsMulP (mulP : A → A → Nat → Nat → Nat → A) (n : Nat) : Prop :=
  ∀ P arr x y, LA.size P = 2 * n + 2 → LA.size P < USize.size → LA.size arr < USize.size →
    x + n + 1 ≤ LA.size arr → y + n + 1 ≤ LA.size arr →
    LA.size (mulP P arr x y n) = 2 * n + 2 ∧
      valAt (mulP P arr x y n) 0 (2 * n + 2) = win arr n x * win arr n y

/-- `sqrP P arr x n` is the square of the window of `n + 1` limbs at `x` of `arr`. -/
public def IsSqrP (sqrP : A → A → Nat → Nat → A) (n : Nat) : Prop :=
  ∀ P arr x, LA.size P = 2 * n + 2 → LA.size P < USize.size → LA.size arr < USize.size →
    x + n + 1 ≤ LA.size arr →
    LA.size (sqrP P arr x n) = 2 * n + 2 ∧
      valAt (sqrP P arr x n) 0 (2 * n + 2) = win arr n x * win arr n x

/--
The pointwise products of windows `p` to `p + cnt - 1` of the blocks at `oA` and `oB`, into the
first, through the array `P` of `2 n + 2` limbs.
-/
@[expose, specialize] public def pointLoop (mulP : A → A → Nat → Nat → Nat → A) (n oA oB : Nat) :
    A → A → Nat → Nat → A
  | arr, _, _, 0 => arr
  | arr, P, p, cnt + 1 =>
    let P := mulP P arr (oA + p * (n + 1)) (oB + p * (n + 1)) n
    pointLoop mulP n oA oB (R.reduce arr n (oA + p * (n + 1)) P) P (p + 1) cnt

public theorem pointLoop_spec (mulP : A → A → Nat → Nat → Nat → A) (n oA oB : Nat) (hn : 1 ≤ n)
    (hmul : IsMulP mulP n) (cnt : Nat) :
    ∀ arr P p, LA.size P = 2 * n + 2 → LA.size P < USize.size → LA.size arr < USize.size →
      oA + (p + cnt) * (n + 1) ≤ oB → oB + (p + cnt) * (n + 1) ≤ LA.size arr →
      (∀ q, p ≤ q → q < p + cnt →
        coef arr n oA q < fermatW LA.w n ∧ coef arr n oB q < fermatW LA.w n) →
      LA.size (R.pointLoop mulP n oA oB arr P p cnt) = LA.size arr ∧
      (∀ j, (j < oA + p * (n + 1) ∨ oA + (p + cnt) * (n + 1) ≤ j) →
        LA.get (R.pointLoop mulP n oA oB arr P p cnt) j = LA.get arr j) ∧
      (∀ q, p ≤ q → q < p + cnt →
        coef (R.pointLoop mulP n oA oB arr P p cnt) n oA q =
          coef arr n oA q * coef arr n oB q % fermatW LA.w n) := by
  induction cnt with
  | zero =>
    intro arr P p _ _ _ _ _ _
    exact ⟨rfl, fun _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr P p hP hPS hS hAB hB hv
    have hw := Nat.mul_le_mul_right (n + 1) (show p + 1 ≤ p + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨m₁, m₂⟩ := hmul P arr (oA + p * (n + 1)) (oB + p * (n + 1)) hP hPS hS (by lia)
      (by lia)
    rw [pointLoop]
    generalize mulP P arr (oA + p * (n + 1)) (oB + p * (n + 1)) n = P' at *
    obtain ⟨hvA, hvB⟩ := hv p (Nat.le_refl _) (by lia)
    simp only [coef, win, fermatW] at hvA hvB m₂
    obtain ⟨r₁, r₂, r₃⟩ := R.reduce_spec arr n (oA + p * (n + 1)) P' hS (by lia) hn m₁
      (by rw [m₁]; lia) (by rw [m₂]; exact Nat.mul_le_mul (by lia) (by lia))
    generalize R.reduce arr n (oA + p * (n + 1)) P' = a₁ at *
    have hu : ∀ q, p + 1 ≤ q → q < p + (cnt + 1) →
        coef a₁ n oA q = coef arr n oA q ∧ coef a₁ n oB q = coef arr n oB q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ p + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      exact ⟨win_congr fun j _ _ => r₂ j (by lia), win_congr fun j _ _ => r₂ j (by lia)⟩
    obtain ⟨i₁, i₂, i₃⟩ := ih a₁ P' (p + 1) m₁ (by rw [m₁]; lia)
      (by rw [r₁]; exact hS) (by lia) (by rw [r₁]; lia) fun q h₁ h₂ => by
        rw [(hu q h₁ (by lia)).1, (hu q h₁ (by lia)).2]; exact hv q (by lia) (by lia)
    refine ⟨i₁.trans r₁, fun j hj => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), r₂ j (by lia)]
    · by_cases e : q = p
      · subst e
        have : coef (R.pointLoop mulP n oA oB a₁ P' (q + 1) cnt) n oA q = coef a₁ n oA q :=
          win_congr fun j _ _ => i₂ j (by lia)
        rw [this]
        exact r₃.trans (by rw [m₂])
      · rw [i₃ q (by lia) (by lia), (hu q (by lia) h₂).1, (hu q (by lia) h₂).2]

/--
The pointwise squares of windows `p` to `p + cnt - 1` of the block at `oA`, through the array `P`
of `2 n + 2` limbs.
-/
@[expose, specialize] public def pointSqrLoop (sqrP : A → A → Nat → Nat → A) (n oA : Nat) :
    A → A → Nat → Nat → A
  | arr, _, _, 0 => arr
  | arr, P, p, cnt + 1 =>
    let P := sqrP P arr (oA + p * (n + 1)) n
    pointSqrLoop sqrP n oA (R.reduce arr n (oA + p * (n + 1)) P) P (p + 1) cnt

public theorem pointSqrLoop_spec (sqrP : A → A → Nat → Nat → A) (n oA : Nat) (hn : 1 ≤ n)
    (hsqr : IsSqrP sqrP n) (cnt : Nat) :
    ∀ arr P p, LA.size P = 2 * n + 2 → LA.size P < USize.size → LA.size arr < USize.size →
      oA + (p + cnt) * (n + 1) ≤ LA.size arr →
      (∀ q, p ≤ q → q < p + cnt → coef arr n oA q < fermatW LA.w n) →
      LA.size (R.pointSqrLoop sqrP n oA arr P p cnt) = LA.size arr ∧
      (∀ j, (j < oA + p * (n + 1) ∨ oA + (p + cnt) * (n + 1) ≤ j) →
        LA.get (R.pointSqrLoop sqrP n oA arr P p cnt) j = LA.get arr j) ∧
      (∀ q, p ≤ q → q < p + cnt →
        coef (R.pointSqrLoop sqrP n oA arr P p cnt) n oA q =
          coef arr n oA q * coef arr n oA q % fermatW LA.w n) := by
  induction cnt with
  | zero =>
    intro arr P p _ _ _ _ _
    exact ⟨rfl, fun _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr P p hP hPS hS hB hv
    have hw := Nat.mul_le_mul_right (n + 1) (show p + 1 ≤ p + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨m₁, m₂⟩ := hsqr P arr (oA + p * (n + 1)) hP hPS hS (by lia)
    rw [pointSqrLoop]
    generalize sqrP P arr (oA + p * (n + 1)) n = P' at *
    have hvA := hv p (Nat.le_refl _) (by lia)
    simp only [coef, win, fermatW] at hvA m₂
    obtain ⟨r₁, r₂, r₃⟩ := R.reduce_spec arr n (oA + p * (n + 1)) P' hS (by lia) hn m₁
      (by rw [m₁]; lia) (by rw [m₂]; exact Nat.mul_le_mul (by lia) (by lia))
    generalize R.reduce arr n (oA + p * (n + 1)) P' = a₁ at *
    have hu : ∀ q, p + 1 ≤ q → q < p + (cnt + 1) → coef a₁ n oA q = coef arr n oA q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ p + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      exact win_congr fun j _ _ => r₂ j (by lia)
    obtain ⟨i₁, i₂, i₃⟩ := ih a₁ P' (p + 1) m₁ (by rw [m₁]; lia)
      (by rw [r₁]; exact hS) (by rw [r₁]; lia) fun q h₁ h₂ => by
        rw [hu q h₁ (by lia)]; exact hv q (by lia) (by lia)
    refine ⟨i₁.trans r₁, fun j hj => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), r₂ j (by lia)]
    · by_cases e : q = p
      · subst e
        have : coef (R.pointSqrLoop sqrP n oA a₁ P' (q + 1) cnt) n oA q = coef a₁ n oA q :=
          win_congr fun j _ _ => i₂ j (by lia)
        rw [this]
        exact r₃.trans (by rw [m₂])
      · rw [i₃ q (by lia) (by lia), hu q (by lia) h₂]

/-! ## Recombination -/

/--
Adds windows `l` to `l + cnt - 1` of the block at `oA` of `src`, the coefficients, to the region
of `T` limbs at `o` of `arr`, window `i` from limb `i m` on.
-/
@[expose, specialize] public def recLoop (T m n oA : Nat) (src : A) : A → Nat → Nat → Nat → A
  | arr, _, _, 0 => arr
  | arr, o, l, cnt + 1 =>
    recLoop T m n oA src
      (if l * m ≤ T then R.addCoef arr o T (l * m) src (oA + l * (n + 1)) (n + 1) else arr) o
      (l + 1) cnt

public theorem recLoop_spec (T m n oA : Nat) (src : A) (hsS : LA.size src < USize.size)
    (cnt : Nat) :
    ∀ arr o l, LA.size arr < USize.size → o + T ≤ LA.size arr →
      oA + (l + cnt) * (n + 1) ≤ LA.size src →
      valAt arr o T + sumRange (fun i => 2 ^ (LA.w * ((l + i) * m)) * coef src n oA (l + i)) cnt <
        2 ^ (LA.w * T) →
      LA.size (R.recLoop T m n oA src arr o l cnt) = LA.size arr ∧
      (∀ j, (j < o ∨ o + T ≤ j) → LA.get (R.recLoop T m n oA src arr o l cnt) j = LA.get arr j) ∧
      valAt (R.recLoop T m n oA src arr o l cnt) o T = valAt arr o T +
        sumRange (fun i => 2 ^ (LA.w * ((l + i) * m)) * coef src n oA (l + i)) cnt := by
  induction cnt with
  | zero => intro arr o l _ _ _ _; exact ⟨rfl, fun _ _ => rfl, by simp [recLoop]⟩
  | succ cnt ih =>
    intro arr o l hS hT hsrc hsum
    rw [sumRange_succ_left] at hsum ⊢
    simp only [Nat.add_zero] at hsum ⊢
    have hw := Nat.mul_le_mul_right (n + 1) (show l + 1 ≤ l + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    have hs' : sumRange (fun i => 2 ^ (LA.w * ((l + (i + 1)) * m)) * coef src n oA (l + (i + 1)))
        cnt = sumRange (fun i => 2 ^ (LA.w * ((l + 1 + i) * m)) * coef src n oA (l + 1 + i)) cnt :=
      sumRange_congr fun i _ => by rw [show l + (i + 1) = l + 1 + i by lia]
    rw [hs'] at hsum ⊢
    rw [recLoop]
    split
    · rename_i hl
      obtain ⟨c₁, c₂, c₃⟩ := R.addCoef_spec arr o T (l * m) src (oA + l * (n + 1)) (n + 1) hS hT
        hl hsS (by lia) (by simp only [coef, win] at hsum; lia)
      generalize R.addCoef arr o T (l * m) src (oA + l * (n + 1)) (n + 1) = a₁ at *
      obtain ⟨i₁, i₂, i₃⟩ := ih a₁ o (l + 1) (by lia) (by lia) (by lia)
        (by rw [c₃]; simp only [coef, win] at hsum ⊢; lia)
      refine ⟨i₁.trans c₁, fun j hj => by rw [i₂ j hj, c₂ j hj], ?_⟩
      rw [i₃, c₃]
      simp only [coef, win]
      lia
    · rename_i hl
      -- The coefficient starts past the region, so it is zero.
      have hc : coef src n oA l = 0 := by
        rcases Nat.eq_zero_or_pos (coef src n oA l) with h | h
        · exact h
        · have := Nat.mul_le_mul_left (2 ^ (LA.w * (l * m))) h
          have : 2 ^ (LA.w * T) ≤ 2 ^ (LA.w * (l * m)) :=
            Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by lia))
          lia
      obtain ⟨i₁, i₂, i₃⟩ := ih arr o (l + 1) hS hT (by lia) (by rw [hc] at hsum; lia)
      refine ⟨i₁, i₂, ?_⟩
      rw [i₃, hc]
      lia

variable [W : WinOps A L]

/-! ## The multiplication -/

/--
`a b` into the `al + bl` limbs of `r` from `rs` on, with `K = 2ᵏ` windows of `n + 1` limbs for
the pieces of `m` limbs of each operand and `mulP` for the pointwise products. The layout of the
flat array: the block of `a` at `0`, the block of `b` at `K (n + 1)`, the scratch window, and a
zero window.
-/
@[expose, specialize] public def fftMulAt (mulP : A → A → Nat → Nat → Nat → A) (r : A) (rs : Nat)
    (a : A) (as al : Nat) (b : A) (bs bl k m n : Nat) : A :=
  let K := 2 ^ k
  let oB := K * (n + 1)
  let t := 2 * K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (LA.w * n) / K
  let FA := R.loadLoop 0 n m a as al (R.zeros (z + (n + 1))) 0 K
  let FA := R.loadLoop oB n m b bs bl FA 0 K
  let FA := WinOps.fwd n t k FA 0 σ
  let FA := WinOps.fwd n t k FA oB σ
  let FA := R.pointLoop mulP n 0 oB FA (R.zeros (2 * n + 2)) 0 K
  let FA := WinOps.inv n t k FA 0 σ
  let FA := scaleLoop n 0 t z k FA 0 K
  R.recLoop (al + bl) m n 0 FA (R.zeroRange r rs (al + bl)) rs 0 K

/-- The parameters of `fftMulAt` for which it computes `a b`. -/
public structure FFTParams (r : A) (rs : Nat) (a : A) (as al : Nat) (b : A) (bs bl k m n : Nat) :
    Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (LA.w * n) % 2 ^ k = 0
  ha : 0 < al
  hb : 0 < bl
  hpieces : (al + m - 1) / m + (bl + m - 1) / m ≤ 2 ^ k + 1
  hbits : 2 ^ k * 2 ^ (LA.w * m + LA.w * m) ≤ 2 ^ (LA.w * n)
  hr : rs + (al + bl) ≤ LA.size r
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  hw : LA.w * n < USize.size
  haS : LA.size a < USize.size
  hbS : LA.size b < USize.size
  hrS : LA.size r < USize.size
  hab : as + al ≤ LA.size a
  hbb : bs + bl ≤ LA.size b

/-- Enough pieces of `m` limbs to cover `x` limbs. -/
private theorem cover (x m : Nat) (hm : 1 ≤ m) : x ≤ (x + m - 1) / m * m := by
  have h₁ := Nat.div_add_mod (x + m - 1) m
  have h₂ := Nat.mod_lt (x + m - 1) (show 0 < m by lia)
  rw [Nat.mul_comm] at h₁
  lia

omit W R in
private theorem coef_pieces (a : A) (as al m L K i : Nat) (hL : al ≤ L * m) :
    (if i < K then piece a as al m i else 0) = (pieces a as al m L).getD i 0 ∨ K ≤ i := by
  rcases Nat.lt_or_ge i K with h | h
  · left
    rw [ite_eq_left h, getD_pieces]
    split
    · rfl
    · rename_i h'
      exact piece_eq_zero a as al m i (Nat.le_trans hL (Nat.mul_le_mul_right m (by lia)))
  · exact .inr h

set_option maxHeartbeats 800000 in
public theorem fftMulAt_spec (mulP : A → A → Nat → Nat → Nat → A) (r : A) (rs : Nat) (a : A)
    (as al : Nat) (b : A) (bs bl k m n : Nat) (hp : FFTParams r rs a as al b bs bl k m n)
    (hmul : IsMulP mulP n) :
    LA.size (R.fftMulAt mulP r rs a as al b bs bl k m n) = LA.size r ∧
      (∀ i, (i < rs ∨ rs + (al + bl) ≤ i) →
        LA.get (R.fftMulAt mulP r rs a as al b bs bl k m n) i = LA.get r i) ∧
      valAt (R.fftMulAt mulP r rs a as al b bs bl k m n) rs (al + bl) =
        valAt a as al * valAt b bs bl := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hbits, hr, hS, hW, haS, hbS, hrS, hab, hbb⟩ := hp
  have hF₀ := fermatW_pos LA.w n
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (LA.w * n) / 2 ^ k * 2 ^ k = 2 * (LA.w * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftMulAt]
  generalize 2 * (LA.w * n) / 2 ^ k = σ at *
  -- The layout.
  have hw := Nat.mul_le_mul_right (n + 1) (show 2 ^ k ≤ 2 * 2 ^ k by lia)
  have hsz : LA.size (R.zeros (2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1))) =
      2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) := R.size_zeros _
  have hSz : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    rw [show 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = (2 * 2 ^ k + 2) * (n + 1) by
      rw [Nat.add_mul]; lia]
    exact hS
  have hBB : 2 ^ k * (n + 1) + 2 ^ k * (n + 1) = 2 * 2 ^ k * (n + 1) := by rw [Nat.mul_assoc]; lia
  generalize hS₀ : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := R.loadLoop_spec 0 n m a as al (by lia) haS hab (2 ^ k)
    (R.zeros S) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_zeros ..)
  generalize R.loadLoop 0 n m a as al (R.zeros S) 0 (2 ^ k) = A₁ at *
  rw [hsz] at l₁
  -- Loading `b`.
  obtain ⟨m₁, m₂, m₃⟩ := R.loadLoop_spec (2 ^ k * (n + 1)) n m b bs bl (by lia) hbS hbb (2 ^ k) A₁ 0
    (by rw [l₁]; exact hSz) (by rw [l₁]; lia) (fun p _ hp => by
      have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) (by lia)
      show win A₁ n _ = 0
      rw [win_congr fun j _ _ => l₂ j (by lia)]
      exact valAt_zeros ..)
  generalize R.loadLoop (2 ^ k * (n + 1)) n m b bs bl A₁ 0 (2 ^ k) = A₂ at *
  rw [l₁] at m₁
  have cA : ∀ p < 2 ^ k, coef A₂ n 0 p = piece a as al m p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    rw [← l₃ p (by lia) (by lia)]
    exact win_congr fun j _ _ => m₂ j (by lia)
  have cB : ∀ p < 2 ^ k, coef A₂ n (2 ^ k * (n + 1)) p = piece b bs bl m p :=
    fun p hp => m₃ p (by lia) (by lia)
  have hXF : 2 ^ (LA.w * m) < fermatW LA.w n := by
    simp only [fermatW]
    have : 2 ^ (LA.w * m) ≤ 2 ^ (LA.w * n) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hmn)
    lia
  -- The forward transforms.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hW k A₂ 0 σ hσ
    ⟨by rw [m₁]; exact hSz, by rw [m₁]; lia, by rw [m₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize WinOps.fwd n (2 * 2 ^ k * (n + 1)) k A₂ 0 σ = A₃ at *
  have cB₃ : ∀ p < 2 ^ k, coef A₃ n (2 ^ k * (n + 1)) p = piece b bs bl m p := by
    intro p hp
    have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) hp
    rw [← cB p hp]
    exact win_congr fun j _ _ => f₂ j (by lia) (by lia)
  obtain ⟨g₁, g₂, g₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hW k A₃ (2 ^ k * (n + 1)) σ hσ
    ⟨by rw [f₁, m₁]; exact hSz, by rw [f₁, m₁]; lia, by rw [f₁, m₁]; lia, by lia⟩
    (fun p hp => by rw [cB₃ p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize WinOps.fwd n (2 * 2 ^ k * (n + 1)) k A₃ (2 ^ k * (n + 1)) σ = A₄ at *
  have cA₄ : ∀ p < 2 ^ k, coef A₄ n 0 p = coef A₃ n 0 p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    exact win_congr fun j _ _ => g₂ j (by lia) (by lia)
  -- The pointwise products.
  obtain ⟨p₁, p₂, p₃⟩ := R.pointLoop_spec mulP n 0 (2 ^ k * (n + 1)) hn hmul (2 ^ k) A₄
    (R.zeros (2 * n + 2)) 0 (R.size_zeros _) (by rw [R.size_zeros]; lia)
    (by rw [g₁, f₁, m₁]; exact hSz)
    (by lia) (by rw [g₁, f₁, m₁]; lia) (fun q _ hq => by
      rw [cA₄ q (by lia), f₃ q (by lia), g₃ q (by lia)]
      exact ⟨Nat.mod_lt _ hF₀, Nat.mod_lt _ hF₀⟩)
  generalize R.pointLoop mulP n 0 (2 ^ k * (n + 1)) A₄ (R.zeros (2 * n + 2)) 0
    (2 ^ k) =
    A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 * 2 ^ k * (n + 1)) hn hW k A₅ 0 σ hσ
    ⟨by rw [p₁, g₁, f₁, m₁]; exact hSz, by rw [p₁, g₁, f₁, m₁]; lia, by rw [p₁, g₁, f₁, m₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize WinOps.inv n (2 * 2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) =
        win (R.zeros S) n (2 * 2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), g₂ j (by lia) (by lia), f₂ j (by lia) (by lia),
          m₂ j (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_zeros ..
  -- The division by `2ᵏ`.
  have hsz₆ : LA.size A₆ = S := by rw [v₁, p₁, g₁, f₁, m₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k
    hn hk hW (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
    (by rw [hsz₆]; lia) (by lia) (by lia) (by lia) hz
    (fun q _ hq => by rw [v₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize scaleLoop n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k A₆ 0 (2 ^ k) =
    A₇ at *
  -- The coefficients are those of the product of the pieces.
  have hla := cover al m hm
  have hlb := cover bl m hm
  have hla₁ : 1 ≤ (al + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  have hlb₁ : 1 ≤ (bl + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  generalize (al + m - 1) / m = la at *
  generalize (bl + m - 1) / m = lb at *
  have hαL : ∀ i < 2 ^ k, coef A₂ n 0 i = (pieces a as al m la).getD i 0 := fun i hi => by
    rw [cA i hi]
    rcases coef_pieces a as al m la (2 ^ k) i hla with h | h
    · rw [← h, ite_eq_left hi]
    · lia
  have hβL : ∀ i < 2 ^ k, coef A₂ n (2 ^ k * (n + 1)) i = (pieces b bs bl m lb).getD i 0 :=
    fun i hi => by
      rw [cB i hi]
      rcases coef_pieces b bs bl m lb (2 ^ k) i hlb with h | h
      · rw [← h, ite_eq_left hi]
      · lia
  have hβne : pieces b bs bl m lb ≠ [] := by
    intro h; have := congrArg List.length h; rw [length_pieces] at this; simp at this; lia
  have hc : ∀ l < 2 ^ k,
      coef A₇ n 0 l = (polyMul (pieces a as al m la) (pieces b bs bl m lb)).getD l 0 := by
    intro l hl
    rw [s₃ l (by lia) (by lia), v₃ l hl]
    rw [← fft_coef (pieces a as al m la) (pieces b bs bl m lb) k (LA.w * n) σ (2 ^ (LA.w * m))
      (F := fermatW LA.w n) rfl
      hk hσ
      (by rw [length_pieces, length_pieces]; lia) hβne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hβ : ∀ q, sumRange (fun i => coef A₃ n (2 ^ k * (n + 1)) i * 2 ^ (σ * i * rev k q))
        (2 ^ k) =
          sumRange (fun i => (pieces b bs bl m lb).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [cB₃ i hi, ← cB i hi, hβL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (LA.w * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermatW LA.w n *
              (sumRange (fun i => (pieces b bs bl m lb).getD i 0 * 2 ^ (σ * i * rev k p))
                (2 ^ k) % fermatW LA.w n) % fermatW LA.w n *
              2 ^ ((2 * (LA.w * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), cA₄ q hq, f₃ q hq, g₃ q hq, hα, hβ]
    rw [hsum]
  -- The value of the coefficients at `2^(64 m)`.
  generalize hZ : polyMul (pieces a as al m la) (pieces b bs bl m lb) = Z at hc
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a as al m la) (pieces b bs bl m lb) hβne
    rw [length_pieces, length_pieces] at this; lia
  have hab : sumRange (fun i => 2 ^ (LA.w * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      valAt a as al * valAt b bs bl := by
    rw [← polyVal_pieces a as al m la hla, ← polyVal_pieces b bs bl m lb hlb, ← polyVal_polyMul, hZ,
      polyVal_eq_sumRange _ Z _ hZK]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hablt : valAt a as al * valAt b bs bl < 2 ^ (LA.w * (al + bl)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : valAt a as al < 2 ^ (LA.w * al) := by exact valAt_lt ..
    have h₂ : valAt b bs bl < 2 ^ (LA.w * bl) := by exact valAt_lt ..
    exact Nat.mul_lt_mul'' h₁ h₂
  -- Zeroing the result, and adding the coefficients.
  obtain ⟨z₁, z₂, z₃⟩ := R.zeroRange_spec r rs (al + bl) hrS (by lia)
  generalize R.zeroRange r rs (al + bl) = R₀ at *
  have hsz₇ : LA.size A₇ = S := by rw [s₁, hsz₆]
  obtain ⟨c₁, c₂, c₃⟩ := R.recLoop_spec (al + bl) m n 0 A₇
    (by rw [hsz₇]; exact hSz) (2 ^ k) R₀ rs 0 (by rw [z₁]; exact hrS) (by rw [z₁]; lia)
    (by rw [hsz₇]; lia) (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hab]


/-! ## The product modulo `2^(w N) - 1` -/

/--
`a b` modulo `2^(w N) - 1`, for `N = m 2ᵏ`, into the `N + n + 1` limbs of `r` from `rs` on, like
`fftMulAt` but with the pieces of each operand wrapping around: `K = 2ᵏ` pieces of `m` limbs of
each, the cyclic convolution of the transforms, and the coefficients added at `2^(w m)`, whose sum
is `≡ a b` modulo `2^(w N) - 1` since `2^(w m K) ≡ 1`. Like GMP's `mpn_mulmod_bnm1`, it costs
about half a product of the same operands.
-/
@[expose, specialize] public def fftMulModAt (mulP : A → A → Nat → Nat → Nat → A) (r : A)
    (rs : Nat) (a : A) (as al : Nat) (b : A) (bs bl k m n : Nat) : A :=
  let K := 2 ^ k
  let oB := K * (n + 1)
  let t := 2 * K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (LA.w * n) / K
  let FA := R.loadLoop 0 n m a as al (R.zeros (z + (n + 1))) 0 K
  let FA := R.loadLoop oB n m b bs bl FA 0 K
  let FA := WinOps.fwd n t k FA 0 σ
  let FA := WinOps.fwd n t k FA oB σ
  let FA := R.pointLoop mulP n 0 oB FA (R.zeros (2 * n + 2)) 0 K
  let FA := WinOps.inv n t k FA 0 σ
  let FA := scaleLoop n 0 t z k FA 0 K
  R.recLoop (m * K + n + 1) m n 0 FA (R.zeroRange r rs (m * K + n + 1)) rs 0 K

/-- The parameters of `fftMulModAt` for which it computes `a b` modulo `2^(w m 2ᵏ) - 1`. -/
public structure FFTModParams (r : A) (rs : Nat) (a : A) (as al : Nat) (b : A) (bs bl k m n : Nat) :
    Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (LA.w * n) % 2 ^ k = 0
  ha : 0 < al
  hb : 0 < bl
  hla : al ≤ m * 2 ^ k
  hlb : bl ≤ m * 2 ^ k
  hbits : 2 * 2 ^ k * 2 ^ (LA.w * m + LA.w * m) ≤ 2 ^ (LA.w * n)
  hr : rs + (m * 2 ^ k + n + 1) ≤ LA.size r
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  hw : LA.w * n < USize.size
  haS : LA.size a < USize.size
  hbS : LA.size b < USize.size
  hrS : LA.size r < USize.size
  hab : as + al ≤ LA.size a
  hbb : bs + bl ≤ LA.size b

/-- A geometric bound: `∑_{i<K} c_i Xⁱ < (C + 1) X^K` for `c_i ≤ C` and `X ≥ 2`. -/
private theorem sum_pow_lt (c : Nat → Nat) (C X K : Nat) (hX : 2 ≤ X) (hc : ∀ i < K, c i ≤ C) :
    sumRange (fun i => X ^ i * c i) K < (C + 1) * X ^ K := by
  induction K with
  | zero => simp [sumRange]
  | succ K ih =>
    rw [sumRange_succ]
    have h₁ := ih fun i hi => hc i (by lia)
    have h₂ := Nat.mul_le_mul_left (X ^ K) (hc K (by lia))
    have h₃ : (C + 1) * X ^ K + X ^ K * C ≤ (C + 1) * X ^ (K + 1) := by
      rw [Nat.pow_succ]
      have := Nat.mul_le_mul_left ((C + 1) * X ^ K) hX
      rw [Nat.mul_comm (X ^ K) C]
      lia
    lia

set_option maxHeartbeats 800000 in
public theorem fftMulModAt_spec (mulP : A → A → Nat → Nat → Nat → A) (r : A) (rs : Nat) (a : A)
    (as al : Nat) (b : A) (bs bl k m n : Nat) (hp : FFTModParams r rs a as al b bs bl k m n)
    (hmul : IsMulP mulP n) :
    LA.size (R.fftMulModAt mulP r rs a as al b bs bl k m n) = LA.size r ∧
      (∀ i, (i < rs ∨ rs + (m * 2 ^ k + n + 1) ≤ i) →
        LA.get (R.fftMulModAt mulP r rs a as al b bs bl k m n) i = LA.get r i) ∧
      valAt (R.fftMulModAt mulP r rs a as al b bs bl k m n) rs (m * 2 ^ k + n + 1) %
          (2 ^ (LA.w * (m * 2 ^ k)) - 1) =
        valAt a as al * valAt b bs bl % (2 ^ (LA.w * (m * 2 ^ k)) - 1) := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpa, hpb, hbits, hr, hS, hW, haS, hbS, hrS, hab, hbb⟩ := hp
  have hF₀ := fermatW_pos LA.w n
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (LA.w * n) / 2 ^ k * 2 ^ k = 2 * (LA.w * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftMulModAt]
  generalize 2 * (LA.w * n) / 2 ^ k = σ at *
  -- The layout.
  have hw := Nat.mul_le_mul_right (n + 1) (show 2 ^ k ≤ 2 * 2 ^ k by lia)
  have hsz : LA.size (R.zeros (2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1))) =
      2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) := R.size_zeros _
  have hSz : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    rw [show 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = (2 * 2 ^ k + 2) * (n + 1) by
      rw [Nat.add_mul]; lia]
    exact hS
  have hBB : 2 ^ k * (n + 1) + 2 ^ k * (n + 1) = 2 * 2 ^ k * (n + 1) := by rw [Nat.mul_assoc]; lia
  generalize hS₀ : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := R.loadLoop_spec 0 n m a as al (by lia) haS hab (2 ^ k)
    (R.zeros S) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_zeros ..)
  generalize R.loadLoop 0 n m a as al (R.zeros S) 0 (2 ^ k) = A₁ at *
  rw [hsz] at l₁
  -- Loading `b`.
  obtain ⟨m₁, m₂, m₃⟩ := R.loadLoop_spec (2 ^ k * (n + 1)) n m b bs bl (by lia) hbS hbb (2 ^ k) A₁ 0
    (by rw [l₁]; exact hSz) (by rw [l₁]; lia) (fun p _ hp => by
      have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) (by lia)
      show win A₁ n _ = 0
      rw [win_congr fun j _ _ => l₂ j (by lia)]
      exact valAt_zeros ..)
  generalize R.loadLoop (2 ^ k * (n + 1)) n m b bs bl A₁ 0 (2 ^ k) = A₂ at *
  rw [l₁] at m₁
  have cA : ∀ p < 2 ^ k, coef A₂ n 0 p = piece a as al m p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    rw [← l₃ p (by lia) (by lia)]
    exact win_congr fun j _ _ => m₂ j (by lia)
  have cB : ∀ p < 2 ^ k, coef A₂ n (2 ^ k * (n + 1)) p = piece b bs bl m p :=
    fun p hp => m₃ p (by lia) (by lia)
  have hXF : 2 ^ (LA.w * m) < fermatW LA.w n := by
    simp only [fermatW]
    have : 2 ^ (LA.w * m) ≤ 2 ^ (LA.w * n) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hmn)
    lia
  -- The forward transforms.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hW k A₂ 0 σ hσ
    ⟨by rw [m₁]; exact hSz, by rw [m₁]; lia, by rw [m₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize WinOps.fwd n (2 * 2 ^ k * (n + 1)) k A₂ 0 σ = A₃ at *
  have cB₃ : ∀ p < 2 ^ k, coef A₃ n (2 ^ k * (n + 1)) p = piece b bs bl m p := by
    intro p hp
    have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) hp
    rw [← cB p hp]
    exact win_congr fun j _ _ => f₂ j (by lia) (by lia)
  obtain ⟨g₁, g₂, g₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hW k A₃ (2 ^ k * (n + 1)) σ hσ
    ⟨by rw [f₁, m₁]; exact hSz, by rw [f₁, m₁]; lia, by rw [f₁, m₁]; lia, by lia⟩
    (fun p hp => by rw [cB₃ p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize WinOps.fwd n (2 * 2 ^ k * (n + 1)) k A₃ (2 ^ k * (n + 1)) σ = A₄ at *
  have cA₄ : ∀ p < 2 ^ k, coef A₄ n 0 p = coef A₃ n 0 p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    exact win_congr fun j _ _ => g₂ j (by lia) (by lia)
  -- The pointwise products.
  obtain ⟨p₁, p₂, p₃⟩ := R.pointLoop_spec mulP n 0 (2 ^ k * (n + 1)) hn hmul (2 ^ k) A₄
    (R.zeros (2 * n + 2)) 0 (R.size_zeros _) (by rw [R.size_zeros]; lia)
    (by rw [g₁, f₁, m₁]; exact hSz)
    (by lia) (by rw [g₁, f₁, m₁]; lia) (fun q _ hq => by
      rw [cA₄ q (by lia), f₃ q (by lia), g₃ q (by lia)]
      exact ⟨Nat.mod_lt _ hF₀, Nat.mod_lt _ hF₀⟩)
  generalize R.pointLoop mulP n 0 (2 ^ k * (n + 1)) A₄ (R.zeros (2 * n + 2)) 0
    (2 ^ k) =
    A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 * 2 ^ k * (n + 1)) hn hW k A₅ 0 σ hσ
    ⟨by rw [p₁, g₁, f₁, m₁]; exact hSz, by rw [p₁, g₁, f₁, m₁]; lia, by rw [p₁, g₁, f₁, m₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize WinOps.inv n (2 * 2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) =
        win (R.zeros S) n (2 * 2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), g₂ j (by lia) (by lia), f₂ j (by lia) (by lia),
          m₂ j (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_zeros ..
  -- The division by `2ᵏ`.
  have hsz₆ : LA.size A₆ = S := by rw [v₁, p₁, g₁, f₁, m₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k
    hn hk hW (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
    (by rw [hsz₆]; lia) (by lia) (by lia) (by lia) hz
    (fun q _ hq => by rw [v₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize scaleLoop n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k A₆ 0 (2 ^ k) =
    A₇ at *
  -- The coefficients are those of the product of the pieces.
  have hla := cover al m hm
  have hlb := cover bl m hm
  have hla₁ : 1 ≤ (al + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  have hlb₁ : 1 ≤ (bl + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  have hlaK : (al + m - 1) / m ≤ 2 ^ k :=
    (Nat.div_le_iff_le_mul_add_pred (by lia)).2 (by rw [Nat.mul_comm] at hpa; lia)
  have hlbK : (bl + m - 1) / m ≤ 2 ^ k :=
    (Nat.div_le_iff_le_mul_add_pred (by lia)).2 (by rw [Nat.mul_comm] at hpb; lia)
  generalize (al + m - 1) / m = la at *
  generalize (bl + m - 1) / m = lb at *
  have hαL : ∀ i < 2 ^ k, coef A₂ n 0 i = (pieces a as al m la).getD i 0 := fun i hi => by
    rw [cA i hi]
    rcases coef_pieces a as al m la (2 ^ k) i hla with h | h
    · rw [← h, ite_eq_left hi]
    · lia
  have hβL : ∀ i < 2 ^ k, coef A₂ n (2 ^ k * (n + 1)) i = (pieces b bs bl m lb).getD i 0 :=
    fun i hi => by
      rw [cB i hi]
      rcases coef_pieces b bs bl m lb (2 ^ k) i hlb with h | h
      · rw [← h, ite_eq_left hi]
      · lia
  have hβne : pieces b bs bl m lb ≠ [] := by
    intro h; have := congrArg List.length h; rw [length_pieces] at this; simp at this; lia
  have hc : ∀ l < 2 ^ k, coef A₇ n 0 l =
      (cyc (polyMul (pieces a as al m la) (pieces b bs bl m lb)) (2 ^ k)).getD l 0 := by
    intro l hl
    rw [getD_cyc _ _ _ hl, s₃ l (by lia) (by lia), v₃ l hl]
    rw [← fft_coef_cyc (pieces a as al m la) (pieces b bs bl m lb) k (LA.w * n) σ (2 ^ (LA.w * m))
      (F := fermatW LA.w n)
      rfl hk hσ hβne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hβ : ∀ q, sumRange (fun i => coef A₃ n (2 ^ k * (n + 1)) i * 2 ^ (σ * i * rev k q))
        (2 ^ k) =
          sumRange (fun i => (pieces b bs bl m lb).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [cB₃ i hi, ← cB i hi, hβL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (LA.w * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermatW LA.w n *
              (sumRange (fun i => (pieces b bs bl m lb).getD i 0 * 2 ^ (σ * i * rev k p))
                (2 ^ k) % fermatW LA.w n) % fermatW LA.w n *
              2 ^ ((2 * (LA.w * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), cA₄ q hq, f₃ q hq, g₃ q hq, hα, hβ]
    rw [hsum]
  have hcF : ∀ l < 2 ^ k, coef A₇ n 0 l ≤ 2 ^ (LA.w * n) := by
    intro l hl
    rw [s₃ l (by lia) (by lia)]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ hF₀)
  -- The value of the coefficients at `X = 2^(64 m)`, modulo `X^K - 1`.
  generalize hZ : polyMul (pieces a as al m la) (pieces b bs bl m lb) = Z at hc
  have hZ2 : Z.length ≤ 2 * 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a as al m la) (pieces b bs bl m lb) hβne
    rw [length_pieces, length_pieces] at this; lia
  have hval : sumRange (fun i => 2 ^ (LA.w * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      polyVal (2 ^ (LA.w * m)) (cyc Z (2 ^ k)) := by
    rw [polyVal_eq_sumRange _ _ (2 ^ k) (by rw [length_cyc]; exact Nat.le_refl _)]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hM : MEq (2 ^ (LA.w * (m * 2 ^ k)) - 1) ((2 ^ (LA.w * m)) ^ 2 ^ k) 1 := by
    rw [← Nat.pow_mul, show LA.w * m * 2 ^ k = LA.w * (m * 2 ^ k) by lia]
    have : 1 ≤ 2 ^ (LA.w * (m * 2 ^ k)) := Nat.one_le_two_pow
    show _ % _ = _ % _
    rw [show 2 ^ (LA.w * (m * 2 ^ k)) = (2 ^ (LA.w * (m * 2 ^ k)) - 1) + 1 by lia,
      Nat.add_sub_cancel, Nat.add_mod_left]
  have hab : MEq (2 ^ (LA.w * (m * 2 ^ k)) - 1) (valAt a as al * valAt b bs bl)
      (polyVal (2 ^ (LA.w * m)) (cyc Z (2 ^ k))) := by
    rw [← polyVal_pieces a as al m la hla, ← polyVal_pieces b bs bl m lb hlb, ← polyVal_polyMul, hZ]
    exact polyVal_cyc _ _ _ _ hM hZ2
  have hlt : sumRange (fun i => 2 ^ (LA.w * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) <
      2 ^ (LA.w * (m * 2 ^ k + n + 1)) := by
    have h₁ := sum_pow_lt (fun i => coef A₇ n 0 i) (2 ^ (LA.w * n)) (2 ^ (LA.w * m)) (2 ^ k)
      (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (Nat.mul_pos LA.w_pos hm))) hcF
    have e : sumRange (fun i => 2 ^ (LA.w * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
        sumRange (fun i => (2 ^ (LA.w * m)) ^ i * coef A₇ n 0 i) (2 ^ k) :=
      sumRange_congr fun i _ => by rw [Nat.zero_add, ← Nat.pow_mul]; congr 2; lia
    rw [e]
    refine Nat.lt_of_lt_of_le h₁ ?_
    have : 2 ^ (LA.w * n) + 1 ≤ 2 ^ (LA.w * n + LA.w) := by
      rw [Nat.pow_add]
      have := Nat.two_pow_pos (LA.w * n)
      have : 2 ≤ 2 ^ LA.w := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) LA.w_pos; simpa using this
      have := Nat.mul_le_mul_left (2 ^ (LA.w * n)) this
      lia
    calc (2 ^ (LA.w * n) + 1) * (2 ^ (LA.w * m)) ^ 2 ^ k
        ≤ 2 ^ (LA.w * n + LA.w) * (2 ^ (LA.w * m)) ^ 2 ^ k := Nat.mul_le_mul_right _ this
      _ = 2 ^ (LA.w * (m * 2 ^ k + n + 1)) := by
          rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; lia
  -- Zeroing the result, and adding the coefficients.
  obtain ⟨z₁, z₂, z₃⟩ := R.zeroRange_spec r rs (m * 2 ^ k + n + 1) hrS (by lia)
  generalize R.zeroRange r rs (m * 2 ^ k + n + 1) = R₀ at *
  have hsz₇ : LA.size A₇ = S := by rw [s₁, hsz₆]
  obtain ⟨c₁, c₂, c₃⟩ := R.recLoop_spec (m * 2 ^ k + n + 1) m n 0 A₇
    (by rw [hsz₇]; exact hSz) (2 ^ k) R₀ rs 0 (by rw [z₁]; exact hrS) (by rw [z₁]; lia)
    (by rw [hsz₇]; lia) (by rw [z₃, Nat.zero_add]; exact hlt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hval]
    exact hab.symm


/-! ## Squaring -/

/--
`a²` into the `2 al` limbs of `r` from `rs` on, like `fftMulAt` with one forward transform and
`sqrP` for the pointwise squares: the block of `a` at `0`, the scratch window and a zero window.
-/
@[expose, specialize] public def fftSqrAt (sqrP : A → A → Nat → Nat → A) (r : A) (rs : Nat)
    (a : A) (as al k m n : Nat) : A :=
  let K := 2 ^ k
  let t := K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (LA.w * n) / K
  let FA := R.loadLoop 0 n m a as al (R.zeros (z + (n + 1))) 0 K
  let FA := WinOps.fwd n t k FA 0 σ
  let FA := R.pointSqrLoop sqrP n 0 FA (R.zeros (2 * n + 2)) 0 K
  let FA := WinOps.inv n t k FA 0 σ
  let FA := scaleLoop n 0 t z k FA 0 K
  R.recLoop (al + al) m n 0 FA (R.zeroRange r rs (al + al)) rs 0 K

set_option maxHeartbeats 800000 in
public theorem fftSqrAt_spec (sqrP : A → A → Nat → Nat → A) (r : A) (rs : Nat) (a : A)
    (as al k m n : Nat) (hp : FFTParams r rs a as al a as al k m n) (hsqr : IsSqrP sqrP n) :
    LA.size (R.fftSqrAt sqrP r rs a as al k m n) = LA.size r ∧
      (∀ i, (i < rs ∨ rs + (al + al) ≤ i) →
        LA.get (R.fftSqrAt sqrP r rs a as al k m n) i = LA.get r i) ∧
      valAt (R.fftSqrAt sqrP r rs a as al k m n) rs (al + al) = valAt a as al * valAt a as al := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, -, hpc, hbits, hr, hS, hW, haS, -, hrS, hab, -⟩ := hp
  have hF₀ := fermatW_pos LA.w n
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (LA.w * n) / 2 ^ k * 2 ^ k = 2 * (LA.w * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftSqrAt]
  generalize 2 * (LA.w * n) / 2 ^ k = σ at *
  -- The layout.
  have hsz : LA.size (R.zeros (2 ^ k * (n + 1) + (n + 1) + (n + 1))) =
      2 ^ k * (n + 1) + (n + 1) + (n + 1) := R.size_zeros _
  have hSz : 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    have : 2 ^ k * (n + 1) + (n + 1) + (n + 1) ≤ (2 * 2 ^ k + 2) * (n + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc]; lia
    lia
  generalize hS₀ : 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := R.loadLoop_spec 0 n m a as al (by lia) haS hab (2 ^ k)
    (R.zeros S) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_zeros ..)
  generalize R.loadLoop 0 n m a as al (R.zeros S) 0 (2 ^ k) = A₂ at *
  rw [hsz] at l₁
  have cA : ∀ p < 2 ^ k, coef A₂ n 0 p = piece a as al m p := fun p hp => l₃ p (by lia) (by lia)
  have hXF : 2 ^ (LA.w * m) < fermatW LA.w n := by
    simp only [fermatW]
    have : 2 ^ (LA.w * m) ≤ 2 ^ (LA.w * n) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hmn)
    lia
  -- The forward transform.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 ^ k * (n + 1)) hn hW k A₂ 0 σ hσ
    ⟨by rw [l₁]; exact hSz, by rw [l₁]; lia, by rw [l₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize WinOps.fwd n (2 ^ k * (n + 1)) k A₂ 0 σ = A₄ at *
  -- The pointwise squares.
  obtain ⟨p₁, p₂, p₃⟩ := R.pointSqrLoop_spec sqrP n 0 hn hsqr (2 ^ k) A₄
    (R.zeros (2 * n + 2)) 0 (R.size_zeros _) (by rw [R.size_zeros]; lia) (by rw [f₁, l₁]; exact hSz)
    (by rw [f₁, l₁]; lia) (fun q _ hq => by rw [f₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize R.pointSqrLoop sqrP n 0 A₄ (R.zeros (2 * n + 2)) 0 (2 ^ k) = A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 ^ k * (n + 1)) hn hW k A₅ 0 σ hσ
    ⟨by rw [p₁, f₁, l₁]; exact hSz, by rw [p₁, f₁, l₁]; lia, by rw [p₁, f₁, l₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize WinOps.inv n (2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 ^ k * (n + 1) + (n + 1)) =
        win (R.zeros S) n (2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), f₂ j (by lia) (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_zeros ..
  -- The division by `2ᵏ`.
  have hsz₆ : LA.size A₆ = S := by rw [v₁, p₁, f₁, l₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 ^ k * (n + 1)) (2 ^ k * (n + 1) + (n + 1)) k
    hn hk hW (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
    (by rw [hsz₆]; lia) (by lia) (by lia) (by lia) hz
    (fun q _ hq => by rw [v₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize scaleLoop n 0 (2 ^ k * (n + 1)) (2 ^ k * (n + 1) + (n + 1)) k A₆ 0 (2 ^ k) = A₇ at *
  -- The coefficients are those of the square of the pieces.
  have hla := cover al m hm
  have hla₁ : 1 ≤ (al + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  generalize (al + m - 1) / m = la at *
  have hαL : ∀ i < 2 ^ k, coef A₂ n 0 i = (pieces a as al m la).getD i 0 := fun i hi => by
    rw [cA i hi]
    rcases coef_pieces a as al m la (2 ^ k) i hla with h | h
    · rw [← h, ite_eq_left hi]
    · lia
  have hαne : pieces a as al m la ≠ [] := by
    intro h; have := congrArg List.length h; rw [length_pieces] at this; simp at this; lia
  have hc : ∀ l < 2 ^ k,
      coef A₇ n 0 l = (polyMul (pieces a as al m la) (pieces a as al m la)).getD l 0 := by
    intro l hl
    rw [s₃ l (by lia) (by lia), v₃ l hl]
    rw [← fft_coef (pieces a as al m la) (pieces a as al m la) k (LA.w * n) σ (2 ^ (LA.w * m))
      (F := fermatW LA.w n) rfl
      hk hσ
      (by rw [length_pieces]; lia) hαne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (LA.w * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermatW LA.w n *
              (sumRange (fun i => (pieces a as al m la).getD i 0 * 2 ^ (σ * i * rev k p))
                (2 ^ k) % fermatW LA.w n) % fermatW LA.w n *
              2 ^ ((2 * (LA.w * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), f₃ q hq, hα]
    rw [hsum]
  -- The value of the coefficients at `2^(64 m)`.
  generalize hZ : polyMul (pieces a as al m la) (pieces a as al m la) = Z at hc
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a as al m la) (pieces a as al m la) hαne
    rw [length_pieces] at this; lia
  have hab : sumRange (fun i => 2 ^ (LA.w * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      valAt a as al * valAt a as al := by
    rw [← polyVal_pieces a as al m la hla, ← polyVal_polyMul, hZ, polyVal_eq_sumRange _ Z _ hZK]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hablt : valAt a as al * valAt a as al < 2 ^ (LA.w * (al + al)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : valAt a as al < 2 ^ (LA.w * al) := by exact valAt_lt ..
    exact Nat.mul_lt_mul'' h₁ h₁
  -- Zeroing the result, and adding the coefficients.
  obtain ⟨z₁, z₂, z₃⟩ := R.zeroRange_spec r rs (al + al) hrS (by lia)
  generalize R.zeroRange r rs (al + al) = R₀ at *
  have hsz₇ : LA.size A₇ = S := by rw [s₁, hsz₆]
  obtain ⟨c₁, c₂, c₃⟩ := R.recLoop_spec (al + al) m n 0 A₇
    (by rw [hsz₇]; exact hSz) (2 ^ k) R₀ rs 0 (by rw [z₁]; exact hrS) (by rw [z₁]; lia)
    (by rw [hsz₇]; lia) (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hab]

end FFTOps

end MPN.FFT
