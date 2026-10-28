/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Sum
public import MPN.Toom.Interp
public import MPN.Toom.Karatsuba

/-!
# The Toom methods

Splitting the operands into pieces of `k` limbs makes them the values at `x = 2^(w k)` of
polynomials with the pieces as coefficients, and their product the value at `x` of the product
polynomial. Its coefficients come from its values at a few points, each a product of about `k`
limbs, which `mulToom` computes recursively. The points are `0, 1, 2, …, ∞`, natural numbers, so
that every intermediate value of the interpolation is a natural number (`MPN.Toom.Interp`).

* Toom-3 (`3 × 3` pieces, degree 4), Toom-3 by 2 (`3 × 2`, degree 3) and Toom-4 by 2 (`4 × 2`,
  degree 4, with the interpolation of Toom-3);
* Toom-4 (`4 × 4`, degree 6) and Toom-4 by 3 (`4 × 3`, degree 5);
* Toom-6 (`6 × 6`, degree 10);
* the squares of Toom-3, Toom-4 and Toom-6.

Each method writes the product of the low pieces and the product of the top pieces into the
window of the result, the products of the values at the other points into new arrays of `2 k + 2`
limbs, and interpolates. `mulToom cfg` chooses by the sizes, and is `mulKaratsuba` below the
thresholds of `cfg`.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : ToomOps A L]

/-! ## Pieces -/

/-- Piece `i` of the `xl` limbs of `x` from `xo`, in pieces of `k` limbs: fewer at the top. -/
@[expose] public def piece (x : A) (xo xl k i : Nat) : Nat :=
  valAt x (xo + i * k) (min k (xl - i * k))

omit R in
public theorem piece_lt (x : A) (xo xl k i : Nat) : piece x xo xl k i < 2 ^ (LA.w * k) :=
  Nat.lt_of_lt_of_le (valAt_lt ..)
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.min_le_left _ _)))

omit R in
/-- A piece below the top one. -/
public theorem piece_full (x : A) (xo xl k i : Nat) (h : i * k + k ≤ xl) :
    piece x xo xl k i = valAt x (xo + i * k) k := by
  rw [piece, Nat.min_eq_left (by lia)]

omit R in
/-- The top piece. -/
public theorem piece_top (x : A) (xo xl k i : Nat) (h : xl ≤ i * k + k) :
    piece x xo xl k i = valAt x (xo + i * k) (xl - i * k) := by
  rw [piece, Nat.min_eq_right (by lia)]

omit R in
/-- The pieces are the digits in base `2^(w k)`. -/
public theorem valAt_eq_pieces (x : A) (k : Nat) :
    ∀ p xo xl, xl ≤ p * k →
      valAt x xo xl = sumRange (fun i => piece x xo xl k i * (2 ^ (LA.w * k)) ^ i) p
  | 0, xo, xl, h => by rw [show xl = 0 by lia]; simp
  | p + 1, xo, xl, h => by
    rw [sumRange_succ_left]
    have hs : ∀ i, piece x xo xl k (i + 1) * (2 ^ (LA.w * k)) ^ (i + 1) =
        2 ^ (LA.w * k) * (piece x (xo + k) (xl - k) k i * (2 ^ (LA.w * k)) ^ i) := by
      intro i
      rw [piece, piece, show xo + (i + 1) * k = xo + k + i * k by rw [Nat.add_mul]; lia,
        show xl - (i + 1) * k = xl - k - i * k by rw [Nat.add_mul]; lia, Nat.pow_succ]
      grind
    rw [sumRange_congr (fun i _ => hs i), ← sumRange_mul_left,
      ← valAt_eq_pieces x k p (xo + k) (xl - k) (by rw [Nat.add_mul] at h; lia),
      piece, Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
    rcases Nat.le_total k xl with hk | hk
    · rw [Nat.min_eq_left hk]; exact valAt_split x xo xl k hk
    · rw [Nat.min_eq_right hk, show xl - k = 0 by lia]
      simp

/-! ## Evaluations -/

/-- Adds pieces `i` to `p - 1` of `x`, times `jⁱ`, to the `len` limbs of `e`, with `jp = jⁱ`. -/
@[expose, specialize] public def evalLoop (x : A) (xo xl k j p len : Nat) (e : A) (i jp : Nat) : A :=
  if i < p then
    evalLoop x xo xl k j p len (R.addMulInto e 0 len x (xo + i * k) (min k (xl - i * k)) jp)
      (i + 1) (jp * j)
  else e
termination_by p - i

/-- The value at `j` of the polynomial of the `p` pieces of `x`, in a new array of `len` limbs. -/
@[expose, specialize] public def evalAt (x : A) (xo xl k p j len : Nat) : A :=
  evalLoop x xo xl k j p len (R.addInto (R.zeros len) 0 len x xo (min k xl)) 1 j

private theorem evalLoop_spec (x : A) (xo xl k j p len : Nat) (hj : 1 ≤ j)
    (hjp : j ^ (p - 1) < 2 ^ 32) :
    ∀ m (e : A) i jp, p - i = m → jp = j ^ i → LA.size e = len →
      valAt e 0 len + sumRange (fun l => piece x xo xl k (i + l) * j ^ (i + l)) m <
        2 ^ (LA.w * len) →
      LA.size (evalLoop x xo xl k j p len e i jp) = len ∧
        valAt (evalLoop x xo xl k j p len e i jp) 0 len =
          valAt e 0 len + sumRange (fun l => piece x xo xl k (i + l) * j ^ (i + l)) m
  | 0, e, i, jp, hm, _, he, _ => by
    have hc : ¬ i < p := by lia
    rw [evalLoop]; simp only [hc, ↓reduceIte]; exact ⟨he, by simp⟩
  | m + 1, e, i, jp, hm, hjp, he, hlt => by
    subst hjp
    have hc : i < p := by lia
    rw [evalLoop]; simp only [hc, ↓reduceIte]
    rw [sumRange_succ_left, Nat.add_zero] at hlt ⊢
    have hji : j ^ i < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right hj (by lia)) hjp
    obtain ⟨w, v⟩ := R.addMulInto_spec e 0 len x (xo + i * k) (min k (xl - i * k)) (j ^ i)
      (by lia) (lt_limb hji) (by rw [← piece]; lia)
    have hs : ∀ l, piece x xo xl k (i + (l + 1)) * j ^ (i + (l + 1)) =
        piece x xo xl k (i + 1 + l) * j ^ (i + 1 + l) := fun l => by rw [Nat.add_assoc, Nat.add_comm 1]
    rw [sumRange_congr (fun l _ => hs l)] at hlt ⊢
    have := evalLoop_spec x xo xl k j p len hj hjp m _ (i + 1) _ (by lia) (Nat.pow_succ ..).symm
      (w.1.trans he)
      (by rw [v, ← piece]; lia)
    rw [this.2, v, ← piece]
    exact ⟨this.1, by lia⟩

/-- A sum of `p` multiples of `jⁱ` by numbers below `X`. -/
private theorem sum_le (f : Nat → Nat) (j X : Nat) (hf : ∀ i, f i < X) :
    ∀ p, sumRange (fun i => f i * j ^ i) p ≤ (X - 1) * sumRange (fun i => j ^ i) p
  | 0 => by simp
  | p + 1 => by
    rw [sumRange_succ, sumRange_succ, Nat.mul_add]
    have := sum_le f j X hf p
    have := Nat.mul_le_mul_right (j ^ p) (show f p ≤ X - 1 by have := hf p; lia)
    lia

/--
The value of the evaluation at `1 ≤ j` of `p` pieces into `k + 1` limbs, which holds it when the
sum of the powers of `j` fits in 32 bits.
-/
public theorem evalAt_spec (x : A) (xo xl k p j : Nat) (hp : 1 ≤ p) (hj : 1 ≤ j)
    (hjp : sumRange (fun i => j ^ i) p ≤ 2 ^ 32) :
    LA.size (evalAt x xo xl k p j (k + 1)) = k + 1 ∧
      valAt (evalAt x xo xl k p j (k + 1)) 0 (k + 1) =
        sumRange (fun i => piece x xo xl k i * j ^ i) p := by
  have hX := Nat.two_pow_pos (LA.w * k)
  have hP : 2 ^ (LA.w * (k + 1)) = 2 ^ (LA.w * k) * 2 ^ LA.w := by rw [Nat.mul_succ, Nat.pow_add]
  have h32 : 2 ^ 32 ≤ 2 ^ LA.w := Nat.pow_le_pow_right (by decide) R.w_ge
  -- The whole sum fits.
  have hsum : sumRange (fun i => piece x xo xl k i * j ^ i) p < 2 ^ (LA.w * (k + 1)) := by
    have := sum_le (piece x xo xl k) j _ (piece_lt x xo xl k) p
    have := Nat.mul_le_mul_left (2 ^ (LA.w * k) - 1) hjp
    rw [hP]
    have := Nat.mul_le_mul_left (2 ^ (LA.w * k) - 1) h32
    have : (2 ^ (LA.w * k) - 1) * 2 ^ LA.w < 2 ^ (LA.w * k) * 2 ^ LA.w :=
      Nat.mul_lt_mul_of_pos_right (by lia) (Nat.two_pow_pos _)
    lia
  have hsplit := sumRange_succ_left (fun i => piece x xo xl k i * j ^ i) (p - 1)
  rw [show p - 1 + 1 = p by lia] at hsplit
  have hz : valAt (R.zeros (k + 1)) 0 (k + 1) = 0 :=
    valAt_eq_zero _ fun i _ _ => R.val_get_zeros _ i
  have hp0 : piece x xo xl k 0 = valAt x xo (min k xl) := by simp [piece]
  obtain ⟨w₀, v₀⟩ := R.addInto_spec (R.zeros (k + 1)) 0 (k + 1) x xo (min k xl)
    (by rw [R.size_zeros]; lia) (by rw [hz, ← hp0]; simp only [Nat.pow_zero, Nat.mul_one] at hsplit; lia)
  rw [hz, Nat.zero_add, ← hp0] at v₀
  have hjp' : j ^ (p - 1) < 2 ^ 32 := by
    have h₁ := sumRange_succ (fun i => j ^ i) (p - 1)
    rw [show p - 1 + 1 = p by lia] at h₁
    rcases Nat.eq_zero_or_pos (p - 1) with h | h
    · rw [h, Nat.pow_zero]; decide
    · have h₂ := sumRange_succ_left (fun i => j ^ i) (p - 2)
      rw [show p - 2 + 1 = p - 1 by lia, Nat.pow_zero] at h₂
      lia
  have := evalLoop_spec x xo xl k j p (k + 1) hj hjp' (p - 1) _ 1 j rfl (Nat.pow_one j).symm
    (by rw [w₀.1, R.size_zeros]) (by
      rw [v₀]
      have e : ∀ l, piece x xo xl k (1 + l) * j ^ (1 + l) = piece x xo xl k (l + 1) * j ^ (l + 1) :=
        fun l => by rw [Nat.add_comm]
      rw [sumRange_congr (fun l _ => e l)]
      simp only [Nat.pow_zero, Nat.mul_one] at hsplit
      lia)
  refine ⟨this.1, ?_⟩
  rw [evalAt, this.2, v₀]
  have e : ∀ l, piece x xo xl k (1 + l) * j ^ (1 + l) = piece x xo xl k (l + 1) * j ^ (l + 1) :=
    fun l => by rw [Nat.add_comm]
  rw [sumRange_congr (fun l _ => e l)]
  simp only [Nat.pow_zero, Nat.mul_one] at hsplit
  lia

/-! ## The products -/

/-- A multiplier for products whose sizes add up to less than `N`. -/
public abbrev MulFn (A : Type) (N : Nat) : Type :=
  (d : A) → (o : Nat) → (x : A) → (xo xl : Nat) → (y : A) → (yo yl : Nat) → xl + yl < N → A

/-- `f` writes `x y` into the `xl + yl` limbs of `d` from `o`, and nothing else. -/
@[expose] public def IsMul {N : Nat} (f : MulFn A N) : Prop :=
  ∀ d o x xo xl y yo yl h, o + (xl + yl) ≤ LA.size d →
    Writes (f d o x xo xl y yo yl h) d o (xl + yl) ∧
      valAt (f d o x xo xl y yo yl h) o (xl + yl) = valAt x xo xl * valAt y yo yl

/-- The product of the values at `j` of `p` pieces of `x` and `q` of `y`, in `2 k + 2` limbs. -/
public theorem point_spec {N : Nat} (mul : MulFn A N) (hmul : IsMul mul) (x : A) (xo xl : Nat)
    (y : A) (yo yl k p q j : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) (hj : 1 ≤ j)
    (hjp : sumRange (fun i => j ^ i) p ≤ 2 ^ 32) (hjq : sumRange (fun i => j ^ i) q ≤ 2 ^ 32)
    (h : k + 1 + (k + 1) < N) :
    LA.size (mul (R.zeros (k + k + 2)) 0 (evalAt x xo xl k p j (k + 1)) 0 (k + 1)
        (evalAt y yo yl k q j (k + 1)) 0 (k + 1) h) = k + k + 2 ∧
      valAt (mul (R.zeros (k + k + 2)) 0 (evalAt x xo xl k p j (k + 1)) 0 (k + 1)
        (evalAt y yo yl k q j (k + 1)) 0 (k + 1) h) 0 (k + k + 2) =
        sumRange (fun i => piece x xo xl k i * j ^ i) p *
          sumRange (fun i => piece y yo yl k i * j ^ i) q := by
  obtain ⟨w, v⟩ := hmul (R.zeros (k + k + 2)) 0 (evalAt x xo xl k p j (k + 1)) 0 (k + 1)
    (evalAt y yo yl k q j (k + 1)) 0 (k + 1) h (by rw [R.size_zeros]; lia)
  rw [show k + 1 + (k + 1) = k + k + 2 by lia, (evalAt_spec x xo xl k p j hp hj hjp).2,
    (evalAt_spec y yo yl k q j hq hj hjq).2] at v
  exact ⟨w.1.trans (R.size_zeros _), v⟩

omit R in
/-- `2^(w (i k))` as a power of `X = 2^(w k)`. -/
public theorem pow_mul_k (i k : Nat) : 2 ^ (LA.w * (i * k)) = (2 ^ (LA.w * k)) ^ i := by
  rw [← Nat.pow_mul]; congr 1; rw [Nat.mul_comm i k, Nat.mul_assoc]

omit R in
/-- The product of two values fits in their limbs. -/
public theorem mul_lt (x y : A) (xo xl yo yl : Nat) :
    valAt x xo xl * valAt y yo yl < 2 ^ (LA.w * (xl + yl)) := by
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)

/-- A squaring for numbers of fewer than `N` limbs. -/
public abbrev SqrFn (A : Type) (N : Nat) : Type :=
  (d : A) → (o : Nat) → (x : A) → (xo xl : Nat) → xl < N → A

/-- `f` writes `x²` into the `2 xl` limbs of `d` from `o`, and nothing else. -/
@[expose] public def IsSqr {N : Nat} (f : SqrFn A N) : Prop :=
  ∀ d o x xo xl h, o + (xl + xl) ≤ LA.size d →
    Writes (f d o x xo xl h) d o (xl + xl) ∧
      valAt (f d o x xo xl h) o (xl + xl) = valAt x xo xl * valAt x xo xl

/-- The square of the value at `j` of `p` pieces of `x`, in `2 k + 2` limbs. -/
public theorem point_sqr_spec {N : Nat} (sq : SqrFn A N) (hsq : IsSqr sq) (x : A) (xo xl k p j : Nat)
    (hp : 1 ≤ p) (hj : 1 ≤ j) (hjp : sumRange (fun i => j ^ i) p ≤ 2 ^ 32) (h : k + 1 < N) :
    LA.size (sq (R.zeros (k + k + 2)) 0 (evalAt x xo xl k p j (k + 1)) 0 (k + 1) h) = k + k + 2 ∧
      valAt (sq (R.zeros (k + k + 2)) 0 (evalAt x xo xl k p j (k + 1)) 0 (k + 1) h) 0
        (k + k + 2) =
        sumRange (fun i => piece x xo xl k i * j ^ i) p *
          sumRange (fun i => piece x xo xl k i * j ^ i) p := by
  obtain ⟨w, v⟩ := hsq (R.zeros (k + k + 2)) 0 (evalAt x xo xl k p j (k + 1)) 0 (k + 1) h
    (by rw [R.size_zeros]; lia)
  rw [show k + 1 + (k + 1) = k + k + 2 by lia, (evalAt_spec x xo xl k p j hp hj hjp).2] at v
  exact ⟨w.1.trans (R.size_zeros _), v⟩

end MPN.Toom
