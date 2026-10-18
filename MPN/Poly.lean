/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Limbs
public import MPN.Sum

/-!
# Polynomials

Coefficient lists of natural numbers and their values, `polyVal x cs = c₀ + x c₁ + x² c₂ + ⋯` by
Horner's rule, of which `ofLimbs` is the case `x = 2³²`: values of sums, products (the convolution
of the coefficients, with a bound on them) and of the even and odd parts, which the Toom
algorithms and the FFT assemble and split their products with.
-/

namespace MPN

/-- `c₀ + x c₁ + x² c₂ + ⋯`. -/
@[expose] public def polyVal (x : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => c + x * polyVal x cs

/-- `polyVal` is a finite sum, over any range that covers the coefficients. -/
public theorem polyVal_eq_sumRange (x : Nat) (as : List Nat) (n : Nat) (h : as.length ≤ n) :
    polyVal x as = sumRange (fun i => as.getD i 0 * x ^ i) n := by
  induction as generalizing n with
  | nil =>
    simp only [polyVal, List.getD_nil, Nat.zero_mul]
    exact (sumRange_const_zero n).symm
  | cons a as ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; lia⟩
    rw [polyVal, ih n (by simp at h; lia)]
    -- Peel off the first term.
    have shift : ∀ m, sumRange (fun i => (a :: as).getD i 0 * x ^ i) (m + 1) =
        a + x * sumRange (fun i => as.getD i 0 * x ^ i) m := by
      intro m
      induction m with
      | zero => simp [sumRange]
      | succ m ihm =>
        rw [sumRange_succ, ihm, sumRange_succ, Nat.mul_add]
        simp only [List.getD_cons_succ, Nat.pow_succ]
        grind
    rw [shift]

/-- Evaluating at congruent points gives congruent values. -/
public theorem polyVal_mod {x y F : Nat} (h : x % F = y % F) (as : List Nat) :
    polyVal x as % F = polyVal y as % F := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [polyVal]
    rw [Nat.add_mod, Nat.mul_mod, h, ih, ← Nat.mul_mod, ← Nat.add_mod]

/-- The sum of two coefficient lists. -/
@[expose] public def polyAdd : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: polyAdd as bs

/-- The product of two coefficient lists: the convolution of the coefficients. -/
@[expose] public def polyMul : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: as, bs => polyAdd (bs.map (a * ·)) (0 :: polyMul as bs)

public theorem polyVal_polyAdd (x : Nat) (as bs : List Nat) :
    polyVal x (polyAdd as bs) = polyVal x as + polyVal x bs := by
  induction as generalizing bs with
  | nil => simp [polyAdd, polyVal]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAdd, polyVal]
    | cons b bs => simp only [polyAdd, polyVal, ih]; grind

public theorem polyVal_map_mul (x c : Nat) (bs : List Nat) :
    polyVal x (bs.map (c * ·)) = c * polyVal x bs := by
  induction bs with
  | nil => simp [polyVal]
  | cons b bs ih => simp only [List.map_cons, polyVal, ih]; grind

public theorem polyVal_polyMul (x : Nat) (as bs : List Nat) :
    polyVal x (polyMul as bs) = polyVal x as * polyVal x bs := by
  induction as with
  | nil => simp [polyMul, polyVal]
  | cons a as ih =>
    simp only [polyMul, polyVal_polyAdd, polyVal_map_mul, polyVal, ih]
    grind

public theorem length_polyAdd (as bs : List Nat) :
    (polyAdd as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [polyAdd]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAdd]
    | cons b bs => simp only [polyAdd, List.length_cons, ih]; lia

public theorem length_polyMul (as bs : List Nat) (hb : bs ≠ []) :
    (polyMul as bs).length ≤ as.length + bs.length - 1 := by
  induction as with
  | nil => simp [polyMul]
  | cons a as ih =>
    have : bs.length ≠ 0 := by simpa using hb
    simp only [polyMul, length_polyAdd, List.length_map, List.length_cons]
    lia

public theorem getD_polyAdd_le (as bs : List Nat) (i : Nat) :
    (polyAdd as bs).getD i 0 ≤ as.getD i 0 + bs.getD i 0 := by
  induction as generalizing bs i with
  | nil => simp [polyAdd]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAdd]
    | cons b bs =>
      cases i with
      | zero => simp [polyAdd]
      | succ i => simpa [polyAdd] using ih bs i

/-- With coefficients at most `A` and `B`, a product's coefficients are at most `len · A · B`. -/
public theorem getD_polyMul_le (as bs : List Nat) (A B : Nat) (ha : ∀ a ∈ as, a ≤ A)
    (hb : ∀ b ∈ bs, b ≤ B) (i : Nat) : (polyMul as bs).getD i 0 ≤ as.length * (A * B) := by
  induction as generalizing i with
  | nil => simp [polyMul]
  | cons a as ih =>
    simp only [polyMul, List.length_cons]
    refine Nat.le_trans (getD_polyAdd_le _ _ i) ?_
    have h₁ : (bs.map (a * ·)).getD i 0 ≤ A * B := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases h : bs[i]? with
      | none => simp
      | some b =>
        have hbm := hb b (List.mem_of_getElem? h)
        simp only [Option.map_some, Option.getD_some]
        exact Nat.mul_le_mul (ha a (by simp)) hbm
    have h₂ : (0 :: polyMul as bs).getD i 0 ≤ as.length * (A * B) := by
      cases i with
      | zero => simp
      | succ i => simpa using ih (fun a h => ha a (by simp [h])) i
    rw [Nat.add_mul, Nat.one_mul]
    lia

/-- The entries at even places. -/
@[expose] public def evens {α : Type} : List α → List α
  | a :: _ :: t => a :: evens t
  | [a] => [a]
  | [] => []

/-- The entries at odd places. -/
@[expose] public def odds {α : Type} : List α → List α
  | _ :: b :: t => b :: odds t
  | _ => []

public theorem map_evens {α β : Type} (f : α → β) (as : List α) :
    (evens as).map f = evens (as.map f) := by
  induction as using evens.induct with
  | case1 a b t ih => simp [evens, ih]
  | case2 a => simp [evens]
  | case3 => simp [evens]

public theorem map_odds {α β : Type} (f : α → β) (as : List α) :
    (odds as).map f = odds (as.map f) := by
  induction as using evens.induct with
  | case1 a b t ih => simp [odds, ih]
  | case2 a => simp [odds]
  | case3 => simp [odds]

public theorem mem_evens {α : Type} {as : List α} {x : α} (h : x ∈ evens as) : x ∈ as := by
  induction as using evens.induct with
  | case1 a b t ih =>
    simp only [evens, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · simp [ih h]
  | case2 a => simpa [evens] using h
  | case3 => simp [evens] at h

public theorem mem_odds {α : Type} {as : List α} {x : α} (h : x ∈ odds as) : x ∈ as := by
  induction as using evens.induct with
  | case1 a b t ih =>
    simp only [odds, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · simp [ih h]
  | case2 a => simp [odds] at h
  | case3 => simp [odds] at h

/-- `p(x) = p_even(x²) + x p_odd(x²)`, the split of the radix-2 transform. -/
public theorem polyVal_evens_odds (x : Nat) (as : List Nat) :
    polyVal x as = polyVal (x * x) (evens as) + x * polyVal (x * x) (odds as) := by
  induction as using evens.induct with
  | case1 a b t ih => simp only [evens, odds, polyVal, ih]; grind
  | case2 a => simp [evens, odds, polyVal]
  | case3 => simp [evens, odds, polyVal]

public theorem length_evens_odds {α : Type} (as : List α) (k : Nat) (h : as.length = 2 * k) :
    (evens as).length = k ∧ (odds as).length = k := by
  induction as using evens.induct generalizing k with
  | case1 a b t ih =>
    simp only [List.length_cons] at h
    obtain ⟨h₁, h₂⟩ := ih (k - 1) (by lia)
    simp only [evens, odds, List.length_cons, h₁, h₂]
    lia
  | case2 a => simp at h; lia
  | case3 => simp at h; simp [evens, odds]; lia

public theorem polyVal_append (x : Nat) (l l' : List Nat) :
    polyVal x (l ++ l') = polyVal x l + x ^ l.length * polyVal x l' := by
  induction l with
  | nil => simp [polyVal]
  | cons c l ih => simp only [List.cons_append, polyVal, ih, List.length_cons, Nat.pow_succ]; grind

public theorem polyVal_zeros (x : Nat) (l : List Nat) (h : ∀ c ∈ l, c = 0) : polyVal x l = 0 := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [polyVal]
    rw [h c (by simp), ih (fun c hc => h c (by simp [hc])), Nat.mul_zero]

/-- `ofLimbs` is the value of the limbs as coefficients at `2³²`. -/
public theorem ofLimbs_eq_polyVal (l : List UInt32) :
    ofLimbs l = polyVal (2 ^ 32) (l.map UInt32.toNat) := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [ofLimbs_cons, polyVal, ih]

end MPN
