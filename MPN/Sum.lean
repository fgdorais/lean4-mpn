/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Finite sums

`sumRange f n = f 0 + ⋯ + f (n - 1)` on natural numbers, with the lemmas that the column sums of
schoolbook products and the inversion of the FFT need: shifting, splitting, reflecting and
swapping sums, and sums modulo `F`.
-/

namespace MPN

/-- `f 0 + f 1 + ⋯ + f (n - 1)`. -/
@[expose] public def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

@[simp] public theorem sumRange_zero (f : Nat → Nat) : sumRange f 0 = 0 := rfl

public theorem sumRange_succ (f : Nat → Nat) (n : Nat) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

/-- Peeling off the first term. -/
public theorem sumRange_succ_left (f : Nat → Nat) (n : Nat) :
    sumRange f (n + 1) = f 0 + sumRange (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange_succ, ih, sumRange_succ]; lia

public theorem sumRange_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun i hi => h i (by lia)), h n (by lia)]

public theorem sumRange_add (f g : Nat → Nat) (n : Nat) :
    sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]; lia

public theorem sumRange_mul_left (c : Nat) (f : Nat → Nat) (n : Nat) :
    c * sumRange f n = sumRange (fun i => c * f i) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sumRange_succ, sumRange_succ, Nat.mul_add, ih]

public theorem sumRange_mul_right (c : Nat) (f : Nat → Nat) (n : Nat) :
    sumRange f n * c = sumRange (fun i => f i * c) n := by
  rw [Nat.mul_comm, sumRange_mul_left]
  exact sumRange_congr fun i _ => Nat.mul_comm _ _

public theorem sumRange_const_zero (n : Nat) : sumRange (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, ih]

/-- Terms that are zero from `n` to `m` don't change the sum. -/
public theorem sumRange_extend {f : Nat → Nat} {n m : Nat} (hnm : n ≤ m)
    (h : ∀ i, n ≤ i → i < m → f i = 0) : sumRange f m = sumRange f n := by
  induction m with
  | zero => rw [Nat.le_zero.1 hnm]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with h' | h'
    · rw [sumRange_succ, ih (by lia) (fun i hi hi' => h i hi (by lia)), h m (by lia) (by lia),
        Nat.add_zero]
    · rw [show n = m + 1 by lia]

public theorem sumRange_append (f : Nat → Nat) (a b : Nat) :
    sumRange f (a + b) = sumRange f a + sumRange (fun i => f (a + i)) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, sumRange_succ, ih, sumRange_succ, Nat.add_assoc]

/-- Summing in reverse order. -/
public theorem sumRange_reflect (f : Nat → Nat) (n : Nat) :
    sumRange (fun i => f (n - 1 - i)) n = sumRange f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ_left, sumRange_succ]
    have : sumRange (fun i => f (n + 1 - 1 - (i + 1))) n = sumRange (fun i => f (n - 1 - i)) n :=
      sumRange_congr fun i _ => by rw [show n + 1 - 1 - (i + 1) = n - 1 - i by lia]
    rw [this, ih, show n + 1 - 1 - 0 = n by lia, Nat.add_comm]

/-- Double sums can be summed in either order. -/
public theorem sumRange_comm (f : Nat → Nat → Nat) (m n : Nat) :
    sumRange (fun j => sumRange (fun i => f i j) m) n =
      sumRange (fun i => sumRange (fun j => f i j) n) m := by
  induction n with
  | zero =>
    simp only [sumRange_zero]
    induction m with
    | zero => rfl
    | succ m ih => rw [sumRange_succ, ← ih]
  | succ n ih =>
    rw [sumRange_succ, ih, ← sumRange_add]
    rfl

/-- Sums of terms that agree modulo `F` agree modulo `F`. -/
public theorem sumRange_mod {f g : Nat → Nat} {n F : Nat} (h : ∀ i < n, f i % F = g i % F) :
    sumRange f n % F = sumRange g n % F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, Nat.add_mod, ih (fun i hi => h i (by lia)), h n (by lia),
      ← Nat.add_mod]

/-- A sum whose terms vanish modulo `F` except at `l` is the term at `l`, modulo `F`. -/
public theorem sumRange_single_mod {f : Nat → Nat} {n F l : Nat} (hl : l < n)
    (h : ∀ i < n, i ≠ l → f i % F = 0) : sumRange f n % F = f l % F := by
  induction n with
  | zero => lia
  | succ n ih =>
    rw [sumRange_succ]
    by_cases hln : l = n
    · subst hln
      have : sumRange f l % F = 0 := by
        rw [sumRange_mod (g := fun _ => 0)
            (fun i hi => by rw [h i (by lia) (by lia), Nat.zero_mod]),
          sumRange_const_zero, Nat.zero_mod]
      rw [Nat.add_mod, this, Nat.zero_add, Nat.mod_mod]
    · rw [Nat.add_mod, ih (by lia) (fun i hi hil => h i (by lia) hil), h n (by lia) (Ne.symm hln),
        Nat.add_zero, Nat.mod_mod]

end MPN
