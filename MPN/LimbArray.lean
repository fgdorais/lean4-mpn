/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Arrays of limbs

`LimbArray A L` describes arrays `A` of limbs `L` of `w` bits: their size, their limbs, and the
value of a limb. `valAt a lo n` is the natural number whose little-endian base `2ʷ` limbs are
`a[lo], …, a[lo + n - 1]`; its lemmas hold for limbs of any width. `main32` and `main64`
instantiate the class on their arrays of 32-bit and 64-bit limbs, and their own `valAt` is this
one.
-/

namespace MPN

/-- Arrays `A` of limbs `L` of `w` bits. -/
public class LimbArray (A : Type) (L : outParam Type) where
  /-- The width of a limb in bits. -/
  w : Nat
  w_pos : 0 < w
  /-- The number of limbs of an array. -/
  size : A → Nat
  /-- Limb `i` of an array, which is zero past its end. -/
  get : A → Nat → L
  /-- The value of a limb. -/
  val : L → Nat
  val_lt : ∀ x, val x < 2 ^ w

namespace LimbArray

variable {A L : Type} [R : LimbArray A L]

/--
The natural number whose little-endian base `2ʷ` limbs are `a[lo], …, a[lo + n - 1]`, where the
limbs past the end of `a` are zero.
-/
@[expose] public def valAt (a : A) (lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => R.val (R.get a lo) + 2 ^ R.w * valAt a (lo + 1) n

@[simp] public theorem valAt_zero (a : A) (lo : Nat) : valAt a lo 0 = 0 := by
  rw [valAt]

public theorem valAt_succ (a : A) (lo n : Nat) :
    valAt a lo (n + 1) = R.val (R.get a lo) + 2 ^ R.w * valAt a (lo + 1) n := by
  rw [valAt]

@[simp] public theorem valAt_one (a : A) (lo : Nat) : valAt a lo 1 = R.val (R.get a lo) := by
  simp [valAt_succ]

public theorem valAt_lt (a : A) (lo n : Nat) : valAt a lo n < 2 ^ (R.w * n) := by
  induction n generalizing lo with
  | zero => simp
  | succ n ih =>
    have h₁ := ih (lo + 1)
    have h₂ := R.val_lt (R.get a lo)
    rw [valAt_succ, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (R.w * n))]
    generalize valAt a _ n = v at *
    generalize 2 ^ (R.w * n) = P at *
    generalize 2 ^ R.w = B at *
    generalize R.val (R.get a lo) = x at *
    have : B * v + B ≤ B * P := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B h₁
    lia

/-- `valAt` only depends on the limbs it reads. -/
public theorem valAt_congr {a b : A} {lo : Nat} :
    (n : Nat) → (∀ i, lo ≤ i → i < lo + n → R.get a i = R.get b i) → valAt a lo n = valAt b lo n
  | 0, _ => by simp
  | n + 1, h => by
    rw [valAt_succ, valAt_succ, h lo (by lia) (by lia),
      valAt_congr n fun i h₁ h₂ => h i (by lia) (by lia)]

/-- Splits `valAt` into its low `m` limbs and the `k` limbs above them. -/
public theorem valAt_add (a : A) (lo m k : Nat) :
    valAt a lo (m + k) = valAt a lo m + 2 ^ (R.w * m) * valAt a (lo + m) k := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, valAt_succ, valAt_succ, ih, Nat.add_assoc lo, Nat.add_comm 1 m,
      Nat.mul_succ, Nat.pow_add]
    generalize valAt a _ m = X
    generalize valAt a _ k = Y
    generalize 2 ^ (R.w * m) = P
    grind

/-- The low `m` of `n` limbs of a value: its residue modulo `2^(w m)`. -/
public theorem valAt_mod (a : A) (lo : Nat) {m n : Nat} (h : m ≤ n) :
    valAt a lo m = valAt a lo n % 2 ^ (R.w * m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by lia⟩
  rw [valAt_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (valAt_lt ..)]

/-- `valAt` of limbs that are all zero. -/
public theorem valAt_eq_zero {a : A} {lo : Nat} :
    (n : Nat) → (∀ i, lo ≤ i → i < lo + n → R.val (R.get a i) = 0) → valAt a lo n = 0
  | 0, _ => by simp
  | n + 1, h => by
    rw [valAt_succ, h lo (by lia) (by lia), valAt_eq_zero n fun i h₁ h₂ => h i (by lia) (by lia)]
    simp

end LimbArray

end MPN
