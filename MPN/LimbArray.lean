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
  /-- Sets limb `i` of an array to `v % 2ʷ`, if `i` is within it. -/
  set : A → Nat → Nat → A
  size_set : ∀ a i v, size (set a i v) = size a
  get_set_ne : ∀ a i v j, j ≠ i → get (set a i v) j = get a j
  val_get_set_self : ∀ a i v, i < size a → val (get (set a i v) i) = v % 2 ^ w

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

/-- Limb `i` of `n` limbs is a digit of their value. -/
public theorem val_get_eq (a : A) {n i : Nat} (h : i < n) :
    R.val (R.get a i) = valAt a 0 n / 2 ^ (R.w * i) % 2 ^ R.w := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - i - 1, by lia⟩
  rw [show i + 1 + k = i + (1 + k) by lia, valAt_add, Nat.zero_add, valAt_add a i 1 k, valAt_one,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (valAt_lt ..), Nat.zero_add,
    Nat.mul_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (R.val_lt _)]

/-- Bit `j` of the value of `n` limbs is bit `j % w` of limb `j / w`. -/
public theorem testBit_valAt (a : A) {n j : Nat} (h : j < R.w * n) :
    (valAt a 0 n).testBit j = (R.val (R.get a (j / R.w))).testBit (j % R.w) := by
  have hq : j / R.w < n := (Nat.div_lt_iff_lt_mul R.w_pos).2 (by rw [Nat.mul_comm]; exact h)
  rw [val_get_eq a hq, Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt _ R.w_pos),
    Bool.true_and, Nat.testBit_div_two_pow]
  congr 1
  have := Nat.div_add_mod j R.w
  rw [Nat.mul_comm] at this
  lia

/-! ## Writing a value -/

/--
Writes `v % 2^(w len)` into the `len` limbs of `a` from `o` on, limb by limb. The branches use it
as the fallback of their in-place operations, which never runs.
-/
@[expose] public def writeNat (a : A) (o : Nat) : Nat → Nat → A
  | 0, _ => a
  | len + 1, v => writeNat (R.set a o v) (o + 1) len (v / 2 ^ R.w)

public theorem size_writeNat (a : A) (o len v : Nat) : R.size (writeNat a o len v) = R.size a := by
  induction len generalizing a o v with
  | zero => rfl
  | succ len ih => rw [writeNat, ih, R.size_set]

public theorem get_writeNat (a : A) (o len v i : Nat) (h : i < o ∨ o + len ≤ i) :
    R.get (writeNat a o len v) i = R.get a i := by
  induction len generalizing a o v with
  | zero => rfl
  | succ len ih => rw [writeNat, ih _ _ _ (by lia), R.get_set_ne _ _ _ _ (by lia)]

public theorem valAt_writeNat (a : A) (o len v : Nat) (h : o + len ≤ R.size a) :
    valAt (writeNat a o len v) o len = v % 2 ^ (R.w * len) := by
  induction len generalizing a o v with
  | zero => simp [Nat.mod_one]
  | succ len ih =>
    rw [writeNat, valAt_succ, get_writeNat _ _ _ _ _ (by lia), R.val_get_set_self _ _ _ (by lia),
      ih _ _ _ (by rw [R.size_set]; lia), Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (R.w * len)),
      Nat.mod_mul]

end LimbArray

end MPN
