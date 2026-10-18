/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Congruences of natural numbers

Lemmas about `a % F = b % F` for the arithmetic modulo the Fermat numbers of the FFT: `-1` to odd
powers and squared, cancelling an addition, and the translation to divisibility in `Int`, where
differences are available.
-/

namespace MPN

/-- `y + 1` divides `yᵘ + 1` for an odd `u`. -/
public theorem dvd_pow_odd_add_one (y u : Nat) (hu : u % 2 = 1) : y + 1 ∣ y ^ u + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, u = 2 * t + 1 := ⟨u / 2, by lia⟩
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; simp
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by lia⟩
  induction t with
  | zero => simp
  | succ t ih =>
    -- `y^(2t + 3) + 1 + (y + 1) (y - 1) = y² (y^(2t + 1) + 1)`.
    have e : (z + 1) ^ (2 * (t + 1) + 1) + 1 + (z + 1 + 1) * z =
        (z + 1) * (z + 1) * ((z + 1) ^ (2 * t + 1) + 1) := by
      rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 by lia, Nat.pow_add]
      grind
    have h := Nat.dvd_mul_left_of_dvd (ih (by lia)) ((z + 1) * (z + 1))
    rw [← e] at h
    exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).mp h

/-- `-1` to an odd power is `-1`, modulo `F`. -/
public theorem pow_odd_mod {y F u : Nat} (hy : (y + 1) % F = 0) (hu : u % 2 = 1) :
    (y ^ u + 1) % F = 0 :=
  Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hy) (dvd_pow_odd_add_one y u hu))

/-- The square of `-1` is `1`, modulo `F`. -/
public theorem sq_of_neg_one {y F : Nat} (hy : (y + 1) % F = 0) : (y * y) % F = 1 % F := by
  have h₁ : (y * (y + 1)) % F = 0 := by rw [Nat.mul_mod, hy, Nat.mul_zero, Nat.zero_mod]
  have e : y * y + (y + 1) = y * (y + 1) + 1 := by grind
  have := congrArg (· % F) e
  rw [Nat.add_mod, hy, Nat.add_zero, Nat.mod_mod, Nat.add_mod (y * (y + 1)), h₁,
    Nat.zero_add, Nat.mod_mod] at this
  exact this

/-- Adding the same number to both sides of a congruence modulo `F > 0` can be undone. -/
public theorem mod_cancel_add {a b c F : Nat} (hF : 0 < F) (h : (a + c) % F = (b + c) % F) :
    a % F = b % F := by
  have e : ∀ x, x + c + (F - c % F) = x + F * (c / F + 1) := fun x => by
    have := Nat.div_add_mod c F
    have := Nat.mod_lt c hF
    rw [Nat.mul_add, Nat.mul_one]; lia
  have h' : (a + c + (F - c % F)) % F = (b + c + (F - c % F)) % F := by
    rw [Nat.add_mod, h, ← Nat.add_mod]
  rwa [e a, e b, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h'

/-- A congruence of natural numbers is a divisibility of their difference in `Int`. -/
public theorem mod_eq_iff_dvd {a b F : Nat} : a % F = b % F ↔ (F : Int) ∣ (a : Int) - b := by
  rw [← Int.ofNat_inj, Int.natCast_emod, Int.natCast_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero,
    Int.dvd_iff_emod_eq_zero]

public theorem dvd_mod_sub (x F : Nat) : (F : Int) ∣ ((x % F : Nat) : Int) - x :=
  mod_eq_iff_dvd.1 (Nat.mod_mod _ _)

end MPN
