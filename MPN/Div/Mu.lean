/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.DC

/-!
# Division by a reciprocal

Barrett's division with a reciprocal from Newton's iteration, like GMP's `mpn_mu_div_qr`, on
`MPN.Num`. The remainders, which are known to be small, are computed modulo `β^N - 1` with the
wrapped product of the FFT (`Num.mulModB`), at about half the cost of a full product.
-/

open ScalarArray UInt64Array

namespace MPN.Num

/-- One fold modulo `β^N - 1`: the low `N` limbs plus the rest, since `β^N ≡ 1`. -/
public def foldB (x : UInt64Array) (N : Nat) : UInt64Array := add (low x N) (shr x (64 * N))

private theorem toNat_foldB (x : UInt64Array) (N : Nat) (hU : 2 * x.size + 2 < USize.size) :
    (foldB x N).toNat % (2 ^ (64 * N) - 1) = x.toNat % (2 ^ (64 * N) - 1) ∧
      (foldB x N).toNat = x.toNat % 2 ^ (64 * N) + x.toNat / 2 ^ (64 * N) ∧
      (foldB x N).size ≤ x.size + 1 := by
  have hl := toNat_low x N (by lia)
  have hls := size_low x N (by lia)
  have hr := toNat_shr x (64 * N) (by lia)
  have hrs := size_shr x (64 * N)
  have hv : (foldB x N).toNat = x.toNat % 2 ^ (64 * N) + x.toNat / 2 ^ (64 * N) := by
    rw [foldB, toNat_add _ _ (by lia), hl, hr]
  refine ⟨?_, hv, by rw [foldB, size_add]; lia⟩
  rw [hv]
  have := Nat.div_add_mod x.toNat (2 ^ (64 * N))
  have h1 : 1 ≤ 2 ^ (64 * N) := Nat.one_le_two_pow
  generalize x.toNat / 2 ^ (64 * N) = h at *
  generalize x.toNat % 2 ^ (64 * N) = l at *
  generalize x.toNat = X at *
  subst this
  generalize hM : 2 ^ (64 * N) - 1 = M
  rw [show 2 ^ (64 * N) = M + 1 by lia,
    show (M + 1) * h + l = (l + h) + h * M by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; lia,
    Nat.add_mul_mod_self_right]

/-- `x mod (2^(64 N) - 1)`: two folds, then the remainder of a short division. -/
public def modB (x : UInt64Array) (N : Nat) : UInt64Array :=
  let y := foldB (foldB x N) N
  if lt y (allOnes N) then y else (divMod y (allOnes N)).2

public theorem toNat_modB (x : UInt64Array) (N : Nat) (hN : 1 ≤ N)
    (hU : 4 * x.size + 2 * N + 8 < USize.size) :
    (modB x N).toNat = x.toNat % (2 ^ (64 * N) - 1) := by
  obtain ⟨f₁, -, f₃⟩ := toNat_foldB x N (by lia)
  obtain ⟨g₁, -, g₃⟩ := toNat_foldB (foldB x N) N (by lia)
  rw [f₁] at g₁
  have hM : 0 < 2 ^ (64 * N) - 1 := by
    have : 2 ≤ 2 ^ (64 * N) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide)
      (show 1 ≤ 64 * N by lia))
    lia
  unfold modB
  dsimp only
  split
  · rename_i h
    rw [lt_iff _ _ (by rw [size_allOnes]; lia), toNat_allOnes] at h
    rw [← g₁, Nat.mod_eq_of_lt h]
  · rw [(toNat_divMod _ _ (by rw [toNat_allOnes]; exact hM)
      (by rw [size_allOnes]; lia)).2, toNat_allOnes, g₁]

end MPN.Num
