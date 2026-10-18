/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add
public import MPN.Poly

/-!
# Assembly

The last step of the Toom algorithms and the FFT: the coefficients of a product, as arrays, added
into one array at limbs `0`, `k`, `2 k`, …, which gives the value of their polynomial at `βᵏ` when
it fits.
-/

open ScalarArray

namespace MPN

/-- Adds `Σ cᵢ βᵏ⁽ᵒᶠᶠ ⁺ ⁱ⁾`... the coefficients `cs` at limbs `off`, `off + k`, `off + 2 k`, …. -/
public def assembleFrom (r : UInt32Array) (off k : Nat) : List UInt32Array → UInt32Array
  | [] => r
  | c :: cs => assembleFrom (addInto r off (c.toSlice 0 (r.size - off))) (off + k) k cs

public theorem assembleFrom_spec (r : UInt32Array) (off k : Nat) (cs : List UInt32Array)
    (hk : off + k * cs.length ≤ r.size + k)
    (hlt : toNat r + 2 ^ (32 * off) *
      polyVal (2 ^ (32 * k)) (cs.map fun c : UInt32Array => toNat c) < 2 ^ (32 * r.size)) :
    (assembleFrom r off k cs).size = r.size ∧ toNat (assembleFrom r off k cs) =
      toNat r + 2 ^ (32 * off) *
        polyVal (2 ^ (32 * k)) (cs.map fun c : UInt32Array => toNat c) := by
  induction cs generalizing r off with
  | nil => simp [assembleFrom, polyVal]
  | cons c cs ih =>
    simp only [List.map_cons, polyVal, List.length_cons] at hk hlt ⊢
    have hoff : off ≤ r.size := by
      rcases Nat.lt_or_ge off (r.size + 1) with h | h
      · lia
      · -- Past the end, the remaining terms would not fit.
        lia
    have hpow : 2 ^ (32 * r.size) = 2 ^ (32 * off) * 2 ^ (32 * (r.size - off)) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hpk : 2 ^ (32 * (off + k)) = 2 ^ (32 * off) * 2 ^ (32 * k) := by
      rw [← Nat.pow_add]; congr 1; lia
    -- `c` alone fits above `off`.
    have hC : toNat c < 2 ^ (32 * (r.size - off)) := by
      have : 2 ^ (32 * off) * toNat c < 2 ^ (32 * off) * 2 ^ (32 * (r.size - off)) := by
        rw [← hpow, Nat.mul_add] at *; lia
      exact Nat.lt_of_mul_lt_mul_left this
    have hcut : toNat (c.toSlice 0 (r.size - off)) = toNat c := toNat_toSlice_of_lt _ _ hC
    have hfit : off + (c.toSlice 0 (r.size - off)).size ≤ r.size := by
      rw [UInt32Array.size_toSlice]; lia
    have hs := size_addInto r off _ hfit
    have hv := toNat_addInto_of_lt r off _ hfit (by rw [hcut, Nat.mul_add] at *; lia)
    rw [hcut] at hv
    obtain ⟨ih₁, ih₂⟩ := ih (addInto r off (c.toSlice 0 (r.size - off))) (off + k)
      (by rw [hs]; lia) (by rw [hv, hs, hpk, Nat.mul_assoc]; rw [Nat.mul_add] at hlt; lia)
    refine ⟨by rw [assembleFrom, ih₁, hs], ?_⟩
    rw [assembleFrom, ih₂, hv, hpk, Nat.mul_assoc, Nat.mul_add]
    lia

/--
`n` limbs of `C₀ + C₁ x + ⋯` at `x = βᵏ` from arrays `cs` whose values are `Cs`, when the sum fits:
the assembly of every Toom product.
-/
public theorem assemble_spec (n k : Nat) (cs : List UInt32Array) (Cs : List Nat)
    (hk : k * cs.length ≤ n + k) (hcs : cs.map (fun c : UInt32Array => toNat c) = Cs)
    (hlt : polyVal (2 ^ (32 * k)) Cs < 2 ^ (32 * n)) :
    (assembleFrom (.replicate n 0) 0 k cs).size = n ∧
      toNat (assembleFrom (.replicate n 0) 0 k cs) = polyVal (2 ^ (32 * k)) Cs := by
  have h := assembleFrom_spec (.replicate n 0) 0 k cs (by simp; lia)
    (by rw [toNat_zeros, hcs]; simpa using hlt)
  rw [toNat_zeros, hcs] at h
  simpa using h

/-! ## Pieces -/

/-- The values of the `L` pieces of `m` limbs of `s` from limb `i`. -/
@[expose] public def pieceList (s : UInt32Array.Slice) (m : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | i, L + 1 => toNat (s.slice i (i + m)) :: pieceList s m (i + m) L

public theorem length_pieceList (s : UInt32Array.Slice) (m i L : Nat) :
    (pieceList s m i L).length = L := by
  induction L generalizing i with
  | zero => rfl
  | succ L ih => simp [pieceList, ih]

/-- The pieces of `s` from limb `i` cover the rest of `s` when `i + L m ≥ s.size`. -/
public theorem toNat_eq_polyVal_pieceList (s : UInt32Array.Slice) (m i L : Nat)
    (h : s.size ≤ i + L * m) :
    toNat (s.slice i s.size) = polyVal (2 ^ (32 * m)) (pieceList s m i L) := by
  induction L generalizing i with
  | zero =>
    simp only [pieceList, polyVal]
    exact toNat_of_size_eq_zero (by simp only [UInt32Array.Slice.size_slice]; lia)
  | succ L ih =>
    rw [toNat_slice_split s i m, ih (i + m) (by rw [Nat.add_mul, Nat.one_mul] at h; lia)]
    rfl

/-- Pieces at or past the end of `s` are zero. -/
public theorem pieceList_zero (s : UInt32Array.Slice) (m i L : Nat) (h : s.size ≤ i) :
    ∀ c ∈ pieceList s m i L, c = 0 := by
  induction L generalizing i with
  | zero => simp [pieceList]
  | succ L ih =>
    intro c hc
    simp only [pieceList, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact toNat_of_size_eq_zero (by simp only [UInt32Array.Slice.size_slice]; lia)
    · exact ih (i + m) (by lia) c hc

public theorem pieceList_append (s : UInt32Array.Slice) (m i L L' : Nat) :
    pieceList s m i (L + L') = pieceList s m i L ++ pieceList s m (i + L * m) L' := by
  induction L generalizing i with
  | zero => simp [pieceList]
  | succ L ih =>
    rw [Nat.add_right_comm, pieceList, ih, pieceList, List.cons_append]
    congr 2
    rw [Nat.add_mul, Nat.one_mul]; lia

public theorem pieceList_lt (s : UInt32Array.Slice) (m i L : Nat) :
    ∀ c ∈ pieceList s m i L, c < 2 ^ (32 * m) := by
  induction L generalizing i with
  | zero => simp [pieceList]
  | succ L ih =>
    intro c hc
    simp only [pieceList, List.mem_cons] at hc
    rcases hc with rfl | hc
    · have := toNat_lt (s.slice i (i + m))
      simp only [UInt32Array.Slice.size_slice] at this
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by lia))
    · exact ih (i + m) c hc

end MPN
