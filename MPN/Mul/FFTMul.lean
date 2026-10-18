/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Fermat

/-!
# The transform

The discrete Fourier transform of length `2ᵏ` modulo `F = 2ᴺ + 1` with `ω = 2ᵉ`, on residues
(`n + 1` limbs below `F`), by the recursive radix-2 split: the values at `ωʲ` and `ω^(j + 2ᵏ⁻¹)` of
a polynomial `p` are `p_even(ω²ʲ) ± ωʲ p_odd(ω²ʲ)`, since `ω^(2ᵏ⁻¹) ≡ -1`. The twiddles `ωʲ` are
products by powers of two, `mulPow2`.
-/

open ScalarArray

namespace MPN.FFT

open Fermat

/-- A residue modulo `fermat n`: `n + 1` limbs with a value below `fermat n`. -/
@[expose] public def IsRes (n : Nat) (x : UInt32Array) : Prop := x.size = n + 1 ∧ toNat x < fermat n

/-- The values at `2^(e j)`, `j < 2ᵏ`, of the polynomial with coefficients `xs`, modulo `F`. -/
public def transform (n : Nat) : Nat → Nat → List UInt32Array → List UInt32Array
  | 0, _, xs => xs
  | k + 1, e, xs =>
    let ev := transform n k (2 * e) (evens xs)
    let od := transform n k (2 * e) (odds xs)
    let tw := List.zipWith (fun o j => mulPow2 n o (e * j)) od (List.range (2 ^ k))
    List.zipWith (addMod n) ev tw ++ List.zipWith (subMod n) ev tw

/-- The values of a list of arrays. -/
@[expose] public def vals (xs : List UInt32Array) : List Nat :=
  xs.map fun x : UInt32Array => toNat x

/-! ## Lists by index -/

public theorem getD_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

public theorem getD_append_left {α : Type} (l l' : List α) (i : Nat) (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [getD_of_lt _ _ _ (by simp; lia), getD_of_lt _ _ _ h, List.getElem_append_left h]

public theorem getD_append_right {α : Type} (l l' : List α) (i : Nat) (d : α)
    (h : l.length ≤ i) : (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

public theorem getD_zipWith {α β γ : Type} (f : α → β → γ) (l : List α) (l' : List β) (i : Nat)
    (d : γ) (a : α) (b : β) (h : i < l.length) (h' : i < l'.length) :
    (List.zipWith f l l').getD i d = f (l.getD i a) (l'.getD i b) := by
  rw [getD_of_lt _ _ _ (by simp; lia), List.getElem_zipWith, getD_of_lt _ _ _ h,
    getD_of_lt _ _ _ h']

public theorem getD_range (m i d : Nat) (h : i < m) : (List.range m).getD i d = i := by
  rw [getD_of_lt _ _ _ (by simp; lia), List.getElem_range]

/-- A property of every entry, from the property of every entry by index. -/
public theorem forall_mem_of_getD {α : Type} {P : α → Prop} (l : List α) (d : α)
    (h : ∀ j < l.length, P (l.getD j d)) : ∀ y ∈ l, P y := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
  have := h i hi
  rwa [getD_of_lt _ _ _ hi] at this

public theorem mem_of_getD {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_of_lt _ _ _ h]; exact List.getElem_mem h

/-! ## Congruences -/

/-- A congruence of natural numbers is a divisibility of their difference in `Int`. -/
public theorem mod_eq_iff_dvd {a b F : Nat} : a % F = b % F ↔ (F : Int) ∣ (a : Int) - b := by
  rw [← Int.ofNat_inj, Int.natCast_emod, Int.natCast_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero,
    Int.dvd_iff_emod_eq_zero]

public theorem dvd_mod_sub (x F : Nat) : (F : Int) ∣ ((x % F : Nat) : Int) - x :=
  mod_eq_iff_dvd.1 (Nat.mod_mod _ _)

/-- The sum of a butterfly. -/
private theorem butterfly_add (A B s F : Nat) :
    (A % F + (B % F * s) % F) % F = (A + s * B) % F := by
  apply mod_eq_iff_dvd.2
  have h₁ := dvd_mod_sub A F
  have h₂ := dvd_mod_sub (B % F * s) F
  have h₃ := dvd_mod_sub B F
  have e : ((A % F + (B % F * s) % F : Nat) : Int) - ((A + s * B : Nat) : Int) =
      (((A % F : Nat) : Int) - A) + ((((B % F * s) % F : Nat) : Int) - ((B % F * s : Nat) : Int)) +
        (s : Int) * (((B % F : Nat) : Int) - B) := by
    push_cast; grind
  rw [e]
  exact Int.dvd_add (Int.dvd_add h₁ h₂) (Int.dvd_trans h₃ (Int.dvd_mul_left _ _))

/-- The difference of a butterfly: `ω^(j + 2ᵏ) = ωʲ u` with `u ≡ -1`. -/
private theorem butterfly_sub (A A' B B' s u F : Nat) (hA : A' % F = A % F)
    (hB : B' % F = B % F) (hu : (u + 1) % F = 0) :
    (A' + s * u * B') % F = (A % F + F - (B % F * s) % F) % F := by
  rcases Nat.eq_zero_or_pos F with hF | hF
  · subst hF; simp at hu
  have hc : (B % F * s) % F < F := Nat.mod_lt _ hF
  apply mod_eq_iff_dvd.2
  have h₁ : (F : Int) ∣ (A' : Int) - ((A % F : Nat) : Int) :=
    mod_eq_iff_dvd.1 (by rw [hA, Nat.mod_mod])
  have h₂ : (F : Int) ∣ (B' : Int) - ((B % F : Nat) : Int) :=
    mod_eq_iff_dvd.1 (by rw [hB, Nat.mod_mod])
  have h₃ : (F : Int) ∣ ((u + 1 : Nat) : Int) - ((0 : Nat) : Int) :=
    mod_eq_iff_dvd.1 (by rw [hu, Nat.zero_mod])
  have h₄ := dvd_mod_sub (B % F * s) F
  have e : ((A' + s * u * B' : Nat) : Int) - ((A % F + F - (B % F * s) % F : Nat) : Int) =
      ((A' : Int) - ((A % F : Nat) : Int)) - F -
        ((((B % F * s) % F : Nat) : Int) - ((B % F * s : Nat) : Int)) * (-1) +
        (s : Int) * B' * (((u + 1 : Nat) : Int) - ((0 : Nat) : Int)) -
        (s : Int) * ((B' : Int) - ((B % F : Nat) : Int)) := by
    rw [Int.ofNat_sub (by lia)]
    push_cast; grind
  rw [e]
  exact Int.dvd_sub (Int.dvd_add (Int.dvd_sub (Int.dvd_sub h₁ (Int.dvd_refl _))
    (Int.dvd_trans h₄ (Int.dvd_mul_right _ _))) (Int.dvd_trans h₃ (Int.dvd_mul_left _ _)))
    (Int.dvd_trans h₂ (Int.dvd_mul_left _ _))

/-! ## The transform -/

/-- `a u + a ≡ 0` when `u ≡ -1`. -/
private theorem mul_neg_one_add {a u F : Nat} (hu : (u + 1) % F = 0) : (a * u + a) % F = 0 := by
  rw [show a * u + a = a * (u + 1) by rw [Nat.mul_add, Nat.mul_one], Nat.mul_mod, hu,
    Nat.mul_zero, Nat.zero_mod]

public theorem transform_spec (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    ∀ (e : Nat) (xs : List UInt32Array), xs.length = 2 ^ k → (∀ x ∈ xs, IsRes n x) →
    (1 ≤ k → (2 ^ (e * 2 ^ (k - 1)) + 1) % fermat n = 0) →
    (transform n k e xs).length = 2 ^ k ∧
      (∀ j < 2 ^ k, IsRes n ((transform n k e xs).getD j default)) ∧
      ∀ j < 2 ^ k, toNat ((transform n k e xs).getD j default) =
        polyVal (2 ^ (e * j)) (vals xs) % fermat n := by
  have hFpos : 0 < fermat n := by simp [fermat]
  induction k with
  | zero =>
    intro e xs hl hres _
    obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := List.length_eq_one_iff.1 (by simpa using hl)
    have hx := hres x (by simp)
    refine ⟨by simp [transform], fun j hj => ?_, fun j hj => ?_⟩
    · have hj0 : j = 0 := by simp at hj; lia
      subst hj0
      simpa [transform] using hx
    · have hj0 : j = 0 := by simp at hj; lia
      subst hj0
      simp only [transform, List.getD_cons_zero, vals, List.map_cons, List.map_nil, polyVal,
        Nat.mul_zero, Nat.add_zero]
      exact (Nat.mod_eq_of_lt hx.2).symm
  | succ k ih =>
    intro e xs hl hres hw
    have hw' := hw (by lia)
    simp only [Nat.add_sub_cancel] at hw'
    obtain ⟨hle, hlo⟩ := length_evens_odds xs (2 ^ k) (by rw [hl, Nat.pow_succ]; lia)
    have hsub : 1 ≤ k → (2 ^ (2 * e * 2 ^ (k - 1)) + 1) % fermat n = 0 := fun hk => by
      rw [show 2 * e * 2 ^ (k - 1) = e * 2 ^ k by
        rw [Nat.mul_comm 2 e, Nat.mul_assoc, ← Nat.pow_succ']; congr 2; lia]
      exact hw'
    obtain ⟨le, re, ve⟩ := ih (2 * e) (evens xs) hle (fun x h => hres x (mem_evens h)) hsub
    obtain ⟨lo, ro, vo⟩ := ih (2 * e) (odds xs) hlo (fun x h => hres x (mem_odds h)) hsub
    simp only [transform]
    generalize transform n k (2 * e) (evens xs) = E at *
    generalize transform n k (2 * e) (odds xs) = O at *
    -- The twiddled odd values.
    have ltw : (List.zipWith (fun o j => mulPow2 n o (e * j)) O (List.range (2 ^ k))).length =
        2 ^ k := by simp [lo]
    have vtw : ∀ j < 2 ^ k, (List.zipWith (fun o j => mulPow2 n o (e * j)) O
        (List.range (2 ^ k))).getD j default = mulPow2 n (O.getD j default) (e * j) :=
        fun j hj => by
      rw [getD_zipWith _ _ _ _ _ default 0 (by rw [lo]; exact hj) (by simpa using hj),
        getD_range _ _ _ hj]
    generalize List.zipWith (fun o j => mulPow2 n o (e * j)) O (List.range (2 ^ k)) = T at *
    have rO := ro
    have rE := re
    have rT : ∀ j < 2 ^ k, IsRes n (T.getD j default) := fun j hj => by
      rw [vtw j hj]
      exact ⟨size_mulPow2 _ _ _, toNat_mulPow2_lt _ _ _ hn (rO j hj).1 (rO j hj).2⟩
    have l1 : (List.zipWith (addMod n) E T).length = 2 ^ k := by simp [le, ltw]
    have g1 : ∀ j < 2 ^ k, (List.zipWith (addMod n) E T ++ List.zipWith (subMod n) E T).getD j
        default = addMod n (E.getD j default) (T.getD j default) := fun j hj => by
      rw [getD_append_left _ _ _ _ (by rw [l1]; exact hj),
        getD_zipWith _ _ _ _ _ default default (by rw [le]; exact hj) (by rw [ltw]; exact hj)]
    have g2 : ∀ j < 2 ^ k, (List.zipWith (addMod n) E T ++ List.zipWith (subMod n) E T).getD
        (j + 2 ^ k) default = subMod n (E.getD j default) (T.getD j default) := fun j hj => by
      rw [getD_append_right _ _ _ _ (by rw [l1]; lia), l1, Nat.add_sub_cancel,
        getD_zipWith _ _ _ _ _ default default (by rw [le]; exact hj) (by rw [ltw]; exact hj)]
    -- The values of the halves.
    have hEv : ∀ j < 2 ^ k, toNat (E.getD j default) =
        polyVal (2 ^ (2 * e * j)) (evens (vals xs)) % fermat n := fun j hj => by
      rw [ve j hj, vals, vals, map_evens]
    have hTv : ∀ j < 2 ^ k, toNat (T.getD j default) =
        (polyVal (2 ^ (2 * e * j)) (odds (vals xs)) % fermat n * 2 ^ (e * j)) % fermat n :=
      fun j hj => by
        rw [vtw j hj, toNat_mulPow2 _ _ _ hn (rO j hj).1 (rO j hj).2, vo j hj, vals, vals,
          map_odds]
    have hsq : ∀ j, 2 ^ (e * j) * 2 ^ (e * j) = 2 ^ (2 * e * j) := fun j => by
      rw [← Nat.pow_add, Nat.mul_assoc, Nat.two_mul]
    refine ⟨by simp [le, ltw, Nat.pow_succ]; lia, fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (2 ^ k) with h | h
      · rw [g1 j h]
        exact ⟨size_addMod _ _ _, by
          rw [toNat_addMod _ _ _ hn (rE j h).1 (rT j h).1 (rE j h).2 (rT j h).2]
          exact Nat.mod_lt _ hFpos⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 ^ k := ⟨j - 2 ^ k, by lia⟩
        have h' : j' < 2 ^ k := by rw [Nat.pow_succ] at hj; lia
        rw [g2 j' h']
        exact ⟨size_subMod _ _ _ (rE j' h').1, toNat_subMod_lt _ _ _ (rE j' h').2 (rT j' h').2⟩
    · rcases Nat.lt_or_ge j (2 ^ k) with h | h
      · rw [g1 j h, toNat_addMod _ _ _ hn (rE j h).1 (rT j h).1 (rE j h).2 (rT j h).2, hEv j h,
          hTv j h, butterfly_add]
        conv => rhs; rw [polyVal_evens_odds, hsq]
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 ^ k := ⟨j - 2 ^ k, by lia⟩
        have h' : j' < 2 ^ k := by rw [Nat.pow_succ] at hj; lia
        rw [g2 j' h', toNat_subMod _ _ _ (rE j' h').2 (rT j' h').2, hEv j' h', hTv j' h']
        conv => rhs; rw [polyVal_evens_odds,
          show 2 ^ (e * (j' + 2 ^ k)) = 2 ^ (e * j') * 2 ^ (e * 2 ^ k) by
            rw [Nat.mul_add, Nat.pow_add]]
        -- `(ωʲ u)² ≡ ω²ʲ`, since `u = ω^(2ᵏ) ≡ -1`.
        have hu2 := sq_of_neg_one hw'
        have ht : (2 ^ (e * j') * 2 ^ (e * 2 ^ k) * (2 ^ (e * j') * 2 ^ (e * 2 ^ k))) %
            fermat n = 2 ^ (2 * e * j') % fermat n := by
          rw [show 2 ^ (e * j') * 2 ^ (e * 2 ^ k) * (2 ^ (e * j') * 2 ^ (e * 2 ^ k)) =
              (2 ^ (e * j') * 2 ^ (e * j')) * (2 ^ (e * 2 ^ k) * 2 ^ (e * 2 ^ k)) by
              rw [Nat.mul_assoc, Nat.mul_left_comm (2 ^ (e * 2 ^ k)), ← Nat.mul_assoc],
            Nat.mul_mod, hu2, ← Nat.mul_mod, Nat.mul_one, hsq]
        exact (butterfly_sub _ _ _ _ _ _ _ (polyVal_mod ht _) (polyVal_mod ht _) hw').symm

end MPN.FFT
