/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# The value of a list of limbs

`ofLimbs l` is the natural number that the little-endian base 2³² limbs `l` denote. It is the
specification of the arithmetic: every operation is proved correct by computing `ofLimbs` of
its result. A list is *trimmed* when its last limb is nonzero, and trimmed lists represent each
natural number exactly once.
-/

namespace Bignum

/-- The natural number that the little-endian base 2³² limbs `l` denote. -/
@[expose] public def ofLimbs : List UInt32 → Nat
  | [] => 0
  | d :: l => d.toNat + 2 ^ 32 * ofLimbs l

@[simp] public theorem ofLimbs_nil : ofLimbs [] = 0 := rfl

@[simp] public theorem ofLimbs_cons (d : UInt32) (l : List UInt32) :
    ofLimbs (d :: l) = d.toNat + 2 ^ 32 * ofLimbs l := rfl

public theorem ofLimbs_append (l₁ l₂ : List UInt32) :
    ofLimbs (l₁ ++ l₂) = ofLimbs l₁ + 2 ^ (32 * l₁.length) * ofLimbs l₂ := by
  induction l₁ with
  | nil => simp
  | cons d l ih =>
    simp only [List.cons_append, ofLimbs_cons, ih, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.pow_add]
    grind

public theorem ofLimbs_concat (l : List UInt32) (d : UInt32) :
    ofLimbs (l ++ [d]) = ofLimbs l + 2 ^ (32 * l.length) * d.toNat := by
  simp [ofLimbs_append]

/-- Peels off the limb at `j`, which is `0` past the end of the list. -/
public theorem ofLimbs_drop (l : List UInt32) (j : Nat) :
    ofLimbs (l.drop j) = (l.getD j 0).toNat + 2 ^ 32 * ofLimbs (l.drop (j + 1)) := by
  by_cases h : j < l.length
  · rw [List.drop_eq_getElem_cons h, ofLimbs_cons]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ j)]

/-- Replacing the limb at `k` changes the value by the difference, scaled by `2^(32 k)`. -/
public theorem ofLimbs_set (l : List UInt32) (k : Nat) (v : UInt32) (h : k < l.length) :
    ofLimbs (l.set k v) + 2 ^ (32 * k) * l[k].toNat = ofLimbs l + 2 ^ (32 * k) * v.toNat := by
  induction l generalizing k with
  | nil => simp at h
  | cons d l ih =>
    cases k with
    | zero => simp; omega
    | succ k =>
      have := ih k (by simpa using h)
      simp only [List.set_cons_succ, ofLimbs_cons, List.getElem_cons_succ, Nat.mul_add,
        Nat.mul_one, Nat.pow_add]
      grind

public theorem ofLimbs_lt (l : List UInt32) : ofLimbs l < 2 ^ (32 * l.length) := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd := d.toNat_lt
    have : 2 ^ 32 * (ofLimbs l + 1) ≤ 2 ^ 32 * 2 ^ (32 * l.length) := Nat.mul_le_mul_left _ ih
    simp only [ofLimbs_cons, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add] at *
    rw [Nat.mul_comm (2 ^ (32 * l.length))]
    omega

public theorem ofLimbs_eq_zero_iff {l : List UInt32} : ofLimbs l = 0 ↔ ∀ d ∈ l, d = 0 := by
  induction l with
  | nil => simp
  | cons d l ih =>
    simp only [ofLimbs_cons, List.mem_cons, forall_eq_or_imp, ← ih]
    have : d = 0 ↔ d.toNat = 0 := by simp [← UInt32.toNat_inj]
    rw [this]
    omega

/-- A number below `2^(32 k)` has no nonzero limb at `k` or above. -/
public theorem getElem_eq_zero_of_ofLimbs_lt {l : List UInt32} {k : Nat} (hk : k < l.length)
    (h : ofLimbs l < 2 ^ (32 * k)) : l[k] = 0 := by
  have hsplit := ofLimbs_append (l.take k) (l.drop k)
  rw [List.take_append_drop, List.length_take_of_le (Nat.le_of_lt hk)] at hsplit
  have hpos : 0 < 2 ^ (32 * k) := Nat.two_pow_pos _
  have hd : ofLimbs (l.drop k) = 0 := by
    rcases Nat.eq_zero_or_pos (ofLimbs (l.drop k)) with h0 | h0
    · exact h0
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) h0
      omega
  have hl : 0 < (l.drop k).length := by simp; omega
  have := ofLimbs_eq_zero_iff.1 hd (l.drop k)[0] (List.getElem_mem hl)
  simpa using this

/-- Dropping limbs at `n` and above keeps a value below `2^(32 n)`. -/
public theorem ofLimbs_take_of_lt {l : List UInt32} {n : Nat} (h : ofLimbs l < 2 ^ (32 * n)) :
    ofLimbs (l.take n) = ofLimbs l := by
  by_cases hn : l.length ≤ n
  · rw [List.take_of_length_le hn]
  · have hsplit := ofLimbs_append (l.take n) (l.drop n)
    rw [List.take_append_drop, List.length_take_of_le (by omega)] at hsplit
    have hd : ofLimbs (l.drop n) = 0 := by
      rcases Nat.eq_zero_or_pos (ofLimbs (l.drop n)) with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_left (2 ^ (32 * n)) h0
        omega
    rw [hsplit, hd, Nat.mul_zero, Nat.add_zero]

/-- The value of the first `i + 1` limbs. -/
public theorem ofLimbs_take_add_one (l : List UInt32) (i : Nat) (h : i < l.length) :
    ofLimbs (l.take (i + 1)) = ofLimbs (l.take i) + 2 ^ (32 * i) * l[i].toNat := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, ofLimbs_concat,
    List.length_take_of_le (Nat.le_of_lt h)]

@[simp] public theorem ofLimbs_replicate_zero (n : Nat) : ofLimbs (List.replicate n 0) = 0 :=
  ofLimbs_eq_zero_iff.2 fun _ h => (List.mem_replicate.1 h).2

/-- Trailing zero limbs do not change the value. -/
@[simp] public theorem ofLimbs_append_replicate_zero (l : List UInt32) (n : Nat) :
    ofLimbs (l ++ List.replicate n 0) = ofLimbs l := by
  simp [ofLimbs_append]

/-! ## Trimmed lists -/

/-- A list of limbs is trimmed when it has no trailing zero limb. -/
@[expose] public def IsTrimmed (l : List UInt32) : Prop := l.getLast? ≠ some 0

public instance : DecidablePred IsTrimmed := fun l =>
  inferInstanceAs (Decidable (l.getLast? ≠ some 0))

@[simp] public theorem isTrimmed_nil : IsTrimmed [] := by simp [IsTrimmed]

public theorem IsTrimmed.of_cons {d : UInt32} {l : List UInt32} (h : IsTrimmed (d :: l)) :
    IsTrimmed l := by
  cases l with
  | nil => simp
  | cons d' l => simpa [IsTrimmed, List.getLast?_cons_cons] using h

/-- A nonempty trimmed list denotes a positive number. -/
public theorem IsTrimmed.ofLimbs_pos {l : List UInt32} (h : IsTrimmed l) (hl : l ≠ []) :
    0 < ofLimbs l := by
  refine Nat.pos_of_ne_zero fun h0 => h ?_
  rw [List.getLast?_eq_some_getLast hl]
  exact congrArg some (ofLimbs_eq_zero_iff.1 h0 _ (List.getLast_mem hl))

/-- Trimmed lists represent each natural number exactly once. -/
public theorem IsTrimmed.ofLimbs_inj {l₁ l₂ : List UInt32} (h₁ : IsTrimmed l₁)
    (h₂ : IsTrimmed l₂) (h : ofLimbs l₁ = ofLimbs l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons d l => exact absurd h (Nat.ne_of_lt (h₂.ofLimbs_pos (List.cons_ne_nil d l)))
  | cons d l ih =>
    cases l₂ with
    | nil => exact absurd h.symm (Nat.ne_of_lt (h₁.ofLimbs_pos (List.cons_ne_nil d l)))
    | cons d' l' =>
      have := d.toNat_lt
      have := d'.toNat_lt
      simp only [ofLimbs_cons, Nat.reducePow] at h
      have hd : d.toNat = d'.toNat := by omega
      have hl : ofLimbs l = ofLimbs l' := by omega
      rw [UInt32.toNat_inj.1 hd, ih h₁.of_cons h₂.of_cons hl]

/-- Lists of limbs of the same length with the same value are equal. -/
public theorem ofLimbs_inj_of_length {l₁ l₂ : List UInt32} (hl : l₁.length = l₂.length)
    (hv : ofLimbs l₁ = ofLimbs l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (List.eq_nil_of_length_eq_zero (by simpa using hl.symm)).symm
  | cons d l ih =>
    cases l₂ with
    | nil => simp at hl
    | cons d' l' =>
      simp only [ofLimbs_cons] at hv
      have hd := d.toNat_lt
      have hd' := d'.toNat_lt
      have h₁ : d.toNat = d'.toNat := by omega
      have h₂ : ofLimbs l = ofLimbs l' := by omega
      rw [UInt32.toNat_inj.1 h₁, ih (by simpa using hl) h₂]

/-! ## Removing trailing zeros -/

/-- Removes the trailing zero limbs. -/
@[expose] public def trimLimbs (l : List UInt32) : List UInt32 :=
  (l.reverse.dropWhile (· == 0)).reverse

@[simp] public theorem ofLimbs_trimLimbs (l : List UInt32) : ofLimbs (trimLimbs l) = ofLimbs l := by
  have h := List.takeWhile_append_dropWhile (p := (· == 0)) (l := l.reverse)
  conv => rhs; rw [← List.reverse_reverse l, ← h]
  have hz : ofLimbs (l.reverse.takeWhile (· == 0)).reverse = 0 :=
    ofLimbs_eq_zero_iff.2 fun d h => by
      simpa using List.all_eq_true.1 List.all_takeWhile d (List.mem_reverse.1 h)
  rw [List.reverse_append, ofLimbs_append, hz, Nat.mul_zero, Nat.add_zero]
  rfl

public theorem isTrimmed_trimLimbs (l : List UInt32) : IsTrimmed (trimLimbs l) := by
  simp only [IsTrimmed, trimLimbs, List.getLast?_reverse]
  intro h
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 h
  have := List.head_dropWhile_not (· == 0) (l := l.reverse) (by simp [ht])
  simp [ht] at this

/-! ## Prefixes -/

/-- The value of the first `i + 1` limbs, with `0` for limbs past the end. -/
public theorem ofLimbs_take_add_one_getD (l : List UInt32) (i : Nat) :
    ofLimbs (l.take (i + 1)) = ofLimbs (l.take i) + 2 ^ (32 * i) * (l.getD i 0).toNat := by
  by_cases h : i < l.length
  · rw [ofLimbs_take_add_one l i h]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ i)]

public theorem ofLimbs_take_lt (l : List UInt32) (i : Nat) : ofLimbs (l.take i) < 2 ^ (32 * i) := by
  have := ofLimbs_lt (l.take i)
  have : 2 ^ (32 * (l.take i).length) ≤ 2 ^ (32 * i) :=
    Nat.pow_le_pow_right (by decide) (by simp; omega)
  omega

end Bignum
