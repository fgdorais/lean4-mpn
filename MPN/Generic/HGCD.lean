/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops

/-!
# Half-gcd, at any base

The subquadratic reduction of a pair of numbers for the greatest common divisor, after Schönhage
and Möller (GMP's `mpn_hgcd`): the matrix of Euclid's steps that halves `a ≥ b` is computed from
their top halves, recursively, and applied to the full numbers with products. A matrix of
determinant `±1` keeps the greatest common divisor whatever its entries (`gcd_applyInv`), so none
of the matrices needs a proof of how well it reduces: the caller only checks that the numbers
got smaller. Matrices have nonnegative entries and the sign of their determinant, and their
determinant stays `±1` by construction, as products of elementary matrices and of the matrices
of a base step, which the instance provides with a proof of their determinant.
-/

namespace MPN

/-- A `2 × 2` matrix with nonnegative entries, and the sign of its determinant. -/
public structure Mat2 (α : Type) where
  m11 : α
  m12 : α
  m21 : α
  m22 : α
  /-- Whether the determinant is `-1` rather than `1`. -/
  neg : Bool

namespace NatOps

variable {α : Type} (o : NatOps α)

/-- `0`. -/
public def zero : α := o.sub o.one o.one

public theorem val_zero : o.val o.zero = 0 := by
  rw [zero, o.val_sub _ _ (Nat.le_refl _)]; simp

/-- `M` has determinant `±1`, with the sign of `M.neg`. -/
@[expose] public def Unimodular (M : Mat2 α) : Prop :=
  (o.val M.m11 * o.val M.m22 : Int) - o.val M.m12 * o.val M.m21 = if M.neg then -1 else 1

/-- The identity matrix. -/
public def matId : Mat2 α := ⟨o.one, o.zero, o.zero, o.one, false⟩

public theorem unimodular_matId : o.Unimodular o.matId := by
  simp [Unimodular, matId, val_one, val_zero]

/-- The matrix `[[q, 1], [1, 0]]` of a step of Euclid's algorithm, of determinant `-1`. -/
public def matStep (q : α) : Mat2 α := ⟨q, o.one, o.one, o.zero, true⟩

public theorem unimodular_matStep (q : α) : o.Unimodular (o.matStep q) := by
  simp [Unimodular, matStep, val_one, val_zero]

/-- The matrix `[[0, 1], [1, 0]]`, which swaps the two numbers. -/
public def matSwap : Mat2 α := ⟨o.zero, o.one, o.one, o.zero, true⟩

public theorem unimodular_matSwap : o.Unimodular o.matSwap := by
  simp [Unimodular, matSwap, val_one, val_zero]

/-- The product of two matrices. -/
public def matMul (M N : Mat2 α) : Mat2 α :=
  ⟨o.add (o.mul M.m11 N.m11) (o.mul M.m12 N.m21), o.add (o.mul M.m11 N.m12) (o.mul M.m12 N.m22),
    o.add (o.mul M.m21 N.m11) (o.mul M.m22 N.m21), o.add (o.mul M.m21 N.m12) (o.mul M.m22 N.m22),
    M.neg != N.neg⟩

private theorem det_mul (a b c d e f g h : Int) :
    (a * e + b * g) * (c * f + d * h) - (a * f + b * h) * (c * e + d * g) =
      (a * d - b * c) * (e * h - f * g) := by
  grind

public theorem unimodular_matMul (M N : Mat2 α) (hM : o.Unimodular M) (hN : o.Unimodular N) :
    o.Unimodular (o.matMul M N) := by
  unfold Unimodular at *
  simp only [matMul, o.val_add, o.val_mul]
  push_cast
  rw [det_mul, hM, hN]
  rcases Bool.eq_false_or_eq_true M.neg with h | h <;>
    rcases Bool.eq_false_or_eq_true N.neg with h' | h' <;> simp [h, h']

/-- `|p - q|`. -/
public def absDiff (p q : α) : α := if o.le q p then o.sub p q else o.sub q p

public theorem val_absDiff (p q : α) :
    o.val (o.absDiff p q) = ((o.val p : Int) - o.val q).natAbs := by
  unfold absDiff
  split
  · rename_i h
    rw [o.le_iff] at h
    rw [o.val_sub _ _ h]
    lia
  · rename_i h
    rw [o.le_iff] at h
    rw [o.val_sub _ _ (by lia)]
    lia

/--
The numbers `|m₂₂ a - m₁₂ b|` and `|m₁₁ b - m₂₁ a|`: `M⁻¹ (a, b)` up to signs, which are the
numbers `M` came from when it is the matrix of Euclid's steps on `a` and `b`.
-/
public def applyInv (M : Mat2 α) (a b : α) : α × α :=
  (o.absDiff (o.mul M.m22 a) (o.mul M.m12 b), o.absDiff (o.mul M.m11 b) (o.mul M.m21 a))

/-- A matrix of determinant `±1` keeps the greatest common divisor. -/
private theorem gcd_unimodular (a b : Nat) (A B C D : Int)
    (h : A * D - B * C = 1 ∨ A * D - B * C = -1) :
    Nat.gcd (A * a + B * b).natAbs (C * a + D * b).natAbs = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · have hx : (Nat.gcd (A * a + B * b).natAbs (C * a + D * b).natAbs : Int) ∣ A * a + B * b :=
      Int.ofNat_dvd_left.2 (Nat.gcd_dvd_left _ _)
    have hy : (Nat.gcd (A * a + B * b).natAbs (C * a + D * b).natAbs : Int) ∣ C * a + D * b :=
      Int.ofNat_dvd_left.2 (Nat.gcd_dvd_right _ _)
    have ha : D * (A * a + B * b) - B * (C * a + D * b) = (A * D - B * C) * a := by grind
    have hb : A * (C * a + D * b) - C * (A * a + B * b) = (A * D - B * C) * b := by grind
    have hda := Int.dvd_sub (Int.dvd_trans hx (Int.dvd_mul_left D _))
      (Int.dvd_trans hy (Int.dvd_mul_left B _))
    have hdb := Int.dvd_sub (Int.dvd_trans hy (Int.dvd_mul_left A _))
      (Int.dvd_trans hx (Int.dvd_mul_left C _))
    rw [ha] at hda
    rw [hb] at hdb
    refine Nat.dvd_gcd ?_ ?_
    · rcases h with h | h <;> rw [h] at hda <;> simp at hda <;> exact Int.natCast_dvd_natCast.1 hda
    · rcases h with h | h <;> rw [h] at hdb <;> simp at hdb <;> exact Int.natCast_dvd_natCast.1 hdb
  · have ga : (Nat.gcd a b : Int) ∣ (a : Int) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a b)
    have gb : (Nat.gcd a b : Int) ∣ (b : Int) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right a b)
    refine Nat.dvd_gcd ?_ ?_
    · exact Int.ofNat_dvd_left.1 (Int.dvd_add (Int.dvd_trans ga (Int.dvd_mul_left A _))
        (Int.dvd_trans gb (Int.dvd_mul_left B _)))
    · exact Int.ofNat_dvd_left.1 (Int.dvd_add (Int.dvd_trans ga (Int.dvd_mul_left C _))
        (Int.dvd_trans gb (Int.dvd_mul_left D _)))

/-- `applyInv` keeps the greatest common divisor, for any matrix of determinant `±1`. -/
public theorem gcd_applyInv (M : Mat2 α) (hM : o.Unimodular M) (a b : α) :
    Nat.gcd (o.val (o.applyInv M a b).1) (o.val (o.applyInv M a b).2) =
      Nat.gcd (o.val a) (o.val b) := by
  simp only [applyInv, val_absDiff, o.val_mul]
  have h := gcd_unimodular (o.val a) (o.val b) (o.val M.m22) (-(o.val M.m12 : Int))
    (-(o.val M.m21 : Int)) (o.val M.m11) (by
      unfold Unimodular at hM
      cases hn : M.neg <;> rw [hn] at hM <;> simp at hM
      · left; lia
      · right; lia)
  rw [← h]
  congr 1
  · congr 1; push_cast; lia
  · congr 1; push_cast; lia

/--
`applyInv` when its signs are right: `m₂₂ a ≥ m₁₂ b` and `m₁₁ b ≥ m₂₁ a` for determinant `1`, the
reverse for `-1`, so that `(a, b) = M (x, y)` exactly and `M` composes with the matrices of `x`
and `y`. A matrix from the top limbs of `a` and `b` that went one step too far fails this.
-/
public def applyInvC (M : Mat2 α) (a b : α) : Option (α × α) :=
  let p₁ := o.mul M.m22 a
  let q₁ := o.mul M.m12 b
  let p₂ := o.mul M.m11 b
  let q₂ := o.mul M.m21 a
  if (if M.neg then o.le p₁ q₁ && o.le p₂ q₂ else o.le q₁ p₁ && o.le q₂ p₂) then
    some (o.absDiff p₁ q₁, o.absDiff p₂ q₂)
  else none

public theorem gcd_applyInvC (M : Mat2 α) (hM : o.Unimodular M) (a b : α) (p : α × α)
    (h : o.applyInvC M a b = some p) :
    Nat.gcd (o.val p.1) (o.val p.2) = Nat.gcd (o.val a) (o.val b) := by
  unfold applyInvC at h
  dsimp only at h
  split at h <;> split at h <;>
    first
    | (rw [Option.some.injEq] at h; subst h; exact o.gcd_applyInv M hM a b)
    | exact absurd h (by simp)

/-- The pair `p` with the larger number first, and `M` with its columns swapped if they were not. -/
public def orient (M : Mat2 α) (p : α × α) : Mat2 α × α × α :=
  if o.le p.2 p.1 then (M, p.1, p.2) else (o.matMul M o.matSwap, p.2, p.1)

public theorem unimodular_orient (M : Mat2 α) (hM : o.Unimodular M) (p : α × α) :
    o.Unimodular (o.orient M p).1 := by
  unfold orient
  split
  · exact hM
  · exact o.unimodular_matMul _ _ hM o.unimodular_matSwap

public theorem gcd_orient (M : Mat2 α) (p : α × α) :
    Nat.gcd (o.val (o.orient M p).2.1) (o.val (o.orient M p).2.2) =
      Nat.gcd (o.val p.1) (o.val p.2) := by
  unfold orient
  split
  · rfl
  · exact Nat.gcd_comm _ _

/-- What half-gcd computes: a matrix of determinant `±1`, and a pair with the same gcd. -/
@[expose] public def HgcdOK (a b : α) (r : Mat2 α × α × α) : Prop :=
  o.Unimodular r.1 ∧ Nat.gcd (o.val r.2.1) (o.val r.2.2) = Nat.gcd (o.val a) (o.val b)

/--
The base case: steps from `step`, the instance's reduction of two short numbers (Lehmer's steps
on their leading words, for one), applied with `applyInvC` while they make the numbers smaller and
`b ≥ Bˢ`, at most `fuel` of them, with the product of their matrices.
-/
def baseLoop (step : α → α → Option (Mat2 α)) (s : Nat) (a b : α) (M : Mat2 α) :
    Nat → Mat2 α × α × α
  | 0 => (M, a, b)
  | fuel + 1 =>
    if o.le (o.pow s) b then
      match step a b with
      | none => (M, a, b)
      | some S =>
        match o.applyInvC S a b with
        | none => (M, a, b)
        | some p =>
          if o.le p.2 p.1 ∧ !(o.le b p.2) then baseLoop step s p.1 p.2 (o.matMul M S) fuel
          else (M, a, b)
    else (M, a, b)

theorem baseLoop_ok (step : α → α → Option (Mat2 α))
    (hstep : ∀ a b S, step a b = some S → o.Unimodular S) (s : Nat) :
    ∀ fuel (a b : α) (M : Mat2 α), o.Unimodular M →
      o.HgcdOK a b (o.baseLoop step s a b M fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a b M hM; exact ⟨hM, rfl⟩
  | succ fuel ih =>
    intro a b M hM
    simp only [baseLoop]
    split
    · split
      · exact ⟨hM, rfl⟩
      · rename_i S hS
        split
        · exact ⟨hM, rfl⟩
        · rename_i p hp
          split
          · obtain ⟨h₁, h₂⟩ := ih p.1 p.2 _ (o.unimodular_matMul _ _ hM (hstep _ _ _ hS))
            exact ⟨h₁, by rw [h₂, o.gcd_applyInvC S (hstep _ _ _ hS) a b p hp]⟩
          · exact ⟨hM, rfl⟩
    · exact ⟨hM, rfl⟩

/--
Half-gcd: the matrix of Euclid's steps that brings `a ≥ b`, of `n` limbs, below `Bˢ` with
`s = ⌊n / 2⌋ + 1`, or close to it, and the numbers it brings them to. Below `T` limbs by
`baseLoop`; above, the matrix of the top `n - s` limbs, recursively, applied to `a` and `b`, then
one step of Euclid's algorithm, then the matrix of the top limbs of what is left. A matrix from
top limbs that went too far for the full numbers (`applyInvC`) is dropped. Only the determinant
and the gcd are proved (`hgcd_ok`): the caller checks how far the numbers came down.
-/
public def hgcd (step : α → α → Option (Mat2 α)) (T : Nat) (a b : α) : Mat2 α × α × α :=
  let n := o.size a
  let s := n / 2 + 1
  if !(o.le (o.pow s) b) then (o.matId, a, b)
  else if n ≤ T then o.baseLoop step s a b o.matId (32 * n)
  else
    match o.applyInvC (hgcd step T (o.hi s a) (o.hi s b)).1 a b with
    | none => (o.matId, a, b)
    | some p =>
      let r := o.orient (hgcd step T (o.hi s a) (o.hi s b)).1 p
      if !(o.le (o.pow s) r.2.2) then r
      else
        -- One step of Euclid's algorithm, then the top limbs of what is left.
        let qr := o.divRem r.2.1 r.2.2
        let M₃ := o.matMul r.1 (o.matStep qr.1)
        let m := o.size r.2.2
        if _h : n < m then (M₃, r.2.2, qr.2)
        else
          match o.applyInvC (hgcd step T (o.hi (2 * s - m) r.2.2) (o.hi (2 * s - m) qr.2)).1
              r.2.2 qr.2 with
          | none => (M₃, r.2.2, qr.2)
          | some p₂ =>
            let r₂ := o.orient (hgcd step T (o.hi (2 * s - m) r.2.2) (o.hi (2 * s - m) qr.2)).1 p₂
            (o.matMul M₃ r₂.1, r₂.2)
termination_by o.size a
decreasing_by
  all_goals rw [o.size_hi]; lia

public theorem hgcd_ok (step : α → α → Option (Mat2 α))
    (hstep : ∀ a b S, step a b = some S → o.Unimodular S) (T : Nat) (a b : α) :
    o.HgcdOK a b (o.hgcd step T a b) := by
  induction hn : o.size a using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    unfold hgcd
    dsimp only
    split
    · exact ⟨o.unimodular_matId, rfl⟩
    split
    · exact o.baseLoop_ok step hstep _ _ _ _ _ o.unimodular_matId
    rename_i hT
    have hR₁ := ih (o.size (o.hi (o.size a / 2 + 1) a)) (by rw [o.size_hi]; lia)
      (o.hi (o.size a / 2 + 1) a) (o.hi (o.size a / 2 + 1) b) rfl
    split
    · exact ⟨o.unimodular_matId, rfl⟩
    rename_i p hp
    have hg₁ := o.gcd_applyInvC _ hR₁.1 a b p hp
    have hM₂ := o.unimodular_orient _ hR₁.1 p
    have hg₂ := o.gcd_orient (o.hgcd step T (o.hi (o.size a / 2 + 1) a)
      (o.hi (o.size a / 2 + 1) b)).1 p
    rw [hg₁] at hg₂
    generalize o.orient (o.hgcd step T (o.hi (o.size a / 2 + 1) a)
      (o.hi (o.size a / 2 + 1) b)).1 p = r at hM₂ hg₂
    split
    · exact ⟨hM₂, hg₂⟩
    rename_i hb₁
    -- After the step of Euclid's algorithm, with `b₁ ≥ Bˢ > 0`.
    have hd : 0 < o.val r.2.2 := by
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hb₁
      have := (o.le_iff _ _).1 hb₁
      rw [o.val_pow] at this
      have := Nat.pow_pos (n := o.size a / 2 + 1) (Nat.lt_trans Nat.zero_lt_one o.one_lt_B)
      lia
    have hg₃ : Nat.gcd (o.val r.2.2) (o.val (o.divRem r.2.1 r.2.2).2) =
        Nat.gcd (o.val a) (o.val b) := by
      rw [← hg₂, (o.val_divRem _ _ (by lia)).2, Nat.gcd_comm (o.val r.2.1) (o.val r.2.2),
        Nat.gcd_rec (o.val r.2.2) (o.val r.2.1), Nat.gcd_comm]
    have hM₃ := o.unimodular_matMul _ _ hM₂ (o.unimodular_matStep (o.divRem r.2.1 r.2.2).1)
    split
    · exact ⟨hM₃, hg₃⟩
    rename_i hm
    have hR₂ := ih _ (by rw [o.size_hi]; lia)
      (o.hi (2 * (o.size a / 2 + 1) - o.size r.2.2) r.2.2)
      (o.hi (2 * (o.size a / 2 + 1) - o.size r.2.2) (o.divRem r.2.1 r.2.2).2) rfl
    split
    · exact ⟨hM₃, hg₃⟩
    rename_i p₂ hp₂
    have hg₄ := o.gcd_applyInvC _ hR₂.1 _ _ p₂ hp₂
    refine ⟨o.unimodular_matMul _ _ hM₃ (o.unimodular_orient _ hR₂.1 p₂), ?_⟩
    show Nat.gcd (o.val (o.orient _ p₂).2.1) (o.val (o.orient _ p₂).2.2) = _
    rw [o.gcd_orient, hg₄, hg₃]

/--
One reduction of `a ≥ b` for the greatest common divisor: the numbers of `hgcd`, the larger first.
It keeps the greatest common divisor (`gcd_hgcdReduce`); the caller checks that they got smaller.
-/
public def hgcdReduce (step : α → α → Option (Mat2 α)) (T : Nat) (a b : α) : α × α :=
  let p := (o.hgcd step T a b).2
  if o.le p.2 p.1 then p else (p.2, p.1)

public theorem gcd_hgcdReduce (step : α → α → Option (Mat2 α))
    (hstep : ∀ a b S, step a b = some S → o.Unimodular S) (T : Nat) (a b : α) :
    Nat.gcd (o.val (o.hgcdReduce step T a b).1) (o.val (o.hgcdReduce step T a b).2) =
      Nat.gcd (o.val a) (o.val b) := by
  have h := (o.hgcd_ok step hstep T a b).2
  unfold hgcdReduce
  dsimp only
  split
  · exact h
  · rw [Nat.gcd_comm]; exact h

end NatOps

end MPN
