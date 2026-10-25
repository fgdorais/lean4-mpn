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
of a base case, which the instance provides with a proof of its determinant and exact relation.
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
public theorem gcd_unimodular (a b : Nat) (A B C D : Int)
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

/-! ## The exact relation -/

/-- `(a, b) = M (x, y)`, on values. -/
@[expose] public def Fwd (M : Mat2 α) (a b x y : α) : Prop :=
  o.val a = o.val M.m11 * o.val x + o.val M.m12 * o.val y ∧
    o.val b = o.val M.m21 * o.val x + o.val M.m22 * o.val y

public theorem fwd_matId (a b : α) : o.Fwd o.matId a b a b := by
  simp [Fwd, matId, val_one, val_zero]

public theorem fwd_matMul (M N : Mat2 α) (a b a₁ b₁ x y : α) (h₁ : o.Fwd M a b a₁ b₁)
    (h₂ : o.Fwd N a₁ b₁ x y) : o.Fwd (o.matMul M N) a b x y := by
  unfold Fwd at *
  simp only [matMul, o.val_add, o.val_mul]
  rw [h₁.1, h₁.2, h₂.1, h₂.2]
  constructor <;> grind

/-- The gcd is that of the numbers a matrix of determinant `±1` takes to `a` and `b`. -/
public theorem gcd_of_fwd (M : Mat2 α) (hM : o.Unimodular M) (a b x y : α)
    (h : o.Fwd M a b x y) : Nat.gcd (o.val a) (o.val b) = Nat.gcd (o.val x) (o.val y) := by
  have g := gcd_unimodular (o.val x) (o.val y) (o.val M.m11) (o.val M.m12) (o.val M.m21)
    (o.val M.m22) (by
      unfold Unimodular at hM
      cases hn : M.neg <;> rw [hn] at hM <;> simp at hM
      · left; lia
      · right; lia)
  rw [← g, h.1, h.2]
  norm_cast

/-- The determinant `±1` on natural numbers, by its sign. -/
private theorem det_nat (M : Mat2 α) (hM : o.Unimodular M) :
    (M.neg = false → o.val M.m11 * o.val M.m22 = o.val M.m12 * o.val M.m21 + 1) ∧
      (M.neg = true → o.val M.m12 * o.val M.m21 = o.val M.m11 * o.val M.m22 + 1) := by
  unfold Unimodular at hM
  constructor
  · intro hn
    rw [hn] at hM
    have : ((o.val M.m11 * o.val M.m22 : Nat) : Int) =
        ((o.val M.m12 * o.val M.m21 + 1 : Nat) : Int) := by
      push_cast; simp at hM; lia
    exact Int.ofNat_inj.1 this
  · intro hn
    rw [hn] at hM
    have : ((o.val M.m12 * o.val M.m21 : Nat) : Int) =
        ((o.val M.m11 * o.val M.m22 + 1 : Nat) : Int) := by
      push_cast; simp at hM; lia
    exact Int.ofNat_inj.1 this

private theorem fwd_pos (m₁₁ m₁₂ m₂₁ m₂₂ a b X Y : Nat) (hd : m₁₁ * m₂₂ = m₁₂ * m₂₁ + 1)
    (hX : X + m₁₂ * b = m₂₂ * a) (hY : Y + m₂₁ * a = m₁₁ * b) :
    a = m₁₁ * X + m₁₂ * Y ∧ b = m₂₁ * X + m₂₂ * Y := by
  constructor <;> grind

private theorem fwd_neg (m₁₁ m₁₂ m₂₁ m₂₂ a b X Y : Nat) (hd : m₁₂ * m₂₁ = m₁₁ * m₂₂ + 1)
    (hX : X + m₂₂ * a = m₁₂ * b) (hY : Y + m₁₁ * b = m₂₁ * a) :
    a = m₁₁ * X + m₁₂ * Y ∧ b = m₂₁ * X + m₂₂ * Y := by
  constructor <;> grind

private theorem split_pos (m₁₁ m₁₂ m₂₁ m₂₂ x₁ y₁ ah al bh bl P X Y : Nat)
    (hd : m₁₁ * m₂₂ = m₁₂ * m₂₁ + 1)
    (ha : ah = m₁₁ * x₁ + m₁₂ * y₁) (hb : bh = m₂₁ * x₁ + m₂₂ * y₁)
    (hX : X + m₁₂ * bl = x₁ * P + m₂₂ * al) (hY : Y + m₂₁ * al = y₁ * P + m₁₁ * bl) :
    ah * P + al = m₁₁ * X + m₁₂ * Y ∧ bh * P + bl = m₂₁ * X + m₂₂ * Y := by
  constructor <;> grind

private theorem split_neg (m₁₁ m₁₂ m₂₁ m₂₂ x₁ y₁ ah al bh bl P X Y : Nat)
    (hd : m₁₂ * m₂₁ = m₁₁ * m₂₂ + 1)
    (ha : ah = m₁₁ * x₁ + m₁₂ * y₁) (hb : bh = m₂₁ * x₁ + m₂₂ * y₁)
    (hX : X + m₂₂ * al = x₁ * P + m₁₂ * bl) (hY : Y + m₁₁ * bl = y₁ * P + m₂₁ * al) :
    ah * P + al = m₁₁ * X + m₁₂ * Y ∧ bh * P + bl = m₂₁ * X + m₂₂ * Y := by
  constructor <;> grind

/--
`M⁻¹ (a, b)` when its entries are nonnegative: `m₂₂ a ≥ m₁₂ b` and `m₁₁ b ≥ m₂₁ a` for determinant
`1`, the reverse for `-1`, so that `(a, b) = M (x, y)` exactly. A matrix from the top limbs of `a`
and `b` that went one step too far fails this.
-/
public def applyInvC (M : Mat2 α) (a b : α) : Option (α × α) :=
  let p₁ := o.mul M.m22 a
  let q₁ := o.mul M.m12 b
  let p₂ := o.mul M.m11 b
  let q₂ := o.mul M.m21 a
  if !M.neg then
    if o.le q₁ p₁ && o.le q₂ p₂ then some (o.sub p₁ q₁, o.sub p₂ q₂) else none
  else
    if o.le p₁ q₁ && o.le p₂ q₂ then some (o.sub q₁ p₁, o.sub q₂ p₂) else none

public theorem fwd_applyInvC (M : Mat2 α) (hM : o.Unimodular M) (a b : α) (p : α × α)
    (h : o.applyInvC M a b = some p) : o.Fwd M a b p.1 p.2 := by
  obtain ⟨hd₁, hd₂⟩ := o.det_nat M hM
  unfold applyInvC at h
  dsimp only at h
  split at h
  · rename_i hn
    simp only [Bool.not_eq_true'] at hn
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, o.le_iff, o.val_mul] at hc
      rw [Option.some.injEq] at h
      subst h
      have hX := o.val_sub (o.mul M.m22 a) (o.mul M.m12 b) 
        (by rw [o.val_mul, o.val_mul]; exact hc.1)
      have hY := o.val_sub (o.mul M.m11 b) (o.mul M.m21 a) 
        (by rw [o.val_mul, o.val_mul]; exact hc.2)
      rw [o.val_mul, o.val_mul] at hX hY
      exact fwd_pos _ _ _ _ _ _ _ _ (hd₁ hn) (by rw [hX]; lia) (by rw [hY]; lia)
    · exact absurd h (by simp)
  · rename_i hn
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hn
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, o.le_iff, o.val_mul] at hc
      rw [Option.some.injEq] at h
      subst h
      have hX := o.val_sub (o.mul M.m12 b) (o.mul M.m22 a) 
        (by rw [o.val_mul, o.val_mul]; exact hc.1)
      have hY := o.val_sub (o.mul M.m21 a) (o.mul M.m11 b) 
        (by rw [o.val_mul, o.val_mul]; exact hc.2)
      rw [o.val_mul, o.val_mul] at hX hY
      exact fwd_neg _ _ _ _ _ _ _ _ (hd₂ hn) (by rw [hX]; lia) (by rw [hY]; lia)
    · exact absurd h (by simp)

/-- The pair `p` with the larger number first, and `M` with its columns swapped if they were not. -/
public def orient (M : Mat2 α) (p : α × α) : Mat2 α × α × α :=
  if o.le p.2 p.1 then (M, p.1, p.2) else (o.matMul M o.matSwap, p.2, p.1)

public theorem unimodular_orient (M : Mat2 α) (hM : o.Unimodular M) (p : α × α) :
    o.Unimodular (o.orient M p).1 := by
  unfold orient
  split
  · exact hM
  · exact o.unimodular_matMul _ _ hM o.unimodular_matSwap

public theorem fwd_orient (M : Mat2 α) (a b : α) (p : α × α) (h : o.Fwd M a b p.1 p.2) :
    o.Fwd (o.orient M p).1 a b (o.orient M p).2.1 (o.orient M p).2.2 := by
  unfold orient
  split
  · exact h
  · apply o.fwd_matMul _ _ a b p.1 p.2 _ _ h
    simp [Fwd, matSwap, val_one, val_zero]

/--
`M⁻¹ (a, b)` from `(x₁, y₁) = M⁻¹ (⌊a / Bˢ⌋, ⌊b / Bˢ⌋)`: `x₁ Bˢ ± (m₂₂ aₗ - m₁₂ bₗ)` and
`y₁ Bˢ ± (m₁₁ bₗ - m₂₁ aₗ)` with the low limbs `aₗ`, `bₗ` of `a`, `b`, so that the products are
with the `s` low limbs only; none when a number would be negative, as in `applyInvC`.
-/
public def applySplit (M : Mat2 α) (x₁ y₁ a b : α) (s : Nat) : Option (α × α) :=
  let aₗ := o.lo s a
  let bₗ := o.lo s b
  let t₁ := o.mul M.m22 aₗ
  let u₁ := o.mul M.m12 bₗ
  let t₂ := o.mul M.m11 bₗ
  let u₂ := o.mul M.m21 aₗ
  if !M.neg then
    let X := o.add (o.shl s x₁) t₁
    let Y := o.add (o.shl s y₁) t₂
    if o.le u₁ X && o.le u₂ Y then some (o.sub X u₁, o.sub Y u₂) else none
  else
    let X := o.add (o.shl s x₁) u₁
    let Y := o.add (o.shl s y₁) u₂
    if o.le t₁ X && o.le t₂ Y then some (o.sub X t₁, o.sub Y t₂) else none

public theorem fwd_applySplit (M : Mat2 α) (hM : o.Unimodular M) (x₁ y₁ a b : α) (s : Nat)
    (h₁ : o.Fwd M (o.hi s a) (o.hi s b) x₁ y₁) (p : α × α)
    (h : o.applySplit M x₁ y₁ a b s = some p) : o.Fwd M a b p.1 p.2 := by
  obtain ⟨hd₁, hd₂⟩ := o.det_nat M hM
  unfold Fwd at h₁ ⊢
  rw [o.val_hi, o.val_hi] at h₁
  have ha := Nat.div_add_mod' (o.val a) (o.B ^ s)
  have hb := Nat.div_add_mod' (o.val b) (o.B ^ s)
  unfold applySplit at h
  dsimp only at h
  split at h
  · rename_i hn
    simp only [Bool.not_eq_true'] at hn
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, o.le_iff] at hc
      rw [Option.some.injEq] at h
      subst h
      have hX := o.val_sub _ _ hc.1
      have hY := o.val_sub _ _ hc.2
      simp only [o.val_mul, o.val_add, o.val_shl, o.val_lo] at hX hY hc
      rw [← ha, ← hb]
      exact split_pos _ _ _ _ _ _ _ _ _ _ _ _ _ (hd₁ hn) h₁.1 h₁.2 (by rw [hX]; lia)
        (by rw [hY]; lia)
    · exact absurd h (by simp)
  · rename_i hn
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hn
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, o.le_iff] at hc
      rw [Option.some.injEq] at h
      subst h
      have hX := o.val_sub _ _ hc.1
      have hY := o.val_sub _ _ hc.2
      simp only [o.val_mul, o.val_add, o.val_shl, o.val_lo] at hX hY hc
      rw [← ha, ← hb]
      exact split_neg _ _ _ _ _ _ _ _ _ _ _ _ _ (hd₂ hn) h₁.1 h₁.2 (by rw [hX]; lia)
        (by rw [hY]; lia)
    · exact absurd h (by simp)

/-- What half-gcd computes: a matrix of determinant `±1` and the numbers it takes to `a`, `b`. -/
@[expose] public def HgcdOK (a b : α) (r : Mat2 α × α × α) : Prop :=
  o.Unimodular r.1 ∧ o.Fwd r.1 a b r.2.1 r.2.2

/--
The base case: steps from `step`, the instance's reduction of two short numbers (Lehmer's steps
on their leading words, for one), applied with `applyInvC` while they make the numbers smaller and
`b ≥ Bˢ`, at most `fuel` of them, with the product of their matrices.
-/
public def baseLoop (step : α → α → Option (Mat2 α)) (s : Nat) (a b : α) (M : Mat2 α) :
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

public theorem baseLoop_ok (step : α → α → Option (Mat2 α))
    (hstep : ∀ a b S, step a b = some S → o.Unimodular S) (s : Nat) (a₀ b₀ : α) :
    ∀ fuel (a b : α) (M : Mat2 α), o.Unimodular M → o.Fwd M a₀ b₀ a b →
      o.HgcdOK a₀ b₀ (o.baseLoop step s a b M fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a b M hM hF; exact ⟨hM, hF⟩
  | succ fuel ih =>
    intro a b M hM hF
    simp only [baseLoop]
    split
    · split
      · exact ⟨hM, hF⟩
      · rename_i S hS
        split
        · exact ⟨hM, hF⟩
        · rename_i p hp
          split
          · exact ih p.1 p.2 _ (o.unimodular_matMul _ _ hM (hstep _ _ _ hS))
              (o.fwd_matMul _ _ _ _ _ _ _ _ hF (o.fwd_applyInvC S (hstep _ _ _ hS) a b p hp))
          · exact ⟨hM, hF⟩
    · exact ⟨hM, hF⟩

/-- `baseLoop` from the identity matrix, as a base case for `hgcd`. -/
public def stepBase (step : α → α → Option (Mat2 α)) (s : Nat) (a b : α) : Mat2 α × α × α :=
  o.baseLoop step s a b o.matId (32 * o.size a)

public theorem stepBase_ok (step : α → α → Option (Mat2 α))
    (hstep : ∀ a b S, step a b = some S → o.Unimodular S) (s : Nat) (a b : α) :
    o.HgcdOK a b (o.stepBase step s a b) :=
  o.baseLoop_ok step hstep s a b _ a b o.matId o.unimodular_matId (o.fwd_matId a b)

/-! ## A base case of word matrices -/

/--
The operations of a base case of half-gcd by matrices of small entries, words for example, which
the instance applies to its numbers in its own way: `step a b` is such a matrix `S` and the numbers
`(x, y)` with `(a, b) = S (x, y)`, from Lehmer's steps on the leading words of `a` and `b`, and
`mulMat M S` is the product `M S`. The entries of `S` as natural numbers are `e₁₁ S`, …,
`e₂₂ S`, and `neg S` is the sign of its determinant; `ok S` is what `mulMat` needs of `S`, such as
bounds on its entries, and `geB b s` whether `b ≥ Bˢ`, which only affects speed.
-/
public structure SmallSteps (o : NatOps α) where
  /-- The matrices. -/
  W : Type
  /-- The entries of a matrix. -/
  e₁₁ : W → Nat
  e₁₂ : W → Nat
  e₂₁ : W → Nat
  e₂₂ : W → Nat
  /-- The sign of the determinant. -/
  neg : W → Bool
  /-- What `mulMat` needs of a matrix. -/
  ok : W → Prop
  /-- A step: a matrix and the numbers it takes to `a` and `b`. -/
  step : α → α → Option (W × α × α)
  /-- The product of a matrix of `NatOps` by a small matrix. -/
  mulMat : Mat2 α → W → Mat2 α
  /-- Whether `b ≥ Bˢ`. -/
  geB : α → Nat → Bool
  det_of_ok : ∀ S, ok S → (neg S = false → e₁₁ S * e₂₂ S = e₁₂ S * e₂₁ S + 1) ∧
    (neg S = true → e₁₂ S * e₂₁ S = e₁₁ S * e₂₂ S + 1)
  step_spec : ∀ a b r, step a b = some r → ok r.1 ∧
    o.val a = e₁₁ r.1 * o.val r.2.1 + e₁₂ r.1 * o.val r.2.2 ∧
    o.val b = e₂₁ r.1 * o.val r.2.1 + e₂₂ r.1 * o.val r.2.2
  mulMat_spec : ∀ M S, ok S →
    o.val (mulMat M S).m11 = o.val M.m11 * e₁₁ S + o.val M.m12 * e₂₁ S ∧
    o.val (mulMat M S).m12 = o.val M.m11 * e₁₂ S + o.val M.m12 * e₂₂ S ∧
    o.val (mulMat M S).m21 = o.val M.m21 * e₁₁ S + o.val M.m22 * e₂₁ S ∧
    o.val (mulMat M S).m22 = o.val M.m21 * e₁₂ S + o.val M.m22 * e₂₂ S ∧
    (mulMat M S).neg = (M.neg != neg S)

private theorem det_small (a b c d e f g h : Int) :
    (a * e + b * g) * (c * f + d * h) - (a * f + b * h) * (c * e + d * g) =
      (a * d - b * c) * (e * h - f * g) := by
  grind

private theorem unimodular_mulMat (B : o.SmallSteps) (M : Mat2 α) (S : B.W) (hM : o.Unimodular M)
    (hS : B.ok S) : o.Unimodular (B.mulMat M S) := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, hn⟩ := B.mulMat_spec M S hS
  obtain ⟨hp, hq⟩ := B.det_of_ok S hS
  unfold Unimodular at *
  rw [h₁₁, h₁₂, h₂₁, h₂₂, hn]
  push_cast
  rw [det_small, hM]
  have hS' : (B.e₁₁ S * B.e₂₂ S - B.e₁₂ S * B.e₂₁ S : Int) = if B.neg S then -1 else 1 := by
    cases hs : B.neg S
    · have := congrArg (fun n : Nat => (n : Int)) (hp hs)
      push_cast at this; simp; lia
    · have := congrArg (fun n : Nat => (n : Int)) (hq hs)
      push_cast at this; simp; lia
  rw [hS']
  rcases Bool.eq_false_or_eq_true M.neg with h | h <;>
    rcases Bool.eq_false_or_eq_true (B.neg S) with h' | h' <;> simp [h, h']

private theorem fwd_mulMat (B : o.SmallSteps) (M : Mat2 α) (S : B.W) (hS : B.ok S)
    (a₀ b₀ a b x y : α) (hF : o.Fwd M a₀ b₀ a b)
    (ha : o.val a = B.e₁₁ S * o.val x + B.e₁₂ S * o.val y)
    (hb : o.val b = B.e₂₁ S * o.val x + B.e₂₂ S * o.val y) :
    o.Fwd (B.mulMat M S) a₀ b₀ x y := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, -⟩ := B.mulMat_spec M S hS
  unfold Fwd at *
  rw [h₁₁, h₁₂, h₂₁, h₂₂, hF.1, hF.2, ha, hb]
  constructor <;> grind

/--
Steps of `B` while `b ≥ Bˢ` and they make the numbers smaller, at most `fuel` of them, with the
product of their matrices (`mulMat`).
-/
public def smallLoop (B : o.SmallSteps) (s : Nat) (a b : α) (M : Mat2 α) :
    Nat → Mat2 α × α × α
  | 0 => (M, a, b)
  | fuel + 1 =>
    if B.geB b s then
      match B.step a b with
      | none => (M, a, b)
      | some r =>
        if o.le r.2.2 r.2.1 ∧ !(o.le b r.2.2) then
          smallLoop B s r.2.1 r.2.2 (B.mulMat M r.1) fuel
        else (M, a, b)
    else (M, a, b)

private theorem smallLoop_ok (B : o.SmallSteps) (s : Nat) (a₀ b₀ : α) :
    ∀ fuel (a b : α) (M : Mat2 α), o.Unimodular M → o.Fwd M a₀ b₀ a b →
      o.HgcdOK a₀ b₀ (o.smallLoop B s a b M fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a b M hM hF; exact ⟨hM, hF⟩
  | succ fuel ih =>
    intro a b M hM hF
    simp only [smallLoop]
    split
    · split
      · exact ⟨hM, hF⟩
      · rename_i r hr
        obtain ⟨hS, ha, hb⟩ := B.step_spec a b r hr
        split
        · exact ih _ _ _ (o.unimodular_mulMat B M r.1 hM hS)
            (o.fwd_mulMat B M r.1 hS a₀ b₀ a b _ _ hF ha hb)
        · exact ⟨hM, hF⟩
    · exact ⟨hM, hF⟩

/-- `smallLoop` from the identity matrix, as a base case for `hgcd`. -/
public def smallBase (B : o.SmallSteps) (s : Nat) (a b : α) : Mat2 α × α × α :=
  o.smallLoop B s a b o.matId (4 * o.size a + 4)

public theorem smallBase_ok (B : o.SmallSteps) (s : Nat) (a b : α) :
    o.HgcdOK a b (o.smallBase B s a b) :=
  o.smallLoop_ok B s a b _ a b o.matId o.unimodular_matId (o.fwd_matId a b)

/--
Half-gcd: the matrix of Euclid's steps that brings `a ≥ b`, of `n` limbs, below `Bˢ` with
`s = ⌊n / 2⌋ + 1`, or close to it, and the numbers it brings them to. Up to `T` limbs by the
instance's `base s a b` (`stepBase`, for one); above, the matrix and numbers of the top `n - s`
limbs, recursively, extended to `a` and `b` with products by their low `s` limbs (`applySplit`),
then one step of Euclid's algorithm, then the same for the top limbs of what is left. A matrix
from top limbs that went too far for the full numbers is dropped. Only the determinant and the
exact relation are proved (`hgcd_ok`): the caller checks how far the numbers came down.
-/
public def hgcd (base : Nat → α → α → Mat2 α × α × α) (T : Nat) (a b : α) :
    Mat2 α × α × α :=
  let n := o.size a
  let s := n / 2 + 1
  if !(o.le (o.pow s) b) then (o.matId, a, b)
  else if n ≤ T then base s a b
  else
    let R₁ := hgcd base T (o.hi s a) (o.hi s b)
    match o.applySplit R₁.1 R₁.2.1 R₁.2.2 a b s with
    | none => (o.matId, a, b)
    | some p =>
      let r := o.orient R₁.1 p
      if !(o.le (o.pow s) r.2.2) then r
      else
        -- One step of Euclid's algorithm, then the top limbs of what is left.
        let qr := o.divRem r.2.1 r.2.2
        let M₃ := o.matMul r.1 (o.matStep qr.1)
        let m := o.size r.2.2
        if _h : n < m then (M₃, r.2.2, qr.2)
        else
          let R₂ := hgcd base T (o.hi (2 * s - m) r.2.2) (o.hi (2 * s - m) qr.2)
          match o.applySplit R₂.1 R₂.2.1 R₂.2.2 r.2.2 qr.2 (2 * s - m) with
          | none => (M₃, r.2.2, qr.2)
          | some p₂ =>
            let r₂ := o.orient R₂.1 p₂
            (o.matMul M₃ r₂.1, r₂.2)
termination_by o.size a
decreasing_by
  all_goals rw [o.size_hi]; lia

public theorem hgcd_ok (base : Nat → α → α → Mat2 α × α × α)
    (hbase : ∀ s a b, o.HgcdOK a b (base s a b)) (T : Nat) (a b : α) :
    o.HgcdOK a b (o.hgcd base T a b) := by
  induction hn : o.size a using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    unfold hgcd
    dsimp only
    split
    · exact ⟨o.unimodular_matId, o.fwd_matId a b⟩
    split
    · exact hbase _ a b
    rename_i hT
    have hR₁ := ih (o.size (o.hi (o.size a / 2 + 1) a)) (by rw [o.size_hi]; lia)
      (o.hi (o.size a / 2 + 1) a) (o.hi (o.size a / 2 + 1) b) rfl
    split
    · exact ⟨o.unimodular_matId, o.fwd_matId a b⟩
    rename_i p hp
    have hF₁ := o.fwd_applySplit _ hR₁.1 _ _ a b _ hR₁.2 p hp
    have hM₂ := o.unimodular_orient _ hR₁.1 p
    have hF₂ := o.fwd_orient _ a b p hF₁
    generalize o.orient (o.hgcd base T (o.hi (o.size a / 2 + 1) a)
      (o.hi (o.size a / 2 + 1) b)).1 p = r at hM₂ hF₂
    split
    · exact ⟨hM₂, hF₂⟩
    rename_i hb₁
    -- After the step of Euclid's algorithm, with `b₁ ≥ Bˢ > 0`.
    have hd : 0 < o.val r.2.2 := by
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hb₁
      have := (o.le_iff _ _).1 hb₁
      rw [o.val_pow] at this
      have := Nat.pow_pos (n := o.size a / 2 + 1) (Nat.lt_trans Nat.zero_lt_one o.one_lt_B)
      lia
    have hF₃ : o.Fwd (o.matMul r.1 (o.matStep (o.divRem r.2.1 r.2.2).1)) a b r.2.2
        (o.divRem r.2.1 r.2.2).2 := by
      apply o.fwd_matMul _ _ a b r.2.1 r.2.2 _ _ hF₂
      obtain ⟨hq, hr⟩ := o.val_divRem r.2.1 r.2.2 (by lia)
      refine ⟨?_, ?_⟩
      · simp only [matStep, val_one, hq, hr]
        rw [Nat.mul_comm (o.val r.2.1 / o.val r.2.2), Nat.one_mul]
        exact (Nat.div_add_mod _ _).symm
      · simp [matStep, val_one, val_zero]
    have hM₃ := o.unimodular_matMul _ _ hM₂ (o.unimodular_matStep (o.divRem r.2.1 r.2.2).1)
    split
    · exact ⟨hM₃, hF₃⟩
    rename_i hm
    have hR₂ := ih _ (by rw [o.size_hi]; lia)
      (o.hi (2 * (o.size a / 2 + 1) - o.size r.2.2) r.2.2)
      (o.hi (2 * (o.size a / 2 + 1) - o.size r.2.2) (o.divRem r.2.1 r.2.2).2) rfl
    split
    · exact ⟨hM₃, hF₃⟩
    rename_i p₂ hp₂
    have hF₄ := o.fwd_applySplit _ hR₂.1 _ _ _ _ _ hR₂.2 p₂ hp₂
    exact ⟨o.unimodular_matMul _ _ hM₃ (o.unimodular_orient _ hR₂.1 p₂),
      o.fwd_matMul _ _ a b _ _ _ _ hF₃ (o.fwd_orient _ _ _ p₂ hF₄)⟩

/--
One reduction of `a ≥ b` for the greatest common divisor: the numbers of `hgcd`, the larger first.
It keeps the greatest common divisor (`gcd_hgcdReduce`); the caller checks that they got smaller.
-/
public def hgcdReduce (base : Nat → α → α → Mat2 α × α × α) (T : Nat) (a b : α) : α × α :=
  let p := (o.hgcd base T a b).2
  if o.le p.2 p.1 then p else (p.2, p.1)

public theorem gcd_hgcdReduce (base : Nat → α → α → Mat2 α × α × α)
    (hbase : ∀ s a b, o.HgcdOK a b (base s a b)) (T : Nat) (a b : α) :
    Nat.gcd (o.val (o.hgcdReduce base T a b).1) (o.val (o.hgcdReduce base T a b).2) =
      Nat.gcd (o.val a) (o.val b) := by
  obtain ⟨hM, hF⟩ := o.hgcd_ok base hbase T a b
  have h := (o.gcd_of_fwd _ hM a b _ _ hF).symm
  unfold hgcdReduce
  dsimp only
  split
  · exact h
  · rw [Nat.gcd_comm]; exact h

end NatOps

end MPN
