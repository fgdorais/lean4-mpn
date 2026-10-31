/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.LinComb
public import MPN.WordGcd
public import MPN.Generic.HGCD

/-!
# Lehmer's step on arrays of limbs

The cofactors of a run of Euclid's steps on the leading words of two numbers `a ≥ b` give a matrix
of words `S = [[|D|, |B|], [|C|, |A|]]` and the numbers `x = |A a + B b|` and `y = |C a + D b|`,
each in one pass (`LinComb.mulSubMul`), with `(a, b) = S (x, y)` (`applyW`). Only words are
checked: the instance turns the cofactors into a matrix whose entries are below `2ᶜ` and whose
determinant is `±1` (`wmat`), and both differences must be nonnegative, which makes the relation
exact; nothing about the cofactors needs a proof.

`stepW` is such a step from the instance's cofactors, `lehmerStep` its two numbers, which have the
same greatest common divisor as `a` and `b`, and `mulMatW` the product of a matrix of numbers by a
matrix of words (`LinComb.mulAddMul`). `smallSteps` makes of them the base case of half-gcd
(`NatOps.SmallSteps`) for any representation that converts to and from the arrays.
-/

namespace MPN

/-- A `2 × 2` matrix of limbs, and the sign of its determinant. -/
public structure WMat (L : Type) where
  s11 : L
  s12 : L
  s21 : L
  s22 : L
  neg : Bool

namespace LehmerStep

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]
  [C : LinCombOps A L]

/-- The value of an array. -/
@[expose] public def vA (a : A) : Nat := LimbArray.valAt a 0 (LA.size a)

variable (A) in
/-- `S` has entries below `2ᶜ` and determinant `±1`, with the sign of `S.neg`. -/
@[expose] public def OK (S : WMat L) : Prop :=
  LA.val S.s11 < 2 ^ C.cb ∧ LA.val S.s12 < 2 ^ C.cb ∧ LA.val S.s21 < 2 ^ C.cb ∧
    LA.val S.s22 < 2 ^ C.cb ∧
    (S.neg = false → LA.val S.s11 * LA.val S.s22 = LA.val S.s12 * LA.val S.s21 + 1) ∧
    (S.neg = true → LA.val S.s12 * LA.val S.s21 = LA.val S.s11 * LA.val S.s22 + 1)

end LehmerStep

open LehmerStep in
/--
The parts of Lehmer's step that depend on the limbs: trimming, the matrix of the cofactors of a run
of Euclid's steps, checked on words (`wmat`), and where the cofactors come from: `cof₁`, and
`cof₂` when `two` and those of `cof₁` do not apply. The cofactors only affect speed.
-/
public class LehmerOps (A : Type) (L : outParam Type) [LA : LimbArray A L] [R : WordArray A L]
    [C : LinCombOps A L] where
  /-- `a` without its zero limbs on top. -/
  trim : A → A
  vA_trim : ∀ a, vA (trim a) = vA a
  /-- Whether an array is trimmed. -/
  trimmed : A → Bool
  trimmed_trim : ∀ a, trimmed (trim a) = true
  /-- The matrix `[[|D|, |B|], [|C|, |A|]]` of the cofactors `A`, `B`, `C`, `D`, when it is `OK`. -/
  wmat : Cofactors → Option (WMat L)
  ok_wmat : ∀ m S, wmat m = some S → OK A S
  /-- The cofactors of `a ≥ b`, first and second. -/
  cof₁ : A → A → Cofactors
  cof₂ : A → A → Cofactors
  two : Bool

namespace LehmerStep

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]
  [C : LinCombOps A L] [O : LehmerOps A L]

omit O in
private theorem vA_mulSubMul (x y : A) (a b : L) (ha : LA.val a < 2 ^ C.cb)
    (hb : LA.val b < 2 ^ C.cb) (h : (LinComb.mulSubMul x y a b).2 = false) :
    vA (LinComb.mulSubMul x y a b).1 + LA.val b * vA y = LA.val a * vA x := by
  obtain ⟨s₁, s₂, -⟩ := LinComb.mulSubMul_spec x y a b ha hb
  unfold vA
  rw [s₁]
  exact s₂ h

omit O in
private theorem vA_mulAddMul (x y : A) (a b : L) (ha : LA.val a < 2 ^ C.cb)
    (hb : LA.val b < 2 ^ C.cb) :
    vA (LinComb.mulAddMul x y a b) = LA.val a * vA x + LA.val b * vA y := by
  obtain ⟨s₁, s₂⟩ := LinComb.mulAddMul_spec x y a b ha hb
  unfold vA
  rw [s₁]
  exact s₂

/--
`S⁻¹ (a, b)` when its entries are nonnegative, by `mulSubMul` in one pass each, trimmed: the
numbers `(x, y)` with `(a, b) = S (x, y)`.
-/
@[expose, specialize] public def applyW (S : WMat L) (a b : A) : Option (A × A) :=
  let x := if !S.neg then LinComb.mulSubMul a b S.s22 S.s12 else LinComb.mulSubMul b a S.s12 S.s22
  let y := if !S.neg then LinComb.mulSubMul b a S.s11 S.s21 else LinComb.mulSubMul a b S.s21 S.s11
  if x.2 || y.2 then none else some (O.trim x.1, O.trim y.1)

private theorem fwd_pos (p q r s a b X Y : Nat) (hd : p * s = q * r + 1)
    (hX : X + q * b = s * a) (hY : Y + r * a = p * b) :
    a = p * X + q * Y ∧ b = r * X + s * Y := by
  constructor <;> grind

private theorem fwd_neg (p q r s a b X Y : Nat) (hd : q * r = p * s + 1)
    (hX : X + s * a = q * b) (hY : Y + p * b = r * a) :
    a = p * X + q * Y ∧ b = r * X + s * Y := by
  constructor <;> grind

private theorem fwd_applyW (S : WMat L) (hS : OK A S) (a b : A) (p : A × A)
    (h : applyW S a b = some p) :
    vA a = LA.val S.s11 * vA p.1 + LA.val S.s12 * vA p.2 ∧
      vA b = LA.val S.s21 * vA p.1 + LA.val S.s22 * vA p.2 := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, hp, hn⟩ := hS
  unfold applyW at h
  cases hs : S.neg <;>
    simp only [hs, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] at h <;>
    split at h <;> (try (cases h; done)) <;> rename_i hc <;>
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc <;>
    rw [Option.some.injEq] at h <;> subst h <;> dsimp only <;> rw [O.vA_trim, O.vA_trim]
  · exact fwd_pos _ _ _ _ _ _ _ _ (hp hs) (vA_mulSubMul _ _ _ _ h₂₂ h₁₂ hc.1)
      (vA_mulSubMul _ _ _ _ h₁₁ h₂₁ hc.2)
  · exact fwd_neg _ _ _ _ _ _ _ _ (hn hs) (vA_mulSubMul _ _ _ _ h₁₂ h₂₂ hc.1)
      (vA_mulSubMul _ _ _ _ h₂₁ h₁₁ hc.2)

private theorem trimmed_applyW (S : WMat L) (a b : A) (p : A × A) (h : applyW S a b = some p) :
    O.trimmed p.1 = true ∧ O.trimmed p.2 = true := by
  unfold applyW at h
  cases hs : S.neg <;>
    simp only [hs, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] at h <;>
    split at h <;> (try (cases h; done)) <;>
    rw [Option.some.injEq] at h <;> subst h <;> exact ⟨O.trimmed_trim _, O.trimmed_trim _⟩

/-- The matrix of the cofactors `m` and the numbers it takes to `a` and `b`, when it is valid. -/
@[expose, specialize] public def tryCof (a b : A) (m : Cofactors) : Option (WMat L × A × A) :=
  match O.wmat m with
  | some S =>
    match applyW S a b with
    | some p => some (S, p)
    | none => none
  | none => none

/-- A step of Lehmer's algorithm on `a ≥ b`, with its matrix, from the instance's cofactors. -/
@[expose, specialize] public def stepW (a b : A) : Option (WMat L × A × A) :=
  match tryCof a b (O.cof₁ a b) with
  | some r => some r
  | none => if O.two then tryCof a b (O.cof₂ a b) else none

public theorem stepW_spec (a b : A) (r : WMat L × A × A) (h : stepW a b = some r) :
    OK A r.1 ∧ vA a = LA.val r.1.s11 * vA r.2.1 + LA.val r.1.s12 * vA r.2.2 ∧
      vA b = LA.val r.1.s21 * vA r.2.1 + LA.val r.1.s22 * vA r.2.2 ∧
      O.trimmed r.2.1 = true ∧ O.trimmed r.2.2 = true := by
  have hc : ∀ m r, tryCof a b m = some r → OK A r.1 ∧
      vA a = LA.val r.1.s11 * vA r.2.1 + LA.val r.1.s12 * vA r.2.2 ∧
      vA b = LA.val r.1.s21 * vA r.2.1 + LA.val r.1.s22 * vA r.2.2 ∧
      O.trimmed r.2.1 = true ∧ O.trimmed r.2.2 = true := by
    intro m r h
    unfold tryCof at h
    split at h
    · rename_i S hS
      split at h
      · rename_i p hp
        rw [Option.some.injEq] at h
        subst h
        have hok := O.ok_wmat m S hS
        obtain ⟨f₁, f₂⟩ := fwd_applyW S hok a b p hp
        obtain ⟨t₁, t₂⟩ := trimmed_applyW S a b p hp
        exact ⟨hok, f₁, f₂, t₁, t₂⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  unfold stepW at h
  split at h
  · rename_i q hq
    rw [Option.some.injEq] at h
    subst h
    exact hc _ _ hq
  · split at h
    · exact hc _ _ h
    · exact absurd h (by simp)

/-- Lehmer's step on `a ≥ b`: two trimmed numbers with the same greatest common divisor, or none. -/
@[expose, specialize] public def lehmerStep (a b : A) : Option (A × A) :=
  match stepW a b with
  | some r => some r.2
  | none => none

public theorem lehmerStep_spec (a b : A) (p : A × A) (h : lehmerStep a b = some p) :
    Nat.gcd (vA p.1) (vA p.2) = Nat.gcd (vA a) (vA b) ∧ O.trimmed p.1 = true ∧
      O.trimmed p.2 = true := by
  unfold lehmerStep at h
  split at h
  · rename_i r hr
    rw [Option.some.injEq] at h
    subst h
    obtain ⟨⟨-, -, -, -, hp, hn⟩, ha, hb, t₁, t₂⟩ := stepW_spec a b r hr
    refine ⟨?_, t₁, t₂⟩
    have g := NatOps.gcd_unimodular (vA r.2.1) (vA r.2.2) (LA.val r.1.s11) (LA.val r.1.s12)
      (LA.val r.1.s21) (LA.val r.1.s22) (by
        cases hs : r.1.neg
        · have := congrArg (fun n : Nat => (n : Int)) (hp hs)
          push_cast at this; left; lia
        · have := congrArg (fun n : Nat => (n : Int)) (hn hs)
          push_cast at this; right; lia)
    rw [← g, ha, hb]
    push_cast
    rfl
  · exact absurd h (by simp)

/-- `M S`, by `mulAddMul`, trimmed. -/
@[expose, specialize] public def mulMatW (M : Mat2 A) (S : WMat L) : Mat2 A :=
  ⟨O.trim (LinComb.mulAddMul M.m11 M.m12 S.s11 S.s21),
    O.trim (LinComb.mulAddMul M.m11 M.m12 S.s12 S.s22),
    O.trim (LinComb.mulAddMul M.m21 M.m22 S.s11 S.s21),
    O.trim (LinComb.mulAddMul M.m21 M.m22 S.s12 S.s22), M.neg != S.neg⟩

public theorem mulMatW_spec (M : Mat2 A) (S : WMat L) (hS : OK A S) :
    vA (mulMatW M S).m11 = vA M.m11 * LA.val S.s11 + vA M.m12 * LA.val S.s21 ∧
      vA (mulMatW M S).m12 = vA M.m11 * LA.val S.s12 + vA M.m12 * LA.val S.s22 ∧
      vA (mulMatW M S).m21 = vA M.m21 * LA.val S.s11 + vA M.m22 * LA.val S.s21 ∧
      vA (mulMatW M S).m22 = vA M.m21 * LA.val S.s12 + vA M.m22 * LA.val S.s22 ∧
      (mulMatW M S).neg = (M.neg != S.neg) := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, -, -⟩ := hS
  simp only [mulMatW, O.vA_trim]
  rw [vA_mulAddMul _ _ _ _ h₁₁ h₂₁, vA_mulAddMul _ _ _ _ h₁₂ h₂₂,
    vA_mulAddMul _ _ _ _ h₁₁ h₂₁, vA_mulAddMul _ _ _ _ h₁₂ h₂₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Nat.mul_comm]

/--
Half-gcd's base case of word matrices, for `NatOps.smallBase` on a representation `α` of numbers
that converts to the arrays (`toA`) and back (`ofA`): Lehmer's steps (`stepW`) and the matrix
updated by `mulAddMul` (`mulMatW`). `geB b s` is whether `b ≥ Bˢ`, which only affects speed.
-/
@[expose, specialize] public def smallSteps {α : Type} (o : NatOps α) (toA : α → A) (ofA : A → α)
    (hto : ∀ x, vA (toA x) = o.val x) (hof : ∀ a, o.val (ofA a) = vA a)
    (geB : α → Nat → Bool) : o.SmallSteps where
  W := WMat L
  e₁₁ S := LA.val S.s11
  e₁₂ S := LA.val S.s12
  e₂₁ S := LA.val S.s21
  e₂₂ S := LA.val S.s22
  neg S := S.neg
  ok S := OK A S
  step a b :=
    match stepW (toA a) (toA b) with
    | some r => some (r.1, ofA r.2.1, ofA r.2.2)
    | none => none
  mulMat M S :=
    let N := mulMatW (A := A) ⟨toA M.m11, toA M.m12, toA M.m21, toA M.m22, M.neg⟩ S
    ⟨ofA N.m11, ofA N.m12, ofA N.m21, ofA N.m22, N.neg⟩
  geB := geB
  det_of_ok _ h := ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  step_spec a b r h := by
    split at h
    · rename_i q hq
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨h₁, h₂, h₃, -, -⟩ := stepW_spec _ _ q hq
      rw [hto] at h₂ h₃
      exact ⟨h₁, by rw [hof, hof]; exact h₂, by rw [hof, hof]; exact h₃⟩
    · exact absurd h (by simp)
  mulMat_spec M S h := by
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := mulMatW_spec (A := A)
      ⟨toA M.m11, toA M.m12, toA M.m21, toA M.m22, M.neg⟩ S h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hof, e₁, e₂, e₃, e₄, e₅, hto]

end LehmerStep

end MPN
