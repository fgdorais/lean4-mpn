/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Natural
public import MPN.LehmerStep
public import MPN.Generic.Sqrt
public import MPN.Generic.HGCD

/-!
# From `GNat` to `NatOps` and back

A width runs the base-generic algorithms of `MPN.Generic` on an instance `NatOps α` of its own,
and its numbers are `GNat A`. A `Bridge A α` is that instance with the conversions: `toO` from
the limbs of a number to `α`, and `ofO` from `α` back to a number, which trims. Over a bridge:

* `sqrtZ`, the square root by Zimmermann's recursion (`NatOps.sqrtRemAux`, GMP's `mpn_sqrtrem`)
  on `x 4ᶜ` of `2 n` limbs with `β^(2n) ≤ 4 x 4ᶜ`, shifted back by `c` bits, with the base case
  `newtonBase`: a width's own for short numbers, and Newton's iteration (`GNat.sqrtNewton`) above;
* `sqrtRem`, any square root with its remainder;
* `hgcd`, one reduction by half-gcd of the top third of the limbs (`NatOps.hgcdReduceP`);

and `lehmer`, Lehmer's step (`LehmerStep.lehmerStep`) on the limbs of two numbers.
-/

namespace MPN

/-- The instance of `NatOps` of a width and its conversions from and to `GNat A`. -/
public structure Bridge (A : Type) [C : NatLimbs A] (α : Type) where
  /-- The operations of the width. -/
  o : NatOps α
  /-- The bits of a limb. -/
  w : Nat
  B_eq : o.B = 2 ^ w
  one_le_w : 1 ≤ w
  /-- The limbs of a number as an operand. -/
  toO : A → α
  val_toO : ∀ a, o.val (toO a) = C.val a
  /-- A result as a number. -/
  ofO : α → GNat A
  toNat_ofO : ∀ x, (ofO x).toNat = o.val x

namespace Bridge

variable {A : Type} [C : NatLimbs A] {α : Type} (b : Bridge A α)

/-! ## Square root -/

/--
`(⌊√N⌋, N - ⌊√N⌋²)`, the base case of Zimmermann's recursion: by `small` when `useSmall` takes `N`,
and by Newton's iteration otherwise.
-/
@[inline] public def newtonBase (small : α → α × α) (useSmall : α → Bool) (N : α) : α × α :=
  if useSmall N then small N
  else
    let S := b.toO (GNat.sqrtNewton (b.ofO N)).limbs
    (S, b.o.sub N (b.o.sqr S))

public theorem newtonBase_spec (small : α → α × α) (useSmall : α → Bool)
    (hsmall : ∀ N, useSmall N = true →
      b.o.val (small N).1 = _root_.Nat.sqrt (b.o.val N) ∧
        b.o.val (small N).2 = b.o.val N - _root_.Nat.sqrt (b.o.val N) * _root_.Nat.sqrt (b.o.val N))
    (N : α) :
    b.o.val (b.newtonBase small useSmall N).1 = _root_.Nat.sqrt (b.o.val N) ∧
      b.o.val (b.newtonBase small useSmall N).2 =
        b.o.val N - _root_.Nat.sqrt (b.o.val N) * _root_.Nat.sqrt (b.o.val N) := by
  unfold newtonBase
  split
  · rename_i h
    exact hsmall N h
  · have hS : b.o.val (b.toO (GNat.sqrtNewton (b.ofO N)).limbs) = _root_.Nat.sqrt (b.o.val N) := by
      rw [b.val_toO, GNat.val_limbs, GNat.toNat_sqrtNewton, b.toNat_ofO]
    refine ⟨hS, ?_⟩
    dsimp only
    rw [b.o.val_sub _ _ (by rw [b.o.val_sqr, hS]; exact Nat.sqrt_le _), b.o.val_sqr, hS]

/--
`⌊√x⌋` for `x ≠ 0` by Zimmermann's recursion (`NatOps.sqrtRemAux`) on `N = x 4ᶜ` of `2 n` limbs
with `β^(2n) ≤ 4 N`, then `⌊√N⌋ / 2ᶜ`, with `base` for roots of up to `T` limbs.
-/
@[inline] public def sqrtZ (base : α → α × α) (T : Nat) (x : GNat A) : GNat A :=
  let L := GNat.log2 x
  let n := L / (2 * b.w) + 1
  let c := (2 * b.w * n - 1 - L) / 2
  let S := (b.o.sqrtRemAux base T (b.toO (GNat.shiftLeft x (2 * c)).limbs) n).1
  GNat.shiftRight (b.ofO S) c

/-- `N = X 4ᶜ` has at most `2 n` limbs of `w` bits and `β^(2n) ≤ 4 N`, for the `n` and `c` of
`sqrtZ`. -/
private theorem sqrtZ_bounds (w X : Nat) (hw : 1 ≤ w) (hx : X ≠ 0) :
    X * 2 ^ (2 * ((2 * w * (X.log2 / (2 * w) + 1) - 1 - X.log2) / 2)) <
        2 ^ (2 * w * (X.log2 / (2 * w) + 1)) ∧
      2 ^ (2 * w * (X.log2 / (2 * w) + 1)) ≤
        4 * (X * 2 ^ (2 * ((2 * w * (X.log2 / (2 * w) + 1) - 1 - X.log2) / 2))) := by
  have hlo : 2 ^ X.log2 ≤ X := Nat.log2_self_le hx
  have hhi : X < 2 ^ (X.log2 + 1) := Nat.lt_log2_self
  have hM := Nat.lt_mul_div_succ X.log2 (show 0 < 2 * w by lia)
  generalize X.log2 = L at *
  generalize 2 * w * (L / (2 * w) + 1) = M at *
  generalize hc : (M - 1 - L) / 2 = c
  have hc₁ : M - 2 ≤ L + 2 * c := by lia
  have hc₂ : L + 2 * c + 1 ≤ M := by lia
  constructor
  · calc X * 2 ^ (2 * c) < 2 ^ (L + 1) * 2 ^ (2 * c) :=
          Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
      _ = 2 ^ (L + 2 * c + 1) := by rw [← Nat.pow_add]; congr 1; lia
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hc₂
  · calc 2 ^ M ≤ 2 ^ (L + 2 * c + 2) := Nat.pow_le_pow_right (by decide) (by lia)
      _ = 4 * (2 ^ L * 2 ^ (2 * c)) := by
          rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
      _ ≤ 4 * (X * 2 ^ (2 * c)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlo)

public theorem toNat_sqrtZ (base : α → α × α) (T : Nat)
    (hbase : ∀ N n, 1 ≤ n → (n ≤ T ∨ n ≤ 1) → b.o.val N < b.o.B ^ (2 * n) →
      b.o.B ^ (2 * n) ≤ 4 * b.o.val N →
      b.o.val (base N).1 = _root_.Nat.sqrt (b.o.val N) ∧
        b.o.val (base N).2 = b.o.val N - _root_.Nat.sqrt (b.o.val N) * _root_.Nat.sqrt (b.o.val N))
    (x : GNat A) (hx : x.toNat ≠ 0) :
    (b.sqrtZ base T x).toNat = _root_.Nat.sqrt x.toNat := by
  obtain ⟨h₁, h₂⟩ := sqrtZ_bounds b.w x.toNat b.one_le_w hx
  have hB2 : 2 ∣ b.o.B := ⟨2 ^ (b.w - 1), by
    rw [b.B_eq, ← Nat.pow_succ']; congr 1; have := b.one_le_w; lia⟩
  unfold sqrtZ
  dsimp only
  rw [GNat.log2_eq]
  generalize x.toNat.log2 / (2 * b.w) + 1 = n at h₁ h₂ ⊢
  generalize (2 * b.w * n - 1 - x.toNat.log2) / 2 = c at h₁ h₂ ⊢
  have hNv : b.o.val (b.toO (GNat.shiftLeft x (2 * c)).limbs) = x.toNat * 2 ^ (2 * c) := by
    rw [b.val_toO, GNat.val_limbs, GNat.toNat_shiftLeft]
  have hBn : b.o.B ^ (2 * n) = 2 ^ (2 * b.w * n) := by
    rw [b.B_eq, ← Nat.pow_mul]; congr 1; lia
  have hn : 1 ≤ n := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h] at h₁
    have := Nat.le_mul_of_pos_right x.toNat (Nat.two_pow_pos (2 * c))
    simp at h₁; lia
  obtain ⟨i₃, -⟩ := b.o.sqrtRemAux_spec base T hbase hB2 n _ hn
    (by rw [hNv, hBn]; exact h₁) (by rw [hNv, hBn]; exact h₂)
  rw [GNat.toNat_shiftRight, b.toNat_ofO, i₃, hNv, sqrt_mul_four_pow]

/-- `(⌊√x⌋, x - ⌊√x⌋²)` from a square root `sqrt`. -/
@[inline] public def sqrtRem (sqrt : GNat A → GNat A) (x : GNat A) : GNat A × GNat A :=
  let s := sqrt x
  (s, GNat.sub x (GNat.sqr s))

public theorem toNat_sqrtRem (sqrt : GNat A → GNat A)
    (h : ∀ x, (sqrt x).toNat = _root_.Nat.sqrt x.toNat) (x : GNat A) :
    (sqrtRem sqrt x).1.toNat = _root_.Nat.sqrt x.toNat ∧
      (sqrtRem sqrt x).2.toNat = x.toNat - _root_.Nat.sqrt x.toNat * _root_.Nat.sqrt x.toNat := by
  simp [sqrtRem, h]

/-! ## Greatest common divisor -/

/--
One reduction of `x ≥ y` by half-gcd of its top third (`NatOps.hgcdReduceP`) with `base` up to `T`
limbs.
-/
@[inline] public def hgcd (base : Nat → α → α → Mat2 α × α × α) (T : Nat) (x y : GNat A) :
    GNat A × GNat A :=
  let p := b.o.hgcdReduceP base T (b.toO x.limbs) (b.toO y.limbs)
  (b.ofO p.1, b.ofO p.2)

public theorem gcd_hgcd (base : Nat → α → α → Mat2 α × α × α)
    (hbase : ∀ s a b', b.o.HgcdOK a b' (base s a b')) (T : Nat) (x y : GNat A) :
    _root_.Nat.gcd (b.hgcd base T x y).1.toNat (b.hgcd base T x y).2.toNat =
      _root_.Nat.gcd x.toNat y.toNat := by
  simp only [hgcd, b.toNat_ofO]
  rw [b.o.gcd_hgcdReduceP base hbase T, b.val_toO, b.val_toO, GNat.val_limbs, GNat.val_limbs]

end Bridge

/-! ## Lehmer's step -/

section Lehmer

variable {A L : Type} [N : NatLimbs A] [LA : LimbArray A L] [R : WordArray A L]
  [F : WordFolds A L] [C : LinCombOps A L] [O : LehmerOps A L]

/--
Lehmer's step on the limbs of `x ≥ y` (`LehmerStep.lehmerStep`), the results, trimmed as
`LehmerOps` trims, by `ofA`.
-/
@[inline] public def Bridge.lehmer (ofA : (a : A) → O.trimmed a = true → GNat A) (x y : GNat A) :
    Option (GNat A × GNat A) :=
  match h : LehmerStep.lehmerStep x.limbs y.limbs with
  | some p => some (ofA p.1 (LehmerStep.lehmerStep_spec _ _ p h).2.1,
      ofA p.2 (LehmerStep.lehmerStep_spec _ _ p h).2.2)
  | none => none

public theorem Bridge.gcd_lehmer (ofA : (a : A) → O.trimmed a = true → GNat A)
    (hof : ∀ a h, (ofA a h).toNat = LehmerStep.vA a) (hv : ∀ a, LehmerStep.vA a = N.val a)
    (x y : GNat A) (p : GNat A × GNat A) (h : Bridge.lehmer ofA x y = some p) :
    _root_.Nat.gcd p.1.toNat p.2.toNat = _root_.Nat.gcd x.toNat y.toNat := by
  unfold Bridge.lehmer at h
  split at h
  · rename_i q hq
    rw [Option.some.injEq] at h
    subst h
    have e := (LehmerStep.lehmerStep_spec _ _ q hq).1
    rw [hv x.limbs, hv y.limbs, GNat.val_limbs, GNat.val_limbs] at e
    simp only [hof]
    exact e
  · exact absurd h (by simp)

end Lehmer

end MPN
