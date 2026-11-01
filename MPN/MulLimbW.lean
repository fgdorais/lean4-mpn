/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordArray

/-!
# Products by a limb, for limbs of any width

`mul1W`, `addMul1W` and `subMul1W` are GMP's `mpn_mul_1`, `mpn_addmul_1` and `mpn_submul_1` on
windows: the `n` limbs of `a` from `ao` times the limb `x`, written into, added to or subtracted
from the limbs of `r` from `ro`, with the carry or borrow out. Each is one in-place fold over the
window of `r` (`foldThen`), whose step reads `a` by `uget` and is a field of the instance:
`mulAdd2`, the double limb `y x + z + c`, or `subMulB`, with its borrow in the instance's form.
`r` and `a` are different arrays, since a second reference to `r` would copy it.

`foldUInPlace_spec1` is the value of such a fold for any step with a linear law.
-/

namespace MPN.WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/--
The value of a fold over a window of `arr` whose step reads limb `ao + j` of `a`, for a step `f`
with a linear law in the limb `z` of `arr` it replaces and the limb of `a`, like
`foldUInPlace2_spec`: `P` and `Q` are the values of the accumulator going out and coming in.
-/
public theorem foldUInPlace_spec1 {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (a : A) (ao : USize) (P Q : β → Nat) (uz ua vz va : Nat) (I : β → Prop)
    (inv : ∀ j h z c, I c → I (f j h z c).2)
    (law : ∀ j h z c, I c → LA.val (f j h z c).1 + 2 ^ LA.w * P (f j h z c).2 +
      uz * LA.val z + ua * LA.val (LA.get a (ao.toNat + j.toNat)) + Q c =
        vz * LA.val z + va * LA.val (LA.get a (ao.toNat + j.toNat)) + 2 ^ LA.w * Q (f j h z c).2 +
          P c)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) (hb : I b) :
    LA.size (foldUInPlace n f arr rs hr j b).1 = LA.size arr ∧
      I (foldUInPlace n f arr rs hr j b).2 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n f arr rs hr j b).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace n f arr rs hr j b).1 (rs.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * P (foldUInPlace n f arr rs hr j b).2 +
        uz * LimbArray.valAt arr (rs.toNat + j.toNat) (n.toNat - j.toNat) +
        ua * LimbArray.valAt a (ao.toNat + j.toNat) (n.toNat - j.toNat) + Q b =
      vz * LimbArray.valAt arr (rs.toNat + j.toNat) (n.toNat - j.toNat) +
        va * LimbArray.valAt a (ao.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * Q (foldUInPlace n f arr rs hr j b).2 + P b := by
  induction arr, hr, j, b using foldUInPlace.induct (R := R) n f rs with
  | case1 arr hr j b h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hI := inv j h (R.uget arr (rs + j) (hr.uset_bound h)) b hb
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    obtain ⟨ih₁, ih₀, ih₂, ih₃⟩ := ih hI
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv : LA.get (foldUInPlace n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs
        (hr.of_uset ..) (j + 1) p.2).1 (rs.toNat + j.toNat) = p.1 := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hri]
    have hZ : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hz' : R.uget arr (rs + j) (hr.uset_bound h) = LA.get arr (rs.toNat + j.toNat) := by
      rw [R.uget_eq, hri]
    refine ⟨ih₁, ih₀, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hri]
      split <;> lia
    · rw [hZ] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      have hl := law j h (R.uget arr (rs + j) (hr.uset_bound h)) b hb
      rw [hz'] at hl
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, Nat.mul_succ,
        Nat.pow_add]
      show _ + _ * P (foldUInPlace n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs
        (hr.of_uset ..) (j + 1) p.2).2 + _ + _ + _ = _
      generalize (foldUInPlace n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs
        (hr.of_uset ..) (j + 1) p.2) = q at *
      simp only [p, hz'] at *
      generalize f j h (LA.get arr (rs.toNat + j.toNat)) b = p' at *
      generalize LimbArray.valAt q.1 _ _ = V at *
      generalize LimbArray.valAt arr (rs.toNat + j.toNat + 1) k = Z at *
      generalize LimbArray.valAt a (ao.toNat + j.toNat + 1) k = X at *
      generalize LA.val (LA.get arr (rs.toNat + j.toNat)) = z at *
      generalize LA.val (LA.get a (ao.toNat + j.toNat)) = x at *
      generalize 2 ^ (LA.w * k) = B at *
      generalize 2 ^ LA.w = W at *
      grind
  | case2 arr hr j b h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this, hb, Nat.add_comm]

private theorem uget_get (a : A) (ao n : USize) (ha : LoopBound a ao n) (j : USize) (h : j < n) :
    R.uget a (ao + j) (ha.uset_bound h) = LA.get a (ao.toNat + j.toNat) := by
  rw [R.uget_eq, ha.toNat_add h]

variable [F : WordFolds A L]

variable (A) in
/-- The step of `mul1W`: limb `ao + j` of `a` times `x`, plus the carry `c`. -/
@[inline, expose] public def mul1Step (a : A) (ao n : USize) (ha : LoopBound a ao n) (x : L)
    (j : USize) (h : j < n) (_z c : L) : L × L :=
  R.mulAdd2 (R.uget a (ao + j) (ha.uset_bound h)) x R.zero c

variable (A) in
/-- The step of `addMul1W`: the limb `z`, plus limb `ao + j` of `a` times `x`, plus the carry. -/
@[inline, expose] public def addMul1Step (a : A) (ao n : USize) (ha : LoopBound a ao n) (x : L)
    (j : USize) (h : j < n) (z c : L) : L × L :=
  R.mulAdd2 (R.uget a (ao + j) (ha.uset_bound h)) x z c

variable (A) in
/-- The step of `subMul1W`: the limb `z`, minus limb `ao + j` of `a` times `x`, minus the borrow. -/
@[inline, expose] public def subMul1Step (a : A) (ao n : USize) (ha : LoopBound a ao n) (x : L)
    (j : USize) (h : j < n) (z c : L) : L × L :=
  R.subMulB z (R.uget a (ao + j) (ha.uset_bound h)) x c

/-- The low limbs of `a x + c`, into the window of `r`, and the high limb, like `mpn_mul_1`. -/
@[inline, expose, specialize] public def mul1W (r : A) (ro : USize) (a : A) (ao n : USize) (x c : L)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) : A × L :=
  F.foldThen n (mul1Step A a ao n ha x) r ro hr 0 c fun arr _ c => (arr, c)

/-- `r + a x + c`, in the window of `r`, and the carry out, like `mpn_addmul_1`. -/
@[inline, expose, specialize] public def addMul1W (r : A) (ro : USize) (a : A) (ao n : USize)
    (x c : L) (hr : LoopBound r ro n) (ha : LoopBound a ao n) : A × L :=
  F.foldThen n (addMul1Step A a ao n ha x) r ro hr 0 c fun arr _ c => (arr, c)

/--
`r - a x - unB b`, in the window of `r`, and the borrow out in the instance's form, like
`mpn_submul_1`; `R.b0` is the borrow `0`.
-/
@[inline, expose, specialize] public def subMul1W (r : A) (ro : USize) (a : A) (ao n : USize)
    (x b : L) (hr : LoopBound r ro n) (ha : LoopBound a ao n) : A × L :=
  F.foldThen n (subMul1Step A a ao n ha x) r ro hr 0 b fun arr _ c => (arr, c)

public theorem mul1W_spec (r : A) (ro : USize) (a : A) (ao n : USize) (x c : L)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) :
    LA.size (mul1W r ro a ao n x c hr ha).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (mul1W r ro a ao n x c hr ha).1 i = LA.get r i) ∧
      LimbArray.valAt (mul1W r ro a ao n x c hr ha).1 ro.toNat n.toNat +
          2 ^ (LA.w * n.toNat) * LA.val (mul1W r ro a ao n x c hr ha).2 =
        LimbArray.valAt a ao.toNat n.toNat * LA.val x + LA.val c := by
  rw [mul1W, F.foldThen_eq, foldUInPlaceThen]
  obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 n (mul1Step A a ao n ha x) a ao LA.val (fun _ => 0)
    0 0 0 (LA.val x) (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun j h z c _ => by
      have := R.val_mulAdd2 (R.uget a (ao + j) (ha.uset_bound h)) x R.zero c
      rw [congrArg LA.val (uget_get a ao n ha j h), R.val_zero] at this
      simp only [mul1Step]
      lia) r ro hr 0 c trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.zero_mul, Nat.mul_zero,
    Nat.add_zero, Nat.zero_add] at i₂ i₃
  refine ⟨i₁, fun i hi => i₂ i hi, ?_⟩
  rw [i₃, Nat.mul_comm]

public theorem addMul1W_spec (r : A) (ro : USize) (a : A) (ao n : USize) (x c : L)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) :
    LA.size (addMul1W r ro a ao n x c hr ha).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (addMul1W r ro a ao n x c hr ha).1 i = LA.get r i) ∧
      LimbArray.valAt (addMul1W r ro a ao n x c hr ha).1 ro.toNat n.toNat +
          2 ^ (LA.w * n.toNat) * LA.val (addMul1W r ro a ao n x c hr ha).2 =
        LimbArray.valAt r ro.toNat n.toNat +
          LimbArray.valAt a ao.toNat n.toNat * LA.val x + LA.val c := by
  rw [addMul1W, F.foldThen_eq, foldUInPlaceThen]
  obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 n (addMul1Step A a ao n ha x) a ao LA.val
    (fun _ => 0) 0 0 1 (LA.val x) (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun j h z c _ => by
      have := R.val_mulAdd2 (R.uget a (ao + j) (ha.uset_bound h)) x z c
      rw [congrArg LA.val (uget_get a ao n ha j h)] at this
      simp only [addMul1Step]
      lia) r ro hr 0 c trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.zero_mul, Nat.mul_zero,
    Nat.add_zero, Nat.one_mul] at i₂ i₃
  refine ⟨i₁, fun i hi => i₂ i hi, ?_⟩
  rw [i₃, Nat.mul_comm (LA.val x)]

public theorem subMul1W_spec (r : A) (ro : USize) (a : A) (ao n : USize) (x b : L)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) :
    LA.size (subMul1W r ro a ao n x b hr ha).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (subMul1W r ro a ao n x b hr ha).1 i = LA.get r i) ∧
      LimbArray.valAt (subMul1W r ro a ao n x b hr ha).1 ro.toNat n.toNat +
          LimbArray.valAt a ao.toNat n.toNat * LA.val x + LA.val (R.unB b) =
        LimbArray.valAt r ro.toNat n.toNat +
          2 ^ (LA.w * n.toNat) * LA.val (R.unB (subMul1W r ro a ao n x b hr ha).2) := by
  rw [subMul1W, F.foldThen_eq, foldUInPlaceThen]
  obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 n (subMul1Step A a ao n ha x) a ao (fun _ => 0)
    (fun c => LA.val (R.unB c)) 0 (LA.val x) 1 0 (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun j h z c _ => by
      have := R.val_subMulB z (R.uget a (ao + j) (ha.uset_bound h)) x c
      rw [congrArg LA.val (uget_get a ao n ha j h)] at this
      simp only [subMul1Step]
      lia) r ro hr 0 b trivial
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.zero_mul, Nat.mul_zero,
    Nat.add_zero, Nat.one_mul] at i₂ i₃
  refine ⟨i₁, fun i hi => i₂ i hi, ?_⟩
  rw [Nat.mul_comm _ (LA.val x)]
  lia

end MPN.WordArray
