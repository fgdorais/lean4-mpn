/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Add
public import Bignum.Mul.Limb

/-!
# Schoolbook squaring

`sqrBasecase a` is the schoolbook square, after GMP's `mpn_sqr_basecase`. Squaring needs each
product `aᵢ aⱼ` with `i ≠ j` only once, since it appears twice: `a² = D + 2 S` where `D` holds the
squares `aᵢ²` on the diagonal and `S` is the sum of the products `aᵢ aⱼ` with `j < i`. That is about
half the limb products of `mulBasecase a a`.

`S` is built one row at a time: row `i` adds `aᵢ * a[0...i]` at limb `i`, with `addMul1`. After `i`
rows, `2 S + D` is the square of the first `i` limbs, since adding the limb `aᵢ` adds
`2 βⁱ Aᵢ aᵢ + β²ⁱ aᵢ²` to the square of `Aᵢ`.
-/

open ScalarArray

namespace Bignum

/-- The value of the squares of the limbs of `l`, the square of limb `i` at limb `2 i`. -/
@[expose] public def sqDiag : List UInt32 → Nat
  | [] => 0
  | d :: l => d.toNat * d.toNat + 2 ^ 64 * sqDiag l

public theorem sqDiag_append (l₁ l₂ : List UInt32) :
    sqDiag (l₁ ++ l₂) = sqDiag l₁ + 2 ^ (64 * l₁.length) * sqDiag l₂ := by
  induction l₁ with
  | nil => simp [sqDiag]
  | cons d l ih =>
    simp only [List.cons_append, sqDiag, ih, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.pow_add]
    grind

/-- Pushes the squares of the limbs `a[j...]`, two limbs each, onto `acc`. -/
def sqrDiagLoop (a : UInt32Array.Slice) (j : Nat) (acc : UInt32Array) : UInt32Array :=
  if h : j < a.size then
    let p := a[j].mulAddAdd a[j] 0 0
    sqrDiagLoop a (j + 1) ((acc.push p.1).push p.2)
  else
    acc
termination_by a.size - j

private theorem sqrDiagLoop_spec (a : UInt32Array.Slice) (j : Nat) (acc : UInt32Array)
    (hj : j ≤ a.size) :
    (sqrDiagLoop a j acc).size = acc.size + 2 * (a.size - j) ∧
      ofLimbs (sqrDiagLoop a j acc).toList =
        ofLimbs acc.toList + 2 ^ (32 * acc.size) * sqDiag (a.copy.toList.drop j) := by
  induction j, acc using sqrDiagLoop.induct a with
  | case1 j acc h p ih =>
    rw [sqrDiagLoop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    simp only [UInt32Array.size_push] at ih₁ ih₂
    refine ⟨by rw [ih₁]; omega, ?_⟩
    have : p.1.toNat + p.2.toNat * 2 ^ 32 = a[j].toNat * a[j].toNat := by
      simpa using UInt32.mulAddAdd_spec a[j] a[j] 0 0
    rw [ih₂, UInt32Array.toList_push, UInt32Array.toList_push, ofLimbs_concat, ofLimbs_concat,
      List.length_append, UInt32Array.length_toList, toList_copy_drop h, sqDiag,
      List.length_singleton]
    rw [show 32 * (acc.size + 1 + 1) = 32 * acc.size + 32 + 32 by omega,
      show 32 * (acc.size + 1) = 32 * acc.size + 32 by omega, Nat.pow_add, Nat.pow_add,
      Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide]
    generalize ofLimbs acc.toList = R at *
    generalize sqDiag (a.copy.toList.drop (j + 1)) = D at *
    generalize 2 ^ (32 * acc.size) = P at *
    generalize p.1.toNat = lo at *
    generalize p.2.toNat = hi at *
    generalize a[j].toNat = x at *
    grind
  | case2 j acc h =>
    rw [sqrDiagLoop]
    simp only [h, ↓reduceDIte]
    have h₁ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    have h₂ : a.size - j = 0 := by omega
    simp [h₁, h₂, sqDiag]

/-- Adds the rows `a[i] * a[0...i]` from `i` on into `r` at limb `i`, one `addMul1` per row. -/
def sqrRowsLoop (a : UInt32Array.Slice) (r : UInt32Array) (i : Nat) (h : r.size = 2 * a.size) :
    UInt32Array :=
  if hi : i < a.size then
    sqrRowsLoop a (addMul1Set r i (a.slice 0 i) a[i] (by simp; omega)) (i + 1) (by simp [h])
  else
    r
termination_by a.size - i

private theorem sqrRowsLoop_spec (a : UInt32Array.Slice) (r : UInt32Array) (i : Nat)
    (h : r.size = 2 * a.size) (hi : i ≤ a.size)
    (hr : 2 * ofLimbs r.toList + sqDiag (a.copy.toList.take i) =
      ofLimbs (a.copy.toList.take i) * ofLimbs (a.copy.toList.take i)) :
    (sqrRowsLoop a r i h).size = 2 * a.size ∧
      2 * ofLimbs (sqrRowsLoop a r i h).toList + sqDiag a.copy.toList = toNat a * toNat a := by
  induction r, i, h using sqrRowsLoop.induct a with
  | case1 r i h hi' ih =>
    rw [sqrRowsLoop]
    simp only [hi', ↓reduceDIte]
    apply ih (by omega)
    have hsl : (a.slice 0 i).size = i := by simp; omega
    have hsl' : toNat (a.slice 0 i) = ofLimbs (a.copy.toList.take i) := by
      simp [toNat, UInt32Array.Slice.copy_slice, List.extract_eq_take_drop]
    -- The limb at `i + i` is zero, since the rows so far are below `2^(32 (i + i))`.
    have hA := ofLimbs_lt (a.copy.toList.take i)
    simp only [List.length_take, UInt32Array.length_toList, UInt32Array.Slice.size_copy,
      Nat.min_eq_left (Nat.le_of_lt hi')] at hA
    have hlt : ofLimbs r.toList < 2 ^ (32 * (i + i)) := by
      have : ofLimbs (a.copy.toList.take i) * ofLimbs (a.copy.toList.take i) <
          2 ^ (32 * i) * 2 ^ (32 * i) := Nat.mul_lt_mul'' hA hA
      rw [Nat.mul_add, Nat.pow_add]
      omega
    have hk : i + i < r.toList.length := by simp; omega
    have hz : r.toList[i + i] = 0 := getElem_eq_zero_of_ofLimbs_lt hk hlt
    simp only [UInt32Array.getElem_toList] at hz
    have hadd := toNat_addMul1Set r i (a.slice 0 i) a[i] (by simp; omega) (by simpa [hsl] using hz)
    simp only [toNat_toSlice, hsl'] at hadd
    rw [hadd]
    have hai : (a.copy.toList)[i]'(by simpa using hi') = a[i] := by simp
    rw [ofLimbs_take_add_one _ _ (by simpa using hi'), hai,
      List.take_add_one, List.getElem?_eq_getElem (by simpa using hi'), Option.toList_some, hai,
      sqDiag_append, List.length_take_of_le (by simpa using Nat.le_of_lt hi')]
    simp only [sqDiag, Nat.mul_zero, Nat.add_zero]
    have hpow : 2 ^ (64 * i) = 2 ^ (32 * i) * 2 ^ (32 * i) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow] at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (a.copy.toList.take i) = A at *
    generalize sqDiag (a.copy.toList.take i) = D at *
    generalize 2 ^ (32 * i) = P at *
    generalize a[i].toNat = x at *
    grind
  | case2 r i h hi' =>
    rw [sqrRowsLoop]
    simp only [hi', ↓reduceDIte]
    refine ⟨h, ?_⟩
    have : i = a.size := by omega
    rw [this, List.take_of_length_le (by simp)] at hr
    rw [hr]
    rfl

/-- All `2 * a.size` limbs of `a * a`, untrimmed, by the schoolbook algorithm. -/
public def sqrBasecase (a : UInt32Array.Slice) : UInt32Array :=
  let s := sqrRowsLoop a (.replicate (2 * a.size) 0) 0 (by simp)
  let d := sqrDiagLoop a 0 (.emptyWithCapacity (2 * a.size))
  addInto (addInto d 0 s) 0 s

public theorem sqrBasecase_spec (a : UInt32Array.Slice) :
    (sqrBasecase a).size = a.size + a.size ∧ toNat (sqrBasecase a) = toNat a * toNat a := by
  rw [toNat_toSlice]
  unfold sqrBasecase
  simp only [UInt32Array.emptyWithCapacity_eq_empty]
  obtain ⟨hss, hs⟩ := sqrRowsLoop_spec a (.replicate (2 * a.size) 0) 0 (by simp) (Nat.zero_le _)
    (by simp [sqDiag])
  obtain ⟨hds, hd⟩ := sqrDiagLoop_spec a 0 .empty (Nat.zero_le _)
  simp only [UInt32Array.size_empty, Nat.zero_add, Nat.sub_zero, UInt32Array.toList_empty,
    ofLimbs_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, List.drop_zero] at hds hd
  generalize sqrRowsLoop a (.replicate (2 * a.size) 0) 0 (by simp) = s at *
  generalize sqrDiagLoop a 0 .empty = d at *
  have hfit₁ : 0 + s.toSlice.size ≤ d.size := by simp [hss, hds]
  have hfit₂ : 0 + s.toSlice.size ≤ (addInto d 0 s).size := by
    rw [size_addInto _ _ _ hfit₁]
    exact hfit₁
  have hlt : toNat a * toNat a < 2 ^ (32 * (2 * a.size)) := by
    rw [show 32 * (2 * a.size) = 32 * a.size + 32 * a.size by omega, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt a)
  have h₁ : toNat (addInto d 0 s) = ofLimbs d.toList + ofLimbs s.toList := by
    rw [toNat_addInto_of_lt _ _ _ hfit₁ (by
      rw [toNat_toSlice, toNat_toSlice, hds, hd, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
      omega)]
    rw [toNat_toSlice, toNat_toSlice, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
  have h₂ : toNat (addInto (addInto d 0 s) 0 s) = toNat a * toNat a := by
    rw [toNat_addInto_of_lt _ _ _ hfit₂ (by
      rw [h₁, size_addInto _ _ _ hfit₁, hds, toNat_toSlice, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
      omega), h₁, toNat_toSlice, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    omega
  refine ⟨?_, ?_⟩
  · rw [size_addInto _ _ _ hfit₂, size_addInto _ _ _ hfit₁, hds]
    omega
  · rw [← toNat_toSlice, h₂]

end Bignum
