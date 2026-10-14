/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Basic
public import Bignum.UInt

/-!
# Addition

* `addLimbs a b` is all `max a.size b.size + 1` limbs of `a + b`, like GMP's `mpn_add`.
* `addAt r off a` adds `a` into `r` from limb `off` on and propagates the carry to the end of `r`,
  like GMP's `mpn_add` followed by `mpn_incr_u`. It works in place when `r` is not shared.
* `add a b` is the trimmed sum.
-/

open ScalarArray

namespace Bignum

/-! ## Adding at an offset -/

/-- Adds `a[j...] + c` to `r` from limb `off + j` on, up to the end of `r`. -/
def addAtLoop (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat) (c : Bool) :
    UInt32Array × Bool :=
  if h : off + j < r.size then
    if a.size ≤ j ∧ c = false then
      (r, false)
    else
      let p := r[off + j].addWithCarry (a.getD j 0) c
      addAtLoop (r.set (off + j) p.1 h) off a (j + 1) p.2
  else
    (r, c)
termination_by r.size - (off + j)

/--
Adds `a` to the limbs of `r` from `off` on and propagates the carry to the end of `r`, like GMP's
`mpn_add` followed by `mpn_incr_u`. Returns the new limbs and the carry out of the last one.
-/
public def addAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array × Bool :=
  addAtLoop r off a 0 false

private theorem addAtLoop_spec (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat)
    (c : Bool) (ha : off + a.size ≤ r.size) (hj : off + j ≤ r.size) :
    (addAtLoop r off a j c).1.size = r.size ∧
      ofLimbs (addAtLoop r off a j c).1.toList +
          2 ^ (32 * r.size) * (addAtLoop r off a j c).2.toNat =
        ofLimbs r.toList + 2 ^ (32 * (off + j)) * (c.toNat + ofLimbs (a.copy.toList.drop j)) := by
  induction r, j, c using addAtLoop.induct off a with
  | case1 r j c h hstop =>
    rw [addAtLoop]
    simp only [h, hstop, ↓reduceDIte, ↓reduceIte, and_self]
    have : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    simp [this]
  | case2 r j c h hstop p ih =>
    rw [addAtLoop]
    simp only [h, hstop, ↓reduceDIte, ↓reduceIte]
    obtain ⟨ih₁, ih₂⟩ := ih (by simpa using ha) (by simp; omega)
    simp only [UInt32Array.size_set] at ih₁ ih₂
    refine ⟨ih₁, ?_⟩
    have hk : off + j < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList (off + j) p.1 hk
    have : p.1.toNat + p.2.toNat * 2 ^ 32 = r[off + j].toNat + (a.getD j 0).toNat + c.toNat :=
      UInt32.addWithCarry_spec r[off + j] (a.getD j 0) c
    simp only [UInt32Array.getElem_toList] at hset
    rw [ih₂, UInt32Array.toList_set, ofLimbs_drop a.copy.toList j, ← getD_eq_getD_toList_copy,
      ← Nat.add_assoc off j 1, Nat.mul_add 32 (off + j) 1, Nat.mul_one, Nat.pow_add]
    generalize ofLimbs (r.toList.set (off + j) p.1) = R₁ at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (a.copy.toList.drop (j + 1)) = A at *
    generalize 2 ^ (32 * (off + j)) = P at *
    generalize p.1.toNat = lo at *
    generalize p.2.toNat = hi at *
    generalize (a.getD j 0).toNat = y at *
    generalize r[off + j].toNat = z at *
    grind
  | case3 r j c h =>
    rw [addAtLoop]
    simp only [h, ↓reduceDIte]
    have h₁ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    have h₂ : off + j = r.size := by omega
    simp [h₁, h₂]

@[simp] public theorem size_addAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) : (addAt r off a).1.size = r.size :=
  (addAtLoop_spec r off a 0 false ha (by omega)).1

public theorem toNat_addAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) :
    toNat (addAt r off a).1 + 2 ^ (32 * r.size) * (addAt r off a).2.toNat =
      toNat r + 2 ^ (32 * off) * toNat a := by
  have := (addAtLoop_spec r off a 0 false ha (by omega)).2
  simpa [addAt, toNat] using this

/-- When the sum fits in `r`, `addAt` has no carry out. -/
public theorem toNat_addAt_of_lt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) (hlt : toNat r + 2 ^ (32 * off) * toNat a < 2 ^ (32 * r.size)) :
    toNat (addAt r off a).1 = toNat r + 2 ^ (32 * off) * toNat a := by
  have := toNat_addAt r off a ha
  cases h : (addAt r off a).2
  · simpa [h] using this
  · simp only [h, Bool.toNat_true, Nat.mul_one] at this
    omega

/-! ## The compiled loop

`addAtFast` runs `addAt`'s loop with `USize` indices, and `@[csimp]` makes the compiler use it, as
for `addMul1Fast`.
-/

/--
`addAtLoop` with `USize` indices: limb `j` of the addend is at `offA + j` in `arr` when `j < na`,
and the loop runs while `j < m`, where `m` is the number of limbs of `r` from `offR` on.
-/
def addAtLoopU (r arr : UInt32Array) (offR offA na m : USize) (j : USize) (c : Bool)
    (hm : offR.toNat + m.toNat = r.size) (ha : offA.toNat + na.toNat ≤ arr.size)
    (hrs : r.size < USize.size) (has : arr.size < USize.size) : UInt32Array × Bool :=
  if hj : j < m then
    if na ≤ j ∧ c = false then
      (r, false)
    else
      have := USize.lt_iff_toNat_lt.1 hj
      have hir : (offR + j).toNat < r.size := by rw [toNat_add_usize (by omega)]; omega
      let y := if hy : j < na then
          arr.uget (offA + j) (by
            have := USize.lt_iff_toNat_lt.1 hy
            rw [toNat_add_usize (by omega)]; omega)
        else 0
      let p := (r.uget (offR + j) hir).addWithCarry y c
      addAtLoopU (r.uset (offR + j) p.1 hir) arr offR offA na m (j + 1) p.2 (by simpa using hm)
        ha (by simpa using hrs) has
  else
    (r, c)
termination_by m.toNat - j.toNat
decreasing_by
  rw [toNat_add_usize (by rw [USize.toNat_one]; omega), USize.toNat_one]
  omega

private theorem addAtLoopU_eq (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat)
    (c : Bool) (hrs : r.size < USize.size) (has : a.array.size < USize.size)
    (ha' : off + a.size ≤ r.size) (hj : off + j ≤ r.size) (m : USize)
    (hmr : m.toNat = r.size - off) (hm ha) :
    addAtLoopU r a.array off.toUSize a.start.toUSize a.size.toUSize m j.toUSize c hm ha hrs has =
      addAtLoop r off a j c := by
  have hstop := a.stop_le_array_size
  have hstart := a.start_le_stop
  have hsize := a.size_eq
  have hoff : off < USize.size := by omega
  have hst : a.start < USize.size := by omega
  have hn : a.size < USize.size := by omega
  induction r, j, c using addAtLoop.induct off a with
  | case1 r j c h hstop' =>
    have hrm : r.size - off < USize.size := by omega
    rw [addAtLoopU, addAtLoop]
    have hlt : j.toUSize < m := by
      rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), hmr]
      omega
    have hle : a.size.toUSize ≤ j.toUSize := by
      rw [USize.le_iff_toNat_le, toNat_toUSize hn, toNat_toUSize (by omega)]
      exact hstop'.1
    simp only [h, hlt, hstop', hle, ↓reduceDIte, ↓reduceIte, and_self]
  | case2 r j c h hstop' p ih =>
    have hrm : r.size - off < USize.size := by omega
    rw [addAtLoopU, addAtLoop]
    have hlt : j.toUSize < m := by
      rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), hmr]
      omega
    have hnot : ¬ (a.size.toUSize ≤ j.toUSize ∧ c = false) := by
      rw [USize.le_iff_toNat_le, toNat_toUSize hn, toNat_toUSize (by omega)]
      exact hstop'
    simp only [h, hlt, hstop', hnot, ↓reduceDIte, ↓reduceIte]
    have hjs : j.toUSize + 1 = (j + 1).toUSize := by
      apply USize.toNat_inj.1
      rw [toNat_add_usize (by rw [toNat_toUSize (by omega), USize.toNat_one]; omega),
        toNat_toUSize (by omega), USize.toNat_one, toNat_toUSize (by omega)]
    have hir : (off.toUSize + j.toUSize).toNat = off + j := by
      rw [toNat_add_usize (by rw [toNat_toUSize hoff, toNat_toUSize (by omega)]; omega),
        toNat_toUSize hoff, toNat_toUSize (by omega)]
    -- The limb of the addend read with `USize` indices is `a.getD j 0`.
    have hy : (if hy : j.toUSize < a.size.toUSize then
        a.array.uget (a.start.toUSize + j.toUSize) (by
          have := USize.lt_iff_toNat_lt.1 hy
          rw [toNat_add_usize (by omega)]; omega)
      else 0) = a.getD j 0 := by
      by_cases hja : j < a.size
      · have hy : j.toUSize < a.size.toUSize := by
          rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), toNat_toUSize hn]
          exact hja
        have hia : (a.start.toUSize + j.toUSize).toNat = a.start + j := by
          rw [toNat_add_usize (by rw [toNat_toUSize hst, toNat_toUSize (by omega)]; omega),
            toNat_toUSize hst, toNat_toUSize (by omega)]
        simp only [hy, ↓reduceDIte, UInt32Array.Slice.getD_eq, hja]
        rw [uget_eq_getElem a.array _ (a.start + j) hia]
        rfl
      · have hy : ¬ j.toUSize < a.size.toUSize := by
          rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), toNat_toUSize hn]
          exact hja
        simp only [hy, ↓reduceDIte, UInt32Array.Slice.getD_eq, hja]
    have ih' := ih (by simpa using hrs) (by simpa using ha') (by simp; omega) (by simp [hmr])
    rw [← hjs] at ih'
    simp only [p, ← hir] at ih'
    simp only [hy, uget_eq_getElem r _ (off + j) hir]
    simp only [← hir]
    exact ih' (by simp only [UInt32Array.size_set, toNat_toUSize hoff, hmr]; omega)
  | case3 r j c h =>
    have hrm : r.size - off < USize.size := by omega
    rw [addAtLoopU, addAtLoop]
    have hlt : ¬ j.toUSize < m := by
      rw [USize.lt_iff_toNat_lt, toNat_toUSize (by omega), hmr]
      omega
    simp only [h, hlt, ↓reduceDIte]

/-- `addAt` with `USize` indices, which the compiler uses in its place. -/
public def addAtFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array × Bool :=
  if hs : r.size < USize.size ∧ a.array.size < USize.size ∧ off + a.size ≤ r.size then
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    addAtLoopU r a.array off.toUSize a.start.toUSize a.size.toUSize (r.size - off).toUSize 0 false
      (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega)
      (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega) hs.1 hs.2.1
  else
    addAtLoop r off a 0 false

@[csimp] public theorem addAt_eq_addAtFast : @addAt = @addAtFast := by
  funext r off a
  rw [addAt, addAtFast]
  split
  · rename_i hs
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (addAtLoopU_eq r off a 0 false hs.1 hs.2.1 hs.2.2 (by omega) _
      (toNat_toUSize (by omega)) _ _).symm
  · rfl

/-! ## Sums -/

/--
All `max a.size b.size + 1` limbs of `a + b`, untrimmed, like GMP's `mpn_add`: `a` is copied into
the result and `b` added in place.
-/
public def addLimbs (a b : UInt32Array.Slice) : UInt32Array :=
  (addAt (copyPadded a (max a.size b.size + 1)) 0 b).1

private theorem addLimbs_fit (a b : UInt32Array.Slice) :
    0 + b.size ≤ (copyPadded a (max a.size b.size + 1)).size := by
  rw [size_copyPadded _ _ (by omega)]
  omega

@[simp] public theorem size_addLimbs (a b : UInt32Array.Slice) :
    (addLimbs a b).size = max a.size b.size + 1 := by
  rw [addLimbs, size_addAt _ _ _ (addLimbs_fit a b), size_copyPadded _ _ (by omega)]

public theorem toNat_addLimbs (a b : UInt32Array.Slice) :
    toNat (addLimbs a b) = toNat a + toNat b := by
  have hA := toNat_lt a
  have hB := toNat_lt b
  have hA' : 2 ^ (32 * a.size) ≤ 2 ^ (32 * max a.size b.size) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hB' : 2 ^ (32 * b.size) ≤ 2 ^ (32 * max a.size b.size) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : 2 ^ (32 * (max a.size b.size + 1)) = 2 ^ (32 * max a.size b.size) * 2 ^ 32 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  rw [addLimbs, toNat_addAt_of_lt _ _ _ (addLimbs_fit a b) (by
    rw [toNat_copyPadded, size_copyPadded _ _ (by omega), hpow]; simp only [Nat.mul_zero,
      Nat.pow_zero, Nat.one_mul]; omega), toNat_copyPadded]
  simp

/-- Adds two numbers. -/
public def add (a b : UInt32Array.Slice) : UInt32Array := trim (addLimbs a b)

@[simp] public theorem toNat_add (a b : UInt32Array.Slice) :
    toNat (add a b) = toNat a + toNat b := by
  rw [add, toNat_trim, toNat_addLimbs]

public theorem isTrimmed_add (a b : UInt32Array.Slice) : isTrimmed (add a b) = true :=
  isTrimmed_trim _

end Bignum
