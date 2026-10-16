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

`addAtFast` adds the limbs of `a` with `foldInPlace`, as `addMul1Fast` does, then
propagates the carry with `addAt`'s own loop, which stops as soon as the carry is gone. The fold
keeps the carry as a word with `UInt32.addWithCarryWord`, which makes a shorter dependency
chain from limb to limb than a `Bool`. `@[csimp]` makes the compiler use `addAtFast` in place
of `addAt`.
-/

/-- The step of the fold of `addAtFast`: adds limb `k` of the slice `arr[st...st + len]` to `y`. -/
@[inline] def addAtStep (arr : UInt32Array) (st len : USize) (has : arr.size < USize.size)
    (h : st.toNat + len.toNat ≤ arr.size) (k : USize) (hk : k.toNat < len.toNat) (y c : UInt32) :
    UInt32 × UInt32 :=
  y.addWithCarryWord (limbU arr st len has h k hk) c

/-- `addAt` with `foldInPlace` over the limbs of `a`, which the compiler uses in its place. -/
public def addAtFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array × Bool :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 ∧ off + a.size ≤ r.size then
    let arr := a.array
    let st := a.start.toUSize
    let p := r.foldInPlace off.toUSize a.size.toUSize (0 : UInt32)
      (addAtStep arr st a.size.toUSize (lt_usizeSize hs.2.1) (limbU_bound a (lt_usizeSize hs.2.1)))
      (by
        have := USize.le_size
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        exact hs.2.2)
    addAtLoop p.1 off a a.size (p.2 != 0)
  else
    addAtLoop r off a 0 false

/--
The fold of `addAtFast` from limb `j` on, with the carry `c` as a word, then the carry, is
`addAtLoop` from limb `j` on.
-/
private theorem foldInPlace_loop_addAt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (has : a.array.size < USize.size) (s n : Nat) (hs : s = off) (hn : n = a.size) (j : Nat)
    (c : Bool) (ha : off + a.size ≤ r.size) (hj : j ≤ a.size) (h' hlen) :
    addAtLoop (UInt32Array.foldInPlace.loop a.size.toUSize
          (addAtStep a.array a.start.toUSize a.size.toUSize has (limbU_bound a has)) s n r h'
          hlen j c.toUInt32).1
        off a a.size
        ((UInt32Array.foldInPlace.loop a.size.toUSize
          (addAtStep a.array a.start.toUSize a.size.toUSize has (limbU_bound a has)) s n r h'
          hlen j c.toUInt32).2 != 0) =
      addAtLoop r off a j c := by
  have hc (c : Bool) : (c.toUInt32 != 0) = c := by cases c <;> rfl
  subst s n
  induction r, j, c using addAtLoop.induct off a with
  | case1 r j c h hstop =>
    have : j = a.size := by omega
    subst this
    rw [UInt32Array.foldInPlace.loop]
    simp [hc]
  | case2 r j c h hstop p ih =>
    by_cases hja : j < a.size
    · rw [UInt32Array.foldInPlace.loop]
      conv => rhs; rw [addAtLoop]
      simp only [hja, ↓reduceDIte, h, hstop, ↓reduceIte, addAtStep, limbU_eq a has j _ hja,
        UInt32.addWithCarryWord_toUInt32]
      have hg : a.getD j 0 = a[j] := by simp [UInt32Array.Slice.getD_eq, hja]
      simp only [p, hg] at ih ⊢
      exact ih (by simpa using ha) (by omega) (by simpa using ha)
    · have : j = a.size := by omega
      subst this
      rw [UInt32Array.foldInPlace.loop]
      simp [hc]
  | case3 r j c h =>
    have : j = a.size := by omega
    subst this
    rw [UInt32Array.foldInPlace.loop]
    simp [hc]

@[csimp] public theorem addAt_eq_addAtFast : @addAt = @addAtFast := by
  funext r off a
  rw [addAt, addAtFast]
  split
  · rename_i hs
    have := USize.le_size
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (foldInPlace_loop_addAt r off a (lt_usizeSize hs.2.1) _ _ (toNat_toUSize (by omega))
      (toNat_toUSize (by omega)) 0 false hs.2.2 (by omega) _ _).symm
  · rfl

/-! ## Adding without the carry out

`addInto r off a` is `(addAt r off a).1`, which is all that the callers use. Its compiled form
ends the fold with `foldInPlaceThen` and then propagates the carry with `incrFrom`, which returns
the array alone, so it allocates no pair.
-/

/-- Adds one at limb `i` of `r` and propagates the carry to the end of `r`, dropping the last. -/
public def incrFrom (r : UInt32Array) (i : Nat) : UInt32Array :=
  if h : i < r.size then
    if r[i] = 0xFFFFFFFF then incrFrom (r.set i 0 h) (i + 1) else r.set i (r[i] + 1) h
  else
    r
termination_by r.size - i

/-- `incrFrom r i` adds `2^(32 i)` to `r` when the sum fits. -/
public theorem incrFrom_spec (r : UInt32Array) (i : Nat) (hi : i ≤ r.size)
    (hlt : ofLimbs r.toList + 2 ^ (32 * i) < 2 ^ (32 * r.size)) :
    (incrFrom r i).size = r.size ∧
      ofLimbs (incrFrom r i).toList = ofLimbs r.toList + 2 ^ (32 * i) := by
  induction r, i using incrFrom.induct with
  | case1 r i h hmax ih =>
    rw [incrFrom]
    simp only [h, hmax, ↓reduceDIte, ↓reduceIte]
    have hk : i < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList i 0 hk
    simp only [UInt32Array.getElem_toList, hmax, UInt32.toNat_zero, Nat.mul_zero,
      Nat.add_zero, UInt32.reduceToNat] at hset
    have hpow : 2 ^ (32 * (i + 1)) = 2 ^ (32 * i) * 4294967296 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    simp only [UInt32Array.size_set, UInt32Array.toList_set, hpow] at ih ⊢
    generalize ofLimbs (r.toList.set i 0) = R' at *
    generalize ofLimbs r.toList = R at *
    generalize 2 ^ (32 * i) = P at *
    obtain ⟨ih₁, ih₂⟩ := ih (by omega) (by omega)
    exact ⟨ih₁, by omega⟩
  | case2 r i h hmax =>
    rw [incrFrom]
    simp only [h, hmax, ↓reduceDIte, ↓reduceIte, UInt32Array.size_set, true_and]
    have hk : i < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList i (r[i] + 1) hk
    simp only [UInt32Array.getElem_toList] at hset
    generalize r[i] = v at hmax hset
    have hv : (v + 1).toNat = v.toNat + 1 := by
      have : v.toNat ≠ 4294967295 := fun e => hmax (UInt32.toNat_inj.1 e)
      have := v.toNat_lt
      rw [UInt32.toNat_add, UInt32.toNat_one]
      omega
    rw [UInt32Array.toList_set]
    rw [hv, Nat.mul_add, Nat.mul_one] at hset
    omega
  | case3 r i h =>
    have : i = r.size := by omega
    subst this
    omega

/-- Past the limbs of `a`, `addAtLoop` only propagates the carry, which `incrFrom` does. -/
private theorem addAtLoop_tail (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (j : Nat)
    (c : Bool) (hj : a.size ≤ j) :
    (addAtLoop r off a j c).1 = if c then incrFrom r (off + j) else r := by
  induction r, j, c using addAtLoop.induct off a with
  | case1 r j c h hstop =>
    rw [addAtLoop]
    simp [h, hstop]
  | case2 r j c h hstop p ih =>
    have hc : c = true := by cases c <;> simp_all
    subst hc
    rw [addAtLoop]
    simp only [h, hstop, ↓reduceDIte, ↓reduceIte]
    rw [ih (by omega)]
    have hg : a.getD j 0 = 0 := by simp [UInt32Array.Slice.getD_eq, show ¬ j < a.size by omega]
    have hp := UInt32.addWithCarry_zero_true r[off + j]
    simp only [p, hg, hp] at *
    conv => rhs; rw [incrFrom]
    simp only [h, ↓reduceDIte]
    by_cases hx : r[off + j] = 0xFFFFFFFF
    · simp [hx, Nat.add_assoc]
    · simp [hx]
  | case3 r j c h =>
    rw [addAtLoop]
    cases c
    · simp [h]
    · simp only [h, ↓reduceDIte, ↓reduceIte]
      rw [incrFrom]
      simp [h]

/-- `addAt` without the carry out of `r`. -/
public def addInto (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array :=
  (addAt r off a).1

/-- `addInto` with `foldInPlaceThen` and `incrFrom`, which the compiler uses in its place. -/
public def addIntoFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 ∧ off + a.size ≤ r.size then
    let arr := a.array
    let st := a.start.toUSize
    r.foldInPlaceThen off.toUSize a.size.toUSize (0 : UInt32)
      (addAtStep arr st a.size.toUSize (lt_usizeSize hs.2.1) (limbU_bound a (lt_usizeSize hs.2.1)))
      (fun r' c => if c != 0 then incrFrom r' (off + a.size) else r')
      (by
        have := USize.le_size
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        exact hs.2.2)
  else
    (addAtLoop r off a 0 false).1

@[csimp] public theorem addInto_eq_addIntoFast : @addInto = @addIntoFast := by
  funext r off a
  rw [addInto, addAt, addIntoFast]
  split
  · rename_i hs
    have := USize.le_size
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    have := USize.le_size
    rw [UInt32Array.foldInPlaceThen_eq]
    rw [← foldInPlace_loop_addAt r off a (lt_usizeSize hs.2.1) _ _ (toNat_toUSize (by omega))
      (toNat_toUSize (by omega)) 0 false hs.2.2 (by omega) _ _, addAtLoop_tail _ _ _ _ _ (by omega)]
    rfl
  · rfl

@[simp] public theorem size_addInto (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) : (addInto r off a).size = r.size :=
  size_addAt r off a ha

/-- When the sum fits in `r`, `addInto` adds. -/
public theorem toNat_addInto_of_lt (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (ha : off + a.size ≤ r.size) (hlt : toNat r + 2 ^ (32 * off) * toNat a < 2 ^ (32 * r.size)) :
    toNat (addInto r off a) = toNat r + 2 ^ (32 * off) * toNat a :=
  toNat_addAt_of_lt r off a ha hlt

/-! ## Sums -/

/--
All `max a.size b.size + 1` limbs of `a + b`, untrimmed, like GMP's `mpn_add`: `a` is copied into
the result and `b` added in place.
-/
public def addLimbs (a b : UInt32Array.Slice) : UInt32Array :=
  addInto (copyPadded a (max a.size b.size + 1)) 0 b

private theorem addLimbs_fit (a b : UInt32Array.Slice) :
    0 + b.size ≤ (copyPadded a (max a.size b.size + 1)).size := by
  rw [size_copyPadded _ _ (by omega)]
  omega

@[simp] public theorem size_addLimbs (a b : UInt32Array.Slice) :
    (addLimbs a b).size = max a.size b.size + 1 := by
  rw [addLimbs, size_addInto _ _ _ (addLimbs_fit a b), size_copyPadded _ _ (by omega)]

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
  rw [addLimbs, toNat_addInto_of_lt _ _ _ (addLimbs_fit a b) (by
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
