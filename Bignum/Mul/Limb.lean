/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Basic
public import Bignum.UInt

/-!
# Multiplication by a limb

The two linear primitives of multiplication, after GMP's `mpn_mul_1` and `mpn_addmul_1`. Neither
trims its result: each returns the limbs it computed and the carry limb separately.
-/

open ScalarArray

namespace Bignum

/-- Adds `a[j...] * x + c` to the limbs of `r` from `off + j` on and returns the carry. -/
def addMul1Loop (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32) (j : Nat)
    (c : UInt32) (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hj : j < a.size then
    let p := a[j].mulAddAdd x r[off + j] c
    addMul1Loop (r.set (off + j) p.1 (by omega)) off a x (j + 1) p.2 (by simpa using h)
  else
    (r, c)
termination_by a.size - j

/--
Adds `a * x` to the limbs of `r` from `off` on, like GMP's `mpn_addmul_1`. Returns the new limbs
and the carry limb, whose place is `off + a.size`.
-/
public def addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  addMul1Loop r off a x 0 0 h

private theorem addMul1Loop_spec (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (j : Nat) (c : UInt32) (h : off + a.size ≤ r.size) (hj : j ≤ a.size) :
    (addMul1Loop r off a x j c h).1.size = r.size ∧
      ofLimbs (addMul1Loop r off a x j c h).1.toList +
          2 ^ (32 * (off + a.size)) * (addMul1Loop r off a x j c h).2.toNat =
        ofLimbs r.toList +
          2 ^ (32 * (off + j)) * (c.toNat + ofLimbs (a.copy.toList.drop j) * x.toNat) := by
  induction r, j, c, h using addMul1Loop.induct off a x with
  | case1 r j c h hj' p ih =>
    rw [addMul1Loop]
    simp only [hj', ↓reduceDIte]
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    simp only [UInt32Array.size_set] at ih₁
    refine ⟨ih₁, ?_⟩
    have hk : off + j < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList (off + j) p.1 hk
    have : p.1.toNat + p.2.toNat * 2 ^ 32 = a[j].toNat * x.toNat + r[off + j].toNat + c.toNat :=
      UInt32.mulAddAdd_spec a[j] x r[off + j] c
    simp only [UInt32Array.getElem_toList] at hset
    rw [ih₂, UInt32Array.toList_set, toList_copy_drop hj', ofLimbs_cons, ← Nat.add_assoc off j 1,
      Nat.mul_add 32 (off + j) 1, Nat.mul_one, Nat.pow_add]
    generalize ofLimbs (r.toList.set (off + j) p.1) = R₁ at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (a.copy.toList.drop (j + 1)) = D at *
    generalize 2 ^ (32 * (off + j)) = P at *
    generalize p.1.toNat = lo at *
    generalize p.2.toNat = hi at *
    generalize a[j].toNat = y at *
    generalize r[off + j].toNat = z at *
    grind
  | case2 r j c h hj' =>
    rw [addMul1Loop]
    simp only [hj', ↓reduceDIte]
    have h₂ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    have h₃ : j = a.size := by omega
    rw [h₂, h₃]
    simp

private theorem getElem?_toList_addMul1Loop (r : UInt32Array) (off : Nat)
    (a : UInt32Array.Slice) (x : UInt32) (j : Nat) (c : UInt32) (h : off + a.size ≤ r.size)
    (k : Nat) (hk : k < off + j ∨ off + a.size ≤ k) :
    (addMul1Loop r off a x j c h).1.toList[k]? = r.toList[k]? := by
  induction r, j, c, h using addMul1Loop.induct off a x with
  | case1 r j c h hj' p ih =>
    rw [addMul1Loop]
    simp only [hj', ↓reduceDIte]
    rw [ih (by omega), UInt32Array.toList_set, List.getElem?_set_ne (by omega)]
  | case2 r j c h hj' =>
    rw [addMul1Loop]
    simp only [hj', ↓reduceDIte]

@[simp] public theorem size_addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ r.size) : (addMul1 r off a x h).1.size = r.size :=
  (addMul1Loop_spec r off a x 0 0 h (Nat.zero_le _)).1

/-- `addMul1` leaves the limbs outside `off` to `off + a.size` unchanged. -/
public theorem getElem?_addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ r.size) (k : Nat) (hk : k < off ∨ off + a.size ≤ k) :
    (addMul1 r off a x h).1[k]? = r[k]? := by
  rw [← UInt32Array.getElem?_toList, ← UInt32Array.getElem?_toList]
  exact getElem?_toList_addMul1Loop r off a x 0 0 h k (by omega)

public theorem toNat_addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) :
    toNat (addMul1 r off a x h).1 + 2 ^ (32 * (off + a.size)) * (addMul1 r off a x h).2.toNat =
      toNat r + 2 ^ (32 * off) * (toNat a * x.toNat) := by
  simpa [addMul1, toNat] using (addMul1Loop_spec r off a x 0 0 h (Nat.zero_le _)).2

/-- `a * x` as `a.size` limbs and a carry limb, like GMP's `mpn_mul_1`: `addMul1` into zeros. -/
public def mul1 (a : UInt32Array.Slice) (x : UInt32) : UInt32Array × UInt32 :=
  addMul1 (.replicate a.size 0) 0 a x (by simp)

@[simp] public theorem size_mul1 (a : UInt32Array.Slice) (x : UInt32) :
    (mul1 a x).1.size = a.size := by
  simp [mul1]

public theorem toNat_mul1 (a : UInt32Array.Slice) (x : UInt32) :
    toNat (mul1 a x).1 + 2 ^ (32 * a.size) * (mul1 a x).2.toNat = toNat a * x.toNat := by
  have := toNat_addMul1 (.replicate a.size 0) 0 a x (by simp)
  rw [toNat_toSlice, toNat_toSlice] at this
  rw [toNat_toSlice]
  simpa [mul1] using this

/-- `v * x` as `v.size + 1` limbs. -/
public def mulRow (v : UInt32Array.Slice) (x : UInt32) : UInt32Array :=
  let p := mul1 v x
  p.1.push p.2

@[simp] public theorem size_mulRow (v : UInt32Array.Slice) (x : UInt32) :
    (mulRow v x).size = v.size + 1 := by
  simp [mulRow]

public theorem toNat_mulRow (v : UInt32Array.Slice) (x : UInt32) :
    toNat (mulRow v x) = toNat v * x.toNat := by
  have := toNat_mul1 v x
  rw [toNat_toSlice] at this ⊢
  rw [mulRow, UInt32Array.toList_push, ofLimbs_concat, UInt32Array.length_toList, size_mul1,
    this]

/-! ## Compiled loops

The loops above use `Nat` indices into slices, which keeps their proofs simple. `addMul1Fast`
computes the same as `addMul1` with `foldInPlace`, which updates the array in place with one
exclusivity check and `USize` indices, and `@[csimp]` makes the compiler use it in place of
`addMul1`, with a proof that the two return the same result. `foldInPlace` needs the arrays to fit
in a `USize`, which every array in memory does; the other case falls back to `addMul1`'s loop.
-/

/-- `addMul1` as a `foldInPlace`, which the compiler uses in its place. -/
public def addMul1Fast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hs : r.size < USize.size ∧ a.array.size < USize.size then
    r.foldInPlace off.toUSize a.size.toUSize 0
      (fun k hk y c => (limbU a hs.2 k hk).mulAddAdd x y c)
      (by
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        exact h)
  else
    addMul1Loop r off a x 0 0 h

/-- The fold of `addMul1Fast` from limb `k` on is `addMul1Loop` from limb `k` on. -/
private theorem foldInPlace_loop_addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (has : a.array.size < USize.size) (s n : Nat) (hs : s = off) (hn : n = a.size)
    (k : Nat) (c : UInt32) (h : off + a.size ≤ r.size) (h' hlen) :
    UInt32Array.foldInPlace.loop a.size.toUSize (fun k hk y c => (limbU a has k hk).mulAddAdd x y c)
        s n r h' hlen k c =
      addMul1Loop r off a x k c h := by
  subst s n
  induction r, k, c, h using addMul1Loop.induct off a x with
  | case1 r k c h hk p ih =>
    rw [UInt32Array.foldInPlace.loop, addMul1Loop]
    simp only [hk, ↓reduceDIte]
    simp only [limbU_eq a has k _ hk]
    exact ih _
  | case2 r k c h hk =>
    rw [UInt32Array.foldInPlace.loop, addMul1Loop]
    simp only [hk, ↓reduceDIte]

@[csimp] public theorem addMul1_eq_addMul1Fast : @addMul1 = @addMul1Fast := by
  funext r off a x h
  rw [addMul1, addMul1Fast]
  split
  · rename_i hs
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (foldInPlace_loop_addMul1 r off a x hs.2 _ _ (toNat_toUSize (by omega))
      (toNat_toUSize (by omega)) 0 0 h _ _).symm
  · rfl

end Bignum
