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

/-! ## The compiled loop

`addMul1Loop` uses `Nat` indices into slices, which keeps its proofs simple. `addMul1Fast`
computes the same as `addMul1` with `foldInPlace`, which updates the array in place with one
exclusivity check and `USize` indices, and `@[csimp]` makes the compiler use it in place of
`addMul1`, with a proof that the two return the same result. `foldInPlace` needs the arrays to fit
in a `USize`, which every array in memory does; the other case falls back to `addMul1`'s loop.
This comes before the rest of the file so that `mul1` and `mulRow` are compiled with it.
-/

/--
The step of the fold of `addMul1Fast`: adds limb `k` of the slice `arr[st...st + len]` times `x`
to `y`.
-/
@[inline] def addMul1Step (arr : UInt32Array) (st len : USize) (has : arr.size < USize.size)
    (h : st.toNat + len.toNat ≤ arr.size) (x : UInt32) (k : USize) (hk : k.toNat < len.toNat)
    (y c : UInt32) : UInt32 × UInt32 :=
  (limbU arr st len has h k hk).mulAddAdd x y c

/-- `addMul1` as a `foldInPlace`, which the compiler uses in its place. -/
public def addMul1Fast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    let arr := a.array
    let st := a.start.toUSize
    r.foldInPlace off.toUSize a.size.toUSize 0
      (addMul1Step arr st a.size.toUSize (lt_usizeSize hs.2) (limbU_bound a (lt_usizeSize hs.2)) x)
      (by
        have := USize.le_size
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
    UInt32Array.foldInPlace.loop a.size.toUSize
        (addMul1Step a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) x) s n r h'
        hlen k c =
      addMul1Loop r off a x k c h := by
  subst s n
  induction r, k, c, h using addMul1Loop.induct off a x with
  | case1 r k c h hk p ih =>
    rw [UInt32Array.foldInPlace.loop, addMul1Loop]
    simp only [hk, ↓reduceDIte]
    simp only [addMul1Step, limbU_eq a has k _ hk]
    exact ih _
  | case2 r k c h hk =>
    rw [UInt32Array.foldInPlace.loop, addMul1Loop]
    simp only [hk, ↓reduceDIte]

@[csimp] public theorem addMul1_eq_addMul1Fast : @addMul1 = @addMul1Fast := by
  funext r off a x h
  rw [addMul1, addMul1Fast]
  split
  · rename_i hs
    have := USize.le_size
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (foldInPlace_loop_addMul1 r off a x (lt_usizeSize hs.2) _ _ (toNat_toUSize (by omega))
      (toNat_toUSize (by omega)) 0 0 h _ _).symm
  · rfl

/-! ## Correctness -/

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

/-! ## Storing the carry -/

/--
`addMul1` followed by writing the carry limb at `off + a.size`, over the limb there: the step of
the schoolbook loops, where that limb is still zero.
-/
public def addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size < r.size) : UInt32Array :=
  let p := addMul1 r off a x (by omega)
  p.1.set (off + a.size) p.2 (by rw [size_addMul1]; exact h)

/--
`addMul1Set` with `foldInPlaceThen`, which the compiler uses in its place: the loop stores the
carry itself, so no pair of the new limbs and the carry is allocated.
-/
public def addMul1SetFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size < r.size) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    let arr := a.array
    let st := a.start.toUSize
    r.foldInPlaceThen off.toUSize a.size.toUSize 0
      (addMul1Step arr st a.size.toUSize (lt_usizeSize hs.2) (limbU_bound a (lt_usizeSize hs.2)) x)
      (fun r' c => if h' : off + a.size < r'.size then r'.set (off + a.size) c h' else r')
      (by
        have := USize.le_size
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        omega)
  else
    let p := addMul1Loop r off a x 0 0 (by omega)
    if h' : off + a.size < p.1.size then p.1.set (off + a.size) p.2 h' else p.1

@[csimp] public theorem addMul1Set_eq_addMul1SetFast : @addMul1Set = @addMul1SetFast := by
  funext r off a x h
  have hsz := size_addMul1 r off a x (by omega)
  rw [addMul1Set, addMul1SetFast]
  split
  · rename_i hs
    have := USize.le_size
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    rw [UInt32Array.foldInPlaceThen_eq]
    have heq : r.foldInPlace off.toUSize a.size.toUSize 0
        (addMul1Step a.array a.start.toUSize a.size.toUSize (lt_usizeSize hs.2)
          (limbU_bound a (lt_usizeSize hs.2)) x)
        (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega) =
        addMul1 r off a x (by omega) :=
      foldInPlace_loop_addMul1 r off a x (lt_usizeSize hs.2) _ _ (toNat_toUSize (by omega))
        (toNat_toUSize (by omega)) 0 0 (by omega) _ _
    simp only [heq, hsz, h, ↓reduceDIte]
  · simp only [addMul1] at hsz ⊢
    simp only [hsz, h, ↓reduceDIte]

@[simp] public theorem size_addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size < r.size) : (addMul1Set r off a x h).size = r.size := by
  simp only [addMul1Set, UInt32Array.size_set, size_addMul1]

/--
`addMul1Set` on the first `n` limbs of `a`. The compiled form reads them from the array of `a`
directly, without the slice object, for the rows of the schoolbook square.
-/
public def addMul1SetPre (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) : UInt32Array :=
  addMul1Set r off (a.slice 0 n) x (by rw [UInt32Array.Slice.size_slice]; omega)

public theorem addMul1SetPre_eq (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) :
    addMul1SetPre r off a n x hn h =
      addMul1Set r off (a.slice 0 n) x (by rw [UInt32Array.Slice.size_slice]; omega) := by
  rw [addMul1SetPre]

private theorem prefix_bound (a : UInt32Array.Slice) (n : Nat) (hn : n ≤ a.size)
    (has : a.array.size < USize.size) :
    a.start.toUSize.toNat + n.toUSize.toNat ≤ a.array.size := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
  omega

private theorem limbU_prefix_eq (a : UInt32Array.Slice) (n : Nat) (hn : n ≤ a.size)
    (has : a.array.size < USize.size) (k : Nat) (hk) (hk' : k < n) :
    limbU a.array a.start.toUSize n.toUSize has (prefix_bound a n hn has) k.toUSize hk =
      (a.slice 0 n)[k]'(by rw [UInt32Array.Slice.size_slice]; omega) := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  rw [limbU_eq_getElem _ _ _ _ _ _ _ (a.start + k)
    (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]), UInt32Array.Slice.getElem_slice]
  simp only [Nat.zero_add]
  rfl

/-- The fold of `addMul1SetPreFast` from limb `k` on is `addMul1Loop` on the prefix. -/
private theorem foldInPlace_loop_addMul1Pre (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (n : Nat) (hn : n ≤ a.size) (x : UInt32) (has : a.array.size < USize.size) (s m : Nat)
    (hs : s = off) (hm : m = n) (k : Nat) (c : UInt32) (h : off + (a.slice 0 n).size ≤ r.size)
    (h' hlen) :
    UInt32Array.foldInPlace.loop n.toUSize
        (addMul1Step a.array a.start.toUSize n.toUSize has (prefix_bound a n hn has) x) s m r h'
        hlen k c =
      addMul1Loop r off (a.slice 0 n) x k c h := by
  have hsz : (a.slice 0 n).size = n := by rw [UInt32Array.Slice.size_slice]; omega
  subst s m
  induction r, k, c, h using addMul1Loop.induct off (a.slice 0 n) x with
  | case1 r k c h hk p ih =>
    rw [UInt32Array.foldInPlace.loop, addMul1Loop]
    simp only [show k < n by omega, hk, ↓reduceDIte]
    simp only [addMul1Step, limbU_prefix_eq a n hn has k _ (by omega)]
    exact ih _
  | case2 r k c h hk =>
    rw [UInt32Array.foldInPlace.loop, addMul1Loop]
    simp only [show ¬ k < n by omega, hk, ↓reduceDIte]

/-- `addMul1SetPre` with `foldInPlaceThen` over the array of `a`, used by the compiler. -/
public def addMul1SetPreFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    let arr := a.array
    let st := a.start.toUSize
    r.foldInPlaceThen off.toUSize n.toUSize 0
      (addMul1Step arr st n.toUSize (lt_usizeSize hs.2) (prefix_bound a n hn (lt_usizeSize hs.2)) x)
      (fun r' c => if h' : off + n < r'.size then r'.set (off + n) c h' else r')
      (by
        have := USize.le_size
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega)
  else
    addMul1Set r off (a.slice 0 n) x (by rw [UInt32Array.Slice.size_slice]; omega)

@[csimp] public theorem addMul1SetPre_eq_addMul1SetPreFast :
    @addMul1SetPre = @addMul1SetPreFast := by
  funext r off a n x hn h
  have hsz : (a.slice 0 n).size = n := by rw [UInt32Array.Slice.size_slice]; omega
  have hsize := size_addMul1 r off (a.slice 0 n) x (by omega)
  rw [addMul1SetPre, addMul1SetPreFast]
  split
  · rename_i hs
    have := USize.le_size
    rw [UInt32Array.foldInPlaceThen_eq]
    have heq : r.foldInPlace off.toUSize n.toUSize 0
        (addMul1Step a.array a.start.toUSize n.toUSize (lt_usizeSize hs.2)
          (prefix_bound a n hn (lt_usizeSize hs.2)) x)
        (by rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]; omega) =
        addMul1 r off (a.slice 0 n) x (by omega) :=
      foldInPlace_loop_addMul1Pre r off a n hn x (lt_usizeSize hs.2) _ _ (toNat_toUSize (by omega))
        (toNat_toUSize (by omega)) 0 0 (by omega) _ _
    rw [heq, addMul1Set]
    simp only [hsz, hsize, h, ↓reduceDIte]
  · rfl

/-- When the limb at `off + a.size` is zero, `addMul1Set` adds `a * x` at limb `off`. -/
public theorem toNat_addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size < r.size) (hz : r[off + a.size] = 0) :
    toNat (addMul1Set r off a x h) = toNat r + 2 ^ (32 * off) * (toNat a * x.toNat) := by
  have hadd := toNat_addMul1 r off a x (by omega)
  -- The limb at `off + a.size` is still zero, so writing the carry there adds `β^(off + n) c`.
  have hz' : (addMul1 r off a x (by omega)).1[off + a.size]'(by simp; omega) = 0 := by
    have := getElem?_addMul1 r off a x (by omega) (off + a.size) (by omega)
    rw [getElem?_pos (addMul1 r off a x (by omega)).1 (off + a.size) (by simp; omega),
      getElem?_pos r (off + a.size) h, Option.some.injEq] at this
    rw [this, hz]
  have hset := ofLimbs_set (addMul1 r off a x (by omega)).1.toList (off + a.size)
    (addMul1 r off a x (by omega)).2 (by simp; omega)
  simp only [UInt32Array.getElem_toList, hz', UInt32.toNat_zero, Nat.mul_zero,
    Nat.add_zero] at hset
  simp only [toNat_toSlice] at hadd
  rw [toNat_toSlice, addMul1Set, UInt32Array.toList_set, hset, hadd, toNat_toSlice]

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
  addMul1Set (.replicate (v.size + 1) 0) 0 v x (by simp)

@[simp] public theorem size_mulRow (v : UInt32Array.Slice) (x : UInt32) :
    (mulRow v x).size = v.size + 1 := by
  simp only [mulRow, size_addMul1Set, UInt32Array.size_replicate]

public theorem toNat_mulRow (v : UInt32Array.Slice) (x : UInt32) :
    toNat (mulRow v x) = toNat v * x.toNat := by
  have h0 : toNat (UInt32Array.replicate (v.size + 1) 0) = 0 := by
    rw [toNat_toSlice, UInt32Array.toList_replicate, ← List.nil_append (List.replicate _ _),
      ofLimbs_append_replicate_zero, ofLimbs_nil]
  rw [mulRow, toNat_addMul1Set _ _ _ _ _ (by simp), h0]
  simp

/-! ## Subtracting a multiple -/

/-- Subtracts `a[j...] * x + c` from the limbs of `r` from `off + j` on and returns the borrow. -/
def subMul1Loop (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32) (j : Nat)
    (c : UInt32) (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hj : j < a.size then
    let p := r[off + j].subMul a[j] x c
    subMul1Loop (r.set (off + j) p.1 (by omega)) off a x (j + 1) p.2 (by simpa using h)
  else
    (r, c)
termination_by a.size - j

/--
Subtracts `a * x` from the limbs of `r` from `off` on, like GMP's `mpn_submul_1`. Returns the new
limbs and the borrow limb, whose place is `off + a.size`.
-/
public def subMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  subMul1Loop r off a x 0 0 h

/--
The step of the fold of `subMul1Fast`: subtracts limb `k` of the slice `arr[st...st + len]` times
`x` from `y`.
-/
@[inline] def subMul1Step (arr : UInt32Array) (st len : USize) (has : arr.size < USize.size)
    (h : st.toNat + len.toNat ≤ arr.size) (x : UInt32) (k : USize) (hk : k.toNat < len.toNat)
    (y c : UInt32) : UInt32 × UInt32 :=
  y.subMul (limbU arr st len has h k hk) x c

/-- `subMul1` as a `foldInPlace`, which the compiler uses in its place, as for `addMul1Fast`. -/
public def subMul1Fast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    let arr := a.array
    let st := a.start.toUSize
    r.foldInPlace off.toUSize a.size.toUSize 0
      (subMul1Step arr st a.size.toUSize (lt_usizeSize hs.2) (limbU_bound a (lt_usizeSize hs.2)) x)
      (by
        have := USize.le_size
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize (by omega), toNat_toUSize (by omega)]
        exact h)
  else
    subMul1Loop r off a x 0 0 h

/-- The fold of `subMul1Fast` from limb `k` on is `subMul1Loop` from limb `k` on. -/
private theorem foldInPlace_loop_subMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (has : a.array.size < USize.size) (s n : Nat) (hs : s = off) (hn : n = a.size)
    (k : Nat) (c : UInt32) (h : off + a.size ≤ r.size) (h' hlen) :
    UInt32Array.foldInPlace.loop a.size.toUSize
        (subMul1Step a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) x) s n r h'
        hlen k c =
      subMul1Loop r off a x k c h := by
  subst s n
  induction r, k, c, h using subMul1Loop.induct off a x with
  | case1 r k c h hk p ih =>
    rw [UInt32Array.foldInPlace.loop, subMul1Loop]
    simp only [hk, ↓reduceDIte]
    simp only [subMul1Step, limbU_eq a has k _ hk]
    exact ih _
  | case2 r k c h hk =>
    rw [UInt32Array.foldInPlace.loop, subMul1Loop]
    simp only [hk, ↓reduceDIte]

@[csimp] public theorem subMul1_eq_subMul1Fast : @subMul1 = @subMul1Fast := by
  funext r off a x h
  rw [subMul1, subMul1Fast]
  split
  · rename_i hs
    have := USize.le_size
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    exact (foldInPlace_loop_subMul1 r off a x (lt_usizeSize hs.2) _ _ (toNat_toUSize (by omega))
      (toNat_toUSize (by omega)) 0 0 h _ _).symm
  · rfl

private theorem subMul1Loop_spec (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (j : Nat) (c : UInt32) (h : off + a.size ≤ r.size) (hj : j ≤ a.size) :
    (subMul1Loop r off a x j c h).1.size = r.size ∧
      ofLimbs (subMul1Loop r off a x j c h).1.toList +
          2 ^ (32 * (off + j)) * (c.toNat + ofLimbs (a.copy.toList.drop j) * x.toNat) =
        ofLimbs r.toList +
          2 ^ (32 * (off + a.size)) * (subMul1Loop r off a x j c h).2.toNat := by
  induction r, j, c, h using subMul1Loop.induct off a x with
  | case1 r j c h hj' p ih =>
    rw [subMul1Loop]
    simp only [hj', ↓reduceDIte]
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    simp only [UInt32Array.size_set] at ih₁ ih₂
    refine ⟨ih₁, ?_⟩
    have hk : off + j < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList (off + j) p.1 hk
    have : p.1.toNat + a[j].toNat * x.toNat + c.toNat = r[off + j].toNat + p.2.toNat * 2 ^ 32 :=
      UInt32.subMul_spec r[off + j] a[j] x c
    simp only [UInt32Array.getElem_toList] at hset
    rw [UInt32Array.toList_set, ← Nat.add_assoc off j 1, Nat.mul_add 32 (off + j) 1, Nat.mul_one,
      Nat.pow_add] at ih₂
    rw [toList_copy_drop hj', ofLimbs_cons]
    generalize subMul1Loop (r.set (off + j) p.1 (by omega)) off a x (j + 1) p.2
      (by simpa using h) = q at *
    generalize ofLimbs q.1.toList = F at *
    generalize q.2.toNat = b at *
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
    rw [subMul1Loop]
    simp only [hj', ↓reduceDIte]
    have h₂ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    have h₃ : j = a.size := by omega
    rw [h₂, h₃]
    simp

private theorem getElem?_toList_subMul1Loop (r : UInt32Array) (off : Nat)
    (a : UInt32Array.Slice) (x : UInt32) (j : Nat) (c : UInt32) (h : off + a.size ≤ r.size)
    (k : Nat) (hk : k < off + j ∨ off + a.size ≤ k) :
    (subMul1Loop r off a x j c h).1.toList[k]? = r.toList[k]? := by
  induction r, j, c, h using subMul1Loop.induct off a x with
  | case1 r j c h hj' p ih =>
    rw [subMul1Loop]
    simp only [hj', ↓reduceDIte]
    rw [ih (by omega), UInt32Array.toList_set, List.getElem?_set_ne (by omega)]
  | case2 r j c h hj' =>
    rw [subMul1Loop]
    simp only [hj', ↓reduceDIte]

@[simp] public theorem size_subMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ r.size) : (subMul1 r off a x h).1.size = r.size :=
  (subMul1Loop_spec r off a x 0 0 h (Nat.zero_le _)).1

/-- `subMul1` leaves the limbs outside `off` to `off + a.size` unchanged. -/
public theorem getElem?_subMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ r.size) (k : Nat) (hk : k < off ∨ off + a.size ≤ k) :
    (subMul1 r off a x h).1[k]? = r[k]? := by
  rw [← UInt32Array.getElem?_toList, ← UInt32Array.getElem?_toList]
  exact getElem?_toList_subMul1Loop r off a x 0 0 h k (by omega)

public theorem toNat_subMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) :
    toNat (subMul1 r off a x h).1 + 2 ^ (32 * off) * (toNat a * x.toNat) =
      toNat r + 2 ^ (32 * (off + a.size)) * (subMul1 r off a x h).2.toNat := by
  simpa [subMul1, toNat] using (subMul1Loop_spec r off a x 0 0 h (Nat.zero_le _)).2


end Bignum
