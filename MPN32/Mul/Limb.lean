/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Basic
public import MPN32.UInt
public import MPN32.UIntArray
public import MPN.MulLimbW

/-!
# Multiplication by a limb

The two linear primitives of multiplication, after GMP's `mpn_mul_1` and `mpn_addmul_1`. Neither
trims its result: each returns the limbs it computed and the carry limb separately.
-/

open ScalarArray

namespace MPN.W32

/-- Adds `a[j...] * x + c` to the limbs of `r` from `off + j` on and returns the carry. -/
def addMul1Loop (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32) (j : Nat)
    (c : UInt32) (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hj : j < a.size then
    let p := a[j].mulAddAdd x r[off + j] c
    addMul1Loop (r.set (off + j) p.1 (by lia)) off a x (j + 1) p.2 (by simpa using h)
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
computes the same as `addMul1` with `main`'s generic pass `WordArray.addMul1W`, which updates the
array in place with one exclusivity check and `USize` indices, and `@[csimp]` makes the compiler
use it in place of `addMul1`, with a proof that the two return the same result. The pass needs the
arrays to fit in a `USize`, which every array in memory does; the other case falls back to
`addMul1`'s loop. This comes before the rest of the file so that `mul1` and `mulRow` are compiled
with it.
-/

/-- The bounds of the generic passes over `n` limbs of `a`, into `r` from limb `off`. -/
public theorem loopBound_window (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (hn : n ≤ a.size) (h : off + n ≤ r.size)
    (hs : r.size < 4294967295 ∧ a.array.size < 4294967295) :
    WordArray.LoopBound r off.toUSize n.toUSize ∧
      WordArray.LoopBound a.array a.start.toUSize n.toUSize := by
  have := USize.le_size
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  simp only [WordArray.LoopBound]
  rw [toNat_toUSize (by lia), toNat_toUSize (by lia), toNat_toUSize (by lia)]
  exact ⟨⟨h, by lia⟩, ⟨show a.start + n ≤ a.array.size by lia, by lia⟩⟩

/-- A fold of `main` on an array equal to another. -/
private theorem fold_congr {β : Type} {n : USize}
    {f : (j : USize) → j < n → UInt32 → β → UInt32 × β} {arr arr' : UInt32Array} {rs : USize}
    {hr : WordArray.LoopBound arr rs n} {j : USize} {b b' : β} (e : arr = arr') (eb : b = b') :
    WordArray.foldUInPlace n f arr rs hr j b =
      WordArray.foldUInPlace n f arr' rs (e ▸ hr) j b' := by
  subst e eb; rfl

/-- The limbs of a slice `b` read from `arr`, as the generic passes read them. -/
private theorem uget_slice (arr : UInt32Array) (ao n : USize) (ha : WordArray.LoopBound arr ao n)
    (b : UInt32Array.Slice) (hb : ∀ k (hk : k < b.size), b[k] = arr[ao.toNat + k]!) (j : USize)
    (hj : j < n) (k : Nat) (hjk : j.toNat = k) (hk : k < b.size) :
    WordArray.uget arr (ao + j) (ha.uset_bound hj) = b[k] := by
  rw [hb k hk, WordArray.uget_eq, ha.toNat_add hj, hjk]; rfl

/-- The limbs of the window of `r`, as the generic passes read them. -/
private theorem uget_window (r : UInt32Array) (ro n : USize) (hr : WordArray.LoopBound r ro n)
    (off : Nat) (hro : ro.toNat = off) (j : USize) (hj : j < n) (k : Nat) (hjk : j.toNat = k)
    (hk : off + k < r.size) :
    WordArray.uget r (ro + j) (hr.uset_bound hj) = r[off + k] := by
  rw [WordArray.uget_eq, hr.toNat_add hj, hro, hjk]
  exact getElem!_pos r (off + k) hk

private theorem uset_window (r : UInt32Array) (ro n : USize) (hr : WordArray.LoopBound r ro n)
    (off : Nat) (hro : ro.toNat = off) (j : USize) (hj : j < n) (k : Nat) (hjk : j.toNat = k)
    (v : UInt32) (hk : off + k < r.size) :
    WordArray.uset r (ro + j) v (hr.uset_bound hj) = r.set (off + k) v hk :=
  uset_eq_set r (ro + j) (off + k) (by rw [hr.toNat_add hj, hro, hjk]) v _

/-- The next index of a fold. -/
private theorem toNat_succ {n j : USize} (hj : j < n) {k : Nat} (hjk : j.toNat = k) :
    (j + 1).toNat = k + 1 := by
  rw [USize.toNat_add_one_of_lt hj, hjk]

/--
The generic fold of `addMul1Step` over the limbs of `b` read from `arr`, from limb `k` on, is
`addMul1Loop` from limb `k` on.
-/
private theorem fold_addMul1 (arr : UInt32Array) (ao n : USize) (ha : WordArray.LoopBound arr ao n)
    (x : UInt32) (off : Nat) (b : UInt32Array.Slice) (hn : n.toNat = b.size)
    (hb : ∀ k (hk : k < b.size), b[k] = arr[ao.toNat + k]!) (ro : USize) (hro : ro.toNat = off)
    (r : UInt32Array) (k : Nat) (c : UInt32) (h : off + b.size ≤ r.size) :
    ∀ (hr : WordArray.LoopBound r ro n) (j : USize), j.toNat = k →
      WordArray.foldUInPlace n (WordArray.addMul1Step UInt32Array arr ao n ha x) r ro hr j c =
        addMul1Loop r off b x k c h := by
  induction r, k, c, h using addMul1Loop.induct off b x with
  | case1 r k c h hk p ih =>
    intro hr j hjk
    have hj : j < n := USize.lt_iff_toNat_lt.2 (by lia)
    rw [WordArray.foldUInPlace_lt _ _ _ _ _ _ _ hj, addMul1Loop, dite_eq_left hk]
    simp only [WordArray.addMul1Step, uget_slice arr ao n ha b hb j hj k hjk hk,
      uget_window r ro n hr off hro j hj k hjk (by lia)]
    exact (fold_congr (uset_window r ro n hr off hro j hj k hjk _ (by lia)) rfl).trans
      (ih _ _ (toNat_succ hj hjk))
  | case2 r k c h hk =>
    intro hr j hjk
    rw [WordArray.foldUInPlace_ge _ _ _ _ _ _ _ (fun e => hk (by
      have := USize.lt_iff_toNat_lt.1 e; lia)), addMul1Loop, dite_eq_right hk]

/-- `addMul1` by `main`'s `addMul1W`, which the compiler uses in its place. -/
public def addMul1Fast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    WordArray.addMul1W r off.toUSize a.array a.start.toUSize a.size.toUSize x 0
      (loopBound_window r off a a.size (Nat.le_refl _) h hs).1
      (loopBound_window r off a a.size (Nat.le_refl _) h hs).2
  else
    addMul1Loop r off a x 0 0 h

/-- The bounds of `addMul1Fast` on its slice, as the generic passes read them. -/
private theorem slice_eq (a : UInt32Array.Slice) (n : Nat) (hn : n ≤ a.size)
    (has : a.array.size < 4294967295) :
    n.toUSize.toNat = n ∧ a.start.toUSize.toNat = a.start := by
  have := USize.le_size
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  exact ⟨toNat_toUSize (by lia), toNat_toUSize (by lia)⟩

private theorem toNat_off (r : UInt32Array) (off n : Nat) (h : off + n ≤ r.size)
    (hs : r.size < 4294967295) : off.toUSize.toNat = off := by
  have := USize.le_size
  exact toNat_toUSize (by lia)

/-- `addMul1` is the generic fold, when the arrays fit in a `USize`. -/
private theorem addMul1_fold (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) (hs : r.size < 4294967295 ∧ a.array.size < 4294967295) :
    WordArray.foldUInPlace a.size.toUSize
        (WordArray.addMul1Step UInt32Array a.array a.start.toUSize a.size.toUSize
          (loopBound_window r off a a.size (Nat.le_refl _) h hs).2 x) r off.toUSize
        (loopBound_window r off a a.size (Nat.le_refl _) h hs).1 0 0 =
      addMul1 r off a x h := by
  obtain ⟨hn, hst⟩ := slice_eq a a.size (Nat.le_refl _) hs.2
  exact fold_addMul1 _ _ _ _ x off a hn (fun k hk => by
      rw [hst, UInt32Array.Slice.getElem_eq_getElem!]) _
    (toNat_off r off a.size h hs.1) r 0 0 h _ 0 rfl

@[csimp] public theorem addMul1_eq_addMul1Fast : @addMul1 = @addMul1Fast := by
  funext r off a x h
  rw [addMul1Fast]
  split
  · rename_i hs
    rw [WordArray.addMul1W, WordArray.foldThen_eq', addMul1_fold r off a x h hs]
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
    obtain ⟨ih₁, ih₂⟩ := ih (by lia)
    simp only [UInt32Array.size_set] at ih₁
    refine ⟨ih₁, ?_⟩
    have hk : off + j < r.toList.length := by simp; lia
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
    have h₂ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; lia)
    have h₃ : j = a.size := by lia
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
    rw [ih (by lia), UInt32Array.toList_set, List.getElem?_set_ne (by lia)]
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
  exact getElem?_toList_addMul1Loop r off a x 0 0 h k (by lia)

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
  let p := addMul1 r off a x (by lia)
  p.1.set (off + a.size) p.2 (by rw [size_addMul1]; exact h)

/--
`addMul1Set` by `main`'s generic fold, which the compiler uses in its place: the loop stores the
carry itself, so no pair of the new limbs and the carry is allocated.
-/
public def addMul1SetFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size < r.size) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    WordFolds.foldThen a.size.toUSize
      (WordArray.addMul1Step UInt32Array a.array a.start.toUSize a.size.toUSize
        (loopBound_window r off a a.size (Nat.le_refl _) (by lia) hs).2 x) r off.toUSize
      (loopBound_window r off a a.size (Nat.le_refl _) (by lia) hs).1 0 0
      (fun r' e c => r'.set (off + a.size) c (by have : r'.size = r.size := e; lia))
  else
    let p := addMul1Loop r off a x 0 0 (by lia)
    if h' : off + a.size < p.1.size then p.1.set (off + a.size) p.2 h' else p.1

@[csimp] public theorem addMul1Set_eq_addMul1SetFast : @addMul1Set = @addMul1SetFast := by
  funext r off a x h
  have hsz := size_addMul1 r off a x (by lia)
  rw [addMul1Set, addMul1SetFast]
  split
  · rename_i hs
    rw [WordArray.foldThen_eq']
    simp only [addMul1_fold r off a x (by lia) hs]
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
  addMul1Set r off (a.slice 0 n) x (by rw [UInt32Array.Slice.size_slice]; lia)

public theorem addMul1SetPre_eq (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) :
    addMul1SetPre r off a n x hn h =
      addMul1Set r off (a.slice 0 n) x (by rw [UInt32Array.Slice.size_slice]; lia) := by
  rw [addMul1SetPre]

/-- `addMul1` on the first `n` limbs of `a` is the generic fold over the array of `a`. -/
private theorem addMul1Pre_fold (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n ≤ r.size)
    (hs : r.size < 4294967295 ∧ a.array.size < 4294967295) (h') :
    WordArray.foldUInPlace n.toUSize
        (WordArray.addMul1Step UInt32Array a.array a.start.toUSize n.toUSize
          (loopBound_window r off a n hn h hs).2 x) r off.toUSize
        (loopBound_window r off a n hn h hs).1 0 0 =
      addMul1 r off (a.slice 0 n) x h' := by
  have hsz : (a.slice 0 n).size = n := by rw [UInt32Array.Slice.size_slice]; lia
  obtain ⟨hn', hst⟩ := slice_eq a n hn hs.2
  exact fold_addMul1 _ _ _ _ x off (a.slice 0 n) (by rw [hn', hsz])
    (fun k hk => by
      rw [UInt32Array.Slice.getElem_slice, UInt32Array.Slice.getElem_eq_getElem!, hst,
        Nat.zero_add])
    _ (toNat_off r off n h hs.1) r 0 0 h' _ 0 rfl

/-- `addMul1SetPre` by `main`'s generic fold over the array of `a`, used by the compiler. -/
public def addMul1SetPreFast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    WordFolds.foldThen n.toUSize
      (WordArray.addMul1Step UInt32Array a.array a.start.toUSize n.toUSize
        (loopBound_window r off a n hn (by lia) hs).2 x) r off.toUSize
      (loopBound_window r off a n hn (by lia) hs).1 0 0
      (fun r' e c => r'.set (off + n) c (by have : r'.size = r.size := e; lia))
  else
    addMul1Set r off (a.slice 0 n) x (by rw [UInt32Array.Slice.size_slice]; lia)

@[csimp] public theorem addMul1SetPre_eq_addMul1SetPreFast :
    @addMul1SetPre = @addMul1SetPreFast := by
  funext r off a n x hn h
  have hsz : (a.slice 0 n).size = n := by rw [UInt32Array.Slice.size_slice]; lia
  rw [addMul1SetPre, addMul1SetPreFast]
  split
  · rename_i hs
    rw [WordArray.foldThen_eq', addMul1Set]
    simp only [addMul1Pre_fold r off a n x hn (by lia) hs (by lia), hsz]
  · rfl

/-- When the limb at `off + a.size` is zero, `addMul1Set` adds `a * x` at limb `off`. -/
public theorem toNat_addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size < r.size) (hz : r[off + a.size] = 0) :
    toNat (addMul1Set r off a x h) = toNat r + 2 ^ (32 * off) * (toNat a * x.toNat) := by
  have hadd := toNat_addMul1 r off a x (by lia)
  -- The limb at `off + a.size` is still zero, so writing the carry there adds `β^(off + n) c`.
  have hz' : (addMul1 r off a x (by lia)).1[off + a.size]'(by simp; lia) = 0 := by
    have := getElem?_addMul1 r off a x (by lia) (off + a.size) (by lia)
    rw [getElem?_pos (addMul1 r off a x (by lia)).1 (off + a.size) (by simp; lia),
      getElem?_pos r (off + a.size) h, Option.some.injEq] at this
    rw [this, hz]
  have hset := ofLimbs_set (addMul1 r off a x (by lia)).1.toList (off + a.size)
    (addMul1 r off a x (by lia)).2 (by simp; lia)
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
  have h0 := toNat_zeros (v.size + 1)
  rw [mulRow, toNat_addMul1Set _ _ _ _ _ (by simp), h0]
  simp

/-! ## Subtracting a multiple -/

/-- Subtracts `a[j...] * x + c` from the limbs of `r` from `off + j` on and returns the borrow. -/
def subMul1Loop (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32) (j : Nat)
    (c : UInt32) (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hj : j < a.size then
    let p := r[off + j].subMul a[j] x c
    subMul1Loop (r.set (off + j) p.1 (by lia)) off a x (j + 1) p.2 (by simpa using h)
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

/-- The step of `main`'s `subMul1W`, with the borrow carried as `2³² - 1` minus it. -/
private theorem subMulB_not (z y x c : UInt32) :
    WordArray.subMulB UInt32Array z y x (~~~c) = ((z.subMul y x c).1, ~~~(z.subMul y x c).2) :=
  UInt32.subMulBiased_not z y x c

/--
The generic fold of `subMul1Step` over the limbs of `b` read from `arr`, from limb `k` on, with
the borrow `c` carried as `~~~c`, is `subMul1Loop` from limb `k` on.
-/
private theorem fold_subMul1 (arr : UInt32Array) (ao n : USize) (ha : WordArray.LoopBound arr ao n)
    (x : UInt32) (off : Nat) (b : UInt32Array.Slice) (hn : n.toNat = b.size)
    (hb : ∀ k (hk : k < b.size), b[k] = arr[ao.toNat + k]!) (ro : USize) (hro : ro.toNat = off)
    (r : UInt32Array) (k : Nat) (c : UInt32) (h : off + b.size ≤ r.size) :
    ∀ (hr : WordArray.LoopBound r ro n) (j : USize), j.toNat = k →
      WordArray.foldUInPlace n (WordArray.subMul1Step UInt32Array arr ao n ha x) r ro hr j (~~~c) =
        ((subMul1Loop r off b x k c h).1, ~~~(subMul1Loop r off b x k c h).2) := by
  induction r, k, c, h using subMul1Loop.induct off b x with
  | case1 r k c h hk p ih =>
    intro hr j hjk
    have hj : j < n := USize.lt_iff_toNat_lt.2 (by lia)
    rw [WordArray.foldUInPlace_lt _ _ _ _ _ _ _ hj, subMul1Loop, dite_eq_left hk]
    simp only [WordArray.subMul1Step, uget_slice arr ao n ha b hb j hj k hjk hk,
      uget_window r ro n hr off hro j hj k hjk (by lia), subMulB_not]
    exact (fold_congr (uset_window r ro n hr off hro j hj k hjk _ (by lia)) rfl).trans
      (ih _ _ (toNat_succ hj hjk))
  | case2 r k c h hk =>
    intro hr j hjk
    rw [WordArray.foldUInPlace_ge _ _ _ _ _ _ _ (fun e => hk (by
      have := USize.lt_iff_toNat_lt.1 e; lia)), subMul1Loop, dite_eq_right hk]

/-- `subMul1` by `main`'s generic fold, which the compiler uses in its place. -/
public def subMul1Fast (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    WordFolds.foldThen a.size.toUSize
      (WordArray.subMul1Step UInt32Array a.array a.start.toUSize a.size.toUSize
        (loopBound_window r off a a.size (Nat.le_refl _) h hs).2 x) r off.toUSize
      (loopBound_window r off a a.size (Nat.le_refl _) h hs).1 0 0xFFFFFFFF
      (fun r' _ c => (r', ~~~c))
  else
    subMul1Loop r off a x 0 0 h

@[csimp] public theorem subMul1_eq_subMul1Fast : @subMul1 = @subMul1Fast := by
  funext r off a x h
  rw [subMul1, subMul1Fast]
  split
  · rename_i hs
    obtain ⟨hn, hst⟩ := slice_eq a a.size (Nat.le_refl _) hs.2
    rw [WordArray.foldThen_eq', show (0xFFFFFFFF : UInt32) = ~~~0 from rfl,
      fold_subMul1 _ _ _ _ x off a hn (fun k hk => by
          rw [hst, UInt32Array.Slice.getElem_eq_getElem!]) _
        (toNat_off r off a.size h hs.1) r 0 0 h _ 0 rfl]
    simp
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
    obtain ⟨ih₁, ih₂⟩ := ih (by lia)
    simp only [UInt32Array.size_set] at ih₁ ih₂
    refine ⟨ih₁, ?_⟩
    have hk : off + j < r.toList.length := by simp; lia
    have hset := ofLimbs_set r.toList (off + j) p.1 hk
    have : p.1.toNat + a[j].toNat * x.toNat + c.toNat = r[off + j].toNat + p.2.toNat * 2 ^ 32 :=
      UInt32.subMul_spec r[off + j] a[j] x c
    simp only [UInt32Array.getElem_toList] at hset
    rw [UInt32Array.toList_set, ← Nat.add_assoc off j 1, Nat.mul_add 32 (off + j) 1, Nat.mul_one,
      Nat.pow_add] at ih₂
    rw [toList_copy_drop hj', ofLimbs_cons]
    generalize subMul1Loop (r.set (off + j) p.1 (by lia)) off a x (j + 1) p.2
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
    have h₂ : a.copy.toList.drop j = [] := List.drop_of_length_le (by simp; lia)
    have h₃ : j = a.size := by lia
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
    rw [ih (by lia), UInt32Array.toList_set, List.getElem?_set_ne (by lia)]
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
  exact getElem?_toList_subMul1Loop r off a x 0 0 h k (by lia)

public theorem toNat_subMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) :
    toNat (subMul1 r off a x h).1 + 2 ^ (32 * off) * (toNat a * x.toNat) =
      toNat r + 2 ^ (32 * (off + a.size)) * (subMul1 r off a x h).2.toNat := by
  simpa [subMul1, toNat] using (subMul1Loop_spec r off a x 0 0 h (Nat.zero_le _)).2

/-! ## Framing

`addMul1` and `subMul1` only touch the limbs from `off` to `off + a.size`: on `W ++ H` with those
limbs in `W`, they act on `W` and leave `H` as it is. Division keeps its quotient limbs above the
window it works on, and uses this to reason about the window alone.
-/

/-- Setting a limb of `W` in `W ++ H`. -/
public theorem set_append_left (W H : UInt32Array) (i : Nat) (x : UInt32) (h : i < W.size)
    (h' : i < (W ++ H).size) : (W ++ H).set i x h' = W.set i x h ++ H := by
  apply UInt32Array.toList_inj.1
  simp only [UInt32Array.toList_set, UInt32Array.toList_append]
  exact List.set_append_left _ _ (by simpa using h)

private theorem addMul1Loop_append (W H : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (j : Nat) (c : UInt32) (h : off + a.size ≤ W.size)
    (h' : off + a.size ≤ (W ++ H).size) :
    addMul1Loop (W ++ H) off a x j c h' =
      ((addMul1Loop W off a x j c h).1 ++ H, (addMul1Loop W off a x j c h).2) := by
  induction W, j, c, h using addMul1Loop.induct off a x with
  | case1 W j c h hj p ih =>
    rw [addMul1Loop, addMul1Loop]
    simp only [hj, ↓reduceDIte]
    have hg : (W ++ H)[off + j]'(by simp; lia) = W[off + j] :=
      UInt32Array.getElem_append_left (by lia)
    simp only [hg, set_append_left W H (off + j) _ (by lia)]
    exact ih _
  | case2 W j c h hj =>
    rw [addMul1Loop, addMul1Loop]
    simp only [hj, ↓reduceDIte]

public theorem addMul1_append (W H : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ W.size) (h' : off + a.size ≤ (W ++ H).size) :
    addMul1 (W ++ H) off a x h' = ((addMul1 W off a x h).1 ++ H, (addMul1 W off a x h).2) :=
  addMul1Loop_append W H off a x 0 0 h h'

private theorem subMul1Loop_append (W H : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (j : Nat) (c : UInt32) (h : off + a.size ≤ W.size)
    (h' : off + a.size ≤ (W ++ H).size) :
    subMul1Loop (W ++ H) off a x j c h' =
      ((subMul1Loop W off a x j c h).1 ++ H, (subMul1Loop W off a x j c h).2) := by
  induction W, j, c, h using subMul1Loop.induct off a x with
  | case1 W j c h hj p ih =>
    rw [subMul1Loop, subMul1Loop]
    simp only [hj, ↓reduceDIte]
    have hg : (W ++ H)[off + j]'(by simp; lia) = W[off + j] :=
      UInt32Array.getElem_append_left (by lia)
    simp only [hg, set_append_left W H (off + j) _ (by lia)]
    exact ih _
  | case2 W j c h hj =>
    rw [subMul1Loop, subMul1Loop]
    simp only [hj, ↓reduceDIte]

public theorem subMul1_append (W H : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ W.size) (h' : off + a.size ≤ (W ++ H).size) :
    subMul1 (W ++ H) off a x h' = ((subMul1 W off a x h).1 ++ H, (subMul1 W off a x h).2) :=
  subMul1Loop_append W H off a x 0 0 h h'

end MPN.W32
