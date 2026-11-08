/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Basic
public import MPN32.Arch.UInt
public import MPN32.Arch.UIntArray
public import MPN.MulLimbW
public import MPN.Toom.Ops

/-!
# Multiplication by a limb

The linear primitives of multiplication, after GMP's `mpn_mul_1` and `mpn_addmul_1`, by `main`'s
generic passes (`MPN.MulLimbW`), which update an array in place with one exclusivity check and
`USize` indices. Neither trims its result.

* `addMul1 r off a x` adds `a x` to the limbs of `r` from `off` on, and returns the carry limb.
* `addMul1SetW r off arr st n x` adds the `n` limbs of `arr` from `st` on times `x` to `r` from
  `off` on and stores the carry at `off + n`, inside the fold: the step of the schoolbook loops,
  where that limb is still zero. `addMul1Set` is it on a slice, and `addMul1SetPre` on the first
  `n` limbs of a slice, read from its array without a slice object.
* `mul1` and `mulRow` multiply into zeros.

Each pass needs the arrays to fit in a `USize`, which every array in memory does; otherwise it
writes the value of its specification with `writeNat`, which never happens.
-/

open ScalarArray MPN.Toom

namespace MPN.W32

/-- The bounds of the generic passes over `n` limbs of `arr` from `st`, into `r` from `off`. -/
public theorem loopBound_win (r : UInt32Array) (off : Nat) (arr : UInt32Array) (st n : Nat)
    (h : off + n ≤ r.size) (ha : st + n ≤ arr.size)
    (hs : r.size < 4294967295 ∧ arr.size < 4294967295) :
    WordArray.LoopBound r off.toUSize n.toUSize ∧ WordArray.LoopBound arr st.toUSize n.toUSize := by
  have := USize.le_size
  simp only [WordArray.LoopBound]
  rw [toNat_toUSize (by lia), toNat_toUSize (by lia), toNat_toUSize (by lia)]
  exact ⟨⟨h, by lia⟩, ⟨ha, by lia⟩⟩

/-- The limbs of a slice lie in its array. -/
private theorem slice_bound (a : UInt32Array.Slice) : a.start + a.size ≤ a.array.size := by
  have := a.stop_le_array_size; have := a.start_le_stop; have := a.size_eq; lia

/-- A window plus a window times a limb fits in one more limb. -/
private theorem add_mul_lt {V A x P B : Nat} (hV : V < P) (hA : A < P) (hx : x < B) :
    V + A * x < P * B := by
  have e₁ : A * x ≤ (P - 1) * x := Nat.mul_le_mul_right _ (by lia)
  have e₂ : (P - 1) * x + (P - 1) = (P - 1) * (x + 1) := by rw [Nat.mul_succ]
  have e₃ : (P - 1) * (x + 1) ≤ (P - 1) * B := Nat.mul_le_mul_left _ hx
  have e₄ : (P - 1) * B < P * B := Nat.mul_lt_mul_of_pos_right (by lia) (by lia)
  generalize A * x = u at *
  generalize (P - 1) * x = v at *
  generalize (P - 1) * (x + 1) = w at *
  generalize (P - 1) * B = s at *
  generalize P * B = t at *
  lia

/-! ## Adding a multiple -/

/-- `r + 2^(32 off) a x` in the limbs of `r` from `off` on, and the carry limb above them. -/
public def addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) : UInt32Array × UInt32 :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 then
    WordArray.addMul1W r off.toUSize a.array a.start.toUSize a.size.toUSize x 0
      (loopBound_win r off a.array a.start a.size h (slice_bound a) hs).1
      (loopBound_win r off a.array a.start a.size h (slice_bound a) hs).2
  else
    (LimbArray.writeNat r off a.size (r.valAt off a.size + toNat a * x.toNat),
      ((r.valAt off a.size + toNat a * x.toNat) / 2 ^ (32 * a.size)).toUInt32)

/-- The window of `addMul1` and its carry. -/
public theorem addMul1_spec (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size ≤ r.size) :
    Writes (addMul1 r off a x h).1 r off a.size ∧
      (addMul1 r off a x h).1.valAt off a.size +
          2 ^ (32 * a.size) * (addMul1 r off a x h).2.toNat =
        r.valAt off a.size + toNat a * x.toNat := by
  unfold addMul1
  split
  · rename_i hs
    have hb := loopBound_win r off a.array a.start a.size h (slice_bound a) hs
    obtain ⟨s₁, s₂, s₃⟩ := WordArray.addMul1W_spec r off.toUSize a.array a.start.toUSize
      a.size.toUSize x 0 hb.1 hb.2
    have e₁ := toNat_toUSize (n := off) (by have := USize.le_size; lia)
    have e₂ := toNat_toUSize (n := a.size) (by have := USize.le_size; have := slice_bound a; lia)
    have e₃ := toNat_toUSize (n := a.start) (by have := USize.le_size; have := slice_bound a; lia)
    simp only [e₁, e₂, e₃] at s₂ s₃
    refine ⟨⟨s₁, s₂⟩, ?_⟩
    rw [toNat_eq_valAt]
    exact s₃
  · have hv : r.valAt off a.size + toNat a * x.toNat < 2 ^ (32 * a.size) * 2 ^ 32 :=
      add_mul_lt (UInt32Array.valAt_lt r off a.size) (toNat_lt a) x.toNat_lt
    refine ⟨writes_writeNat .., ?_⟩
    rw [show (LimbArray.writeNat r off a.size _).valAt off a.size = _ from
      LimbArray.valAt_writeNat _ _ _ _ h]
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hv)]
    exact Nat.mod_add_div ..

@[simp] public theorem size_addMul1 (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size ≤ r.size) : (addMul1 r off a x h).1.size = r.size :=
  (addMul1_spec r off a x h).1.1

/-! ## Adding a multiple and storing the carry -/

/--
`addMul1` of the `n` limbs of `arr` from `st` on, followed by writing the carry limb at `off + n`,
over the limb there, inside the fold, so that no pair of the new limbs and the carry is allocated.
-/
@[inline] public def addMul1SetW (r : UInt32Array) (off : Nat) (arr : UInt32Array) (st n : Nat)
    (x : UInt32) (h : off + n < r.size) (ha : st + n ≤ arr.size) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ arr.size < 4294967295 then
    WordFolds.foldThen n.toUSize
      (WordArray.addMul1Step UInt32Array arr st.toUSize n.toUSize
        (loopBound_win r off arr st n (by lia) ha hs).2 x) r off.toUSize
      (loopBound_win r off arr st n (by lia) ha hs).1 0 0
      (fun r' e c => r'.set (off + n) c (by have : r'.size = r.size := e; lia))
  else
    LimbArray.writeNat r off (n + 1) (r.valAt off (n + 1) + arr.valAt st n * x.toNat)

@[simp] public theorem size_addMul1SetW (r : UInt32Array) (off : Nat) (arr : UInt32Array)
    (st n : Nat) (x : UInt32) (h : off + n < r.size) (ha : st + n ≤ arr.size) :
    (addMul1SetW r off arr st n x h ha).size = r.size := by
  unfold addMul1SetW
  split
  · rw [WordFolds.foldThen_eq, WordArray.foldUInPlaceThen, UInt32Array.size_set]
    exact WordArray.size_foldUInPlace (A := UInt32Array) ..
  · exact LimbArray.size_writeNat (A := UInt32Array) ..

/-- Storing the carry above a window written by a pass. -/
private theorem set_carry (r : UInt32Array) (off n V : Nat) (q : UInt32Array × UInt32)
    (hq₁ : q.1.size = r.size) (hq₂ : ∀ i, (i < off ∨ off + n ≤ i) → q.1[i]! = r[i]!)
    (hq₃ : q.1.valAt off n + 2 ^ (32 * n) * q.2.toNat = r.valAt off n + V)
    (hr1 : r.valAt off (n + 1) = r.valAt off n) (hp : off + n < q.1.size) :
    Writes (q.1.set (off + n) q.2 hp) r off (n + 1) ∧
      (q.1.set (off + n) q.2 hp).valAt off (n + 1) = r.valAt off (n + 1) + V := by
  refine ⟨⟨by show (q.1.set _ _ _).size = r.size; rw [UInt32Array.size_set, hq₁],
    fun i hi => ?_⟩, ?_⟩
  · show (q.1.set _ _ _)[i]! = r[i]!
    rw [UInt32Array.getElem!_set, ite_eq_right (by lia), hq₂ i (by lia)]
  · rw [UInt32Array.valAt_add, UInt32Array.valAt_one, UInt32Array.getElem!_set,
      ite_eq_left rfl, hr1, UInt32Array.valAt_congr (b := q.1) _ fun i _ _ => by
        rw [UInt32Array.getElem!_set, ite_eq_right (by lia)]]
    lia

/-- The window of `addMul1SetW`, when the limb at `off + n` is zero. -/
private theorem addMul1SetW_spec (r : UInt32Array) (off : Nat) (arr : UInt32Array) (st n : Nat)
    (x : UInt32) (h : off + n < r.size) (ha : st + n ≤ arr.size) (hz : r[off + n] = 0) :
    Writes (addMul1SetW r off arr st n x h ha) r off (n + 1) ∧
      (addMul1SetW r off arr st n x h ha).valAt off (n + 1) =
        r.valAt off (n + 1) + arr.valAt st n * x.toNat := by
  have hr1 : r.valAt off (n + 1) = r.valAt off n := by
    rw [UInt32Array.valAt_add, UInt32Array.valAt_one, UInt32Array.getElem!_eq_getElem _ _ h, hz,
      UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero]
  unfold addMul1SetW
  split
  · rename_i hs
    have hb := loopBound_win r off arr st n (by lia) ha hs
    rw [WordFolds.foldThen_eq, WordArray.foldUInPlaceThen]
    obtain ⟨f₁, f₂, f₃⟩ := WordArray.addMul1Fold_spec arr st.toUSize n.toUSize hb.2 x r
      off.toUSize hb.1 0 0
    have e₁ := toNat_toUSize (n := off) (by have := USize.le_size; lia)
    have e₂ := toNat_toUSize (n := n) (by have := USize.le_size; lia)
    have e₃ := toNat_toUSize (n := st) (by have := USize.le_size; lia)
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₁, e₂, e₃] at f₂ f₃
    exact set_carry r off n _ _ f₁ f₂ f₃ hr1 _
  · rw [hr1]
    have hv : r.valAt off n + arr.valAt st n * x.toNat < 2 ^ (32 * (n + 1)) := by
      rw [Nat.mul_succ, Nat.pow_add]
      exact add_mul_lt (UInt32Array.valAt_lt r off n) (UInt32Array.valAt_lt arr st n) x.toNat_lt
    refine ⟨writes_writeNat .., ?_⟩
    rw [show (LimbArray.writeNat r off (n + 1) _).valAt off (n + 1) = _ from
      LimbArray.valAt_writeNat _ _ _ _ (show off + (n + 1) ≤ r.size by lia)]
    exact Nat.mod_eq_of_lt hv

/-- `addMul1SetW` adds when the limb at `off + n` is zero. -/
public theorem toNat_addMul1SetW (r : UInt32Array) (off : Nat) (arr : UInt32Array) (st n : Nat)
    (x : UInt32) (h : off + n < r.size) (ha : st + n ≤ arr.size) (hz : r[off + n] = 0) :
    (addMul1SetW r off arr st n x h ha).size = r.size ∧
      toNat (addMul1SetW r off arr st n x h ha) =
        toNat r + 2 ^ (32 * off) * (arr.valAt st n * x.toNat) := by
  obtain ⟨hw, hv⟩ := addMul1SetW_spec r off arr st n x h ha hz
  have hwh := hw.valAt_whole (by show off + (n + 1) ≤ r.size; lia)
  have hs : (addMul1SetW r off arr st n x h ha).size = r.size := hw.1
  refine ⟨hs, ?_⟩
  change UInt32Array.valAt _ 0 (addMul1SetW r off arr st n x h ha).size +
      2 ^ (32 * off) * r.valAt off (n + 1) = r.valAt 0 r.size +
        2 ^ (32 * off) * (addMul1SetW r off arr st n x h ha).valAt off (n + 1) at hwh
  rw [hv, Nat.mul_add] at hwh
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt]
  lia

/-- `addMul1SetW` on the limbs of a slice. -/
public def addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (x : UInt32)
    (h : off + a.size < r.size) : UInt32Array :=
  addMul1SetW r off a.array a.start a.size x h (slice_bound a)

@[simp] public theorem size_addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size < r.size) : (addMul1Set r off a x h).size = r.size := by
  rw [addMul1Set, size_addMul1SetW]

public theorem toNat_addMul1Set (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (x : UInt32) (h : off + a.size < r.size) (hz : r[off + a.size] = 0) :
    toNat (addMul1Set r off a x h) = toNat r + 2 ^ (32 * off) * (toNat a * x.toNat) := by
  rw [addMul1Set, (toNat_addMul1SetW r off a.array a.start a.size x h (slice_bound a) hz).2,
    toNat_eq_valAt a]

/--
`addMul1SetW` on the first `n` limbs of a slice, read from its array directly, without a slice
object, for the rows of the schoolbook square.
-/
public def addMul1SetPre (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice) (n : Nat)
    (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) : UInt32Array :=
  addMul1SetW r off a.array a.start n x h (by have := slice_bound a; lia)

@[simp] public theorem size_addMul1SetPre (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (n : Nat) (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) :
    (addMul1SetPre r off a n x hn h).size = r.size := by
  rw [addMul1SetPre, size_addMul1SetW]

public theorem toNat_addMul1SetPre (r : UInt32Array) (off : Nat) (a : UInt32Array.Slice)
    (n : Nat) (x : UInt32) (hn : n ≤ a.size) (h : off + n < r.size) (hz : r[off + n] = 0) :
    (addMul1SetPre r off a n x hn h).size = r.size ∧
      toNat (addMul1SetPre r off a n x hn h) =
        toNat r + 2 ^ (32 * off) * (a.array.valAt a.start n * x.toNat) :=
  toNat_addMul1SetW r off a.array a.start n x h _ hz

/-! ## Into zeros -/

/-- `a * x` as `a.size` limbs and a carry limb, like GMP's `mpn_mul_1`: `addMul1` into zeros. -/
public def mul1 (a : UInt32Array.Slice) (x : UInt32) : UInt32Array × UInt32 :=
  addMul1 (.replicate a.size 0) 0 a x (by simp)

@[simp] public theorem size_mul1 (a : UInt32Array.Slice) (x : UInt32) :
    (mul1 a x).1.size = a.size := by
  simp [mul1]

public theorem toNat_mul1 (a : UInt32Array.Slice) (x : UInt32) :
    toNat (mul1 a x).1 + 2 ^ (32 * a.size) * (mul1 a x).2.toNat = toNat a * x.toNat := by
  obtain ⟨hw, hv⟩ := addMul1_spec (.replicate a.size 0) 0 a x (by simp)
  have hs : (mul1 a x).1.size = a.size := by simp [mul1]
  rw [toNat_array_eq_valAt, hs]
  simpa [mul1] using hv

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

end MPN.W32
