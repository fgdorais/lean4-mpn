/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.AddDiff
public import MPN32.Sub
public import MPN32.Mul.Basecase
public import MPN32.Arch.SqrBasecase
public import MPN.Toom.Ops
public import MPN.Toom.Kernels
public import MPN32.Arch.UIntArray
public import MPN32.Basic

/-!
# The operations of the Karatsuba and Toom methods

The instance of `MPN.Toom.ToomOps` on `UInt32Array`. The linear operations are `main`'s generic
kernels (`MPN.Toom.Kernels`), in place on the windows. The middle term of Karatsuba's method and the
base cases are the kernels of this library on its slices, which return new arrays: each copies the
window it writes into a new array, applies its kernel, and copies the result back (`put`). Each
checks the bounds its kernel needs; otherwise it writes the value of its specification with
`LimbArray.writeNat`, which never happens.
-/

open ScalarArray UInt32Array MPN.Toom

namespace MPN.W32

/-- `valAt` of windows whose limbs agree. -/
private theorem valAt_shift (a b : UInt32Array) :
    ∀ (n o p : Nat), (∀ i, i < n → a[o + i]! = b[p + i]!) → a.valAt o n = b.valAt p n
  | 0, _, _, _ => by simp
  | n + 1, o, p, h => by
    rw [valAt_succ, valAt_succ, show a[o]! = b[p]! from h 0 (by lia),
      valAt_shift a b n (o + 1) (p + 1) fun i hi => by
        rw [Nat.add_right_comm, Nat.add_right_comm p]; exact h (i + 1) (by lia)]

/-! ## Windows -/

/-- The window of `len` limbs of `a` from `o` on, as a library slice. -/
@[inline] public def winL (a : UInt32Array) (o len : Nat) : UInt32Array.Slice :=
  a.toSlice o (o + len)

private theorem winL_spec {a : UInt32Array} {o len : Nat} (h : o + len ≤ a.size) :
    (winL a o len).size = len ∧ MPN.W32.toNat (winL a o len) = a.valAt o len := by
  have hs : (winL a o len).size = len := by rw [winL, UInt32Array.size_toSlice]; lia
  refine ⟨hs, ?_⟩
  rw [toNat_eq_valAt, hs, winL, UInt32Array.array_toSlice, UInt32Array.start_toSlice,
    show min o (min (o + len) a.size) = o by lia]

/-- The window in a new array of `n ≥ len` limbs, the limbs above zero. -/
@[inline] public def ext (a : UInt32Array) (o len n : Nat) : UInt32Array :=
  copyPadded (winL a o len) n

private theorem ext_spec {a : UInt32Array} {o len n : Nat} (h : o + len ≤ a.size) (hn : len ≤ n) :
    (ext a o len n).size = n ∧ MPN.W32.toNat (ext a o len n) = a.valAt o len := by
  obtain ⟨s₁, s₂⟩ := winL_spec h
  exact ⟨size_copyPadded _ _ (by lia), by rw [ext, toNat_copyPadded, s₂]⟩

/-- The value of an array of `n` limbs. -/
private theorem toNat_arr {r : UInt32Array} {n : Nat} (h : r.size = n) :
    MPN.W32.toNat r = r.valAt 0 n := by
  rw [toNat_array_eq_valAt, h]

/-- Writes the low `len` limbs of `r` into the limbs of `d` from `o` on. -/
@[inline] public def put (d : UInt32Array) (o len : Nat) (r : UInt32Array) : UInt32Array :=
  r.copySlice 0 d o len

private theorem getElem!_put {d r : UInt32Array} {o len : Nat} (h : o + len ≤ d.size)
    (hr : len ≤ r.size) (i : Nat) :
    (put d o len r)[i]! = if o ≤ i ∧ i < o + len then r[i - o]! else d[i]! := by
  unfold put
  have hsz : (r.copySlice 0 d o len).size = d.size := by
    rw [UInt32Array.size_copySlice]; lia
  by_cases hi : i < d.size
  · rw [getElem!_eq_getElem _ _ (by rw [hsz]; exact hi), UInt32Array.getElem_copySlice]
    have hmin : min o d.size = o := by lia
    have hmin2 : min len (r.size - 0) = len := by lia
    simp only [hmin, hmin2]
    split
    · rw [ite_eq_right_iff.2 (fun _ => by exfalso; lia), getElem!_eq_getElem _ _ hi]
    · split
      · rw [ite_eq_left_iff.2 (fun _ => by exfalso; lia), getElem!_eq_getElem _ _ (by lia)]
        simp
      · rw [ite_eq_right_iff.2 (fun _ => by exfalso; lia), getElem!_eq_getElem _ _ hi]
  · rw [getElem!_neg (r.copySlice 0 d o len) i (by rw [hsz]; exact hi), getElem!_neg d i hi,
      ite_eq_right_iff.2 (fun _ => by exfalso; lia)]

private theorem put_spec {d r : UInt32Array} {o len : Nat} (h : o + len ≤ d.size)
    (hr : len ≤ r.size) :
    Writes (put d o len r) d o len ∧ (put d o len r).valAt o len = r.valAt 0 len := by
  refine ⟨⟨by show (put d o len r).size = d.size; rw [put, UInt32Array.size_copySlice]; lia,
    fun i hi => ?_⟩, ?_⟩
  · show (put d o len r)[i]! = d[i]!
    rw [getElem!_put h hr]; simp only [show ¬(o ≤ i ∧ i < o + len) by lia, ↓reduceIte]
  · exact valAt_shift _ _ len o 0 fun i hi => by
      rw [getElem!_put h hr, ite_eq_left_iff.2 (fun h' => by exfalso; exact h' (by lia)),
        Nat.add_sub_cancel_left, Nat.zero_add]

/-- The window in a new array of `len` limbs, copied with one `memcpy`. -/
@[inline] public def cut (a : UInt32Array) (o len : Nat) : UInt32Array := a.extract o (o + len)

private theorem cut_spec {a : UInt32Array} {o len : Nat} (h : o + len ≤ a.size) :
    (cut a o len).size = len ∧ MPN.W32.toNat (cut a o len) = a.valAt o len := by
  have hs : (cut a o len).size = len := by rw [cut, UInt32Array.size_extract]; lia
  refine ⟨hs, ?_⟩
  rw [cut, toNat_extract, show o + len - o = len by lia]

/-- The fallback: the value of the specification, when it fits. -/
private theorem fallback (d : UInt32Array) (o len v : Nat) (h : o + len ≤ d.size)
    (hv : v < 2 ^ (32 * len)) :
    Writes (LimbArray.writeNat d o len v) d o len ∧
      LimbArray.valAt (LimbArray.writeNat d o len v) o len = v :=
  ⟨writes_writeNat .., by rw [LimbArray.valAt_writeNat _ _ _ _ h]; exact Nat.mod_eq_of_lt hv⟩

/-! ## The operations -/

/--
The middle term of Karatsuba's method, by `addDiffInto` on a copy of the window with two more
limbs, which holds the sum.
-/
public def midT (d : UInt32Array) (o k n : Nat) (t : UInt32Array) : UInt32Array :=
  if o + n ≤ d.size ∧ t.size = k + k + 2 ∧ 3 * k ≤ n ∧ n ≤ 4 * k + 2 then
    let r := addDiffInto (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
      (ext d (o + (k + k)) (n - (k + k)) (n - (k + k)))
    if r.size = n + 2 then put d o n r
    else LimbArray.writeNat d o n (d.valAt o n)
  else
    LimbArray.writeNat d o n (d.valAt o (k + k) +
      2 ^ (32 * k) * (t.valAt 0 (k + k + 2) - d.valAt o (k + k) -
        d.valAt (o + (k + k)) (n - (k + k))) +
      2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)))

/-- `x y`, with the rows over the shorter operand. -/
public def mulBaseT (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat) (y : UInt32Array)
    (yo yl : Nat) : UInt32Array :=
  if o + (xl + yl) ≤ d.size ∧ xo + xl ≤ x.size ∧ yo + yl ≤ y.size then
    put d o (xl + yl)
      (if yl ≤ xl then mulBasecase (winL y yo yl) (winL x xo xl)
       else mulBasecase (winL x xo xl) (winL y yo yl))
  else LimbArray.writeNat d o (xl + yl) (x.valAt xo xl * y.valAt yo yl)

/-- `x²`. -/
public def sqrBaseT (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat) : UInt32Array :=
  if o + (xl + xl) ≤ d.size ∧ xo + xl ≤ x.size then
    put d o (xl + xl)
      (if 2 ≤ xl then sqrBasecase (winL x xo xl) else mulBasecase (winL x xo xl) (winL x xo xl))
  else LimbArray.writeNat d o (xl + xl) (x.valAt xo xl * x.valAt xo xl)

/-! ## Their specifications -/

private theorem toNat_toUInt32 {v : Nat} (h : v < 2 ^ 32) : v.toUInt32.toNat = v := by
  rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The result of a kernel of `len` limbs with value `V`, written into the window. -/
private theorem put_val {d r : UInt32Array} {o len V : Nat} (h : o + len ≤ d.size)
    (hr : r.size = len) (hv : MPN.W32.toNat r = V) :
    Writes (put d o len r) d o len ∧ (put d o len r).valAt o len = V := by
  obtain ⟨w, v⟩ := put_spec h (Nat.le_of_eq hr.symm)
  exact ⟨w, by rw [v, ← toNat_arr hr, hv]⟩

public theorem midT_spec (d : UInt32Array) (o k n : Nat) (t : UInt32Array) (h : o + n ≤ d.size) :
    Writes (midT d o k n t) d o n ∧
      ∀ Z₁, t.valAt 0 (k + k + 2) = d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) →
        d.valAt o (k + k) + 2 ^ (32 * k) * Z₁ +
            2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) < 2 ^ (32 * n) →
        (midT d o k n t).valAt o n = d.valAt o (k + k) + 2 ^ (32 * k) * Z₁ +
          2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
  rw [midT]
  split
  · rename_i hg
    obtain ⟨-, ht, h₃, h₄⟩ := hg
    dsimp only
    split
    · rename_i hr
      obtain ⟨w, v⟩ := put_spec (r := addDiffInto (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
        (ext d (o + (k + k)) (n - (k + k)) (n - (k + k)))) h (by lia)
      refine ⟨w, fun Z₁ hT hlt => ?_⟩
      obtain ⟨r₁, r₂⟩ := ext_spec (n := n + 2) h (by lia)
      obtain ⟨z₁, z₂⟩ := ext_spec (n := k + k) (o := o) (len := k + k) (a := d) (by lia) (Nat.le_refl _)
      obtain ⟨y₁, y₂⟩ := ext_spec (n := n - (k + k)) (o := o + (k + k)) (len := n - (k + k)) (a := d)
        (by lia) (Nat.le_refl _)
      have hR : d.valAt o n = d.valAt o (k + k) +
          2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
        rw [← valAt_add, show k + k + (n - (k + k)) = n by lia]
      have hT' : MPN.W32.toNat t = t.valAt 0 (k + k + 2) := toNat_arr ht
      obtain ⟨-, a₂⟩ := addDiffInto_spec (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
        (ext d (o + (k + k)) (n - (k + k)) (n - (k + k))) (by rw [ht, r₁]; lia)
        (by rw [z₁, ht]; lia) (by rw [y₁, ht]; lia) (by rw [z₂, y₂, hT', hT]; lia)
        (by
          rw [r₂, z₂, y₂, hT', hT, r₁, hR,
            show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) -
              d.valAt o (k + k) - d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
          have : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 2)) := Nat.pow_le_pow_right (by decide) (by lia)
          lia)
      rw [r₂, z₂, y₂, hT', hT,
        show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) -
          d.valAt o (k + k) - d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia, hR] at a₂
      rw [v, valAt_mod _ 0 (show n ≤ n + 2 by lia), ← toNat_arr hr, a₂,
        Nat.mod_eq_of_lt (by lia)]
      lia
    · -- The size is always `n + 2`, so this does not happen.
      refine ⟨writes_writeNat .., fun Z₁ hT hlt => ?_⟩
      exfalso
      obtain ⟨r₁, r₂⟩ := ext_spec (n := n + 2) h (by lia)
      obtain ⟨z₁, z₂⟩ := ext_spec (n := k + k) (o := o) (len := k + k) (a := d) (by lia) (Nat.le_refl _)
      obtain ⟨y₁, y₂⟩ := ext_spec (n := n - (k + k)) (o := o + (k + k)) (len := n - (k + k)) (a := d)
        (by lia) (Nat.le_refl _)
      have hR : d.valAt o n = d.valAt o (k + k) +
          2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
        rw [← valAt_add, show k + k + (n - (k + k)) = n by lia]
      have hT' : MPN.W32.toNat t = t.valAt 0 (k + k + 2) := toNat_arr ht
      obtain ⟨a₁, -⟩ := addDiffInto_spec (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
        (ext d (o + (k + k)) (n - (k + k)) (n - (k + k))) (by rw [ht, r₁]; lia)
        (by rw [z₁, ht]; lia) (by rw [y₁, ht]; lia) (by rw [z₂, y₂, hT', hT]; lia)
        (by
          rw [r₂, z₂, y₂, hT', hT, r₁, hR,
            show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) -
              d.valAt o (k + k) - d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
          have : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 2)) := Nat.pow_le_pow_right (by decide) (by lia)
          lia)
      rename_i hr
      exact hr (a₁.trans r₁)
  · refine ⟨writes_writeNat .., fun Z₁ hT hlt => ?_⟩
    rw [show (LimbArray.writeNat d o n _).valAt o n = _ from LimbArray.valAt_writeNat _ _ _ _ h, hT,
      show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) - d.valAt o (k + k) -
        d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
    exact Nat.mod_eq_of_lt hlt

private theorem lt_mul (x y : UInt32Array) (xo xl yo yl : Nat) :
    x.valAt xo xl * y.valAt yo yl < 2 ^ (32 * (xl + yl)) := by
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)

public theorem mulBaseT_spec (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat)
    (y : UInt32Array) (yo yl : Nat) (h : o + (xl + yl) ≤ d.size) :
    Writes (mulBaseT d o x xo xl y yo yl) d o (xl + yl) ∧
      (mulBaseT d o x xo xl y yo yl).valAt o (xl + yl) = x.valAt xo xl * y.valAt yo yl := by
  rw [mulBaseT]
  split
  · rename_i hg
    obtain ⟨x₁, x₂⟩ := winL_spec hg.2.1
    obtain ⟨y₁, y₂⟩ := winL_spec hg.2.2
    by_cases hyx : yl ≤ xl
    · simp only [hyx, ↓reduceIte]
      exact put_val h (by rw [size_mulBasecase, x₁, y₁]; lia)
        (by rw [toNat_mulBasecase, x₂, y₂, Nat.mul_comm])
    · simp only [hyx, ↓reduceIte]
      exact put_val h (by rw [size_mulBasecase, x₁, y₁]) (by rw [toNat_mulBasecase, x₂, y₂])
  · exact fallback _ _ _ _ h (lt_mul ..)

public theorem sqrBaseT_spec (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat)
    (h : o + (xl + xl) ≤ d.size) :
    Writes (sqrBaseT d o x xo xl) d o (xl + xl) ∧
      (sqrBaseT d o x xo xl).valAt o (xl + xl) = x.valAt xo xl * x.valAt xo xl := by
  rw [sqrBaseT]
  split
  · rename_i hg
    obtain ⟨x₁, x₂⟩ := winL_spec hg.2
    by_cases h2 : 2 ≤ xl
    · simp only [h2, ↓reduceIte]
      exact put_val h (by rw [(sqrBasecase_spec _).1, x₁]) (by rw [(sqrBasecase_spec _).2, x₂])
    · simp only [h2, ↓reduceIte]
      exact put_val h (by rw [size_mulBasecase, x₁]) (by rw [toNat_mulBasecase, x₂])
  · exact fallback _ _ _ _ h (lt_mul ..)

/--
The operations of `ToomOps` on 32-bit limbs beyond `main`'s kernels: Karatsuba's middle term and
the products below the thresholds. `MPN.Toom.toomOpsW` gives the rest.
-/
public instance toomBase32 : ToomBase UInt32Array UInt32 where
  w_ge := by show 32 ≤ 32; decide
  mid := midT
  mid_spec := midT_spec
  mulBase := mulBaseT
  mulBase_spec := mulBaseT_spec
  sqrBase := sqrBaseT
  sqrBase_spec := sqrBaseT_spec

end MPN.W32
