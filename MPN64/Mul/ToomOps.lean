/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Bits
public import MPN64.Arch.SqrBasecase
public import MPN.Toom.Ops
public import MPN.Toom.Kernels

/-!
# The operations of the Karatsuba and Toom methods

The instance of `MPN.Toom.ToomOps` on `UInt64Array`: the linear operations are `main`'s generic
kernels (`MPN.Toom.Kernels`), and so is the middle term of Karatsuba's method (`MPN.Toom.Mid`);
the base cases are the kernels of this library on `USlice`s. Each of these checks that the indices
of its windows fit in a `USize` and that the kernel's conditions hold; otherwise it writes the value
of its specification with `LimbArray.writeNat`, which never happens.
-/

open ScalarArray UInt64Array MPN.Toom

namespace MPN.W64

/-! ## Windows as slices -/

/-- The window of `len` limbs of `a` from `o` on, as a `USlice`. -/
@[inline] public def winS (a : UInt64Array) (o len : Nat) : USlice :=
  a.uslice o.toUSize (o + len).toUSize

private theorem toNat_toUSize {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a := by
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt h]

private theorem winS_spec (a : UInt64Array) (o len : Nat) (hS : a.size < USize.size)
    (h : o + len ≤ a.size) :
    (winS a o len).array = a ∧ (winS a o len).start.toNat = o ∧
      (winS a o len).size.toNat = len ∧ (winS a o len).toNat = a.valAt o len := by
  have h₁ := toNat_toUSize (a := o) (by lia)
  have h₂ := toNat_toUSize (a := o + len) (by lia)
  have hs := uslice_start a o.toUSize (o + len).toUSize
    (USize.le_iff_toNat_le.2 (by rw [h₁, h₂]; lia)) (by rw [h₂]; exact h)
  have ht := uslice_stop a o.toUSize (o + len).toUSize (by rw [h₂]; exact h)
  have hz : (winS a o len).size.toNat = len := by
    rw [winS, USlice.toNat_size, hs, ht, h₁, h₂]; lia
  refine ⟨rfl, by rw [winS, hs, h₁], hz, ?_⟩
  rw [USlice.toNat_eq_valAt, hz, show (winS a o len).start.toNat = o by rw [winS, hs, h₁]]
  rfl

/--
`a.size < USize.size`, as `a.usize.toNat = a.size`: a comparison of small numbers, where
`USize.size` would be a big one.
-/
public abbrev Fits (a : UInt64Array) : Prop := a.usize.toNat = a.size

public theorem Fits.lt {a : UInt64Array} (h : Fits a) : a.size < USize.size :=
  h ▸ a.usize.toNat_lt_size

/-- The fallback: the value of the specification, when it fits. -/
private theorem fallback (d : UInt64Array) (o len v : Nat) (h : o + len ≤ d.size)
    (hv : v < 2 ^ (64 * len)) :
    Writes (LimbArray.writeNat d o len v) d o len ∧
      LimbArray.valAt (LimbArray.writeNat d o len v) o len = v :=
  ⟨writes_writeNat .., by rw [LimbArray.valAt_writeNat _ _ _ _ h]; exact Nat.mod_eq_of_lt hv⟩

/-- A kernel's result as writes within a window. -/
private theorem writes_of {d' d : UInt64Array} {o len : Nat} (h₁ : d'.size = d.size)
    (h₂ : ∀ i, (i < o ∨ o + len ≤ i) → d'[i]! = d[i]!) : Writes d' d o len := ⟨h₁, h₂⟩

/-! ## The operations -/

/-- `x y`. -/
public def mulBaseT (d : UInt64Array) (o : Nat) (x : UInt64Array) (xo xl : Nat) (y : UInt64Array)
    (yo yl : Nat) : UInt64Array :=
  if Fits d ∧ Fits x ∧ Fits y ∧ o + (xl + yl) ≤ d.size ∧
      xo + xl ≤ x.size ∧ yo + yl ≤ y.size ∧ 0 < yl then
    mulBasecase (winS d o (xl + yl)) (winS x xo xl) (winS y yo yl)
  else LimbArray.writeNat d o (xl + yl) (x.valAt xo xl * y.valAt yo yl)

/-- `x²`. -/
public def sqrBaseT (d : UInt64Array) (o : Nat) (x : UInt64Array) (xo xl : Nat) : UInt64Array :=
  if Fits d ∧ Fits x ∧ o + (xl + xl) ≤ d.size ∧ xo + xl ≤ x.size ∧
      0 < xl then
    sqrBasecase (winS d o (xl + xl)) (winS x xo xl)
  else LimbArray.writeNat d o (xl + xl) (x.valAt xo xl * x.valAt xo xl)

/-! ## Their specifications -/

private theorem toNat_toUInt64 {v : Nat} (h : v < 2 ^ 64) : v.toUInt64.toNat = v := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

private theorem le_usize {a b : USlice} {x y : Nat} (ha : a.size.toNat = x) (hb : b.size.toNat = y)
    (h : y ≤ x) : b.size ≤ a.size := USize.le_iff_toNat_le.2 (by lia)

private theorem lt_mul (x y : UInt64Array) (xo xl yo yl : Nat) :
    x.valAt xo xl * y.valAt yo yl < 2 ^ (64 * (xl + yl)) := by
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)

public theorem mulBaseT_spec (d : UInt64Array) (o : Nat) (x : UInt64Array) (xo xl : Nat)
    (y : UInt64Array) (yo yl : Nat) (h : o + (xl + yl) ≤ d.size) :
    Writes (mulBaseT d o x xo xl y yo yl) d o (xl + yl) ∧
      (mulBaseT d o x xo xl y yo yl).valAt o (xl + yl) = x.valAt xo xl * y.valAt yo yl := by
  rw [mulBaseT]
  split
  · rename_i hg
    obtain ⟨hd, hx, hy, -, hxo, hyo, hyl⟩ := hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o (xl + yl) hd.lt h
    obtain ⟨x₁, x₂, x₃, x₄⟩ := winS_spec x xo xl hx.lt hxo
    obtain ⟨y₁, y₂, y₃, y₄⟩ := winS_spec y yo yl hy.lt hyo
    have := valAt_mulBasecase (winS d o (xl + yl)) (winS x xo xl) (winS y yo yl)
      (USize.lt_iff_toNat_lt.2 (by rw [y₃, USize.toNat_zero]; exact hyl)) (by rw [d₃, x₃, y₃] <;> lia)
    rw [d₂, x₃, y₃, x₄, y₄] at this
    refine ⟨writes_of (by rw [size_mulBasecase, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_mulBasecase _ _ _ i (by rw [d₂, x₃, y₃]; lia), d₁]
  · exact fallback _ _ _ _ h (lt_mul ..)

public theorem sqrBaseT_spec (d : UInt64Array) (o : Nat) (x : UInt64Array) (xo xl : Nat)
    (h : o + (xl + xl) ≤ d.size) :
    Writes (sqrBaseT d o x xo xl) d o (xl + xl) ∧
      (sqrBaseT d o x xo xl).valAt o (xl + xl) = x.valAt xo xl * x.valAt xo xl := by
  rw [sqrBaseT]
  split
  · rename_i hg
    obtain ⟨hd, hx, -, hxo, hxl⟩ := hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o (xl + xl) hd.lt h
    obtain ⟨x₁, x₂, x₃, x₄⟩ := winS_spec x xo xl hx.lt hxo
    have := valAt_sqrBasecase (winS d o (xl + xl)) (winS x xo xl)
      (USize.lt_iff_toNat_lt.2 (by rw [x₃, USize.toNat_zero]; exact hxl)) (by rw [d₃, x₃]; lia)
    rw [d₂, x₃, x₄, show 2 * xl = xl + xl by lia] at this
    refine ⟨writes_of (by rw [size_sqrBasecase, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_sqrBasecase _ _ i (by rw [d₂, x₃]; lia), d₁]
  · exact fallback _ _ _ _ h (lt_mul ..)

/--
The operations of `ToomOps` on 64-bit limbs beyond `main`'s kernels: Karatsuba's middle term and
the products below the thresholds. `MPN.Toom.toomOpsW` gives the rest.
-/
public instance toomBase64 : ToomBase UInt64Array UInt64 where
  w_ge := by show 32 ≤ 64; decide
  mid := WordArray.midW
  mid_spec := WordArray.midW_spec
  mulBase := mulBaseT
  mulBase_spec := mulBaseT_spec
  sqrBase := sqrBaseT
  sqrBase_spec := sqrBaseT_spec

end MPN.W64
