/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.Bits
public import MPN64.Mul.KaratsubaMid
public import MPN64.Sqr.Basecase
public import MPN.Toom.Ops
public import MPN.Toom.Kernels

/-!
# The operations of the Karatsuba and Toom methods

The instance of `MPN.Toom.ToomOps` on `UInt64Array`: the linear operations are `main`'s generic
kernels (`MPN.Toom.Kernels`); the middle term of Karatsuba's method and the base cases are the
kernels of this library on `USlice`s. Each of these checks that the indices of its windows fit in
a `USize` and that the kernel's conditions hold; otherwise it writes the value of its
specification with `LimbArray.writeNat`, which never happens.
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

/-- The middle term of Karatsuba's method. -/
public def midT (d : UInt64Array) (o k n : Nat) (t : UInt64Array) : UInt64Array :=
  if Fits d ∧ o + n ≤ d.size ∧ 3 * k ≤ n ∧ n ≤ 4 * k + 2 ∧ t.size = k + k + 2 ∧
      2 ≤ k then
    karatsubaMid d o.toUSize k.toUSize n.toUSize t
  else
    LimbArray.writeNat d o n (d.valAt o (k + k) +
      2 ^ (64 * k) * (t.valAt 0 (k + k + 2) - d.valAt o (k + k) -
        d.valAt (o + (k + k)) (n - (k + k))) +
      2 ^ (64 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)))

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

public theorem midT_spec (d : UInt64Array) (o k n : Nat) (t : UInt64Array) (h : o + n ≤ d.size) :
    Writes (midT d o k n t) d o n ∧
      ∀ Z₁, t.valAt 0 (k + k + 2) = d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) →
        d.valAt o (k + k) + 2 ^ (64 * k) * Z₁ +
            2 ^ (64 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) < 2 ^ (64 * n) →
        (midT d o k n t).valAt o n = d.valAt o (k + k) + 2 ^ (64 * k) * Z₁ +
          2 ^ (64 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
  rw [midT]
  split
  · rename_i hg
    obtain ⟨hS', -, h₃, h₄, ht, h₂⟩ := hg
    have hS := hS'.lt
    have ho := toNat_toUSize (a := o) (by lia)
    have hk := toNat_toUSize (a := k) (by lia)
    have hn := toNat_toUSize (a := n) (by lia)
    have hOK : MidOK d o.toUSize k.toUSize n.toUSize t :=
      ⟨⟨by rw [ho, hn]; exact h, by rw [ho, hn]; lia⟩, by rw [hk, hn]; lia, by rw [hk, hn]; lia,
        by rw [hk]; exact ht, by rw [hk]; exact h₂⟩
    obtain ⟨m₁, m₂, m₃⟩ := karatsubaMid_spec d o.toUSize k.toUSize n.toUSize t hOK
    simp only [ho, hk, hn] at m₂ m₃
    exact ⟨writes_of m₁ m₂, m₃⟩
  · refine ⟨writes_writeNat .., fun Z₁ hT hlt => ?_⟩
    rw [show (LimbArray.writeNat d o n _).valAt o n = _ from LimbArray.valAt_writeNat _ _ _ _ h, hT,
      show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) - d.valAt o (k + k) -
        d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
    exact Nat.mod_eq_of_lt hlt

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

/-- The operations of the Karatsuba and Toom methods on arrays of 64-bit limbs. -/
public instance toomOps64 : ToomOps UInt64Array UInt64 where
  w_ge := by show 32 ≤ 64; decide
  zeros n := UInt64Array.replicate n 0
  size_zeros n := by simp [LimbArray.size]
  val_get_zeros n i := by
    show (UInt64Array.replicate n 0)[i]!.toNat = 0
    have := valAt_replicate_zero n i 1
    rwa [valAt_one] at this
  addInto := WordArray.addIntoK
  addInto_spec := WordArray.addIntoK_spec
  subInto := WordArray.subIntoK
  subInto_spec := WordArray.subIntoK_spec
  addMulInto := WordArray.addMulIntoK
  addMulInto_spec := WordArray.addMulIntoK_spec
  subMulInto := WordArray.subMulIntoK
  subMulInto_spec := WordArray.subMulIntoK_spec
  shlTop := WordArray.shlTopK
  shlTop_spec := WordArray.shlTopK_spec
  shr := WordArray.shrK
  shr_spec := WordArray.shrK_spec
  divExact := WordArray.divExactK
  divExact_spec := WordArray.divExactK_spec
  zeroInto := WordArray.zeroIntoK
  zeroInto_spec := WordArray.zeroIntoK_spec
  sum x xo xl y yo yl := WordArray.sumK (UInt64Array.replicate (xl + 1) 0) x xo xl y yo yl
  sum_spec x xo xl y yo yl hyl := WordArray.sumK_spec _ x xo xl y yo yl hyl (by simp [LimbArray.size])
    (fun i => by
      show (UInt64Array.replicate (xl + 1) 0)[i]!.toNat = 0
      have := valAt_replicate_zero (xl + 1) i 1
      rwa [valAt_one] at this)
  mid := midT
  mid_spec := midT_spec
  mulBase := mulBaseT
  mulBase_spec := mulBaseT_spec
  sqrBase := sqrBaseT
  sqrBase_spec := sqrBaseT_spec

end MPN.W64
