/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Bits
public import MPN.Linear
public import MPN.Mul.KaratsubaMid
public import MPN.Sqr.Basecase
public import MPN.Toom.Ops

/-!
# The operations of the Karatsuba and Toom methods

The instance of `MPN.Toom.ToomOps` on `UInt64Array`, from the kernels of this library on `USlice`s.
Each operation checks that the indices of its windows fit in a `USize` and that the kernel's
conditions hold; otherwise it writes the value of its specification with `LimbArray.writeNat`,
which never happens.
-/

open ScalarArray UInt64Array MPN.Toom

namespace MPN

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

/-- `D + S`. -/
public def addIntoT (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl : Nat) : UInt64Array :=
  if Fits d ∧ Fits s ∧ o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl ≤ len then
    (addInto (winS d o len) (winS s so sl)).1
  else LimbArray.writeNat d o len (d.valAt o len + s.valAt so sl)

/-- `D - S`. -/
public def subIntoT (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl : Nat) : UInt64Array :=
  if Fits d ∧ Fits s ∧ o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl ≤ len then
    (subInto (winS d o len) (winS s so sl)).1
  else LimbArray.writeNat d o len (d.valAt o len - s.valAt so sl)

/-- `D + S v`. -/
public def addMulIntoT (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl v : Nat) :
    UInt64Array :=
  if Fits d ∧ Fits s ∧ o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl ≤ len then
    (addMulInto (winS d o len) (winS s so sl) v.toUInt64).1
  else LimbArray.writeNat d o len (d.valAt o len + s.valAt so sl * v)

/-- `D - S v`. -/
public def subMulIntoT (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl v : Nat) :
    UInt64Array :=
  if Fits d ∧ Fits s ∧ o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl ≤ len then
    (subMulInto (winS d o len) (winS s so sl) v.toUInt64).1
  else LimbArray.writeNat d o len (d.valAt o len - s.valAt so sl * v)

/-- `D 2⁶³`, wrapped. -/
public def shlTopT (d : UInt64Array) (o len : Nat) : UInt64Array :=
  if Fits d ∧ o + len ≤ d.size then (shl63Into (winS d o len)).1
  else LimbArray.writeNat d o len (d.valAt o len * 2 ^ 63 % 2 ^ (64 * len))

/-- `D / 2ˢ`. -/
public def shrT (d : UInt64Array) (o len s : Nat) : UInt64Array :=
  if Fits d ∧ o + len ≤ d.size ∧ 0 < s ∧ s < 64 then
    rshiftInto (winS d o len) s.toUInt64
  else LimbArray.writeNat d o len (d.valAt o len / 2 ^ s)

/-- The inverse of an odd `q` modulo `2⁶⁴`, by Newton's iteration from `q`, exact to 3 bits. -/
public def inv64 (q : UInt64) : UInt64 :=
  let x := q * (2 - q * q)
  let x := x * (2 - q * x)
  let x := x * (2 - q * x)
  let x := x * (2 - q * x)
  x * (2 - q * x)

/-- `D / q`, exactly, for an odd `q`. -/
public def divExactT (d : UInt64Array) (o len q : Nat) : UInt64Array :=
  if Fits d ∧ o + len ≤ d.size ∧ q.toUInt64 * inv64 q.toUInt64 = 1 ∧ q % 2 = 1 ∧
      q.toUInt64.toNat = q then
    (divExactInto (winS d o len) q.toUInt64 (inv64 q.toUInt64)).1
  else LimbArray.writeNat d o len (d.valAt o len / q)

/-- `0`. -/
public def zeroIntoT (d : UInt64Array) (o len : Nat) : UInt64Array :=
  if Fits d ∧ o + len ≤ d.size then zeroInto (winS d o len)
  else LimbArray.writeNat d o len 0

/-- `x + y` in a new array of `xl + 1` limbs. -/
public def sumT (x : UInt64Array) (xo xl : Nat) (y : UInt64Array) (yo yl : Nat) : UInt64Array :=
  let r := UInt64Array.replicate (xl + 1) 0
  if Fits x ∧ Fits y ∧ Fits r ∧ xo + xl ≤ x.size ∧ yo + yl ≤ y.size ∧ yl ≤ xl then
    let p := add (r.uslice 0 xl.toUSize) (winS x xo xl) (winS y yo yl)
    p.1.set! xl p.2
  else
    LimbArray.writeNat r 0 (xl + 1) (x.valAt xo xl + y.valAt yo yl)

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

public theorem addIntoT_spec (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl : Nat)
    (h : o + len ≤ d.size) (hlt : d.valAt o len + s.valAt so sl < 2 ^ (64 * len)) :
    Writes (addIntoT d o len s so sl) d o len ∧
      (addIntoT d o len s so sl).valAt o len = d.valAt o len + s.valAt so sl := by
  rw [addIntoT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    obtain ⟨s₁, s₂, s₃, s₄⟩ := winS_spec s so sl hg.2.1.lt hg.2.2.2.1
    have hb := le_usize d₃ s₃ hg.2.2.2.2
    have := addInto_exact _ _ hb (by rw [d₁, d₂, d₃, s₄]; exact hlt)
    rw [d₁, d₂, d₃, s₄] at this
    refine ⟨writes_of (by rw [size_addInto, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_addInto _ _ _ i (by rw [d₂, d₃]; exact hi), d₁]
  · exact fallback _ _ _ _ h hlt

public theorem subIntoT_spec (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl : Nat)
    (h : o + len ≤ d.size) (hle : s.valAt so sl ≤ d.valAt o len) :
    Writes (subIntoT d o len s so sl) d o len ∧
      (subIntoT d o len s so sl).valAt o len = d.valAt o len - s.valAt so sl := by
  rw [subIntoT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    obtain ⟨s₁, s₂, s₃, s₄⟩ := winS_spec s so sl hg.2.1.lt hg.2.2.2.1
    have hb := le_usize d₃ s₃ hg.2.2.2.2
    have := subInto_exact _ _ hb (by rw [d₁, d₂, d₃, s₄]; exact hle)
    rw [d₁, d₂, d₃, s₄] at this
    refine ⟨writes_of (by rw [size_subInto, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_subInto _ _ _ i (by rw [d₂, d₃]; exact hi), d₁]
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.sub_le ..) (valAt_lt ..))

public theorem addMulIntoT_spec (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl v : Nat)
    (h : o + len ≤ d.size) (hv : v < 2 ^ 64)
    (hlt : d.valAt o len + s.valAt so sl * v < 2 ^ (64 * len)) :
    Writes (addMulIntoT d o len s so sl v) d o len ∧
      (addMulIntoT d o len s so sl v).valAt o len = d.valAt o len + s.valAt so sl * v := by
  rw [addMulIntoT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    obtain ⟨s₁, s₂, s₃, s₄⟩ := winS_spec s so sl hg.2.1.lt hg.2.2.2.1
    have hb := le_usize d₃ s₃ hg.2.2.2.2
    have := addMulInto_exact _ _ v.toUInt64 hb (by rw [d₁, d₂, d₃, s₄, toNat_toUInt64 hv]; exact hlt)
    rw [d₁, d₂, d₃, s₄, toNat_toUInt64 hv] at this
    refine ⟨writes_of (by rw [size_addMulInto, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_addMulInto _ _ _ i (by rw [d₂, d₃]; exact hi), d₁]
  · exact fallback _ _ _ _ h hlt

public theorem subMulIntoT_spec (d : UInt64Array) (o len : Nat) (s : UInt64Array) (so sl v : Nat)
    (h : o + len ≤ d.size) (hv : v < 2 ^ 64) (hle : s.valAt so sl * v ≤ d.valAt o len) :
    Writes (subMulIntoT d o len s so sl v) d o len ∧
      (subMulIntoT d o len s so sl v).valAt o len = d.valAt o len - s.valAt so sl * v := by
  rw [subMulIntoT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    obtain ⟨s₁, s₂, s₃, s₄⟩ := winS_spec s so sl hg.2.1.lt hg.2.2.2.1
    have hb := le_usize d₃ s₃ hg.2.2.2.2
    have := subMulInto_exact _ _ v.toUInt64 hb (by rw [d₁, d₂, d₃, s₄, toNat_toUInt64 hv]; exact hle)
    rw [d₁, d₂, d₃, s₄, toNat_toUInt64 hv] at this
    refine ⟨writes_of (by rw [size_subMulInto, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_subMulInto _ _ _ i (by rw [d₂, d₃]; exact hi), d₁]
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.sub_le ..) (valAt_lt ..))

public theorem shlTopT_spec (d : UInt64Array) (o len : Nat) (h : o + len ≤ d.size) :
    Writes (shlTopT d o len) d o len ∧
      (shlTopT d o len).valAt o len = d.valAt o len * 2 ^ 63 % 2 ^ (64 * len) := by
  rw [shlTopT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    have := valAt_shl63Into (winS d o len)
    rw [d₁, d₂, d₃] at this
    refine ⟨writes_of (by rw [size_shl63Into, d₁]) fun i hi => ?_, ?_⟩
    · rw [getElem!_shl63Into _ i (by rw [d₂, d₃]; exact hi), d₁]
    · rw [← this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (valAt_lt ..)]
  · exact fallback _ _ _ _ h (Nat.mod_lt _ (Nat.two_pow_pos _))

public theorem shrT_spec (d : UInt64Array) (o len s : Nat) (h : o + len ≤ d.size) (hs₀ : 0 < s)
    (hs : s < 64) :
    Writes (shrT d o len s) d o len ∧ (shrT d o len s).valAt o len = d.valAt o len / 2 ^ s := by
  rw [shrT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    have hs' := toNat_toUInt64 (v := s) (by lia)
    have := valAt_rshiftInto (winS d o len) s.toUInt64 (by rw [hs']; exact hs₀) (by rw [hs']; exact hs)
    rw [d₁, d₂, d₃, hs'] at this
    refine ⟨writes_of (by rw [size_rshiftInto, d₁]) fun i hi => ?_, this⟩
    rw [getElem!_rshiftInto _ _ (by rw [hs']; exact hs₀) (by rw [hs']; exact hs) i
      (by rw [d₂, d₃]; exact hi), d₁]
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.div_le_self ..) (valAt_lt ..))

public theorem divExactT_spec (d : UInt64Array) (o len q : Nat) (h : o + len ≤ d.size)
    (hq : q % 2 = 1) (hd : d.valAt o len % q = 0) :
    Writes (divExactT d o len q) d o len ∧ (divExactT d o len q).valAt o len = d.valAt o len / q := by
  rw [divExactT]
  split
  · rename_i hg
    obtain ⟨hS, -, hinv, -, hq'⟩ := hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hS.lt h
    have hi : q.toUInt64.toNat * (inv64 q.toUInt64).toNat % 2 ^ 64 = 1 := by
      have := congrArg UInt64.toNat hinv
      rwa [UInt64.toNat_mul] at this
    have := valAt_divExactInto (winS d o len) q.toUInt64 (inv64 q.toUInt64) hi (by rw [hq']; exact hq)
      (by rw [d₁, d₂, d₃, hq']; exact hd)
    rw [d₁, d₂, d₃, hq'] at this
    refine ⟨writes_of (by rw [size_divExactInto, d₁]) fun i hi' => ?_, this⟩
    rw [getElem!_divExactInto _ _ _ hi i (by rw [d₂, d₃]; exact hi'), d₁]
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.div_le_self ..) (valAt_lt ..))

public theorem zeroIntoT_spec (d : UInt64Array) (o len : Nat) (h : o + len ≤ d.size) :
    Writes (zeroIntoT d o len) d o len ∧ (zeroIntoT d o len).valAt o len = 0 := by
  rw [zeroIntoT]
  split
  · rename_i hg
    obtain ⟨d₁, d₂, d₃, d₄⟩ := winS_spec d o len hg.1.lt h
    obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec (winS d o len)
    rw [d₁, d₂, d₃] at *
    exact ⟨writes_of z₁ fun i hi => z₂ i hi, z₃⟩
  · exact fallback _ _ _ _ h (Nat.two_pow_pos _)

public theorem sumT_spec (x : UInt64Array) (xo xl : Nat) (y : UInt64Array) (yo yl : Nat)
    (hyx : yl ≤ xl) :
    (sumT x xo xl y yo yl).size = xl + 1 ∧
      (sumT x xo xl y yo yl).valAt 0 (xl + 1) = x.valAt xo xl + y.valAt yo yl := by
  rw [sumT]
  generalize hR : UInt64Array.replicate (xl + 1) 0 = R
  have hRs : R.size = xl + 1 := by rw [← hR]; simp
  split
  · rename_i hg
    obtain ⟨hx, hy, hS, hxo, hyo, -⟩ := hg
    obtain ⟨x₁, x₂, x₃, x₄⟩ := winS_spec x xo xl hx.lt hxo
    obtain ⟨y₁, y₂, y₃, y₄⟩ := winS_spec y yo yl hy.lt hyo
    dsimp only
    obtain ⟨r₁, r₂, r₃, r₄⟩ := winS_spec R 0 xl hS.lt (by lia)
    have hw : R.uslice 0 xl.toUSize = winS R 0 xl := by
      simp only [winS, Nat.zero_add]; rfl
    rw [hw]
    have hv := MPN.valAt_add (winS R 0 xl) (winS x xo xl) (winS y yo yl) 0
      (le_usize x₃ y₃ (by lia)) (le_usize r₃ x₃ (by lia))
    rw [r₂, x₃, x₄, y₄, UInt64.toNat_zero, Nat.add_zero] at hv
    have hsz : (add (winS R 0 xl) (winS x xo xl) (winS y yo yl) 0).1.size = xl + 1 := by
      rw [size_add, r₁, hRs]
    refine ⟨by rw [size_set!, hsz], ?_⟩
    rw [UInt64Array.valAt_add, valAt_one, Nat.zero_add, getElem!_set!_self _ _ _ (by lia), ← hv]
    congr 1
    exact valAt_congr _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)
  · have hz : 0 + (xl + 1) ≤ R.size := by lia
    refine ⟨(LimbArray.size_writeNat (A := UInt64Array) ..).trans hRs,
      (LimbArray.valAt_writeNat _ _ _ (x.valAt xo xl + y.valAt yo yl) hz).trans ?_⟩
    apply Nat.mod_eq_of_lt
    show _ < 2 ^ (64 * (xl + 1))
    have := valAt_lt x xo xl
    have := valAt_lt y yo yl
    have : 2 ^ (64 * yl) ≤ 2 ^ (64 * xl) := Nat.pow_le_pow_right (by decide) (by lia)
    rw [Nat.mul_succ, Nat.pow_add]
    lia

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
  addInto := addIntoT
  addInto_spec := addIntoT_spec
  subInto := subIntoT
  subInto_spec := subIntoT_spec
  addMulInto := addMulIntoT
  addMulInto_spec := addMulIntoT_spec
  subMulInto := subMulIntoT
  subMulInto_spec := subMulIntoT_spec
  shlTop := shlTopT
  shlTop_spec := shlTopT_spec
  shr := shrT
  shr_spec := shrT_spec
  divExact := divExactT
  divExact_spec d o len q h hq _ hd := divExactT_spec d o len q h hq hd
  zeroInto := zeroIntoT
  zeroInto_spec := zeroIntoT_spec
  sum := sumT
  sum_spec := sumT_spec
  mid := midT
  mid_spec := midT_spec
  mulBase := mulBaseT
  mulBase_spec := mulBaseT_spec
  sqrBase := sqrBaseT
  sqrBase_spec := sqrBaseT_spec

end MPN
