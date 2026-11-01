/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Transform
public import MPN.FFT.Product
public import MPN.Basic
public import MPN.ValAt
public import MPN.Mul.Basecase
public import MPN.FFT.Kernels

/-!
# FFT multiplication

Schönhage–Strassen multiplication on 32-bit limbs: `main`'s `MPN.FFT.Product` on the instance
`fftOps32` of `FFTOps`, whose operations are `main`'s generic kernels (`MPN.FFT.Kernels`), with a
callback (the dispatcher's `mulLimbsWith`) for the pointwise products. `fftMul` and `fftSqr` at
the end take the library's slices and `MPN.toNat`, as the dispatcher does, and run `main`'s
`FFTOps.fftMulAt` and `fftSqrAt` on their arrays under `main`'s checks.
-/

open ScalarArray UInt32Array

namespace MPN.FFT

/-! ## Slices at `Nat` offsets -/

/-- The limbs `o` to `o + len - 1` of `arr`. -/
public def sl (arr : UInt32Array) (o len : Nat) : USlice := arr.uslice o.toUSize (o + len).toUSize

public theorem sl_spec (arr : UInt32Array) (o len : Nat) (h : o + len ≤ arr.size)
    (hS : arr.size < USize.size) :
    (sl arr o len).array = arr ∧ (sl arr o len).start.toNat = o ∧
      (sl arr o len).size.toNat = len ∧ (sl arr o len).toNat = arr.valAt o len := by
  have ho : o.toUSize.toNat = o := by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hol : (o + len).toUSize.toNat = o + len := by
    rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hst := uslice_start arr o.toUSize (o + len).toUSize (USize.le_iff_toNat_le.2 (by lia))
    (by rw [hol]; exact h)
  have hsp := uslice_stop arr o.toUSize (o + len).toUSize (by rw [hol]; exact h)
  have hsz : (sl arr o len).size.toNat = len := by
    rw [USlice.toNat_size, sl, hst, hsp, ho, hol]; lia
  refine ⟨rfl, by rw [sl, hst, ho], hsz, ?_⟩
  rw [USlice.toNat_eq_valAt, hsz, sl, hst, ho]
  rfl

/-- An array of zeros has the value zero everywhere. -/
private theorem valAt_replicate_zero (n lo m : Nat) :
    (UInt32Array.replicate n 0).valAt lo m = 0 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [valAt_succ, ih]
    rw [getElem!_eq_getElem!_toArray, toArray_replicate]
    by_cases h : lo < n
    · simp [h]
    · simp [h]; rfl

/-! ## The instance -/

/-- The operations of `FFTOps` on 32-bit limbs. -/
public instance fftOps32 : FFTOps UInt32Array UInt32 where
  zeros n := UInt32Array.replicate n 0
  size_zeros n := by simp [LimbArray.size]
  val_get_zeros n i := by
    have := valAt_replicate_zero n i 1
    rwa [valAt_one] at this
  addRange := WordArray.addIntoK
  addRange_spec := WordArray.addRange_spec
  reduce := WordArray.reduceK
  reduce_spec := WordArray.reduceK_spec
  addCoef := WordArray.addCoefK
  addCoef_spec := WordArray.addCoefK_spec
  zeroRange := WordArray.zeroIntoK
  zeroRange_spec := WordArray.zeroRange_spec

/-- A multiplication of slices of fewer than `N` limbs together, into a new array. -/
public abbrev MulN (N : Nat) : Type :=
  (x y : USlice) → x.size.toNat + y.size.toNat < N → UInt32Array

/-- `mul` multiplies: a new array of `x.size + y.size` limbs with the value `x y`. -/
public def IsMulN {N : Nat} (mul : MulN N) : Prop :=
  ∀ x y h, (mul x y h).size = x.size.toNat + y.size.toNat ∧
    (mul x y h).valAt 0 (x.size.toNat + y.size.toNat) = x.toNat * y.toNat

/-- A squaring of a slice of fewer than `N` limbs, into a new array. -/
public abbrev SqrN (N : Nat) : Type := (x : USlice) → x.size.toNat < N → UInt32Array

/-- `sqr` squares: a new array of `2 x.size` limbs with the value `x²`. -/
public def IsSqrN {N : Nat} (sqr : SqrN N) : Prop :=
  ∀ x h, (sqr x h).size = 2 * x.size.toNat ∧
    (sqr x h).valAt 0 (2 * x.size.toNat) = x.toNat * x.toNat

/-- The pointwise products of the FFT: `mul` on the windows, into a new array. -/
public def mulP32 (N : Nat) (mul : MulN N) (_P arr : UInt32Array) (x y n : Nat) : UInt32Array :=
  let x := sl arr x (n + 1)
  let y := sl arr y (n + 1)
  if h : x.size.toNat + y.size.toNat < N then mul x y h else UInt32Array.replicate (2 * n + 2) 0

public theorem isMulP32 (N : Nat) (mul : MulN N) (hmul : IsMulN mul) (n : Nat)
    (hN : 2 * n + 2 < N) : FFTOps.IsMulP (mulP32 N mul) n := by
  intro P arr x y hP hPS hS hx hy
  change arr.size < _ at hS
  change _ ≤ arr.size at hx hy
  obtain ⟨-, -, x₃, x₄⟩ := sl_spec arr x (n + 1) hx hS
  obtain ⟨-, -, y₃, y₄⟩ := sl_spec arr y (n + 1) hy hS
  have hxy : (sl arr x (n + 1)).size.toNat + (sl arr y (n + 1)).size.toNat < N := by
    rw [x₃, y₃]; lia
  obtain ⟨m₁, m₂⟩ := hmul _ _ hxy
  rw [x₃, y₃, x₄, y₄, show n + 1 + (n + 1) = 2 * n + 2 by lia] at m₂
  rw [x₃, y₃, show n + 1 + (n + 1) = 2 * n + 2 by lia] at m₁
  simp only [mulP32, dite_eq_left hxy]
  exact ⟨m₁, m₂⟩

/-- The pointwise squares of the FFT: `sqr` on the window, into a new array. -/
public def sqrP32 (N : Nat) (sqr : SqrN N) (_P arr : UInt32Array) (x n : Nat) : UInt32Array :=
  let x := sl arr x (n + 1)
  if h : x.size.toNat < N then sqr x h else UInt32Array.replicate (2 * n + 2) 0

public theorem isSqrP32 (N : Nat) (sqr : SqrN N) (hsqr : IsSqrN sqr) (n : Nat)
    (hN : n + 1 < N) : FFTOps.IsSqrP (sqrP32 N sqr) n := by
  intro P arr x hP hPS hS hx
  change arr.size < _ at hS
  change _ ≤ arr.size at hx
  obtain ⟨-, -, x₃, x₄⟩ := sl_spec arr x (n + 1) hx hS
  have hx' : (sl arr x (n + 1)).size.toNat < N := by rw [x₃]; lia
  obtain ⟨m₁, m₂⟩ := hsqr _ hx'
  rw [x₃, x₄, show 2 * (n + 1) = 2 * n + 2 by lia] at m₂
  rw [x₃, show 2 * (n + 1) = 2 * n + 2 by lia] at m₁
  simp only [sqrP32, dite_eq_left hx']
  exact ⟨m₁, m₂⟩

/-- The limbs of a slice are within its array. -/
private theorem sliceBound (a : USlice) :
    a.start.toNat + a.size.toNat ≤ a.array.size := by
  have := a.toNat_size
  have := a.stop_le_size
  have := USize.le_iff_toNat_le.1 a.start_le_stop
  lia

/-! ## The parameters -/

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 5 T`. From a sweep of
`k = 5, …, 12` at 8192 to 262144 limbs per operand (Zen 3, 2026-10-26), products and squares
alike: this choice is the best at every size measured from 12288 limbs, and within 6% at 8192.
-/
public def fftK (T : Nat) : Nat := min 30 ((Nat.log2 (5 * T - 1) + 2) / 2)

/-! ## On the library's slices

The rest of the library multiplies the library's slices into new arrays, with values by
`MPN.toNat`: `fftMul` and `fftSqr` take its multiplication for the pointwise products, on the
windows as library slices (`ofUS`), and fall back to schoolbook when the parameters do not suit.
-/

/-- A `USlice` as a library slice. -/
@[inline, expose] public def ofUS (x : USlice) : UInt32Array.Slice :=
  x.array.toSlice x.start.toNat x.stop.toNat

public theorem ofUS_spec (x : USlice) :
    (ofUS x).size = x.size.toNat ∧ MPN.toNat (ofUS x) = x.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 x.start_le_stop
  have h₂ := x.stop_le_size
  have hs : (ofUS x).size = x.size.toNat := by
    rw [ofUS, size_toSlice, USlice.toNat_size]; lia
  refine ⟨hs, ?_⟩
  rw [toNat_eq_valAt, USlice.toNat_eq_valAt, hs, ofUS, array_toSlice, start_toSlice]
  congr 1; lia

/-- The pointwise products by a multiplication of the library's slices. -/
@[inline, expose] public def mulOf {N : Nat}
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < N → UInt32Array) : MulN N :=
  fun x y h => mulRec (ofUS x) (ofUS y) (by rw [(ofUS_spec x).1, (ofUS_spec y).1]; exact h)

public theorem isMulN_mulOf {N : Nat}
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < N → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      MPN.toNat (mulRec x y h) = MPN.toNat x * MPN.toNat y) : IsMulN (mulOf mulRec) := by
  intro x y h
  obtain ⟨h₁, h₂⟩ := hrec (ofUS x) (ofUS y) (by rw [(ofUS_spec x).1, (ofUS_spec y).1]; exact h)
  have h₁' : (mulOf mulRec x y h).size = x.size.toNat + y.size.toNat := by
    show (mulRec _ _ _).size = _
    rw [h₁, (ofUS_spec x).1, (ofUS_spec y).1]
  have h₂' : MPN.toNat (mulOf mulRec x y h).toSlice = x.toNat * y.toNat := by
    show MPN.toNat (mulRec _ _ _).toSlice = _
    rw [h₂, (ofUS_spec x).2, (ofUS_spec y).2]
  refine ⟨h₁', ?_⟩
  rw [← h₁', ← toNat_array_eq_valAt]
  exact h₂'

/-- The pointwise squares by a squaring of the library's slices. -/
@[inline, expose] public def sqrOf {N : Nat}
    (sqrRec : (x : UInt32Array.Slice) → x.size < N → UInt32Array) : SqrN N :=
  fun x h => sqrRec (ofUS x) (by rw [(ofUS_spec x).1]; exact h)

public theorem isSqrN_sqrOf {N : Nat}
    (sqrRec : (x : UInt32Array.Slice) → x.size < N → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      MPN.toNat (sqrRec x h) = MPN.toNat x * MPN.toNat x) : IsSqrN (sqrOf sqrRec) := by
  intro x h
  obtain ⟨h₁, h₂⟩ := hrec (ofUS x) (by rw [(ofUS_spec x).1]; exact h)
  have h₁' : (sqrOf sqrRec x h).size = 2 * x.size.toNat := by
    show (sqrRec _ _).size = _
    rw [h₁, (ofUS_spec x).1]; lia
  have h₂' : MPN.toNat (sqrOf sqrRec x h).toSlice = x.toNat * x.toNat := by
    show MPN.toNat (sqrRec _ _).toSlice = _
    rw [h₂, (ofUS_spec x).2]
  refine ⟨h₁', ?_⟩
  rw [← h₁', ← toNat_array_eq_valAt]
  exact h₂'

/-- The conditions under which `fftMul` multiplies by the FFT. -/
public abbrev FFTMulOK (a b : UInt32Array.Slice) (k : Nat) : Prop :=
  FFTOps.FFTCheck (UInt32Array.replicate (a.size + b.size) 0) 0 (a.size + b.size) a.array a.start
      a.size b.array b.start b.size k (FFTOps.fftParams 32 (a.size + b.size) k).1
      (FFTOps.fftParams 32 (a.size + b.size) k).2 ∧
    2 * (FFTOps.fftParams 32 (a.size + b.size) k).2 + 2 < a.size + b.size

/--
The product `a b` by the FFT with `2ᵏ` pieces, the parameters of `main`'s `fftParams`, and
`mulRec` for the pointwise products, into a new array; schoolbook when the parameters do not suit
the sizes, which the dispatcher avoids.
-/
public def fftMul (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  if FFTMulOK a b k then
    FFTOps.fftMulAt (mulP32 (a.size + b.size) (mulOf mulRec))
      (UInt32Array.replicate (a.size + b.size) 0) 0 a.array a.start a.size b.array b.start b.size
      k (FFTOps.fftParams 32 (a.size + b.size) k).1 (FFTOps.fftParams 32 (a.size + b.size) k).2
  else mulBasecase a b

public theorem fftMul_spec (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      MPN.toNat (mulRec x y h) = MPN.toNat x * MPN.toNat y) :
    (fftMul a b k mulRec).size = a.size + b.size ∧
      MPN.toNat (fftMul a b k mulRec) = MPN.toNat a * MPN.toNat b := by
  by_cases hc : FFTMulOK a b k
  · have e : fftMul a b k mulRec = FFTOps.fftMulAt (mulP32 (a.size + b.size) (mulOf mulRec))
        (UInt32Array.replicate (a.size + b.size) 0) 0 a.array a.start a.size b.array b.start
        b.size k (FFTOps.fftParams 32 (a.size + b.size) k).1
        (FFTOps.fftParams 32 (a.size + b.size) k).2 := by
      rw [fftMul]; exact ite_eq_left hc
    obtain ⟨s₁, -, s₃⟩ := FFTOps.fftMulAt_spec (mulP32 _ (mulOf mulRec)) _ _ _ _ _ _ _ _ k _ _
      (FFTOps.FFTCheck.params hc.1) (isMulP32 _ _ (isMulN_mulOf mulRec hrec) _ hc.2)
    have hs := s₁.trans (show LimbArray.size (UInt32Array.replicate (a.size + b.size) 0) =
      a.size + b.size by simp [LimbArray.size])
    rw [e]
    refine ⟨hs, ?_⟩
    rw [toNat_array_eq_valAt, show UInt32Array.size _ = _ from hs, toNat_eq_valAt a,
      toNat_eq_valAt b]
    exact s₃
  · have e : fftMul a b k mulRec = mulBasecase a b := by
      rw [fftMul]; exact ite_eq_right hc
    rw [e]
    exact ⟨size_mulBasecase a b, toNat_mulBasecase a b⟩

/-- The conditions under which `fftSqr` squares by the FFT. -/
public abbrev FFTSqrOK (a : UInt32Array.Slice) (k : Nat) : Prop :=
  FFTOps.FFTCheck (UInt32Array.replicate (a.size + a.size) 0) 0 (a.size + a.size) a.array a.start
      a.size a.array a.start a.size k (FFTOps.fftParams 32 (a.size + a.size) k).1
      (FFTOps.fftParams 32 (a.size + a.size) k).2 ∧
    (FFTOps.fftParams 32 (a.size + a.size) k).2 + 1 < a.size

/--
The square `a²` by the FFT with `2ᵏ` pieces, one forward transform, and `sqrRec` for the pointwise
squares, into a new array; schoolbook when the parameters do not suit.
-/
public def fftSqr (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  if FFTSqrOK a k then
    FFTOps.fftSqrAt (sqrP32 a.size (sqrOf sqrRec)) (UInt32Array.replicate (a.size + a.size) 0) 0
      a.array a.start a.size k (FFTOps.fftParams 32 (a.size + a.size) k).1
      (FFTOps.fftParams 32 (a.size + a.size) k).2
  else mulBasecase a a

public theorem fftSqr_spec (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      MPN.toNat (sqrRec x h) = MPN.toNat x * MPN.toNat x) :
    (fftSqr a k sqrRec).size = a.size + a.size ∧
      MPN.toNat (fftSqr a k sqrRec) = MPN.toNat a * MPN.toNat a := by
  by_cases hc : FFTSqrOK a k
  · have e : fftSqr a k sqrRec = FFTOps.fftSqrAt (sqrP32 a.size (sqrOf sqrRec))
        (UInt32Array.replicate (a.size + a.size) 0) 0 a.array a.start a.size k
        (FFTOps.fftParams 32 (a.size + a.size) k).1
        (FFTOps.fftParams 32 (a.size + a.size) k).2 := by
      rw [fftSqr]; exact ite_eq_left hc
    obtain ⟨s₁, -, s₃⟩ := FFTOps.fftSqrAt_spec (sqrP32 _ (sqrOf sqrRec)) _ _ _ _ _ k _ _
      (FFTOps.FFTCheck.params hc.1) (isSqrP32 _ _ (isSqrN_sqrOf sqrRec hrec) _ hc.2)
    have hs := s₁.trans (show LimbArray.size (UInt32Array.replicate (a.size + a.size) 0) =
      a.size + a.size by simp [LimbArray.size])
    rw [e]
    refine ⟨hs, ?_⟩
    rw [toNat_array_eq_valAt, show UInt32Array.size _ = _ from hs, toNat_eq_valAt a]
    exact s₃
  · have e : fftSqr a k sqrRec = mulBasecase a a := by
      rw [fftSqr]; exact ite_eq_right hc
    rw [e]
    exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

end MPN.FFT
