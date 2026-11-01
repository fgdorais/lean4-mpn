/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.FFT.Transform
public import MPN.FFT.Product
public import MPN.FFT.Kernels
public import MPN64.Mul.Toom
public import MPN64.Sqr.Karatsuba

/-!
# FFT multiplication

Schönhage–Strassen multiplication on 64-bit limbs: `main`'s `MPN.FFT.Product` on the instance
`fftOps64` of `FFTOps`, whose operations are `main`'s generic kernels (`MPN.FFT.Kernels`), with
`mulToom` and `sqrKaratsuba` for the pointwise products.
`fftMulAt`, `fftMulModAt` and `fftSqrAt` take `USlice`s; `fftMul`, `fftSqr` and the dispatchers
`MPN.mul` and `MPN.sqr` choose the parameters.
-/

open ScalarArray UInt64Array

namespace MPN.W64.FFT

open MPN.FFT

variable (cfg : Config)

/-! ## Slices at `Nat` offsets -/

/-- The limbs `o` to `o + len - 1` of `arr`. -/
public def sl (arr : UInt64Array) (o len : Nat) : USlice := arr.uslice o.toUSize (o + len).toUSize

public theorem sl_spec (arr : UInt64Array) (o len : Nat) (h : o + len ≤ arr.size)
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

/-! ## Pieces of slices -/

/-- Piece `i` of `a`: its limbs `i m` to `i m + m - 1`, or fewer at the end. -/
@[expose] public def piece (a : USlice) (m i : Nat) : Nat :=
  FFTOps.piece a.array a.start.toNat a.size.toNat m i

/-- The first `L` pieces of `a`. -/
@[expose] public def pieces (a : USlice) (m L : Nat) : List Nat :=
  FFTOps.pieces a.array a.start.toNat a.size.toNat m L

/-- The pieces of `a` are its digits in base `2^(64 m)`. -/
public theorem polyVal_pieces (a : USlice) (m L : Nat) (hL : a.size.toNat ≤ L * m) :
    polyVal (2 ^ (64 * m)) (pieces a m L) = a.toNat := by
  rw [USlice.toNat_eq_valAt]
  exact FFTOps.polyVal_pieces a.array a.start.toNat a.size.toNat m L hL

public theorem length_pieces (a : USlice) (m L : Nat) : (pieces a m L).length = L :=
  FFTOps.length_pieces ..

public theorem getD_pieces (a : USlice) (m L i : Nat) :
    (pieces a m L).getD i 0 = if i < L then piece a m i else 0 :=
  FFTOps.getD_pieces ..

/-- The slice of piece `i` of `a`. -/
public def pieceSl (a : USlice) (m i : Nat) : USlice :=
  sl a.array (a.start.toNat + min (i * m) a.size.toNat) (min m (a.size.toNat - i * m))

public theorem pieceSl_spec (a : USlice) (m i : Nat) (hS : a.array.size < USize.size) :
    (pieceSl a m i).size.toNat = min m (a.size.toNat - i * m) ∧
      (pieceSl a m i).toNat = piece a m i := by
  have := a.toNat_size
  have := a.stop_le_size
  have := USize.le_iff_toNat_le.1 a.start_le_stop
  obtain ⟨-, -, s₃, s₄⟩ := sl_spec a.array (a.start.toNat + min (i * m) a.size.toNat)
    (min m (a.size.toNat - i * m)) (by lia) hS
  refine ⟨s₃, ?_⟩
  rw [pieceSl, s₄]
  show _ = a.array.valAt (a.start.toNat + i * m) (min m (a.size.toNat - i * m))
  rcases Nat.le_total (i * m) a.size.toNat with h | h
  · rw [Nat.min_eq_left h]
  · rw [show a.size.toNat - i * m = 0 by lia, Nat.min_zero, valAt_zero, valAt_zero]

/-! ## The instance -/

/-- The operations of `FFTOps` on 64-bit limbs. -/
public instance fftOps64 : FFTOps UInt64Array UInt64 where
  zeros n := UInt64Array.replicate n 0
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

/-- The pointwise products of the FFT: `mulToom` into `P`. -/
public def mulP64 (cfg : Config) (P arr : UInt64Array) (x y n : Nat) : UInt64Array :=
  mulToom cfg P.toUSlice (sl arr x (n + 1)) (sl arr y (n + 1))

public theorem isMulP64 (n : Nat) : FFTOps.IsMulP (mulP64 cfg) n := by
  intro P arr x y hP hPS hS hx hy
  change P.size = _ at hP; change P.size < _ at hPS; change arr.size < _ at hS
  change _ ≤ arr.size at hx hy
  obtain ⟨-, -, x₃, x₄⟩ := sl_spec arr x (n + 1) hx hS
  obtain ⟨-, -, y₃, y₄⟩ := sl_spec arr y (n + 1) hy hS
  have hPs := size_toUSlice P hPS
  have hx₀ : 0 < (sl arr x (n + 1)).size :=
    USize.lt_iff_toNat_lt.2 (by rw [x₃, USize.toNat_zero]; lia)
  have hy₀ : 0 < (sl arr y (n + 1)).size :=
    USize.lt_iff_toNat_lt.2 (by rw [y₃, USize.toNat_zero]; lia)
  have m₁ := size_mulToom cfg P.toUSlice (sl arr x (n + 1)) (sl arr y (n + 1))
  have m₂ := valAt_mulToom cfg P.toUSlice (sl arr x (n + 1)) (sl arr y (n + 1)) hx₀ hy₀
    (by rw [x₃, y₃, hPs]; lia)
  rw [x₃, y₃, x₄, y₄, start_toUSlice, USize.toNat_zero, show n + 1 + (n + 1) = 2 * n + 2 by lia]
    at m₂
  rw [array_toUSlice] at m₁
  exact ⟨m₁.trans hP, m₂⟩

/-- The pointwise squares of the FFT: `sqrKaratsuba` into `P`. -/
public def sqrP64 (cfg : Config) (P arr : UInt64Array) (x n : Nat) : UInt64Array :=
  sqrKaratsuba cfg P.toUSlice (sl arr x (n + 1))

public theorem isSqrP64 (n : Nat) : FFTOps.IsSqrP (sqrP64 cfg) n := by
  intro P arr x hP hPS hS hx
  change P.size = _ at hP; change P.size < _ at hPS; change arr.size < _ at hS
  change _ ≤ arr.size at hx
  obtain ⟨-, -, x₃, x₄⟩ := sl_spec arr x (n + 1) hx hS
  have hPs := size_toUSlice P hPS
  have hx₀ : 0 < (sl arr x (n + 1)).size :=
    USize.lt_iff_toNat_lt.2 (by rw [x₃, USize.toNat_zero]; lia)
  have m₁ := size_sqrKaratsuba cfg P.toUSlice (sl arr x (n + 1))
  have m₂ := valAt_sqrKaratsuba cfg P.toUSlice (sl arr x (n + 1)) hx₀ (by rw [x₃, hPs]; lia)
  rw [x₃, x₄, start_toUSlice, USize.toNat_zero, show 2 * (n + 1) = 2 * n + 2 by lia] at m₂
  rw [array_toUSlice] at m₁
  exact ⟨m₁.trans hP, m₂⟩

/-- The limbs of a slice are within its array. -/
private theorem sliceBound (a : USlice) :
    a.start.toNat + a.size.toNat ≤ a.array.size := by
  have := a.toNat_size
  have := a.stop_le_size
  have := USize.le_iff_toNat_le.1 a.start_le_stop
  lia

/-! ## The parameters -/

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 10 T`. From a sweep of
`k = 4, …, 11` at 1024 to 65536 limbs per operand (Zen 3, 2026-10-23): the best `K = 2ᵏ` has
`K² / T` between 8 and 32, and this choice is within 6% of the best at every size measured.
-/
public def fftK (T : Nat) : Nat := min 30 ((Nat.log2 (10 * T - 1) + 2) / 2)

/-- `main`'s `FFTOps.FFTCheck` on slices. -/
public abbrev FFTCheck (r a b : USlice) (k m n : Nat) : Prop :=
  FFTOps.FFTCheck r.array r.start.toNat r.size.toNat a.array a.start.toNat a.size.toNat b.array
    b.start.toNat b.size.toNat k m n

/-- `main`'s `FFTOps.fftParams` for 64-bit limbs. -/
@[inline] public def fftParams (T k : Nat) : Nat × Nat := FFTOps.fftParams 64 T k

/-- `main`'s `FFTOps.fftModN` for 64-bit limbs. -/
@[inline] public def fftModN (k m : Nat) : Nat := FFTOps.fftModN 64 k m

/-! ## The products -/

/--
Writes the `a.size + b.size` limbs of `a b` into `r`, by the FFT with `2ᵏ` pieces, or by
`mulToom` when the parameters of `fftParams` do not suit the sizes.
-/
public def fftMul (cfg : Config) (r a b : USlice) (k : Nat) : UInt64Array :=
  let p := fftParams (a.size.toNat + b.size.toNat) k
  if FFTCheck r a b k p.1 p.2 then
    FFTOps.fftMulAt (mulP64 cfg) r.array r.start.toNat a.array a.start.toNat a.size.toNat
      b.array b.start.toNat b.size.toNat k p.1 p.2
  else mulToom cfg r a b

private theorem fftMul_spec (r a b : USlice) (k : Nat) :
    (fftMul cfg r a b k).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMul cfg r a b k)[i]! = r.array[i]!) ∧
      (0 < a.size → 0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (fftMul cfg r a b k).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  rw [fftMul]
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := FFTOps.fftMulAt_spec (mulP64 cfg) _ _ _ _ _ _ _ _ k _ _
      (FFTOps.FFTCheck.params h) (isMulP64 cfg _)
    rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
    exact ⟨s₁, fun i hi => s₂ i (by lia), fun _ _ _ => s₃⟩
  · exact ⟨size_mulToom cfg r a b, getElem!_mulToom cfg r a b, valAt_mulToom cfg r a b⟩

@[simp] public theorem size_fftMul (r a b : USlice) (k : Nat) :
    (fftMul cfg r a b k).size = r.array.size :=
  (fftMul_spec cfg r a b k).1

/-- `fftMul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_fftMul (r a b : USlice) (k : Nat) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (fftMul cfg r a b k)[i]! = r.array[i]! :=
  (fftMul_spec cfg r a b k).2.1 i hi

public theorem valAt_fftMul (r a b : USlice) (k : Nat) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (fftMul cfg r a b k).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat :=
  (fftMul_spec cfg r a b k).2.2 ha hb hr

/--
Writes the `2 a.size` limbs of `a²` into `r`, by the FFT with `2ᵏ` pieces, or by `sqrKaratsuba`
when the parameters of `fftParams` do not suit the size.
-/
public def fftSqr (cfg : Config) (r a : USlice) (k : Nat) : UInt64Array :=
  let p := fftParams (a.size.toNat + a.size.toNat) k
  if FFTCheck r a a k p.1 p.2 then
    FFTOps.fftSqrAt (sqrP64 cfg) r.array r.start.toNat a.array a.start.toNat a.size.toNat k p.1
      p.2
  else sqrKaratsuba cfg r a

private theorem fftSqr_spec (r a : USlice) (k : Nat) :
    (fftSqr cfg r a k).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) →
        (fftSqr cfg r a k)[i]! = r.array[i]!) ∧
      (0 < a.size → 2 * a.size.toNat ≤ r.size.toNat →
        (fftSqr cfg r a k).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat) := by
  rw [fftSqr]
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := FFTOps.fftSqrAt_spec (sqrP64 cfg) _ _ _ _ _ k _ _
      (FFTOps.FFTCheck.params h) (isSqrP64 cfg _)
    rw [show 2 * a.size.toNat = a.size.toNat + a.size.toNat by lia, USlice.toNat_eq_valAt]
    exact ⟨s₁, fun i hi => s₂ i (by lia), fun _ _ => s₃⟩
  · exact ⟨size_sqrKaratsuba cfg r a, getElem!_sqrKaratsuba cfg r a, valAt_sqrKaratsuba cfg r a⟩

@[simp] public theorem size_fftSqr (r a : USlice) (k : Nat) :
    (fftSqr cfg r a k).size = r.array.size :=
  (fftSqr_spec cfg r a k).1

/-- `fftSqr` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_fftSqr (r a : USlice) (k : Nat) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (fftSqr cfg r a k)[i]! = r.array[i]! :=
  (fftSqr_spec cfg r a k).2.1 i hi

public theorem valAt_fftSqr (r a : USlice) (k : Nat) (ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (fftSqr cfg r a k).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat :=
  (fftSqr_spec cfg r a k).2.2 ha hr

end MPN.W64.FFT

namespace MPN.W64

open MPN.FFT MPN.W64.FFT

variable (cfg : Config)

/--
Writes the `a.size + b.size` limbs of `a b` into `r`, for operands of comparable sizes: by
`fftMul` from `cfg.mulFFT` limbs in the larger operand, or `cfg.mulFFTUnbal` when they differ
by `3 : 2` or more, when the smaller one has `cfg.mulFFTMin` limbs, by `mulToom` otherwise, which
uses the Toom methods, Karatsuba and the schoolbook method by the sizes. It requires
`0 < a.size`, `0 < b.size` and `a.size + b.size ≤ r.size`.
-/
public def mulBal (cfg : Config) (r a b : USlice) : UInt64Array :=
  if (cfg.mulFFT ≤ max a.size.toNat b.size.toNat ∨
      cfg.mulFFTUnbal ≤ max a.size.toNat b.size.toNat ∧
        3 * min a.size.toNat b.size.toNat ≤ 2 * max a.size.toNat b.size.toNat) ∧
      cfg.mulFFTMin ≤ min a.size.toNat b.size.toNat then
    fftMul cfg r a b (fftK (a.size.toNat + b.size.toNat))
  else mulToom cfg r a b

@[simp] public theorem size_mulBal (r a b : USlice) : (mulBal cfg r a b).size = r.array.size := by
  rw [mulBal]; split <;> simp

/-- `mulBal` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulBal (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulBal cfg r a b)[i]! = r.array[i]! := by
  rw [mulBal]; split
  · exact getElem!_fftMul cfg r a b _ i hi
  · exact getElem!_mulToom cfg r a b i hi

public theorem valAt_mulBal (r a b : USlice) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulBal cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  rw [mulBal]; split
  · exact valAt_fftMul cfg r a b _ ha hb hr
  · exact valAt_mulToom cfg r a b ha hb hr

/-! ## Unbalanced products -/

/--
The products of pieces `i` to `i + cnt - 1` of `a`, of `c` limbs, by `b`, each by `mulBal` into
a new array, added to the region of `T` limbs at `rs` of `arr`, piece `j` from limb `j c` on.
-/
public def chunkLoop (cfg : Config) (T c rs : Nat) (a b : USlice) :
    UInt64Array → Nat → Nat → UInt64Array
  | arr, _, 0 => arr
  | arr, i, cnt + 1 =>
    let P := mulBal cfg
      (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat + b.size.toNat) 0).toUSlice
      (FFT.pieceSl a c i) b
    chunkLoop cfg T c rs a b
      (WordArray.addCoefK arr rs T (i * c) P 0 ((FFT.pieceSl a c i).size.toNat + b.size.toNat))
        (i + 1) cnt

set_option maxHeartbeats 400000 in
public theorem chunkLoop_spec (T c rs : Nat) (a b : USlice) (hc : 1 ≤ c)
    (haS : a.array.size < USize.size) (hb : 0 < b.size) (hab : a.size.toNat + b.size.toNat ≤ T)
    (hTS : T < USize.size) (cnt : Nat) :
    ∀ arr i, arr.size < USize.size → rs + T ≤ arr.size → (i + cnt) * c < a.size.toNat + c →
      arr.valAt rs T + sumRange (fun j => 2 ^ (64 * ((i + j) * c)) *
        (FFT.piece a c (i + j) * b.toNat)) cnt < 2 ^ (64 * T) →
      (chunkLoop cfg T c rs a b arr i cnt).size = arr.size ∧
      (∀ t, (t < rs ∨ rs + T ≤ t) → (chunkLoop cfg T c rs a b arr i cnt)[t]! = arr[t]!) ∧
      (chunkLoop cfg T c rs a b arr i cnt).valAt rs T = arr.valAt rs T +
        sumRange (fun j => 2 ^ (64 * ((i + j) * c)) * (FFT.piece a c (i + j) * b.toNat)) cnt := by
  induction cnt with
  | zero => intro arr i _ _ _ _; exact ⟨rfl, fun _ _ => rfl, by simp [chunkLoop]⟩
  | succ cnt ih =>
    intro arr i hS hT hcov hsum
    rw [sumRange_succ_left] at hsum ⊢
    simp only [Nat.add_zero] at hsum ⊢
    have hs' : sumRange (fun j => 2 ^ (64 * ((i + (j + 1)) * c)) *
        (FFT.piece a c (i + (j + 1)) * b.toNat)) cnt = sumRange (fun j =>
          2 ^ (64 * ((i + 1 + j) * c)) * (FFT.piece a c (i + 1 + j) * b.toNat)) cnt :=
      sumRange_congr fun j _ => by rw [show i + (j + 1) = i + 1 + j by lia]
    rw [hs'] at hsum ⊢
    rw [chunkLoop]
    -- The product of piece `i` by `b`.
    obtain ⟨p₁, p₂⟩ := FFT.pieceSl_spec a c i haS
    have hic : i * c < a.size.toNat := by
      have := Nat.mul_le_mul_right c (show i + 1 ≤ i + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at this; lia
    have hlen : (FFT.pieceSl a c i).size.toNat + b.size.toNat < USize.size := by
      rw [p₁]; lia
    have hrep := size_toUSlice (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat +
      b.size.toNat) 0) (by rw [size_replicate]; exact hlen)
    simp only [size_replicate] at hrep
    have hv := valAt_mulBal cfg (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat +
      b.size.toNat) 0).toUSlice (FFT.pieceSl a c i) b
      (USize.lt_iff_toNat_lt.2 (by rw [p₁, USize.toNat_zero]; lia)) hb
      (by rw [hrep]; exact Nat.le_refl _)
    have hsz := size_mulBal cfg (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat +
      b.size.toNat) 0).toUSlice (FFT.pieceSl a c i) b
    rw [start_toUSlice, USize.toNat_zero, p₂] at hv
    rw [array_toUSlice, size_replicate] at hsz
    generalize mulBal cfg (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat + b.size.toNat)
      0).toUSlice (FFT.pieceSl a c i) b = P at *
    -- Added from limb `i c` on.
    obtain ⟨c₁, c₂, c₃⟩ := WordArray.addCoefK_spec arr rs T (i * c) P 0
      ((FFT.pieceSl a c i).size.toNat + b.size.toNat) hS hT (by lia)
      (show P.size < _ by rw [hsz]; exact hlen) (show 0 + _ ≤ P.size by rw [hsz]; lia)
      (show arr.valAt rs T + 2 ^ (64 * (i * c)) * P.valAt 0 _ < 2 ^ (64 * T) by rw [hv]; lia)
    generalize WordArray.addCoefK arr rs T (i * c) P 0
      ((FFT.pieceSl a c i).size.toNat + b.size.toNat) = A at *
    replace c₁ : A.size = arr.size := c₁
    replace c₂ : ∀ t, (t < rs ∨ rs + T ≤ t) → A[t]! = arr[t]! := c₂
    replace c₃ : A.valAt rs T = arr.valAt rs T + 2 ^ (64 * (i * c)) *
        P.valAt 0 ((FFT.pieceSl a c i).size.toNat + b.size.toNat) := c₃
    rw [hv] at c₃
    obtain ⟨i₁, i₂, i₃⟩ := ih A (i + 1) (by rw [c₁]; exact hS) (by rw [c₁]; exact hT) (by lia)
      (by rw [c₃]; lia)
    refine ⟨i₁.trans c₁, fun t ht => by rw [i₂ t ht, c₂ t ht], ?_⟩
    rw [i₃, c₃]
    lia

/--
`a b` for `b.size ≤ a.size`, by `mulBal` on the pieces of `a` of `b.size` limbs, the products
added into the zeroed limbs of `r`, like GMP's `mpn_mul` on unbalanced operands.
-/
public def mulChunked (cfg : Config) (r a b : USlice) : UInt64Array :=
  chunkLoop cfg (a.size.toNat + b.size.toNat) b.size.toNat r.start.toNat a b
    (zeroInto (r.slice 0 (a.size + b.size))) 0 ((a.size.toNat + b.size.toNat - 1) / b.size.toNat)

private theorem mulChunked_spec (r a b : USlice) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) (haS : a.array.size < USize.size)
    (hrS : r.array.size < USize.size) :
    (mulChunked cfg r a b).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (mulChunked cfg r a b)[i]! = r.array[i]!) ∧
      (mulChunked cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
        a.toNat * b.toNat := by
  have hb' := USize.lt_iff_toNat_lt.1 hb
  rw [USize.toNat_zero] at hb'
  -- The number of pieces covers `a`, and no more.
  generalize hL : (a.size.toNat + b.size.toNat - 1) / b.size.toNat = L
  have hL₁ : a.size.toNat ≤ L * b.size.toNat := by
    have h₁ := Nat.div_add_mod (a.size.toNat + b.size.toNat - 1) b.size.toNat
    have h₂ := Nat.mod_lt (a.size.toNat + b.size.toNat - 1) hb'
    rw [hL, Nat.mul_comm] at h₁
    lia
  have hL₂ : L * b.size.toNat < a.size.toNat + b.size.toNat := by
    rw [← hL]
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by lia)
  -- The sum of the products of the pieces is `a b`.
  have hab : sumRange (fun j => 2 ^ (64 * ((0 + j) * b.size.toNat)) *
      (FFT.piece a b.size.toNat (0 + j) * b.toNat)) L = a.toNat * b.toNat := by
    rw [← FFT.polyVal_pieces a b.size.toNat L hL₁,
      polyVal_eq_sumRange _ _ L (by rw [FFT.length_pieces]; exact Nat.le_refl _),
      sumRange_mul_right]
    exact sumRange_congr fun j hj => by
      rw [FFT.getD_pieces, ite_eq_left hj, Nat.zero_add, ← Nat.pow_mul,
        show 64 * b.size.toNat * j = 64 * (j * b.size.toNat) by lia]
      grind
  have hablt : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : a.toNat < 2 ^ (64 * a.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    have h₂ : b.toNat < 2 ^ (64 * b.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    exact Nat.mul_lt_mul'' h₁ h₂
  -- Zeroing the result, and adding the products.
  have hT : (a.size + b.size).toNat = a.size.toNat + b.size.toNat :=
    USize.toNat_add_of_lt (by have := r.size.toNat_lt_size; lia)
  have hrs := r.toNat_size
  have hrst := r.stop_le_size
  have hrle := USize.le_iff_toNat_le.1 r.start_le_stop
  have e₁ := r.start_slice (i := 0) (j := a.size + b.size) (by simp) (by rw [hT]; exact hr)
  have e₂ := r.size_slice (i := 0) (j := a.size + b.size) (by simp) (by rw [hT]; exact hr)
  rw [USize.toNat_zero, Nat.add_zero] at e₁
  rw [USize.toNat_zero, Nat.sub_zero, hT] at e₂
  obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec (r.slice 0 (a.size + b.size))
  simp only [USlice.array_slice, e₁, e₂] at z₁ z₂ z₃
  rw [mulChunked, hL]
  generalize zeroInto (r.slice 0 (a.size + b.size)) = R₀ at *
  obtain ⟨c₁, c₂, c₃⟩ := chunkLoop_spec cfg (a.size.toNat + b.size.toNat) b.size.toNat r.start.toNat
    a b (by lia) haS hb (Nat.le_refl _) (by have := r.size.toNat_lt_size; lia) L R₀ 0
    (by rw [z₁]; exact hrS) (by rw [z₁]; lia) (by lia) (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hab]

/-- `mul` for `b.size ≤ a.size`. -/
public def mulU (cfg : Config) (r a b : USlice) : UInt64Array :=
  if cfg.mulUnbalanced ≤ b.size.toNat ∧ 2 * b.size.toNat ≤ a.size.toNat ∧
      (b.size.toNat < cfg.mulChunkMax ∨ a.size.toNat < cfg.mulFFTUnbal) ∧
      a.size.toNat + b.size.toNat ≤ r.size.toNat ∧
      a.array.size < USize.size ∧ r.array.size < USize.size then
    mulChunked cfg r a b
  else mulBal cfg r a b

private theorem mulU_spec (r a b : USlice) :
    (mulU cfg r a b).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (mulU cfg r a b)[i]! = r.array[i]!) ∧
      (0 < a.size → 0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (mulU cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  rw [mulU]
  split
  · rename_i h
    have h₁ := h.1
    have := cfg.one_le_mulUnbalanced
    have hb : 0 < b.size := USize.lt_iff_toNat_lt.2 (by rw [USize.toNat_zero]; lia)
    obtain ⟨s₁, s₂, s₃⟩ := mulChunked_spec cfg r a b hb h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    exact ⟨s₁, s₂, fun _ _ _ => s₃⟩
  · exact ⟨size_mulBal cfg r a b, getElem!_mulBal cfg r a b, valAt_mulBal cfg r a b⟩

/--
Writes the `a.size + b.size` limbs of `a b` into `r`: by `mulChunked` when the larger operand
has at least twice the limbs of the smaller, which has at least `cfg.mulUnbalanced` limbs, and less
than `cfg.mulChunkMax` unless the larger one is below `cfg.mulFFTUnbal`; by `mulBal` otherwise. It
requires `0 < a.size`, `0 < b.size` and `a.size + b.size ≤ r.size`.
-/
public def mul (cfg : Config) (r a b : USlice) : UInt64Array :=
  if b.size ≤ a.size then mulU cfg r a b else mulU cfg r b a

@[simp] public theorem size_mul (r a b : USlice) : (mul cfg r a b).size = r.array.size := by
  rw [mul]; split <;> exact (mulU_spec cfg ..).1

/-- `mul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mul (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mul cfg r a b)[i]! = r.array[i]! := by
  rw [mul]; split
  · exact (mulU_spec cfg r a b).2.1 i hi
  · exact (mulU_spec cfg r b a).2.1 i (by lia)

public theorem valAt_mul (r a b : USlice) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mul cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  rw [mul]; split
  · exact (mulU_spec cfg r a b).2.2 ha hb hr
  · rw [Nat.add_comm, Nat.mul_comm]; exact (mulU_spec cfg r b a).2.2 hb ha (by lia)

/--
Writes the `2 a.size` limbs of `a²` into `r`: by `fftSqr` from `cfg.sqrFFT` limbs, by
`sqrToom` below. It requires
`0 < a.size` and `2 a.size ≤ r.size`.
-/
public def sqr (cfg : Config) (r a : USlice) : UInt64Array :=
  if cfg.sqrFFT ≤ a.size.toNat then fftSqr cfg r a (fftK (2 * a.size.toNat))
  else sqrToom cfg r a

@[simp] public theorem size_sqr (r a : USlice) : (sqr cfg r a).size = r.array.size := by
  rw [sqr]; split <;> simp

/-- `sqr` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqr (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqr cfg r a)[i]! = r.array[i]! := by
  rw [sqr]; split
  · exact getElem!_fftSqr cfg r a _ i hi
  · exact getElem!_sqrToom cfg r a i hi

public theorem valAt_sqr (r a : USlice) (ha : 0 < a.size) (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqr cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  rw [sqr]; split
  · exact valAt_fftSqr cfg r a _ ha hr
  · exact valAt_sqrToom cfg r a ha hr

end MPN.W64
