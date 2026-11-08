/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Windows
public import MPN64.Arch.UIntArray
public import MPN.FFT.Product
public import MPN.Dispatch
public import MPN64.Mul.Toom
public import MPN64.Sqr.Karatsuba

/-!
# Products and squares

The products and squares on 64-bit limbs, by `MPN`'s choice of an algorithm (`MPN.Dispatch`) on
the slices: `mul` and `sqr` choose by the sizes with the thresholds of `cfg`, `fftMul` and
`fftSqr` use the FFT with `2ᵏ` pieces when its parameters suit the sizes. Each writes into the
slice `r` when it holds the result, and leaves `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN.W64.FFT

open MPN.FFT

/-! ## The parameters -/

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 10 T`, `10` being the
`fftKFactor` of `Config`. From a sweep of `k = 4, …, 11` at 1024 to 65536 limbs per operand
(Zen 3, 2026-10-23): the best `K = 2ᵏ` has `K² / T` between 8 and 32, and this choice is within 6%
of the best at every size measured.
-/
public def fftK (T : Nat) : Nat := Dispatch.fftK ({} : Config).fftKFactor T

/-- `MPN`'s `FFTOps.FFTCheck` on slices. -/
public abbrev FFTCheck (r a b : USlice) (k m n : Nat) : Prop :=
  FFTOps.FFTCheck r.array r.start.toNat r.size.toNat a.array a.start.toNat a.size.toNat b.array
    b.start.toNat b.size.toNat k m n

/-- `MPN`'s `FFTOps.fftParams` for 64-bit limbs. -/
@[inline] public def fftParams (T k : Nat) : Nat × Nat := FFTOps.fftParams 64 T k

/-- `MPN`'s `FFTOps.fftModN` for 64-bit limbs. -/
@[inline] public def fftModN (k m : Nat) : Nat := FFTOps.fftModN 64 k m

/-- `a b` into `r` by `Dispatch.fftMulW`, with `2ᵏ` pieces, when it fits. -/
public def fftMul (cfg : Config) (r a b : USlice) (k : Nat) : UInt64Array :=
  if a.size.toNat + b.size.toNat ≤ r.size.toNat then
    Dispatch.fftMulW cfg.mul r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat k
  else r.array

/-- `a²` into `r` by `Dispatch.fftSqrW`, with `2ᵏ` pieces, when it fits. -/
public def fftSqr (cfg : Config) (r a : USlice) (k : Nat) : UInt64Array :=
  if a.size.toNat + a.size.toNat ≤ r.size.toNat then
    Dispatch.fftSqrW cfg.mul r.array r.start.toNat a.array a.start.toNat a.size.toNat k
  else r.array

end MPN.W64.FFT

namespace MPN.W64

variable (cfg : Config)

/-- The bounds of a slice. -/
private theorem slice_bound (r : USlice) : r.start.toNat + r.size.toNat ≤ r.array.size := by
  have := r.toNat_size; have := r.stop_le_size; have := USize.le_iff_toNat_le.1 r.start_le_stop
  lia

/-! ## Products -/

/--
Writes the `a.size + b.size` limbs of `a b` into `r`, by `Dispatch.mul`, which chooses by the
sizes. It requires `a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def mul (cfg : Config) (r a b : USlice) : UInt64Array :=
  if a.size.toNat + b.size.toNat ≤ r.size.toNat then
    Dispatch.mul cfg.mul r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat
  else r.array

private theorem mul_spec (r a b : USlice) :
    Toom.Writes (mul cfg r a b) r.array r.start.toNat (a.size.toNat + b.size.toNat) ∧
      (a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (mul cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat) := by
  unfold mul
  split
  · rename_i h
    have := slice_bound r
    rw [USlice.toNat_eq_valAt a, USlice.toNat_eq_valAt b]
    obtain ⟨s₁, s₂⟩ := Dispatch.mul_spec cfg.mul r.array r.start.toNat a.array a.start.toNat
      a.size.toNat b.array b.start.toNat b.size.toNat (by show _ ≤ r.array.size; lia)
    exact ⟨s₁, fun _ => s₂⟩
  · rename_i h
    exact ⟨Toom.Writes.refl .., fun h' => absurd h' h⟩

@[simp] public theorem size_mul (r a b : USlice) : (mul cfg r a b).size = r.array.size :=
  (mul_spec cfg r a b).1.1

/-- `mul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mul (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mul cfg r a b)[i]! = r.array[i]! :=
  (mul_spec cfg r a b).1.2 i (by lia)

public theorem valAt_mul (r a b : USlice) (_ : 0 < a.size) (_ : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mul cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat :=
  (mul_spec cfg r a b).2 hr

/-! ## Squares -/

/--
Writes the `2 a.size` limbs of `a²` into `r`, by `Dispatch.sqr`, the FFT from `cfg.sqrFFT` limbs
and the Toom methods below. It requires `2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def sqr (cfg : Config) (r a : USlice) : UInt64Array :=
  if a.size.toNat + a.size.toNat ≤ r.size.toNat then
    Dispatch.sqr cfg.mul r.array r.start.toNat a.array a.start.toNat a.size.toNat
  else r.array

private theorem sqr_spec (r a : USlice) :
    Toom.Writes (sqr cfg r a) r.array r.start.toNat (a.size.toNat + a.size.toNat) ∧
      (a.size.toNat + a.size.toNat ≤ r.size.toNat →
        (sqr cfg r a).valAt r.start.toNat (a.size.toNat + a.size.toNat) = a.toNat * a.toNat) := by
  unfold sqr
  split
  · rename_i h
    have := slice_bound r
    rw [USlice.toNat_eq_valAt a]
    obtain ⟨s₁, s₂⟩ := Dispatch.sqr_spec cfg.mul r.array r.start.toNat a.array a.start.toNat
      a.size.toNat (by show _ ≤ r.array.size; lia)
    exact ⟨s₁, fun _ => s₂⟩
  · rename_i h
    exact ⟨Toom.Writes.refl .., fun h' => absurd h' h⟩

@[simp] public theorem size_sqr (r a : USlice) : (sqr cfg r a).size = r.array.size :=
  (sqr_spec cfg r a).1.1

/-- `sqr` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqr (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqr cfg r a)[i]! = r.array[i]! :=
  (sqr_spec cfg r a).1.2 i (by lia)

public theorem valAt_sqr (r a : USlice) (_ : 0 < a.size) (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqr cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  rw [Nat.two_mul]; exact (sqr_spec cfg r a).2 (by lia)

end MPN.W64
