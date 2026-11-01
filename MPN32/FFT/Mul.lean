/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Dispatch
public import MPN32.Mul.ToomOps
public import MPN32.Settings

/-!
# FFT products

The products and squares by the FFT on 32-bit limbs, `MPN`'s `Dispatch.fftMulW` and
`Dispatch.fftSqrW` into new arrays, for the tuner; the library's products choose them through
`MPN.Dispatch`.
-/

open ScalarArray

namespace MPN.W32.FFT

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 5 T`, `5` being the
`fftKFactor` of `Config`. From a sweep of `k = 5, …, 12` at 8192 to 262144 limbs per operand
(Zen 3, 2026-10-26), products and squares alike: this choice is the best at every size measured
from 12288 limbs, and within 6% at 8192.
-/
public def fftK (T : Nat) : Nat := Dispatch.fftK ({} : Config).fftKFactor T

/-- `a b` by the FFT with `2ᵏ` pieces, into a new array of `a.size + b.size` limbs. -/
public def fftMul (cfg : Config) (a b : UInt32Array.Slice) (k : Nat) : UInt32Array :=
  Dispatch.fftMulW cfg.mul (UInt32Array.replicate (a.size + b.size) 0) 0 a.array a.start a.size
    b.array b.start b.size k

/-- `a²` by the FFT with `2ᵏ` pieces, into a new array of `a.size + a.size` limbs. -/
public def fftSqr (cfg : Config) (a : UInt32Array.Slice) (k : Nat) : UInt32Array :=
  Dispatch.fftSqrW cfg.mul (UInt32Array.replicate (a.size + a.size) 0) 0 a.array a.start a.size k

end MPN.W32.FFT
