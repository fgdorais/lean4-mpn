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
callback (the dispatcher's `mulLimbsWith`) for the pointwise products. `fftMulAt`, `fftMulModAt` and `fftSqrAt` take `USlice`s; `fftMul` and
`fftSqr` at the end take the library's slices and `MPN.toNat`, as the dispatcher does.
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

/-! ## The multiplication -/

/--
`a b` into the first `a.size + b.size` limbs of `r`, with `K = 2ᵏ` windows of `n + 1` limbs for
the pieces of `m` limbs of each operand: `FFTOps.fftMulAt`.
-/
public def fftMulAt (N : Nat) (mul : MulN N) (r a b : USlice) (k m n : Nat) : UInt32Array :=
  FFTOps.fftMulAt (mulP32 N mul) r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
    b.start.toNat b.size.toNat k m n

/-- The parameters of `fftMulAt` for which it computes `a b`. -/
public structure FFTParams (r a b : USlice) (k m n : Nat) : Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (32 * n) % 2 ^ k = 0
  ha : 0 < a.size.toNat
  hb : 0 < b.size.toNat
  hpieces : (a.size.toNat + m - 1) / m + (b.size.toNat + m - 1) / m ≤ 2 ^ k + 1
  hbits : 2 ^ k * 2 ^ (64 * m) ≤ 2 ^ (32 * n)
  hr : a.size.toNat + b.size.toNat ≤ r.size.toNat
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  hN32 : 32 * n < USize.size
  haS : a.array.size < USize.size
  hbS : b.array.size < USize.size
  hrS : r.array.size < USize.size

private theorem FFTParams.gen {r a b : USlice} {k m n : Nat} (hp : FFTParams r a b k m n) :
    FFTOps.FFTParams r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat k m n := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hbits, hr, hS, h32, haS, hbS, hrS⟩ := hp
  have := sliceBound r
  have hb₂ : 2 ^ k * 2 ^ (32 * m + 32 * m) ≤ 2 ^ (32 * n) := by
    rw [show 32 * m + 32 * m = 64 * m by lia]; exact hbits
  exact ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hb₂, by show _ ≤ r.array.size; lia, hS, h32, haS, hbS,
    hrS, sliceBound a, sliceBound b⟩

public theorem fftMulAt_spec (N : Nat) (mul : MulN N) (hmul : IsMulN mul) (r a b : USlice)
    (k m n : Nat) (hN : 2 * n + 2 < N) (hp : FFTParams r a b k m n) :
    (fftMulAt N mul r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMulAt N mul r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulAt N mul r a b k m n).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
        a.toNat * b.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := FFTOps.fftMulAt_spec (mulP32 N mul) _ _ _ _ _ _ _ _ k m n hp.gen
    (isMulP32 N mul hmul n hN)
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
  exact ⟨h₁, fun i hi => h₂ i (by lia), h₃⟩

/-! ## The product modulo `β^N - 1` -/

/--
`a b` modulo `2^(32 N) - 1`, for `N = m 2ᵏ`, into the first `N + n + 1` limbs of `r`:
`FFTOps.fftMulModAt`, at about half the cost of a product of the same operands.
-/
public def fftMulModAt (N : Nat) (mul : MulN N) (r a b : USlice) (k m n : Nat) : UInt32Array :=
  FFTOps.fftMulModAt (mulP32 N mul) r.array r.start.toNat a.array a.start.toNat a.size.toNat
    b.array b.start.toNat b.size.toNat k m n

/-- The parameters of `fftMulModAt` for which it computes `a b` modulo `2^(32 m 2ᵏ) - 1`. -/
public structure FFTModParams (r a b : USlice) (k m n : Nat) : Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (32 * n) % 2 ^ k = 0
  ha : 0 < a.size.toNat
  hb : 0 < b.size.toNat
  hla : a.size.toNat ≤ m * 2 ^ k
  hlb : b.size.toNat ≤ m * 2 ^ k
  hbits : 2 * 2 ^ k * 2 ^ (64 * m) ≤ 2 ^ (32 * n)
  hr : m * 2 ^ k + n + 1 ≤ r.size.toNat
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  hN32 : 32 * n < USize.size
  haS : a.array.size < USize.size
  hbS : b.array.size < USize.size
  hrS : r.array.size < USize.size

private theorem FFTModParams.gen {r a b : USlice} {k m n : Nat}
    (hp : FFTModParams r a b k m n) :
    FFTOps.FFTModParams r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat k m n := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hla, hlb, hbits, hr, hS, h32, haS, hbS, hrS⟩ := hp
  have := sliceBound r
  have hb₂ : 2 * 2 ^ k * 2 ^ (32 * m + 32 * m) ≤ 2 ^ (32 * n) := by
    rw [show 32 * m + 32 * m = 64 * m by lia]; exact hbits
  exact ⟨hk, hn, hm, hmn, hdiv, ha, hb, hla, hlb, hb₂, by show _ ≤ r.array.size; lia, hS, h32,
    haS, hbS, hrS, sliceBound a, sliceBound b⟩

public theorem fftMulModAt_spec (N : Nat) (mul : MulN N) (hmul : IsMulN mul) (r a b : USlice)
    (k m n : Nat) (hN : 2 * n + 2 < N) (hp : FFTModParams r a b k m n) :
    (fftMulModAt N mul r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + (m * 2 ^ k + n + 1) ≤ i) →
        (fftMulModAt N mul r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulModAt N mul r a b k m n).valAt r.start.toNat (m * 2 ^ k + n + 1) %
          (2 ^ (32 * (m * 2 ^ k)) - 1) =
        a.toNat * b.toNat % (2 ^ (32 * (m * 2 ^ k)) - 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := FFTOps.fftMulModAt_spec (mulP32 N mul) _ _ _ _ _ _ _ _ k m n hp.gen
    (isMulP32 N mul hmul n hN)
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
  exact ⟨h₁, h₂, h₃⟩

/-- The conditions of `FFTModParams`, decidably, with `k + 1 + 64 m ≤ 32 n` for the bound. -/
public abbrev FFTModCheck (r a b : USlice) (k m n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 31 ∧ 1 ≤ n ∧ 1 ≤ m ∧ m ≤ n ∧ 2 * (32 * n) % 2 ^ k = 0 ∧ 0 < a.size.toNat ∧
    0 < b.size.toNat ∧ a.size.toNat ≤ m * 2 ^ k ∧ b.size.toNat ≤ m * 2 ^ k ∧
    k + 1 + 64 * m ≤ 32 * n ∧ m * 2 ^ k + n + 1 ≤ r.size.toNat ∧
    (2 * 2 ^ k + 2) * (n + 1) < USize.size ∧ 32 * n < USize.size ∧
    a.array.size < USize.size ∧ b.array.size < USize.size ∧ r.array.size < USize.size

public theorem FFTModCheck.params {r a b : USlice} {k m n : Nat} (h : FFTModCheck r a b k m n) :
    FFTModParams r a b k m n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
  refine ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ?_, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_comm], ← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by lia)

/-- The coefficient size `n` for `fftMulModAt` with `2ᵏ` pieces of `m` limbs. -/
public def fftModN (k m : Nat) : Nat :=
  let q := max 1 (2 ^ k / 64)
  (2 * m + 1 + q - 1) / q * q

/-! ## Squaring -/

/--
`a²` into the first `2 a.size` limbs of `r`, with one forward transform and squares for the
pointwise products: `FFTOps.fftSqrAt`.
-/
public def fftSqrAt (N : Nat) (sqr : SqrN N) (r a : USlice) (k m n : Nat) : UInt32Array :=
  FFTOps.fftSqrAt (sqrP32 N sqr) r.array r.start.toNat a.array a.start.toNat a.size.toNat k m n

public theorem fftSqrAt_spec (N : Nat) (sqr : SqrN N) (hsqr : IsSqrN sqr) (r a : USlice)
    (k m n : Nat) (hN : n + 1 < N) (hp : FFTParams r a a k m n) :
    (fftSqrAt N sqr r a k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + a.size.toNat ≤ i) →
        (fftSqrAt N sqr r a k m n)[i]! = r.array[i]!) ∧
      (fftSqrAt N sqr r a k m n).valAt r.start.toNat (a.size.toNat + a.size.toNat) =
        a.toNat * a.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := FFTOps.fftSqrAt_spec (sqrP32 N sqr) _ _ _ _ _ k m n hp.gen
    (isSqrP32 N sqr hsqr n hN)
  rw [USlice.toNat_eq_valAt]
  exact ⟨h₁, fun i hi => h₂ i (by lia), h₃⟩

/-! ## The parameters -/

/--
The parameters for `T` limbs and `K = 2ᵏ` pieces: pieces of `m = ⌈T / (K - 1)⌉` limbs, so that
the two operands have at most `K + 1`, and residues of `n` limbs, `2 m + 1` rounded up to a
multiple of `K / 64`, so that the root `2^(64 n / K)` is a power of two.
-/
public def fftParams (T k : Nat) : Nat × Nat :=
  let m := (T + 2 ^ k - 2) / (2 ^ k - 1)
  let q := max 1 (2 ^ k / 64)
  (m, (2 * m + 1 + q - 1) / q * q)

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 5 T`. From a sweep of
`k = 5, …, 12` at 8192 to 262144 limbs per operand (Zen 3, 2026-10-26), products and squares
alike: this choice is the best at every size measured from 12288 limbs, and within 6% at 8192.
-/
public def fftK (T : Nat) : Nat := min 30 ((Nat.log2 (5 * T - 1) + 2) / 2)

/-- The conditions of `FFTParams`, decidably, with `k + 64 m ≤ 32 n` for the bound. -/
public abbrev FFTCheck (r a b : USlice) (k m n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 32 ∧ 1 ≤ n ∧ 1 ≤ m ∧ m ≤ n ∧ 2 * (32 * n) % 2 ^ k = 0 ∧ 0 < a.size.toNat ∧
    0 < b.size.toNat ∧ (a.size.toNat + m - 1) / m + (b.size.toNat + m - 1) / m ≤ 2 ^ k + 1 ∧
    k + 64 * m ≤ 32 * n ∧ a.size.toNat + b.size.toNat ≤ r.size.toNat ∧
    (2 * 2 ^ k + 2) * (n + 1) < USize.size ∧ 32 * n < USize.size ∧
    a.array.size < USize.size ∧ b.array.size < USize.size ∧ r.array.size < USize.size

private theorem FFTCheck.params {r a b : USlice} {k m n : Nat} (h : FFTCheck r a b k m n) :
    FFTParams r a b k m n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ := h
  exact ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia), h₁₁, h₁₂, h₁₃, h₁₄,
    h₁₅, h₁₆⟩

/-! ## On the library's slices

The rest of the library multiplies the library's slices into new arrays, with values by
`MPN.toNat`: `fftMul` and `fftSqr` take its multiplication for the pointwise products, convert
the slices to `USlice`s and back, and fall back to schoolbook when the parameters do not suit.
-/

/-- A library slice as a `USlice`, for an array whose size is a `USize`. -/
@[inline, expose] public def toUS (s : UInt32Array.Slice) (h : s.array.size < USize.size) :
    USlice where
  array := s.array
  start := s.start.toUSize
  stop := s.stop.toUSize
  start_le_stop := USize.le_iff_toNat_le.2 (by
    have := s.start_le_stop; have := s.stop_le_array_size
    rw [Nat.toUSize_eq, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia),
      USize.toNat_ofNat_of_lt' (by lia)]; exact s.start_le_stop)
  stop_le_size := by
    have := s.stop_le_array_size
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]; exact this

public theorem toUS_spec (s : UInt32Array.Slice) (h : s.array.size < USize.size) :
    (toUS s h).array = s.array ∧ (toUS s h).start.toNat = s.start ∧
      (toUS s h).size.toNat = s.size ∧ (toUS s h).toNat = MPN.toNat s := by
  have := s.start_le_stop; have := s.stop_le_array_size
  have e₁ : (toUS s h).start.toNat = s.start := by
    show s.start.toUSize.toNat = _
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]
  have e₂ : (toUS s h).stop.toNat = s.stop := by
    show s.stop.toUSize.toNat = _
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]
  have e₃ : (toUS s h).size.toNat = s.size := by
    rw [USlice.toNat_size, e₁, e₂, Slice.size_eq]
  exact ⟨rfl, e₁, e₃, by rw [USlice.toNat_eq_valAt, e₁, e₃, toNat_eq_valAt]; rfl⟩

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

/--
The product `a b` by the FFT with `2ᵏ` pieces, the parameters of `fftParams`, and `mulRec` for
the pointwise products, into a new array; schoolbook when the parameters do not suit the sizes,
which the dispatcher avoids.
-/
public def fftMul (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  if h : a.array.size < USize.size ∧ b.array.size < USize.size then
    let r := UInt32Array.replicate (a.size + b.size) 0
    let p := fftParams (a.size + b.size) k
    if FFTCheck r.toUSlice (toUS a h.1) (toUS b h.2) k p.1 p.2 ∧ 2 * p.2 + 2 < a.size + b.size then
      fftMulAt (a.size + b.size) (mulOf mulRec) r.toUSlice (toUS a h.1) (toUS b h.2) k p.1 p.2
    else mulBasecase a b
  else mulBasecase a b

public theorem fftMul_spec (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      MPN.toNat (mulRec x y h) = MPN.toNat x * MPN.toNat y) :
    (fftMul a b k mulRec).size = a.size + b.size ∧
      MPN.toNat (fftMul a b k mulRec) = MPN.toNat a * MPN.toNat b := by
  unfold fftMul
  by_cases h : a.array.size < USize.size ∧ b.array.size < USize.size
  · rw [dite_eq_left h]
    dsimp only
    by_cases hc : FFTCheck (UInt32Array.replicate (a.size + b.size) 0).toUSlice (toUS a h.1)
          (toUS b h.2) k (fftParams (a.size + b.size) k).1 (fftParams (a.size + b.size) k).2 ∧
        2 * (fftParams (a.size + b.size) k).2 + 2 < a.size + b.size
    · rw [ite_eq_left hc]
      obtain ⟨hc, hN⟩ := hc
      obtain ⟨A₁, A₂, A₃, A₄⟩ := toUS_spec a h.1
      obtain ⟨B₁, B₂, B₃, B₄⟩ := toUS_spec b h.2
      obtain ⟨s₁, -, s₃⟩ := fftMulAt_spec (a.size + b.size) (mulOf mulRec)
        (isMulN_mulOf mulRec hrec)
        _ _ _ k _ _ hN hc.params
      rw [A₃, B₃, A₄, B₄, start_toUSlice, USize.toNat_zero] at s₃
      simp only [array_toUSlice, size_replicate] at s₁
      refine ⟨s₁, ?_⟩
      rw [toNat_array_eq_valAt, s₁]
      exact s₃
    · rw [ite_eq_right hc]
      exact ⟨size_mulBasecase a b, toNat_mulBasecase a b⟩
  · rw [dite_eq_right h]
    exact ⟨size_mulBasecase a b, toNat_mulBasecase a b⟩

/--
The square `a²` by the FFT with `2ᵏ` pieces, one forward transform, and `sqrRec` for the pointwise
squares, into a new array; schoolbook when the parameters do not suit.
-/
public def fftSqr (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  if h : a.array.size < USize.size then
    let r := UInt32Array.replicate (a.size + a.size) 0
    let p := fftParams (a.size + a.size) k
    if FFTCheck r.toUSlice (toUS a h) (toUS a h) k p.1 p.2 ∧ p.2 + 1 < a.size then
      fftSqrAt a.size (sqrOf sqrRec) r.toUSlice (toUS a h) k p.1 p.2
    else mulBasecase a a
  else mulBasecase a a

public theorem fftSqr_spec (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      MPN.toNat (sqrRec x h) = MPN.toNat x * MPN.toNat x) :
    (fftSqr a k sqrRec).size = a.size + a.size ∧
      MPN.toNat (fftSqr a k sqrRec) = MPN.toNat a * MPN.toNat a := by
  unfold fftSqr
  by_cases h : a.array.size < USize.size
  · rw [dite_eq_left h]
    dsimp only
    by_cases hc : FFTCheck (UInt32Array.replicate (a.size + a.size) 0).toUSlice (toUS a h)
          (toUS a h) k (fftParams (a.size + a.size) k).1 (fftParams (a.size + a.size) k).2 ∧
        (fftParams (a.size + a.size) k).2 + 1 < a.size
    · rw [ite_eq_left hc]
      obtain ⟨hc, hN⟩ := hc
      obtain ⟨A₁, A₂, A₃, A₄⟩ := toUS_spec a h
      obtain ⟨s₁, -, s₃⟩ := fftSqrAt_spec a.size (sqrOf sqrRec) (isSqrN_sqrOf sqrRec hrec)
        _ _ k _ _ hN hc.params
      rw [A₃, A₄, start_toUSlice, USize.toNat_zero] at s₃
      simp only [array_toUSlice, size_replicate] at s₁
      refine ⟨s₁, ?_⟩
      rw [toNat_array_eq_valAt, s₁]
      exact s₃
    · rw [ite_eq_right hc]
      exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩
  · rw [dite_eq_right h]
    exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

end MPN.FFT
