/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Mul
public import MPN.FFT.Kernels

/-!
# Choosing a product

The products and squares of both widths, written into a window of an array like GMP's `mpn_mul`
and `mpn_sqr`, choosing the algorithm by the sizes with the thresholds of a `MulConfig`:

* `mul` puts the longer operand first; `mulU` splits a longer operand that is at least twice as
  long as a shorter one of at least `mulUnbalanced` limbs into pieces of the size of the shorter
  (`mulChunked`), unless the shorter one has `mulChunkMax` limbs and the longer one is in the
  range of the FFT for unbalanced operands; `mulBal` multiplies by the FFT (`fftMulW`) from
  `mulFFT` limbs in the larger operand, or `mulFFTUnbal` when they differ by `3 : 2` or more,
  when the smaller one has `mulFFTMin` limbs, and by the Toom methods otherwise (`Toom.mulToom`),
  which go down to Karatsuba and the base case of the width (`ToomBase`);
* `sqr` squares by the FFT (`fftSqrW`) from `sqrFFT` limbs, and by the Toom methods otherwise.

The FFT has `2ᵏ` pieces for the least `k` with `4ᵏ ≥ c T`, `T` the size of the product and `c`
the factor `fftKFactor` of the width, and multiplies its pointwise products by the Toom methods
(`mulP`, `sqrP`). Each function writes the limbs of its window only, and its window holds the
product, whatever the thresholds.
-/

namespace MPN.Dispatch

open LimbArray Toom FFT

/-- The thresholds of the choice of a product or a square, beyond those of the Toom methods. -/
public structure MulConfig extends Toom.Config where
  /-- The size of the larger operand from which multiplication uses the FFT. -/
  mulFFT : Nat
  /--
  The size of the larger operand from which multiplication uses the FFT when the operands differ
  by `3 : 2` or more, where the Toom methods are slower.
  -/
  mulFFTUnbal : Nat
  /--
  The size of the smaller operand below which multiplication does not use the FFT, whose cost
  follows the total size, where that of schoolbook grows with the smaller operand.
  -/
  mulFFTMin : Nat
  /--
  The size of the smaller operand from which multiplication splits a larger operand that is at
  least twice as long into pieces of the size of the smaller one.
  -/
  mulUnbalanced : Nat
  /-- The pieces need at least one limb. -/
  one_le_mulUnbalanced : 1 ≤ mulUnbalanced := by decide
  /--
  The size of the smaller operand from which multiplication no longer splits the larger operand
  when that one is in the range of the FFT, since one FFT on the whole product is faster.
  -/
  mulChunkMax : Nat
  /-- The size from which squaring uses the FFT. -/
  sqrFFT : Nat
  /-- The factor `c` of the number of pieces of the FFT: `2ᵏ` for the least `k` with `4ᵏ ≥ c T`. -/
  fftKFactor : Nat
  deriving Repr

/-- The number of pieces, `2ᵏ`, of an FFT on `T` limbs: the least `k` with `4ᵏ ≥ c T`. -/
public def fftK (c T : Nat) : Nat := min 30 ((Nat.log2 (c * T - 1) + 2) / 2)

variable {A L : Type} [LA : LimbArray A L] [W : WordArray A L] [F : WordFolds A L]
  [B : ToomBase A L]

/-! ## The pointwise products of the FFT -/

/-- The pointwise products of the FFT: the Toom methods into `P`. -/
@[expose] public def mulP (cfg : Toom.Config) (P arr : A) (x y n : Nat) : A :=
  Toom.mulToom cfg P 0 arr x (n + 1) arr y (n + 1)

public theorem isMulP (cfg : Toom.Config) (n : Nat) : FFTOps.IsMulP (mulP (A := A) cfg) n := by
  intro P arr x y hP _ _ _ _
  obtain ⟨⟨s₁, -⟩, s₂⟩ := Toom.mulToom_spec cfg P 0 arr x (n + 1) arr y (n + 1) (by lia)
  rw [show n + 1 + (n + 1) = 2 * n + 2 by lia] at s₂
  exact ⟨s₁.trans hP, s₂⟩

/-- The pointwise squares of the FFT: Karatsuba's square into `P`. -/
@[expose] public def sqrP (cfg : Toom.Config) (P arr : A) (x n : Nat) : A :=
  Toom.sqrKaratsuba cfg P 0 arr x (n + 1)

public theorem isSqrP (cfg : Toom.Config) (n : Nat) : FFTOps.IsSqrP (sqrP (A := A) cfg) n := by
  intro P arr x hP _ _ _
  obtain ⟨⟨s₁, -⟩, s₂⟩ := Toom.sqrKaratsuba_spec cfg (n + 1) P 0 arr x (n + 1) rfl (by lia)
  rw [show n + 1 + (n + 1) = 2 * n + 2 by lia] at s₂
  exact ⟨s₁.trans hP, s₂⟩

/-! ## The FFT -/

/--
`A B` into the `al + bl` limbs of `d` from `o` on, by the FFT with `2ᵏ` pieces, or by the Toom
methods when the parameters of `fftParams` do not suit the sizes.
-/
@[expose] public def fftMulW (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl k : Nat) : A :=
  let p := FFTOps.fftParams LA.w (al + bl) k
  if FFTOps.FFTCheck d o (al + bl) a ao al b bo bl k p.1 p.2 then
    FFTOps.fftMulAt (mulP cfg.toConfig) d o a ao al b bo bl k p.1 p.2
  else Toom.mulToom cfg.toConfig d o a ao al b bo bl

public theorem fftMulW_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl k : Nat) (hd : o + (al + bl) ≤ LA.size d) :
    Writes (fftMulW cfg d o a ao al b bo bl k) d o (al + bl) ∧
      valAt (fftMulW cfg d o a ao al b bo bl k) o (al + bl) = valAt a ao al * valAt b bo bl := by
  unfold fftMulW
  dsimp only
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := FFTOps.fftMulAt_spec (mulP cfg.toConfig) _ _ _ _ _ _ _ _ k _ _
      (FFTOps.FFTCheck.params h) (isMulP _ _)
    exact ⟨⟨s₁, s₂⟩, s₃⟩
  · exact Toom.mulToom_spec _ _ _ _ _ _ _ _ _ hd

/--
`A²` into the `al + al` limbs of `d` from `o` on, by the FFT with `2ᵏ` pieces, or by the Toom
methods when the parameters of `fftParams` do not suit the size.
-/
@[expose] public def fftSqrW (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al k : Nat) : A :=
  let p := FFTOps.fftParams LA.w (al + al) k
  if FFTOps.FFTCheck d o (al + al) a ao al a ao al k p.1 p.2 then
    FFTOps.fftSqrAt (sqrP cfg.toConfig) d o a ao al k p.1 p.2
  else Toom.sqrToom cfg.toConfig d o a ao al

public theorem fftSqrW_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al k : Nat)
    (hd : o + (al + al) ≤ LA.size d) :
    Writes (fftSqrW cfg d o a ao al k) d o (al + al) ∧
      valAt (fftSqrW cfg d o a ao al k) o (al + al) = valAt a ao al * valAt a ao al := by
  unfold fftSqrW
  dsimp only
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := FFTOps.fftSqrAt_spec (sqrP cfg.toConfig) _ _ _ _ _ k _ _
      (FFTOps.FFTCheck.params h) (isSqrP _ _)
    exact ⟨⟨s₁, s₂⟩, s₃⟩
  · exact Toom.sqrToom_spec _ _ _ _ _ _ hd

/-! ## Products of comparable sizes -/

/--
`A B` into the `al + bl` limbs of `d` from `o` on, for operands of comparable sizes: by the FFT
from `mulFFT` limbs in the larger operand, or `mulFFTUnbal` when they differ by `3 : 2` or more,
when the smaller one has `mulFFTMin` limbs, and by the Toom methods otherwise.
-/
@[expose] public def mulBal (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : A :=
  if (cfg.mulFFT ≤ max al bl ∨ cfg.mulFFTUnbal ≤ max al bl ∧ 3 * min al bl ≤ 2 * max al bl) ∧
      cfg.mulFFTMin ≤ min al bl then
    fftMulW cfg d o a ao al b bo bl (fftK cfg.fftKFactor (al + bl))
  else Toom.mulToom cfg.toConfig d o a ao al b bo bl

public theorem mulBal_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (hd : o + (al + bl) ≤ LA.size d) :
    Writes (mulBal cfg d o a ao al b bo bl) d o (al + bl) ∧
      valAt (mulBal cfg d o a ao al b bo bl) o (al + bl) = valAt a ao al * valAt b bo bl := by
  unfold mulBal
  split
  · exact fftMulW_spec _ _ _ _ _ _ _ _ _ _ hd
  · exact Toom.mulToom_spec _ _ _ _ _ _ _ _ _ hd

/-! ## Unbalanced products -/

/--
The products of pieces `i` to `i + cnt - 1` of `A`, of `c` limbs, by `B`, each by `mulBal` into
a new array, added to the region of `T` limbs at `rs` of `arr`, piece `j` from limb `j c` on.
-/
@[expose] public def chunkLoop (cfg : MulConfig) (T c rs : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : A → Nat → Nat → A
  | arr, _, 0 => arr
  | arr, i, cnt + 1 =>
    let pl := min c (al - i * c)
    let P := mulBal cfg (W.zeros (pl + bl)) 0 a (ao + i * c) pl b bo bl
    chunkLoop cfg T c rs a ao al b bo bl (WordArray.addCoefK arr rs T (i * c) P 0 (pl + bl))
      (i + 1) cnt

set_option maxHeartbeats 400000 in
public theorem chunkLoop_spec (cfg : MulConfig) (T c rs : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (hab : al + bl ≤ T) (hTS : T < USize.size) (cnt : Nat) :
    ∀ arr i, LA.size arr < USize.size → rs + T ≤ LA.size arr → (i + cnt) * c < al + c →
      valAt arr rs T + sumRange (fun j => 2 ^ (LA.w * ((i + j) * c)) *
        (FFTOps.piece a ao al c (i + j) * valAt b bo bl)) cnt < 2 ^ (LA.w * T) →
      Writes (chunkLoop cfg T c rs a ao al b bo bl arr i cnt) arr rs T ∧
      valAt (chunkLoop cfg T c rs a ao al b bo bl arr i cnt) rs T = valAt arr rs T +
        sumRange (fun j => 2 ^ (LA.w * ((i + j) * c)) *
          (FFTOps.piece a ao al c (i + j) * valAt b bo bl)) cnt := by
  induction cnt with
  | zero => intro arr i _ _ _ _; exact ⟨Writes.refl .., by simp [chunkLoop, sumRange]⟩
  | succ cnt ih =>
    intro arr i hS hT hcov hsum
    rw [sumRange_succ_left] at hsum ⊢
    simp only [Nat.add_zero] at hsum ⊢
    have hs' : sumRange (fun j => 2 ^ (LA.w * ((i + (j + 1)) * c)) *
        (FFTOps.piece a ao al c (i + (j + 1)) * valAt b bo bl)) cnt = sumRange (fun j =>
          2 ^ (LA.w * ((i + 1 + j) * c)) * (FFTOps.piece a ao al c (i + 1 + j) * valAt b bo bl))
          cnt :=
      sumRange_congr fun j _ => by rw [show i + (j + 1) = i + 1 + j by lia]
    rw [hs'] at hsum ⊢
    rw [chunkLoop]
    -- The product of piece `i` by `B`.
    have hpl : min c (al - i * c) ≤ al := Nat.le_trans (Nat.min_le_right _ _) (Nat.sub_le _ _)
    obtain ⟨⟨p₁, -⟩, p₂⟩ := mulBal_spec cfg (W.zeros (min c (al - i * c) + bl)) 0 a (ao + i * c)
      (min c (al - i * c)) b bo bl (by rw [W.size_zeros]; lia)
    rw [W.size_zeros] at p₁
    have p₂' : valAt (mulBal cfg (W.zeros (min c (al - i * c) + bl)) 0 a (ao + i * c)
        (min c (al - i * c)) b bo bl) 0 (min c (al - i * c) + bl) =
          FFTOps.piece a ao al c i * valAt b bo bl := p₂
    generalize mulBal cfg (W.zeros (min c (al - i * c) + bl)) 0 a (ao + i * c)
      (min c (al - i * c)) b bo bl = P at p₁ p₂'
    -- Added from limb `i c` on.
    obtain ⟨c₁, c₂, c₃⟩ := WordArray.addCoefK_spec arr rs T (i * c) P 0 (min c (al - i * c) + bl)
      hS hT (by
        have := Nat.mul_le_mul_right c (show i ≤ i + (cnt + 1) by lia)
        lia) (by rw [p₁]; lia) (by rw [p₁]; lia) (by rw [p₂']; lia)
    rw [p₂'] at c₃
    generalize WordArray.addCoefK arr rs T (i * c) P 0 (min c (al - i * c) + bl) = X at c₁ c₂ c₃
    obtain ⟨⟨i₁, i₂⟩, i₃⟩ := ih X (i + 1) (by rw [c₁]; exact hS) (by rw [c₁]; exact hT)
      (by rw [show i + 1 + cnt = i + (cnt + 1) by lia]; exact hcov) (by rw [c₃]; lia)
    refine ⟨⟨i₁.trans c₁, fun t ht => (i₂ t ht).trans (c₂ t ht)⟩, ?_⟩
    rw [i₃, c₃]
    lia

/--
`A B` for `bl ≤ al`, by `mulBal` on the pieces of `A` of `bl` limbs, the products added into the
zeroed window, like GMP's `mpn_mul` on unbalanced operands.
-/
@[expose] public def mulChunked (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : A :=
  chunkLoop cfg (al + bl) bl o a ao al b bo bl (WordArray.zeroIntoK d o (al + bl)) 0
    ((al + bl - 1) / bl)

public theorem mulChunked_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (hb : 0 < bl) (hd : o + (al + bl) ≤ LA.size d) (hS : LA.size d < USize.size) :
    Writes (mulChunked cfg d o a ao al b bo bl) d o (al + bl) ∧
      valAt (mulChunked cfg d o a ao al b bo bl) o (al + bl) = valAt a ao al * valAt b bo bl := by
  -- The number of pieces covers `A`, and no more.
  generalize hL : (al + bl - 1) / bl = L
  have hL₁ : al ≤ L * bl := by
    have h₁ := Nat.div_add_mod (al + bl - 1) bl
    have h₂ := Nat.mod_lt (al + bl - 1) hb
    rw [hL, Nat.mul_comm] at h₁
    lia
  have hL₂ : L * bl < al + bl := by
    rw [← hL]
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by lia)
  -- The sum of the products of the pieces is `A B`.
  have hab : sumRange (fun j => 2 ^ (LA.w * ((0 + j) * bl)) *
      (FFTOps.piece a ao al bl (0 + j) * valAt b bo bl)) L = valAt a ao al * valAt b bo bl := by
    rw [← FFTOps.polyVal_pieces a ao al bl L hL₁,
      polyVal_eq_sumRange _ _ L (by rw [FFTOps.length_pieces]; exact Nat.le_refl _),
      sumRange_mul_right]
    exact sumRange_congr fun j hj => by
      rw [FFTOps.getD_pieces, ite_eq_left hj, Nat.zero_add, ← Nat.pow_mul,
        show LA.w * bl * j = LA.w * (j * bl) by rw [Nat.mul_assoc, Nat.mul_comm bl j]]
      grind
  have hablt : valAt a ao al * valAt b bo bl < 2 ^ (LA.w * (al + bl)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' (valAt_lt ..) (valAt_lt ..)
  -- Zeroing the window, and adding the products.
  obtain ⟨⟨z₁, z₂⟩, z₃⟩ := WordArray.zeroIntoK_spec d o (al + bl) hd
  unfold mulChunked
  rw [hL]
  generalize WordArray.zeroIntoK d o (al + bl) = R₀ at z₁ z₂ z₃
  obtain ⟨⟨c₁, c₂⟩, c₃⟩ := chunkLoop_spec cfg (al + bl) bl o a ao al b bo bl (Nat.le_refl _)
    (by lia) L R₀ 0 (by rw [z₁]; exact hS) (by rw [z₁]; exact hd) (by lia)
    (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨⟨c₁.trans z₁, fun i hi => (c₂ i hi).trans (z₂ i hi)⟩, ?_⟩
  rw [c₃, z₃, Nat.zero_add, hab]

/-! ## Products -/

/-- `mul` for `bl ≤ al`. -/
@[expose] public def mulU (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : A :=
  if cfg.mulUnbalanced ≤ bl ∧ 2 * bl ≤ al ∧ (bl < cfg.mulChunkMax ∨ al < cfg.mulFFTUnbal) ∧
      o + (al + bl) ≤ LA.size d ∧ LA.size d < USize.size then
    mulChunked cfg d o a ao al b bo bl
  else mulBal cfg d o a ao al b bo bl

public theorem mulU_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (hd : o + (al + bl) ≤ LA.size d) :
    Writes (mulU cfg d o a ao al b bo bl) d o (al + bl) ∧
      valAt (mulU cfg d o a ao al b bo bl) o (al + bl) = valAt a ao al * valAt b bo bl := by
  unfold mulU
  split
  · rename_i h
    have := cfg.one_le_mulUnbalanced
    exact mulChunked_spec _ _ _ _ _ _ _ _ _ (by lia) hd h.2.2.2.2
  · exact mulBal_spec _ _ _ _ _ _ _ _ _ hd

/--
`A B` into the `al + bl` limbs of `d` from `o` on, with the longer operand first: `mulChunked`
when the longer one has at least twice the limbs of the shorter, which has at least
`mulUnbalanced` limbs, and fewer than `mulChunkMax` unless the longer one is below `mulFFTUnbal`;
`mulBal` otherwise.
-/
@[expose] public def mul (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : A :=
  if bl ≤ al then mulU cfg d o a ao al b bo bl else mulU cfg d o b bo bl a ao al

public theorem mul_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) (hd : o + (al + bl) ≤ LA.size d) :
    Writes (mul cfg d o a ao al b bo bl) d o (al + bl) ∧
      valAt (mul cfg d o a ao al b bo bl) o (al + bl) = valAt a ao al * valAt b bo bl := by
  unfold mul
  split
  · exact mulU_spec _ _ _ _ _ _ _ _ _ hd
  · obtain ⟨s₁, s₂⟩ := mulU_spec cfg d o b bo bl a ao al (by lia)
    rw [Nat.add_comm bl al, Nat.mul_comm] at s₂
    rw [Nat.add_comm bl al] at s₁
    exact ⟨s₁, s₂⟩

/-- `A²` into the `al + al` limbs of `d` from `o` on: by the FFT from `sqrFFT` limbs. -/
@[expose] public def sqr (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat) : A :=
  if cfg.sqrFFT ≤ al then fftSqrW cfg d o a ao al (fftK cfg.fftKFactor (al + al))
  else Toom.sqrToom cfg.toConfig d o a ao al

public theorem sqr_spec (cfg : MulConfig) (d : A) (o : Nat) (a : A) (ao al : Nat)
    (hd : o + (al + al) ≤ LA.size d) :
    Writes (sqr cfg d o a ao al) d o (al + al) ∧
      valAt (sqr cfg d o a ao al) o (al + al) = valAt a ao al * valAt a ao al := by
  unfold sqr
  split
  · exact fftSqrW_spec _ _ _ _ _ _ _ hd
  · exact Toom.sqrToom_spec _ _ _ _ _ _ hd

/-! ## Products modulo `β^N - 1` -/

/--
The size `N` of the modulus `β^N - 1` of `mulModW` for products of `n` limbs: `n` rounded up to a
multiple of the `2ᵏ` pieces of an FFT on `n` limbs.
-/
@[expose] public def modSize (c n : Nat) : Nat :=
  (n + 2 ^ fftK c n - 1) / 2 ^ fftK c n * 2 ^ fftK c n

public theorem le_modSize (c n : Nat) : n ≤ modSize c n := by
  rw [modSize]
  have h₀ : 0 < 2 ^ fftK c n := Nat.two_pow_pos _
  generalize 2 ^ fftK c n = P at *
  have h₁ := Nat.div_add_mod (n + P - 1) P
  have h₂ := Nat.mod_lt (n + P - 1) h₀
  rw [Nat.mul_comm] at h₁
  lia

/--
`A B` modulo `β^N - 1` for `N = modSize c n`, up to a multiple, in a fresh array: by the FFT's
wrapped product (`FFTOps.fftMulModAt`) when the product is longer than the modulus, and otherwise by
`mul`, since it would not wrap. Barrett's division takes its products this way (`NatOps.mulMod`).
-/
@[expose] public def mulModW (cfg : MulConfig) (n : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) : A :=
  let k := fftK cfg.fftKFactor n
  let m := (n + 2 ^ k - 1) / 2 ^ k
  if m * 2 ^ k < al + bl then
    -- The window of the FFT, allocated only when the product wraps.
    let nn := FFTOps.fftModN LA.w k m
    let r := W.zeros (m * 2 ^ k + nn + 1)
    if FFTOps.FFTModCheck r 0 (m * 2 ^ k + nn + 1) a ao al b bo bl k m nn then
      FFTOps.fftMulModAt (mulP cfg.toConfig) r 0 a ao al b bo bl k m nn
    else mul cfg (W.zeros (al + bl)) 0 a ao al b bo bl
  else mul cfg (W.zeros (al + bl)) 0 a ao al b bo bl

public theorem mulModW_spec (cfg : MulConfig) (n : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl : Nat) :
    valAt (mulModW cfg n a ao al b bo bl) 0 (LA.size (mulModW cfg n a ao al b bo bl)) %
        (2 ^ (LA.w * modSize cfg.fftKFactor n) - 1) =
      valAt a ao al * valAt b bo bl % (2 ^ (LA.w * modSize cfg.fftKFactor n) - 1) := by
  have hmul : valAt (mul cfg (W.zeros (al + bl)) 0 a ao al b bo bl) 0
      (LA.size (mul cfg (W.zeros (al + bl)) 0 a ao al b bo bl)) =
        valAt a ao al * valAt b bo bl := by
    obtain ⟨⟨s₁, -⟩, e⟩ := mul_spec cfg (W.zeros (al + bl)) 0 a ao al b bo bl
      (by rw [W.size_zeros]; lia)
    rw [s₁, W.size_zeros, e]
  unfold mulModW modSize
  dsimp only
  split
  · split
    · rename_i h
      obtain ⟨s₁, -, e⟩ := FFTOps.fftMulModAt_spec (mulP cfg.toConfig) _ _ _ _ _ _ _ _ _ _ _
        (FFTOps.FFTModCheck.params h) (isMulP _ _)
      rw [s₁, W.size_zeros]
      exact e
    · rw [hmul]
  · rw [hmul]

end MPN.Dispatch
