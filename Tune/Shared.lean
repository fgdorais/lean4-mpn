/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN
public import Tune.Harness

/-!
# The tuning of the shared thresholds

The thresholds of `MPN`'s dispatchers, tuned the same way for any width: the Toom methods,
Karatsuba's above the width's base case, the FFT and unbalanced products (`tuneMul`), the same for
squares (`tuneSqr`), and division by blocks and by Barrett's method (`tuneDiv`). Each threshold is
found by running the same dispatcher with two configurations, one where the method starts at the
size measured and one where it never starts, so that the two differ by one step of the method, as
in GMP's `tuneup`; they are tuned in order, each with the ones found before it.

The sizes searched are those of 64-bit limbs times `64 / w`, since a threshold in limbs grows about
as the limbs get shorter.
-/

open MPN

namespace Tune

/-- A threshold beyond every size tried: the method it starts never runs. -/
public def never : Nat := 1_000_000_000

variable {A L : Type} [LA : MPN.LimbArray A L] [W : MPN.WordArray A L] [F : MPN.WordFolds A L]
  [B : MPN.Toom.ToomBase A L]

/-- Pseudorandom operands of `m` and `n` limbs. -/
def operandsW (m n : Nat) : A × A := (sample m 1, sample n 2)

/-- `a b` by the Toom methods with `cfg`. -/
def toomW (cfg : Toom.Config) (a b : A) : A :=
  Toom.mulToom cfg (W.zeros (LA.size a + LA.size b)) 0 a 0 (LA.size a) b 0 (LA.size b)

/-- `a b` by Karatsuba's method with `cfg`. -/
def karatsubaW (cfg : Toom.Config) (a b : A) : A :=
  Toom.mulKaratsuba cfg (W.zeros (LA.size a + LA.size b)) 0 a 0 (LA.size a) b 0 (LA.size b)

/-- `a²` by the Toom squares with `cfg`. -/
def sqrToomW (cfg : Toom.Config) (a _ : A) : A :=
  Toom.sqrToom cfg (W.zeros (2 * LA.size a)) 0 a 0 (LA.size a)

/-- `a²` by Karatsuba's square with `cfg`. -/
def sqrKaratsubaW (cfg : Toom.Config) (a _ : A) : A :=
  Toom.sqrKaratsuba cfg (W.zeros (2 * LA.size a)) 0 a 0 (LA.size a)

/-- `a b` by `Dispatch.mul` with `cfg`. -/
def mulW (cfg : Dispatch.MulConfig) (a b : A) : A :=
  Dispatch.mul cfg (W.zeros (LA.size a + LA.size b)) 0 a 0 (LA.size a) b 0 (LA.size b)

/-- `a²` by `Dispatch.sqr` with `cfg`. -/
def sqrW (cfg : Dispatch.MulConfig) (a _ : A) : A :=
  Dispatch.sqr cfg (W.zeros (2 * LA.size a)) 0 a 0 (LA.size a)

/-- The sizes `start`, …, below `stop`, by `step`, all times `64 / w`. -/
def scaled (start stop step : Nat) : List Nat :=
  let s := max 1 (64 / LA.w)
  range (s * start) (s * stop) (s * step)

/-- `c` without the unbalanced Toom methods. -/
def noShapes (c : Dispatch.MulConfig) : Dispatch.MulConfig :=
  { c with
    mulToom32 := never, twelve_le_mulToom32 := (by decide),
    mulToom42 := never, twelve_le_mulToom42 := (by decide),
    mulToom43 := never, thirtytwo_le_mulToom43 := by decide }

/-- `c` without splitting unbalanced products. -/
def noSplit (c : Dispatch.MulConfig) : Dispatch.MulConfig :=
  { c with mulUnbalanced := never, one_le_mulUnbalanced := by decide }

/-! ## Products -/

/--
The thresholds of products, from `base`, in order: Karatsuba's method, Toom-3, Toom-3 by 2 at
`7 : 4`, Toom-4 by 2 at `7 : 2`, Toom-4, Toom-4 by 3 at `8 : 5`, Toom-6, the FFT, the FFT at
`2 : 1`, the FFT with a small operand, splitting at `4 : 1`, and one FFT over the pieces at `8 : 1`.
-/
public def tuneMul (base : Dispatch.MulConfig) (log : Bool) : IO Dispatch.MulConfig := do
  let c := checkA (A := A)
  IO.println "mulKaratsuba: one Karatsuba step against the base case"
  let kar ← tune "Karatsuba"
    (karatsubaW (A := A)
      { base.toConfig with mulKaratsuba := never, four_le_mulKaratsuba := by decide })
    (fun n => karatsubaW
      { base.toConfig with mulKaratsuba := max 4 n, four_le_mulKaratsuba := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 8 256 4) (log := log)
  let b : Dispatch.MulConfig := { base with
    mulKaratsuba := max 4 kar, four_le_mulKaratsuba := (by lia),
    mulToom8 := never, sixtyfour_le_mulToom8 := by decide }
  IO.println "mulToom3: one step of Toom-3 against Karatsuba"
  let t := { noShapes b with
    mulToom4 := never, thirtytwo_le_mulToom4 := (by decide),
    mulToom6 := never, thirtytwo_le_mulToom6 := by decide }
  let toom3 ← tune "Toom-3"
    (toomW (A := A) { t.toConfig with mulToom3 := never, twelve_le_mulToom3 := by decide })
    (fun n => toomW { t.toConfig with mulToom3 := max 12 n, twelve_le_mulToom3 := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 64 1024 16) (log := log)
  let b := { b with mulToom3 := max 12 toom3, twelve_le_mulToom3 := by lia }
  IO.println "mulToom32: one step of Toom-3 by 2 against the methods below it, at 7:4"
  let t := (noShapes b).toConfig
  let toom32 ← tune "Toom-3 by 2" (toomW (A := A) t)
    (fun n => toomW { t with mulToom32 := max 12 n, twelve_le_mulToom32 := by lia })
    c (fun n => operandsW (7 * n / 4) n) (scaled (A := A) 16 800 8) (log := log)
  IO.println "mulToom42: one step of Toom-4 by 2 against the methods below it, at 7:2"
  let toom42 ← tune "Toom-4 by 2" (toomW (A := A) t)
    (fun n => toomW { t with mulToom42 := max 12 n, twelve_le_mulToom42 := by lia })
    c (fun n => operandsW (7 * n / 2) n) (scaled (A := A) 16 800 8) (log := log)
  let b := { b with
    mulToom32 := max 12 toom32, twelve_le_mulToom32 := (by lia),
    mulToom42 := max 12 toom42, twelve_le_mulToom42 := by lia }
  IO.println "mulToom4: one step of Toom-4 against the methods below it"
  let t := { b.toConfig with mulToom6 := never, thirtytwo_le_mulToom6 := by decide }
  let toom4 ← tune "Toom-4"
    (toomW (A := A) { t with mulToom4 := never, thirtytwo_le_mulToom4 := by decide })
    (fun n => toomW { t with mulToom4 := max 32 n, thirtytwo_le_mulToom4 := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 128 1600 32) (log := log)
  let b := { b with mulToom4 := max 32 toom4, thirtytwo_le_mulToom4 := by lia }
  IO.println "mulToom43: one step of Toom-4 by 3 against the methods below it, at 8:5"
  let t := { b.toConfig with mulToom43 := never, thirtytwo_le_mulToom43 := by decide }
  let toom43 ← tune "Toom-4 by 3" (toomW (A := A) t)
    (fun n => toomW { t with mulToom43 := max 32 n, thirtytwo_le_mulToom43 := by lia })
    c (fun n => operandsW (8 * n / 5) n) (scaled (A := A) 32 1200 16) (log := log)
  let b := { b with mulToom43 := max 32 toom43, thirtytwo_le_mulToom43 := by lia }
  IO.println "mulToom6: one step of Toom-6 against the methods below it"
  let toom6 ← tune "Toom-6"
    (toomW (A := A) { b.toConfig with mulToom6 := never, thirtytwo_le_mulToom6 := by decide })
    (fun n => toomW { b.toConfig with mulToom6 := max 32 n, thirtytwo_le_mulToom6 := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 256 2560 64) (log := log)
  let b := { b with mulToom6 := max 32 toom6, thirtytwo_le_mulToom6 := by lia }
  IO.println "mulToom8: one step of Toom-8 against the methods below it"
  let toom8 ← tune "Toom-8" (toomW (A := A) b.toConfig)
    (fun n => toomW { b.toConfig with mulToom8 := max 64 n, sixtyfour_le_mulToom8 := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 768 4096 128) (log := log)
  let b := { b with mulToom8 := max 64 toom8, sixtyfour_le_mulToom8 := by lia }
  IO.println "mulFFT: the FFT against the Toom methods"
  let m := noSplit { b with mulFFTUnbal := never, mulFFTMin := 0 }
  let fft ← tune "the FFT" (mulW (A := A) { m with mulFFT := never })
    (fun n => mulW { m with mulFFT := n }) c (fun n => operandsW n n)
    (scaled (A := A) 1024 12288 512)
    (confirm := 2) (log := log)
  let b := { b with mulFFT := fft }
  IO.println "mulFFTUnbal: the FFT against the Toom methods, at 2:1"
  let m := noSplit { b with mulFFTMin := 0 }
  let fftUnbal ← tune "the FFT at 2:1" (mulW (A := A) { m with mulFFTUnbal := never })
    (fun n => mulW { m with mulFFTUnbal := n }) c (fun n => operandsW n (n / 2))
    (range (fft / 4) fft (max 1 (fft / 16))) (confirm := 2) (log := log)
  let b := { b with mulFFTUnbal := fftUnbal }
  IO.println "mulFFTMin: the FFT against the Toom methods on a small operand"
  let big := 4 * fft
  let fftMin ← tune "the FFT on a small operand"
    (mulW (A := A) { noSplit b with mulFFTMin := never })
    (fun n => mulW { noSplit b with mulFFTMin := n }) c (fun n => operandsW big n)
    (scaled (A := A) 64 1024 32) (log := log)
  let b := { b with mulFFTMin := fftMin }
  IO.println "mulUnbalanced: products of pieces against one product, at 4:1"
  let unbalanced ← tune "splitting" (mulW (A := A) (noSplit b))
    (fun n => mulW { b with mulUnbalanced := max 1 n, one_le_mulUnbalanced := by lia })
    c (fun n => operandsW (4 * n) n) (scaled (A := A) 16 512 8) (log := log)
  let b := { b with mulUnbalanced := max 1 unbalanced, one_le_mulUnbalanced := by lia }
  IO.println "mulChunkMax: one FFT against products of pieces, at 8:1"
  let chunkMax ← tune "one FFT over the pieces" (mulW (A := A) { b with mulChunkMax := never })
    (fun n => mulW { b with mulChunkMax := n }) c (fun n => operandsW (8 * n) n)
    (range (fft / 8) (3 * fft / 4) (max 1 (fft / 32))) (confirm := 2) (log := log)
  return { b with mulChunkMax := chunkMax }

/-! ## Squares -/

/--
The thresholds of squares, from `base`: Karatsuba's, Toom-3, Toom-4, Toom-6, Toom-8 and the FFT.
-/
public def tuneSqr (base : Dispatch.MulConfig) (log : Bool) : IO Dispatch.MulConfig := do
  let c := checkA (A := A)
  IO.println "sqrKaratsuba: one Karatsuba square against the base case"
  let kar ← tune "Karatsuba squaring"
    (sqrKaratsubaW (A := A)
      { base.toConfig with sqrKaratsuba := never, four_le_sqrKaratsuba := by decide })
    (fun n => sqrKaratsubaW
      { base.toConfig with sqrKaratsuba := max 4 n, four_le_sqrKaratsuba := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 16 400 8) (log := log)
  let b := { base with
    sqrKaratsuba := max 4 kar, four_le_sqrKaratsuba := (by lia),
    sqrToom8 := never, sixtyfour_le_sqrToom8 := by decide }
  IO.println "sqrToom3: one Toom-3 square against Karatsuba squaring"
  let t := { b.toConfig with
    sqrToom4 := never, thirtytwo_le_sqrToom4 := (by decide),
    sqrToom6 := never, thirtytwo_le_sqrToom6 := by decide }
  let toom3 ← tune "Toom-3 squaring"
    (sqrToomW (A := A) { t with sqrToom3 := never, twelve_le_sqrToom3 := by decide })
    (fun n => sqrToomW { t with sqrToom3 := max 12 n, twelve_le_sqrToom3 := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 128 1600 32) (log := log)
  let b := { b with sqrToom3 := max 12 toom3, twelve_le_sqrToom3 := by lia }
  IO.println "sqrToom4: one Toom-4 square against the squares below it"
  let t := { b.toConfig with sqrToom6 := never, thirtytwo_le_sqrToom6 := by decide }
  let toom4 ← tune "Toom-4 squaring"
    (sqrToomW (A := A) { t with sqrToom4 := never, thirtytwo_le_sqrToom4 := by decide })
    (fun n => sqrToomW { t with sqrToom4 := max 32 n, thirtytwo_le_sqrToom4 := by lia })
    c (fun n => operandsW n n) (range b.sqrToom3 (3 * b.sqrToom3 + 1) (max 1 (b.sqrToom3 / 16)))
    (log := log)
  let b := { b with sqrToom4 := max 32 toom4, thirtytwo_le_sqrToom4 := by lia }
  IO.println "sqrToom6: one Toom-6 square against the squares below it"
  let toom6 ← tune "Toom-6 squaring"
    (sqrToomW (A := A) { b.toConfig with sqrToom6 := never, thirtytwo_le_sqrToom6 := by decide })
    (fun n => sqrToomW { b.toConfig with sqrToom6 := max 32 n, thirtytwo_le_sqrToom6 := by lia })
    c (fun n => operandsW n n) (range b.sqrToom3 (4 * b.sqrToom3 + 1) (max 1 (b.sqrToom3 / 12)))
    (log := log)
  let b := { b with sqrToom6 := max 32 toom6, thirtytwo_le_sqrToom6 := by lia }
  IO.println "sqrToom8: one Toom-8 square against the squares below it"
  let toom8 ← tune "Toom-8 squaring" (sqrToomW (A := A) b.toConfig)
    (fun n => sqrToomW { b.toConfig with sqrToom8 := max 64 n, sixtyfour_le_sqrToom8 := by lia })
    c (fun n => operandsW n n) (scaled (A := A) 1024 5120 128) (log := log)
  let b := { b with sqrToom8 := max 64 toom8, sixtyfour_le_sqrToom8 := by lia }
  IO.println "sqrFFT: the FFT square against the Toom squares"
  let fft ← tune "FFT squaring" (sqrW (A := A) { b with sqrFFT := never })
    (fun n => sqrW { b with sqrFFT := n }) c (fun n => operandsW n n)
    (scaled (A := A) 1024 8192 256)
    (confirm := 2) (log := log)
  return { b with sqrFFT := fft }

/-! ## Division -/

/--
A normalized division of `2 n` by `n` limbs: `V` with its top bit set, and `U < V βⁿ` with the top
bit of its top limb clear.
-/
def divOperandsW (n : Nat) : A × A :=
  let top := 2 ^ (LA.w - 1)
  let v : A := sample n 2
  let u : A := sample (2 * n) 1
  (LA.set u (2 * n - 1) (LA.val (LA.get u (2 * n - 1)) % top),
    LA.set v (n - 1) (LA.val (LA.get v (n - 1)) % top + top))

/--
The thresholds of division, on the width's instance `o` of `NatOps` with its schoolbook division
`base`, reading arrays by `toO`: one level of division by blocks against the schoolbook method,
then Barrett's division with Newton's reciprocal against division by blocks, with the remainder
(`divMu`) and the quotient alone (`divQMu`), all at `2 n / n`.
-/
public def tuneDiv {α : Type} (o : NatOps α) (base : α → α → α × α) (toO : A → α)
    (checkO : α → UInt64) (log : Bool) : IO Dispatch.DivConfig := do
  let off : Dispatch.DivConfig := { divDC := never, divMu := never, divQMu := never }
  let divR (cfg : Dispatch.DivConfig) (u v : A) : α :=
    (Dispatch.divN o cfg base (toO u) (toO v) (LA.size v) (LA.size v)).2
  let divQ (cfg : Dispatch.DivConfig) (u v : A) : α :=
    Dispatch.divQN o cfg base (toO u) (toO v) (LA.size v) (LA.size v)
  IO.println "divDC: one level of division by blocks against the schoolbook method, at 2n / n"
  let dc ← tune "division by blocks" (divR off) (fun n => divR { off with divDC := n }) checkO
    (fun n => divOperandsW n) (scaled (A := A) 16 1600 16) (log := log)
  IO.println "divMu: Barrett's division against division by blocks, at 2n / n"
  let b := { off with divDC := dc }
  let mu ← tune "Barrett's division" (divR b) (fun n => divR { b with divMu := n }) checkO
    (fun n => divOperandsW n) (scaled (A := A) 1024 16384 1024) (confirm := 2) (log := log)
  IO.println "divQMu: Barrett's quotient alone against division by blocks, at 2n / n"
  let b := { b with divMu := mu }
  let qmu ← tune "Barrett's quotient" (divQ b) (fun n => divQ { b with divQMu := n }) checkO
    (fun n => divOperandsW n) (scaled (A := A) 1024 16384 1024) (confirm := 2) (log := log)
  return { b with divQMu := qmu }

end Tune
