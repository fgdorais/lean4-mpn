/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN

/-!
# Threshold tuning

`lake exe tune` measures where each algorithm starts to beat the ones below it on this machine,
like GMP's `tuneup`, and prints the `Config` it finds together with the options that compile it
into the library: for a project that requires it, and on the command line. Pinning it to one
core, for example with `taskset -c 2`, gives steadier results; `--verbose` prints the timings.

Each threshold is found by running the same dispatcher with two configurations: one where the
method starts at the size being measured, and one where it never starts. The products below that
size use the methods below it either way, so the two differ by one step of the method, as in
GMP's `tuneup`. The thresholds are tuned in order, each with the ones found before it.
-/

open ScalarArray MPN

namespace Tune

/-- `n` pseudorandom limbs, with a nonzero top limb. -/
def sample (n seed : Nat) : UInt64Array := Id.run do
  let mut s := seed
  let mut r := UInt64Array.emptyWithCapacity n
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    r := r.push s.toUInt64
  if n > 0 then r := r.set! (n - 1) (r[n - 1]! ||| 1)
  return r

/-- Runs `f a b` `reps` times, folding `check` of each result, constant time, into a checksum. -/
@[noinline] def repeatOp {α β : Type} (f : α → α → β) (check : β → UInt64) (a b : α)
    (reps : Nat) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for _ in [0:reps] do
    acc := acc + check (f a b)
  return acc

/-- The median time of `f a b` in nanoseconds, over trials of at least `minNs` each. -/
def timeOp {α β : Type} (f : α → α → β) (check : β → UInt64) (a b : α) (trials := 7)
    (minNs := 5_000_000) : IO Nat := do
  let mut reps := 1
  repeat
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => repeatOp f check a b reps
    let t₁ ← IO.monoNanosNow
    if t₁ - t₀ ≥ minNs then break
    reps := reps * 2
  let mut samples := #[]
  for _ in [0:trials] do
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => repeatOp f check a b reps
    let t₁ ← IO.monoNanosNow
    samples := samples.push ((t₁ - t₀) / reps)
  return (samples.qsort (· < ·))[trials / 2]!

/--
The smallest size `n` in `sizes` from which `fast n` beats `slow` on the inputs `input n` at `n`
and at the next `confirm` sizes, or `none` if it never does.
-/
def crossoverOn {α β : Type} (slow : α → α → β) (fast : Nat → α → α → β) (check : β → UInt64)
    (input : Nat → α × α) (sizes : List Nat) (confirm := 3) (log : Bool := false) :
    IO (Option Nat) := do
  let mut wins : List Nat := []
  for n in sizes do
    let (a, b) := input n
    let ts ← timeOp slow check a b
    let tf ← timeOp (fast n) check a b
    if log then IO.println s!"  {n}: {ts} ns vs {tf} ns"
    if tf < ts then
      wins := wins ++ [n]
      if wins.length > confirm then return wins.head?
    else
      wins := []
  return wins.head?

/-- The median of `runs` searches, since the timings near a crossover are close. -/
def medianOf (runs : Nat) (search : IO Nat) : IO Nat := do
  let mut found := #[]
  for _ in [0:runs] do
    found := found.push (← search)
  return (found.qsort (· < ·))[runs / 2]!

/-- A threshold beyond every size tried: the method it starts never runs. -/
def never : Nat := 1_000_000_000

/--
Tunes a threshold by `crossoverOn`, three times, with `fallback` and a warning when the faster
side never wins.
-/
def tune {α β : Type} (name : String) (slow : α → α → β) (fast : Nat → α → α → β)
    (check : β → UInt64) (input : Nat → α × α) (sizes : List Nat) (confirm := 3)
    (log : Bool) : IO Nat := medianOf 3 do
  match ← crossoverOn slow fast check input sizes confirm log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    let last := sizes.getLast?.getD 0
    IO.eprintln s!"warning: {name} never won up to {last} limbs; using {last}"
    return last

/-- The sizes `start`, `start + step`, …, below `stop`. -/
def range (start stop step : Nat) : List Nat :=
  (List.range ((stop - start + step - 1) / step)).map (start + step * ·)

/-- A constant-time check of a result. -/
def checkArr (a : UInt64Array) : UInt64 := a.size.toUInt64 + a[0]!

/-- Pseudorandom operands of `m` and `n` limbs. -/
def operands (m n : Nat) : UInt64Array × UInt64Array := (sample m 1, sample n 2)

/-- `a b` by `f`, into a new array. -/
@[inline] def prod (f : UInt64Array.USlice → UInt64Array.USlice → UInt64Array.USlice → UInt64Array)
    (a b : UInt64Array) : UInt64Array :=
  f (UInt64Array.replicate (a.size + b.size) 0).toUSlice a.toUSlice b.toUSlice

/-- `a²` by `f`, into a new array. -/
@[inline] def square (f : UInt64Array.USlice → UInt64Array.USlice → UInt64Array)
    (a _ : UInt64Array) : UInt64Array :=
  f (UInt64Array.replicate (2 * a.size) 0).toUSlice a.toUSlice

/-! ## Products -/

/-- `c` without splitting unbalanced products. -/
def noSplit (c : Config) : Config :=
  { c with mulUnbalanced := never, one_le_mulUnbalanced := by decide }

def tuneKaratsuba (log : Bool) : IO Nat :=
  tune "Karatsuba"
    (prod (mulKaratsuba { mulKaratsuba := never, four_le_mulKaratsuba := by decide }))
    (fun n => prod (mulKaratsuba { mulKaratsuba := max 4 n, four_le_mulKaratsuba := by lia }))
    checkArr (fun n => operands n n) (range 8 256 4) (log := log)

def tuneToom3 (base : Config) (log : Bool) : IO Nat :=
  let cfg : Config := { base with
    mulToom4 := never, thirtytwo_le_mulToom4 := by decide,
    mulToom6 := never, thirtytwo_le_mulToom6 := by decide }
  tune "Toom-3" (prod (mulToom { cfg with mulToom3 := never, twelve_le_mulToom3 := by decide }))
    (fun n => prod (mulToom { cfg with mulToom3 := max 12 n, twelve_le_mulToom3 := by lia }))
    checkArr (fun n => operands n n) (range 64 1024 16) (log := log)

def tuneToom4 (base : Config) (log : Bool) : IO Nat :=
  let cfg : Config := { base with mulToom6 := never, thirtytwo_le_mulToom6 := by decide }
  tune "Toom-4" (prod (mulToom { cfg with mulToom4 := never, thirtytwo_le_mulToom4 := by decide }))
    (fun n => prod (mulToom { cfg with mulToom4 := max 32 n, thirtytwo_le_mulToom4 := by lia }))
    checkArr (fun n => operands n n) (range 128 1600 32) (log := log)

def tuneToom6 (base : Config) (log : Bool) : IO Nat :=
  tune "Toom-6" (prod (mulToom { base with mulToom6 := never, thirtytwo_le_mulToom6 := by decide }))
    (fun n => prod (mulToom { base with mulToom6 := max 32 n, thirtytwo_le_mulToom6 := by lia }))
    checkArr (fun n => operands n n) (range 256 2560 64) (log := log)

def tuneFFT (base : Config) (log : Bool) : IO Nat :=
  let cfg := noSplit { base with mulFFTUnbal := never, mulFFTMin := 0 }
  tune "the FFT" (prod (MPN.mul { cfg with mulFFT := never }))
    (fun n => prod (MPN.mul { cfg with mulFFT := n })) checkArr (fun n => operands n n)
    (range 1024 12288 512) (confirm := 2) (log := log)

/-- Tunes `mulFFTUnbal` on operands of `n` and `n / 2` limbs, below `mulFFT`. -/
def tuneFFTUnbal (base : Config) (log : Bool) : IO Nat :=
  let cfg := noSplit { base with mulFFTMin := 0 }
  tune "the FFT at 2:1" (prod (MPN.mul { cfg with mulFFTUnbal := never }))
    (fun n => prod (MPN.mul { cfg with mulFFTUnbal := n }))
    checkArr (fun n => operands n (n / 2)) (range 1024 base.mulFFT 256) (confirm := 2)
    (log := log)

/-- Tunes `mulFFTMin` on operands of 16384 and `n` limbs. -/
def tuneFFTMin (base : Config) (log : Bool) : IO Nat :=
  let cfg := noSplit base
  tune "the FFT on a small operand" (prod (MPN.mul { cfg with mulFFTMin := never }))
    (fun n => prod (MPN.mul { cfg with mulFFTMin := n }))
    checkArr (fun n => operands 16384 n) (range 64 1024 32) (log := log)

/-- Tunes `mulUnbalanced` on operands of `4 n` and `n` limbs. -/
def tuneUnbalanced (base : Config) (log : Bool) : IO Nat :=
  tune "splitting" (prod (MPN.mul (noSplit base)))
    (fun n => prod (MPN.mul { base with mulUnbalanced := max 1 n, one_le_mulUnbalanced := by lia }))
    checkArr (fun n => operands (4 * n) n) (range 16 512 8) (log := log)

/--
Tunes `mulChunkMax` on operands of `8 n` and `n` limbs: where one FFT on the whole product beats
the products of the pieces.
-/
def tuneChunkMax (base : Config) (log : Bool) : IO Nat :=
  tune "one FFT over the pieces" (prod (MPN.mul { base with mulChunkMax := never }))
    (fun n => prod (MPN.mul { base with mulChunkMax := n }))
    checkArr (fun n => operands (8 * n) n) (range 384 3072 128) (confirm := 2) (log := log)

/-! ## Squares -/

def tuneSqrKaratsuba (log : Bool) : IO Nat :=
  tune "Karatsuba squaring"
    (square (sqrKaratsuba { sqrKaratsuba := never, four_le_sqrKaratsuba := by decide }))
    (fun n => square (sqrKaratsuba { sqrKaratsuba := max 4 n, four_le_sqrKaratsuba := by lia }))
    checkArr (fun n => operands n n) (range 16 400 8) (log := log)

def tuneSqrToom3 (base : Config) (log : Bool) : IO Nat :=
  let cfg : Config := { base with
    sqrToom4 := never, thirtytwo_le_sqrToom4 := by decide,
    sqrToom6 := never, thirtytwo_le_sqrToom6 := by decide }
  tune "Toom-3 squaring"
    (square (sqrToom { cfg with sqrToom3 := never, twelve_le_sqrToom3 := by decide }))
    (fun n => square (sqrToom { cfg with sqrToom3 := max 12 n, twelve_le_sqrToom3 := by lia }))
    checkArr (fun n => operands n n) (range 128 1600 32) (log := log)

/-- Tunes `sqrToom4`, which `sqrToom` takes from `sqrToom3` on, so above it. -/
def tuneSqrToom4 (base : Config) (log : Bool) : IO Nat :=
  let cfg : Config := { base with sqrToom6 := never, thirtytwo_le_sqrToom6 := by decide }
  tune "Toom-4 squaring"
    (square (sqrToom { cfg with sqrToom4 := never, thirtytwo_le_sqrToom4 := by decide }))
    (fun n => square (sqrToom { cfg with sqrToom4 := max 32 n, thirtytwo_le_sqrToom4 := by lia }))
    checkArr (fun n => operands n n) (range base.sqrToom3 2400 48) (log := log)

def tuneSqrToom6 (base : Config) (log : Bool) : IO Nat :=
  tune "Toom-6 squaring"
    (square (sqrToom { base with sqrToom6 := never, thirtytwo_le_sqrToom6 := by decide }))
    (fun n => square (sqrToom { base with sqrToom6 := max 32 n, thirtytwo_le_sqrToom6 := by lia }))
    checkArr (fun n => operands n n) (range base.sqrToom3 3200 64) (log := log)

def tuneSqrFFT (base : Config) (log : Bool) : IO Nat :=
  tune "FFT squaring" (square (MPN.sqr { base with sqrFFT := never }))
    (fun n => square (MPN.sqr { base with sqrFFT := n })) checkArr (fun n => operands n n)
    (range 1024 8192 256) (confirm := 2) (log := log)

/-! ## Division, gcd and decimal strings -/

/--
A normalized division of `2 n` by `n` limbs: `V` with its top bit set, and `U < V βⁿ` with the top
bit of its top limb clear.
-/
def divOperands (n : Nat) : UInt64Array × UInt64Array :=
  let v := sample n 2
  let u := sample (2 * n) 1
  (u.set! (2 * n - 1) (u[2 * n - 1]! &&& 0x7FFFFFFFFFFFFFFF),
    v.set! (n - 1) (v[n - 1]! ||| 0x8000000000000000))

/-- The quotient of `divOperands`, by `ops64B.divNorm` with threshold `T`. -/
def divNormWith (T : Nat) (u v : UInt64Array) : UInt64Array :=
  (ops64B.divNorm divBase64 T u v v.size v.size).1

/-- Tunes `divDC`: where one level of division by blocks beats the schoolbook method. -/
def tuneDivDC (log : Bool) : IO Nat :=
  tune "division by blocks" (divNormWith never) divNormWith checkArr divOperands
    (range 64 1600 32) (log := log)

def tuneGcdHalf (log : Bool) : IO Nat :=
  tune "half-gcd" (gcdWith never) gcdWith checkArr (fun n => operands n n) (range 256 4096 128)
    (confirm := 2) (log := log)

def tuneStrDC (log : Bool) : IO Nat :=
  tune "writing by divide and conquer" (fun a _ => toDecimalWith never a)
    (fun n a _ => toDecimalWith n a) (·.utf8ByteSize.toUInt64) (fun n => operands n n)
    (range 8 200 4) (log := log)

/-- Tunes `parseDC` on strings of `19 n` digits. -/
def tuneParseDC (log : Bool) : IO Nat :=
  let digits (n : Nat) : String :=
    String.ofList ((List.range (19 * n)).map fun i => Char.ofNat (48 + (i * 7 + i / 3) % 10))
  tune "reading by divide and conquer" (fun s (_ : String) => ofDecimalWith never s)
    (fun n s _ => ofDecimalWith n s) (fun r => checkArr (r.getD (.replicate 1 0)))
    (fun n => (digits n, digits n)) (range 64 2048 64) (log := log)

end Tune

open Tune in
public def main (args : List String) : IO UInt32 := do
  let log := args.contains "--verbose"
  IO.println "Tuning the lean4-mpn thresholds; this takes several minutes."
  IO.println "mulKaratsuba: one Karatsuba step against schoolbook"
  let karatsuba ← tuneKaratsuba log
  let c₁ : Config := { mulKaratsuba := max 4 karatsuba, four_le_mulKaratsuba := by lia }
  IO.println "mulToom3: one step of Toom-3 against Karatsuba"
  let toom3 ← tuneToom3 c₁ log
  let c₂ := { c₁ with mulToom3 := max 12 toom3, twelve_le_mulToom3 := by lia }
  IO.println "mulToom4: one step of Toom-4 against the methods below it"
  let toom4 ← tuneToom4 c₂ log
  let c₃ := { c₂ with mulToom4 := max 32 toom4, thirtytwo_le_mulToom4 := by lia }
  IO.println "mulToom6: one step of Toom-6 against the methods below it"
  let toom6 ← tuneToom6 c₃ log
  let c₄ := { c₃ with mulToom6 := max 32 toom6, thirtytwo_le_mulToom6 := by lia }
  IO.println "mulFFT: the FFT against the Toom methods"
  let fft ← tuneFFT c₄ log
  let c₅ := { c₄ with mulFFT := fft }
  IO.println "mulFFTUnbal: the FFT against the Toom methods, at 2:1"
  let fftUnbal ← tuneFFTUnbal c₅ log
  let c₆ := { c₅ with mulFFTUnbal := fftUnbal }
  IO.println "mulFFTMin: the FFT against schoolbook on a small operand, by 16384 limbs"
  let fftMin ← tuneFFTMin c₆ log
  let c₇ := { c₆ with mulFFTMin := fftMin }
  IO.println "mulUnbalanced: products of pieces against one product, at 4:1"
  let unbalanced ← tuneUnbalanced c₇ log
  let c₈ := { c₇ with mulUnbalanced := max 1 unbalanced, one_le_mulUnbalanced := by lia }
  IO.println "mulChunkMax: one FFT against products of pieces, at 8:1"
  let chunkMax ← tuneChunkMax c₈ log
  let c₉ := { c₈ with mulChunkMax := chunkMax }
  IO.println "sqrKaratsuba: one Karatsuba square against the schoolbook square"
  let sqrKaratsuba ← tuneSqrKaratsuba log
  let s₁ := { c₉ with sqrKaratsuba := max 4 sqrKaratsuba, four_le_sqrKaratsuba := by lia }
  IO.println "sqrToom3: one Toom-3 square against Karatsuba squaring"
  let sqrToom3 ← tuneSqrToom3 s₁ log
  let s₂ := { s₁ with sqrToom3 := max 12 sqrToom3, twelve_le_sqrToom3 := by lia }
  IO.println "sqrToom4: one Toom-4 square against the squares below it"
  let sqrToom4 ← tuneSqrToom4 s₂ log
  let s₃ := { s₂ with sqrToom4 := max 32 sqrToom4, thirtytwo_le_sqrToom4 := by lia }
  IO.println "sqrToom6: one Toom-6 square against the squares below it"
  let sqrToom6 ← tuneSqrToom6 s₃ log
  let s₄ := { s₃ with sqrToom6 := max 32 sqrToom6, thirtytwo_le_sqrToom6 := by lia }
  IO.println "sqrFFT: the FFT square against the Toom squares"
  let sqrFFT ← tuneSqrFFT s₄ log
  IO.println "divDC: one level of division by blocks against the schoolbook method, at 2n / n"
  let divDC ← tuneDivDC log
  IO.println "gcdHalf: half-gcd against Lehmer's algorithm"
  let gcdHalf ← tuneGcdHalf log
  IO.println "strDC: writing decimal digits by divide and conquer against the base case"
  let strDC ← tuneStrDC log
  IO.println "parseDC: reading decimal digits by divide and conquer against the base case"
  let parseDC ← tuneParseDC log
  let cfg : Config := { s₄ with sqrFFT, divDC, gcdHalf, strDC, parseDC }
  IO.println ""
  IO.println s!"Found:   {repr cfg}"
  IO.println s!"Default: {repr ({} : Config)}"
  IO.println ""
  let opts := [("mulKaratsuba", cfg.mulKaratsuba), ("mulToom3", cfg.mulToom3),
    ("mulToom4", cfg.mulToom4), ("mulToom6", cfg.mulToom6), ("mulFFT", cfg.mulFFT),
    ("mulFFTUnbal", cfg.mulFFTUnbal), ("mulFFTMin", cfg.mulFFTMin),
    ("mulUnbalanced", cfg.mulUnbalanced), ("mulChunkMax", cfg.mulChunkMax),
    ("sqrKaratsuba", cfg.sqrKaratsuba), ("sqrToom3", cfg.sqrToom3), ("sqrToom4", cfg.sqrToom4),
    ("sqrToom6", cfg.sqrToom6), ("sqrFFT", cfg.sqrFFT), ("divDC", cfg.divDC),
    ("gcdHalf", cfg.gcdHalf), ("strDC", cfg.strDC), ("parseDC", cfg.parseDC)]
  IO.println "To compile these into the library, add to its `require` in lakefile.toml:"
  IO.println s!"  options = \{ {", ".intercalate (opts.map fun (k, v) => s!"{k} = \"{v}\"")} }"
  IO.println "or build this package with:"
  IO.println s!"  lake build -R {" ".intercalate (opts.map fun (k, v) => s!"-K {k}={v}")}"
  return 0
