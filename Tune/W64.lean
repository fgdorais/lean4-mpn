/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN64
import Tune.Harness
import Tune.Shared

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

open ScalarArray MPN MPN.W64

namespace Tune

/-- A constant-time check of a result. -/
def checkArr (a : UInt64Array) : UInt64 := checkA a

/-- Pseudorandom operands of `m` and `n` limbs. -/
def operands (m n : Nat) : UInt64Array × UInt64Array := (sample m 1, sample n 2)

/-! ## Division, gcd and decimal strings -/

/--
A normalized division of `2 n` by `n` limbs: `V` with its top bit set, and `U < V βⁿ` with the top
bit of its top limb clear.
-/
def divOperands (n : Nat) : UInt64Array × UInt64Array :=
  let v : UInt64Array := sample n 2
  let u : UInt64Array := sample (2 * n) 1
  (u.set! (2 * n - 1) (u[2 * n - 1]! &&& 0x7FFFFFFFFFFFFFFF),
    v.set! (n - 1) (v[n - 1]! ||| 0x8000000000000000))

/--
Tunes `div32Recip`: where schoolbook division of `2 n` by `n` limbs with GMP's 3-by-2 steps with a
precomputed reciprocal beats the steps by the hardware divider, or `1000000`, never, if it does
not win up to 512 limbs.
-/
def tuneDiv32Recip (log : Bool) : IO Nat := medianOf 3 do
  let div (t : USize) (a b : UInt64Array) : UInt64Array :=
    (divRemWith t a.toUSlice b.toUSlice).1
  match ← crossoverOn (div 4294967295) (fun n => div n.toUSize) checkArr divOperands
      [4, 6, 8, 12, 16, 24, 32, 40, 48, 56, 64, 80, 96, 128, 192, 256, 384, 512] 3 log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    if log then IO.println "  the hardware divider always won"
    return 1000000

/--
Tunes `div1Recip`: where division by a normalized limb with Möller and Granlund's steps with a
precomputed reciprocal beats the hardware divider, or `1000000`, never, if it does not win up to
512 limbs.
-/
def tuneDiv1Recip (log : Bool) : IO Nat := medianOf 3 do
  let div1 (t : USize) (a _ : UInt64Array) : UInt64Array × UInt64 :=
    divRem1With t 4294967295 (UInt64Array.replicate a.size 0).toUSlice a.toUSlice
      0xF123456789ABCDEF
  match ← crossoverOn (div1 4294967295) (fun n => div1 n.toUSize)
      (fun p => p.2 + p.1.size.toUInt64)
      (fun n => operands n n) [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512]
      3 log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    if log then IO.println "  the hardware divider always won"
    return 1000000

/-- `n` pseudorandom limbs as a number. -/
def sampleNat (n seed : Nat) : MPN.W64.Nat :=
  MPN.W64.Nat.ofLimbs (Limbs64.norm (sample (A := UInt64Array) n seed)) (Limbs64.isTrim_norm _)

/--
Tunes `sqrtBase`: the largest root, in limbs, that Zimmermann's recursion finishes by Newton's
iteration, from where one level of the recursion on roots of `n` limbs, with Newton's iteration
below, beats Newton's iteration on the whole root.
-/
def tuneSqrtBase (log : Bool) : IO Nat := medianOf 3 do
  match ← crossoverOn (fun x (_ : MPN.W64.Nat) => MPN.W64.Nat.sqrtWith 1 never x)
      (fun n x _ => MPN.W64.Nat.sqrtWith 1 (n - 1) x) (fun r => checkArr r.limbs)
      (fun n => (sampleNat (2 * n) 1, sampleNat (2 * n) 1))
      [2, 3, 4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 128] 3 log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n - 1
  | none =>
    IO.eprintln "warning: one level of Zimmermann's recursion never won up to 128 limbs; using 128"
    return 128

/--
Tunes `sqrtZimmermann`: the size of the root, in limbs, from which Zimmermann's recursion, down to
roots of `T` limbs, beats Newton's iteration.
-/
def tuneSqrtZimmermann (T : Nat) (log : Bool) : IO Nat := medianOf 3 do
  match ← crossoverOn (fun x (_ : MPN.W64.Nat) => MPN.W64.Nat.sqrtWith never T x)
      (fun _ x _ => MPN.W64.Nat.sqrtWith 1 T x) (fun r => checkArr r.limbs)
      (fun n => (sampleNat (2 * n) 1, sampleNat (2 * n) 1))
      [1, 2, 3, 4, 6, 8, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128, 192, 256] 3 log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Zimmermann's recursion never won up to 256 limbs; using 256"
    return 256

/--
Tunes `div1Unnorm`: where division by an unnormalized limb with the steps with the reciprocal,
after a shift, beats the hardware divider, or `1000000`, never, if it does not win up to 512 limbs.
-/
def tuneDiv1Unnorm (log : Bool) : IO Nat := medianOf 3 do
  let div1 (tu : USize) (a _ : UInt64Array) : UInt64Array × UInt64 :=
    divRem1With 4294967295 tu (UInt64Array.replicate a.size 0).toUSlice a.toUSlice
      0x0123456789ABCDEF
  match ← crossoverOn (div1 4294967295) (fun n => div1 n.toUSize)
      (fun p => p.2 + p.1.size.toUInt64) (fun n => operands n n)
      [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512] 3 log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    if log then IO.println "  the hardware divider always won"
    return 1000000

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
  let d : Config := {}
  let m ← tuneMul (A := UInt64Array) d.toMulConfig log
  let m ← tuneSqr (A := UInt64Array) m log
  let dv ← tuneDiv (A := UInt64Array) ops64B divBase64 id checkArr log
  IO.println "div1Recip: division by a limb with a reciprocal against the hardware divider"
  let div1Recip ← tuneDiv1Recip log
  IO.println "div1Unnorm: the same after a shift, for an unnormalized limb"
  let div1Unnorm ← tuneDiv1Unnorm log
  IO.println "div32Recip: schoolbook steps with a reciprocal against the hardware divider"
  let div32Recip ← tuneDiv32Recip log
  IO.println "sqrtBase: one level of Zimmermann's recursion against Newton's iteration"
  let sqrtBase ← tuneSqrtBase log
  IO.println "sqrtZimmermann: Zimmermann's recursion against Newton's iteration"
  let sqrtZimmermann ← tuneSqrtZimmermann sqrtBase log
  IO.println "gcdHalf: half-gcd against Lehmer's algorithm"
  let gcdHalf ← tuneGcdHalf log
  IO.println "strDC: writing decimal digits by divide and conquer against the base case"
  let strDC ← tuneStrDC log
  IO.println "parseDC: reading decimal digits by divide and conquer against the base case"
  let parseDC ← tuneParseDC log
  let cfg : Config := { d with
    toMulConfig := m, toDivConfig := dv, div1Recip, div1Unnorm, div32Recip, sqrtBase,
    sqrtZimmermann, gcdHalf, strDC, parseDC }
  IO.println ""
  IO.println s!"Found:   {repr cfg}"
  IO.println s!"Default: {repr d}"
  IO.println ""
  let opts := [("mulKaratsuba", cfg.mulKaratsuba), ("mulToom3", cfg.mulToom3),
    ("mulToom32", cfg.mulToom32), ("mulToom42", cfg.mulToom42), ("mulToom43", cfg.mulToom43),
    ("mulToom4", cfg.mulToom4), ("mulToom6", cfg.mulToom6), ("mulToom8", cfg.mulToom8),
    ("mulFFT", cfg.mulFFT), ("mulFFTUnbal", cfg.mulFFTUnbal), ("mulFFTMin", cfg.mulFFTMin),
    ("mulUnbalanced", cfg.mulUnbalanced), ("mulChunkMax", cfg.mulChunkMax),
    ("sqrKaratsuba", cfg.sqrKaratsuba), ("sqrToom3", cfg.sqrToom3), ("sqrToom4", cfg.sqrToom4),
    ("sqrToom6", cfg.sqrToom6), ("sqrToom8", cfg.sqrToom8), ("sqrFFT", cfg.sqrFFT),
    ("divDC", cfg.divDC), ("divMu", cfg.divMu), ("divQMu", cfg.divQMu),
    ("div1Recip", cfg.div1Recip), ("div1Unnorm", cfg.div1Unnorm), ("div32Recip", cfg.div32Recip),
    ("gcdHalf", cfg.gcdHalf), ("strDC", cfg.strDC), ("parseDC", cfg.parseDC),
    ("sqrtZimmermann", cfg.sqrtZimmermann), ("sqrtBase", cfg.sqrtBase),
    ("sqrtRemRenorm", cfg.sqrtRemRenorm)]
  IO.println "To compile these into the library, add to its `require` in lakefile.toml:"
  IO.println s!"  options = \{ {", ".intercalate (opts.map fun (k, v) => s!"w64_{k} = \"{v}\"")} }"
  IO.println "or build this package with:"
  IO.println s!"  lake build -R {" ".intercalate (opts.map fun (k, v) => s!"-K w64_{k}={v}")}"
  return 0
