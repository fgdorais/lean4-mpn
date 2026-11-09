/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN32
import Tune.Harness
import Tune.Shared

/-!
# Threshold tuning

`lake exe tune` measures where each algorithm starts to beat the one below it on this machine,
like GMP's `tuneup`, and prints the `Config` it finds together with the options that compile it
into the library: for a project that requires it, and on the command line. Pinning it to one
core, for example with `taskset -c 2`, gives steadier results.
-/

open ScalarArray MPN MPN.W32

namespace Tune

/--
The smallest size `n` in `sizes` from which `fast` beats `slow` on operands of `shape n` limbs at
`n` and at the next `confirm` sizes, or `none` if it never does. The operands are balanced unless
`shape` says otherwise.
-/
def crossover (slow fast : UInt32Array.Slice → UInt32Array.Slice → UInt32Array)
    (sizes : List Nat) (shape : Nat → Nat × Nat := fun n => (n, n)) (confirm := 3)
    (log : Bool := false) : IO (Option Nat) :=
  crossoverFixed (fun a b : UInt32Array => slow a b) (fun a b => fast a b) (·[0]!)
    (fun n => (sample (shape n).1 1, sample (shape n).2 2)) sizes confirm log

/-- Tunes `sqrBasecase`: where the schoolbook square starts to beat multiplying. -/
def tuneSqrBasecase (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 61).map (2 + 2 * ·)
  match ← crossover (fun a _ => mulBasecase a a) (fun a _ => sqrBasecase a) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: the schoolbook square never won up to 122 limbs; using 122"
    return 122

/-- A constant-time check of a number. -/
def checkNat : MPN.W32.Nat → UInt32
  | .small w => w.toUInt32
  | .large a _ => a.size.toUInt32 + a[0]!

/-- `n` pseudorandom limbs as a number. -/
def sampleNat (n seed : Nat) : MPN.W32.Nat :=
  MPN.W32.Nat.ofNat (MPN.W32.toNat (sample (A := UInt32Array) n seed))

/-- Decimal digits by `toDecimalWith strDC`, of a trimmed array. -/
def decimalWith (strDC : Nat) (a _ : UInt32Array) : String :=
  if h : isTrimmed a = true then MPN.W32.Nat.toDecimalWith strDC a h else ""

/--
Tunes `gcdHalf`: where half-gcd beats Lehmer's algorithm on two numbers of `n` limbs, with half-gcd
from `n` limbs, so that the numbers it reduces finish by Lehmer's algorithm.
-/
def tuneGcdHalf (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 32).map (1024 + 512 * ·)
  match ← crossoverFixed (MPN.W32.Nat.gcdWith 1000000000)
      (fun x y => MPN.W32.Nat.gcdWith x.limbs.size x y) checkNat
      (fun n => (sampleNat n 1, sampleNat n 2)) sizes (confirm := 2) (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: half-gcd never won up to 16896 limbs; using 16896"
    return 16896

/--
Tunes `div1Recip`: where division by a normalized limb with Möller and Granlund's steps with a
precomputed reciprocal beats the hardware divider, or `1000000`, never, if it does not win up to
512 limbs.
-/
def tuneDiv1Recip (log : Bool) : IO Nat := medianOf 3 do
  let sizes := [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512]
  match ← crossoverFixed (fun (a _ : UInt32Array) => divRem1With 4294967295 4294967295 a 0xF1234567)
      (fun a _ => divRem1With 0 4294967295 a 0xF1234567) (fun p => p.2 + p.1.size.toUInt32)
      (fun n => (sample n 1, sample n 1)) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    if log then IO.println "  the hardware divider always won"
    return 1000000

/--
Tunes `div1Unnorm`: where division by the unnormalized limb `10⁹`, the base of decimal strings, with
the steps with the reciprocal after a shift beats the hardware divider, or `1000000`, never, if it
does not win up to 512 limbs.
-/
def tuneDiv1Unnorm (log : Bool) : IO Nat := medianOf 3 do
  let sizes := [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512]
  match ← crossoverFixed (fun (a _ : UInt32Array) => divRem1With 4294967295 4294967295 a 1000000000)
      (fun a _ => divRem1With 4294967295 0 a 1000000000) (fun p => p.2 + p.1.size.toUInt32)
      (fun n => (sample n 1, sample n 1)) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    if log then IO.println "  the hardware divider always won"
    return 1000000

/--
Tunes `div32Recip`: where schoolbook division of `2 n` by a normalized `n` limbs with GMP's 3-by-2
steps with a precomputed reciprocal beats the steps by the hardware divider, or `1000000`, never,
if it does not win up to 512 limbs.
-/
def tuneDiv32Recip (log : Bool) : IO Nat := medianOf 3 do
  let div (t : USize) (u v : UInt32Array) : UInt32Array :=
    if h : 2 ≤ v.toSlice.size then (divRemBasecase t u v h).1 else u
  let sizes := [4, 6, 8, 12, 16, 24, 32, 40, 48, 56, 64, 80, 96, 128, 192, 256, 384, 512]
  let input (n : Nat) : UInt32Array × UInt32Array :=
    let v : UInt32Array := sample n 2
    (sample (2 * n) 1, v.set! (n - 1) (v[n - 1]! ||| 0x80000000))
  match ← crossoverFixed (div 4294967295) (div 0) (fun q => q.size.toUInt32 + q[0]!) input sizes
      (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    if log then IO.println "  the hardware divider always won"
    return 1000000

/--
Tunes `sqrtBase`: the largest root, in limbs, that Zimmermann's recursion finishes by Newton's
iteration, from where one level of the recursion on roots of `n` limbs, with Newton's iteration
below, beats Newton's iteration on the whole root.
-/
def tuneSqrtBase (log : Bool) : IO Nat := medianOf 3 do
  let sizes := [4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 128]
  match ← crossoverFixed (fun x (_ : MPN.W32.Nat) => MPN.W32.Nat.sqrtWith 1 1000000 x)
      (fun x _ => MPN.W32.Nat.sqrtWith 1 (x.limbs.size / 2 - 1) x) checkNat
      (fun n => (sampleNat (2 * n) 1, sampleNat (2 * n) 1)) sizes (log := log) with
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
  let sizes := [4, 6, 8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 128, 160, 192, 256]
  match ← crossoverFixed (fun x (_ : MPN.W32.Nat) => MPN.W32.Nat.sqrtWith 1000000 T x)
      (fun x _ => MPN.W32.Nat.sqrtWith 1 T x) checkNat
      (fun n => (sampleNat (2 * n) 1, sampleNat (2 * n) 1)) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Zimmermann's recursion never won up to 256 limbs; using 256"
    return 256

/-- The checksum of a product, in constant time. -/
def checkArr32 (r : UInt32Array) : UInt32 := r.size.toUInt32 + r[0]!

/--
Tunes `mulRows`: the size of both operands together from which the schoolbook product by rows into
wide accumulators beats Comba's method, at `n` by `n` limbs.
-/
def tuneMulRows (log : Bool) : IO Nat := medianOf 3 do
  let sizes := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 32, 40, 48, 64]
  match ← crossoverFixed (fun (a b : UInt32Array) => mulBasecaseWith 1000000 config.mulCombaW a b)
      (fun a b => mulBasecaseWith 0 config.mulCombaW a b) checkArr32
      (fun n => (sample n 1, sample n 2)) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return 2 * n
  | none =>
    IO.eprintln "warning: the product by rows never won up to 64 limbs; using 128"
    return 128

/--
Tunes `mulCombaW`: the size of the shorter operand from which Comba's method with whole products
in its columns beats the one with single products, at `n` by `n` limbs.
-/
def tuneMulCombaW (log : Bool) : IO Nat := medianOf 3 do
  let sizes := [4, 6, 8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 128]
  match ← crossoverFixed (fun (a b : UInt32Array) => mulBasecaseWith 1000000 1000000 a b)
      (fun a b => mulBasecaseWith 1000000 0 a b) checkArr32
      (fun n => (sample n 1, sample n 2)) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: whole products in Comba's columns never won up to 128 limbs; using 128"
    return 128

/-- Tunes `sqrRows`: the size from which the schoolbook square by rows beats Comba's method. -/
def tuneSqrRows (log : Bool) : IO Nat := medianOf 3 do
  let sizes := [2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 32, 40, 48, 64]
  match ← crossoverFixed (fun (a _ : UInt32Array) => sqrBasecaseWith 1000000 a)
      (fun a _ => sqrBasecaseWith 0 a) checkArr32 (fun n => (sample n 1, sample n 1)) sizes
      (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: the square by rows never won up to 64 limbs; using 64"
    return 64

/-- Tunes `strDC`: where writing decimal digits by divide and conquer beats the base case. -/
def tuneStrDC (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 60).map (16 + 8 * ·)
  match ← crossoverFixed (decimalWith 1000000000) (decimalWith 0) (·.utf8ByteSize.toUInt32)
      (fun n => let a := (sample (A := UInt32Array) (n - 1) 1).push 1; (a, a)) sizes
      (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: writing by divide and conquer never won up to 488 limbs; using 488"
    return 488

/--
Tunes `parseDC`: where reading decimal digits by divide and conquer beats the base case, on
strings of `9 n` digits.
-/
def tuneParseDC (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 48).map (128 + 64 * ·)
  let digits (n : Nat) : String :=
    String.ofList ((List.range (9 * n)).map fun i => Char.ofNat (48 + (i * 7 + i / 3) % 10))
  match ← crossoverFixed (fun t (_ : String) => MPN.W32.Nat.ofStringWith 1000000000 t)
      (fun t _ => MPN.W32.Nat.ofStringWith 0 t) (fun r => checkNat r.get!)
      (fun n => (digits n, digits n)) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: reading by divide and conquer never won up to 3136; using 3136"
    return 3136

end Tune

open Tune in
public def main (args : List String) : IO UInt32 := do
  let log := args.contains "--verbose"
  IO.println "Tuning the lean4-mpn thresholds; this takes several minutes."
  let d : Config := {}
  let m ← tuneMul (A := UInt32Array) d.toMulConfig log
  IO.println "mulRows: the product by rows against Comba's method"
  let mulRows ← tuneMulRows log
  IO.println "mulCombaW: whole products in Comba's columns against single products"
  let mulCombaW ← tuneMulCombaW log
  IO.println "sqrRows: the square by rows against Comba's method"
  let sqrRows ← tuneSqrRows log
  IO.println "sqrBasecase: the schoolbook square against multiplying"
  let sqrBasecase ← tuneSqrBasecase log
  let m ← tuneSqr (A := UInt32Array) m log
  let dv ← tuneDiv (A := UInt32Array) ops32B divBase32 id
    (fun s => s.size.toUInt64 + (s.getD 0 0).toUInt64) log
  IO.println "div1Recip: division by a limb with a reciprocal against the hardware divider"
  let div1Recip ← tuneDiv1Recip log
  IO.println "div1Unnorm: the same after a shift, for an unnormalized limb"
  let div1Unnorm ← tuneDiv1Unnorm log
  IO.println "div32Recip: schoolbook steps with a reciprocal against the hardware divider"
  let div32Recip ← tuneDiv32Recip log
  IO.println "gcdHalf: half-gcd against Lehmer's algorithm"
  let gcdHalf ← tuneGcdHalf log
  IO.println "strDC: writing decimal digits by divide and conquer against the base case"
  let strDC ← tuneStrDC log
  IO.println "parseDC: reading decimal digits by divide and conquer against the base case"
  let parseDC ← tuneParseDC log
  IO.println "sqrtBase: one level of Zimmermann's recursion against Newton's iteration"
  let sqrtBase ← tuneSqrtBase log
  IO.println "sqrtZimmermann: Zimmermann's recursion against Newton's iteration"
  let sqrtZimmermann ← tuneSqrtZimmermann sqrtBase log
  let cfg : Config := { d with
    toMulConfig := m, toDivConfig := { dv with divDC := max 4 dv.divDC },
    four_le_divDC := Nat.le_max_left .., div1Recip, div1Unnorm, div32Recip, gcdHalf, strDC,
    parseDC, sqrtZimmermann, sqrtBase, mulRows, mulCombaW, sqrRows, sqrBasecase }
  IO.println ""
  IO.println s!"Found:   {repr cfg}"
  IO.println s!"Default: {repr d}"
  IO.println ""
  let opts := [("mulKaratsuba", cfg.mulKaratsuba), ("mulToom3", cfg.mulToom3),
    ("mulToom32", cfg.mulToom32), ("mulToom42", cfg.mulToom42), ("mulToom43", cfg.mulToom43),
    ("mulToom4", cfg.mulToom4), ("mulToom6", cfg.mulToom6), ("mulToom8", cfg.mulToom8),
    ("mulFFT", cfg.mulFFT), ("mulFFTUnbal", cfg.mulFFTUnbal), ("mulFFTMin", cfg.mulFFTMin),
    ("mulUnbalanced", cfg.mulUnbalanced), ("mulChunkMax", cfg.mulChunkMax),
    ("mulRows", cfg.mulRows), ("mulCombaW", cfg.mulCombaW), ("sqrRows", cfg.sqrRows),
    ("sqrBasecase", cfg.sqrBasecase), ("sqrKaratsuba", cfg.sqrKaratsuba),
    ("sqrToom3", cfg.sqrToom3), ("sqrToom4", cfg.sqrToom4), ("sqrToom6", cfg.sqrToom6),
    ("sqrToom8", cfg.sqrToom8), ("sqrFFT", cfg.sqrFFT), ("divDC", cfg.divDC),
    ("divMu", cfg.divMu), ("divQMu", cfg.divQMu), ("div1Recip", cfg.div1Recip),
    ("div1Unnorm", cfg.div1Unnorm), ("div32Recip", cfg.div32Recip), ("gcdHalf", cfg.gcdHalf),
    ("strDC", cfg.strDC), ("parseDC", cfg.parseDC), ("sqrtZimmermann", cfg.sqrtZimmermann),
    ("sqrtBase", cfg.sqrtBase)]
  IO.println "To compile these into the library, add to its `require` in lakefile.toml:"
  IO.println s!"  options = \{ {", ".intercalate (opts.map fun (k, v) => s!"w32_{k} = \"{v}\"")} }"
  IO.println "or build this package with:"
  IO.println s!"  lake build -R {" ".intercalate (opts.map fun (k, v) => s!"-K w32_{k}={v}")}"
  return 0
