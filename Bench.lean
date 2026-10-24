/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN
import Batteries.Data.RunningStats

/-!
# Benchmark

`lake exe bench` times each operation of the library against the same operation on `Nat`, which
Lean implements with GMP, on pseudorandom operands of 64-bit limbs. Pinning it to one core, for
example with `taskset -c 2`, gives steadier results.

Each time is the median of five trials. The last two columns are the spread of the trials of each
side, their sample standard deviation relative to their mean (`Batteries.RunningStats`), which
tells how far to trust a difference between two runs.

`bench [--no-nat] [op…] [size…]` selects the operations and the sizes, in limbs; `--no-nat` skips
`Nat`, for a profiler.
-/

open ScalarArray

namespace Bench

/-! ## Reference loop -/

/--
Adds `x * b` into `r` at offset `i`, from limb `j` on, with carry `c`: a hand-written loop with
the same arithmetic as `MPN.addMul1`, the target for the library's loops.
-/
def refRow (x : UInt64) (b r : UInt64Array) (i j : Nat) (c : UInt64) : UInt64Array :=
  if h : j < b.size then
    let y := b[j]
    let lo := x * y
    let hi := UInt64.addh (x.mulh y) lo r[i + j]!
    let lo := lo + r[i + j]!
    refRow x b (r.set! (i + j) (lo + c)) i (j + 1) (UInt64.addh hi lo c)
  else
    r.set! (i + j) c

/-- Schoolbook multiplication with `refRow`, from row `i` on. -/
def refMulLoop (a b r : UInt64Array) (i : Nat) : UInt64Array :=
  if h : i < a.size then refMulLoop a b (refRow a[i] b r i 0 0) (i + 1) else r

/-- Schoolbook multiplication with `refRow`. -/
def refMul (a b : UInt64Array) : UInt64Array :=
  refMulLoop a b (.replicate (a.size + b.size) 0) 0

/-! ## Harness -/

/-- `n` pseudorandom limbs, with a nonzero top limb. -/
def sample (n seed : Nat) : UInt64Array := Id.run do
  let mut s := seed
  let mut r := UInt64Array.emptyWithCapacity n
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    r := r.push s.toUInt64
  if n > 0 then r := r.set! (n - 1) (r[n - 1]! ||| 1)
  return r

/-- Runs `f a b` `reps` times, folding each result into a checksum so that it is computed. -/
@[noinline] def repeatOp {α β : Type} (f : α → α → β) (check : β → UInt64) (a b : α)
    (reps : Nat) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for _ in [0:reps] do
    acc := acc + check (f a b)
  return acc

/-- The median time in nanoseconds of a set of trials, and their running statistics. -/
structure Timing where
  median : Float
  stats : Batteries.RunningStats

/-- The sample standard deviation of the trials relative to their mean. -/
def Timing.spread (t : Timing) : Float :=
  if t.stats.mean > 0 then t.stats.sampleStandardDeviation / t.stats.mean else 0

/-- The time of `f a b` in nanoseconds, over trials of at least `minNs` each. -/
def time {α β : Type} (f : α → α → β) (check : β → UInt64) (a b : α) (trials := 5)
    (minNs := 2_000_000) : IO Timing := do
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
    samples := samples.push ((t₁ - t₀).toFloat / reps.toFloat)
  let stats := samples.foldl (fun s x => s.push x) ({} : Batteries.RunningStats)
  return { median := (samples.qsort (· < ·))[trials / 2]!, stats }

/-- O(1), like `checkNat`: hashing the result would add a pass over its limbs to the time. -/
def checkArr (r : UInt64Array) : UInt64 := r.size.toUInt64 + r[0]!
def checkPair (p : UInt64Array × UInt64) : UInt64 := checkArr p.1 + p.2
def checkNat (n : Nat) : UInt64 := n.toUInt64

/-- `x` with `w` characters, padded on the left. -/
def pad (w : Nat) (s : String) : String := "".pushn ' ' (w - s.length) ++ s

/-- `t` nanoseconds with three significant digits, in ns, µs or ms. -/
def fmt (t : Float) : String :=
  let (v, unit) := if t < 1e3 then (t, "ns") else if t < 1e6 then (t / 1e3, "µs")
    else (t / 1e6, "ms")
  let digits := if v < 10 then 2 else if v < 100 then 1 else 0
  let scale := (10 : Float) ^ digits.toFloat
  let n := (v * scale).round.toUInt64.toNat
  let int := toString (n / 10 ^ digits)
  let frac := toString (n % 10 ^ digits)
  let s := if digits = 0 then int else int ++ "." ++ "".pushn '0' (digits - frac.length) ++ frac
  s ++ " " ++ unit

/-- A spread as a percentage with one decimal, `±1.2%`. -/
def fmtSpread (x : Float) : String :=
  let n := (x * 1000).round.toUInt64.toNat
  "±" ++ toString (n / 10) ++ "." ++ toString (n % 10) ++ "%"

/-- A ratio with two decimals. -/
def fmtRatio (x : Float) : String :=
  let n := (x * 100).round.toUInt64.toNat
  let frac := toString (n % 100)
  toString (n / 100) ++ "." ++ "".pushn '0' (2 - frac.length) ++ frac

def sizes : List Nat := [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 512]

/--
Times one operation at one size against `Nat`, unless `noNat`, and prints a table row: the two
median times, their ratio and the spreads of their trials.
-/
def row (noNat : Bool) (name : String) (n : Nat) (mpn : IO Timing) (nat : IO Timing) :
    IO Unit := do
  let tm ← mpn
  if noNat then
    IO.println <| s!"{pad 7 name} {pad 6 (toString n)} {pad 10 (fmt tm.median)} " ++
      s!"{pad 8 (fmtSpread tm.spread)}"
  else
    let tn ← nat
    IO.println <|
      s!"{pad 7 name} {pad 6 (toString n)} {pad 10 (fmt tm.median)} {pad 10 (fmt tn.median)} " ++
        s!"{pad 8 (fmtRatio (tm.median / tn.median))} {pad 8 (fmtSpread tm.spread)} " ++
        s!"{pad 8 (fmtSpread tn.spread)}"

/-- The value of an array of limbs. -/
def toNat (a : UInt64Array) : Nat := a.foldr (fun d n => n * 2 ^ 64 + d.toNat) 0

def ops : List String :=
  ["add", "sub", "shl", "shr", "div1", "sbdiv", "div", "sqrt", "mulmod", "mul1", "addmul1", "mul",
    "sqr", "comba", "kara", "toom", "kara2", "toom2", "fft", "fft2", "auto", "ksqr", "fftsqr",
    "toomsqr", "autosqr", "mulref"]

def main (args : List String) : IO Unit := do
  let noNat := args.contains "--no-nat"
  let (nums, names) := (args.filter (· != "--no-nat")).partition (·.isNat)
  let ops := if names.isEmpty then ops else names
  let sizes := if nums.isEmpty then sizes else nums.map String.toNat!
  IO.println <| s!"{pad 7 "op"} {pad 6 "limbs"} {pad 10 "MPN"} {pad 10 "Nat"} {pad 8 "ratio"} " ++
    s!"{pad 8 "±MPN"} {pad 8 "±Nat"}"
  for op in ops do
    for n in sizes do
      let a := sample n 1
      let b := sample n 2
      let (na, nb) := (toNat a, toNat b)
      let s := sample (n + 1) 3
      let ns := toNat s
      match op with
      | "add" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.add (UInt64Array.replicate x.size 0).toUSlice x.toUSlice y.toUSlice) checkPair a b)
          (time (· + ·) checkNat na nb)
      | "sub" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.sub (UInt64Array.replicate x.size 0).toUSlice x.toUSlice y.toUSlice) checkPair s b)
          (time (· - ·) checkNat ns nb)
      | "shl" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.lshift (UInt64Array.replicate x.size 0).toUSlice x.toUSlice 13) checkPair a a)
          (time (fun x _ => x <<< 13) checkNat na na)
      | "shr" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.rshift (UInt64Array.replicate x.size 0).toUSlice x.toUSlice 13) checkPair a a)
          (time (fun x _ => x >>> 13) checkNat na na)
      | "div1" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.divRem1 (UInt64Array.replicate x.size 0).toUSlice x.toUSlice 0xF123456789ABCDEF)
            checkPair a a)
          (time (fun x _ => x / 0xF123456789ABCDEF) checkNat na na)
      | "div" =>
        -- `2 n` by `n` limbs; `Nat` computes the quotient only.
        let a2 := sample (2 * n) 4
        row noNat op n
          (time (fun (x y : UInt64Array) => MPN.Num.divMod x y)
            (fun p => checkArr p.1 + checkArr p.2) a2 b)
          (time (· / ·) checkNat (toNat a2) nb)
      | "sbdiv" =>
        let a2 := sample (2 * n) 4
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.divRem (UInt64Array.replicate (x.size - y.size + 1) 0).toUSlice
              (UInt64Array.replicate y.size 0).toUSlice x.toUSlice y.toUSlice)
            (fun p => checkArr p.1 + checkArr p.2) a2 b)
          (time (· / ·) checkNat (toNat a2) nb)
      | "mulmod" =>
        -- `n` by `n` limbs modulo `β^n - 1`, with `2ᵏ` pieces, `k = fftK n`; `Nat` multiplies.
        let k := MPN.FFT.fftK n
        row noNat op n
          (time (fun (x y : UInt64Array) => MPN.Num.mulModB x y k (n / 2 ^ k)) checkArr a b)
          (time (· * ·) checkNat na nb)
      | "sqrt" =>
        -- `Nat.sqrt` is Lean's Newton iteration on `Nat`, not GMP's `mpz_sqrt`.
        row noNat op n
          (time (fun (x _ : UInt64Array) => MPN.sqrtRem x) (fun p => checkArr p.1 + checkArr p.2)
            a a)
          (time (fun x _ => x.sqrt) checkNat na na)
      | "mul1" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.mul1 (UInt64Array.replicate x.size 0).toUSlice x.toUSlice 7) checkPair a a)
          (time (fun x _ => x * 7) checkNat na na)
      | "addmul1" =>
        -- `b` is shared, so `addMul1` first copies it, as `Nat` allocates its result.
        row noNat op n
          (time (fun (x y : UInt64Array) => MPN.addMul1 y.toUSlice x.toUSlice 7) checkPair a b)
          (time (fun x y => y + x * 7) checkNat na nb)
      | "mul" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mulBasecase (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice) checkArr a b)
          (time (· * ·) checkNat na nb)
      | "comba" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mulComba (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice) checkArr a b)
          (time (· * ·) checkNat na nb)
      | "kara" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mulKaratsuba (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice) checkArr a b)
          (time (· * ·) checkNat na nb)
      | "sqr" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.sqrBasecase (UInt64Array.replicate (2 * x.size) 0).toUSlice x.toUSlice)
            checkArr a a)
          (time (fun x _ => x * x) checkNat na na)
      | "ksqr" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.sqrKaratsuba (UInt64Array.replicate (2 * x.size) 0).toUSlice x.toUSlice)
            checkArr a a)
          (time (fun x _ => x * x) checkNat na na)
      | "toom" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mulToom (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice) checkArr a b)
          (time (· * ·) checkNat na nb)
      | "kara2" =>
        -- `n` by `n / 2` limbs.
        let h := sample (n / 2) 2
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mulKaratsuba (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice) checkArr a h)
          (time (· * ·) checkNat na (toNat h))
      | "toom2" =>
        let h := sample (n / 2) 2
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mulToom (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice) checkArr a h)
          (time (· * ·) checkNat na (toNat h))
      | "fft" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.FFT.fftMul (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice (MPN.FFT.fftK (x.size + y.size))) checkArr a b)
          (time (· * ·) checkNat na nb)
      | "fftsqr" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.FFT.fftSqr (UInt64Array.replicate (2 * x.size) 0).toUSlice x.toUSlice
              (MPN.FFT.fftK (2 * x.size))) checkArr a a)
          (time (fun x _ => x * x) checkNat na na)
      | "toomsqr" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.sqrToom (UInt64Array.replicate (2 * x.size) 0).toUSlice x.toUSlice)
            checkArr a a)
          (time (fun x _ => x * x) checkNat na na)
      | "autosqr" =>
        row noNat op n
          (time (fun (x _ : UInt64Array) =>
            MPN.sqr (UInt64Array.replicate (2 * x.size) 0).toUSlice x.toUSlice) checkArr a a)
          (time (fun x _ => x * x) checkNat na na)
      | "auto" =>
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.mul (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice y.toUSlice)
            checkArr a b)
          (time (· * ·) checkNat na nb)
      | "fft2" =>
        let h := sample (n / 2) 2
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.FFT.fftMul (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
              y.toUSlice (MPN.FFT.fftK (x.size + y.size))) checkArr a h)
          (time (· * ·) checkNat na (toNat h))
      | "mulref" =>
        row noNat op n (time refMul checkArr a b) (time (· * ·) checkNat na nb)
      | _ =>
        -- `fftb<s>`, `toomb<s>`: `n` by `s` limbs, for tuning `fftMinSmall`.
        -- `auto2`, `auto4`, `auto8`: `MPN.mul` on `n` by `n / d` limbs; `autobS`: on `n` by `S`.
        let sh : Option Nat := if op == "auto2" then some (n / 2) else if op == "auto4" then
          some (n / 4) else if op == "auto8" then some (n / 8) else if op.startsWith "autob" then
          (op.drop 5).toString.toNat? else none
        if let some sz := sh then
          let h := sample sz 2
          row noNat op n
            (time (fun (x y : UInt64Array) =>
              MPN.mul (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice y.toUSlice)
              checkArr a h)
            (time (· * ·) checkNat na (toNat h))
        else
        if op.startsWith "fsq" then
          let k := (op.drop 3).toString.toNat!
          row noNat op n
            (time (fun (x _ : UInt64Array) =>
              MPN.FFT.fftSqr (UInt64Array.replicate (2 * x.size) 0).toUSlice x.toUSlice k)
              checkArr a a)
            (time (fun x _ => x * x) checkNat na na)
        else
        let sb := if op.startsWith "fftb" then (op.drop 4).toString.toNat?
          else if op.startsWith "toomb" then (op.drop 5).toString.toNat? else none
        if let some sz := sb then
          let h := sample sz 2
          row noNat op n
            (time (fun (x y : UInt64Array) =>
              if op.startsWith "fftb" then
                MPN.FFT.fftMul (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
                  y.toUSlice (MPN.FFT.fftK (x.size + y.size))
              else
                MPN.mulToom (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
                  y.toUSlice) checkArr a h)
            (time (· * ·) checkNat na (toNat h))
        else
        -- `fft<k>`: the FFT with `2ᵏ` pieces, for tuning `fftK`.
        match (op.drop 3).toString.toNat? with
        | some k =>
          if op.startsWith "fft" then
            row noNat op n
              (time (fun (x y : UInt64Array) =>
                MPN.FFT.fftMul (UInt64Array.replicate (x.size + y.size) 0).toUSlice x.toUSlice
                  y.toUSlice k) checkArr a b)
              (time (· * ·) checkNat na nb)
          else throw <| .userError s!"unknown operation {op}"
        | none => throw <| .userError s!"unknown operation {op}"

end Bench

public def main (args : List String) : IO Unit := Bench.main args
