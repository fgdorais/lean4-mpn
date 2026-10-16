/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Bignum

/-!
# Benchmark

`lake exe bench` times each operation of the library against the same operation on `Nat`, which
Lean implements with GMP, on pseudorandom operands from 1 to 4096 limbs. Division divides `2 n`
limbs by `n` limbs. Pinning it to one core, for example with `taskset -c 2`, gives steadier
results.
-/

open ScalarArray Bignum

namespace Bench

/-- `n` pseudorandom limbs, with a nonzero top limb. -/
def sample (n seed : Nat) : UInt32Array := Id.run do
  let mut s := seed
  let mut r := UInt32Array.emptyWithCapacity n
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    r := r.push (s / 2 ^ 32).toUInt32
  if n > 0 then r := r.set! (n - 1) (r[n - 1]! ||| 1)
  return r

/-- Runs `f a b` `reps` times, folding each result into a checksum so that it is computed. -/
@[noinline] def repeatOp {α β : Type} (f : α → α → β) (check : β → UInt32) (a b : α)
    (reps : Nat) : UInt32 := Id.run do
  let mut acc : UInt32 := 0
  for _ in [0:reps] do
    acc := acc + check (f a b)
  return acc

/-- The median time of `f a b` in nanoseconds, over trials of at least `minNs` each. -/
def time {α β : Type} (f : α → α → β) (check : β → UInt32) (a b : α) (trials := 5)
    (minNs := 2_000_000) : IO Float := do
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
  return (samples.qsort (· < ·))[trials / 2]!

def checkArr (r : UInt32Array) : UInt32 := r.size.toUInt32 + r.getD 0 0
def checkNat (n : Nat) : UInt32 := n.toUInt32
/-- O(1), like `checkNat`: hashing the result would add a pass over its limbs to the time. -/
def checkBig : BigNat → UInt32
  | .small w => w.toUInt32
  | .large a _ => a.size.toUInt32 + a[0]!
def checkStr (s : String) : UInt32 := s.utf8ByteSize.toUInt32

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

/-- A ratio with two decimals. -/
def fmtRatio (x : Float) : String :=
  let n := (x * 100).round.toUInt64.toNat
  let frac := toString (n % 100)
  toString (n / 100) ++ "." ++ "".pushn '0' (2 - frac.length) ++ frac

def sizes : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]

/-- Times one operation at one size against `Nat`, unless `noNat`, and prints a table row. -/
def row (noNat : Bool) (name : String) (n : Nat) (bn : IO Float) (nat : IO Float) : IO Unit := do
  let tb ← bn
  if noNat then
    IO.println s!"{pad 6 name} {pad 6 (toString n)} {pad 10 (fmt tb)}"
  else
    let tn ← nat
    IO.println <|
      s!"{pad 6 name} {pad 6 (toString n)} {pad 10 (fmt tb)} {pad 10 (fmt tn)} " ++
        s!"{pad 8 (fmtRatio (tb / tn))}"

def main (args : List String) : IO Unit := do
  let noNat := args.contains "--no-nat"
  let (nums, names) := (args.filter (· != "--no-nat")).partition (·.isNat)
  let ops := if names.isEmpty then ["add", "sub", "mul1", "mul", "sqr", "div", "shr"] else names
  let sizes := if nums.isEmpty then sizes else nums.map String.toNat!
  IO.println s!"{pad 6 "op"} {pad 6 "limbs"} {pad 10 "Bignum"} {pad 10 "Nat"} {pad 8 "ratio"}"
  for op in ops do
    for n in sizes do
      let a := sample n 1
      let b := sample n 2
      let a2 := sample (2 * n) 3
      let s := add a b
      let (na, nb, na2, ns) := (toNat a, toNat b, toNat a2, toNat s)
      match op with
      | "add" =>
        row noNat op n (time (fun x y => add x y) checkArr a b) (time (· + ·) checkNat na nb)
      | "sub" => row noNat op n (time subVal checkArr s b) (time (· - ·) checkNat ns nb)
      | "mul" =>
        row noNat op n (time (fun x y => mul x y) checkArr a b) (time (· * ·) checkNat na nb)
      | "mul1" =>
        row noNat op n (time (fun x _ => mul1 x 7) (fun p => checkArr p.1) a a)
          (time (fun x _ => x * 7) checkNat na na)
      | "badd" =>
        let (x, y) := (BigNat.ofNat na, BigNat.ofNat nb)
        row noNat op n (time (· + ·) checkBig x y) (time (· + ·) checkNat na nb)
      | "bsub" =>
        let (x, y) := (BigNat.ofNat ns, BigNat.ofNat nb)
        row noNat op n (time (· - ·) checkBig x y) (time (· - ·) checkNat ns nb)
      | "bmul" =>
        let (x, y) := (BigNat.ofNat na, BigNat.ofNat nb)
        row noNat op n (time (· * ·) checkBig x y) (time (· * ·) checkNat na nb)
      | "bdiv" =>
        let (x, y) := (BigNat.ofNat na2, BigNat.ofNat nb)
        row noNat op n (time (· / ·) checkBig x y) (time (· / ·) checkNat na2 nb)
      | "bgcd" =>
        let (x, y) := (BigNat.ofNat na, BigNat.ofNat nb)
        row noNat op n (time BigNat.gcd checkBig x y) (time Nat.gcd checkNat na nb)
      | "bshl" =>
        let x := BigNat.ofNat na
        row noNat op n (time (fun (x : BigNat) _ => x <<< (37 : Nat)) checkBig x x)
          (time (fun x _ => x <<< 37) checkNat na na)
      | "bshr" =>
        let x := BigNat.ofNat na
        row noNat op n (time (fun (x : BigNat) _ => x >>> (37 : Nat)) checkBig x x)
          (time (fun x _ => x >>> 37) checkNat na na)
      | "bsqrt" =>
        let x := BigNat.ofNat na2
        row noNat op n (time (fun x _ => BigNat.sqrt x) checkBig x x)
          (time (fun x _ => Nat.sqrt x) checkNat na2 na2)
      | "btostr" =>
        let x := BigNat.ofNat na
        row noNat op n (time (fun (x : BigNat) _ => toString x) checkStr x x)
          (time (fun (x : Nat) _ => toString x) checkStr na na)
      | "bofstr" =>
        let t := toString na
        row noNat op n (time (fun t _ => BigNat.ofString? t) (fun r => checkBig r.get!) t t)
          (time (fun t _ => t.toNat?) (fun r => checkNat r.get!) t t)
      | "btonat" =>
        -- `Nat` has nothing to convert: its column is one linear pass, `x + 1`.
        let x := BigNat.ofNat na
        row noNat op n (time (fun (x : BigNat) _ => x.toNat) checkNat x x)
          (time (fun x _ => x + 1) checkNat na na)
      | "bofnat" =>
        row noNat op n (time (fun x _ => BigNat.ofNat x) checkBig na na)
          (time (fun x _ => x + 1) checkNat na na)
      | "shr" =>
        row noNat op n (time (fun (x : UInt32Array) _ => shiftRight x 37) checkArr a a)
          (time (fun x _ => x >>> 37) checkNat na na)
      | "sqr" =>
        row noNat op n (time (fun x _ => sqr x) checkArr a a)
          (time (fun x _ => x * x) checkNat na na)
      | "div" =>
        -- The quotient alone on both sides: `Nat` has no single division with remainder, and
        -- `(x / y, x % y)` is two divisions.
        row noNat op n (time (fun x y => div x y) checkArr a2 b) (time (· / ·) checkNat na2 nb)
      | _ => throw <| .userError s!"unknown operation {op}"

end Bench

public def main (args : List String) : IO Unit := Bench.main args
