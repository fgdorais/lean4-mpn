/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

def checkArr (r : UInt32Array) : UInt32 := r.size.toUInt32 + r[0]!
def checkPair (r : UInt32Array × UInt32Array) : UInt32 := checkArr r.1 + checkArr r.2
def checkNat (n : Nat) : UInt32 := n.toUInt32
def checkNatPair (r : Nat × Nat) : UInt32 := r.1.toUInt32 + r.2.toUInt32

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

/-- Times one operation at each size and prints a table row per size. -/
def row (name : String) (n : Nat) (bn : IO Float) (nat : IO Float) : IO Unit := do
  let tb ← bn
  let tn ← nat
  IO.println <|
    s!"{pad 6 name} {pad 6 (toString n)} {pad 10 (fmt tb)} {pad 10 (fmt tn)} " ++
      s!"{pad 8 (fmtRatio (tb / tn))}"

def main (args : List String) : IO Unit := do
  let ops := if args.isEmpty then ["add", "sub", "mul1", "mul", "sqr", "div"] else args
  IO.println s!"{pad 6 "op"} {pad 6 "limbs"} {pad 10 "Bignum"} {pad 10 "Nat"} {pad 8 "ratio"}"
  for op in ops do
    for n in sizes do
      let a := sample n 1
      let b := sample n 2
      let a2 := sample (2 * n) 3
      let s := add a b
      let (na, nb, na2, ns) := (toNat a, toNat b, toNat a2, toNat s)
      match op with
      | "add" => row op n (time (fun x y => add x y) checkArr a b) (time (· + ·) checkNat na nb)
      | "sub" => row op n (time subVal checkArr s b) (time (· - ·) checkNat ns nb)
      | "mul" => row op n (time (fun x y => mul x y) checkArr a b) (time (· * ·) checkNat na nb)
      | "mul1" =>
        row op n (time (fun x _ => mul1 x 7) (fun p => checkArr p.1) a a)
          (time (fun x _ => x * 7) checkNat na na)
      | "sqr" =>
        row op n (time (fun x _ => sqr x) checkArr a a) (time (fun x _ => x * x) checkNat na na)
      | "div" =>
        row op n (time (fun x y => divMod x y) checkPair a2 b)
          (time (fun x y => (x / y, x % y)) checkNatPair na2 nb)
      | _ => throw <| .userError s!"unknown operation {op}"

end Bench

def main (args : List String) : IO Unit := Bench.main args
