/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN32
import Bench.Harness

/-!
# Benchmark

`lake exe bench` times each operation of the library against the same operation on `Nat`, which
Lean implements with GMP, on pseudorandom operands from 1 to 4096 limbs. Division divides `2 n`
limbs by `n` limbs. Pinning it to one core, for example with `taskset -c 2`, gives steadier
results.

Each time is the median of five trials. The last two columns are the spread of the trials of each
side, their sample standard deviation relative to their mean, which
tells how far to trust a difference between two runs.
-/

open ScalarArray MPN MPN.W32

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

def checkArr (r : UInt32Array) : UInt32 := r.size.toUInt32 + r.getD 0 0
/-- O(1), like `checkNat`: hashing the result would add a pass over its limbs to the time. -/
def checkBig : MPN.W32.Nat → UInt64
  | .small w => w
  | .large a _ => a.size.toUInt64 + a[0]!.toUInt64

def sizes : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]

/-- The operations of `MPN.W32.Nat` that `bigRow` times. -/
def big : BigOps MPN.W32.Nat where
  ofNat := MPN.W32.Nat.ofNat
  toNat := (·.toNat)
  check := checkBig
  sqr := MPN.W32.Nat.sqr
  sqrt := MPN.W32.Nat.sqrt
  gcd := MPN.W32.Nat.gcd
  lcm := MPN.W32.Nat.lcm
  log2 := (·.log2)
  ofString? := MPN.W32.Nat.ofString?

/-- The row of `op` at `n` limbs, or `false` when it is not an operation. -/
def run (noNat : Bool) (op : String) (n : Nat) : IO Bool := do
  let a := sample n 1
  let b := sample n 2
  let a2 := sample (2 * n) 3
  let s := add a b
  let (na, nb, na2, ns) := (toNat a, toNat b, toNat a2, toNat s)
  if ← bigRow big noNat op n na nb na2 ns then return true
  match op with
  | "add" =>
    row noNat op n (time (fun x y => add x y) checkArr a b) (time (· + ·) checkNat na nb)
  | "sub" => row noNat op n (time subVal checkArr s b) (time (· - ·) checkNat ns nb)
  | "mul" =>
    row noNat op n (time (fun x y => mul x y) checkArr a b) (time (· * ·) checkNat na nb)
  | "mul1" =>
    row noNat op n (time (fun x _ => mul1 x 7) (fun p => checkArr p.1) a a)
      (time (fun x _ => x * 7) checkNat na na)
  | "shr" =>
    row noNat op n (time (fun (x : UInt32Array) _ => shiftRight x 37) checkArr a a)
      (time (fun x _ => x >>> 37) checkNat na na)
  | "div1" =>
    row noNat op n (time (fun (x : UInt32Array) _ => divRem1 x 0xF1234567)
      (fun p => checkArr p.1) a a) (time (fun x _ => x / 0xF1234567) checkNat na na)
  | "div1u" =>
    row noNat op n (time (fun (x : UInt32Array) _ => divRem1 x 1000000000)
      (fun p => checkArr p.1) a a) (time (fun x _ => x / 1000000000) checkNat na na)
  | "sqr" =>
    row noNat op n (time (fun x _ => sqr x) checkArr a a)
      (time (fun x _ => x * x) checkNat na na)
  | "div" =>
    -- The quotient alone on both sides: `Nat` has no single division with remainder, and
    -- `(x / y, x % y)` is two divisions.
    row noNat op n (time (fun x y => div x y) checkArr a2 b) (time (· / ·) checkNat na2 nb)
  | _ => return false
  return true

/-- `bench32 [--no-nat] [op…] [size…]`. -/
def main (args : List String) : IO Unit :=
  runMain args (["add", "sub", "mul1", "mul", "sqr", "div", "shr"]) sizes run

end Bench

public def main (args : List String) : IO Unit := Bench.main args
