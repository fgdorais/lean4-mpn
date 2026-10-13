/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Bignum

open ScalarArray Bignum

/-! Conversion -/

#guard (ofNat 0).size == 0
#guard (ofNat 1).toList == [1]
#guard (ofNat (2 ^ 32)).toList == [0, 1]
#guard (ofNat (2 ^ 64 - 1)).toList == [4294967295, 4294967295]
#guard [0, 1, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 100 + 7, 10 ^ 50].all fun n => toNat (ofNat n) == n
#guard trim (UInt32Array.mk #[1, 2, 0, 0]) == UInt32Array.mk #[1, 2]
#guard trim (UInt32Array.mk #[0, 0]) == .empty
#guard toNat (UInt32Array.mk #[5, 0, 0]) == 5

/-! Word operations -/

/-- Checks the word operations of an `n`-bit type against `Nat` on its edge values. -/
def checkWords (n : Nat) (ofNat : Nat → α) (toNat : α → Nat)
    (adc sbb : α → α → Bool → α × Bool) (maa : α → α → α → α → α × α) : Bool :=
  let vs := [0, 1, 2, 2 ^ (n - 1) - 1, 2 ^ (n - 1), 2 ^ n - 2, 2 ^ n - 1]
  vs.all fun x => vs.all fun y => [false, true].all fun c =>
    let (s, c') := adc (ofNat x) (ofNat y) c
    let (d, b') := sbb (ofNat x) (ofNat y) c
    toNat s + (if c' then 2 ^ n else 0) == x + y + c.toNat &&
    (toNat d : Int) - (if b' then 2 ^ n else 0) == (x : Int) - y - c.toNat &&
    vs.all fun a => vs.all fun b =>
      let (lo, hi) := maa (ofNat x) (ofNat y) (ofNat a) (ofNat b)
      toNat hi * 2 ^ n + toNat lo == x * y + a + b

#guard checkWords 8 UInt8.ofNat UInt8.toNat
  UInt8.addWithCarry UInt8.subWithBorrow UInt8.mulAddAdd
#guard checkWords 16 UInt16.ofNat UInt16.toNat
  UInt16.addWithCarry UInt16.subWithBorrow UInt16.mulAddAdd
#guard checkWords 32 UInt32.ofNat UInt32.toNat
  UInt32.addWithCarry UInt32.subWithBorrow UInt32.mulAddAdd
#guard checkWords 64 UInt64.ofNat UInt64.toNat
  UInt64.addWithCarry UInt64.subWithBorrow UInt64.mulAddAdd

/-! Test values -/

/-- Pseudorandom numbers of up to `bits` bits from a linear congruential generator. -/
def samples (count bits : Nat) (seed : Nat := 2026) : List Nat := Id.run do
  let mut s := seed
  let mut l := []
  for _ in [0:count] do
    let mut n := 0
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let len := s % (bits + 1)
    for _ in [0:(len + 31) / 32] do
      s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      n := n * 2 ^ 32 + s / 2 ^ 32
    l := (n % 2 ^ len) :: l
  return l

/-- Numbers whose limbs are all `2³² - 1` or all zero but one, where carries propagate the most. -/
def edges : List Nat :=
  [0, 1, 2, 2 ^ 31] ++ (List.range 5).flatMap fun k =>
    [2 ^ (32 * (k + 1)) - 1, 2 ^ (32 * (k + 1)), 2 ^ (32 * (k + 1)) + 1]

def values : List Nat := edges ++ samples 40 400

/-! Addition -/

#guard values.all fun m => values.all fun n =>
  let r := add (ofNat m) (ofNat n)
  toNat r == m + n && isTrimmed r

#guard add (ofNat (2 ^ 128 - 1)) (ofNat 1) == ofNat (2 ^ 128)
#guard add UInt32Array.empty UInt32Array.empty == .empty

/-! Multiplication -/

#guard values.all fun m => values.all fun n =>
  let r := mul (ofNat m) (ofNat n)
  toNat r == m * n && isTrimmed r

#guard mul (ofNat (2 ^ 128 - 1)) (ofNat (2 ^ 128 - 1)) ==
  ofNat ((2 ^ 128 - 1) * (2 ^ 128 - 1))
#guard mul (ofNat 0) (ofNat (2 ^ 100)) == .empty

-- A long computation that reuses each result: 200 factorial.
#guard
  let r := (List.range 200).foldl (fun a i => mul a (ofNat (i + 1))) (ofNat 1)
  toNat r == (List.range 200).foldl (fun a i => a * (i + 1)) 1

-- Repeated squaring: 3 ^ (2 ^ 10).
#guard
  let r := (List.range 10).foldl (fun a _ => mul a a) (ofNat 3)
  toNat r == 3 ^ 2 ^ 10

/-! Slices of limbs -/

-- Splitting a number into a low and a high part, with the slices of a single array.
#guard values.all fun n =>
  let a := ofNat n
  (List.range (a.size + 1)).all fun k =>
    let lo := a[*...k]
    let hi := a[k...*]
    toNat lo + toNat hi * 2 ^ (32 * k) == n &&
    add (shiftLimbs (trim hi.copy) k) lo == a

-- One step of Karatsuba's algorithm, which multiplies the halves of each operand.
#guard (samples 20 600).all fun m => (samples 20 600 (seed := 7)).all fun n =>
  let a := ofNat m
  let b := ofNat n
  let k := (max a.size b.size + 1) / 2
  let z₀ := mul a[*...k] b[*...k]
  let z₂ := mul a[k...*] b[k...*]
  let z₁ := mul (add a[*...k] a[k...*]) (add b[*...k] b[k...*])
  -- z₁ - z₀ - z₂ is computed with `Nat` since there is no subtraction here.
  let mid := ofNat (toNat z₁ - toNat z₀ - toNat z₂)
  let r := add (add z₀ (shiftLimbs mid k)) (shiftLimbs z₂ (2 * k))
  r == mul a b && toNat r == m * n
