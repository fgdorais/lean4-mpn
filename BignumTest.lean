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

/-- A pseudorandom number of exactly `bits` bits. -/
def sample1 (bits seed : Nat) : Nat := Id.run do
  let mut s := seed
  let mut n := 0
  for _ in [0:(bits + 31) / 32] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    n := n * 2 ^ 32 + s / 2 ^ 32
  return n % 2 ^ bits ||| 2 ^ (bits - 1)

def values : List Nat := edges ++ samples 40 400

/-! Addition -/

#guard values.all fun m => values.all fun n =>
  let r := add (ofNat m) (ofNat n)
  toNat r == m + n && isTrimmed r

#guard add (ofNat (2 ^ 128 - 1)) (ofNat 1) == ofNat (2 ^ 128)
#guard add UInt32Array.empty UInt32Array.empty == .empty

/-! Untrimmed addition, subtraction and adding at an offset -/

#guard values.all fun m => values.all fun n =>
  let r := addLimbs (ofNat m) (ofNat n)
  r.size == max (ofNat m).size (ofNat n).size + 1 && toNat r == m + n

#guard values.all fun m => values.all fun n =>
  let (hi, lo) := if m < n then (n, m) else (m, n)
  let a := ofNat hi ++ .replicate 1 0
  let r := subLimbs a (ofNat lo)
  r.size == a.size && toNat r == hi - lo

#guard (values.take 12).all fun m => (values.take 12).all fun n =>
  let r := ofNat m ++ .replicate 3 0
  let a : UInt32Array.Slice := ofNat n
  (List.range (r.size + 1)).all fun off =>
    if off + a.size ≤ r.size then
      let (r', c) := addAt r off a
      r'.size == r.size && toNat r' + 2 ^ (32 * r.size) * c.toNat == m + 2 ^ (32 * off) * n
    else true

/-! Multiplication by a limb -/

def limbs : List UInt32 := [0, 1, 2, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFE, 0xFFFFFFFF]

#guard values.all fun m => limbs.all fun x =>
  let (r, c) := mul1 (ofNat m) x
  r.size == (ofNat m).size && toNat r + 2 ^ (32 * r.size) * c.toNat == m * x.toNat

-- Adds `n * x` into `ofNat m` at every offset that fits.
#guard (values.take 12).all fun m => (values.take 12).all fun n => limbs.all fun x =>
  let r := ofNat m
  let a : UInt32Array.Slice := ofNat n
  (List.range (r.size + 1)).all fun off =>
    if h : off + a.size ≤ r.size then
      let (r', c) := addMul1 r off a x h
      r'.size == r.size &&
        toNat r' + 2 ^ (32 * (off + a.size)) * c.toNat == m + 2 ^ (32 * off) * (n * x.toNat)
    else true

/-! Multiplication -/

#guard values.all fun m => values.all fun n =>
  let r := mul (ofNat m) (ofNat n)
  toNat r == m * n && isTrimmed r

#guard mul (ofNat (2 ^ 128 - 1)) (ofNat (2 ^ 128 - 1)) ==
  ofNat ((2 ^ 128 - 1) * (2 ^ 128 - 1))
#guard mul (ofNat 0) (ofNat (2 ^ 100)) == .empty

-- Every case of the dispatcher, with operands in both orders and trailing zero limbs.
#guard values.all fun m => (edges ++ samples 10 100).all fun n =>
  let a := ofNat m ++ .replicate 2 0
  let b := ofNat n
  let r := mulLimbs a b
  let r' := mulLimbs b a
  r.size == a.size + b.size && toNat r == m * n && r'.size == r.size && toNat r' == m * n

-- Karatsuba: sizes around and well above `karatsubaThreshold`, balanced and not, odd and even,
-- with all-ones operands for the longest carries.
def bigSizes : List Nat := [31, 32, 33, 47, 64, 65, 100, 129, 200, 257]

#guard bigSizes.all fun m => bigSizes.all fun n =>
  let x := sample1 (32 * m) 7
  let y := sample1 (32 * n) 11
  toNat (mulLimbs (ofNat x) (ofNat y)) == x * y &&
    toNat (mulLimbs (ofNat (2 ^ (32 * m) - 1)) (ofNat (2 ^ (32 * n) - 1))) ==
      (2 ^ (32 * m) - 1) * (2 ^ (32 * n) - 1)

#guard (mul (ofNat (2 ^ 9600 - 1)) (ofNat (2 ^ 9000 - 1))).size ==
  (ofNat ((2 ^ 9600 - 1) * (2 ^ 9000 - 1))).size

-- Very unbalanced products, which split the longer operand.
#guard [47, 50, 64].all fun n => [100, 141, 300, 517].all fun m =>
  let x := sample1 (32 * m) 3
  let y := sample1 (32 * n) 5
  let r := mulLimbs (ofNat x) (ofNat y)
  r.size == m + n && toNat r == x * y && toNat (mulLimbs (ofNat y) (ofNat x)) == x * y

/-! Squaring -/

#guard values.all fun m => toNat (sqr (ofNat m)) == m * m && isTrimmed (sqr (ofNat m))

#guard (edges ++ bigSizes.map fun n => sample1 (32 * n) 13).all fun m =>
  let r := sqrLimbs (ofNat m ++ UInt32Array.replicate 2 0)
  r.size == 2 * ((ofNat m).size + 2) && toNat r == m * m

#guard [1, 2, 3, 46, 47, 100, 257].all fun n =>
  toNat (sqrBasecase (ofNat (2 ^ (32 * n) - 1))) == (2 ^ (32 * n) - 1) ^ 2

#guard mulBasecase (ofNat (2 ^ 64 - 1)) (ofNat (2 ^ 96 - 1)) ==
  ofNat ((2 ^ 64 - 1) * (2 ^ 96 - 1))

-- A long computation that reuses each result: 200 factorial.
#guard
  let r := (List.range 200).foldl (fun a i => mul a (ofNat (i + 1))) (ofNat 1)
  toNat r == (List.range 200).foldl (fun a i => a * (i + 1)) 1

-- Repeated squaring: 3 ^ (2 ^ 10).
#guard
  let r := (List.range 10).foldl (fun a _ => mul a a) (ofNat 3)
  toNat r == 3 ^ 2 ^ 10

/-! Division by a limb -/

#guard values.all fun m => limbs.all fun d => d == 0 ||
  let (q, r) := divRem1 (ofNat m) d
  q.size == (ofNat m).size && toNat q == m / d.toNat && r.toNat == m % d.toNat

/-! Comparison -/

#guard values.all fun m => values.all fun n =>
  lt (ofNat m) (ofNat n) == decide (m < n) &&
    lt (ofNat m ++ UInt32Array.replicate 2 0) (ofNat n) == decide (m < n)

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
