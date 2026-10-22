/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPN

/-! Word operations -/

/-- Checks the high-word operations of an `n`-bit type against `Nat` on its edge values. -/
def checkWords (n : Nat) (ofNat : Nat → α) (toNat : α → Nat)
    (addh subh : α → α → α → α) (mulh : α → α → α) : Bool :=
  let vs := [0, 1, 2, 2 ^ (n - 1) - 1, 2 ^ (n - 1), 2 ^ n - 2, 2 ^ n - 1]
  vs.all fun x => vs.all fun y =>
    toNat (mulh (ofNat x) (ofNat y)) == x * y / 2 ^ n &&
    vs.all fun c =>
      toNat (addh (ofNat c) (ofNat x) (ofNat y)) == (c + (x + y) / 2 ^ n) % 2 ^ n &&
      -- A borrow makes the high word of `x - y` all ones, which `subh` subtracts from `c`.
      toNat (subh (ofNat c) (ofNat x) (ofNat y)) == (c + if x < y then 1 else 0) % 2 ^ n

#guard checkWords 32 UInt32.ofNat UInt32.toNat UInt32.addh UInt32.subh UInt32.mulh
#guard checkWords 64 UInt64.ofNat UInt64.toNat UInt64.addh UInt64.subh UInt64.mulh

/-! Addition and subtraction -/

open ScalarArray

/-- The `n` low base `2⁶⁴` limbs of `m`. -/
def limbs (n m : Nat) : UInt64Array := .ofFn fun (i : Fin n) => (m / 2 ^ (64 * i.1)).toUInt64

/-- The value of the limbs `r[off], …, r[off + n - 1]`. -/
def window (r : UInt64Array) (off n : Nat) : Nat :=
  (List.range n).foldr (fun i v => r[off + i]!.toNat + 2 ^ 64 * v) 0

/-- Edge values of up to `n` limbs, where carries and borrows propagate the most. -/
def edges (n : Nat) : List Nat :=
  [0, 1, 2 ^ 63, 2 ^ (64 * n) - 1, 2 ^ (64 * n) - 2, 2 ^ (64 * (n - 1)), 2 ^ (64 * n) / 3]

/-- The limbs `1` to `n` of `r`, a window between two padding limbs. -/
def inner (r : UInt64Array) (n : Nat) : UInt64Array.USlice := r.uslice 1 (n + 1).toUSize

/-- Checks `addN` and `subN` on `n`-limb numbers written at offset 1 of a 2-limb padded buffer. -/
def checkAddSub (n : Nat) : Bool :=
  let r := UInt64Array.replicate (n + 2) 0xAAAAAAAAAAAAAAAA
  (edges n).all fun x => (edges n).all fun y => [0, 1, 2, 2 ^ 64 - 1].all fun c =>
    let a := (limbs n x).toUSlice
    let b := (limbs n y).toUSlice
    let (s, cs) := MPN.addN (inner r n) a b c.toUInt64
    let (d, cd) := MPN.subN (inner r n) a b c.toUInt64
    window s 1 n + 2 ^ (64 * n) * cs.toNat == x + y + c &&
    window d 1 n + y + c == x + 2 ^ (64 * n) * cd.toNat &&
    -- The padding limbs are untouched.
    s[0]! == r[0]! && s[n + 1]! == r[n + 1]! && d[0]! == r[0]! && d[n + 1]! == r[n + 1]!

#guard [1, 2, 3, 5].all checkAddSub
#guard
  let e := UInt64Array.empty.toUSlice
  (MPN.addN e e e 5).2 == 5

-- A window shorter than the operands: only its limbs are written.
#guard
  let r := UInt64Array.replicate 4 7
  let a := (limbs 3 (2 ^ 192 - 1)).toUSlice
  let (s, c) := MPN.addN (inner r 2) a a
  s.toList == [7, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 7] && c == 1

/-- Checks `add` and `sub` on an `m`-limb `a` and an `n`-limb `b`, with `n ≤ m`. -/
def checkAddSubGen (m n : Nat) : Bool :=
  let r := UInt64Array.replicate (m + 2) 0xAAAAAAAAAAAAAAAA
  (edges m).all fun x => (edges n).all fun y => [0, 1, 2 ^ 64 - 1].all fun c =>
    let y := y % 2 ^ (64 * n)
    let a := (limbs m x).toUSlice
    let b := (limbs n y).toUSlice
    let (s, cs) := MPN.add (inner r m) a b c.toUInt64
    let (d, cd) := MPN.sub (inner r m) a b c.toUInt64
    window s 1 m + 2 ^ (64 * m) * cs.toNat == x + y + c &&
    window d 1 m + y + c == x + 2 ^ (64 * m) * cd.toNat &&
    s[0]! == r[0]! && s[m + 1]! == r[m + 1]! && d[0]! == r[0]! && d[m + 1]! == r[m + 1]!

#guard [(1, 0), (1, 1), (3, 1), (3, 2), (4, 4), (5, 0)].all fun (m, n) => checkAddSubGen m n

/-! Multiplication -/

/-- Checks `mul1`, `addMul1` and `mulBasecase` on an `m`-limb `a` and an `n`-limb `b`. -/
def checkMul (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  (edges m).all fun x => (edges n).all fun y => [0, 1, 2 ^ 64 - 1].all fun c =>
    let a := (limbs m x).toUSlice
    let b := (limbs n y).toUSlice
    let z := y % 2 ^ 64
    let (p, cp) := MPN.mul1 (inner r m) a z.toUInt64 c.toUInt64
    let (q, cq) := MPN.addMul1 (inner r m) a z.toUInt64 c.toUInt64
    let s := MPN.mulBasecase (inner r (m + n)) a b
    window p 1 m + 2 ^ (64 * m) * cp.toNat == x * z + c &&
    window q 1 m + 2 ^ (64 * m) * cq.toNat == window r 1 m + x * z + c &&
    window s 1 (m + n) == x * y &&
    p[0]! == pad && p[m + 1]! == pad && q[0]! == pad && q[m + 1]! == pad &&
    s[0]! == pad && s[m + n + 1]! == pad

#guard [(1, 1), (2, 1), (1, 2), (3, 3), (4, 2), (2, 5)].all fun (m, n) => checkMul m n

/-- Checks `mulComba` on an `m`-limb `a` and an `n`-limb `b`. -/
def checkComba (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  (edges m).all fun x => (edges n).all fun y =>
    let x := x % 2 ^ (64 * m)
    let y := y % 2 ^ (64 * n)
    let s := MPN.mulComba (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    window s 1 (m + n) == x * y && s[0]! == pad && s[m + n + 1]! == pad

#guard [(0, 0), (0, 3), (3, 0), (1, 1), (2, 1), (1, 2), (3, 3), (4, 2), (2, 5), (7, 7)].all
  fun (m, n) => checkComba m n

-- A window too short for the product: `mulBasecase` and `mulComba` leave it unchanged.
#guard
  let r := UInt64Array.replicate 5 7
  let a := (limbs 2 (2 ^ 100)).toUSlice
  MPN.mulBasecase (inner r 3) a a == r && MPN.mulComba (inner r 3) a a == r

/-! Karatsuba multiplication -/

/-- Pseudorandom numbers of exactly `n` limbs. -/
def randomLimbs (n seed : Nat) : Nat := Id.run do
  let mut s := seed
  let mut x := 0
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    x := x * 2 ^ 64 + s
  return x ||| 2 ^ (64 * n - 1)

/-- Checks `mulKaratsuba` on an `m`-limb `a` and an `n`-limb `b`, on random and all-ones limbs. -/
def checkKaratsuba (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1),
    (2 ^ (64 * m) - 1, 2 ^ (64 * (n - 1)))].all fun (x, y) =>
    let s := MPN.mulKaratsuba (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    window s 1 (m + n) == x * y && s[0]! == pad && s[m + n + 1]! == pad

-- Around `karatsubaThreshold = 64`: one level, two levels (130 splits into 65), unbalanced
-- operands below and above the split point, and below the threshold.
#guard [(64, 64), (65, 64), (100, 77), (127, 65), (130, 130), (130, 60), (257, 256), (63, 63),
  (50, 10)].all fun (m, n) => checkKaratsuba m n
