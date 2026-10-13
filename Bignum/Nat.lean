/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32

/-!
# Natural numbers as limbs

A natural number is stored as little-endian base 2³² limbs in a `UInt32Array`. The arithmetic
works on slices of limbs, so it accepts trailing zero limbs, and its results are trimmed so that
the most significant limb is nonzero. Addition and multiplication are the schoolbook algorithms.
-/

open ScalarArray

namespace Bignum

/-- Removes the trailing zero limbs. -/
public def trim (a : UInt32Array) : UInt32Array := a.popWhile (· == 0)

/-- Whether the most significant limb is nonzero. -/
public def isTrimmed (a : UInt32Array) : Bool := a.back? != some 0

/-- The limbs of a natural number. -/
public def ofNat (n : Nat) : UInt32Array := loop n .empty
where
  loop (n : Nat) (acc : UInt32Array) : UInt32Array :=
    if h : n = 0 then acc else loop (n / 2 ^ 32) (acc.push n.toUInt32)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The natural number that a slice of limbs denotes. -/
public def toNat (s : UInt32Array.Slice) : Nat := s.foldr (fun d n => n * 2 ^ 32 + d.toNat) 0

/-- Adds two numbers. -/
public def add (a b : UInt32Array.Slice) : UInt32Array := Id.run do
  let n := max a.size b.size
  let mut r := UInt32Array.emptyWithCapacity (n + 1)
  let mut c : UInt64 := 0
  for i in [0:n] do
    let t := (a.getD i 0).toUInt64 + (b.getD i 0).toUInt64 + c
    r := r.push t.toUInt32
    c := t >>> 32
  return trim (r.push c.toUInt32)

/-- Multiplies two numbers. -/
public def mul (a b : UInt32Array.Slice) : UInt32Array := Id.run do
  let mut r := UInt32Array.replicate (a.size + b.size) 0
  let mut i := 0
  for x in a do
    -- Adds `x * b`, shifted by `i` limbs. The sum fits in 64 bits since
    -- `(2³² - 1) + (2³² - 1) * (2³² - 1) + (2³² - 1) = 2⁶⁴ - 1`.
    let mut c : UInt64 := 0
    let mut j := i
    for y in b do
      let t := r[j]!.toUInt64 + x.toUInt64 * y.toUInt64 + c
      r := r.set! j t.toUInt32
      c := t >>> 32
      j := j + 1
    r := r.set! j c.toUInt32
    i := i + 1
  return trim r

/-- Shifts a number left by `k` limbs. -/
public def shiftLimbs (a : UInt32Array) (k : Nat) : UInt32Array :=
  if a.isEmpty then a else .replicate k 0 ++ a

end Bignum
