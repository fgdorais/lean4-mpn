/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPN64

namespace MPNTest.W64

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

/-! Multiplication -/

/-- Checks `mul1`, `addMul1` and `mulBasecase` on an `m`-limb `a` and an `n`-limb `b`. -/
def checkMul (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  (edges m).all fun x => (edges n).all fun y => [0, 1, 2 ^ 64 - 1].all fun c =>
    let a := (limbs m x).toUSlice
    let b := (limbs n y).toUSlice
    let z := y % 2 ^ 64
    let (p, cp) := MPN.W64.mul1 (inner r m) a z.toUInt64 c.toUInt64
    let (q, cq) := MPN.W64.addMul1 (inner r m) a z.toUInt64 c.toUInt64
    let s := MPN.W64.mulBasecase (inner r (m + n)) a b
    window p 1 m + 2 ^ (64 * m) * cp.toNat == x * z + c &&
    window q 1 m + 2 ^ (64 * m) * cq.toNat == window r 1 m + x * z + c &&
    window s 1 (m + n) == x * y &&
    p[0]! == pad && p[m + 1]! == pad && q[0]! == pad && q[m + 1]! == pad &&
    s[0]! == pad && s[m + n + 1]! == pad

-- `mulBasecase` adds the rows after the first two at a time: even and odd counts of them.
#guard [(1, 1), (2, 1), (1, 2), (3, 3), (4, 2), (2, 5), (5, 4), (3, 6), (8, 7), (1, 7)].all
  fun (m, n) => checkMul m n

-- A window too short for the product: `mulBasecase` leaves it unchanged.
#guard
  let r := UInt64Array.replicate 5 7
  let a := (limbs 2 (2 ^ 100)).toUSlice
  MPN.W64.mulBasecase (inner r 3) a a == r

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
    let s := MPN.W64.mulKaratsuba MPN.W64.config (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    window s 1 (m + n) == x * y && s[0]! == pad && s[m + n + 1]! == pad

-- Around `mulKaratsuba = 64`: one level, two levels (130 splits into 65), unbalanced
-- operands below and above the split point, and below the threshold.
#guard [(64, 64), (65, 64), (100, 77), (127, 65), (130, 130), (130, 60), (257, 256), (63, 63),
  (50, 10)].all fun (m, n) => checkKaratsuba m n

/-! Squaring -/

/-- Checks `sqrBasecase` on an `n`-limb `a`, on random, all-ones and edge limbs. -/
def checkSqr (n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  ([randomLimbs n 1, randomLimbs n 7, 2 ^ (64 * n) - 1] ++ (edges n).map (· % 2 ^ (64 * n))).all
    fun x =>
      let s := MPN.W64.sqrBasecase (inner r (2 * n)) (limbs n x).toUSlice
      window s 1 (2 * n) == x * x && s[0]! == pad && s[2 * n + 1]! == pad

#guard [1, 2, 3, 4, 5, 8, 13, 32, 64].all checkSqr

/-- Checks `sqrKaratsuba` on an `n`-limb `a`. -/
def checkSqrKaratsuba (n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  [randomLimbs n 1, randomLimbs n 7, 2 ^ (64 * n) - 1, 2 ^ (64 * n - 1)].all fun x =>
    let s := MPN.W64.sqrKaratsuba MPN.W64.config (inner r (2 * n)) (limbs n x).toUSlice
    window s 1 (2 * n) == x * x && s[0]! == pad && s[2 * n + 1]! == pad

-- Around `sqrKaratsuba = 96`: below, one level, two levels, odd sizes.
#guard [64, 95, 96, 97, 127, 192, 193, 257, 400].all checkSqrKaratsuba

-- A window too short for the square: both leave it unchanged.
#guard
  let r := UInt64Array.replicate 5 7
  let a := (limbs 2 (2 ^ 100)).toUSlice
  MPN.W64.sqrBasecase (inner r 3) a == r && MPN.W64.sqrKaratsuba MPN.W64.config (inner r 3) a == r

/-! Subtracting a product by a limb -/

-- `subMul1`, main's `subMul1Step` on slices; main's kernels are checked in `MPNTest.Kernels`.
#guard [2, 3, 5, 16].all fun n =>
  [randomLimbs n 3, 2 ^ (64 * n) - 1].all fun x => [1, 3, 2 ^ 64 - 1].all fun m =>
    let y := randomLimbs n 5
    let (p, cp) := MPN.W64.subMul1 (limbs n x).toUSlice (limbs n y).toUSlice m.toUInt64
    window p 0 n + y * m == x + 2 ^ (64 * n) * cp.toNat

/-! Shifts and bits -/

/--
Checks the shifts and `log2` on an `n`-limb value: those by less than a limb written at offset 1
of a padded buffer, with the padding unchanged, and those of arrays by any number of bits.
-/
def checkBits (n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  (edges n ++ [randomLimbs n 7]).all fun x =>
    let a := (limbs n x).toUSlice
    let ls := [1, 7, 63].all fun s =>
      let r := UInt64Array.replicate (n + 2) pad
      let (p, c) := MPN.W64.lshift (inner r n) a s.toUInt64
      let (q, d) := MPN.W64.rshift (inner r n) a s.toUInt64
      window p 1 n + 2 ^ (64 * n) * c.toNat == x * 2 ^ s && p[0]! == pad && p[n + 1]! == pad &&
        window q 1 n == x / 2 ^ s && d.toNat == x % 2 ^ s && q[0]! == pad && q[n + 1]! == pad
    let gs := [0, 1, 63, 64, 65, 128, 64 * n - 1, 64 * n + 3].all fun k =>
      let p := MPN.W64.Num.shl (limbs n x) k
      let q := MPN.W64.Num.shr (limbs n x) k
      p.size == k / 64 + n + 1 && p.toNat == x * 2 ^ k && q.size == n - k / 64 &&
        q.toNat == x / 2 ^ k
    ls && gs && MPN.W64.log2 a == x.log2

#guard [1, 2, 3, 5, 16, 33].all checkBits

/-! Division -/

-- Two-by-one division of words, on both widths, against `Nat`.
#guard [(0, 0, 1), (0, 5, 3), (2, 7, 3), (0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF), (1, 0, 2),
  (0x7FFFFFFF, 0x12345678, 0x80000000)].all fun (h, l, d) =>
    (UInt32.div2 h.toUInt32 l.toUInt32 d.toUInt32).toNat == (h * 2 ^ 32 + l) / d &&
    (UInt64.div2 h.toUInt64 l.toUInt64 d.toUInt64).toNat == (h * 2 ^ 64 + l) / d
#guard (UInt64.div2 0xFFFFFFFFFFFFFFFE 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF).toNat ==
  ((2 ^ 64 - 2) * 2 ^ 64 + 2 ^ 64 - 1) / (2 ^ 64 - 1)

-- `divRem1With` on edge values, written at offset 1 of a padded buffer: normalized divisors (the
-- reciprocal steps of `div21`, from the first limb or never), unnormalized ones (the same steps
-- after a shift, or `UInt64.div2`), and the largest quotient limbs.
#guard [0, 4294967295].all fun t => [1, 2, 5, 8, 40].all fun n => (edges n).all fun x =>
  [1, 3, 10 ^ 19 - 1, 10 ^ 19, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 0xF123456789ABCDEF,
    2 ^ 64 - 2, 2 ^ 64 - 1].all fun d =>
    let r := UInt64Array.replicate (n + 2) 0xAAAAAAAAAAAAAAAA
    let (q, m) := MPN.W64.divRem1With t t (inner r n) (limbs n x).toUSlice d.toUInt64
    window q 1 n == x / d && m.toNat == x % d && q[0]! == 0xAAAAAAAAAAAAAAAA &&
      q[n + 1]! == 0xAAAAAAAAAAAAAAAA


/--
Checks `divRemWith t` on an `m`-limb `a` and an `n`-limb `b`, read at offset 1 of padded buffers:
the quotient in `m - n + 1` limbs and the remainder in `n` limbs.
-/
def checkDiv (t : USize) (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let as := [randomLimbs m 11, 2 ^ (64 * m) - 1, 2 ^ (64 * (m - 1)), 2 ^ (64 * m - 1) + 12345]
  let bs := [randomLimbs n 12, 2 ^ (64 * n) - 1, 2 ^ (64 * (n - 1)), 2 ^ (64 * (n - 1)) + 1,
    2 ^ (64 * n - 1), 3 * 2 ^ (64 * (n - 1)) + 5]
  let padded (k x : Nat) : UInt64Array := .ofFn fun (i : Fin (k + 2)) =>
    if i.1 = 0 ∨ i.1 = k + 1 then pad else (x / 2 ^ (64 * (i.1 - 1))).toUInt64
  as.all fun x => bs.all fun y =>
    let (q, r) := MPN.W64.divRemWith t (inner (padded m x) m) (inner (padded n y) n)
    q.size == m - n + 1 && r.size == n && q.toNat == x / y && r.toNat == x % y

#guard [(1, 1), (5, 1), (2, 2), (3, 2), (10, 3), (10, 10), (40, 17), (100, 50), (300, 2)].all
  fun (m, n) => checkDiv 0 m n && checkDiv 4294967295 m n

-- An estimate one too large after the 3-by-2 correction, so that `addBack` runs: the top limbs of
-- `2 ^ (64 n - 1) + 2 ^ (64 (n - 2)) - 1` give the estimate `2` for `2 ^ (64 n)`, whose quotient is
-- `1`, and the same shifted up a few limbs.
#guard [3, 4, 9].all fun n =>
  let y := 2 ^ (64 * n - 1) + 2 ^ (64 * (n - 2)) - 1
  [2 ^ (64 * n), 2 ^ (64 * n) + 5, 2 ^ (64 * (n + 3)) + 2 ^ (64 * 3) - 1].all fun x =>
    let m := (Nat.log2 x) / 64 + 1
    let k := m - n + 1
    let (q', r') := MPN.W64.divRem (limbs m x).toUSlice (limbs n y).toUSlice
    window q' 0 k == x / y && window r' 0 n == x % y

/-- Checks `Num.divMod` on an `m`-limb `x` and an `n`-limb `y`, against `Nat`. -/
def checkNumDiv (m n : Nat) : Bool :=
  [randomLimbs m 41, 2 ^ (64 * m) - 1].all fun x =>
    [randomLimbs n 42, 2 ^ (64 * n) - 1, 2 ^ (64 * (n - 1)) + 1, 2 ^ (64 * n - 1)].all fun y =>
      let (q, r) := MPN.W64.Num.divMod (limbs m x) (limbs n y)
      q.toNat == x / y && r.toNat == x % y && (MPN.W64.Num.div (limbs m x) (limbs n y)).toNat == x / y

-- Below `divDC`, at it, and recursing: digits of `⌊n / 2⌋` limbs and a shorter top digit,
-- and digits that recurse once more (`1100 / 2 ≥ 512`).
#guard [(10, 3), (300, 100), (1000, 333), (1100, 512), (2000, 1000), (700, 512),
  (4000, 1100)].all fun (m, n) => checkNumDiv m n

/--
Checks `ops64B.divMu`, `ops64B.divMuW` and `ops64B.divQMuW`, Barrett's division with Newton's
reciprocal, the others with wrapped remainders, which `Num.divMod` and `Num.div` use from `divMu`
and `divQMu` limbs, on an `m`-limb `x` and an `n`-limb `y`, against `Nat`: normalized divisors, as
`Num.divMod` passes, and others, on which `divMuW` falls back on `divMu`.
-/
def checkDivMu (m n : Nat) : Bool :=
  [randomLimbs m 43, 2 ^ (64 * m) - 1].all fun x =>
    [randomLimbs n 44 ||| 2 ^ (64 * n - 1), 2 ^ (64 * n) - 1, 2 ^ (64 * n - 1),
      2 ^ (64 * (n - 1)) + 1].all fun y =>
      let (q, r) := MPN.W64.ops64B.divMu (limbs m x) (limbs n y)
      let (q', r') := MPN.W64.ops64B.divMuW (limbs m x) (limbs n y)
      -- Just below a multiple of `y`, the estimate of the quotient alone does not decide.
      let x' := x / y * y - 1
      q.toNat == x / y && r.toNat == x % y && q'.toNat == x / y && r'.toNat == x % y &&
        (MPN.W64.ops64B.divQMuW (limbs m x) (limbs n y)).toNat == x / y &&
        (MPN.W64.ops64B.divQMuW (limbs m x') (limbs n y)).toNat == x' / y

-- The reciprocal by the slow division (up to 4 limbs), by Newton's iteration, and in blocks.
#guard [(8, 3), (9, 5), (40, 20), (100, 33), (300, 101), (64, 64), (200, 7)].all fun (m, n) =>
  checkDivMu m n

/-- Checks `Num.mulModB` (`2ᵏ` pieces of `m` limbs) and `Num.modB` against `Nat`. -/
def checkMulMod (k m na nb : Nat) : Bool :=
  let M := 2 ^ (64 * (m * 2 ^ k)) - 1
  [(randomLimbs na 51, randomLimbs nb 52), (2 ^ (64 * na) - 1, 2 ^ (64 * nb) - 1)].all
    fun (x, y) =>
      let p := MPN.W64.Num.mulModB (limbs na x) (limbs nb y) k m
      p.toNat % M == x * y % M && (MPN.W64.Num.modB p (m * 2 ^ k)).toNat == x * y % M

-- Through the FFT (`FFTModCheck` holds) and through the fallback, and `modB` on long inputs.
#guard [(2, 8, 32, 32), (3, 5, 40, 17), (4, 16, 256, 200), (6, 64, 4096, 4096), (1, 3, 6, 6),
  (2, 4, 40, 40)].all fun (k, m, na, nb) => checkMulMod k m na nb

/-! Square root -/

/-- Checks `sqrtRem` on `x` against `Nat.sqrt`. -/
def checkSqrt (x : Nat) : Bool :=
  let n := Nat.log2 x / 64 + 1
  let (s, r) := MPN.W64.sqrtRem (limbs n x)
  s.toNat == x.sqrt && r.toNat == x - x.sqrt * x.sqrt

#guard [0, 1, 2, 3, 4, 8, 15, 16, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 126, 2 ^ 128 - 1, 2 ^ 128,
  (2 ^ 64 - 1) ^ 2, (2 ^ 64 - 1) ^ 2 - 1, 3 * 2 ^ 200 + 7].all checkSqrt

#guard [1, 2, 3, 4, 5, 7, 8, 13, 16, 31, 64, 100, 300, 600].all fun n =>
  let x := randomLimbs n 31
  let y := randomLimbs ((n + 1) / 2) 32
  [x, x / 3, 2 ^ (64 * n) - 1, y * y, y * y - 1, y * y + 2 * y].all checkSqrt

/-! Greatest common divisor -/

/-- Checks `Num.gcd` against `Nat.gcd` on `x g` and `y g` for a common factor `g`. -/
def checkGcd (m n k : Nat) : Bool :=
  let g := randomLimbs k 61
  [(randomLimbs m 62 * g, randomLimbs n 63 * g), (randomLimbs m 64, randomLimbs n 65),
    (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1), (randomLimbs m 66 * g, g)].all fun (x, y) =>
    let lx := Nat.log2 x / 64 + 1
    let ly := Nat.log2 y / 64 + 1
    (MPN.W64.Num.gcd (limbs (lx + 1) x) (limbs ly y)).toNat == Nat.gcd x y

#guard checkGcd 1 1 1 && (MPN.W64.Num.gcd (limbs 2 0) (limbs 1 7)).toNat == 7 &&
  (MPN.W64.Num.gcd (limbs 2 12) (limbs 0 0)).toNat == 12
#guard [(2, 2, 1), (5, 3, 2), (20, 20, 7), (64, 60, 16), (200, 190, 50)].all
  fun (m, n, k) => checkGcd m n k
-- On pairs of words (`gcd2`): edge values, a top word `2⁶⁴ - 1` (where `bh + 1` wraps), common
-- factors of one and two words, and both orders.
#guard
  let vs := edges 2 ++ [2 ^ 64, 2 ^ 64 + 1, 2 ^ 65 - 1, (2 ^ 64 - 1) * 2 ^ 64, 2 ^ 127 + 2 ^ 63,
    randomLimbs 2 81, randomLimbs 2 82 / 2 ^ 70 * 0xFFFFFFFB, randomLimbs 1 83 * 3 ^ 40,
    randomLimbs 1 84 * 3 ^ 40, 3 ^ 80, 5 ^ 55]
  vs.all fun x => vs.all fun y =>
    (MPN.W64.Num.gcd (limbs 2 x) (limbs 2 y)).toNat == Nat.gcd x y &&
      (MPN.W64.Num.gcd (limbs 2 x) (limbs 1 (y % 2 ^ 64))).toNat == Nat.gcd x (y % 2 ^ 64)
-- Through half-gcd (`gcdWith` with a low threshold), with recursion above `hgcdBase` limbs.
#guard [(40, 40, 8), (100, 90, 20), (700, 650, 100), (900, 900, 1)].all fun (m, n, k) =>
  let g := randomLimbs k 71
  let x := randomLimbs m 72 * g
  let y := randomLimbs n 73 * g
  (MPN.W64.gcdWith 16 (limbs (Nat.log2 x / 64 + 1) x) (limbs (Nat.log2 y / 64 + 1) y)).toNat ==
    Nat.gcd x y

/-! Decimal strings -/

/-- Checks `Num.toDecimal` and `Num.ofDecimal?` on `x`, through both of their methods. -/
def checkDec (x : Nat) : Bool :=
  let n := Nat.log2 x / 64 + 1
  let a := limbs (n + 1) x
  MPN.W64.Num.toDecimal a == Nat.repr x && MPN.W64.toDecimalWith 2 a == Nat.repr x &&
    (MPN.W64.Num.ofDecimal? (Nat.repr x)).map (·.toNat) == some x &&
    (MPN.W64.ofDecimalWith 1 (Nat.repr x)).map (·.toNat) == some x

#guard [0, 1, 9, 10, 10 ^ 19 - 1, 10 ^ 19, 10 ^ 19 + 1, 2 ^ 64 - 1, 2 ^ 64, 10 ^ 38,
  10 ^ 38 - 1, 3 * 10 ^ 57 + 7].all checkDec
#guard [1, 2, 3, 5, 17, 40, 100].all fun n =>
  [randomLimbs n 81, 2 ^ (64 * n) - 1, 10 ^ (19 * n), 10 ^ (19 * n) - 1].all checkDec
#guard (MPN.W64.Num.ofDecimal? "1_000_000").map (·.toNat) == some 1000000 &&
  (MPN.W64.Num.ofDecimal? "12a").isNone && (MPN.W64.Num.ofDecimal? "").isNone

/-! Toom multiplication -/

/-- Checks `mulToom` on an `m`-limb `a` and an `n`-limb `b`, in both orders. -/
def checkToom (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1)].all fun (x, y) =>
    let s := MPN.W64.mulToom MPN.W64.config (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    let t := MPN.W64.mulToom MPN.W64.config (inner r (m + n)) (limbs n y).toUSlice (limbs m x).toUSlice
    window s 1 (m + n) == x * y && window t 1 (m + n) == x * y &&
      s[0]! == pad && s[m + n + 1]! == pad

-- Below the threshold; Toom-3 (`2/3 < n/m`); Toom-3 by 2 (`1/3 < n/m ≤ 2/3`); Toom-4 by 2
-- (`1/4 < n/m ≤ 1/3`, roughly); Karatsuba for the rest; and Toom-3 recursing into itself.
#guard [(128, 128), (300, 200), (385, 385), (500, 400), (900, 450), (700, 400), (1200, 400),
  (1600, 500), (2000, 390), (1200, 1200)].all fun (m, n) => checkToom m n

-- Toom-4 (`3/4 < n/m`), Toom-4 by 3 (`1/2 < n/m ≤ 3/4`, roughly), and Toom-4 recursing into itself.
#guard [(700, 700), (800, 610), (900, 650), (1000, 600), (2400, 2400)].all
  fun (m, n) => checkToom m n

-- Toom-6 (`5/6 < n/m`), at and above `mulToom6`, and recursing into Toom-4.
#guard [(770, 770), (800, 790), (1500, 1500), (1700, 1500), (3000, 2600), (6000, 6000)].all
  fun (m, n) => checkToom m n

-- The unbalanced shapes from their own thresholds: Toom-3 by 2 from `mulToom32` and Toom-4 by 2
-- from `mulToom42`, below `mulToom3`.
#guard [(308, 176), (350, 100), (350, 87), (240, 175), (330, 180)].all fun (m, n) => checkToom m n

/-! FFT multiplication -/

/--
Checks `fftMul` with `2ᵏ` pieces on an `m`-limb `a` and an `n`-limb `b`, in both orders, and that
it takes the FFT path.
-/
def checkFFT (m n k : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  let p := MPN.W64.FFT.fftParams (m + n) k
  decide (MPN.W64.FFT.FFTCheck (inner r (m + n)) (limbs m 1).toUSlice (limbs n 1).toUSlice k p.1 p.2) &&
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1)].all fun (x, y) =>
    let s := MPN.W64.FFT.fftMul MPN.W64.config (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice k
    let t := MPN.W64.FFT.fftMul MPN.W64.config (inner r (m + n)) (limbs n y).toUSlice (limbs m x).toUSlice k
    window s 1 (m + n) == x * y && window t 1 (m + n) == x * y &&
      s[0]! == pad && s[m + n + 1]! == pad

#guard [(50, 40, 3), (1, 1, 1), (7, 3, 2), (100, 1, 4), (64, 64, 5), (300, 200, 6), (200, 7, 7),
  (150, 150, 8), (1000, 900, 5)].all fun (m, n, k) => checkFFT m n k

/-- Checks `MPN.mul` on an `m`-limb `a` and an `n`-limb `b`, in both orders. -/
def checkMPNMul (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1)].all fun (x, y) =>
    let s := MPN.W64.mul MPN.W64.config (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    let t := MPN.W64.mul MPN.W64.config (inner r (m + n)) (limbs n y).toUSlice (limbs m x).toUSlice
    window s 1 (m + n) == x * y && window t 1 (m + n) == x * y &&
      s[0]! == pad && s[m + n + 1]! == pad

-- Below and above `mulFFT`, and an unbalanced pair on each side of `mulFFTMin`.
#guard [(4095, 4095), (4096, 4000), (3072, 2048), (3072, 2049), (5000, 330), (5000, 300),
  (4, 3)].all
  fun (m, n) => checkMPNMul m n

-- Unbalanced products, split into chunks of the smaller operand: around `mulUnbalanced`, around
-- twice the smaller operand, a last chunk of one limb, and around `mulChunkMax`.
#guard [(1000, 96), (1000, 95), (1000, 500), (999, 500), (1001, 100), (3071, 1500), (5000, 1023),
  (5000, 1024)].all
  fun (m, n) => checkMPNMul m n

/-- Checks `fftSqr` with `2ᵏ` pieces and `MPN.sqr` on an `n`-limb `a`. -/
def checkMPNSqr (n k : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  let p := MPN.W64.FFT.fftParams (2 * n) k
  decide (MPN.W64.FFT.FFTCheck (inner r (2 * n)) (limbs n 1).toUSlice (limbs n 1).toUSlice k p.1
    p.2) &&
  [randomLimbs n 1, 2 ^ (64 * n) - 1].all fun x =>
    let s := MPN.W64.FFT.fftSqr MPN.W64.config (inner r (2 * n)) (limbs n x).toUSlice k
    let t := MPN.W64.sqr MPN.W64.config (inner r (2 * n)) (limbs n x).toUSlice
    window s 1 (2 * n) == x * x && window t 1 (2 * n) == x * x &&
      s[0]! == pad && s[2 * n + 1]! == pad && t[0]! == pad && t[2 * n + 1]! == pad

-- `MPN.sqr` on each side of `sqrFFT`.
#guard [(1, 1), (7, 2), (100, 4), (300, 6), (2047, 8), (2815, 8), (2816, 8)].all
  fun (n, k) => checkMPNSqr n k

/-- Checks `MPN.sqrToom` on an `n`-limb `a`. -/
def checkSqrToom (n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  [randomLimbs n 1, 2 ^ (64 * n) - 1].all fun x =>
    let s := MPN.W64.sqrToom MPN.W64.config (inner r (2 * n)) (limbs n x).toUSlice
    window s 1 (2 * n) == x * x && s[0]! == pad && s[2 * n + 1]! == pad

-- Around `sqrToom3`, `sqrToom4` and `sqrToom6`, and recursion.
#guard [599, 600, 999, 1000, 1199, 1200, 2800, 7300].all checkSqrToom


/-- A random number of `bits` bits. -/
def randomBits (bits seed : Nat) : Nat := randomLimbs ((bits + 63) / 64) seed % 2 ^ bits

-- Values at and around the boundary between words and limbs; `MPNTest.Kernels` checks the
-- operations of `MPN.Nat` on them against `Nat`.
def bigNatValues : List Nat :=
  [0, 1, 2, 7, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 128 - 1, 2 ^ 128, randomBits 200 61, randomBits 1000 67, 3 ^ 200]

-- Division by a word, and literals.
#guard [2 ^ 64, 2 ^ 128 - 1, randomBits 300 89, 2 ^ 1024 - 1].all fun a =>
  [1, 3, 2 ^ 32 + 1, 2 ^ 63, 2 ^ 64 - 1, 10 ^ 18].all fun b =>
    (MPN.W64.Nat.ofNat a / MPN.W64.Nat.ofNat b).toNat == a / b &&
      (MPN.W64.Nat.ofNat a % MPN.W64.Nat.ofNat b).toNat == a % b
#guard ((12345678901234567890123 : MPN.W64.Nat) * 1000).toNat == 12345678901234567890123000
#guard (MPN.W64.Nat.ofNat (2 ^ 64 - 1) + 1).toNat == 2 ^ 64
#guard (MPN.W64.Nat.ofNat (2 ^ 64) - 1).toNat == 2 ^ 64 - 1

-- Shifts, `log2`, `sqrt` and `pow`.
#guard bigNatValues.all fun a =>
  let x := MPN.W64.Nat.ofNat a
  [0, 1, 5, 63, 64, 65, 100, 200].all (fun k =>
    (x <<< k).toNat == a <<< k && (x >>> k).toNat == a >>> k) &&
  x.log2 == a.log2 && (MPN.W64.Nat.sqrt x).toNat == Nat.sqrt a &&
  [0, 1, 2, 3, 7, 10].all (fun k => (x ^ k).toNat == a ^ k)

#guard [2 ^ 64 + 1, 2 ^ 128 - 1, 3 ^ 50, randomBits 500 113, randomBits 3000 83].all
  fun r => [r * r - 1, r * r, r * r + 1].all fun a =>
    (MPN.W64.Nat.sqrt (MPN.W64.Nat.ofNat a)).toNat == Nat.sqrt a

-- Decimal strings, and what `String.toNat?` accepts.
#guard (bigNatValues ++ [10 ^ 19 - 1, 10 ^ 19, 10 ^ 38 * 7, randomBits 3000 89]).all fun a =>
  let x := MPN.W64.Nat.ofNat a
  toString x == toString a && reprStr x == reprStr a &&
    (MPN.W64.Nat.ofString? (toString a)).map (·.toNat) == some a

#guard ["", "_", "_1", "1_", "1__0", "abc", "12a", "-1", " 1", "000", "007", "1_000",
    "18446744073709551616", "18_446_744_073_709_551_615", "123456789012345678901234567890"].all
  fun s => (MPN.W64.Nat.ofString? s).map (·.toNat) == s.toNat?

end MPNTest.W64
