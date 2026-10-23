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

/-! Squaring -/

/-- Checks `sqrBasecase` on an `n`-limb `a`, on random, all-ones and edge limbs. -/
def checkSqr (n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  ([randomLimbs n 1, randomLimbs n 7, 2 ^ (64 * n) - 1] ++ (edges n).map (· % 2 ^ (64 * n))).all
    fun x =>
      let s := MPN.sqrBasecase (inner r (2 * n)) (limbs n x).toUSlice
      window s 1 (2 * n) == x * x && s[0]! == pad && s[2 * n + 1]! == pad

#guard [1, 2, 3, 4, 5, 8, 13, 32, 64].all checkSqr

/-- Checks `sqrKaratsuba` on an `n`-limb `a`. -/
def checkSqrKaratsuba (n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  [randomLimbs n 1, randomLimbs n 7, 2 ^ (64 * n) - 1, 2 ^ (64 * n - 1)].all fun x =>
    let s := MPN.sqrKaratsuba (inner r (2 * n)) (limbs n x).toUSlice
    window s 1 (2 * n) == x * x && s[0]! == pad && s[2 * n + 1]! == pad

-- Around `sqrKaratsubaThreshold = 96`: below, one level, two levels, odd sizes.
#guard [64, 95, 96, 97, 127, 192, 193, 257, 400].all checkSqrKaratsuba

-- A window too short for the square: both leave it unchanged.
#guard
  let r := UInt64Array.replicate 5 7
  let a := (limbs 2 (2 ^ 100)).toUSlice
  MPN.sqrBasecase (inner r 3) a == r && MPN.sqrKaratsuba (inner r 3) a == r

/-! Linear passes for the Toom methods -/

/-- Checks `subMul1`, `addMulInto`, `subMulInto`, halving and exact division by 3 on `n` limbs. -/
def checkLinear (n : Nat) : Bool :=
  [randomLimbs n 3, 2 ^ (64 * n) - 1, 2 ^ (64 * n - 1)].all fun x =>
    let y := randomLimbs (n / 2 + 1) 5 % 2 ^ (64 * n)
    let r := limbs n x
    [1, 3, 16, 81, 2 ^ 64 - 1].all fun m =>
      let (p, cp) := MPN.subMul1 r.toUSlice (limbs n y).toUSlice m.toUInt64
      let (q, cq) := MPN.addMulInto r.toUSlice (limbs (n / 2 + 1) y).toUSlice m.toUInt64
      let (s, cs) := MPN.subMulInto r.toUSlice (limbs (n / 2 + 1) y).toUSlice m.toUInt64
      window p 0 n + y * m == x + 2 ^ (64 * n) * cp.toNat &&
      window q 0 n + 2 ^ (64 * n) * cq.toNat == x + y * m &&
      window s 0 n + y * m == x + 2 ^ (64 * n) * cs.toNat
  && [randomLimbs (n - 1) 9, 2 ^ (64 * (n - 1)) - 1].all fun x =>
    let x2 := 2 * (x / 2)
    let x3 := 3 * (x / 3)
    let x5 := 5 * (x / 5)
    window (MPN.shl63Into (limbs n x2).toUSlice).1 1 (n - 1) == x2 / 2 &&
    window (MPN.divExact3Into (limbs n x3).toUSlice).1 0 n == x3 / 3 &&
    window (MPN.divExact5Into (limbs n x5).toUSlice).1 0 n == x5 / 5 &&
    [1, 2, 7, 63].all fun s => window (MPN.rshiftInto (limbs n x).toUSlice s.toUInt64) 0 n == x / 2
        ^ s

#guard [2, 3, 5, 16, 33].all checkLinear

/-! Toom multiplication -/

/-- Checks `mulToom` on an `m`-limb `a` and an `n`-limb `b`, in both orders. -/
def checkToom (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1)].all fun (x, y) =>
    let s := MPN.mulToom (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    let t := MPN.mulToom (inner r (m + n)) (limbs n y).toUSlice (limbs m x).toUSlice
    window s 1 (m + n) == x * y && window t 1 (m + n) == x * y &&
      s[0]! == pad && s[m + n + 1]! == pad

-- Below the threshold; Toom-3 (`2/3 < n/m`); Toom-3 by 2 (`1/3 < n/m ≤ 2/3`); Toom-4 by 2
-- (`1/4 < n/m ≤ 1/3`, roughly); Karatsuba for the rest; and Toom-3 recursing into itself.
#guard [(128, 128), (300, 200), (385, 385), (500, 400), (900, 450), (700, 400), (1200, 400),
  (1600, 500), (2000, 390), (1200, 1200)].all fun (m, n) => checkToom m n

-- Toom-4 (`3/4 < n/m`), Toom-4 by 3 (`1/2 < n/m ≤ 3/4`, roughly), and Toom-4 recursing into itself.
#guard [(700, 700), (800, 610), (900, 650), (1000, 600), (2400, 2400)].all fun (m, n) => checkToom m
    n

/-! FFT residues -/

/--
Checks the residue operations modulo `F = 2^(64 n) + 1` on three windows of `n + 1` limbs, at
`1`, `n + 2` and `2 n + 3` of an array with a padding limb at each end, holding `x`, `y` and `z`:
the window written has the right value, and the other limbs are unchanged.
-/
def checkFermat (n : Nat) : Bool :=
  let F := 2 ^ (64 * n) + 1
  let pad : UInt64Array := .replicate 1 0xAAAAAAAAAAAAAAAA
  let vals := [0, 1, F - 1, F - 2, 2 ^ (64 * n) - 1, 2 ^ 63, randomLimbs n 3 % F,
    2 ^ (64 * (n - 1))]
  let (oa, ob, oc) := (1, n + 2, 2 * n + 3)
  let others (r arr : UInt64Array) (o : Nat) : Bool :=
    (List.range arr.size).all fun i => i ∈ List.range' o (n + 1) || r[i]! == arr[i]!
  vals.all fun x => vals.all fun y =>
    let arr := pad ++ limbs (n + 1) x ++ limbs (n + 1) y ++ limbs (n + 1) 12345 ++ pad
    let ok : Bool := Id.run do
      if h : MPN.FFT.Win arr n.toUSize oa.toUSize ∧ MPN.FFT.Win arr n.toUSize ob.toUSize ∧
          MPN.FFT.Win arr n.toUSize oc.toUSize then
        let s := MPN.FFT.addModAt arr n.toUSize oa.toUSize oa.toUSize ob.toUSize h.1 h.1 h.2.1
        let d := MPN.FFT.subModAt arr n.toUSize oc.toUSize oa.toUSize ob.toUSize h.2.2 h.1 h.2.1
        let d' := MPN.FFT.subModAt arr n.toUSize oa.toUSize oa.toUSize ob.toUSize h.1 h.1 h.2.1
        let es := [0, 1, 63, 64, 65, 64 * (n - 1), 64 * (n - 1) + 7, 64 * n - 1].filter
          (· < 64 * n)
        let pw := es.all fun e =>
          if he : e.toUSize.toNat < 64 * n.toUSize.toNat then
            let m := MPN.FFT.mulPow2At arr n.toUSize oc.toUSize oa.toUSize e.toUSize h.2.2 h.1 he
            window m oc (n + 1) == x * 2 ^ e % F && others m arr oc
          else false
        return window s oa (n + 1) == (x + y) % F && others s arr oa &&
          window d oc (n + 1) == (x + F - y) % F && others d arr oc &&
          window d' oa (n + 1) == (x + F - y) % F && others d' arr oa && pw
      else return false
    -- Reduction of any `n + 1` limbs.
    let v := x % 2 ^ (64 * n) + 2 ^ (64 * n) * (y % 2 ^ 64)
    let arr' := pad ++ limbs (n + 1) v ++ pad
    let ok' : Bool :=
      if h : MPN.FFT.Win arr' n.toUSize 1 then
        let r := MPN.FFT.normAt arr' n.toUSize 1 h
        window r 1 (n + 1) == v % F && others r arr' 1
      else false
    ok && ok'

#guard [1, 2, 3, 5].all checkFermat


/-! FFT transforms -/

/--
Checks the transforms of length `2ᵐ` modulo `2^(64 n) + 1`, on a block of windows at `1` with
the scratch window after it, against their sums, and that the inverse of the forward transform
is `2ᵐ` times the input.
-/
def checkTransform (n m : Nat) : Bool :=
  let F := 2 ^ (64 * n) + 1
  let K := 2 ^ m
  let σ := 2 * (64 * n) / K
  let xs := (List.range K).map fun i => (randomLimbs n (i + 5) * (i + 1)) % F
  let xs := if K > 2 then xs.set 1 (F - 1) |>.set 2 0 else xs
  let pad : UInt64Array := .replicate 1 0xAAAAAAAAAAAAAAAA
  let arr := xs.foldl (fun a x => a ++ limbs (n + 1) x) pad ++ limbs (n + 1) 77 ++ pad
  let t := 1 + K * (n + 1)
  let co (a : UInt64Array) (p : Nat) := window a (1 + p * (n + 1)) (n + 1)
  let f := MPN.FFT.fwd n t m arr 1 σ
  let g := MPN.FFT.inv n t m f 1 σ
  let fOK := (List.range K).all fun p =>
    co f p == (List.range K).foldl (fun s i => s + xs[i]! * 2 ^ (σ * i * MPN.FFT.rev m p)) 0 % F
  let gOK := (List.range K).all fun l => co g l == K * xs[l]! % F
  fOK && gOK && f[0]! == arr[0]! && f[arr.size - 1]! == arr[arr.size - 1]! &&
    g[0]! == arr[0]! && g.size == arr.size

#guard [(1, 1), (1, 2), (1, 3), (2, 1), (2, 3), (2, 4), (3, 5)].all fun (n, m) => checkTransform n m

/-! FFT multiplication -/

/--
Checks `fftMul` with `2ᵏ` pieces on an `m`-limb `a` and an `n`-limb `b`, in both orders, and that
it takes the FFT path.
-/
def checkFFT (m n k : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  let p := MPN.FFT.fftParams (m + n) k
  decide (MPN.FFT.FFTCheck (inner r (m + n)) (limbs m 1).toUSlice (limbs n 1).toUSlice k p.1 p.2) &&
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1)].all fun (x, y) =>
    let s := MPN.FFT.fftMul (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice k
    let t := MPN.FFT.fftMul (inner r (m + n)) (limbs n y).toUSlice (limbs m x).toUSlice k
    window s 1 (m + n) == x * y && window t 1 (m + n) == x * y &&
      s[0]! == pad && s[m + n + 1]! == pad

#guard [(50, 40, 3), (1, 1, 1), (7, 3, 2), (100, 1, 4), (64, 64, 5), (300, 200, 6), (200, 7, 7),
  (150, 150, 8), (1000, 900, 5)].all fun (m, n, k) => checkFFT m n k

/-- Checks `MPN.mul` on an `m`-limb `a` and an `n`-limb `b`, in both orders. -/
def checkMPNMul (m n : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (m + n + 2) pad
  [(randomLimbs m 1, randomLimbs n 2), (2 ^ (64 * m) - 1, 2 ^ (64 * n) - 1)].all fun (x, y) =>
    let s := MPN.mul (inner r (m + n)) (limbs m x).toUSlice (limbs n y).toUSlice
    let t := MPN.mul (inner r (m + n)) (limbs n y).toUSlice (limbs m x).toUSlice
    window s 1 (m + n) == x * y && window t 1 (m + n) == x * y &&
      s[0]! == pad && s[m + n + 1]! == pad

-- Below and above `fftThreshold`, and an unbalanced pair on each side of `fftMinSmall`.
#guard [(3071, 3071), (3072, 3000), (3072, 1500), (5000, 330), (5000, 300), (4, 3)].all
  fun (m, n) => checkMPNMul m n

/-- Checks `fftSqr` with `2ᵏ` pieces and `MPN.sqr` on an `n`-limb `a`. -/
def checkMPNSqr (n k : Nat) : Bool :=
  let pad : UInt64 := 0xAAAAAAAAAAAAAAAA
  let r := UInt64Array.replicate (2 * n + 2) pad
  let p := MPN.FFT.fftParams (2 * n) k
  decide (MPN.FFT.FFTCheck (inner r (2 * n)) (limbs n 1).toUSlice (limbs n 1).toUSlice k p.1
    p.2) &&
  [randomLimbs n 1, 2 ^ (64 * n) - 1].all fun x =>
    let s := MPN.FFT.fftSqr (inner r (2 * n)) (limbs n x).toUSlice k
    let t := MPN.sqr (inner r (2 * n)) (limbs n x).toUSlice
    window s 1 (2 * n) == x * x && window t 1 (2 * n) == x * x &&
      s[0]! == pad && s[2 * n + 1]! == pad && t[0]! == pad && t[2 * n + 1]! == pad

-- `MPN.sqr` on each side of `sqrFFTThreshold`.
#guard [(1, 1), (7, 2), (100, 4), (300, 6), (2047, 8), (2048, 8), (2500, 8)].all
  fun (n, k) => checkMPNSqr n k
