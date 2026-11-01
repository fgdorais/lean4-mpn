/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPN32
import MPN64

/-!
# Tests of the shared code, on both widths

The checks of `MPN`'s generic kernels, written once over any `WordArray` and run on `UInt32Array`
and `UInt64Array`: addition and subtraction (`addW`, `subW`), the passes of the Toom methods, the
residues modulo `2^(w n) + 1` and the transforms of the FFT. The operations of `GNat` against
`Nat` are checked over any `NatLimbs`, on `MPN.W32.Nat` and `MPN.W64.Nat`. Arrays are built with
`LimbArray.writeNat` and read with `LimbArray.valAt`, so the checks use nothing of a width.
-/

namespace MPNTest.Kernels

open ScalarArray MPN MPN.FFT

/-! ## Values -/

/-- Pseudorandom numbers of `bits` bits from a linear congruential generator. -/
def rnd (bits seed : Nat) : Nat := Id.run do
  let mut s := seed
  let mut v := 0
  for _ in [0:(bits + 31) / 32] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    v := v * 2 ^ 32 + s / 2 ^ 32
  return v % 2 ^ bits

section

variable (A : Type) {L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-- The limb width. -/
abbrev w : Nat := LA.w

/-- A padding limb, `1010…` in binary. -/
def padV : Nat := 2 ^ w A / 3 * 2

/-- `k` padding limbs. -/
def pads (k : Nat) : Nat := padV A * ((2 ^ (w A * k) - 1) / (2 ^ w A - 1))

/-- Edge values of up to `n` limbs, where carries and borrows propagate the most. -/
def edges (n : Nat) : List Nat :=
  [0, 1, 2 ^ (w A - 1), 2 ^ (w A * n) - 1, 2 ^ (w A * n) - 2, 2 ^ (w A * (n - 1)),
    2 ^ (w A * n) / 3]

/-- `n` limbs holding `x` modulo `2^(w n)`. -/
def ofN (n x : Nat) : A := LimbArray.writeNat (R.zeros n) 0 n x

/-- `k` padding limbs, with windows `(o, n, x)` written into them. -/
def buf (k : Nat) (ws : List (Nat × Nat × Nat)) : A :=
  ws.foldl (fun a (o, n, x) => LimbArray.writeNat a o n x)
    (LimbArray.writeNat (R.zeros k) 0 k (pads A k))

/-- The limbs of `r` outside the window `[o, o + n)` are those of `a`. -/
def same (r a : A) (o n : Nat) : Bool :=
  LimbArray.size r == LimbArray.size a &&
    (List.range (LimbArray.size a)).all fun i =>
      (o ≤ i && i < o + n) || LA.val (LA.get r i) == LA.val (LA.get a i)

/-! ## Addition and subtraction -/

/-- `addW` and `subW` on an `m`-limb `a` and an `n`-limb `b`, `n ≤ m`, at limb 1 of a buffer. -/
def checkAddSubW (m n : Nat) : Bool :=
  let r := buf A (m + 3) []
  (edges A m).all fun x => (edges A n).all fun y =>
    let y := y % 2 ^ (w A * n)
    let s := WordArray.addW r 1 (ofN A m x) 0 m (ofN A n y) 0 n
    let d := WordArray.subW r 1 (ofN A m x) 0 m (ofN A n y) 0 n
    LimbArray.valAt s 1 (m + 1) == x + y && same A s r 1 (m + 1) &&
      (x < y || LimbArray.valAt d 1 m == x - y) && same A d r 1 m

/-! ## The passes of the Toom methods -/

/--
`addMulIntoK` and `subMulIntoK` when the result fits, `addIntoK`, `subIntoK`, halving by `shlTopK`,
exact division by 3 and 5, and `shrK`, on `n` limbs.
-/
def checkLinear (n : Nat) : Bool :=
  let N := 2 ^ (w A * n)
  [rnd (w A * n) 3, N - 1, N / 2].all fun x =>
    let y := rnd (w A * (n / 2 + 1)) 5 % N
    let r := ofN A n x
    let sy := ofN A (n / 2 + 1) y
    [1, 3, 16, 81, 2 ^ w A - 1].all fun m =>
      let q := WordArray.addMulIntoK r 0 n sy 0 (n / 2 + 1) m
      let s := WordArray.subMulIntoK r 0 n sy 0 (n / 2 + 1) m
      (N ≤ x + y * m || LimbArray.valAt q 0 n == x + y * m) &&
      (x < y * m || LimbArray.valAt s 0 n == x - y * m)
    && (N ≤ x + y || LimbArray.valAt (WordArray.addIntoK r 0 n sy 0 (n / 2 + 1)) 0 n == x + y)
    && (x < y || LimbArray.valAt (WordArray.subIntoK r 0 n sy 0 (n / 2 + 1)) 0 n == x - y)
  && [rnd (w A * (n - 1)) 9, 2 ^ (w A * (n - 1)) - 1].all fun x =>
    let x2 := 2 * (x / 2)
    let x3 := 3 * (x / 3)
    let x5 := 5 * (x / 5)
    LimbArray.valAt (WordArray.shlTopK (ofN A n x2) 0 n) 1 (n - 1) == x2 / 2 &&
    LimbArray.valAt (WordArray.divExactK (ofN A n x3) 0 n 3) 0 n == x3 / 3 &&
    LimbArray.valAt (WordArray.divExactK (ofN A n x5) 0 n 5) 0 n == x5 / 5 &&
    [1, 2, 7, w A - 1].all fun s =>
      LimbArray.valAt (WordArray.shrK (ofN A n x) 0 n s) 0 n == x / 2 ^ s

/-! ## The residues of the FFT -/

/--
The residue operations modulo `F = 2^(w n) + 1` on three windows of `n + 1` limbs at `1`, `n + 2`
and `2 n + 3` of a padded array, holding `x`, `y` and `12345`: the window written has the right
value and the other limbs are unchanged; and the reduction of any `n + 1` limbs.
-/
def checkFermat (n : Nat) : Bool :=
  let W := w A
  let F := 2 ^ (W * n) + 1
  let vals := [0, 1, F - 1, F - 2, 2 ^ (W * n) - 1, 2 ^ (W - 1), rnd (W * n) 3 % F,
    2 ^ (W * (n - 1))]
  let (oa, ob, oc) := (1, n + 2, 2 * n + 3)
  vals.all fun x => vals.all fun y =>
    let arr := buf A (3 * n + 5) [(oa, n + 1, x), (ob, n + 1, y), (oc, n + 1, 12345)]
    let ok : Bool := Id.run do
      if h : Win arr n.toUSize oa.toUSize ∧ Win arr n.toUSize ob.toUSize ∧
          Win arr n.toUSize oc.toUSize then
        let s := addModAt arr n.toUSize oa.toUSize oa.toUSize ob.toUSize h.1 h.1 h.2.1
        let d := subModAt arr n.toUSize oc.toUSize oa.toUSize ob.toUSize h.2.2 h.1 h.2.1
        let d' := subModAt arr n.toUSize oa.toUSize oa.toUSize ob.toUSize h.1 h.1 h.2.1
        let es := [0, 1, W - 1, W, W + 1, W * (n - 1), W * (n - 1) + 7, W * n - 1].filter
          (· < W * n)
        let pw := es.all fun e =>
          if he : e.toUSize.toNat < LA.w * n.toUSize.toNat then
            let m := mulPow2At arr n.toUSize oc.toUSize oa.toUSize e.toUSize h.2.2 h.1 he
            LimbArray.valAt m oc (n + 1) == x * 2 ^ e % F && same A m arr oc (n + 1)
          else false
        return LimbArray.valAt s oa (n + 1) == (x + y) % F && same A s arr oa (n + 1) &&
          LimbArray.valAt d oc (n + 1) == (x + F - y) % F && same A d arr oc (n + 1) &&
          LimbArray.valAt d' oa (n + 1) == (x + F - y) % F && same A d' arr oa (n + 1) && pw
      else return false
    let v := x % 2 ^ (W * n) + 2 ^ (W * n) * (y % 2 ^ W)
    let arr' := buf A (n + 3) [(1, n + 1, v)]
    let ok' : Bool :=
      if h : Win arr' n.toUSize 1 then
        let r := normAt arr' n.toUSize 1 h
        LimbArray.valAt r 1 (n + 1) == v % F && same A r arr' 1 (n + 1)
      else false
    ok && ok'

/--
The transforms of length `2ᵐ` modulo `2^(w n) + 1` on a block of windows at `1` with the scratch
window after it, against their sums, and the inverse of the forward transform, `2ᵐ` times the
input.
-/
def checkTransform (n m : Nat) : Bool :=
  let W := w A
  let F := 2 ^ (W * n) + 1
  let K := 2 ^ m
  let σ := 2 * (W * n) / K
  let xs := (List.range K).map fun i => (rnd (W * n) (i + 5) * (i + 1)) % F
  let xs := if K > 2 then xs.set 1 (F - 1) |>.set 2 0 else xs
  let t := 1 + K * (n + 1)
  let arr := buf A (t + n + 2)
    ((List.range K).map (fun i => (1 + i * (n + 1), n + 1, xs[i]!)) ++ [(t, n + 1, 77)])
  let co (a : A) (p : Nat) := LimbArray.valAt a (1 + p * (n + 1)) (n + 1)
  let f := WinOps.fwd n t m arr 1 σ
  let g := WinOps.inv n t m f 1 σ
  (List.range K).all (fun p =>
    co f p == (List.range K).foldl (fun s i => s + xs[i]! * 2 ^ (σ * i * rev m p)) 0 % F) &&
  (List.range K).all (fun l => co g l == K * xs[l]! % F) &&
    same A f arr 1 (t + n) && same A g arr 1 (t + n)

end

/-! ## The natural numbers -/

/-- Values at and around the boundaries between words and limbs of both widths. -/
def natValues : List Nat :=
  [0, 1, 2, 7, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 63, 2 ^ 64 - 2, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 96 - 1, 2 ^ 96, 2 ^ 128 - 1, 2 ^ 128, rnd 200 61, rnd 1000 67, 3 ^ 200]

/-- The operations of `GNat A` against `Nat` on `a` and `b`. -/
def checkNat (A : Type) [NatLimbs A] [GcdLimbs A] (a b : Nat) : Bool :=
  let x : GNat A := GNat.ofNat a
  let y : GNat A := GNat.ofNat b
  (x + y).toNat == a + b && (x - y).toNat == a - b && (x * y).toNat == a * b &&
    (x / y).toNat == a / b && (x % y).toNat == a % b &&
    decide (x < y) == decide (a < b) && decide (x ≤ y) == decide (a ≤ b) &&
    decide (x = y) == decide (a = b) && (x == y || hash x != hash y || a != b) &&
    (x.toNat == a && toString x == toString a) &&
    (GNat.gcd x y).toNat == Nat.gcd a b && (GNat.lcm x y).toNat == Nat.lcm a b &&
    (x &&& y).toNat == (a &&& b) && (x ||| y).toNat == (a ||| b) && (x ^^^ y).toNat == (a ^^^ b)

/-! ## Both widths -/

#guard [(1, 0), (1, 1), (3, 1), (3, 2), (4, 4), (5, 0)].all fun (m, n) =>
  checkAddSubW UInt32Array m n && checkAddSubW UInt64Array m n

#guard [2, 3, 5, 16, 33].all fun n => checkLinear UInt32Array n && checkLinear UInt64Array n

#guard [1, 2, 3, 5].all fun n => checkFermat UInt32Array n && checkFermat UInt64Array n

#guard [(1, 1), (1, 2), (1, 3), (2, 1), (2, 3), (2, 4), (3, 5)].all fun (n, m) =>
  checkTransform UInt32Array n m && checkTransform UInt64Array n m

#guard natValues.all fun a => natValues.all fun b =>
  checkNat UInt32Array a b && checkNat UInt64Array a b

end MPNTest.Kernels
