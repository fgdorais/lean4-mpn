/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN64
import Bench.Harness

/-!
# Benchmark

`lake exe bench` times each operation of the library against the same operation on `Nat`, which
Lean implements with GMP, on pseudorandom operands of 64-bit limbs. Pinning it to one core, for
example with `taskset -c 2`, gives steadier results.

Each time is the median of five trials. The two columns after the ratio are the spread of the
trials of each side, their sample standard deviation relative to their mean, which tells how far
to trust a difference between two runs. A row with a GMP kernel for its operation then has the
time of that `mpn_*` function on the same limbs, without allocating its result (`Bench.Mpn`), the
ratio to it and its spread.

`bench [--no-nat] [op…] [size…]` selects the operations and the sizes, in limbs; `--no-nat` skips
`Nat`, for a profiler.
-/

open ScalarArray

namespace Bench

/-! ## Reference loop -/

/--
Adds `x * b` into `r` at offset `i`, from limb `j` on, with carry `c`: a hand-written loop with
the same arithmetic as `MPN.addMul1`, the target for the library's loops.
-/
def refRow (x : UInt64) (b r : UInt64Array) (i j : Nat) (c : UInt64) : UInt64Array :=
  if h : j < b.size then
    let y := b[j]
    let lo := x * y
    let hi := UInt64.addh (x.mulh y) lo r[i + j]!
    let lo := lo + r[i + j]!
    refRow x b (r.set! (i + j) (lo + c)) i (j + 1) (UInt64.addh hi lo c)
  else
    r.set! (i + j) c

/-- Schoolbook multiplication with `refRow`, from row `i` on. -/
def refMulLoop (a b r : UInt64Array) (i : Nat) : UInt64Array :=
  if h : i < a.size then refMulLoop a b (refRow a[i] b r i 0 0) (i + 1) else r

/-- Schoolbook multiplication with `refRow`. -/
def refMul (a b : UInt64Array) : UInt64Array :=
  refMulLoop a b (.replicate (a.size + b.size) 0) 0

/-! ## Harness -/

/-- `n` pseudorandom limbs, with a nonzero top limb. -/
def sample (n seed : Nat) : UInt64Array := Id.run do
  let mut s := seed
  let mut r := UInt64Array.emptyWithCapacity n
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    r := r.push s.toUInt64
  if n > 0 then r := r.set! (n - 1) (r[n - 1]! ||| 1)
  return r

/-- O(1), like `checkNat`: hashing the result would add a pass over its limbs to the time. -/
def checkArr (r : UInt64Array) : UInt64 := r.size.toUInt64 + r[0]!
def checkPair (p : UInt64Array × UInt64) : UInt64 := checkArr p.1 + p.2
def checkBig : MPN.W64.Nat → UInt64
  | .small w => w
  | .large a _ => a.size.toUInt64 + a[0]!

def sizes : List Nat := [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 512]

/-- `n` zero limbs, as a slice: the result buffer of an operation. -/
def zr (n : Nat) : UInt64Array.USlice := (UInt64Array.replicate n 0).toUSlice

/-- The value of an array of limbs. -/
def toNat (a : UInt64Array) : Nat := a.foldr (fun d n => n * 2 ^ 64 + d.toNat) 0

/-- The width's operations, then those of `bigRow`. -/
def ops : List String :=
  ["add", "sub", "shl", "shr", "div1", "div1u", "sbdiv", "div", "divmod", "sqrt", "mulmod", "gcd",
    "str", "parse",
    "mul1", "addmul1", "mul", "sqr", "kara", "toom", "kara2", "toom2", "fft", "fft2",
    "auto", "ksqr", "fftsqr", "toomsqr", "autosqr", "mulref"] ++ bigOps

/-- The operations of `MPN.W64.Nat` that `bigRow` times. -/
def big : BigOps MPN.W64.Nat where
  ofNat := MPN.W64.Nat.ofNat
  toNat := (·.toNat)
  check := checkBig
  sqr := MPN.W64.Nat.sqr
  sqrt := MPN.W64.Nat.sqrt
  gcd := MPN.W64.Nat.gcd
  lcm := MPN.W64.Nat.lcm
  log2 := (·.log2)
  ofString? := MPN.W64.Nat.ofString?

/-- The row of `op` at `n` limbs, or `false` when it is not an operation. -/
def run (noNat : Bool) (op : String) (n : Nat) : IO Bool := do
  let a := sample n 1
  let b := sample n 2
  -- The operands of the `MPN.Nat` rows come from these, with or without `--no-nat`.
  let (na, nb) := (toNat a, toNat b)
  let s := sample (n + 1) 3
  let ns := toNat s
  if ← bigRow big noNat op n na nb (toNat (sample (2 * n) 4)) ns then return true
  match op with
  | "add" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.WordArray.addW (UInt64Array.replicate (x.size + 1) 0) 0 x 0 x.size y 0 y.size)
        checkArr a b)
      (time (· + ·) checkNat na nb)
      (some (time Mpn.add id a b))
  | "sub" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.WordArray.subW (UInt64Array.replicate x.size 0) 0 x 0 x.size y 0 y.size)
        checkArr s b)
      (time (· - ·) checkNat ns nb)
      (some (time Mpn.sub id s b))
  | "shl" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) => MPN.W64.Num.shl x 13) checkArr a a)
      (time (fun x _ => x <<< 13) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.lshift x 13) id a a))
  | "shr" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) => MPN.W64.Num.shr x 13) checkArr a a)
      (time (fun x _ => x >>> 13) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.rshift x 13) id a a))
  | "div1" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.divRem1 (zr x.size) x.toUSlice 0xF123456789ABCDEF)
        checkPair a a)
      (time (fun x _ => x / 0xF123456789ABCDEF) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.divRem1 x 0xF123456789ABCDEF) id a a))
  | "div1u" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.divRem1 (zr x.size) x.toUSlice 0x0123456789ABCDEF)
        checkPair a a)
      (time (fun x _ => x / 0x0123456789ABCDEF) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.divRem1 x 0x0123456789ABCDEF) id a a))
  | "div" =>
    -- `2 n` by `n` limbs, the quotient only.
    let a2 := sample (2 * n) 4
    row noNat op n
      (time (fun (x y : UInt64Array) => MPN.W64.Num.div x y) checkArr a2 b)
      (time (· / ·) checkNat (toNat a2) nb)
      (some (time Mpn.tdivQR id a2 b))
  | "divmod" =>
    -- `2 n` by `n` limbs, both results; `Nat` computes the quotient only.
    let a2 := sample (2 * n) 4
    row noNat op n
      (time (fun (x y : UInt64Array) => MPN.W64.Num.divMod x y)
        (fun p => checkArr p.1 + checkArr p.2) a2 b)
      (time (· / ·) checkNat (toNat a2) nb)
      (some (time Mpn.tdivQR id a2 b))
  | "sbdiv" =>
    let a2 := sample (2 * n) 4
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.divRem x.toUSlice y.toUSlice)
        (fun p => checkArr p.1 + checkArr p.2) a2 b)
      (time (· / ·) checkNat (toNat a2) nb)
      (some (time Mpn.tdivQR id a2 b))
  | "gcd" =>
    row noNat op n
      (time (fun (x y : UInt64Array) => MPN.W64.Num.gcd x y) checkArr a b)
      (time Nat.gcd checkNat na nb)
      (some (time Mpn.gcd id a b))
  | "str" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) => MPN.W64.Num.toDecimal x) (fun s => s.length.toUInt64) a a)
      (time (fun x _ => Nat.repr x) (fun s => s.length.toUInt64) na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.getStr x) id a a))
  | "parse" =>
    let str := MPN.W64.Num.toDecimal a
    row noNat op n
      (time (fun (s _ : String) => MPN.W64.Num.ofDecimal? s)
        (fun o => (o.map checkArr).getD (0 : UInt64)) str str)
      (time (fun (s _ : String) => s.toNat?)
        (fun o => (o.map checkNat).getD (0 : UInt64)) str str)
        (some (time (fun (s _ : String) => Mpn.setStr s) id str str))
  | "mulmod" =>
    -- `n` by `n` limbs modulo `β^n - 1`, with `2ᵏ` pieces, `k = fftK n`; `Nat` multiplies.
    let k := MPN.W64.FFT.fftK n
    row noNat op n
      (time (fun (x y : UInt64Array) => MPN.W64.Num.mulModB x y k (n / 2 ^ k)) checkArr a b)
      (time (· * ·) checkNat na nb)
      (some (time Mpn.mul id a b))
  | "sqrt" =>
    -- `Nat.sqrt` is Lean's Newton iteration on `Nat`, not GMP's `mpz_sqrt`.
    row noNat op n
      (time (fun (x _ : UInt64Array) => MPN.W64.sqrtRem x) (fun p => checkArr p.1 + checkArr p.2)
        a a)
      (time (fun x _ => x.sqrt) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.sqrtRem x true) id a a))
  | "mul1" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.mul1 (zr x.size) x.toUSlice 7) checkPair a a)
      (time (fun x _ => x * 7) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.mul1 x 7) id a a))
  | "addmul1" =>
    -- `b` is shared, so `addMul1` first copies it, as `Nat` allocates its result.
    row noNat op n
      (time (fun (x y : UInt64Array) => MPN.W64.addMul1 y.toUSlice x.toUSlice 7) checkPair a b)
      (time (fun x y => y + x * 7) checkNat na nb)
      (some (time (fun x (_ : UInt64Array) => Mpn.addMul1 x 7) id a b))
  | "mul" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.mulBasecase (zr (x.size + y.size)) x.toUSlice
          y.toUSlice) checkArr a b)
      (time (· * ·) checkNat na nb)
      (some (time Mpn.mul id a b))
  | "kara" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.mulKaratsuba MPN.W64.config (zr (x.size + y.size)) x.toUSlice
          y.toUSlice) checkArr a b)
      (time (· * ·) checkNat na nb)
      (some (time Mpn.mul id a b))
  | "sqr" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.sqrBasecase (zr (2 * x.size)) x.toUSlice)
        checkArr a a)
      (time (fun x _ => x * x) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.sqr x) id a a))
  | "ksqr" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.sqrKaratsuba MPN.W64.config (zr (2 * x.size)) x.toUSlice)
        checkArr a a)
      (time (fun x _ => x * x) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.sqr x) id a a))
  | "toom" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.mulToom MPN.W64.config (zr (x.size + y.size)) x.toUSlice
          y.toUSlice) checkArr a b)
      (time (· * ·) checkNat na nb)
      (some (time Mpn.mul id a b))
  | "kara2" =>
    -- `n` by `n / 2` limbs.
    let h := sample (n / 2) 2
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.mulKaratsuba MPN.W64.config (zr (x.size + y.size)) x.toUSlice
          y.toUSlice) checkArr a h)
      (time (· * ·) checkNat na (toNat h))
      (some (timeMpnA Mpn.mul a h))
  | "toom2" =>
    let h := sample (n / 2) 2
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.mulToom MPN.W64.config (zr (x.size + y.size)) x.toUSlice
          y.toUSlice) checkArr a h)
      (time (· * ·) checkNat na (toNat h))
      (some (timeMpnA Mpn.mul a h))
  | "fft" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.FFT.fftMul MPN.W64.config (zr (x.size + y.size)) x.toUSlice
          y.toUSlice (MPN.W64.FFT.fftK (x.size + y.size))) checkArr a b)
      (time (· * ·) checkNat na nb)
      (some (time Mpn.mul id a b))
  | "fftsqr" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.FFT.fftSqr MPN.W64.config (zr (2 * x.size)) x.toUSlice
          (MPN.W64.FFT.fftK (2 * x.size))) checkArr a a)
      (time (fun x _ => x * x) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.sqr x) id a a))
  | "toomsqr" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.sqrToom MPN.W64.config (zr (2 * x.size)) x.toUSlice)
        checkArr a a)
      (time (fun x _ => x * x) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.sqr x) id a a))
  | "autosqr" =>
    row noNat op n
      (time (fun (x _ : UInt64Array) =>
        MPN.W64.sqr MPN.W64.config (zr (2 * x.size)) x.toUSlice) checkArr a a)
      (time (fun x _ => x * x) checkNat na na)
      (some (time (fun x (_ : UInt64Array) => Mpn.sqr x) id a a))
  | "auto" =>
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.mul MPN.W64.config (zr (x.size + y.size)) x.toUSlice y.toUSlice)
        checkArr a b)
      (time (· * ·) checkNat na nb)
      (some (time Mpn.mul id a b))
  | "fft2" =>
    let h := sample (n / 2) 2
    row noNat op n
      (time (fun (x y : UInt64Array) =>
        MPN.W64.FFT.fftMul MPN.W64.config (zr (x.size + y.size)) x.toUSlice
          y.toUSlice (MPN.W64.FFT.fftK (x.size + y.size))) checkArr a h)
      (time (· * ·) checkNat na (toNat h))
      (some (timeMpnA Mpn.mul a h))
  | "mulref" =>
    row noNat op n (time refMul checkArr a b) (time (· * ·) checkNat na nb)
  | _ =>
    -- `fftb<s>`, `toomb<s>`: `n` by `s` limbs, for tuning `mulFFTMin`.
    -- `auto2`, `auto4`, `auto8`: `MPN.mul` on `n` by `n / d` limbs; `autobS`: on `n` by `S`.
    let sh : Option Nat := if op == "auto2" then some (n / 2) else if op == "auto4" then
      some (n / 4) else if op == "auto8" then some (n / 8) else if op.startsWith "autob" then
      (op.drop 5).toString.toNat? else none
    if let some sz := sh then
      let h := sample sz 2
      row noNat op n
        (time (fun (x y : UInt64Array) =>
          MPN.W64.mul MPN.W64.config (zr (x.size + y.size)) x.toUSlice y.toUSlice)
          checkArr a h)
        (time (· * ·) checkNat na (toNat h))
        (some (timeMpnA Mpn.mul a h))
    else
    if op.startsWith "gcdh" then
      -- `gcdh<T>`: `gcd` with half-gcd from `T` limbs, for tuning `gcdHalf`.
      let T := (op.drop 4).toString.toNat!
      row noNat op n
        (time (fun (x y : UInt64Array) => MPN.W64.gcdWith T x y) checkArr a b)
        (time Nat.gcd checkNat na nb)
        (some (time Mpn.gcd id a b))
    else
    if op.startsWith "fsq" then
      let k := (op.drop 3).toString.toNat!
      row noNat op n
        (time (fun (x _ : UInt64Array) =>
          MPN.W64.FFT.fftSqr MPN.W64.config (zr (2 * x.size)) x.toUSlice k)
          checkArr a a)
        (time (fun x _ => x * x) checkNat na na)
        (some (time (fun x (_ : UInt64Array) => Mpn.sqr x) id a a))
    else
    let sb := if op.startsWith "fftb" then (op.drop 4).toString.toNat?
      else if op.startsWith "toomb" then (op.drop 5).toString.toNat? else none
    if let some sz := sb then
      let h := sample sz 2
      row noNat op n
        (time (fun (x y : UInt64Array) =>
          if op.startsWith "fftb" then
            MPN.W64.FFT.fftMul MPN.W64.config (zr (x.size + y.size)) x.toUSlice
              y.toUSlice (MPN.W64.FFT.fftK (x.size + y.size))
          else
            MPN.W64.mulToom MPN.W64.config (zr (x.size + y.size)) x.toUSlice
              y.toUSlice) checkArr a h)
        (time (· * ·) checkNat na (toNat h))
        (some (timeMpnA Mpn.mul a h))
    else
    -- `fft<k>`: the FFT with `2ᵏ` pieces, for tuning `fftK`.
    match (op.drop 3).toString.toNat? with
    | some k =>
      if op.startsWith "fft" then
        row noNat op n
          (time (fun (x y : UInt64Array) =>
            MPN.W64.FFT.fftMul MPN.W64.config (zr (x.size + y.size)) x.toUSlice
              y.toUSlice k) checkArr a b)
          (time (· * ·) checkNat na nb)
          (some (time Mpn.mul id a b))
      else throw <| .userError s!"unknown operation {op}"
    | none => throw <| .userError s!"unknown operation {op}"
  return true

/-- `bench64 [--no-nat] [op…] [size…]`. -/
def main (args : List String) : IO Unit := runMain args ops sizes run

end Bench

public def main (args : List String) : IO Unit := Bench.main args
