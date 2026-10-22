/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPN
import ScalarArray.UInt32
import ScalarArray.UInt64

/-!
# Benchmarks

Times schoolbook multiplication of two `N`-bit numbers, for each way of computing the
double-width multiply-add, against `Nat` (GMP), and the conversions between `Nat` and limbs.
The Lean variants share one loop shape, explicit tail recursion with unboxed state, so they
differ only in the limb width and the multiply-add implementation.
-/

open ScalarArray

namespace Bench

/-! Implementations of the multiply-add `x * y + a + b` as its low and high words -/

/-- With the high-word operations on `UInt32`. -/
@[inline] def mulAddAdd32 (x y a b : UInt32) : UInt32 × UInt32 :=
  let lo := x * y
  let hi := UInt32.addh (x.mulh y) lo a
  let lo := lo + a
  (lo + b, UInt32.addh hi lo b)

/-- With the high-word operations on `UInt64`, which are C with `__uint128_t`. -/
@[inline] def mulAddAdd64 (x y a b : UInt64) : UInt64 × UInt64 :=
  let lo := x * y
  let hi := UInt64.addh (x.mulh y) lo a
  let lo := lo + a
  (lo + b, UInt64.addh hi lo b)

/-- The pure Lean version, multiplying by 32-bit halves. -/
@[inline] def mulAddAddPure (x y a b : UInt64) : UInt64 × UInt64 :=
  let m : UInt64 := 0xFFFFFFFF
  let x₀ := x &&& m
  let x₁ := x >>> 32
  let y₀ := y &&& m
  let y₁ := y >>> 32
  let p₀₀ := x₀ * y₀
  let p₀₁ := x₀ * y₁
  let p₁₀ := x₁ * y₀
  let p₁₁ := x₁ * y₁
  let mid := (p₀₀ >>> 32) + (p₀₁ &&& m) + (p₁₀ &&& m)
  let lo := (mid <<< 32) ||| (p₀₀ &&& m)
  let hi := p₁₁ + (p₀₁ >>> 32) + (p₁₀ >>> 32) + (mid >>> 32)
  -- Each addition carries out exactly when its sum wraps below an addend.
  let lo₁ := lo + a
  let lo₂ := lo₁ + b
  (lo₂, hi + (decide (lo₁ < a)).toUInt64 + (decide (lo₂ < b)).toUInt64)

/-! Multiplication variants -/

/-- Adds `x * b` into `r` at offset `i`, from limb `j` on, with carry `c`. -/
@[specialize] def row64 (f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 × UInt64)
    (x : UInt64) (b r : UInt64Array) (i j : Nat) (c : UInt64) : UInt64Array :=
  if h : j < b.size then
    let (lo, hi) := f x b[j] r[i + j]! c
    row64 f x b (r.set! (i + j) lo) i (j + 1) hi
  else
    r.set! (i + j) c
termination_by b.size - j

/-- Schoolbook multiplication on `UInt64` limbs with the given multiply-add, from row `i` on. -/
@[specialize] def mul64With (f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 × UInt64)
    (a b r : UInt64Array) (i : Nat) : UInt64Array :=
  if h : i < a.size then mul64With f a b (row64 f a[i] b r i 0 0) (i + 1) else r
termination_by a.size - i

/-- Adds `x * b` into `r` at offset `i`, from limb `j` on, with carry `c`. -/
def row32 (x : UInt32) (b r : UInt32Array) (i j : Nat) (c : UInt32) : UInt32Array :=
  if h : j < b.size then
    let (lo, hi) := mulAddAdd32 x b[j] r[i + j]! c
    row32 x b (r.set! (i + j) lo) i (j + 1) hi
  else
    r.set! (i + j) c
termination_by b.size - j

/-- Schoolbook multiplication on `UInt32` limbs with `mulAddAdd32`, from row `i` on. -/
def mul32Loop (a b r : UInt32Array) (i : Nat) : UInt32Array :=
  if h : i < a.size then mul32Loop a b (row32 a[i] b r i 0 0) (i + 1) else r
termination_by a.size - i

def mul32 (a b : UInt32Array) : UInt32Array :=
  mul32Loop a b (.replicate (a.size + b.size) 0) 0

def mul64Pure (a b : UInt64Array) : UInt64Array :=
  mul64With mulAddAddPure a b (.replicate (a.size + b.size) 0) 0
def mul64Extern (a b : UInt64Array) : UInt64Array :=
  mul64With mulAddAdd64 a b (.replicate (a.size + b.size) 0) 0

/-! Conversions -/

def ofNat64 (n : Nat) : UInt64Array := loop n .empty
where
  loop (n : Nat) (acc : UInt64Array) : UInt64Array :=
    if h : n = 0 then acc else loop (n / 2 ^ 64) (acc.push n.toUInt64)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def toNat64 (a : UInt64Array) : Nat := a.foldr (fun d n => n * 2 ^ 64 + d.toNat) 0

def ofNat32 (n : Nat) : UInt32Array := loop n .empty
where
  loop (n : Nat) (acc : UInt32Array) : UInt32Array :=
    if h : n = 0 then acc else loop (n / 2 ^ 32) (acc.push n.toUInt32)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def toNat32 (a : UInt32Array) : Nat := a.foldr (fun d n => n * 2 ^ 32 + d.toNat) 0

/-! Harness -/

/-- An `N`-bit number with pseudorandom bits and the top bit set. -/
def sample (bits seed : Nat) : Nat := Id.run do
  let mut s := seed
  let mut n := 0
  for _ in [0:(bits + 31) / 32] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    n := n * 2 ^ 32 + s / 2 ^ 32
  return n % 2 ^ bits ||| 2 ^ (bits - 1)

/-- A variant runs `reps` multiplications and returns a checksum so they cannot be skipped. -/
structure Variant where
  name : String
  prepare : Nat → Nat → (Nat → UInt64) × (Unit → Nat)

/-- Runs `mul` on fixed inputs `reps` times, folding each result's top limb into a checksum. -/
@[noinline] def repeatMul {α : Type} (mul : α → α → α) (top : α → UInt64) (a b : α) (reps : Nat) :
    UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for _ in [0:reps] do
    acc := acc + top (mul a b)
  return acc

def variants : List Variant :=
  let v64 (name : String) (mul : UInt64Array → UInt64Array → UInt64Array) : Variant :=
    ⟨name, fun m n =>
      let a := ofNat64 m
      let b := ofNat64 n
      (repeatMul mul (fun r => r[r.size - 1]!) a b, fun _ => toNat64 (mul a b))⟩
  let v32 (name : String) (mul : UInt32Array → UInt32Array → UInt32Array) : Variant :=
    ⟨name, fun m n =>
      let a := ofNat32 m
      let b := ofNat32 n
      (repeatMul mul (fun r => r[r.size - 1]!.toUInt64) a b, fun _ => toNat32 (mul a b))⟩
  [ v32 "mul32" mul32,
    v64 "mul64 pure Lean" mul64Pure,
    v64 "mul64 mulh/addh" mul64Extern,
    ⟨"Nat (GMP)", fun m n =>
      (repeatMul (· * ·) (fun r => r.toUInt64) m n, fun _ => m * n)⟩ ]

/-- Runs `f` on a fixed input `reps` times, folding a summary of each result into a checksum. -/
@[noinline] def repeatFn {α β : Type} (f : α → β) (summary : β → UInt64) (a : α) (reps : Nat) :
    UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for _ in [0:reps] do
    acc := acc + summary (f a)
  return acc

/-- A conversion benchmark: given `n`, the timed loop and a correctness check. -/
structure Conversion where
  name : String
  prepare : Nat → (Nat → UInt64) × (Unit → Bool)

def conversions : List Conversion :=
  let toLimbs (name : String) (f : Nat → UInt64Array) : Conversion :=
    ⟨name, fun n =>
      (repeatFn f (fun r => r.size.toUInt64 + r[0]!) n, fun _ => (f n).toList == (ofNat64 n).toList)⟩
  let ofLimbs (name : String) (f : UInt64Array → Nat) : Conversion :=
    ⟨name, fun n =>
      let a := ofNat64 n
      (repeatFn f (·.toUInt64) a, fun _ => f a == n && f (a.push 0 |>.push 0) == n)⟩
  let toLimbs32 (name : String) (f : Nat → UInt32Array) : Conversion :=
    ⟨name, fun n =>
      (repeatFn f (fun r => r.size.toUInt64 + (r[0]!).toUInt64) n, fun _ => toNat32 (f n) == n)⟩
  let ofLimbs32 (name : String) (f : UInt32Array → Nat) : Conversion :=
    ⟨name, fun n =>
      let a := ofNat32 n
      (repeatFn f (·.toUInt64) a, fun _ => f a == n && f (a.push 0 |>.push 0) == n)⟩
  [ toLimbs "Nat → 64-bit limbs" ofNat64,
    toLimbs32 "Nat → 32-bit limbs" ofNat32,
    ofLimbs "64-bit limbs → Nat" toNat64,
    ofLimbs32 "32-bit limbs → Nat" toNat32 ]

def median (xs : Array Nat) : Nat := (xs.qsort (· < ·))[xs.size / 2]!

/-- Median nanoseconds per multiplication over `trials` trials of at least `minNs` each. -/
def time (run : Nat → UInt64) (trials := 11) (minNs := 20_000_000) : IO Nat := do
  -- Calibrates the repetition count by doubling.
  let mut reps := 1
  repeat
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => run reps
    let t₁ ← IO.monoNanosNow
    if t₁ - t₀ ≥ minNs / 4 then break
    reps := reps * 2
  reps := reps * 4
  let mut samples := #[]
  let mut sink : UInt64 := 0
  for _ in [0:trials] do
    let t₀ ← IO.monoNanosNow
    let s ← IO.lazyPure fun _ => run reps
    let t₁ ← IO.monoNanosNow
    sink := sink + s
    samples := samples.push ((t₁ - t₀) * 1000 / reps)
  if sink == 0xDEADBEEF then IO.println "" -- Keeps `sink` alive.
  return median samples

def fmt (picos : Nat) : String :=
  let ns := picos / 1000
  let frac := toString (picos % 1000 / 10)
  s!"{ns}.{"".pushn '0' (2 - frac.length)}{frac}"

def padL (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s
def padR (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

end Bench

open Bench in
def benchMul (sizes : List Nat) : IO UInt32 := do
  -- Checks every variant against `Nat` before timing.
  for bits in sizes do
    let m := sample bits 1
    let n := sample bits 2
    for v in variants do
      if (v.prepare m n).2 () != m * n then
        IO.eprintln s!"{v.name} is wrong at {bits} bits"
        return 1
  IO.println "Median time per N×N-bit product, ns (in parentheses: ns per 64×64-bit limb product)"
  IO.println ""
  IO.print (padR "variant" 20)
  for bits in sizes do IO.print (padL s!"{bits}" 22)
  IO.println ""
  for v in variants do
    IO.print (padR v.name 20)
    for bits in sizes do
      let m := sample bits 1
      let n := sample bits 2
      let ps ← time (v.prepare m n).1
      let limbs := (bits + 63) / 64
      IO.print (padL s!"{fmt ps} ({fmt (ps / (limbs * limbs))})" 22)
      (← IO.getStdout).flush
    IO.println ""
  return 0

open Bench in
def benchConv (sizes : List Nat) : IO UInt32 := do
  -- Checks every conversion, including zero and the scalar boundary, before timing.
  for bits in [0, 1, 62, 63, 64, 65] ++ sizes do
    let ns := if bits = 0 then [0] else [sample bits 1, 2 ^ bits - 1, 2 ^ (bits - 1)]
    for n in ns do
      for c in conversions do
        unless (c.prepare n).2 () do
          IO.eprintln s!"{c.name} is wrong at {n}"
          return 1
  IO.println "Median time per conversion of an N-bit number, ns"
  IO.println ""
  IO.print (padR "variant" 30)
  for bits in sizes do IO.print (padL s!"{bits}" 12)
  IO.println ""
  for c in conversions do
    IO.print (padR c.name 30)
    for bits in sizes do
      let ps ← time (c.prepare (sample bits 1)).1
      IO.print (padL (fmt ps) 12)
      (← IO.getStdout).flush
    IO.println ""
  return 0

/-- `bench [mul|conv] [sizes…]` runs the multiplication or the conversion benchmarks. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "conv" :: sizes =>
    benchConv (if sizes.isEmpty then [63, 64, 128, 256, 1024, 4096, 16384, 65536]
      else sizes.map String.toNat!)
  | "mul" :: sizes => benchMul (if sizes.isEmpty then defaultMulSizes else sizes.map String.toNat!)
  | sizes => benchMul (if sizes.isEmpty then defaultMulSizes else sizes.map String.toNat!)
where
  defaultMulSizes := [128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
