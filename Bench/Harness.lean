/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tune.Harness

/-!
# The benches' harness

What both widths' benches share: the timing of an operation, the rows of the table, the command
line, and the rows of the natural numbers of a width against `Nat` (`bigRow`), whose operations are
the same on both widths. Each time is the median of five trials; the last two columns of a row are
the spread of the trials of each side, their sample standard deviation relative to their mean,
which tells how far to trust a difference between two runs.
-/

namespace Bench

/-- The median time in nanoseconds of a set of trials, and the trials. -/
public structure Timing where
  median : Float
  /-- The times of the trials. -/
  samples : Array Float

/-- The sample standard deviation of the trials relative to their mean. -/
public def Timing.spread (t : Timing) : Float :=
  let n := t.samples.size.toFloat
  let mean := t.samples.foldl (· + ·) 0 / n
  let var := t.samples.foldl (fun s x => s + (x - mean) ^ 2) 0 / (n - 1)
  if mean > 0 ∧ 1 < n then var.sqrt / mean else 0

/-- The time of `f a b` in nanoseconds, over trials of at least `minNs` each. -/
public def time {α β γ : Type} [Add γ] [OfNat γ 0] (f : α → α → β) (check : β → γ) (a b : α)
    (trials := 5) (minNs := 2_000_000) : IO Timing := do
  let mut reps := 1
  repeat
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => Tune.repeatOp f check a b reps
    let t₁ ← IO.monoNanosNow
    if t₁ - t₀ ≥ minNs then break
    reps := reps * 2
  let mut samples := #[]
  for _ in [0:trials] do
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => Tune.repeatOp f check a b reps
    let t₁ ← IO.monoNanosNow
    samples := samples.push ((t₁ - t₀).toFloat / reps.toFloat)
  return { median := (samples.qsort (· < ·))[trials / 2]!, samples }

/-- O(1), like the checks of results of the library: hashing would add a pass over the limbs. -/
public def checkNat (n : Nat) : UInt64 := n.toUInt64
public def checkStr (s : String) : UInt64 := s.utf8ByteSize.toUInt64
public def checkBool (b : Bool) : UInt64 := if b then 1 else 0

/-- `s` with `w` characters, padded on the left. -/
public def pad (w : Nat) (s : String) : String := "".pushn ' ' (w - s.length) ++ s

/-- `t` nanoseconds with three significant digits, in ns, µs or ms. -/
public def fmt (t : Float) : String :=
  let (v, unit) := if t < 1e3 then (t, "ns") else if t < 1e6 then (t / 1e3, "µs")
    else (t / 1e6, "ms")
  let digits := if v < 10 then 2 else if v < 100 then 1 else 0
  let scale := (10 : Float) ^ digits.toFloat
  let n := (v * scale).round.toUInt64.toNat
  let int := toString (n / 10 ^ digits)
  let frac := toString (n % 10 ^ digits)
  let s := if digits = 0 then int else int ++ "." ++ "".pushn '0' (digits - frac.length) ++ frac
  s ++ " " ++ unit

/-- A spread as a percentage with one decimal, `±1.2%`. -/
public def fmtSpread (x : Float) : String :=
  let n := (x * 1000).round.toUInt64.toNat
  "±" ++ toString (n / 10) ++ "." ++ toString (n % 10) ++ "%"

/-- A ratio with two decimals. -/
public def fmtRatio (x : Float) : String :=
  let n := (x * 100).round.toUInt64.toNat
  let frac := toString (n % 100)
  toString (n / 100) ++ "." ++ "".pushn '0' (2 - frac.length) ++ frac

/--
Times one operation at one size against `Nat`, unless `noNat`, and prints a row: the two median
times, their ratio and the spreads of their trials.
-/
public def row (noNat : Bool) (name : String) (n : Nat) (mpn : IO Timing) (nat : IO Timing) :
    IO Unit := do
  let tm ← mpn
  if noNat then
    IO.println <| s!"{pad 7 name} {pad 6 (toString n)} {pad 10 (fmt tm.median)} " ++
      s!"{pad 8 (fmtSpread tm.spread)}"
  else
    let tn ← nat
    IO.println <|
      s!"{pad 7 name} {pad 6 (toString n)} {pad 10 (fmt tm.median)} {pad 10 (fmt tn.median)} " ++
        s!"{pad 8 (fmtRatio (tm.median / tn.median))} {pad 8 (fmtSpread tm.spread)} " ++
        s!"{pad 8 (fmtSpread tn.spread)}"

/-- The operations of a width's natural numbers that `bigRow` times, beyond their instances. -/
public structure BigOps (N : Type) where
  ofNat : Nat → N
  toNat : N → Nat
  /-- A constant-time check of a result. -/
  check : N → UInt64
  sqr : N → N
  sqrt : N → N
  gcd : N → N → N
  lcm : N → N → N
  log2 : N → Nat
  ofString? : String → Option N

/--
The row of `op`, an operation of the natural numbers `N` of a width against `Nat`, on numbers `na`
and `nb` of `n` limbs, `na2` of `2 n` and `ns > nb`; `false` when `op` is not one of them.
-/
public def bigRow {N : Type} [Add N] [Sub N] [Mul N] [Div N] [Mod N] [AndOp N] [OrOp N] [XorOp N]
    [HShiftLeft N Nat N] [HShiftRight N Nat N] [HPow N Nat N] [LT N]
    [DecidableRel (α := N) (· < ·)] [DecidableEq N] [Hashable N] [ToString N] (B : BigOps N)
    (noNat : Bool) (op : String) (n na nb na2 ns : Nat) : IO Bool := do
  let c := B.check
  let two (f : N → N → N) (g : Nat → Nat → Nat) (x y : Nat) :=
    row noNat op n (time f c (B.ofNat x) (B.ofNat y)) (time g checkNat x y)
  let one {β : Type} (f : N → β) (cf : β → UInt64) (g : Nat → Nat) (x : Nat) :=
    row noNat op n (time (fun a (_ : N) => f a) cf (B.ofNat x) (B.ofNat x))
      (time (fun a (_ : Nat) => g a) checkNat x x)
  match op with
  | "badd" => two (· + ·) (· + ·) na nb
  | "bsub" => two (· - ·) (· - ·) ns nb
  | "bmul" => two (· * ·) (· * ·) na nb
  | "bdiv" => two (· / ·) (· / ·) na2 nb  -- `2 n` by `n` limbs.
  | "bmod" => two (· % ·) (· % ·) na2 nb
  -- `n` limbs by `10⁹ + 7`, a word below `2³²`: one limb on both widths, unnormalized.
  | "bdiv1" => two (· / ·) (· / ·) na 1000000007
  | "bmod1" => two (· % ·) (· % ·) na 1000000007
  | "band" => two (· &&& ·) (· &&& ·) na nb
  | "bor" => two (· ||| ·) (· ||| ·) na nb
  | "bxor" => two (· ^^^ ·) (· ^^^ ·) na nb
  | "bgcd" => two B.gcd Nat.gcd na nb
  | "blcm" => two B.lcm Nat.lcm na nb
  | "bsqr" => one B.sqr c (fun x => x * x) na
  | "bpow" => one (· ^ (3 : Nat)) c (· ^ 3) na
  | "bshl" => one (· <<< (37 : Nat)) c (· <<< 37) na
  | "bshr" => one (· >>> (37 : Nat)) c (· >>> 37) na
  | "bsqrt" => one B.sqrt c Nat.sqrt na2
  | "blog2" => one B.log2 checkNat Nat.log2 na
  -- `Nat` has nothing to convert: its column is one linear pass, `x + 1`.
  | "btonat" => one B.toNat checkNat (· + 1) na
  | "bofnat" =>
    row noNat op n (time (fun x (_ : Nat) => B.ofNat x) c na na)
      (time (fun x (_ : Nat) => x + 1) checkNat na na)
  | "bcmp" =>
    -- `x < x + 1`, which differ in the lowest limb, so both compare every limb.
    row noNat op n (time (fun x y : N => decide (x < y)) checkBool (B.ofNat na) (B.ofNat (na + 1)))
      (time (fun x y : Nat => decide (x < y)) checkBool na (na + 1))
  | "beq" =>
    -- Two copies of the same number, so both compare every limb; the second from another
    -- expression, which the compiler does not share with the first.
    let nc := 2 * na / 2
    row noNat op n (time (fun x y : N => decide (x = y)) checkBool (B.ofNat na) (B.ofNat nc))
      (time (fun x y : Nat => decide (x = y)) checkBool na nc)
  | "bhash" =>
    row noNat op n (time (fun (x _ : N) => hash x) id (B.ofNat na) (B.ofNat na))
      (time (fun (x _ : Nat) => hash x) id na na)
  | "btostr" =>
    row noNat op n (time (fun (x _ : N) => toString x) checkStr (B.ofNat na) (B.ofNat na))
      (time (fun (x _ : Nat) => toString x) checkStr na na)
  | "bofstr" =>
    let t := toString na
    row noNat op n (time (fun t (_ : String) => B.ofString? t) (fun r => (r.map c).getD 0) t t)
      (time (fun t (_ : String) => t.toNat?) (fun r => (r.map checkNat).getD 0) t t)
  | _ => return false
  return true

/-- The operations of `bigRow`. -/
public def bigOps : List String :=
  ["badd", "bsub", "bmul", "bdiv", "bmod", "bdiv1", "bmod1", "band", "bor", "bxor", "bgcd",
    "blcm", "bsqr", "bpow", "bshl", "bshr", "bsqrt", "blog2", "btonat", "bofnat", "bcmp", "beq",
    "bhash", "btostr", "bofstr"]

/--
The command line `[--no-nat] [op…] [size…]`, with the operations and sizes given or else the
defaults; `--no-nat` skips `Nat`, for a profiler. Prints the header and runs `run noNat op n` for
each operation and size, an error for an operation it does not know.
-/
public def runMain (args : List String) (ops : List String) (sizes : List Nat)
    (run : Bool → String → Nat → IO Bool) : IO Unit := do
  let noNat := args.contains "--no-nat"
  let (nums, names) := (args.filter (· != "--no-nat")).partition (·.isNat)
  let ops := if names.isEmpty then ops else names
  let sizes := if nums.isEmpty then sizes else nums.map String.toNat!
  IO.println <| s!"{pad 7 "op"} {pad 6 "limbs"} {pad 10 "MPN"} {pad 10 "Nat"} {pad 8 "ratio"} " ++
    s!"{pad 8 "±MPN"} {pad 8 "±Nat"}"
  for op in ops do
    for n in sizes do
      unless ← run noNat op n do
        throw <| .userError s!"unknown operation {op}"

end Bench
