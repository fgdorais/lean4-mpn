/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN

/-!
# The tuners' harness

What both widths' tuners share: pseudorandom operands on any `WordArray`, the median time of an
operation, and the search for the size from which one configuration beats another, like GMP's
`tuneup`. A result is folded into a checksum by a constant-time `check`, so that the compiler
keeps the operation and the check costs nothing next to it.
-/

open MPN

namespace Tune

/-- `n` pseudorandom limbs of any width, the high bits of a linear congruential generator, with a
nonzero top limb. -/
public def sample {A L : Type} [LA : LimbArray A L] [R : WordArray A L] (n seed : Nat) : A :=
  Id.run do
    let mut s := seed
    let mut r := R.zeros n
    for i in [0:n] do
      s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      r := LA.set r i (s / 2 ^ (64 - min 64 LA.w) ||| (if i + 1 = n then 1 else 0))
    return r

/-- A constant-time check of an array: its size and its lowest limb. -/
public def checkA {A L : Type} [LA : LimbArray A L] (a : A) : UInt64 :=
  (LA.size a).toUInt64 + (LA.val (LA.get a 0)).toUInt64

/-- Runs `f a b` `reps` times, folding `check` of each result into a checksum. -/
@[noinline] public def repeatOp {α β γ : Type} [Add γ] [OfNat γ 0] (f : α → α → β)
    (check : β → γ) (a b : α) (reps : Nat) : γ := Id.run do
  let mut acc : γ := 0
  for _ in [0:reps] do
    acc := acc + check (f a b)
  return acc

/-- The median time of `f a b` in nanoseconds, over trials of at least `minNs` each. -/
public def timeOp {α β γ : Type} [Add γ] [OfNat γ 0] (f : α → α → β) (check : β → γ) (a b : α)
    (trials := 7) (minNs := 5_000_000) : IO Nat := do
  let mut reps := 1
  repeat
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => repeatOp f check a b reps
    let t₁ ← IO.monoNanosNow
    if t₁ - t₀ ≥ minNs then break
    reps := reps * 2
  let mut samples := #[]
  for _ in [0:trials] do
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => repeatOp f check a b reps
    let t₁ ← IO.monoNanosNow
    samples := samples.push ((t₁ - t₀) / reps)
  return (samples.qsort (· < ·))[trials / 2]!

/--
The smallest size `n` in `sizes` from which `fast n` beats `slow` on the inputs `input n` at `n`
and at the next `confirm` sizes, or `none` if it never does.
-/
public def crossoverOn {α β γ : Type} [Add γ] [OfNat γ 0] (slow : α → α → β)
    (fast : Nat → α → α → β) (check : β → γ) (input : Nat → α × α) (sizes : List Nat)
    (confirm := 3) (log : Bool := false) : IO (Option Nat) := do
  let mut wins : List Nat := []
  for n in sizes do
    let (a, b) := input n
    let ts ← timeOp slow check a b
    let tf ← timeOp (fast n) check a b
    if log then IO.println s!"  {n}: {ts} ns vs {tf} ns"
    if tf < ts then
      wins := wins ++ [n]
      if wins.length > confirm then return wins.head?
    else
      wins := []
  return wins.head?

/-- `crossoverOn` with the same `fast` at every size, for thresholds that `fast` reads itself. -/
public def crossoverFixed {α β γ : Type} [Add γ] [OfNat γ 0] (slow fast : α → α → β)
    (check : β → γ) (input : Nat → α × α) (sizes : List Nat) (confirm := 3)
    (log : Bool := false) : IO (Option Nat) :=
  crossoverOn slow (fun _ => fast) check input sizes confirm log

/-- The median of `runs` searches, since the timings near a crossover are close. -/
public def medianOf (runs : Nat) (search : IO Nat) : IO Nat := do
  let mut found := #[]
  for _ in [0:runs] do
    found := found.push (← search)
  return (found.qsort (· < ·))[runs / 2]!

/--
Tunes a threshold by `crossoverOn`, the median of three searches, with the last size and a
warning when the faster side never wins.
-/
public def tune {α β γ : Type} [Add γ] [OfNat γ 0] (name : String) (slow : α → α → β)
    (fast : Nat → α → α → β) (check : β → γ) (input : Nat → α × α) (sizes : List Nat)
    (confirm := 3) (log : Bool) : IO Nat := medianOf 3 do
  match ← crossoverOn slow fast check input sizes confirm log with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    let last := sizes.getLast?.getD 0
    IO.eprintln s!"warning: {name} never won up to {last} limbs; using {last}"
    return last

/-- The sizes `start`, `start + step`, …, below `stop`. -/
public def range (start stop step : Nat) : List Nat :=
  (List.range ((stop - start + step - 1) / step)).map (start + step * ·)

end Tune
