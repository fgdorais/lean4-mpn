/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import MPN

/-!
# Threshold tuning

`lake exe tune` measures where each algorithm starts to beat the one below it on this machine,
like GMP's `tuneup`, and prints the `Config` it finds together with the options that compile it
into the library: for a project that requires it, and on the command line. Pinning it to one
core, for example with `taskset -c 2`, gives steadier results.
-/

open ScalarArray MPN

namespace Tune

/-- `n` pseudorandom limbs. -/
def sample (n seed : Nat) : UInt32Array := Id.run do
  let mut s := seed
  let mut r := UInt32Array.emptyWithCapacity n
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    r := r.push (s / 2 ^ 32).toUInt32
  return r

/-- Runs `f a b` `reps` times, folding a limb of each result into a checksum. -/
@[noinline] def repeatMul (f : UInt32Array.Slice → UInt32Array.Slice → UInt32Array)
    (a b : UInt32Array) (reps : Nat) : UInt32 := Id.run do
  let mut acc : UInt32 := 0
  for _ in [0:reps] do
    acc := acc + (f a b)[0]!
  return acc

/-- The median time of `f a b` in nanoseconds, over trials of at least `minNs` each. -/
def time (f : UInt32Array.Slice → UInt32Array.Slice → UInt32Array) (a b : UInt32Array)
    (trials := 7) (minNs := 5_000_000) : IO Nat := do
  let mut reps := 1
  repeat
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => repeatMul f a b reps
    let t₁ ← IO.monoNanosNow
    if t₁ - t₀ ≥ minNs then break
    reps := reps * 2
  let mut samples := #[]
  for _ in [0:trials] do
    let t₀ ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => repeatMul f a b reps
    let t₁ ← IO.monoNanosNow
    samples := samples.push ((t₁ - t₀) / reps)
  return (samples.qsort (· < ·))[trials / 2]!

/--
The smallest size `n` in `sizes` from which `fast` beats `slow` on operands of `shape n` limbs at
`n` and at the next `confirm` sizes, or `none` if it never does. The operands are balanced unless
`shape` says otherwise.
-/
def crossover (slow fast : UInt32Array.Slice → UInt32Array.Slice → UInt32Array)
    (sizes : List Nat) (shape : Nat → Nat × Nat := fun n => (n, n)) (confirm := 3)
    (log : Bool := false) : IO (Option Nat) := do
  let mut wins : List Nat := []
  for n in sizes do
    let a := sample (shape n).1 1
    let b := sample (shape n).2 2
    let ts ← time slow a b
    let tf ← time fast a b
    if log then IO.println s!"  {n} limbs: {ts} ns vs {tf} ns"
    if tf < ts then
      wins := wins ++ [n]
      if wins.length > confirm then return wins.head?
    else
      wins := []
  return wins.head?

/-- One step of Karatsuba over schoolbook, or schoolbook where Karatsuba does not apply. -/
def karatsubaStep (a b : UInt32Array.Slice) : UInt32Array :=
  if h : 4 ≤ b.size ∧ b.size ≤ a.size then
    karatsuba a b h.1 h.2 fun x y _ => mulBasecase x y
  else
    mulBasecase a b

/-- The median of `runs` searches, since the timings near a crossover are close. -/
def medianOf (runs : Nat) (search : IO Nat) : IO Nat := do
  let mut found := #[]
  for _ in [0:runs] do
    found := found.push (← search)
  return (found.qsort (· < ·))[runs / 2]!

/-- Tunes `mulKaratsuba`: where one Karatsuba step starts to beat schoolbook. -/
def tuneKaratsuba (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 61).map (8 + 4 * ·)
  match ← crossover (fun a b => mulBasecase a b) karatsubaStep sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Karatsuba never won up to 248 limbs; using 248"
    return 248

/--
Tunes `mulUnbalanced`: where splitting beats schoolbook on operands of `8 n` and `n` limbs, with
Karatsuba from `karatsuba` limbs on the pieces.
-/
def tuneUnbalanced (karatsuba : Nat) (h : 4 ≤ karatsuba) (log : Bool) : IO Nat := medianOf 3 do
  let cfg : Config := { mulKaratsuba := karatsuba, four_le_mulKaratsuba := h, mulUnbalanced := 0 }
  let sizes := (List.range 40).map (karatsuba + 8 * ·)
  match ← crossover (fun a b => mulBasecase b a) (fun a b => mulLimbsWith cfg a b) sizes
      (shape := fun n => (8 * n, n)) (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln s!"warning: splitting never won up to {karatsuba + 312} limbs; using that"
    return karatsuba + 312

/--
Tunes `mulToom3`: where one Toom-3 step beats Karatsuba, with Karatsuba from `karatsuba` limbs on
the products of both.
-/
def tuneToom3 (karatsuba : Nat) (h : 4 ≤ karatsuba) (log : Bool) : IO Nat := medianOf 3 do
  -- A threshold for Toom-3 beyond every size tried, so that only Karatsuba recurses.
  let cfg : Config := { mulKaratsuba := karatsuba, four_le_mulKaratsuba := h, mulToom3 := 100000 }
  let toom3Step (a b : UInt32Array.Slice) : UInt32Array :=
    if h : 12 ≤ b.size ∧ b.size ≤ a.size ∧ 3 * a.size < 4 * b.size then
      toom3 a b h.1 h.2.1 h.2.2 fun x y _ => mulLimbsWith cfg x y
    else
      mulLimbsWith cfg a b
  let sizes := (List.range 50).map (karatsuba + 16 * ·)
  match ← crossover (fun a b => mulLimbsWith cfg a b) toom3Step sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln s!"warning: Toom-3 never won up to {karatsuba + 784} limbs; using that"
    return karatsuba + 784

/--
Tunes `mulToom32`: where one step of Toom-3 by 2 beats the dispatcher without it, on operands of
`3 n / 2` and `n` limbs, with Karatsuba and Toom-3 from the tuned thresholds below it.
-/
def tuneToom32 (karatsuba toom3 : Nat) (h : 4 ≤ karatsuba) (h₃ : 12 ≤ toom3) (log : Bool) :
    IO Nat := medianOf 3 do
  -- A threshold for Toom-3 by 2 beyond every size tried, so that only the others recurse.
  let cfg : Config := {
    mulKaratsuba := karatsuba, four_le_mulKaratsuba := h
    mulToom3 := toom3, twelve_le_mulToom3 := h₃
    mulToom32 := 100000 }
  let toom32Step (a b : UInt32Array.Slice) : UInt32Array :=
    if h : 12 ≤ b.size ∧ b.size ≤ a.size ∧ (a.size + 2) / 3 ≤ b.size then
      toom32 a b h.1 h.2.1 h.2.2 fun x y _ => mulLimbsWith cfg x y
    else
      mulLimbsWith cfg a b
  let sizes := (List.range 50).map (16 + 8 * ·)
  match ← crossover (fun a b => mulLimbsWith cfg a b) toom32Step sizes
      (shape := fun n => (3 * n / 2, n)) (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Toom-3 by 2 never won up to 408 limbs; using 408"
    return 408

/--
Tunes `mulToom42`: where one step of Toom-4 by 2 beats the dispatcher without it, on operands of
`15 n / 8` and `n` limbs, with the other thresholds tuned below it.
-/
def tuneToom42 (karatsuba toom3 toom32 : Nat) (h : 4 ≤ karatsuba) (h₃ : 12 ≤ toom3)
    (h₃₂ : 12 ≤ toom32) (log : Bool) : IO Nat := medianOf 3 do
  -- A threshold for Toom-4 by 2 beyond every size tried, so that only the others recurse.
  let cfg : Config := {
    mulKaratsuba := karatsuba, four_le_mulKaratsuba := h
    mulToom3 := toom3, twelve_le_mulToom3 := h₃
    mulToom32 := toom32, twelve_le_mulToom32 := h₃₂
    mulToom42 := 100000 }
  let toom42Step (a b : UInt32Array.Slice) : UInt32Array :=
    if h : 12 ≤ b.size ∧ 15 * b.size ≤ 8 * a.size ∧ a.size < 2 * b.size then
      toom42 a b h.1 (by lia) h.2.2 fun x y _ => mulLimbsWith cfg x y
    else
      mulLimbsWith cfg a b
  let sizes := (List.range 50).map (32 + 16 * ·)
  match ← crossover (fun a b => mulLimbsWith cfg a b) toom42Step sizes
      (shape := fun n => (15 * n / 8, n)) (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Toom-4 by 2 never won up to 816 limbs; using 816"
    return 816

/--
Tunes `mulToom43`: where one step of Toom-4 by 3 beats the dispatcher without it, on operands of
`4 n / 3` and `n` limbs, with the other thresholds tuned below it and no Toom-4.
-/
def tuneToom43 (karatsuba toom3 toom32 toom42 : Nat) (h : 4 ≤ karatsuba) (h₃ : 12 ≤ toom3)
    (h₃₂ : 12 ≤ toom32) (h₄₂ : 12 ≤ toom42) (log : Bool) : IO Nat := medianOf 3 do
  -- Thresholds for Toom-4 by 3 and Toom-4 beyond every size tried, so that only the others
  -- recurse.
  let cfg : Config := {
    mulKaratsuba := karatsuba, four_le_mulKaratsuba := h
    mulToom3 := toom3, twelve_le_mulToom3 := h₃
    mulToom32 := toom32, twelve_le_mulToom32 := h₃₂
    mulToom42 := toom42, twelve_le_mulToom42 := h₄₂
    mulToom43 := 100000, mulToom4 := 100000 }
  let toom43Step (a b : UInt32Array.Slice) : UInt32Array :=
    if h : 32 ≤ b.size ∧ 6 * b.size ≤ 5 * a.size ∧ 8 * a.size < 15 * b.size then
      toom43 a b h.1 h.2.1 h.2.2 fun x y _ => mulLimbsWith cfg x y
    else
      mulLimbsWith cfg a b
  let sizes := (List.range 50).map (32 + 16 * ·)
  match ← crossover (fun a b => mulLimbsWith cfg a b) toom43Step sizes
      (shape := fun n => (4 * n / 3, n)) (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Toom-4 by 3 never won up to 816 limbs; using 816"
    return 816

/--
Tunes `mulToom4`: where one Toom-4 step beats the dispatcher without it, on balanced operands,
with the other thresholds tuned below it.
-/
def tuneToom4 (karatsuba toom3 toom32 toom42 toom43 : Nat) (h : 4 ≤ karatsuba) (h₃ : 12 ≤ toom3)
    (h₃₂ : 12 ≤ toom32) (h₄₂ : 12 ≤ toom42) (h₄₃ : 32 ≤ toom43) (log : Bool) :
    IO Nat := medianOf 3 do
  -- A threshold for Toom-4 beyond every size tried, so that only the others recurse.
  let cfg : Config := {
    mulKaratsuba := karatsuba, four_le_mulKaratsuba := h
    mulToom3 := toom3, twelve_le_mulToom3 := h₃
    mulToom32 := toom32, twelve_le_mulToom32 := h₃₂
    mulToom42 := toom42, twelve_le_mulToom42 := h₄₂
    mulToom43 := toom43, thirtytwo_le_mulToom43 := h₄₃
    mulToom4 := 100000 }
  let toom4Step (a b : UInt32Array.Slice) : UInt32Array :=
    if h : 32 ≤ b.size ∧ b.size ≤ a.size ∧ 3 * a.size < 4 * b.size then
      toom44 a b h.1 h.2.1 h.2.2 fun x y _ => mulLimbsWith cfg x y
    else
      mulLimbsWith cfg a b
  let sizes := (List.range 40).map (256 + 32 * ·)
  match ← crossover (fun a b => mulLimbsWith cfg a b) toom4Step sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Toom-4 never won up to 1504 limbs; using 1504"
    return 1504

/-- Tunes `sqrBasecase`: where the schoolbook square starts to beat multiplying. -/
def tuneSqrBasecase (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 61).map (2 + 2 * ·)
  match ← crossover (fun a _ => mulBasecase a a) (fun a _ => sqrBasecase a) sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: the schoolbook square never won up to 122 limbs; using 122"
    return 122

/-- One step of Karatsuba squaring over schoolbook squaring. -/
def karatsubaSqrStep (a _ : UInt32Array.Slice) : UInt32Array :=
  if h : 4 ≤ a.size then karatsubaSqr a h fun x _ => sqrBasecase x else sqrBasecase a

/-- Tunes `sqrKaratsuba`: where one Karatsuba square starts to beat the schoolbook square. -/
def tuneSqrKaratsuba (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 91).map (8 + 4 * ·)
  match ← crossover (fun a _ => sqrBasecase a) karatsubaSqrStep sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: Karatsuba squaring never won up to 368 limbs; using 368"
    return 368

/--
Tunes `sqrToom3`: where one Toom-3 square beats Karatsuba squaring, with the squares of both
computed by `sqrLimbsWith` from the tuned schoolbook and Karatsuba thresholds.
-/
def tuneSqrToom3 (basecase karatsuba : Nat) (h : 4 ≤ karatsuba) (log : Bool) :
    IO Nat := medianOf 3 do
  -- A threshold for Toom-3 beyond every size tried, so that only Karatsuba recurses.
  let cfg : Config := {
    sqrBasecase := basecase, sqrKaratsuba := karatsuba, four_le_sqrKaratsuba := h,
    sqrToom3 := 100000 }
  let toom3SqrStep (a _ : UInt32Array.Slice) : UInt32Array :=
    if h : 12 ≤ a.size then toom3Sqr a h fun x _ => sqrLimbsWith cfg x else sqrLimbsWith cfg a
  let sizes := (List.range 50).map (karatsuba + 16 * ·)
  match ← crossover (fun a _ => sqrLimbsWith cfg a) toom3SqrStep sizes (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln s!"warning: Toom-3 squaring never won up to {karatsuba + 784} limbs; using that"
    return karatsuba + 784

/-- The quotient of `a` by `b` after normalizing both, with `div` on the normalized numbers. -/
def normDiv (div : (u v : UInt32Array.Slice) → 2 ≤ v.size → UInt32Array)
    (a b : UInt32Array.Slice) : UInt32Array :=
  let f := normFactor (b.getD (b.size - 1) 0)
  let vf := mulRow b f
  let v := vf.toSlice.slice 0 (topSize vf)
  if h : 2 ≤ v.size then div (mulRow a f) v h else a.copy

/-- One level of division by blocks over `divRemBasecase`. -/
def divDCStep (u v : UInt32Array.Slice) (h : 2 ≤ v.size) : UInt32Array :=
  if h4 : 4 ≤ v.size then
    (divRemDC config u v h4 fun u' v' _ hn' => divRemBasecase u' v' hn').1
  else
    (divRemBasecase u v h).1

/-- Tunes `divDC`: where one level of division by blocks beats `divRemBasecase`, at `2 n / n`. -/
def tuneDivDC (log : Bool) : IO Nat := medianOf 3 do
  let sizes := (List.range 60).map (16 + 8 * ·)
  match ← crossover (normDiv fun u v h => (divRemBasecase u v h).1) (normDiv divDCStep) sizes
      (shape := fun n => (2 * n, n)) (log := log) with
  | some n =>
    if log then IO.println s!"  found {n}"
    return n
  | none =>
    IO.eprintln "warning: division by blocks never won up to 488 limbs; using 488"
    return 488

end Tune

open Tune in
public def main (args : List String) : IO UInt32 := do
  let log := args.contains "--verbose"
  IO.println "Tuning the lean4-mpn thresholds; this takes a few minutes."
  IO.println "mulKaratsuba: one Karatsuba step against schoolbook"
  let karatsuba ← tuneKaratsuba log
  IO.println "mulToom3: one Toom-3 step against Karatsuba"
  let toom3 ← tuneToom3 (max 4 karatsuba) (by lia) log
  IO.println "mulToom32: one step of Toom-3 by 2 against the others, at 3:2"
  let toom32 ← tuneToom32 (max 4 karatsuba) (max 12 toom3) (by lia) (by lia) log
  IO.println "mulToom42: one step of Toom-4 by 2 against the others, at 15:8"
  let toom42 ← tuneToom42 (max 4 karatsuba) (max 12 toom3) (max 12 toom32) (by lia) (by lia)
    (by lia) log
  IO.println "mulToom43: one step of Toom-4 by 3 against the others, at 4:3"
  let toom43 ← tuneToom43 (max 4 karatsuba) (max 12 toom3) (max 12 toom32) (max 12 toom42)
    (by lia) (by lia) (by lia) (by lia) log
  IO.println "mulToom4: one Toom-4 step against the others"
  let toom4 ← tuneToom4 (max 4 karatsuba) (max 12 toom3) (max 12 toom32) (max 12 toom42)
    (max 32 toom43) (by lia) (by lia) (by lia) (by lia) (by lia) log
  IO.println "mulUnbalanced: halving the longer operand against schoolbook, at 8:1"
  let unbalanced ← tuneUnbalanced (max 4 karatsuba) (by lia) log
  IO.println "sqrBasecase: the schoolbook square against multiplying"
  let sqrBasecase ← tuneSqrBasecase log
  IO.println "sqrKaratsuba: one Karatsuba square against the schoolbook square"
  let sqrKaratsuba ← tuneSqrKaratsuba log
  IO.println "sqrToom3: one Toom-3 square against Karatsuba squaring"
  let sqrToom3 ← tuneSqrToom3 sqrBasecase (max 4 sqrKaratsuba) (by lia) log
  IO.println "divDC: one level of division by blocks against Algorithm D, at 2n / n"
  let divDC ← tuneDivDC log
  let cfg : Config := {
    mulKaratsuba := max 4 karatsuba, four_le_mulKaratsuba := by lia,
    mulToom3 := max 12 toom3, twelve_le_mulToom3 := by lia,
    mulToom32 := max 12 toom32, twelve_le_mulToom32 := by lia,
    mulToom42 := max 12 toom42, twelve_le_mulToom42 := by lia,
    mulToom43 := max 32 toom43, thirtytwo_le_mulToom43 := by lia,
    mulToom4 := max 32 toom4, thirtytwo_le_mulToom4 := by lia, mulUnbalanced := unbalanced
    sqrBasecase, sqrKaratsuba := max 4 sqrKaratsuba, four_le_sqrKaratsuba := by lia,
    sqrToom3 := max 12 sqrToom3, twelve_le_sqrToom3 := by lia,
    divDC := max 4 divDC, four_le_divDC := by lia }
  IO.println ""
  IO.println s!"Found:   {repr cfg}"
  IO.println s!"Default: {repr ({} : Config)}"
  IO.println ""
  let opts := [("mulKaratsuba", cfg.mulKaratsuba), ("mulToom3", cfg.mulToom3),
    ("mulToom32", cfg.mulToom32), ("mulToom42", cfg.mulToom42), ("mulToom43", cfg.mulToom43),
    ("mulToom4", cfg.mulToom4),
    ("mulUnbalanced", cfg.mulUnbalanced), ("sqrBasecase", cfg.sqrBasecase),
    ("sqrKaratsuba", cfg.sqrKaratsuba), ("sqrToom3", cfg.sqrToom3), ("divDC", cfg.divDC)]
  IO.println "To compile these into the library, add to its `require` in lakefile.toml:"
  IO.println s!"  options = \{ {", ".intercalate (opts.map fun (k, v) => s!"{k} = \"{v}\"")} }"
  IO.println "or build this package with:"
  IO.println s!"  lake build -R {" ".intercalate (opts.map fun (k, v) => s!"-K {k}={v}")}"
  return 0
