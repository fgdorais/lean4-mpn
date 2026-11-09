/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPN.Default
import MPN32

/-!
Every declaration of the three libraries depends on the standard axioms alone: `propext`,
`Classical.choice` and `Quot.sound`, so no `sorry` and no `native_decide`. It checks every
declaration of the modules `MPN.*`, `MPN32.*` and `MPN64.*`, by the axioms each module records for
its declarations when it is compiled.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ours (m : Name) : Bool := [`MPN, `MPN32, `MPN64].any (·.isPrefixOf m)
  let names := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if ours env.header.moduleNames[i.toNat]! then acc.push n else acc
    | none => acc
  if names.size < 1000 then
    throwError "only {names.size} declarations found in the libraries' modules"
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut seen : NameSet := {}
  for n in names do
    for ax in ← collectAxioms n do
      seen := seen.insert ax
      unless std.contains ax do bad := bad.push (n, ax)
  unless bad.isEmpty do
    throwError "axioms beyond the standard ones (declaration, axiom): {bad.toList.take 20}"
  -- The proofs use all three, so finding none would mean the check saw no proofs.
  unless std.all seen.contains do
    throwError "the standard axioms not all found: {seen.toList}"
