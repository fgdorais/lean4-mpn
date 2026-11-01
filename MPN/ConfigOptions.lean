/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean

/-!
# Thresholds as options

The thresholds of a width are the `Nat` fields of a structure `C` with defaults, such as
`MPN.W64.Config`. `declare_config_options C pfx` registers an option `pfx.f : Nat` for each of
them, with the default of the structure and the field's docstring as its description, and
`mpn_config% C pfx` is the `C` that the options in effect give: the fields whose options are set,
and the defaults of the others. The proof fields of `C` keep their default tactics, so a value
that breaks one is an error when `mpn_config%` elaborates. A module cannot read the options it
registers, so `mpn_config%` goes in a module that imports the one with `declare_config_options`.
-/

open Lean Elab Command Term Meta

namespace MPN.ConfigOptions

/-- The fields of type `Nat` of the structure `C`, with their projections. -/
meta def natFields (C : Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let mut out := #[]
  for f in getStructureFieldsFlattened env C (includeSubobjectFields := false) do
    let some proj := (findField? env C f).bind fun S => getProjFnForField? env S f
      | continue
    let ty ← inferType (mkConst proj ((← getConstInfo proj).levelParams.map mkLevelParam))
    let ty ← whnf ty
    if let .forallE _ _ b _ := ty then
      if b.isConstOf ``Nat then out := out.push (f, proj)
  return out

/-- A docstring as a one-line description. -/
meta def oneLine (s : String) : String :=
  " ".intercalate ((s.splitToList Char.isWhitespace).filter (· ≠ ""))

end MPN.ConfigOptions

open MPN.ConfigOptions

/--
`declare_config_options C pfx` registers the option `pfx.f : Nat` for each field `f : Nat` of the
structure `C`, with the default of `C` and the field's docstring as its description.
-/
syntax (name := declareConfigOptions) "declare_config_options " ident ident : command

@[command_elab declareConfigOptions]
public meta def elabDeclareConfigOptions : CommandElab := fun stx => do
  match stx with
  | `(declare_config_options $c:ident $pfx:ident) =>
    let C ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    let fields ← liftTermElabM <| natFields C
    for (f, proj) in fields do
      let doc := oneLine ((← findDocString? (← getEnv) proj).getD s!"the threshold {f}")
      let opt := mkIdent (pfx.getId ++ f)
      let fld := mkIdent f
      let descr := Syntax.mkStrLit doc
      elabCommand (← `(public meta register_option $opt:ident : Nat := {
        defValue := ({} : $c).$fld:ident
        descr := $descr }))
  | _ => throwUnsupportedSyntax

/--
`mpn_config% C pfx` is the structure `C` with the field `f` set to the option `pfx.f` for each
option that is set, and the defaults of `C` for the others.
-/
syntax (name := mpnConfig) "mpn_config% " ident ident : term

@[term_elab mpnConfig]
public meta def elabMpnConfig : TermElab := fun stx _ => do
  match stx with
  | `(mpn_config% $c:ident $pfx:ident) =>
    let C ← realizeGlobalConstNoOverloadWithInfo c
    let opts ← getOptions
    let mut fs : Array String := #[]
    for (f, _) in ← natFields C do
      match opts.find? (pfx.getId ++ f) with
      | some (.ofNat n) => fs := fs.push s!"{f} := {n}"
      | some v => throwError "the option {pfx.getId ++ f} must be a number, but it is {v}"
      | none => pure ()
    let src := s!"(\{ {", ".intercalate fs.toList} } : {C})"
    let some t := (Parser.runParserCategory (← getEnv) `term src).toOption
      | throwError "mpn_config%: cannot parse {src}"
    elabTerm t (mkConst C)
  | _ => throwUnsupportedSyntax
