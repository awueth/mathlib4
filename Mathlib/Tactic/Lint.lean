/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean.Linter.Util
import Std.Data.Array.Basic
import Std.Tactic.Lint

/-!
# Linters for Mathlib

In this file we define additional linters for mathlib.

Perhaps these should be moved to Std in the future.
-/

namespace Std.Tactic.Lint
open Lean Meta

/--
Linter that checks whether a structure should be in Prop.
-/
@[std_linter] def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    -- remark: using `Lean.Meta.isProp` doesn't suffice here, because it doesn't (always?)
    -- recognize predicates as propositional.
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty => return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none -- don't flag empty structures
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."

end Std.Tactic.Lint

/-!
#  `dupNamespace` linter

The `dupNamespace` linter produces a warning when a declaration contains the same namespace
at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.
-/

namespace Mathlib.Linter

/--
The `dupNamespace` linter is set on by default.  Lean emits a warning on any declaration that
contains the same namespace at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.

*Note.*
This linter will not detect duplication in namespaces of autogenerated declarations
(other than the one whose `declId` is present in the source declaration).
-/
register_option linter.dupNamespace : Bool := {
  defValue := true
  descr := "enable the duplicated namespace linter"
}

namespace DupNamespaceLinter

open Lean Parser Elab Command Meta

/-- Gets the value of the `linter.dupNamespace` option. -/
def getLinterDupNamespace (o : Options) : Bool := Linter.getLinterValue linter.dupNamespace o

/-- `getIds stx` extracts the `declId` nodes from the `Syntax` `stx`.
If `stx` is an `alias` or an `export`, then it extracts an `ident`, instead of a `declId`. -/
partial
def getIds : Syntax → Array Syntax
  | .node _ `Std.Tactic.Alias.alias args => #[args[2]!]
  | .node _ ``Lean.Parser.Command.export args => #[args[3]![0]]
  | stx@(.node _ _ args) =>
    ((args.attach.map fun ⟨a, _⟩ => getIds a).foldl (· ++ ·) #[stx]).filter (·.getKind == ``declId)
  | _ => default

@[inherit_doc linter.dupNamespace]
def dupNamespace : Linter where run := withSetOptionIn fun stx => do
  if getLinterDupNamespace (← getOptions) then
    match getIds stx with
      | #[id] =>
        let ns := (← getScope).currNamespace
        let declName := ns ++ (if id.getKind == ``declId then id[0].getId else id.getId)
        let nm := declName.components
        let some (dup, _) := nm.zip (nm.tailD []) |>.find? fun (x, y) => x == y
          | return
        Linter.logLint linter.dupNamespace id
          m!"The namespace '{dup}' is duplicated in the declaration '{declName}'"
      | _ => return

initialize addLinter dupNamespace

end Mathlib.Linter.DupNamespaceLinter
