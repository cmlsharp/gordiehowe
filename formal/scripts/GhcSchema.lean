-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import Lean
import GordieHoweNative.Data

/-! The schema of the `.ghc` data types as text: every inductive type `GordieHoweNative/Data.lean`
declares, sorted by name, with its parameter count and its constructors in Lean's order; a
structure with its fields' names and types, any other inductive with each constructor's name and
field types. A type is printed as the C++ schema prints it (`ghc::Ty::text`): full constant names,
applications parenthesized as arguments, `#i` for the type's parameter `i`. The C++ writer's schema
(`lib/gordiehowe/compiler/ghc_gkr.h`, `gkr_schema`) prints the same text (`ghc::Schema::dump`, the
binary `ghc_show --schema`), kept in `scripts/ghc_schema.txt`; `scripts/check.sh` compares this
script's output with that file, and the C++ test `gordiehowe_ghc_test` the C++ schema's. -/

open Lean Meta Elab Command

/-- The type `e` as `ghc::Ty::text` prints it, `ps` the type's parameters. -/
partial def ghcTyText (ps : Array Expr) (e : Expr) : MetaM String := do
  let e := e.consumeTypeAnnotations
  let atom (a : Expr) : MetaM String := do
    let s ← ghcTyText ps a
    return if a.consumeTypeAnnotations.getAppNumArgs > 0 then s!"({s})" else s
  match e.getAppFn with
  | .const c _ =>
    let args ← e.getAppArgs.mapM atom
    return " ".intercalate (c.toString (escape := false) :: args.toList)
  | .fvar _ =>
    match ps.findIdx? (· == e) with
    | some i => return s!"#{i}"
    | none => return s!"?{← ppExpr e}"
  | _ => return s!"?{← ppExpr e}"

run_cmd liftTermElabM do
  let env ← getEnv
  let some mod := env.getModuleIdx? `GordieHoweNative.Data
    | throwError "GordieHoweNative.Data is not imported"
  let mut types : Array (Name × InductiveVal) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some mod || n.isInternal then continue
    if let .inductInfo v := ci then types := types.push (n, v)
  for (n, v) in types.qsort (fun a b => a.1.toString < b.1.toString) do
    let isStr := isStructure env n
    IO.println s!"{if isStr then "structure" else "inductive"} {n.toString (escape := false)} \
      (params {v.numParams})"
    for c in v.ctors do
      let ty := (← getConstInfo c).type
      let lines ← forallTelescope ty fun xs _ => do
        let ps := xs.extract 0 v.numParams
        let fs := xs.extract v.numParams xs.size
        let mut out : Array String := #[]
        for f in fs do
          let d ← f.fvarId!.getDecl
          out := out.push (s!"{d.userName.eraseMacroScopes} : " ++ (← ghcTyText ps d.type))
        return out
      if isStr then
        for l in lines do IO.println s!"  {l}"
      else
        let fts := lines.toList.map fun l => (l.splitOn " : ").drop 1 |> " : ".intercalate
        let fts := fts.map fun t => if t.contains ' ' then s!"({t})" else t
        IO.println s!"  | {(c.updatePrefix .anonymous).toString (escape := false)}\
          {String.join (fts.map (" " ++ ·))}"
