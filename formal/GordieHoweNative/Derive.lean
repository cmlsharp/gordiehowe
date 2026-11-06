-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Ghc
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Command

public meta section

/-!
# GordieHowe: deriving the `.ghc` decoder of an inductive type

`deriving instance GordieHowe.Ghc.Decode for T` derives `T`'s instance of `Ghc.Decode`
(`Ghc.lean`) from its constructors: a structure is read as its fields in order, any other inductive
as its constructor's index then its fields, each field by its own type's instance (a field of type
`T` or `List T` uses the recursive operations being defined), in the plain and in the spine form;
a value's expression is its constructor applied to the type's parameters and the fields' expressions, as
Lean's derived `ToExpr` builds it. `T`'s parameters must be types (each gets a `Decode` instance
argument) and `T` must have no universe parameters and no indices; a field's type is built from
constants, applications and the parameters.

The handler writes the instance's auxiliary definitions under `GordieHowe.Ghc.Derived.T` (`tyE`,
then mutually `toE`, `dec`, `inline`, `spine`, `inlineE`, `spineE`) and the instance as Lean text,
and elaborates it.
-/

namespace GordieHowe.Ghc.Derive

open Lean Elab Command Meta

/-- A name as an identifier from the root. -/
def rootId (n : Name) : String := s!"_root_.{n}"

/-- **A field's type as Lean text**: its constants from the root, applications in parentheses,
the type's parameters by name. -/
partial def typeText (e : Expr) : MetaM String := do
  match e with
  | .const n _ => pure (rootId n)
  | .fvar id => pure (← id.getUserName).toString
  | .app .. =>
    let args ← e.getAppArgs.mapM typeText
    pure s!"({← typeText e.getAppFn} {" ".intercalate args.toList})"
  | _ => throwError "Ghc.Decode: unsupported field type {e}"

/-- **The commands deriving `Decode` for `T`** (see the module docstring). -/
def mkCommands (T : Name) : TermElabM (Array String) := do
  let env ← getEnv
  let ind ← getConstInfoInduct T
  unless ind.levelParams.isEmpty do throwError "Ghc.Decode: {T} has universe parameters"
  unless ind.numIndices == 0 do throwError "Ghc.Decode: {T} has indices"
  let isStruct := isStructure env T
  let pfx := `GordieHowe.Ghc.Derived ++ T
  -- an auxiliary definition: declared from the root, referred to by its full name (in the mutual
  -- block a definition being declared is not found from the root)
  let auxD (s : String) := rootId (pfx ++ Name.mkSimple s)
  let aux (s : String) := toString (pfx ++ Name.mkSimple s)
  forallTelescopeReducing ind.type fun ps _ => do
    let mut pnames : Array String := #[]
    for p in ps do
      unless (← inferType p).isSort do throwError "Ghc.Decode: {T}: a parameter is not a type"
      pnames := pnames.push (← p.fvarId!.getUserName).toString
    let binders := " ".intercalate (pnames.toList.map fun a =>
      s!"\{{a} : Type} [_root_.GordieHowe.Ghc.Decode {a}]")
    let named := " ".intercalate (pnames.toList.map fun a => s!"({a} := {a})")
    let tApp := if pnames.isEmpty then rootId T else s!"({rootId T} {" ".intercalate pnames.toList})"
    let tyEs := ", ".intercalate (pnames.toList.map fun a =>
      s!"(_root_.GordieHowe.Ghc.Decode.tyE (α := {a}))")
    let tyE := s!"(Lean.mkAppN (Lean.mkConst `{T} []) #[{tyEs}])"
    let tyD := s!"(_root_.GordieHowe.Ghc.tyOf ({aux "tyE"} {named}))"
    let D := "_root_.GordieHowe.Ghc.D"
    -- Per constructor: index, name and fields (type text, whether recursive).
    -- Direct recursion has empty type text; recursive lists keep their container type.
    let mut ctors : Array (Nat × Name × Array (String × Bool)) := #[]
    for (c, i) in ind.ctors.zipIdx do
      let ci ← getConstInfoCtor c
      let fields ← forallTelescopeReducing ci.type fun xs _ => do
        let mut fs := #[]
        for x in xs.extract ci.numParams xs.size do
          -- the field's type, with the constructor's parameters replaced by the type's
          let t := (← inferType x).replaceFVars (xs.extract 0 ci.numParams) ps
          if t.isAppOf T then
            unless t.getAppArgs == ps do throwError "Ghc.Decode: {c}: a field of {T} at other parameters"
            fs := fs.push ("", true)
          else
            if t.find? (fun e => e.isConstOf T) |>.isSome then
              unless t.isAppOfArity ``List 1 && t.getAppArgs[0]!.isAppOf T &&
                  t.getAppArgs[0]!.getAppArgs == ps do
                throwError "Ghc.Decode: {c}: unsupported nested occurrence of {T}"
              fs := fs.push (← typeText t, true)
            else
              fs := fs.push (← typeText t, false)
        pure fs
      ctors := ctors.push (i, c, fields)
    -- a constructor's application: its fields read by `field`
    let ctorApp (c : Name) (fs : Array (String × Bool)) (field : String × Bool → String) : String :=
      let args := fs.toList.map field
      s!"(@{rootId c} {" ".intercalate (List.replicate pnames.size "_")} {" ".intercalate args})"
    let ctorAppE (c : Name) (fs : Array (String × Bool)) (field : String × Bool → String) : String :=
      let args := (pnames.toList.map fun a => s!"(_root_.GordieHowe.Ghc.Decode.tyE (α := {a}))") ++
        fs.toList.map field
      s!"(Lean.mkAppN (Lean.mkConst `{c} []) #[{", ".intercalate args}])"
    -- a reader: the constructor index (unless a structure), then the fields
    let reader (pure_ : String → String) (app : Name → Array (String × Bool) → String) : String :=
      if isStruct then
        let (_, c, fs) := ctors[0]!
        s!"do {pure_ (app c fs)}"
      else
        let arms := ctors.toList.map fun (i, c, fs) => s!"  | {i} => {pure_ (app c fs)}\n"
        s!"do\n  match (← _root_.GordieHowe.Ghc.nat) with\n{String.join arms}  | k => \
          _root_.GordieHowe.Ghc.badCtor \"{T}\" k"
    -- A nested list uses the existing container codec with the current recursive operations.
    let selfCodec := s!"letI : _root_.GordieHowe.Ghc.Decode {tApp} := \
      ⟨{aux "tyE"} {named}, {aux "toE"}, {aux "dec"}, {aux "spine"}, \
      {aux "spineE"} {named}⟩; "
    let decField (m r : String) : String × Bool → String
      | ("", true) => s!"(← {aux r} {named})"
      | (t, true) => s!"(← ({selfCodec}_root_.GordieHowe.Ghc.Decode.{m} (α := {t})))"
      | (t, false) => s!"(← _root_.GordieHowe.Ghc.Decode.{m} (α := {t}))"
    let pureV (s : String) := s!"pure {s}"
    let dec := reader pureV fun c fs => ctorApp c fs (decField "dec" "dec")
    let inline := reader pureV fun c fs => ctorApp c fs (decField "spine" "spine")
    let inlineE := reader pureV fun c fs => ctorAppE c fs (decField "spineE" "spineE")
    -- the expression of a value
    let toEArms := ctors.toList.map fun (_, c, fs) =>
      let vars := (List.range fs.size).map fun j => s!"a{j}"
      let pat := s!"@{rootId c} {" ".intercalate (List.replicate pnames.size "_")} {" ".intercalate vars}"
      let args := (pnames.toList.map fun a => s!"(_root_.GordieHowe.Ghc.Decode.tyE (α := {a}))") ++
        (fs.toList.zip vars).map fun ((t, r), v) =>
          if r && t.isEmpty then s!"({aux "toE"} {v})"
          else if r then s!"({selfCodec}_root_.GordieHowe.Ghc.Decode.toE {v})"
          else s!"(_root_.GordieHowe.Ghc.Decode.toE {v})"
      s!"  | {pat} => Lean.mkAppN (Lean.mkConst `{c} []) #[{", ".intercalate args}]\n"
    let cmds := #[
      s!"def {auxD "tyE"} {binders} : Lean.Expr := {tyE}",
      s!"mutual\n\
        partial def {auxD "toE"} {binders} : {tApp} → Lean.Expr\n{String.join toEArms}\n\
        partial def {auxD "dec"} {binders} : {D} {tApp} := {dec}\n\n\
        partial def {auxD "inline"} {binders} : {D} {tApp} := {inline}\n\n\
        partial def {auxD "spine"} {binders} : {D} {tApp} :=\n  \
          _root_.GordieHowe.Ghc.spineWith {tyD} {aux "dec"} {aux "spine"} {aux "inline"}\n\n\
        partial def {auxD "inlineE"} {binders} : {D} Lean.Expr := {inlineE}\n\n\
        partial def {auxD "spineE"} {binders} : {D} Lean.Expr :=\n  \
          _root_.GordieHowe.Ghc.spineEWith {tyD} ({aux "toE"} {named}) ({aux "dec"} {named})
    ({aux "inlineE"} {named})\n\
        end",
      s!"instance {binders} : _root_.GordieHowe.Ghc.Decode {tApp} where\n  \
        tyE := {aux "tyE"} {named}\n  toE := {aux "toE"}\n  dec := {aux "dec"}\n  \
        spine := {aux "spine"}\n  spineE := {aux "spineE"} {named}"]
    pure cmds

/-- **The deriving handler of `Ghc.Decode`**: each named type's instance (`mkCommands`). -/
def handler (declNames : Array Name) : CommandElabM Bool := do
  unless ← declNames.allM isInductive do return false
  for T in declNames do
    let cmds ← liftTermElabM (mkCommands T)
    for c in cmds do
      match Parser.runParserCategory (← getEnv) `command c with
      | .ok stx => elabCommand stx
      | .error e => throwError "Ghc.Decode: {T}: {e}\n{c}"
  return true

initialize registerDerivingHandler ``GordieHowe.Ghc.Decode handler

end GordieHowe.Ghc.Derive
