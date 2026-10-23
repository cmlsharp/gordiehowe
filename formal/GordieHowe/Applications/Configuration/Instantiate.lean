-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public meta import Lean
public meta import GordieHowe.Headline

public meta section

/-!
# Instantiating a configuration: `config_template` and `instantiate_config`

A configuration's statements are proved once, generically, as theorems and definitions whose
leading arguments are a configuration record, its facts and further data (a configuration's
`Extraction`). `@[config_template]` marks such a declaration; `instantiate_config N from
[F₁, …, Fₘ] a₁ … aₙ` adds, for every marked declaration `G` in one of the namespaces `Fᵢ`, in the
order the attribute was applied, the declaration `N.g` (`g` the last component of `G`, or the name
given in the attribute). `G` takes, for each of its leading binders in turn, the first remaining
`aᵢ` of that binder's type. The value of a theorem is `G a₁ … aₙ`, an ordinary term the kernel
checks against the stated type. The value of a computable definition is `G`'s body at the
arguments, with the record projections of the arguments reduced as in the stated type, so its code
reads the configuration's own definitions (its IOP and transcript) and not the record: it has
compiled code although the record's soundness and honest-prover fields do not. The kernel compares
the value with `G a₁ … aₙ` by unfolding.

The stated type is `G`'s type at `a₁ … aₙ`, made readable in two ways, both definitional:

* a projection of one of the arguments `aᵢ` that is a constant defined as a structure instance
  (`R.kq` for the configuration record `R`) is replaced by the field's value, so a configuration's
  figures appear as numerals;
* a projection of a (non-class) structure-valued definition's application whose field is a numeral
  (`(forkTranscript C).k` with `k := 32`) is replaced by the numeral;
* an application `G' a₁ … aₙ x…` of an earlier marked definition `G'` is replaced by `N.g' x…`,
  so the statement names the configuration's own definitions.

A definition `@[config_reduce]` computed from a record's fields (`Configuration.proofBound :=
max R.N R.nq`) is unfolded in a definition's value wherever it is applied to one of the records,
so that its fields are reduced as well and the instance's code does not read the record. The
stated type keeps the definition's name.

`@[config_template headline]` also tags the instance `@[headline]` (`GordieHowe/Headline.lean`), so the
statement closure and the audit see the configuration's theorems under their own names. The
instance carries the template's docstring.

Each argument `aᵢ` is elaborated at the type of the corresponding argument of the first marked
declaration, so a coercion (a configuration's facts to the facts the templates take) is inserted.

A configuration whose record depends on data takes leading binders:
`instantiate_config N from [F₁, …, Fₘ] (x₁ : X₁) … (xₖ : Xₖ) => a₁ … aₙ`, with the `aᵢ` mentioning
the `xⱼ`. Every generated declaration is abstracted over the binders, `N.g x₁ … xₖ := G a₁ … aₙ`,
and an earlier instance in a statement is applied to the binders, `N.g' x₁ … xₖ x…`. A theorem
keeps the binders' kinds as written (`{x : X}` is implicit); a definition takes them explicitly,
since nothing at its uses determines them.

`renaming g₁ → h₁, …` (after the families) names the instance of the template with last name
component `gᵢ` as `N.hᵢ`.

This is a code generator, not a decision procedure: every generated value is the application of a
proved generic declaration, checked by the kernel.
-/

open Lean Meta Elab Command

namespace GordieHowe.Configuration.Template

/-- A marked template: the generic declaration, the instance's last name component, and whether
the instance is a headline. -/
structure Template where
  /-- The generic declaration. -/
  decl : Name
  /-- The last component of the instance's name. -/
  target : Name
  /-- Whether the instance is tagged `@[headline]`. -/
  headline : Bool
  /-- The template's docstring, recorded when the attribute is applied (an importing module does
  not load docstrings under the module system), given to every instance. -/
  doc : Option String := none
  deriving Inhabited

/-- The templates, in the order the attribute was applied (imported modules first). -/
initialize templateExt : SimplePersistentEnvExtension Template (Array Template) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- `@[config_template]`, `@[config_template headline]`, `@[config_template name]`,
`@[config_template headline name]`. -/
syntax (name := configTemplate) "config_template" (&" headline")? (ppSpace ident)? : attr

initialize registerBuiltinAttribute {
    name := `configTemplate
    descr := "a generic configuration statement instantiated by `instantiate_config`"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "@[config_template] must be global"
      let headline := !stx[1].isNone
      let target := if stx[2].isNone then decl.componentsRev.head! else stx[2][0].getId
      let doc ← findDocString? (← getEnv) decl
      modifyEnv (templateExt.addEntry ·
        { decl := decl, target := target, headline := headline, doc := doc })
  }

/-- `@[config_reduce]`: a definition computed from a configuration record's fields, unfolded in
the values of instances (module docstring). -/
initialize configReduceAttr : TagAttribute ←
  registerTagAttribute `config_reduce
    "a definition of a configuration record unfolded in the values of `instantiate_config`"

/-- **A marked definition of a configuration record, unfolded**: `g … c …` with `g`
`@[config_reduce]` and `c` one of the records `recs` becomes `g`'s body at the arguments. -/
def unfoldConfigReduce? (recs : Array Expr) (e : Expr) : MetaM (Option Expr) := do
  let .const g _ := e.getAppFn | return none
  unless configReduceAttr.hasTag (← getEnv) g do return none
  unless e.getAppArgs.any recs.contains do return none
  unfoldDefinition? e

/-- The templates of the environment. -/
def templates (env : Environment) : Array Template :=
  templateExt.getState env

/-- **A projection of a configuration record, reduced**: `S.f c x…` with `c` one of the records
`recs` (a definition, possibly applied to the binders, whose value is a structure instance) becomes
the field's value applied to `x…`. -/
def reduceConstProj? (recs : Array Expr) (e : Expr) : MetaM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? f | return none
  let args := e.getAppArgs
  if args.size ≤ info.numParams then return none
  let s := args[info.numParams]!
  unless s.getAppFn.isConst && recs.contains s do return none
  let some sv ← unfoldDefinition? s | return none
  let sv ← whnfCore sv
  let .const c _ := sv.getAppFn | return none
  let some (.ctorInfo ctorVal) := (← getEnv).find? c | return none
  let fieldArgs := sv.getAppArgs
  let idx := ctorVal.numParams + info.i
  if h : idx < fieldArgs.size then
    return some (mkAppN fieldArgs[idx] (args.extract (info.numParams + 1) args.size)).headBeta
  return none

/-- **A numeral field of a structure-valued definition, reduced**: `S.f (c x…)` with `S` not a
class and `c x…` unfolding to a structure instance whose field `f` is a numeral `OfNat.ofNat n`
becomes that numeral. -/
def reduceNumeralProj? (e : Expr) : MetaM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? f | return none
  if info.fromClass then return none
  let args := e.getAppArgs
  unless args.size == info.numParams + 1 do return none
  let s := args[info.numParams]!
  unless s.getAppFn.isConst do return none
  let some sv ← unfoldDefinition? s | return none
  let sv ← whnfCore sv
  let .const c _ := sv.getAppFn | return none
  let some (.ctorInfo ctorVal) := (← getEnv).find? c | return none
  let fieldArgs := sv.getAppArgs
  let idx := ctorVal.numParams + info.i
  if h : idx < fieldArgs.size then
    let v := fieldArgs[idx]
    if v.isAppOfArity ``OfNat.ofNat 3 && (v.getArg! 1).isRawNatLit then
      return some v
  return none

/-- **The readable type of an instance** (module docstring): constant record projections reduced,
earlier instances named, applied to the binders `bs`. -/
def readable (ty : Expr) (lead : Array Expr) (done : Array (Name × Name × Array Expr))
    (bs : Array Expr := #[]) : MetaM Expr := do
  let ty ← instantiateMVars ty
  Meta.transform ty (pre := fun x => do
    if let .const g lvls := x.getAppFn then
      if let some (_, n, args) := done.find? (·.1 == g) then
        let xs := x.getAppArgs
        if xs.size ≥ args.size && (← (List.range args.size).allM fun i =>
            pure (xs[i]! == args[i]!)) then
          return .visit (mkAppN (.const n lvls) (bs ++ xs.extract args.size xs.size))
    if let some x' ← reduceConstProj? lead x then
      return .visit x'
    return .continue) (post := fun x => do
    if let some x' ← reduceNumeralProj? x then
      return .done x'
    return .done x)

/-- The leading `n` binders of a `∀` or a `λ`, made explicit. -/
def explicitLeading : Nat → Expr → Expr
  | n + 1, .forallE x d b _ => .forallE x d (explicitLeading n b) .default
  | n + 1, .lam x d b _ => .lam x d (explicitLeading n b) .default
  | _, e => e

/-- `instantiate_config N from [F₁, …, Fₘ] renaming g → h, … (x : X) … => a₁ … aₙ`: add
`N.g x… := G a₁ … aₙ` for every `@[config_template]` declaration `G` in one of the namespaces `Fᵢ`
(module docstring); the renaming and the binders are optional. -/
syntax (name := instantiateConfig)
  "instantiate_config " ident " from " "[" ident,+ "]"
    (&" renaming " sepBy1(ident " → " ident, ", "))?
    (atomic((ppSpace bracketedBinder)+ " => "))? (ppSpace term:max)+ : command

@[command_elab instantiateConfig]
def elabInstantiateConfig : CommandElab := fun stx => do
  let ns := stx[1].getId
  let fams := stx[4].getSepArgs.map (·.getId)
  let renames : Array (Name × Name) :=
    if stx[6].isNone then #[] else
      stx[6][1].getSepArgs.map fun p => (p[0].getId, p[2].getId)
  let binderStxs : Array Syntax := if stx[7].isNone then #[] else stx[7][0].getArgs
  let argStxs := stx[8].getArgs
  let ref := stx
  liftTermElabM do
    let tmpls := (templates (← getEnv)).filter fun t => fams.any (·.isPrefixOf t.decl)
    let some t0 := tmpls[0]? | throwError "no templates in {fams}"
    Term.elabBinders binderStxs fun bs => do
    let mut ty0 ← inferType (← mkConstWithFreshMVarLevels t0.decl)
    let mut lead : Array Expr := #[]
    -- Each argument is elaborated at the type of the next leading binder of the first template
    -- when it has that type, and as it stands otherwise (an argument the first template does not
    -- take, such as a configuration's `Extraction`).
    for a in argStxs do
      let e ← match ← whnf ty0 with
        | .forallE _ d b _ =>
          let e? ← observing? (Term.withoutErrToSorry do
            let e ← Term.elabTermEnsuringType a d
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e)
          match e? with
          | some e =>
            ty0 := b.instantiate1 e
            pure e
          | none => do
            let e ← Term.elabTerm a none
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
        | _ => do
          let e ← Term.elabTerm a none
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
      lead := lead.push e
    let mut done : Array (Name × Name × Array Expr) := #[]
    for t in tmpls do
      let some ci := (← getEnv).find? t.decl | throwError "unknown template {t.decl}"
      let lvls := ci.levelParams.map mkLevelParam
      -- The arguments the template takes: for each leading binder in turn, the first remaining
      -- argument of its type.
      let mut args : Array Expr := #[]
      let mut rest := lead
      let mut tyT := ci.type.instantiateLevelParams ci.levelParams lvls
      repeat
        let .forallE _ d b _ ← whnf tyT | break
        let some i ← rest.findIdxM? fun a => do isDefEq (← inferType a) d | break
        args := args.push rest[i]!
        tyT := b.instantiate1 rest[i]!
        rest := rest.eraseIdx! i
      let value := mkAppN (.const t.decl lvls) args
      let ty ← inferType value
      let ty ← readable ty lead done bs
      let ty ← instantiateMVars (← mkForallFVars bs ty)
      -- A definition's value is the template's body at the arguments, made readable as the type
      -- is: its constant record projections reduced, so that the instance's code reads the
      -- configuration's own definitions and not the record (whose soundness fields are not
      -- computable).
      let reduced ← if (← isProp ci.type) || isNoncomputable (← getEnv) t.decl then pure none else
        match ci.value? with
        | some v =>
          pure (some ((v.instantiateLevelParams ci.levelParams lvls).beta args))
        | none => pure none
      -- The record projections of the value reduced as in the type, so that the instance's code
      -- reads the configuration's own definitions (its IOP, transcript, simulator data) and not the
      -- record, whose soundness and honest-prover fields are not computable.
      let reduced ← reduced.mapM fun v => Meta.transform v (pre := fun x => do
        if let some x' ← reduceConstProj? lead x then return .visit x'
        if let some x' ← unfoldConfigReduce? lead x then return .visit x'
        return .continue)
      let reduced ← reduced.mapM fun v => do instantiateMVars (← mkLambdaFVars bs v)
      let value ← instantiateMVars (← mkLambdaFVars bs value)
      if ty.hasMVar || value.hasMVar then
        throwError "the instance of {t.decl} has unassigned metavariables"
      -- An imported theorem may be seen without its value (the module system), so a template is
      -- a theorem when its type is a proposition.
      let isThm ← isProp ci.type
      let (ty, value) :=
        if isThm then (ty, value)
        else (explicitLeading bs.size ty, explicitLeading bs.size value)
      let target := (renames.find? (·.1 == t.target)).map (·.2) |>.getD t.target
      let name := ns ++ target
      let cv : ConstantVal := { name := name, levelParams := ci.levelParams, type := ty }
      let mkDecl (value : Expr) : Declaration :=
        if isThm then
          .thmDecl { toConstantVal := cv, value := value, all := [name] }
        else
          .defnDecl (mkDefinitionValEx name ci.levelParams ty value ReducibilityHints.abbrev
            DefinitionSafety.safe [name])
      -- The reduced value when the kernel accepts it, else `G a₁ … aₙ`.
      let decl ← match reduced with
        | some v =>
          let d := mkDecl (explicitLeading bs.size v)
          try
            addDecl d
            pure d
          catch _ =>
            let d := mkDecl value
            addDecl d
            pure d
        | none =>
          let d := mkDecl value
          addDecl d
          pure d
      if !isThm then
        setReducibleAttribute name
        compileDecl decl (logErrors := false)
      let env ← getEnv
      let doc? ← match t.doc with
        | some d => pure (some d)
        | none => findDocString? env t.decl
      if let some doc := doc? then
        addDocStringCore name doc
      addDeclarationRangesFromSyntax name ref
      if t.headline then
        modifyEnv (GordieHowe.headlineExt.addEntry · name)
      done := done.push (t.decl, name, args)

end GordieHowe.Configuration.Template
