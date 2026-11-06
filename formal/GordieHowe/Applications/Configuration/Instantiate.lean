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

`at p` (after the arguments) states the theorems at the proof system `p`: a theorem `G` whose next
binder has `p`'s type (the configuration's proof systems) is stated at `p`, so its instance has no
such binder and names `p`. Its value is the instance at a free proof system, checked as without
`at`, applied to `p` through `id` at its own type, so the kernel compares nothing at `p`. A
definition keeps the binder, so its code reads the proof system at run time.

`renaming g₁ → h₁, …` (after the families) names the instance of the template with last name
component `gᵢ` as `N.hᵢ`.

A template's implicit and instance binders before an argument it takes are determined by
unification with the arguments (instances synthesized), as are instance binders before the
proof-system binder of `at p`.

Every instance is recorded: a later `instantiate_config` in the same namespace names an earlier
instance in its statements and values wherever the instance's template is applied to arguments
that match (first-order, or up to reducible unfolding and proof irrelevance) the earlier
instance's, its binders read off the match. A configuration built from records by a generic
definition (`Configuration.ofCertified`, its fields the generic templates at the records) so
states its headlines with the application's own instances. `folding [c₁, …]` (after the
renamings) names the definitions `cᵢ` likewise wherever their bodies appear.

Projections are reduced, besides those of the arguments, at constant instances of the
`@[config_record]` structures (`attribute [config_record] S` also marks an imported structure), and
through definitions whose value unfolds to a structure instance; a projection of such a
projection is reduced in turn.

`@[config_template keep_binders]` gives a definition's instance the binder kinds the command
writes (an implicit binder stays implicit), as a theorem's has. A definition instance's body is
exposed under the module system: its unfolding is its interface.

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
  /-- Whether a definition's instance keeps the kinds of `instantiate_config`'s binders (an
  implicit binder stays implicit), as a theorem's does. -/
  keepBinders : Bool := false
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

/-- `@[config_template]`, `@[config_template headline]`, `@[config_template keep_binders]`,
`@[config_template name]`, and their combinations in that order. -/
syntax (name := configTemplate) "config_template" (&" headline")? (&" keep_binders")?
  (ppSpace ident)? : attr

initialize registerBuiltinAttribute {
    name := `configTemplate
    descr := "a generic configuration statement instantiated by `instantiate_config`"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "@[config_template] must be global"
      let headline := !stx[1].isNone
      let keepBinders := !stx[2].isNone
      let target := if stx[3].isNone then decl.componentsRev.head! else stx[3][0].getId
      let doc ← findDocString? (← getEnv) decl
      modifyEnv (templateExt.addEntry ·
        { decl := decl, target := target, headline := headline, keepBinders := keepBinders,
          doc := doc })
  }

/-- An instance made by `instantiate_config`: the template, the instance, the number of the
command's binders, and the template's leading arguments with the binders abstracted (loose bound
variables, the last binder `0`). -/
structure InstanceEntry where
  /-- The template. -/
  decl : Name
  /-- The instance. -/
  name : Name
  /-- The number of the command's binders. -/
  nb : Nat
  /-- The template's leading arguments, the binders abstracted. -/
  args : Array Expr
  deriving Inhabited

/-- The instances of the environment, in the order they were made (imported modules first). A
later `instantiate_config` in the same namespace names them in its statements. -/
initialize instanceExt : SimplePersistentEnvExtension InstanceEntry (Array InstanceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- The `@[config_record]` structures: structures whose constant instances (`R.f` for a definition `R` whose
value unfolds to a structure instance) `instantiate_config` reduces to the field's value in the
statements of instances, as it does for its own arguments. -/
initialize configRecordExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun es => es.foldl (fun s a => a.foldl NameSet.insert s) {}
  }

/-- `@[config_record]` (module docstring of `configRecordExt`); it may be added to an imported
structure (`attribute [config_record] S`). -/
initialize registerBuiltinAttribute {
    name := `config_record
    descr := "a structure whose constant instances' projections `instantiate_config` reduces"
    add := fun decl _ kind => do
      unless kind == AttributeKind.global do
        throwError "@[config_record] must be global"
      unless isStructure (← getEnv) decl do
        throwError "@[config_record] applies only to structures: {decl}"
      modifyEnv (configRecordExt.addEntry · decl)
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

/-- **A definition's structure instance**: `e` unfolded (`unfoldDefinition?`, at most `fuel`
times, `whnfCore` after each step) until its head is a structure constructor. -/
partial def ctorOf? (e : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  let e ← whnfCore e
  if let .const c _ := e.getAppFn then
    if let some (.ctorInfo _) := (← getEnv).find? c then return some e
  if fuel == 0 then return none
  let some e' ← unfoldDefinition? e | return none
  ctorOf? e' (fuel - 1)

/-- Whether `s` is an instance whose projections are reduced: one of the records `recs`, or a
constant (applied) whose type is a `@[config_record]` structure. -/
def isRecordInstance (recs : Array Expr) (s : Expr) : MetaM Bool := do
  unless s.getAppFn.isConst do return false
  if recs.contains s then return true
  let ty ← whnfR (← inferType s)
  let .const n _ := ty.getAppFn | return false
  return (configRecordExt.getState (← getEnv)).contains n

/-- **A projection of a configuration record, reduced**: `S.f c x…` with `c` one of the records
`recs` or a constant instance of a `@[config_record]` structure (a definition, possibly applied,
whose value unfolds to a structure instance, through further definitions such as
`Configuration.ofCertified`) becomes the field's value applied to `x…`. A projection of such a
projection (`F.toFrontendCore.codec`) is reduced in turn. -/
partial def reduceConstProj? (recs : Array Expr) (e : Expr) : MetaM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? f | return none
  if info.fromClass then return none
  let args := e.getAppArgs
  if args.size ≤ info.numParams then return none
  let s := args[info.numParams]!
  let sv? ← if ← isRecordInstance recs s then ctorOf? s else
    match ← reduceConstProj? recs s with
    | some s' => ctorOf? s' 0
    | none => pure none
  let some sv := sv? | return none
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

/-- **First-order matching of an instance's arguments**: `p` (at binder depth `d`, its loose bound
variables from `d` on the `nb` holes, the last `0`) against `e`, extending the holes' assignment
`σ` (indexed by binder). -/
partial def matchPat (nb : Nat) (p e : Expr) (d : Nat) (σ : Array (Option Expr)) :
    Option (Array (Option Expr)) :=
  match p, e with
  | .bvar j, _ =>
    if j < d then (if e == .bvar j then some σ else none)
    else
      let h := j - d
      if h < nb then
        let k := nb - 1 - h
        if e.hasLooseBVars then none
        else match σ[k]! with
          | some v => if v == e then some σ else none
          | none => some (σ.set! k (some e))
      else none
  | .mdata _ p', _ => matchPat nb p' e d σ
  | _, .mdata _ e' => matchPat nb p e' d σ
  | .app f a, .app f' a' => (matchPat nb f f' d σ).bind fun σ => matchPat nb a a' d σ
  | .lam _ t b _, .lam _ t' b' _ =>
    (matchPat nb t t' d σ).bind fun σ => matchPat nb b b' (d + 1) σ
  | .forallE _ t b _, .forallE _ t' b' _ =>
    (matchPat nb t t' d σ).bind fun σ => matchPat nb b b' (d + 1) σ
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    ((matchPat nb t t' d σ).bind fun σ => matchPat nb v v' d σ).bind fun σ =>
      matchPat nb b b' (d + 1) σ
  | .proj s i x, .proj s' i' x' => if s == s' && i == i' then matchPat nb x x' d σ else none
  | _, _ => if !p.hasLooseBVars && p == e then some σ else none

/-- **An earlier instance at `x`**: `G a… y…` with `G` the instance's template and `a…` matching
its abstracted arguments becomes `N.g b… y…`, `b…` the matched binders. The arguments match
first-order, or else up to reducible unfolding and proof irrelevance (a definition's nested
proofs are abstracted into auxiliary lemmas, `_proof_n`, which only proof irrelevance relates). -/
def foldInstance? (done : Array InstanceEntry) (x : Expr) : MetaM (Option Expr) := do
  let .const g _ := x.getAppFn | return none
  let xs := x.getAppArgs
  for ent in done do
    if ent.decl == g && xs.size ≥ ent.args.size then
      let mut σ? : Option (Array (Option Expr)) := some (Array.replicate ent.nb none)
      for i in [0:ent.args.size] do
        σ? := σ?.bind fun σ => matchPat ent.nb ent.args[i]! xs[i]! 0 σ
      let rest := xs.extract ent.args.size xs.size
      if let some σ := σ? then
        if σ.all (·.isSome) then
          return some (mkAppN (.const ent.name []) (σ.map (·.get!) ++ rest))
      if x.hasLooseBVars then continue
      let r ← withNewMCtxDepth <| withReducible do
        let ms ← (List.range ent.nb).toArray.mapM fun _ => mkFreshExprMVar none
        let ok ← (List.range ent.args.size).allM fun i =>
          isDefEq (ent.args[i]!.instantiateRev ms) xs[i]!
        if !ok then return none
        let vs ← ms.mapM instantiateMVars
        if vs.any (·.hasMVar) then return none
        return some vs
      if let some vs := r then
        return some (mkAppN (.const ent.name []) (vs ++ rest))
  return none

/-- A lambda's body and its number of binders. -/
def lamBody : Expr → Nat → Nat × Expr
  | .lam _ _ b _, n => lamBody b (n + 1)
  | e, n => (n, e)

/-- **A folded definition at `x`** (`folding`): `x` with the head of the body of a definition `c`
that matches the body (first-order, or up to reducible unfolding, its parameters the holes)
becomes `c` at the matched parameters. -/
def foldDef? (folds : Array InstanceEntry) (x : Expr) : MetaM (Option Expr) := do
  for f in folds do
    let p := f.args[0]!
    unless p.getAppFn.isConst && p.getAppFn == x.getAppFn do continue
    if let some σ := matchPat f.nb p x 0 (Array.replicate f.nb none) then
      if σ.all (·.isSome) then
        return some (mkAppN (.const f.name []) (σ.map (·.get!)))
    if x.hasLooseBVars then continue
    let r ← withNewMCtxDepth <| withReducible do
      let ms ← (List.range f.nb).toArray.mapM fun _ => mkFreshExprMVar none
      unless ← isDefEq (p.instantiateRev ms) x do return none
      let vs ← ms.mapM instantiateMVars
      if vs.any (·.hasMVar) then return none
      return some vs
    if let some vs := r then
      return some (mkAppN (.const f.name []) vs)
  return none

/-- **The readable type of an instance** (module docstring): constant record projections reduced,
earlier instances (of this command and of earlier commands in the namespace) named, the
definitions `folds` folded. -/
def readable (ty : Expr) (lead : Array Expr) (done : Array InstanceEntry)
    (folds : Array InstanceEntry := #[]) : MetaM Expr := do
  let ty ← instantiateMVars ty
  Meta.transform ty (pre := fun x => do
    if let some x' ← foldInstance? done x then
      return .visit x'
    if let some x' ← reduceConstProj? lead x then
      return .visit x'
    return .continue) (post := fun x => do
    if let some x' ← foldDef? folds x then
      return .done x'
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
    (&" folding " "[" ident,+ "]")?
    (atomic((ppSpace bracketedBinder)+ " => "))? (ppSpace term:max)+ (" at " term:max)? : command

@[command_elab instantiateConfig]
def elabInstantiateConfig : CommandElab := fun stx => do
  let ns := stx[1].getId
  let fams := stx[4].getSepArgs.map (·.getId)
  let renames : Array (Name × Name) :=
    if stx[6].isNone then #[] else
      stx[6][1].getSepArgs.map fun p => (p[0].getId, p[2].getId)
  let foldStxs : Array Syntax := if stx[7].isNone then #[] else stx[7][2].getSepArgs
  let binderStxs : Array Syntax := if stx[8].isNone then #[] else stx[8][0].getArgs
  let argStxs := stx[9].getArgs
  let atStx? : Option Syntax := if stx[10].isNone then none else some stx[10][1]
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
    -- The proof system the theorems are stated at (`at p`): an argument of the theorems only.
    let pt? ← atStx?.mapM fun a => do
      let e ← Term.elabTerm a none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let mut done : Array InstanceEntry := #[]
    -- The instances of earlier commands in this namespace.
    let prior := (instanceExt.getState (← getEnv)).filter fun e => ns.isPrefixOf e.name
    -- The definitions to fold (`folding`): each one's body, its parameters the holes.
    let folds ← foldStxs.mapM fun f => do
      let n ← realizeGlobalConstNoOverloadWithInfo f
      let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
      let some v := ci.value? (allowOpaque := true) | throwError "{n} has no value"
      let (nb, body) := lamBody v 0
      pure ({ decl := .anonymous, name := n, nb := nb, args := #[body] } : InstanceEntry)
    for t in tmpls do
      let some ci := (← getEnv).find? t.decl | throwError "unknown template {t.decl}"
      -- The template's universe levels are fixed by the arguments (the record's universe).
      let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
      -- The arguments the template takes: for each leading binder in turn, the first remaining
      -- argument of its type.
      let mut args : Array Expr := #[]
      let mut rest := lead
      let mut tyT := ci.type.instantiateLevelParams ci.levelParams lvls
      -- The template's implicit and instance binders before its last matched argument are
      -- unified (instances synthesized).
      -- Instance binders after the last matched argument are synthesized, so that `at p` reaches
      -- the proof-system binder behind them.
      let mut pend : Array Expr := #[]
      let mut pendInst := true
      repeat
        let .forallE _ d b bi ← whnf tyT | break
        if bi != .default then
          let m ← mkFreshExprMVar d (if bi == .instImplicit then .synthetic else .natural)
          pend := pend.push m
          pendInst := pendInst && bi == .instImplicit
          tyT := b.instantiate1 m
          continue
        let some i ← rest.findIdxM? fun a => do isDefEq (← inferType a) d | break
        pendInst := true
        args := args ++ pend |>.push rest[i]!
        pend := #[]
        tyT := b.instantiate1 rest[i]!
        rest := rest.eraseIdx! i
      if !pend.isEmpty && pendInst then
        let ok ← pend.allM fun m => do
          match ← synthInstance? (← inferType m) with
          | some inst => m.mvarId!.assign inst; pure true
          | none => pure false
        if ok then args := args ++ pend
      for a in args do
        if let .mvar m := a then
          unless ← m.isAssigned do
            let some inst ← synthInstance? (← inferType a) | throwError
              "instantiate_config: cannot determine an implicit argument of {t.decl}"
            m.assign inst
      args ← args.mapM instantiateMVars
      let value := mkAppN (.const t.decl lvls) args
      let ty ← inferType value
      let ty ← readable ty lead (prior ++ done) folds
      -- `at p`: a theorem whose next binder has `p`'s type is stated at `p`, with no binder. Its
      -- value is the instance at a free point, `G a₁ … aₙ : ∀ C, T C` (checked with `C` free, as
      -- without `at`), applied to `p` through `id` at that type, so the kernel compares nothing at
      -- `p` and never unfolds it (its certificates). A definition keeps the binder.
      let atP ← match pt?, ← isProp ci.type, ty with
        | some pt, true, .forallE _ d b _ => do
          if ← isDefEq (← inferType pt) d then
            pure (some (b.instantiate1 pt, mkApp (mkApp2 (mkConst ``id [levelZero]) ty value) pt))
          else pure none
        | _, _, _ => pure none
      let (ty, value) := atP.getD (ty, value)
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
      -- The record projections of the value reduced and the earlier instances named, as in the
      -- type, so that the instance's code reads the configuration's own definitions (its IOP,
      -- transcript, simulator data) and not the record, whose soundness and honest-prover fields
      -- are not computable.
      let reduced ← reduced.mapM fun v => Meta.transform v (pre := fun x => do
        if let some x' ← foldInstance? (prior ++ done) x then return .visit x'
        if let some x' ← reduceConstProj? lead x then return .visit x'
        if let some x' ← unfoldConfigReduce? lead x then return .visit x'
        return .continue)
      let reduced ← reduced.mapM fun v => do instantiateMVars (← mkLambdaFVars bs v)
      let value ← instantiateMVars (← mkLambdaFVars bs value)
      if ty.hasMVar || value.hasMVar || ty.hasLevelMVar || value.hasLevelMVar then
        throwError "the instance of {t.decl} has unassigned metavariables"
      -- An imported theorem may be seen without its value (the module system), so a template is
      -- a theorem when its type is a proposition.
      let isThm ← isProp ci.type
      let (ty, value) :=
        if isThm || t.keepBinders then (ty, value)
        else (explicitLeading bs.size ty, explicitLeading bs.size value)
      let target := (renames.find? (·.1 == t.target)).map (·.2) |>.getD t.target
      let name := ns ++ target
      let cv : ConstantVal := { name := name, levelParams := [], type := ty }
      let mkDecl (value : Expr) : Declaration :=
        if isThm then
          .thmDecl { toConstantVal := cv, value := value, all := [name] }
        else
          .defnDecl (mkDefinitionValEx name [] ty value ReducibilityHints.abbrev
            DefinitionSafety.safe [name])
      -- The reduced value when the kernel accepts it, else `G a₁ … aₙ`. A definition's body is
      -- exposed under the module system: its unfolding is its interface, which later instances'
      -- statements (folded to it) and the kernel read.
      let decl ← match reduced with
        | some v =>
          let d := mkDecl (if t.keepBinders then v else explicitLeading bs.size v)
          try
            addDecl d (forceExpose := !isThm)
            pure d
          catch _ =>
            let d := mkDecl value
            addDecl d (forceExpose := !isThm)
            pure d
        | none =>
          let d := mkDecl value
          addDecl d (forceExpose := !isThm)
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
      if atP.isNone then
        let pats ← args.mapM fun a => do return (← instantiateMVars a).abstract bs
        let ent : InstanceEntry := { decl := t.decl, name := name, nb := bs.size, args := pats }
        done := done.push ent
        modifyEnv (instanceExt.addEntry · ent)

end GordieHowe.Configuration.Template
