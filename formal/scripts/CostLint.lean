-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-!
# Running-time lint for extractors and simulators

Every definition in the `GordieHowe` namespace whose type ends in one of the cost-bearing
types below (after the binders, with reducible definitions unfolded) must carry a docstring with
a "Running time" paragraph arguing that the procedure runs in polynomial time:

* `GordieHowe.IOP.Extractor`, a round-by-round extractor (CMS19 Definition 8.5; the docstring of
  `GordieHowe.IOP.Extractor`);
* `GordieHowe.IOP.IOP.Simulator`, an honest-verifier simulator of an IOP (the docstring of
  `GordieHowe.IOP.IOP.Simulator`);
* `GordieHowe.IOP.IOP.JointSimulator`, an honest-verifier simulator of an IOP that outputs the
  challenges with the view (CY24 Definition 23.1.8; the docstring of
  `GordieHowe.IOP.IOP.JointSimulator`);
* `GordieHowe.FieldProof.Shape.Simulator`, a simulator of one circuit proof's view;
* `Quantum.NIZK.Simulator`, a zero-knowledge simulator of a non-interactive argument in the
  quantum random-oracle model (the docstring of `Quantum.NIZK.Simulator`);
* `Quantum.NIZK.SimulatorProg`, a zero-knowledge simulator as a counted classical oracle program
  (the docstring of `Quantum.NIZK.SimulatorProg`);
* `GordieHowe.IOP.CausalExtractor`, a causal one-shot extractor of a series–parallel composition
  (the docstring of `GordieHowe.IOP.CausalExtractor`);
* `GordieHowe.IOP.CausalJointSimulator`, a joint simulator of a series–parallel composition (CY24
  Definition 23.1.8; the docstring of `GordieHowe.IOP.CausalJointSimulator`);
* `GordieHowe.NARG.ROM.OracleSampler`, the oracle simulator of an online extractor in the classical
  random-oracle model as a randomized algorithm (DFMS22 Definition 3.1; the docstring of
  `GordieHowe.NARG.ROM.OracleSampler`).

**Reductions** (section "Reductions" below): every definition in the `GordieHowe` namespace whose type
ends in an adversary type (`adversaryTypes`: the adversaries, algorithms and forgers of the model
and of the security games) and that takes an argument of an adversary type builds an adversary
from another, as a reduction does (a forger from a ring adversary, a WI adversary from an
anonymity adversary, the expanded adversary of CMS19 Proposition 8.11, an adversary followed by a
test). It must carry a "Running time" docstring paragraph and be computable or listed in
`knownNoncomputable`, unless it is listed in `notReductions` with the reason: the translations
that define the model's semantics or give an equivalent form of the same algorithm inside proofs
(the composition with a challenger, the dilation, the pure serial form).

The extraction procedures of other types (`extractorFunctions`: the database extractors, which
return a `Multiset`) are checked the same way, and every definition named like an extractor whose
result is a `Multiset`, `Option`, `List` or `Finset` must be listed there or exempted with a reason
(`notExtractors`). The configuration templates of `configProcedures` (the decoding of the
database extractor's queries, `queryDecoder`) are checked the same way at the template and at
every configuration's instance.

Structure projections, constructors, recursors, matchers and other auxiliary declarations are
skipped. An extractor or simulator written inline inside a statement is not a declaration and is
not seen by this lint.

The second check (section "Computability" below) requires every extractor, simulator and
decoder to be a computable definition, with the open exceptions listed in
`knownNoncomputable`.

The third check (section "Classical decisions passed to extractors" below) requires every
decision an extractor takes as an instance argument (the statement comparison of the database
extractor) to be computable where the extractor is applied, in the statements as well as in the
code: no application of an extractor procedure, or of a definition that uses one, takes a
classical `Decidable` instance.

The fourth check (section "Oracle simulators in statements" below) requires every oracle
simulator of the classical random-oracle model that a statement fixes to be the law of a computable
`GordieHowe.NARG.ROM.OracleSampler`.

Every name listed in `extractorFunctions`, `configProcedures`, `notExtractors` or
`knownNoncomputable` must be a declaration of the environment, so a renamed or removed declaration fails the lint instead of
dropping out of the checks.

Run by `scripts/check.sh` as `lake env lean scripts/CostLint.lean`; it fails with the list of
offending declarations. `COST_LINT_COMPUTABILITY=report` turns the computability failures into a
warning.
-/

open Lean Meta Elab Command

/-- The types whose definitions must document their running time. -/
def costTypes : List Name :=
  [``GordieHowe.IOP.Extractor, ``GordieHowe.IOP.IOP.Simulator, ``GordieHowe.IOP.IOP.JointSimulator,
    ``GordieHowe.FieldProof.Shape.Simulator,
    ``GordieHowe.NARG.SimulatorFn, ``GordieHowe.NARG.Simulator,
    ``GordieHowe.IOP.CausalExtractor, ``GordieHowe.IOP.CausalJointSimulator,
    ``GordieHowe.NARG.ROM.OracleSampler]

/-- **Extractor procedures of other types**: named extraction procedures whose type is not one of
`costTypes` (they return a `Multiset`, an `Option`, a witness), checked like the cost types: a
"Running time" docstring paragraph, and compiled code unless listed in `knownNoncomputable`. -/
def extractorFunctions : List Name :=
  [``GordieHowe.SPBCS.Base.dbExtract, ``GordieHowe.SPBCS.Base.targetedExtract,
    ``GordieHowe.SPBCS.dbExtract, ``GordieHowe.SPBCS.dbExtractBits,
    ``GordieHowe.SPBCS.targetedExtractor, ``GordieHowe.SPBCS.targetedExtractorOf,
    ``GordieHowe.SPBCS.targetedExtractorAt,
    ``GordieHowe.SPBCS.extractLabel, ``GordieHowe.SPBCS.extractLabelR]

/-- **Configuration templates checked like extractor procedures**: `@[config_template]`
definitions (`GordieHowe/Applications/Configuration/Instantiate.lean`) that are part of an
extractor's computation but have no cost-bearing type. The template and each configuration's
instance (a declaration of the `GordieHowe` namespace with the template's last name component)
are checked like `extractorFunctions`. -/
def configProcedures : List Name :=
  [``GordieHowe.Configuration.Common.queryDecoder]

/-- Whether `un` is an extractor procedure: listed in `extractorFunctions`, or a configuration
template of `configProcedures` or an instance of one. -/
def isExtractorProcedure (un : Name) : Bool :=
  extractorFunctions.contains un || configProcedures.any fun t =>
    un.getRoot == `GordieHowe && (match t, un with
      | .str _ a, .str _ b => a == b
      | _, _ => false)

/-- The result types under which a definition named like an extractor (its last name component
contains `xtract`) must be listed in `extractorFunctions` or in `notExtractors`. -/
def extractorResultTypes : List Name := [``Multiset, ``Option, ``List, ``Finset]

/-- **Definitions named like extractors that are not extractor procedures**, each with the reason. -/
def notExtractors : List (Name × String) :=
  [(`GordieHowe.SPBCS.extract, "a Merkle view read from a database (`GordieHowe/SPBCS/Merkle/Extract.lean`), a general \
      Merkle object with its lemmas; no extractor runs it")]

/-! ### Reductions -/

/-- **The adversary types**: the adversaries, algorithms and forgers of the model and of the
security games. A definition whose type ends in one of them and that takes an argument of one of
them is a reduction (`reductionDefs`). -/
def adversaryTypes : List Name :=
  [``GordieHowe.Quantum.Alg, ``GordieHowe.Quantum.IAlg, ``GordieHowe.Quantum.KindAlg, ``GordieHowe.Quantum.AdaptiveIAlg,
    ``GordieHowe.Quantum.QueryAlg, ``GordieHowe.Quantum.Distinguisher,
    ``GordieHowe.Quantum.OracleAlg, ``GordieHowe.Quantum.MixedAlg, ``GordieHowe.SPBCS.Base.SimExtractionAdversary,
    ``GordieHowe.SPBCS.Base.WIAdversary, ``GordieHowe.ROM.Alg, ``GordieHowe.ROM.Adversary,
    ``GordieHowe.Ring.ExtractionForger, ``GordieHowe.Ring.RingAdversary, ``GordieHowe.Ring.AnonAdversary,
    ``GordieHowe.Ring.KeyedAnonAdversary]

/-- **Constructions on adversaries that are not reductions**, each with the reason: the
translations that define the semantics of the model and the
equivalent forms of the same algorithm used inside proofs. They do not build an adversary that
another party runs, so they carry no running-time obligation. -/
def notReductions : List (Name × String) :=
  [(`GordieHowe.Quantum.IAlg.compose, "the semantics of an interactive adversary with a challenger \
      (the definition of the model)"),
    (`GordieHowe.Quantum.IAlg.composeOut, "`IAlg.compose` with the classical registers as output, \
      a proof device"),
    (`GordieHowe.Quantum.IAlg.toKindAlg, "the adversary with its slot counter, the internal form of \
      `IAlg.compose`"),
    (`GordieHowe.Quantum.AdaptiveIAlg.compose, "the semantics of an adversary with run-time kinds \
      with a challenger (the definition of the model)"),
    (`GordieHowe.Quantum.AdaptiveIAlg.toKindAlg, "the adversary with its query counter, the internal \
      form of `AdaptiveIAlg.compose`"),
    (`GordieHowe.Quantum.KindAlg.composeBoth, "the semantics of an adversary with a kind register with \
      a challenger"),
    (`GordieHowe.Quantum.KindAlg.composeBothOut, "`KindAlg.composeBoth` with the classical registers as \
      output, a proof device"),
    (`GordieHowe.Quantum.AdaptiveIAlg.toTPKindAlg, "the trace-preserving form of the adversary with its \
      query counter, the same run on the branches that have not ended \
      (`AdaptiveIAlg.intertwined_fullCircBoth`), a proof device"),
    (`GordieHowe.Quantum.KindAlg.gameMixed, "the mixed game of the deferred-measurement bridge, a proof \
      device"),
    (`GordieHowe.Quantum.KindAlg.dilate, "the dilated distinguisher of the deferred-measurement bridge, \
      the same algorithm (`IAlg.compose_eq_pureGame`)"),
    (`GordieHowe.Quantum.MixedAlg.dilate, "the Stinespring dilation, the same algorithm as a pure one"),
    (`GordieHowe.Quantum.Distinguisher.withPostSlots, "the same distinguisher with its post phase of \
      query batches as query slots (`Distinguisher.acceptProb_withPostSlots`), a proof device"),
    (`GordieHowe.Quantum.Distinguisher.mapReq, "the same distinguisher with its request register \
      relabelled (`Distinguisher.acceptProb_mapReq`), a proof device"),
    (`GordieHowe.Quantum.MixedAlg.dilateCoh, "the Stinespring dilation without the final measurement, \
      the same algorithm as a pure one (`Alg.outLaw_toQueryAlgCoh`)"),
    (`GordieHowe.Quantum.Alg.toQueryAlgCoh, "the coherent pure serial form of the same algorithm \
      (`Alg.realLaw_toQueryAlgCoh`)"),
    (`GordieHowe.Quantum.KindAlg.toAdaptive, "the same algorithm with a query budget, an equivalent form \
      (`mgRun_toAdaptive`)"),
    (`GordieHowe.Quantum.IAlg.toAdaptive, "the fixed-schedule algorithm as a run-time adaptive one, the \
      same outcome law (`IAlg.realLaw_compose_toAdaptive`)"),
    (`GordieHowe.Quantum.AdaptiveIAlg.tpRun, "the trace-preserving run of the adversary with the \
      challenger that answers nothing, the real run of run-time knowledge soundness"),
    (`GordieHowe.Quantum.AdaptiveIAlg.abortAlg, "the adversary with an abort on an over-budget call, the \
      same outcome law for an adversary within its budget (`WithinBudget.outLaw_compose_abortAlg`)"),
    (`GordieHowe.Quantum.Alg.halting, "the same algorithm with a halting flag, an equivalent form"),
    (`GordieHowe.Quantum.QueryAlg.mapOut, "the same algorithm with its output relabelled"),
    (`GordieHowe.Quantum.QueryAlg.toOracleAlg, "the same algorithm as an oracle algorithm of AHU19"),
    (`GordieHowe.Quantum.OracleAlg.relabel, "the same algorithm on relabelled basis states"),
    (`GordieHowe.Quantum.O2HSetting.dilAlg, "the dilation of a mixed algorithm in the O2H statement, \
      the same algorithm"),
    (`GordieHowe.Quantum.Distinguisher.gameAlg, "the game as an oracle algorithm, the same run")]

/-- The reductions: the definitions in the `GordieHowe` namespace whose type ends in one of
`adversaryTypes` and that take an argument of one of `adversaryTypes`, outside `notReductions`. -/
def reductionDefs : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe do continue
    unless ci matches .defnInfo _ do continue
    if un.isInternal || isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n ||
        isMatcherCore env n || un.components.contains `Experiments then
      continue
    if (notReductions.map (·.1)).contains un then continue
    let isRed ← forallTelescopeReducing ci.type fun xs body => do
      let body ← whnfR body
      unless adversaryTypes.any body.getAppFn.isConstOf do return false
      for x in xs do
        let t ← forallTelescopeReducing (← inferType x) fun _ b => whnfR b
        if adversaryTypes.any t.getAppFn.isConstOf then return true
      return false
    if isRed then out := out.push un
  return out

/-- The reductions without a "Running time" docstring paragraph. -/
def undocumentedReductions (reds : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  reds.filterM fun n => do
    let doc ← findDocString? env n
    return !(match doc with
      | some d => decide ((d.splitOn "Running time").length > 1)
      | none => false)

/-- The definitions named like extractors with a result type of `extractorResultTypes` that are in
neither `extractorFunctions` nor `notExtractors`. -/
def unlistedExtractorFunctions : MetaM (Array Name) := do
  let env ← getEnv
  let mut bad := #[]
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe || un.getRoot == `Quantum do continue
    unless ci matches .defnInfo _ do continue
    if un.isInternal || env.isProjectionFn n || isMatcherCore env n ||
        un.components.contains `Experiments then
      continue
    let last := match un with | .str _ s => s | _ => ""
    unless (last.splitOn "xtract").length > 1 do continue
    if isExtractorProcedure un || (notExtractors.map (·.1)).contains un then continue
    let head? ← forallTelescopeReducing ci.type fun _ body => do
      let body ← whnfR body
      pure (extractorResultTypes.find? body.getAppFn.isConstOf)
    if head?.isSome then bad := bad.push un
  return bad

/-- The definitions in the `GordieHowe` namespace of a type in `costTypes` without a
"Running time" docstring paragraph, and the number of such definitions checked, per type. -/
def undocumentedCostDefs : MetaM (Array Name × List (Name × Nat)) := do
  let env ← getEnv
  let mut bad := #[]
  let mut checked : List (Name × Nat) := (costTypes ++ [`extractorFunctions]).map (·, 0)
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe || un.getRoot == `Quantum do continue
    unless ci matches .defnInfo _ do continue
    if un.isInternal || isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n ||
        isMatcherCore env n then
      continue
    let head? ← forallTelescopeReducing ci.type fun _ body => do
      let body ← whnfR body
      pure (costTypes.find? body.getAppFn.isConstOf)
    let head? := if isExtractorProcedure un then some `extractorFunctions else head?
    let some head := head? | continue
    checked := checked.map fun (t, k) => if t == head then (t, k + 1) else (t, k)
    let doc ← findDocString? env n
    let documented := match doc with
      | some d => decide ((d.splitOn "Running time").length > 1)
      | none => false
    unless documented do
      bad := bad.push un
  return (bad, checked)

/-! ### Computability

Every extractor, simulator and decoder is a computable definition: it has compiled code, and no
constant it uses outside types and proofs is `noncomputable` or an axiom (`Classical.choice`
behind `Classical.choose`, `Classical.dec`, `Classical.arbitrary`). Checked for

* every definition whose type ends in one of `computableTypes` (the cost-bearing types, the
  message decoders `GordieHowe.IOP.MessageView.Decoder`, and the data-only simulator structures
  `IOP.TranscriptSim`, `CommitProve.Sim`, `FieldProof.Sim`, `TreeFieldProof.SimData`,
  `TreeFork.SimData`, `IOP.SimData`, `MultiCircuitIOP.SimData`): it must have compiled code;
* every definition whose type ends in one of the interface structures of `computableFields`:
  the value it gives the extractor and decoder fields (`CommitProve.extract`, `AppPhase.extract`,
  `CircuitShape.ext`) uses no `noncomputable` constant and no axiom outside types and proofs.
  The other fields of these structures (the proofs) are not checked.
-/

/-- The types whose definitions must have compiled code: the cost-bearing types, the message
decoders, and the data-only simulator structures (each honest prover takes its simulator as a
parameter, so a simulator is a definition of one of these types). -/
def computableTypes : List Name :=
  costTypes ++ [``GordieHowe.IOP.MessageView.Decoder, ``GordieHowe.IOP.TranscriptSim,
    ``GordieHowe.FieldProof.CommitProve.Sim, ``GordieHowe.FieldProof.Sim,
    ``GordieHowe.RingSwitching.TreeFieldProof.SimData, ``GordieHowe.TreeFork.SimData,
    ``GordieHowe.RealizedProgram.ProofSystem.IOP.SimData, ``GordieHowe.MultiCircuitIOP.SimData]

/-- The interface structures and their extractor, decoder and simulator fields. -/
def computableFields : List (Name × List Name) :=
  [(``GordieHowe.FieldProof.CommitProve, [`extract]),
    (``GordieHowe.RealizedProgram.ProofSystem.PhaseStep, [`extract]), (``GordieHowe.FieldProof.Shape, [`ext])]

/-- Whether the compiler rejects a use of `c` in a computationally relevant position: a
`noncomputable` constant or an axiom (`Quot` primitives, `extern`, `implemented_by`,
`macro_inline` and `csimp`-replaced constants excepted). -/
def rejectedByCompiler (env : Environment) (c : Name) : Bool :=
  if c matches ``Quot.mk | ``Quot.lift | ``Quot.ind then false
  else if isExtern env c || (Compiler.getImplementedBy? env c).isSome ||
      Compiler.hasMacroInlineAttribute env c ||
      ((Compiler.CSimp.ext.getState env).map.find? c).isSome then false
  else isNoncomputable env c || isNoncomputable env (Compiler.mkUnsafeRecName c) ||
    (env.find? c matches some (.axiomInfo _))

/-- The constants an expression uses in computationally relevant positions: types, proofs and
type formers are skipped. -/
partial def relevantConstants (e : Expr) : StateT NameSet MetaM Unit := do
  let e := e.headBeta
  if (← (do pure ((← isProof e) || (← isType e))) <|> pure false) then return
  match e with
  | .lam .. => lambdaTelescope e fun _ b => relevantConstants b
  | .letE _ t v b _ => do
    relevantConstants v
    withLetDecl `x t v fun x => relevantConstants (b.instantiate1 x)
  | .mdata _ b => relevantConstants b
  | .proj _ _ b => relevantConstants b
  | .app .. => do
    let env ← getEnv
    -- The parameters of a constructor, a projection or a `casesOn`/matcher are erased.
    let skip ← match e.getAppFn with
      | .const c _ => do
        modify (·.insert c)
        if let some info := env.getProjectionFnInfo? c then pure info.numParams
        else if let some (.ctorInfo info) := env.find? c then pure info.numParams
        else if let some info ← getMatcherInfo? c then pure (info.numParams + 1)
        else if isCasesOnRecursor env c then
          match env.find? c.getPrefix with
          | some (.inductInfo info) => pure (info.numParams + 1)
          | _ => pure 0
        else pure 0
      | f => do relevantConstants f; pure 0
    for a in e.getAppArgs[skip:] do
      try relevantConstants a catch _ => pure ()
  | .const c _ => modify (·.insert c)
  | _ => pure ()

/-- The constants of `e` the compiler rejects. -/
def rejectedConstants (e : Expr) : MetaM (List Name) := do
  let env ← getEnv
  let (_, s) ← (relevantConstants e).run {}
  return s.toList.filter (rejectedByCompiler env)

/-- The constants the compiler rejects in the value a definition `d` (applied to the binders `xs`)
gives the field `field` of the structure `S`, found by unfolding `d` until a constructor of `S`
appears. A definition by cases on its arguments (a stuck matcher application) is followed into
every alternative, and the rejected constants of all alternatives are collected. `none` when
some alternative reaches no constructor. -/
partial def fieldRejected? (S : Name) (field : Name) (e : Expr) : MetaM (Option (List Name)) := do
  let env ← getEnv
  let some info := getStructureInfo? env S | return none
  let some idx := info.fieldNames.idxOf? field | return none
  let ctor := (getStructureCtor env S).name
  let some (.ctorInfo ctorInfo) := env.find? ctor | return none
  let rec go (e : Expr) (fuel : Nat) : MetaM (Option (List Name)) := do
    if fuel = 0 then return none
    let e ← whnfCore e
    if e.getAppFn.isConstOf ctor then
      let some v := e.getArg? (ctorInfo.numParams + idx) | return none
      return some (← rejectedConstants v)
    if let some mapp ← matchMatcherApp? e then
      let mut acc := []
      for alt in mapp.alts do
        let r ← lambdaTelescope alt fun _ body => go (mkAppN body mapp.remaining) (fuel - 1)
        let some r := r | return none
        acc := acc ++ r
      return some acc
    match ← unfoldDefinition? e with
    | some e' => go e' (fuel - 1)
    | none => return none
  go e 32

/-- The computability failures: definitions of a type in `computableTypes` without compiled
code (and the reductions without compiled code), and interface definitions whose extractor,
decoder or simulator fields use rejected
constants (or whose fields cannot be found and that have no compiled code). -/
def computabilityFailures (reductions : Array Name) : MetaM (Array (Name × String) × Nat) := do
  let env ← getEnv
  let mut bad := #[]
  let mut checked := 0
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe || un.getRoot == `Quantum do continue
    unless ci matches .defnInfo _ do continue
    if un.isInternal || isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n ||
        isMatcherCore env n || (un.getPrefix.getRoot == `GordieHowe && un.components.contains `Experiments) then
      continue
    let hasIR := (IR.findEnvDecl env n).isSome
    let res ← forallTelescopeReducing ci.type fun xs body => do
      let body ← whnfR body
      if computableTypes.any body.getAppFn.isConstOf || isExtractorProcedure un ||
          reductions.contains un then
        return some (if hasIR then [] else [(un, s!"{un}: no compiled code")])
      let some (S, fields) := computableFields.find? (body.getAppFn.isConstOf ·.1) | return none
      let lvls := ci.levelParams.map Level.param
      let mut out := []
      for f in fields do
        match ← fieldRejected? S f (mkAppN (.const n lvls) xs) with
        | some rej =>
          unless rej.isEmpty do out := out ++ [(un, s!"{un}.{f}: uses {rej}")]
        | none => unless hasIR do
            out := out ++ [(un, s!"{un}.{f}: field not found, no compiled code")]
      return some out
    let some msgs := res | continue
    checked := checked + 1
    bad := bad ++ msgs.toArray
  return (bad, checked)

/-- Whether the computability check only reports (the environment variable
`COST_LINT_COMPUTABILITY=report`) instead of failing. -/
def computabilityReportOnly : IO Bool := do
  return (← IO.getEnv "COST_LINT_COMPUTABILITY") == some "report"

/-- The reason a quantum reduction has no compiled code: its states, Kraus operators and unitaries
are matrices over Mathlib's `ℂ`, whose real parts are Cauchy sequences without compiled
arithmetic; the classical part of the construction (the expansion's queries, the copies) is
explicit. -/
def quantumReduction : String :=
  "a quantum algorithm: its states, Kraus operators and unitaries are complex matrices, and \
  Mathlib's `ℂ` has no compiled arithmetic; the classical part of the construction is explicit"

/-- **The known noncomputable extractors, simulators and decoders**, each with the reason it
is not yet computable. The check fails on a
failure not listed here and on a listed definition that has become computable (remove it from
the list), so the list records the open work exactly. -/
def knownNoncomputable : List (Name × String) :=
  [
    (`GordieHowe.SPBCS.extractLabelR,
      "a device of the proof that makes the label type finite: it tests membership of `extractLabel` \
      (computable) in its range over the basis states of the simulated registers of the quantum \
      algorithm `𝒜_E` (`MergeModel.labelRange`), and that range reads the register type's \
      enumeration and the output map (`SPModel.pureCtrl`) of the quantum algorithm \
      `SPModel.pureWithTest`, fields of a structure defined over Mathlib's complex matrices; it \
      changes no outcome of the measurement"),
    (`GordieHowe.Quantum.AdaptiveIAlg.withTest, quantumReduction),
    (`GordieHowe.SPBCS.Base.pureWithTest, quantumReduction),
    (`GordieHowe.SPBCS.extAt, quantumReduction),
    (`GordieHowe.SPBCS.extAdv, quantumReduction),
    (`GordieHowe.SPBCS.extRun, quantumReduction),
    (`GordieHowe.SPBCS.extRunFull, quantumReduction),
    (`GordieHowe.SPBCS.simRun, quantumReduction),
    (`GordieHowe.SPBCS.simRunModel, quantumReduction),
    (`GordieHowe.QROM.expandAdv, quantumReduction),
    (`GordieHowe.QROM.expandAt, quantumReduction),
    (`GordieHowe.NARG.QROM.Verifier.expandedOpt, quantumReduction),
    (`GordieHowe.SPBCS.QROM.extAdvVia, quantumReduction),
    (`GordieHowe.SPBCS.Base.SimExtractionAdversary.withTest, quantumReduction)]

/-! ### Classical decisions passed to extractors

An extractor procedure's own code is compiled (section "Computability"), so it contains no
classical decision. A decision it takes as an instance argument (the `DecidableEq X` of
`SPBCS.dbExtract`, which compares the recorded statements with the one it extracts at) is
supplied where the extractor is applied, and in a statement no compiler checks it: under
`open Classical` it is `Classical.propDecidable`. This check covers those arguments.

The decision positions of a definition are the positions of its instance binders of a decision
type (`Decidable`, `DecidableEq`, `DecidablePred`, `DecidableRel`, after the binders); a decision
position is used when its bound variable occurs in the value other than at an unused decision
position of an application (`usedPositions`, a greatest fixed point; an included section
instance that the value only passes on to definitions ignoring it is unused). The reaching
positions of a definition are the decision positions whose value reaches an extractor: every used
decision position of an extractor procedure (outside `knownNoncomputable`: a procedure listed there
has no compiled code, so a classical decision it reads adds no exception; `extractLabelR` reads the
simulator's coins through the quantum algorithm's register enumeration), and a decision position of another definition whose
bound variable occurs, in its value, in an argument at a reaching position of an application
(`SPBCS.WeakOnlineSimulationExtractable` passes its `DecidableEq X` to `dbExtract`; its decision on
the simulator's coins reaches no extractor). They are computed as a least fixed
point over the definitions of the `GordieHowe` and `Quantum` namespaces. At every application in
the type of a declaration of the `GordieHowe` namespace, or in the value of a definition that
applies a definition with reaching positions, the argument at each reaching position must use no
constant the compiler rejects (`rejectedConstants`). -/

/-- The positions of the instance binders of a type whose type is a decision, among its leading
binders read without unfolding (the positions of an application's arguments). -/
def decisionBinders (ty : Expr) : MetaM (Array Nat) :=
  forallTelescope ty fun xs _ => do
    let mut out := #[]
    for h : i in [:xs.size] do
      let x := xs[i]
      unless (← x.fvarId!.getBinderInfo) == .instImplicit do continue
      let isDec ← (forallTelescopeReducing (← inferType x) fun _ b => do
        return (← whnfR b).isAppOf ``Decidable) <|> pure false
      if isDec then out := out.push i
    return out

/-- Runs `f` on every argument of `e` at a reaching position (`m`) of an application, with the
applied constant, in the local context of the argument. -/
def forReachingArgs (m : NameMap (Array Nat)) (e : Expr) (f : Name → Expr → MetaM Unit) :
    MetaM Unit :=
  forEachExpr' e fun sub => do
    let .const c _ := sub.getAppFn | return true
    let some idx := m.find? c | return true
    let args := sub.getAppArgs
    for i in idx do
      if h : i < args.size then f c args[i]
    return true

/-- The definitions of the `GordieHowe` and `Quantum` namespaces: name, user name, type, value and
the constants the value uses. -/
def namespaceDefs : MetaM (Array (Name × Name × Expr × Expr × Array Name)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe || un.getRoot == `Quantum do continue
    let .defnInfo d := ci | continue
    if un.isInternal || un.components.contains `Experiments then continue
    out := out.push (n, un, d.type, d.value, d.value.getUsedConstants)
  return out

/-- The decision types' heads: a type mentioning none of them is not a decision type. -/
def decisionHeads : List Name := [``Decidable, ``DecidableEq, ``DecidablePred, ``DecidableRel]

/-- The decision binder positions of every definition of `defs` whose type has some. -/
def decisionPositions (defs : Array (Name × Name × Expr × Expr × Array Name)) :
    MetaM (NameMap (Array Nat)) := do
  let mut m : NameMap (Array Nat) := {}
  for (n, _, ty, _, _) in defs do
    unless ty.getUsedConstants.any decisionHeads.contains do continue
    let idx ← (decisionBinders ty) <|> pure #[]
    unless idx.isEmpty do m := m.insert n idx
  return m

/-- The positions of the leading binders of a type whose domain is a universe (type arguments,
which are erased), read syntactically. -/
def typeBinders (ty : Expr) : Array Nat := Id.run do
  let mut out := #[]
  let mut e := ty
  let mut i := 0
  while e.isForall do
    if e.bindingDomain!.isSort then out := out.push i
    e := e.bindingBody!
    i := i + 1
  return out

/-- The field `S.f` of `x` when `x` is an application of a definition whose value, applied to the
arguments, is a constructor application of `S`: the projection read through the definition. -/
def projectThroughDef? (env : Environment) (info : ProjectionFunctionInfo) (x : Expr) :
    Option Expr := do
  let .const c lvls := x.getAppFn | none
  let some ci@(.defnInfo _) := env.find? c | none
  let v := (ci.instantiateValueLevelParams! lvls).beta x.getAppArgs
  let .const ctor _ := v.getAppFn | none
  guard (ctor == info.ctorName)
  v.getAppArgs[info.numParams + info.i]?

/-- Whether the free variable `fv` occurs in `e` in a computationally relevant position: not in an
argument at a type position (`typeBinders`) or at a decision position (`decs`) that the applied
definition does not use (absent from `used`), and, under a projection of an application of a
definition that unfolds to a constructor, only in the projected field. -/
partial def occursUsed (env : Environment) (decs used : NameMap (Array Nat)) (fv : FVarId)
    (e : Expr) : Bool :=
  if !e.hasFVar then false else
  match e with
  | .fvar f => f == fv
  | .app .. =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const c _ =>
      let projected := do
        let info ← env.getProjectionFnInfo? c
        let x ← args[info.numParams]?
        let field ← projectThroughDef? env info x
        pure (mkAppN field (args.extract (info.numParams + 1) args.size))
      match projected with
      | some e' => occursUsed env decs used fv e'
      | none =>
        let skip := (decs.find? c).getD #[]
        let u := (used.find? c).getD #[]
        let tys := match env.find? c with
          | some ci => typeBinders ci.type
          | none => #[]
        (List.range args.size).any fun i =>
          if tys.contains i || (skip.contains i && !u.contains i) then false
          else occursUsed env decs used fv args[i]!
    | f => occursUsed env decs used fv f || args.any (occursUsed env decs used fv)
  | .lam _ t b _ | .forallE _ t b _ =>
    occursUsed env decs used fv t || occursUsed env decs used fv b
  | .letE _ t v b _ =>
    occursUsed env decs used fv t || occursUsed env decs used fv v ||
      occursUsed env decs used fv b
  | .mdata _ b | .proj _ _ b => occursUsed env decs used fv b
  | _ => false

/-- **The used decision positions**: the decision binder positions of each definition whose bound
variable occurs in its value other than at an unused position of an application, as the greatest
fixed point (a decision passed only to definitions that ignore it is unused; a constant outside
`defs` uses every argument). -/
def usedPositions (defs : Array (Name × Name × Expr × Expr × Array Name))
    (decs : NameMap (Array Nat)) : MetaM (NameMap (Array Nat)) := do
  let mut used := decs
  let mut changed := true
  while changed do
    changed := false
    for (n, _, _, v, _) in defs do
      let some old := used.find? n | continue
      if old.isEmpty then continue
      let cur := used
      let env ← getEnv
      let new ← lambdaTelescope v fun xs body => pure <| old.filter fun i =>
        if h : i < xs.size then occursUsed env decs cur xs[i].fvarId! body else true
      if new.size < old.size then
        used := used.insert n new
        changed := true
  return used

/-- **The reaching positions** (section docstring) of every definition that has some: the used
decision positions of the extractor procedures outside `knownNoncomputable`, and the positions of other definitions whose
bound variable occurs in an argument at a reaching position of an application in their value. -/
def reachingPositions (defs : Array (Name × Name × Expr × Expr × Array Name)) :
    MetaM (NameMap (Array Nat)) := do
  let decs ← decisionPositions defs
  let used ← usedPositions defs decs
  let mut m : NameMap (Array Nat) := {}
  for (n, un, _, _, _) in defs do
    if isExtractorProcedure un && !(knownNoncomputable.map (·.1)).contains un then
      let idx := (used.find? n).getD #[]
      unless idx.isEmpty do m := m.insert n idx
  let mut changed := true
  while changed do
    changed := false
    for (n, un, _, v, usedConsts) in defs do
      if isExtractorProcedure un then continue
      unless usedConsts.any m.contains do continue
      let some ds := decs.find? n | continue
      let old := (m.find? n).getD #[]
      let reached ← lambdaTelescope v fun xs body => do
        let occ ← IO.mkRef ({} : FVarIdSet)
        forReachingArgs m body fun _ a =>
          occ.modify fun s => (collectFVars {} a).fvarIds.foldl (·.insert ·) s
        let occ ← occ.get
        return ds.filter fun i => if h : i < xs.size then occ.contains xs[i].fvarId! else false
      if reached.size > old.size then
        m := m.insert n reached
        changed := true
  return m

/-- The applications at a reaching position of a decision the compiler rejects: the declaration
(of the `GordieHowe` namespace, in its type, or in its value for a definition that applies a
definition with reaching positions), the applied constant and the rejected constants; and the
number of definitions with reaching positions. -/
def classicalExtractorDecisions : MetaM (Array (Name × Name × List Name) × Nat) := do
  let env ← getEnv
  let defs ← namespaceDefs
  let m ← reachingPositions defs
  let bad ← IO.mkRef #[]
  let check (un : Name) (e : Expr) : MetaM Unit :=
    forReachingArgs m e fun c a => do
      let rej ← (rejectedConstants a) <|> pure []
      unless rej.isEmpty do
        bad.modify fun b =>
          let entry := (un, (privateToUserName? c).getD c, rej)
          if b.contains entry then b else b.push entry
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe do continue
    if un.components.contains `Experiments then continue
    check un ci.type
  for (_, un, _, v, used) in defs do
    if used.any m.contains then check un v
  return (← bad.get, m.size)

/-! ### Oracle simulators in statements

An online extractor of the classical random-oracle model is an oracle simulator and an extractor
reading the simulator's final state (`GordieHowe.NARG.ROM.Adversary.OnlineExtracts`, DFMS22
Definition 3.1). The extractor is an extractor procedure (`extractorFunctions`). The simulator is a
`GordieHowe.NARG.ROM.OracleSim`, given by its laws, which have no compiled code; a statement fixes
it as the law (`GordieHowe.NARG.ROM.OracleSampler.law`) of a randomized algorithm, a definition of
the cost type `GordieHowe.NARG.ROM.OracleSampler` with compiled code (section "Computability").

The `OracleSim` positions of a declaration of the `GordieHowe` namespace are the positions of its
binders whose type is an `OracleSim`. In the type of every declaration of the `GordieHowe`
namespace, the argument at each `OracleSim` position of an application is a local variable (a
statement about every simulator) or `OracleSampler.law s`, where `s` uses no constant the compiler
rejects (`rejectedConstants`). -/

/-- The `OracleSim` positions (section docstring) of every declaration of the `GordieHowe`
namespace that has some. -/
def oracleSimPositions : MetaM (NameMap (Array Nat)) := do
  let env ← getEnv
  let mut m : NameMap (Array Nat) := {}
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe do continue
    unless ci.type.getUsedConstants.contains ``GordieHowe.NARG.ROM.OracleSim do continue
    let idx ← (forallTelescope ci.type fun xs _ => do
      let mut out := #[]
      for h : i in [:xs.size] do
        let t ← whnfR (← inferType xs[i])
        if t.isAppOf ``GordieHowe.NARG.ROM.OracleSim then out := out.push i
      return out) <|> pure #[]
    unless idx.isEmpty do m := m.insert n idx
  return m

/-- Runs `f` on every application in `e`, with the bound variables of binders and `let`s as local
variables. -/
partial def forEachApp (f : Expr → MetaM Unit) : Expr → MetaM Unit
  | e@(.app ..) => do
    f e
    forEachApp f e.getAppFn
    for a in e.getAppArgs do forEachApp f a
  | .forallE n t b bi => do
    forEachApp f t
    withLocalDecl n bi t fun x => forEachApp f (b.instantiate1 x)
  | .lam n t b bi => do
    forEachApp f t
    withLocalDecl n bi t fun x => forEachApp f (b.instantiate1 x)
  | .letE n t v b _ => do
    forEachApp f t
    forEachApp f v
    withLetDecl n t v fun x => forEachApp f (b.instantiate1 x)
  | .mdata _ b | .proj _ _ b => forEachApp f b
  | _ => pure ()

/-- The arguments at an `OracleSim` position, in the type of a declaration of the `GordieHowe`
namespace, that are neither a local variable nor the law of a sampler using only constants the
compiler accepts: the declaration, the applied constant and the reason; and the number of
arguments checked. -/
def oracleSimFailures : MetaM (Array (Name × Name × String) × Nat) := do
  let env ← getEnv
  let m ← oracleSimPositions
  let bad ← IO.mkRef #[]
  let checked ← IO.mkRef 0
  for (n, ci) in env.constants.toList do
    let un := (privateToUserName? n).getD n
    unless un.getRoot == `GordieHowe do continue
    if un.components.contains `Experiments then continue
    unless ci.type.getUsedConstants.any m.contains do continue
    let visit (e : Expr) : MetaM Unit := do
      let .const c _ := e.getAppFn | return
      let some idx := m.find? c | return
      let args := e.getAppArgs
      for i in idx do
        let some a := args[i]? | continue
        let a ← instantiateMVars a
        checked.modify (· + 1)
        if a.isFVar then continue
        let report (why : String) : MetaM Unit := bad.modify fun b =>
          let entry := (un, (privateToUserName? c).getD c, why)
          if b.contains entry then b else b.push entry
        if a.isAppOfArity ``GordieHowe.NARG.ROM.OracleSampler.law 3 then
          let rej ← (rejectedConstants a.appArg!) <|> pure []
          unless rej.isEmpty do report s!"the sampler uses {rej}"
        else
          report s!"{← ppExpr a} is not the law of an `OracleSampler`"
    forEachApp visit ci.type
  return (← bad.get, ← checked.get)

/-- The names listed in `extractorFunctions`, `notExtractors` and `knownNoncomputable` that are not
declarations of the environment, and the fields `S.f` listed in `computableFields` that are not
fields of the structure `S`. A listed name that is renamed or removed would otherwise silently
drop out of the checks. -/
def missingListedNames : MetaM (List Name) := do
  let env ← getEnv
  let listed := extractorFunctions ++ configProcedures ++ notExtractors.map (·.1) ++
    knownNoncomputable.map (·.1) ++ notReductions.map (·.1)
  let fields := computableFields.flatMap fun (S, fs) =>
    (fs.filter fun f => !(getStructureInfo? env S).any (·.fieldNames.contains f)).map (S ++ ·)
  return listed.filter (fun n => !env.contains n) ++ fields

run_cmd liftTermElabM do
  let missing ← missingListedNames
  unless missing.isEmpty do
    throwError m!"cost lint: {missing.length} name(s) listed in `extractorFunctions`, \
      `notExtractors` or `knownNoncomputable` are not declarations, or listed in \
      `computableFields` are not fields of their structure: {missing}"
  logInfo m!"cost lint: every listed name is a declaration or a field of its structure"

run_cmd liftTermElabM do
  let (bad, checked) ← undocumentedCostDefs
  unless bad.isEmpty do
    throwError m!"cost lint: {bad.size} extractor or simulator definition(s) without a \
      \"Running time\" docstring paragraph:\n{bad.toList}"
  let counts := checked.map fun (t, k) => m!"{k} {t}"
  logInfo m!"cost lint: every definition checked has a \"Running time\" docstring paragraph: \
    {counts}"

run_cmd liftTermElabM do
  let bad ← unlistedExtractorFunctions
  unless bad.isEmpty do
    throwError m!"cost lint: {bad.size} definition(s) named like an extractor, returning a \
      `Multiset`, `Option`, `List` or `Finset`, in neither `extractorFunctions` nor \
      `notExtractors`:\n{bad.toList}"
  logInfo m!"cost lint: every definition named like an extractor with a collection result is \
    listed ({extractorFunctions.length} extractor procedures, {notExtractors.length} exempt)"

run_cmd liftTermElabM do
  let (bad, nReaching) ← classicalExtractorDecisions
  unless bad.isEmpty do
    throwError m!"cost lint: {bad.size} application(s) passing an extractor a decision the \
      compiler rejects (a classical `Decidable` instance):\n\
      {String.intercalate "\n" (bad.map fun (d, c, rej) => s!"{d}: {c} at {rej}").toList}"
  logInfo m!"cost lint: {nReaching} definitions pass instance decisions to an extractor; no \
    application passes them a classical decision"

run_cmd liftTermElabM do
  let (bad, checked) ← oracleSimFailures
  unless bad.isEmpty do
    throwError m!"cost lint: {bad.size} oracle simulator(s) in statements that are not the law of \
      a computable `OracleSampler`:\n\
      {String.intercalate "\n" (bad.map fun (d, c, why) => s!"{d}: {c}: {why}").toList}"
  logInfo m!"cost lint: {checked} oracle simulator arguments in statements checked; each is a \
    local variable or the law of a computable `OracleSampler`"

run_cmd liftTermElabM do
  let reds ← reductionDefs
  let bad ← undocumentedReductions reds
  unless bad.isEmpty do
    throwError m!"cost lint: {bad.size} reduction(s) (an adversary built from another) without a       \"Running time\" docstring paragraph:\n{bad.toList}"
  logInfo m!"cost lint: {reds.size} reductions checked, each with a \"Running time\" docstring \
    paragraph; {notReductions.length} constructions exempt as model translations"

run_cmd liftTermElabM do
  let (bad, checked) ← computabilityFailures (← reductionDefs)
  let known := knownNoncomputable.map (·.1)
  let unexpected := bad.filter fun (n, _) => !known.contains n
  let stale := knownNoncomputable.filter fun (n, _) => !bad.any (·.1 == n)
  let knownMsgs := knownNoncomputable.filterMap fun (n, why) =>
    if bad.any (·.1 == n) then some s!"{n}: {why}" else none
  logInfo m!"cost lint: {checked} extractor, simulator and decoder definitions checked; \
    {knownMsgs.length} known noncomputable:\n{String.intercalate "\n" knownMsgs}"
  unless unexpected.isEmpty && stale.isEmpty do
    let msg := m!"cost lint: {unexpected.size} unexpected computability failure(s):\n\
      {String.intercalate "\n" (unexpected.map (·.2)).toList}\n\
      {stale.length} entr(y/ies) of `knownNoncomputable` now computable (remove them): \
      {stale.map (·.1)}"
    if ← computabilityReportOnly then logWarning msg else throwError msg
