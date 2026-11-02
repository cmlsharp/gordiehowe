-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-! # The compiler-trust hypotheses of the headline theorems

A headline has a compiler-trust hypothesis when one of its leading binders has a type whose weak
head normal form is `CircuitsEnforce` or `CircuitsAccept`, or whose type mentions one of them or a
constant of a GKR certificate module (`GordieHowe.Generated.<App>.<Params>.GKR.*`). The proof
system of a program carries both facts as fields (`RealizedProgram.ProofSystem.enforce`,
`RealizedProgram.ProofSystem.accept`), proved from its certificates where an application builds it
(`RealizedProgram.ProgramCerts.proofSystem`), so an application's headlines are stated at its proof
system and take neither.

Prints `<headline>\t<binders>` for each headline with such a binder, then one line `trust: …`. A
headline of an application module (`GordieHowe.Applications.*`) with such a binder fails. The
generic theorems are printed only.

Whether a headline's statement, outside its binders, reaches certificate data is a question of the
roles of the statement's parts (`_agent/scratch/audit/closure-design.md`: the proof system a
headline is about is its subject, whose closure stops at the data); it is checked once the
property-head registry that assigns those roles exists. -/

open Lean Meta Elab Command

/-- The trust types, by the head constant of a binder's type in weak head normal form, or mentioned
in a binder's type. -/
def trustHeads : List Name :=
  [`GordieHowe.RealizedProgram.CircuitsEnforce, `GordieHowe.RealizedProgram.CircuitsAccept]

/-- The module of a constant, if known. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- Whether a module is a GKR certificate module: `GordieHowe.Generated.….GKR.…`. -/
def isCertModule (m : Name) : Bool :=
  (`GordieHowe.Generated).isPrefixOf m && m.components.contains `GKR

run_cmd liftTermElabM do
  let env ← getEnv
  let heads := (GordieHowe.headlines env).toList.toArray.qsort (·.toString < ·.toString)
  let mut trusting := 0
  let mut failures : Array Name := #[]
  for n in heads do
    let some ci := env.find? n | continue
    let bad ← forallTelescope ci.type fun xs _ => do
      let mut bad : Array String := #[]
      for x in xs do
        let ty ← instantiateMVars (← inferType x)
        let name ← x.fvarId!.getUserName
        let whnfTy ← whnf ty
        if let .const h _ := whnfTy.getAppFn then
          if trustHeads.contains h then
            bad := bad.push s!"{name} : {h.componentsRev.head!}"
            continue
        for c in ty.getUsedConstants do
          if trustHeads.contains c then
            bad := bad.push s!"{name} mentions {c.componentsRev.head!}"
            break
          if (moduleOf env c).any isCertModule then
            bad := bad.push s!"{name} mentions certificate data {c}"
            break
      return bad
    unless bad.isEmpty do
      trusting := trusting + 1
      IO.println s!"{n}\t{", ".intercalate bad.toList}"
      let app := match moduleOf env n with
        | some m => (`GordieHowe.Applications).isPrefixOf m
        | none => false
      if app then
        failures := failures.push n
  for n in failures do
    IO.println s!"FAIL: {n}: an application headline with a compiler-trust hypothesis"
  IO.println s!"trust: {trusting} headlines with a compiler-trust hypothesis, {failures.size} failing"
