-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProgramCodecs
public meta import GordieHoweNative.ProgramCodecs
public import GordieHowe.Language.Realizations.Circuit.Load
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Basic
public meta import Lean.Compiler.InlineAttrs

public meta section

/-!
# GordieHowe: native mode's certificate data and check

With this module imported, the GKR certificate data includes readers in both check modes. In native
mode, compiled checks use the file-backed readers. Sections marked `compile` still retain
compiled literal definitions for computational consumers:

* **The data.** `load_ghc "path.ghc" "hash"` adds the definitions exactly as in kernel mode
  (`Load.loadFile`: the sections decoded by the decoders of `GordieHoweNative`, which both modes
  use, and the definitions of `Ghc.loadDefs`, each the expression of a decoded value, the index maps
  by name `idx<j>`). As in kernel mode, only the sections flagged `compile` have compiled code.
* **The readers.** For each section `X` flagged `reader` (for a GKR circuit: `name`, each
  `name.layer<d>` and `name.wtab<d>`, the constants its checks name) it adds
  `X.ghNative : Unit → T`, whose definition is the loaded definition and whose compiled code
  (`@[implemented_by]`) reads the section at run time (`Ghc.readSectionUnsafe`: the same file, by
  its path relative to the working directory, which is the package root under Lake, the same hash,
  the same decoder at the section's type `T`, the index maps `ghcIdx_<file>`), reading the file
  once per process and decoding each section once (`Ghc.readCache`). The kernel sees only the
  definition, so a reader is the loaded value by definition.
* **The check.** `gh_native_check`: it replaces every constant of the goal
  that has a reader by the reader applied to `()` (a definitional rewrite), compiles and evaluates
  the goal's decision on a thread of its own (`evalBool`, so the evaluation and the file's decoding
  do not count against the elaboration's heartbeats), and on `true` adds the axiom
  `<decl>._native.native_decide.ax_<i>_<j>` stating it, as `native_decide` does. The compiled
  code runs in the current environment: a module closing a check imports its checker's and its
  data's modules also as `meta`, which makes their code accessible there, so no environment is
  imported again. Code in `GordieHoweNative` runs from the shared library Lake loads into the
  process. Definitions outside it (`orderB`, `padsB`, `programOkB` and its groups, in
  `GordieHowe`) have no shared library and run in the IR interpreter, calling compiled code where
  they reach it; the certificate data's values are evaluated from their IR or read at run time.
* **A failing check.** When a Boolean check `b = true` evaluates to `false`, the error names its
  conjuncts that fail (`failingParts`: the outer operands of `&&` and the named program-check
  groups, evaluated together with the check's argument passed to one compiled function, as
  the check itself is), so a program check (`ProgramData.programOkB`) names its failing parts.

What native mode trusts beyond the kernel: Lean's compiler and run time (the evaluation, and its
thread; the native code of `GordieHoweNative`, the decoders and the checkers, which Lake compiles
with the toolchain's C compiler and loads as a shared library), the file read (once per process, each section's value
kept by path, hash, section and index maps), the decoders (`Decode.dec`, `Decode.spine`) run at run
time on the same bytes as at elaboration, and `Ghc.loadDefs` (that the definitions it builds from
the same bytes, by `Decode.toE` and `Decode.spineE`, sharing, the index maps' and earlier
sections' constants and the chained lists, denote the decoded values). Kernel proofs reduce the
loaded definitions; importing reader registration alone adds no proof axiom.
-/

namespace GordieHowe.LoadNative

open Lean Elab Command Meta
open GordieHowe.RealizedProgram (IndexMap)

/-- The identifier of a full name. -/
def rootId (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-- **A section's type as a term**: its constants from the root, its applications. -/
partial def tyTerm : Ghc.Ty → CommandElabM Term
  | .const n => pure (rootId n.toName)
  | .app f a => do `($(← tyTerm f) $(← tyTerm a))

/-- **Native mode's loading** of `load_ghc "path.ghc" "hash"`: the definitions as in kernel mode
(`Load.loadFile`), then the readers (see the module docstring). -/
def loadNative (stx : Syntax) (types : Array Ghc.Entry := Ghc.sectionTypes) :
    CommandElabM Unit := do
  let some rel := stx[1].isStrLit? | throwError "load_ghc: expected a file name"
  let { path, hash, idxs, ns, secs } ← Load.loadFile stx types
  -- the index maps the readers decode with, one array per file
  let idxN := ns ++ Name.mkSimple s!"ghcIdx_{path.fileStem.getD "ghc"}"
  let idxIds : Array Term := idxs.map fun n => rootId n
  elabCommand (← `(command| def $(rootId idxN) : Array $(mkIdent ``IndexMap) := #[$idxIds,*]))
  -- the path the reader opens: relative to the working directory (the package root under Lake),
  -- so a copied tree reads its own file; absolute only for a file outside it
  let cwd := (← IO.FS.realPath (← IO.currentDir)).toString
  let pathS := path.toString
  let pathL := Syntax.mkStrLit <|
    if pathS.startsWith (cwd ++ "/") then s!"{pathS.drop (cwd.length + 1)}" else pathS
  let hashL := Syntax.mkStrLit hash
  let mut n : Nat := 0
  for h : j in [0:secs.size] do
    let s := secs[j]
    unless s.reader do continue
    let x := Ghc.sectionName ns s.name
    let T ← tyTerm s.ty
    let jL := Syntax.mkNumLit (toString j)
    elabCommand (← `(command| unsafe def $(rootId (x ++ `ghNativeImpl)) (_ : Unit) : $T :=
      $(mkIdent ``Ghc.readSectionUnsafe) $pathL $hashL $(rootId idxN) $jL))
    elabCommand (← `(command| @[implemented_by $(rootId (x ++ `ghNativeImpl))]
      def $(rootId (x ++ `ghNative)) (_ : Unit) : $T := $(rootId x)))
    n := n + 1
  logInfo m!"load_ghc (native): {rel}: {secs.size} sections, {n} readers"

/-- **`load_ghc` with readers** (`loadNative`), in both check modes. The kernel checks the
loaded values; the readers are used only when a proof explicitly invokes compiled checking. -/
@[command_elab GordieHowe.Load.loadGhc]
def elabLoadGhcNative : CommandElab := fun stx => do
  loadNative stx

/-- Program literal loading registers the same file-backed readers as ordinary GKR loading.
The explicit profile changes only the kernel-checked definition expressions. -/
@[command_elab GordieHowe.Load.loadProgramGhc]
def elabLoadProgramGhcNative : CommandElab := fun stx => do
  loadNative stx (Ghc.programSectionTypes (← getEnv))

/-! ## The check -/

/-- **Evaluate a closed `Bool`** in the current environment: compile it as an auxiliary `meta`
definition, then run it. Its constants' code must be accessible here, so a module closing a check
by `gh_native_check` imports, besides its usual imports, the modules of the checker and the data as
`meta` (`meta import`); otherwise the compilation fails, naming the inaccessible constant. The
environment change is discarded (`evalBool` runs this on a copy of the state). The definition's
name `name` is below the current declaration's (an asynchronous elaboration may add only those). -/
def evalBoolHere (name : Name) (e : Expr) : CoreM Bool := do
  let decl := Declaration.defnDecl
    (mkDefinitionValEx name [] (mkConst ``Bool) e .abbrev .safe [name])
  modifyEnv (markMeta · name)
  withOptions (fun o => o |>.set `Elab.async false) do
    addAndCompile decl
  unsafe evalConst Bool name

/-- **`evalBoolHere` on a thread of its own**, awaited: the compiled check, and the reading of
the certificate file it runs, allocate on that thread, so they do not count against the
elaboration's heartbeats (counted per thread). The heartbeat count starts again on that thread.
An error is the same error as on the elaboration thread. -/
def evalBool (name : Name) (e : Expr) : CoreM Bool := do
  let ctx ← read
  let st ← get
  let t ← IO.asTask (prio := .dedicated) do
    let ctx := { ctx with initHeartbeats := ← IO.getNumHeartbeats }
    let (r, _) ← (evalBoolHere name e).toIO ctx st
    pure r
  IO.ofExcept (← IO.wait t)

/-- **A goal with its data read at run time**: every constant `c` with a reader `c.ghNative`
replaced by `c.ghNative ()`, definitionally equal. -/
def withReaders (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const c [] =>
      let r := c ++ `ghNative
      if env.contains r then some (mkApp (mkConst r) (mkConst ``Unit.unit)) else none
    | _ => none

/-- **The conjuncts of a check** `e : Bool`: its outer conjunction and the named groups of
`ProgramData.programOkB`. The individual parts remain applications of their checkers, so their
compiled reader substitutions still apply. Unfolding inside a part would bypass those fast paths. -/
partial def conjuncts (e : Expr) (outer : Bool := true) : MetaM (Array Expr) := do
  if e.isAppOfArity ``and 2 then
    return (← conjuncts e.appFn!.appArg! false) ++ (← conjuncts e.appArg! false)
  let groups : List Name :=
    [`GordieHowe.ProgramData.programOkB, `GordieHowe.ProgramData.coreOkB,
     `GordieHowe.ProgramData.validB, `GordieHowe.ProgramData.realizationB,
     `GordieHowe.ProgramData.factsB, `GordieHowe.ProgramData.completeB]
  unless outer || groups.contains (e.getAppFn.constName?.getD .anonymous) do return #[e]
  match ← unfoldDefinition? e with
  | some e' =>
    let e' ← whnfCore e'
    if e'.isAppOfArity ``and 2 then conjuncts e' false else return #[e]
  | none => return #[e]

/-- **Evaluate a closed `List Bool`** as `evalBoolHere` evaluates a `Bool`, on a thread of its own
(`evalBool`). -/
def evalBools (name : Name) (e : Expr) : CoreM (List Bool) := do
  let ctx ← read
  let st ← get
  let t ← IO.asTask (prio := .dedicated) do
    let ctx := { ctx with initHeartbeats := ← IO.getNumHeartbeats }
    let run : CoreM (List Bool) := do
      let decl := Declaration.defnDecl
        (mkDefinitionValEx name [] (mkApp (mkConst ``List [0]) (mkConst ``Bool)) e .abbrev .safe
          [name])
      modifyEnv (markMeta · name)
      withOptions (fun o => o |>.set `Elab.async false) do
        addAndCompile decl
      unsafe evalConst (List Bool) name
    let (r, _) ← run.toIO ctx st
    pure r
  IO.ofExcept (← IO.wait t)

/-- **The failing conjuncts of a false check** `lhs`: the head constants of the leaves of
`conjuncts` that evaluate to `false`. The leaves are evaluated together, as one list, by an
auxiliary definition whose parameter is the check's argument (for a program's check, its data):
`fun d => [part₁ d, …]` with no inlining, applied to the argument with its data through the
readers. Compiled code thus sees the data only as the argument of compiled functions, as the
check itself does; a part compiled at the unfolded data alone can hit a compiler error. Any error
here gives no parts (the caller reports the check's failure alone). -/
def failingParts (lhs : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  try
    -- Discover parts at a variable, before unfolding any projection of the closed data.
    -- Abstracting this variable also preserves references below nested lambda binders.
    let arg? := if lhs.isApp && !lhs.appArg!.hasLooseBVars then some lhs.appArg! else none
    let (cs, vals) ← match arg? with
      | some a =>
        let ty ← inferType a
        withLocalDeclD `d ty fun x => do
          let cs ← conjuncts (mkApp lhs.appFn! x)
          let body ← mkLambdaFVars #[x] (← mkListLit (mkConst ``Bool) cs.toList)
          let f ← mkAuxDeclName (`_native ++ `native_decide ++ `parts)
          let fv := Declaration.defnDecl
            (mkDefinitionValEx f [] (← inferType body) body .opaque .safe [f])
          modifyEnv (markMeta · f)
          withOptions (fun o => o |>.set `Elab.async false) do
            addDecl fv
            modifyEnv fun env => (Compiler.setInlineAttribute env f .noinline).toOption.getD env
            compileDecl fv
          let n ← mkAuxDeclName (`_native ++ `native_decide ++ `part)
          let vals ← evalBools n (mkApp (mkConst f) (withReaders env a))
          return (cs, vals)
      | none =>
        let cs ← conjuncts lhs
        let n ← mkAuxDeclName (`_native ++ `native_decide ++ `part)
        let vals ← evalBools n (← mkListLit (mkConst ``Bool) (cs.toList.map (withReaders env)))
        pure (cs, vals)
    let mut out := #[]
    for (c, v) in cs.toList.zip vals do
      unless v do out := out.push (c.getAppFn.constName?.getD `_)
    return out
  catch _ => return #[]

/-- The elaborator of `gh_native_check` (declared in `Load.lean`). In a file outside the
module system the imports' code is already loaded, so `native_decide` checks the goal directly. -/
@[tactic GordieHowe.ghNativeCheck]
def evalGhNativeCheck : Tactic.Tactic := fun _ => Tactic.withMainContext do
  unless (← getEnv).header.isModule do
    Tactic.evalTactic (← `(tactic| native_decide))
    return
  let g ← Tactic.getMainGoal
  let P ← instantiateMVars (← g.getType)
  if P.hasFVar || P.hasMVar then throwError "gh_native_check: the goal is not closed{indentExpr P}"
  let P' := withReaders (← getEnv) P
  let d ← mkDecide P'
  let check ← mkAuxDeclName (`_native ++ `native_decide ++ `check)
  unless ← evalBool check d do
    -- The parts that fail, when the goal is a Boolean check `b = true`.
    let parts ← if P.isAppOfArity ``Eq 3 && P.appArg!.isConstOf ``Bool.true then
        failingParts P.appFn!.appArg! else pure #[]
    if parts.isEmpty then
      throwError "gh_native_check: the check evaluates to false{indentExpr P}"
    throwError "gh_native_check: the check evaluates to false; its parts that fail: {parts.toList}"
  let ax ← mkAuxDeclName (`_native ++ `native_decide ++ `ax)
  let axTy := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) d (mkConst ``Bool.true)
  addDecl (.axiomDecl { name := ax, levelParams := [], type := axTy, isUnsafe := false })
  let pf ← mkAppM ``of_decide_eq_true #[mkConst ax]
  g.assign (← mkExpectedTypeHint pf P)
  Tactic.replaceMainGoal []

end GordieHowe.LoadNative
