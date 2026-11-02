-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Codecs
public meta import GordieHoweNative.Codecs
public import GordieHowe.Language.Realizations.Circuit.Load
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Basic
public meta import Std.Sync.Mutex

public meta section

/-!
# GordieHowe: native mode's certificate data and check

In native mode (`GordieHowe.certCheckNative`, set by `scripts/cert_mode.sh`) the GKR certificates
are checked by compiled code, which never compiles the loaded literals:

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
* **The check.** `gh_cert_check` runs `gh_native_check`: it replaces every constant of the goal
  that has a reader by the reader applied to `()` (a definitional rewrite), compiles and evaluates
  the goal's decision on a thread of its own (`evalBool`, so the evaluation and the file's decoding
  do not count against the elaboration's heartbeats), and on `true` adds the axiom
  `<decl>._native.native_decide.ax_<i>_<j>` stating it, as `native_decide` does. The compiled
  code runs in the imports of the current module imported again with their code (`meta`), since a
  generated module imports its data and checkers without it; that environment is imported once per
  process. The checkers and everything their compiled code calls are in `GordieHoweNative`, whose
  shared library Lake loads into the process, so the evaluation calls their native code; the
  certificate data's values are evaluated from their IR.

What native mode trusts beyond the kernel: Lean's compiler and run time (the evaluation, and its
thread; the native code of `GordieHoweNative`, the decoders and the checkers, which Lake compiles
with the toolchain's C compiler and loads as a shared library), the file read (once per process, each section's value
kept by path, hash, section and index maps), the decoders (`Decode.dec`, `Decode.spine`) run at run
time on the same bytes as at elaboration, and `Ghc.loadDefs` (that the definitions it builds from
the same bytes, by `Decode.toE` and `Decode.spineE`, sharing, the index maps' and earlier
sections' constants and the chained lists, denote the decoded values). Kernel mode uses none of this file.
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
def loadNative (stx : Syntax) : CommandElabM Unit := do
  let some rel := stx[1].isStrLit? | throwError "load_ghc: expected a file name"
  let { path, hash, idxs, ns, secs } ← Load.loadFile stx
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

/-- **`load_ghc` in native mode** (`loadNative`). Kernel mode leaves the command to
`Load.elabLoadGhc`. -/
@[command_elab GordieHowe.Load.loadGhc]
def elabLoadGhcNative : CommandElab := fun stx => do
  unless GordieHowe.certCheckNative do throwUnsupportedSyntax
  loadNative stx

/-! ## The check -/

/-- The imports of a module imported again with their code, once per process. -/
initialize nativeEnv : Std.Mutex (Option (Array Import × Environment)) ← Std.Mutex.new none

/-- **The imports of the current module with their code** (`meta`), imported once per process. -/
def codeEnv : CoreM Environment := do
  let imports := (← getEnv).header.imports
  let opts ← getOptions
  nativeEnv.atomically do
    if let some (imps, env) ← get then
      if imps == imports then return env
    unsafe enableInitializersExecution
    let env ← importModules (imports.map fun i => { i with isMeta := true }) opts
      (loadExts := true) (level := .exported)
    let env := env.setMainModule `_ghNative
    set (some (imports, env))
    pure env

/-- **Evaluate a closed `Bool`** in `codeEnv`: compile it as an auxiliary definition, then run
it. -/
def evalBoolHere (e : Expr) : CoreM Bool := do
  let env ← codeEnv
  let name := `_ghNative.check
  let decl := Declaration.defnDecl
    (mkDefinitionValEx name [] (mkConst ``Bool) e .abbrev .safe [name])
  let run : CoreM Bool := do
    modifyEnv (markMeta · name)
    withOptions (fun o => o |>.set `compiler.relaxedMetaCheck true |>.set `Elab.async false) do
      addAndCompile decl
    unsafe evalConst Bool name
  let (r, _) ← run.toIO (← read) { env := env }
  pure r

/-- **`evalBoolHere` on a thread of its own**, awaited: the compiled check, and the reading of
the certificate file it runs, allocate on that thread, so they do not count against the
elaboration's heartbeats (counted per thread). The heartbeat count starts again on that thread.
An error is the same error as on the elaboration thread. -/
def evalBool (e : Expr) : CoreM Bool := do
  let ctx ← read
  let st ← get
  let t ← IO.asTask (prio := .dedicated) do
    let ctx := { ctx with initHeartbeats := ← IO.getNumHeartbeats }
    let (r, _) ← (evalBoolHere e).toIO ctx st
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

/-- The elaborator of `gh_native_check` (declared in `CertCheck.lean`). In a file outside the
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
  unless ← evalBool d do
    throwError "gh_native_check: the check evaluates to false{indentExpr P}"
  let ax ← mkAuxDeclName (`_native ++ `native_decide ++ `ax)
  let axTy := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) d (mkConst ``Bool.true)
  addDecl (.axiomDecl { name := ax, levelParams := [], type := axTy, isUnsafe := false })
  let pf ← mkAppM ``of_decide_eq_true #[mkConst ax]
  g.assign (← mkExpectedTypeHint pf P)
  Tactic.replaceMainGoal []

end GordieHowe.LoadNative
