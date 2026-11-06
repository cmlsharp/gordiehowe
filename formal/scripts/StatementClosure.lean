-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-!
# The statement closure of the headline theorems

Lists every declaration of this project that a reader must trust to understand the headline
theorems: the constants in the headline statements, and transitively the constants in the types
and bodies of definitions, the constructor types of inductives and the field types of structures
reached that way. Proofs of theorems are not followed: a theorem reached through a definition's
body contributes only its statement.

The roots are the theorems tagged `@[headline]` (`GordieHowe/Headline.lean`). The instance corollaries
are stated at concrete settings, so none of them is vacuous.

**Certified witnesses are not followed.** For a program's data and its GKR certificates
(`readFields`), the closure follows only the fields a headline reads: what the proof system, its
verifier, the certified program, the figures or the interpretation read. The fields only the
program's check (`programOk`) reads (the expression annotations, the realization's derivations,
the assignment reads, the shapes, the source roles, the certificates' DAG, schedule, node table and entries) are not followed: under the
sealed-data rule a checked witness cannot change a headline's meaning (`certifiedFields`).

Own code, followed: `GordieHowe`, `GordieHoweNative`, `GordieHoweCheck`, `LatticeCrypto`, `HashSig`
and the vendored `ArkLib` and `CompPoly`.
Every other constant reached (Lean core, Batteries, Mathlib, ...) is listed by name, grouped by
the root of its module, and not followed.

Output format:
* `# headline\t<name>`: the roots;
* `# transitive\t<name>\t<fingerprint>`: per root, its transitive fingerprint, a hash over the
  fingerprints of every own declaration the root reaches (itself included, compiler auxiliaries
  such as matchers too), in name order. A change in the type or body of any declaration in a
  headline's closure changes that headline's transitive fingerprint, though the headline's own
  fingerprint may not move (a configuration constant's body, read through a named constant);
* `<module>\t<declaration>\t<fingerprint>`: one line per own declaration, the fingerprint hashing
  the type and, for a definition, the body, with private constants by their user-facing names
  (`stripPrivate`), so that moving a file changes no fingerprint;
* a fourth column, present when a declaration mentions a constant renamed at the last renaming
  pass (`audit/renames.tsv`, `<old>\t<new>`): the fingerprint with every renamed constant replaced
  by its old name, which `scripts/carry_audits.py` compares with the ledger to carry an audit
  across the renaming;
* after `# ==== external constants`: `# external\t<module root>\t<name>`, one line per external
  constant reached;
* last line: `# total ...`, the counts.

Run as `lake env lean scripts/StatementClosure.lean`.
-/

open Lean Meta Elab Command

/-- The libraries followed as own code. -/
def ownRoots : List Name :=
  [`GordieHowe, `GordieHoweNative, `GordieHoweCheck, `LatticeCrypto, `HashSig, `ArkLib, `CompPoly]

/-- Whether a module belongs to this project (including the vendored libraries). -/
def ownModule (m : Name) : Bool :=
  ownRoots.contains m.getRoot

/-- The module of a constant, if known. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- **The fields a headline reads**, by structure: for a definition whose type is one of these
structures and whose value is a constructor application, the closure follows the constants of
these fields only. The other fields are witnesses that only the program's check
(`GordieHowe.ProgramData.programOkB`, theorem `programOk`) reads, so a reader need not trust their
content:

* a program's data (`GordieHowe.ProgramData`): its computational inputs (`RuntimeInputs`,
  `CompletionInputs`) and its GKR certificates; not the hints (the expression annotations, the
  derivations of the realization and the checked assignment-read rows), the shapes or the
  source-role table, which only the check reads;
* a GKR certificate (`GordieHowe.RealizedProgram.CircuitData`): the source parts the proof
  system's verifier reads (the layered circuit, the term width, the constants;
  `CircuitData.sourceParts`) and the scalar fields; not the DAG, the schedule, the node table or
  the entries, which only the circuit check reads. -/
def readFields : List (Name × List Name) :=
  [(`GordieHowe.ProgramData, [`inputs, `completion, `circuits]),
    (`GordieHowe.RealizedProgram.CircuitData,
      [`c, `w, `chr, `prime, `char2, `neg1, `half, `consts, `layered])]

/-- An expression with its leading `let` and `have` bindings substituted into the body: the
structure instance notation binds a parent given whole (`{ inputs := r, … }`) before the
constructor application. -/
partial def zetaHead (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ val body _ => zetaHead (body.instantiate1 val)
  | e => e

/-- **The followed arguments of a definition of a structure of `readFields`**: for a definition
whose type is such a structure and whose value is a constructor application (after its leading
`let` bindings, `zetaHead`), its arguments at that structure's read fields, and the constructor;
`none` for any other definition (followed whole). -/
def certifiedFields (env : Environment) (ty v : Expr) : Option (List Expr) := do
  let .const S _ := ty.consumeMData | none
  let read ← readFields.lookup S
  let v := zetaHead v
  let some info := getStructureInfo? env S | none
  let ctor := (getStructureCtor env S).name
  guard (v.getAppFn.isConstOf ctor)
  let fields := info.fieldNames
  let args := v.getAppArgs
  guard (args.size == fields.size)
  return v.getAppFn :: (fields.toList.zip args.toList).filterMap fun (f, a) =>
    if read.contains f then some a else none

/-- The constants to follow from a declaration: its type, and for definitions its body, for
inductives its constructors' types. -/
def successors (env : Environment) (ci : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d =>
    match certifiedFields env ci.type d.value with
    | some args => for a in args do s := s.append a.getUsedConstantsAsSet
    | none => s := s.append d.value.getUsedConstantsAsSet
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then s := s.append cc.type.getUsedConstantsAsSet
  | _ => pure ()
  return s

/-- An expression with every private constant replaced by its user-facing name, so that the
fingerprint of a declaration does not depend on the module a private constant it mentions lives in
(a file move renames `_private.<Module>.0.c`). -/
def stripPrivate (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (privateToUserName? n).map fun u => .const u ls
    | _ => none

/-- The rename map of the last renaming pass, new name to old name (`audit/renames.tsv`). -/
def loadRenames : IO (Std.HashMap Name Name) := do
  let path : System.FilePath := "audit/renames.tsv"
  unless ← path.pathExists do return {}
  let mut m : Std.HashMap Name Name := {}
  for line in (← IO.FS.lines path) do
    if line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [o, n] => m := m.insert n.toName o.toName
    | _ => pure ()
  return m

/-- The old name of `n`: its entry in the rename map, or, for a name below a renamed one (an
auxiliary `_proof_1`, `match_1`, `eq_1`), the old name of that prefix with the same suffix. -/
def undoName (m : Std.HashMap Name Name) : Name → Option Name
  | .anonymous => none
  | n@(.str p s) => (m.get? n).orElse fun _ => (undoName m p).map (·.str s)
  | n@(.num p k) => (m.get? n).orElse fun _ => (undoName m p).map (·.num k)

/-- An expression with every renamed constant, and every renamed structure of a projection,
replaced by its old name. -/
partial def undoRenames (m : Std.HashMap Name Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (undoName m n).map fun o => .const o ls
    | .proj s i b => some (.proj ((undoName m s).getD s) i (undoRenames m b))
    | _ => none

run_cmd liftTermElabM do
  let env ← getEnv
  let renames ← loadRenames
  let heads := (GordieHowe.headlines env).toList.toArray.qsort (·.toString < ·.toString)
  let mut seen : NameSet := {}
  let mut external : NameSet := {}
  -- the own successors of each own declaration, for the transitive fingerprints
  let mut succs : Std.HashMap Name (Array Name) := {}
  let mut stack := heads.toList
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n || external.contains n then continue
    let some ci := env.find? n | continue
    let some m := moduleOf env n | continue
    unless ownModule m do
      external := external.insert n
      continue
    seen := seen.insert n
    let ss := (successors env ci).toList
    succs := succs.insert n (ss.filter (fun c =>
      ((moduleOf env c).map ownModule).getD false && (env.find? c).isSome)).toArray
    for c in ss do
      unless seen.contains c do stack := c :: stack
  -- the fingerprint of every own declaration reached, compiler auxiliaries included
  let mut fp : Std.HashMap Name UInt64 := {}
  for n in seen.toList do
    let some ci := env.find? n | continue
    fp := fp.insert n (match ci with
      | .defnInfo d => mixHash (stripPrivate ci.type).hash (stripPrivate d.value).hash
      | _ => (stripPrivate ci.type).hash)
  let mut byModule : Std.HashMap Name (Array (Name × UInt64 × UInt64)) := {}
  for n in seen.toList do
    let un := (privateToUserName? n).getD n
    -- skip compiler-generated auxiliaries; what they mention was followed
    if un.isInternal || isAuxRecursor env n || isNoConfusion env n || isMatcherCore env n then
      continue
    let some m := moduleOf env n | continue
    let some ci := env.find? n | continue
    -- the fingerprint of what a reader trusts: the type, and the body of a definition
    let h : UInt64 := fp.getD n 0
    let u := fun e => undoRenames renames e
    let h₀ : UInt64 := match ci with
      | .defnInfo d => mixHash (u (stripPrivate ci.type)).hash (u (stripPrivate d.value)).hash
      | _ => (u (stripPrivate ci.type)).hash
    byModule := byModule.insert m ((byModule.getD m #[]).push (un, h, h₀))
  let mods := byModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for n in heads do
    IO.println s!"# headline\t{n}"
  -- each headline's transitive fingerprint: its closure in name order, hashed with each fingerprint
  for n in heads do
    let mut reach : NameSet := {}
    let mut todo := [n]
    while !todo.isEmpty do
      let c := todo.head!
      todo := todo.tail!
      if reach.contains c || !seen.contains c then continue
      reach := reach.insert c
      for d in succs.getD c #[] do
        unless reach.contains d do todo := d :: todo
    -- by user-facing name, then fingerprint (two private constants may share a name)
    let named := reach.toList.toArray.map fun c =>
      (((privateToUserName? c).getD c).toString, fp.getD c 0)
    let mut t : UInt64 := 7
    for (u, h) in named.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) do
      t := mixHash (mixHash t (hash u)) h
    IO.println s!"# transitive\t{n}\t{t}"
  let mut total := 0
  let mut perLib : Std.HashMap Name Nat := {}
  for (m, ns) in mods do
    total := total + ns.size
    perLib := perLib.insert m.getRoot (perLib.getD m.getRoot 0 + ns.size)
    for (n, h, h₀) in ns.qsort (·.1.toString < ·.1.toString) do
      if h₀ == h then
        IO.println s!"{m}\t{n}\t{h}"
      else
        IO.println s!"{m}\t{n}\t{h}\t{h₀}"
  -- external constants, grouped by the root of their module
  let mut extByLib : Std.HashMap Name (Array Name) := {}
  for n in external.toList do
    let lib := ((moduleOf env n).map Name.getRoot).getD `unknown
    extByLib := extByLib.insert lib ((extByLib.getD lib #[]).push n)
  let libs := extByLib.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  IO.println "# ==== external constants (not followed), by module root ===="
  for (lib, ns) in libs do
    IO.println s!"# library {lib}: {ns.size}"
    for n in ns.qsort (·.toString < ·.toString) do
      IO.println s!"# external\t{lib}\t{n}"
  let ownCounts := ownRoots.map fun r => s!"{r} {perLib.getD r 0}"
  let extCounts := libs.toList.map fun (lib, ns) => s!"{lib} {ns.size}"
  IO.println s!"# total: headlines {heads.size}; project declarations {total} ({", ".intercalate ownCounts}); external constants {external.size} ({", ".intercalate extCounts})"
