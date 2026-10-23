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

Own code, followed: `GordieHowe`, `LatticeCrypto`, `HashSig` and the vendored `ArkLib` and `CompPoly`.
Every other constant reached (Lean core, Batteries, Mathlib, ...) is listed by name, grouped by
the root of its module, and not followed.

Output format:
* `# headline\t<name>`: the roots;
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
def ownRoots : List Name := [`GordieHowe, `LatticeCrypto, `HashSig, `ArkLib, `CompPoly]

/-- Whether a module belongs to this project (including the vendored libraries). -/
def ownModule (m : Name) : Bool :=
  ownRoots.contains m.getRoot

/-- The module of a constant, if known. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- The constants to follow from a declaration: its type, and for definitions its body, for
inductives its constructors' types. -/
def successors (env : Environment) (ci : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d => s := s.append d.value.getUsedConstantsAsSet
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
    for c in (successors env ci).toList do
      unless seen.contains c do stack := c :: stack
  let mut byModule : Std.HashMap Name (Array (Name × UInt64 × UInt64)) := {}
  for n in seen.toList do
    let un := (privateToUserName? n).getD n
    -- skip compiler-generated auxiliaries; what they mention was followed
    if un.isInternal || isAuxRecursor env n || isNoConfusion env n || isMatcherCore env n then
      continue
    let some m := moduleOf env n | continue
    let some ci := env.find? n | continue
    -- the fingerprint of what a reader trusts: the type, and the body of a definition
    let h : UInt64 := match ci with
      | .defnInfo d => mixHash (stripPrivate ci.type).hash (stripPrivate d.value).hash
      | _ => (stripPrivate ci.type).hash
    let u := fun e => undoRenames renames e
    let h₀ : UInt64 := match ci with
      | .defnInfo d => mixHash (u (stripPrivate ci.type)).hash (u (stripPrivate d.value)).hash
      | _ => (u (stripPrivate ci.type)).hash
    byModule := byModule.insert m ((byModule.getD m #[]).push (un, h, h₀))
  let mods := byModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for n in heads do
    IO.println s!"# headline\t{n}"
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
