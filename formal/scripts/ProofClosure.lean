-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-!
# The proof closure of the headline theorems

Lists, per module of `GordieHowe`, which declarations the headline theorems need: the constants in the
types and values of the theorems tagged `@[headline]` (`GordieHowe/Headline.lean`), and transitively the
constants in the types and values of every declaration reached, proofs of theorems included.
A declaration outside this closure can be deleted without changing any headline theorem.

Compiler-generated constants (auxiliary proofs, matchers, equation lemmas, constructors,
projections, recursors) count for the declaration that generates them: reaching `Foo.bar._proof_1`
or `Foo.mk` keeps `Foo.bar` or `Foo`.

Own code, followed: `GordieHowe`, `LatticeCrypto`, `HashSig` and the vendored `ArkLib` and `CompPoly`;
only `GordieHowe` modules are reported.

Output format:
* `# module\t<module>\t<used>\t<total>\t<lines of unused declarations>`: one line per module;
* `used\t<module>\t<declaration>` and `unused\t<module>\t<declaration>\t<lines>`: one line per
  declaration (syntax and other metaprograms are listed as `meta`);
* last line: `# total ...`.

Run as `lake env lean scripts/ProofClosure.lean`.
-/

open Lean Meta Elab Command

/-- The libraries followed as own code. -/
def ownRoots : List Name := [`GordieHowe, `LatticeCrypto, `HashSig, `ArkLib, `CompPoly]

/-- The module of a constant, if known. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- Whether `s` is `pre` followed by a nonempty run of digits (`eq_1`, `proof_2`): the names of
generated equation lemmas and auxiliary proofs, unlike a theorem named `eq_of_foo`. -/
def isNumbered (pre s : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit

/-- The declaration that a compiler-generated constant belongs to: the inductive of a
constructor, recursor or projection; otherwise the longest non-internal prefix that is a
constant. -/
partial def owner (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo c) => c.induct
  | some (.recInfo r) => r.getMajorInduct
  | _ =>
    if let some info := env.getProjectionFnInfo? n then
      match env.find? info.ctorName with
      | some (.ctorInfo c) => c.induct
      | _ => n
    else
      let un := (privateToUserName? n).getD n
      let generatedSuffix : Bool := match un with
        | .str p s => (env.contains p || (match n with | .str q _ => env.contains q | _ => false)) &&
            (isNumbered "eq_" s || isNumbered "proof_" s ||
              ["eq_def", "eq_unfold", "induct", "inj", "injEq", "sizeOf_spec", "ctorIdx",
                "mutual_induct", "fun_cases", "induct_unfolding", "ext_iff", "ext"].contains s)
        | _ => false
      if un.isInternal || generatedSuffix || isAuxRecursor env n || isNoConfusion env n ||
          isMatcherCore env n then
        match n with
        | .str p _ | .num p _ => if env.contains p then owner env p else
            -- private prefixes: try the user-facing parent
            match un with
            | .str q _ | .num q _ => if env.contains q then owner env q else n
            | _ => n
        | _ => n
      else n

/-- The constants to follow from a declaration: its type and value, constructor types. -/
def successors (env : Environment) (ci : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := ci.type.getUsedConstantsAsSet
  if let some v := ci.value? (allowOpaque := true) then
    s := s.append v.getUsedConstantsAsSet
  match ci with
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then s := s.append cc.type.getUsedConstantsAsSet
  | _ => pure ()
  return s

/-- Whether a constant is a metaprogram (syntax, macro, elaborator, tactic, attribute). -/
def isMetaDecl (ci : ConstantInfo) : Bool :=
  ci.type.getUsedConstants.any fun c =>
    [`Lean.ParserDescr, `Lean.TrailingParserDescr, `Lean.Macro, `Lean.Elab, `Lean.Meta,
      `Lean.PrettyPrinter, `Lean.Syntax, `Lean.Environment, `Lean.Name, `IO, `Lean.Parser,
      `Lean.KeyedDeclsAttribute, `Lean.Core, `Lean.Linter].any (·.isPrefixOf c)

run_cmd liftTermElabM do
  let env ← getEnv
  let heads := (GordieHowe.headlines env).toList
  let mut seen : NameSet := {}
  let mut stack := heads
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    let some ci := env.find? n | continue
    let some m := moduleOf env n | continue
    unless ownRoots.contains m.getRoot do continue
    seen := seen.insert n
    let o := owner env n
    if o != n && !seen.contains o then stack := o :: stack
    for c in (successors env ci).toList do
      unless seen.contains c do stack := c :: stack
  let used : NameSet := seen.toList.foldl (fun s n => s.insert (owner env n)) {}
  -- every user-facing declaration of a PQ module
  let mut byModule : Std.HashMap Name (Array (Name × Bool × Bool)) := {}
  for (n, ci) in env.constants.map₁.toList do
    let some m := moduleOf env n | continue
    unless m.getRoot == `GordieHowe do continue
    if owner env n != n then continue
    let un := (privateToUserName? n).getD n
    if un.isInternal then continue
    byModule := byModule.insert m ((byModule.getD m #[]).push (n, used.contains n, isMetaDecl ci))
  let mods := byModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut totUsed := 0
  let mut tot := 0
  let mut totLines := 0
  for (m, ns) in mods do
    let mut u := 0
    let mut lines := 0
    let mut rows : Array String := #[]
    for (n, isUsed, isMeta) in ns.qsort (·.1.toString < ·.1.toString) do
      let un := (privateToUserName? n).getD n
      if isUsed then
        u := u + 1
        rows := rows.push s!"used\t{m}\t{un}"
      else
        let l ← match ← findDeclarationRanges? n with
          | some r => pure (r.range.endPos.line + 1 - r.range.pos.line)
          | none => pure 0
        lines := lines + l
        rows := rows.push s!"{if isMeta then "meta" else "unused"}\t{m}\t{un}\t{l}"
    IO.println s!"# module\t{m}\t{u}\t{ns.size}\t{lines}"
    for r in rows do IO.println r
    totUsed := totUsed + u
    tot := tot + ns.size
    totLines := totLines + lines
  IO.println s!"# total: headlines {heads.length}; PQ declarations used {totUsed} of {tot}; lines of unused declarations {totLines}"
