-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Ghc

@[expose] public section

/-!
# GordieHowe: the definitions of a `.ghc` file, as terms

`Ghc.loadDefs` turns the sections of a `.ghc` file (`Ghc.lean`) into the definitions `load_ghc`
adds (`Load.lean`, in both check modes): one definition per section, in the file's order, at the
section's type, named by the section under the loading namespace, with compiled code when the
section's `compile` flag is set. The section's type picks its decoder from the registry it is given
(`Entry`, `GordieHoweNative/Codecs.lean`'s `sectionTypes`). A definition's value is the expression
of the decoded value, built as follows:

* **Shared.** Each plain value's expression is shared (`Ghc.valueExpr`: `ShareCommon.shareCommon'`
  merges structurally equal subterms into one object), and every later step keeps the sharing, so
  the kernel and the compiler see a repeated subterm once.
* **Raw literals.** Every natural number is a raw literal (`Decode Nat`'s `toE`).
* **The index maps by name.** An index map is read as a stand-in and its expression replaced by the
  constant `idx<j>` in scope (`Ghc.replaceStubs`).
* **Earlier definitions by name.** A spine-form value's references to earlier sections are their
  definitions' constants.
* **Long lists chained** (`chainLists`): a list literal of more than `listRun` items keeps its first
  `listRun` items, and each later run of `listRun` items is the definition `<def>_l<i>`, whose
  tail is the next run's definition. A term then nests about `listRun` deep however long its lists
  are. The walk is memoized by subterm where it adds no definition, so a shared subterm is walked
  once.

This file is part of the precompiled library `GordieHoweNative`, so the term building runs as
native code. The terms add no trust: the kernel checks every added definition.
-/

namespace GordieHowe.Ghc

open Lean GordieHowe.RealizedProgram

/-! ## The registry of section types -/

/-- **A type a section may have**: its descriptor and expression, and the readers of a section's
expression in the plain and the spine form. -/
structure Entry where
  /-- The type's descriptor. -/
  ty : Ty
  /-- The type. -/
  tyE : Expr
  /-- A plain section's expression. -/
  plainE : D Expr
  /-- A spine-form section's expression. -/
  spineE : D Expr

/-- The registry entry of a type with a decoder. -/
def Entry.of (α : Type) [Decode α] : Entry where
  ty := tyOf (Decode.tyE (α := α))
  tyE := Decode.tyE (α := α)
  plainE := do pure (valueExpr (← read).idxNames (Decode.toE (α := α) (← Decode.dec)))
  spineE := Decode.spineE (α := α)

/-! ## Chaining long lists -/

/-- The most items of a list literal in one definition. -/
def listRun : Nat := 128

/-- The items of a `List.cons` chain, and the chain's tail. -/
partial def consChain (e : Expr) (acc : Array Expr := #[]) : Array Expr × Expr :=
  if e.isAppOfArity ``List.cons 3 then consChain e.appArg! (acc.push e.appFn!.appArg!)
  else (acc, e)

/-- **A definition `load_ghc` adds**: its name, type and value, and whether it gets compiled
code. -/
structure Def where
  /-- The name. -/
  name : Name
  /-- The type. -/
  type : Expr
  /-- The value. -/
  value : Expr
  /-- Whether the definition gets compiled code. -/
  compile : Bool

/-- The state of a chaining: the next run's number, the run definitions added, and the subterms
chained so far. -/
structure ChainState where
  /-- The next run's number. -/
  next : Nat := 0
  /-- The run definitions, in the order they are added. -/
  defs : Array (Name × Expr × Expr) := #[]
  /-- The chained form of each subterm met. -/
  memo : Std.HashMap Expr Expr := {}

/-- **`e` with every long list literal chained through definitions** `base_l<i>` (see the module
docstring): a cons chain of more than `listRun` items keeps its first `listRun` items and continues
in the definitions of its later runs, each run's definition added before the one whose tail it is.
A subterm with no long list is memoized, so a shared one is walked once; one with a long list is
chained at each occurrence, so the definitions and their numbering are those of a walk of the
expression as a tree. -/
partial def chainLists (base : Name) (e : Expr) : StateM ChainState Expr := do
  if let some r := (← get).memo[e]? then return r
  let n0 := (← get).defs.size
  let r ← if e.isAppOfArity ``List.cons 3 then do
      let α := e.appFn!.appFn!.appArg!
      let (xs, tl) := consChain e
      let xs ← xs.mapM (chainLists base)
      let tl ← chainLists base tl
      let cons (lo hi : Nat) (t : Expr) : Expr :=
        (xs.extract lo hi).foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) α x acc) t
      let nch := (xs.size + listRun - 1) / listRun
      let mut rest := tl
      for j in [1:nch] do
        let i := nch - j
        let k ← modifyGet fun s => (s.next, { s with next := s.next + 1 })
        let n := base.appendAfter s!"_l{k}"
        let v := cons (i * listRun) ((i + 1) * listRun) rest
        modify fun s => { s with defs := s.defs.push (n, mkApp (mkConst ``List [Level.zero]) α, v) }
        rest := mkConst n
      pure (cons 0 listRun rest)
    else
      match e with
      | .app f a => do pure (e.updateApp! (← chainLists base f) (← chainLists base a))
      | _ => pure e
  modify fun s => if s.defs.size == n0 then { s with memo := s.memo.insert e r } else s
  pure r

/-! ## The definitions -/

/-- **The definition of `name : type := value`** with its long lists chained (`chainLists`): the
run definitions first, then the definition. -/
def chainedDefs (name : Name) (type value : Expr) (compile : Bool) : Array Def :=
  let (v, s) := (chainLists name value).run {}
  (s.defs.map fun (n, t, x) => { name := n, type := t, value := x, compile }).push
    { name, type, value := v, compile }

/-- **A section's name under the namespace `ns`** (the name's components separated by dots). -/
def sectionName (ns : Name) (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr ns

/-- **The definitions of a file's sections** (see the module docstring): the bytes and sections,
the registry of section types `types`, the loading namespace `ns`, the index maps' stand-ins `idx`
and constants `idxNames`. -/
def loadDefs (types : Array Entry) (ns : Name) (bytes : ByteArray) (secs : Array Section)
    (idx : Nat → Option IndexMap) (idxNames : Array Name) : Except String (Array Def) := do
  let names := secs.map fun s => sectionName ns s.name
  let mut defs := #[]
  for h : j in [0:secs.size] do
    let s := secs[j]
    let some e := types.find? (·.ty == s.ty) | throw s!"section {s.name}: unknown type {s.ty}"
    let d : D Expr := do
      let v ← if s.spine then e.spineE else e.plainE
      unless (← get) == s.off + s.len do throw s!"section {s.name}: trailing bytes"
      pure v
    let v ← (d.run' s.off).run { bytes, secs, cur := j, idx, names, idxNames }
      |>.mapError (s!"section {s.name}: " ++ ·)
    defs := defs ++ chainedDefs names[j]! e.tyE v s.compile
  pure defs

end GordieHowe.Ghc
