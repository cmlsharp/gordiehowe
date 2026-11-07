-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-!
# Statement-size report (report only)

Lists the declarations of GordieHowe's own modules whose type, counted as a tree (without
sharing, `Lean.Expr.sizeWithoutSharing`), has at least `threshold` nodes. The olean writer and
term traversals that do not cache shared subterms (abstraction for `rw`, motive checks,
instantiation) pay for the tree, not for the shared graph: in MLDSAW1SlotLaws a statement of
1.7 billion tree nodes took 580 s to serialize. A statement is large when a type is read through
a constructed object (an algorithm term inside an implicit shape argument, repeated at every
mention); the fix is at the definition that spells the type (audit/PERF.md).

Counts saturate at `cap` per declaration. Shared expression subtrees are memoized,
while each occurrence still contributes its full tree size. The report prints declarations at or
above the threshold, largest first (at the cap, the size is at least the cap), and exits
successfully: it is not a gate.
-/

open Lean Meta

namespace StatementSize

/-- The report threshold, in tree nodes. -/
def threshold : Nat := 1000000

/-- The count stops here. -/
def cap : Nat := 50000000

/-- Tree sizes are memoized structurally, but every occurrence contributes its full
size: this counts the unfolded tree, not distinct DAG nodes. Saturation commutes
with addition, so storing capped sizes preserves the original result. -/
partial def treeSizeMemo (e : Expr) : StateM (ExprStructMap Nat) Nat := do
  if let some n := (← get).get? ⟨e⟩ then return n
  let n ← match e with
    | .app f a | .lam _ f a _ | .forallE _ f a _ =>
      pure (min cap (1 + (← treeSizeMemo f) + (← treeSizeMemo a)))
    | .letE _ t v b _ =>
      pure (min cap (1 + (← treeSizeMemo t) + (← treeSizeMemo v) + (← treeSizeMemo b)))
    | .mdata _ b | .proj _ _ b => pure (min cap (1 + (← treeSizeMemo b)))
    | _ => pure 1
  modify (·.insert ⟨e⟩ n)
  return n

def treeSize (e : Expr) : StateM Nat Unit :=
  modify fun n => if n ≥ cap then n else min cap (n + ((treeSizeMemo e).run {}).1)

/-- The subtree size from which an application counts in `bigHeads`. -/
def bigSub : Nat := 10000

abbrev HeadCounts := Std.HashMap Name (Nat × Nat)

/-- First-occurrence order is retained so replaying a summary inserts hash-map
keys in the same order as the original traversal, including output ties. -/
structure HeadSummary where
  size : Nat
  order : Array Name
  heads : HeadCounts
  deriving Inhabited

def addHeads (a : HeadCounts) (b : HeadSummary) : HeadCounts := Id.run do
  let mut a := a
  for name in b.order do
    let (k, z) := b.heads.getD name (0, 0)
    let (k₀, z₀) := a.getD name (0, 0)
    a := a.insert name (k₀ + k, z₀ + z)
  return a

/-- Summarize a prefix of the original flattened-application traversal. Only
complete subtrees are cached; a budget-truncated subtree is never reused.
The size and every head's multiplicity still count all repeated occurrences. -/
partial def headSummary (e : Expr) (budget : Nat) :
    StateM (ExprStructMap HeadSummary) HeadSummary := do
  if budget == 0 then return ⟨0, #[], {}⟩
  if let some summary := (← get).get? ⟨e⟩ then
    if summary.size ≤ budget then return summary
  let children := match e with
    | .app .. =>
      let f := e.getAppFn
      if f.isConst then e.getAppArgs else #[f] ++ e.getAppArgs
    | .lam _ t b _ | .forallE _ t b _ => #[t, b]
    | .letE _ t v b _ => #[t, v, b]
    | .mdata _ b | .proj _ _ b => #[b]
    | _ => #[]
  let mut size := 1
  let mut heads : HeadCounts := {}
  let mut order := #[]
  for child in children do
    let summary ← headSummary child (budget - size)
    size := size + summary.size
    for name in summary.order do
      unless heads.contains name do order := order.push name
    heads := addHeads heads summary
  if e.isApp then
    if let .const c _ := e.getAppFn then
      if size ≥ bigSub then
        unless heads.contains c do order := order.push c
        let (k, z) := heads.getD c (0, 0)
        heads := heads.insert c (k + 1, z + size)
  let summary := { size, order, heads }
  if size < budget then modify (·.insert ⟨e⟩ summary)
  return summary

def bigHeads (e : Expr) : StateM (Nat × HeadCounts) Nat := do
  let (used, heads) ← get
  let summary := ((headSummary e (cap - used)).run {}).1
  set (used + summary.size, addHeads heads summary)
  return summary.size

/-- How many of the largest statements get a breakdown by application head. -/
def detailed : Nat := 10

/-- A declaration of GordieHowe's own modules, outside the generated certificates. -/
def ownModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i =>
    -- `moduleNames` maps the entire module array; do not rebuild it per declaration.
    let m := env.header.modules[i.toNat]!.module
    ((`GordieHowe).isPrefixOf m || (`GordieHoweCerts).isPrefixOf m) &&
      !(`GordieHoweCerts.Generated).isPrefixOf m

end StatementSize

open StatementSize in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut cache : ExprStructMap Nat := {}
  let mut rows : Array (Nat × Name) := #[]
  for (n, c) in env.constants.map₁.toList do
    unless ownModule env n do continue
    if n.isInternal then continue
    let (s, nextCache) := (treeSizeMemo c.type).run cache
    cache := nextCache
    if s ≥ threshold then rows := rows.push (s, n)
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  IO.println s!"statement size: {sorted.size} declaration(s) with a type of at least {threshold} \
    tree nodes (counted up to {cap})"
  for (s, n) in sorted do
    let m := (env.getModuleIdxFor? n).map (fun i => env.header.modules[i.toNat]!.module)
    IO.println s!"  {s}\t{n}\t{m.getD .anonymous}"
  IO.println s!"the heads of the largest repeated subterms of the {detailed} largest statements (tree nodes in subterms of at least {bigSub} nodes):"
  for (_, n) in sorted.toList.take detailed do
    let some c := env.find? n | continue
    let hs := ((bigHeads c.type).run (0, {})).2.2.toArray.qsort (fun a b => a.2.2 > b.2.2)
    IO.println s!"  {n}"
    for (h, k, z) in hs.toList.take 6 do
      IO.println s!"    {z}\tin {k} subterm(s) of at least {bigSub} nodes headed by\t{h}"
