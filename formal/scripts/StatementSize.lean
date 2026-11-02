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

The count stops at `cap` per declaration, so that a pathological statement costs at most `cap`
steps here. The report prints the declarations at or above the threshold, largest first (at the
cap, the size is at least the cap), and exits successfully: it is not a gate.
-/

open Lean Meta

namespace StatementSize

/-- The report threshold, in tree nodes. -/
def threshold : Nat := 1000000

/-- The count stops here. -/
def cap : Nat := 50000000

/-- The tree size of `e`, counted up to `cap` nodes. -/
partial def treeSize (e : Expr) : StateM Nat Unit := do
  if (← get) ≥ cap then return
  modify (· + 1)
  match e with
  | .app f a => treeSize f; treeSize a
  | .lam _ t b _ => treeSize t; treeSize b
  | .forallE _ t b _ => treeSize t; treeSize b
  | .letE _ t v b _ => treeSize t; treeSize v; treeSize b
  | .mdata _ b => treeSize b
  | .proj _ _ b => treeSize b
  | _ => pure ()

/-- The subtree size from which an application counts in `bigHeads`. -/
def bigSub : Nat := 10000

/-- The tree size of `e` (counted up to `cap` nodes over the whole statement); for every
application of a constant whose subtree has at least `bigSub` nodes, the number of such
occurrences and their total tree size are recorded under the constant. The heads with the largest
total name the repeated subterms that make a statement large. -/
partial def bigHeads (e : Expr) : StateM (Nat × Std.HashMap Name (Nat × Nat)) Nat := do
  if (← get).1 ≥ cap then return 0
  modify fun (n, m) => (n + 1, m)
  let sub ← match e with
    | .app .. => do
      let f := e.getAppFn
      let mut t := 1
      unless f.isConst do t := t + (← bigHeads f)
      for a in e.getAppArgs do t := t + (← bigHeads a)
      if let .const c _ := f then
        if t ≥ bigSub then
          modify fun (n, m) => (n, m.insert c (let (k, z) := m.getD c (0, 0); (k + 1, z + t)))
      pure t
    | .lam _ t b _ => return 1 + (← bigHeads t) + (← bigHeads b)
    | .forallE _ t b _ => return 1 + (← bigHeads t) + (← bigHeads b)
    | .letE _ t v b _ => return 1 + (← bigHeads t) + (← bigHeads v) + (← bigHeads b)
    | .mdata _ b => return 1 + (← bigHeads b)
    | .proj _ _ b => return 1 + (← bigHeads b)
    | _ => pure 1
  return sub

/-- How many of the largest statements get a breakdown by application head. -/
def detailed : Nat := 10

/-- A declaration of GordieHowe's own modules, outside the generated certificates. -/
def ownModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`GordieHowe).isPrefixOf m && !(`GordieHowe.Generated).isPrefixOf m

end StatementSize

open StatementSize in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut rows : Array (Nat × Name) := #[]
  for (n, c) in env.constants.map₁.toList do
    unless ownModule env n do continue
    if n.isInternal then continue
    let s := ((treeSize c.type).run 0).2
    if s ≥ threshold then rows := rows.push (s, n)
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  IO.println s!"statement size: {sorted.size} declaration(s) with a type of at least {threshold} \
    tree nodes (counted up to {cap})"
  for (s, n) in sorted do
    let m := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
    IO.println s!"  {s}\t{n}\t{m.getD .anonymous}"
  IO.println s!"the heads of the largest repeated subterms of the {detailed} largest statements (tree nodes in subterms of at least {bigSub} nodes):"
  for (_, n) in sorted.toList.take detailed do
    let some c := env.find? n | continue
    let hs := ((bigHeads c.type).run (0, {})).2.2.toArray.qsort (fun a b => a.2.2 > b.2.2)
    IO.println s!"  {n}"
    for (h, k, z) in hs.toList.take 6 do
      IO.println s!"    {z}\tin {k} subterm(s) of at least {bigSub} nodes headed by\t{h}"
