-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Locality

/-!
# GordieHowe: the program reader of the compiled checkers

A checker that reads a program's values, predicates and tables by index is written once against
a **program reader** (`PReader`), a class with one field per thing it reads by index; the program
itself is an explicit argument, so that a kernel checker reads every other table of the program as
the same closed term the kernel already evaluated. Two readers instantiate it:

* `PReader.ofProgram ir` reads the program as the kernel definitions do (`RealizedProgram.value`,
  `predicate`, `readsT`): closed terms the kernel evaluates once. Each kernel checker is its
  generic form at the program and this reader.
* `PReader.ofCtx (PCtx.build ir)` reads a context built once per check: arrays of the values, the
  predicates and the reads table, read in `O(1)`. Compiled code runs the checkers at this reader
  (their `@[csimp]` theorems), and Lean's compiler specializes each generic checker at it, so the
  reads are array reads, not closure calls.

The two readers are equal (`PReader.ofCtx_build`, in
`GordieHowe/Language/RealizedProgram/Reader.lean`).
-/

local notation "ℕ" => Nat

public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A program reader**: what the compiled checkers read of a program by index. -/
class PReader where
  /-- Value `v` (`RealizedProgram.value`). -/
  value : ℕ → Value
  /-- Predicate `p` (`RealizedProgram.predicate`). -/
  predicate : ℕ → Predicate
  /-- The number of values. -/
  nValues : ℕ
  /-- The number of predicates. -/
  nPreds : ℕ
  /-- What value `v` reads from the run (`readsT`'s entry). -/
  reads : ℕ → List Read
  /-- What each value reads from the run, in value order (`readsL`). -/
  readsL : List (List Read)
  /-- What value `v` reads of the committed assignment (`asgReadsT`'s entry). -/
  asgReads : ℕ → List ℕ
  /-- The values shared expression `k` reads, each once (`closureT Expr.directNodes`'s entry). -/
  nodes : ℕ → List ℕ

/-- **The program reader of the kernel definitions**: the program's tables, as closed terms. -/
@[expose, instance_reducible] def PReader.ofProgram (ir : RealizedProgram) : PReader where
  value := ir.value
  predicate := ir.predicate
  nValues := ir.values.length
  nPreds := ir.predicates.length
  reads v := ir.readsT.getD v []
  readsL := ir.readsL
  asgReads v := ir.asgReadsT.getD v []
  nodes k := (ir.closureT Expr.directNodes).getD k []

/-- **The context of a compiled check**: the program, its values, predicates and reads tables as
arrays, built once (`PCtx.build`). -/
structure PCtx where
  /-- The values. -/
  values : Array Value
  /-- The predicates. -/
  preds : Array Predicate
  /-- The reads table's entries, in value order. -/
  readsL : List (List Read)
  /-- The reads table's entries, by value. -/
  reads : Array (List Read)
  /-- The committed-assignment reads table's entries, by value. -/
  asgReads : Array (List ℕ)
  /-- The closure table's entries, by shared expression. -/
  nodes : Array (List ℕ)

/-- **The program reader of a context**: array reads. -/
@[expose, instance_reducible] def PReader.ofCtx (c : PCtx) : PReader where
  value v := c.values[v]?.getD default
  predicate p := c.preds[p]?.getD default
  nValues := c.values.size
  nPreds := c.preds.size
  reads v := c.reads[v]?.getD []
  readsL := c.readsL
  asgReads v := c.asgReads[v]?.getD []
  nodes k := c.nodes[k]?.getD []

/-- **`readsStep` with the closure table `ct`** in place of `nodesOf`'s
(`readsStepWith_closureT`). -/
@[expose] def readsStepWith (ct : NatTrie (List ℕ)) (r : ℕ → List Read) (v : ℕ) (x : Value) :
    List Read :=
  match x.kind with
  | .pub (.expr e) =>
    insertAll [] ((e.directNodes ++ e.refs.flatMap fun k => ct.getD k []).flatMap r)
  | .pub (.opaque _ args) => insertAll [] (args.flatMap r)
  | .challenge c => [.chal c]
  | .late => [.late v]
  | .bits w _ => r w
  | .message u => [.late u]
  | _ => []

/-- **`asgStep` with the closure table `ct`** in place of `nodesOf`'s (`asgStepWith_closureT`). -/
@[expose] def asgStepWith (ir : RealizedProgram) (ct : NatTrie (List ℕ)) (r : ℕ → List ℕ) (v : ℕ)
    (x : Value) : List ℕ :=
  match x.kind with
  | .priv => [v]
  | .padCopy _ _ => [v]
  | .late => [v]
  | .bound e => ir.exprNodes e
  | .pub (.expr e) =>
    insertAll [] ((e.directNodes ++ e.refs.flatMap fun k => ct.getD k []).flatMap r)
  | .pub (.opaque _ args) => insertAll [] (args.flatMap r)
  | .bits w _ => r w
  | _ => []

/-- **The context of program `ir`**: its lists as arrays and its reads tables' entries
(`memoList`), the shared expressions' closure table built once for both. -/
@[expose] def PCtx.build (ir : RealizedProgram) : PCtx :=
  let cm := memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []
  let ct := cm.1
  let rl := memoList (readsStepWith ct) [] ir.values
  { values := ir.values.toArray
    preds := ir.predicates.toArray
    readsL := rl
    reads := rl.toArray
    asgReads := (memoList (asgStepWith ir ct) [] ir.values).toArray
    nodes := cm.2.toArray }

namespace PReader

variable (ir : RealizedProgram) [r : PReader]

/-- **A late value node** of a phase the program has (`RealizedProgram.IsLate`), at the reader. -/
@[expose] def IsLate (v : ℕ) : Prop :=
  (r.value v).kind.isLate = true ∧ 1 ≤ (r.value v).phase ∧ (r.value v).phase ≤ ir.phases

@[expose] instance (v : ℕ) : Decidable (PReader.IsLate ir v) := inferInstanceAs (Decidable (_ ∧ _))

/-- **A source value** (`RealizedProgram.IsSourceValue`), at the reader. -/
@[expose] def IsSourceValue (v : ℕ) : Prop := (r.value v).role = .source

@[expose] instance (v : ℕ) : Decidable (PReader.IsSourceValue v) :=
  inferInstanceAs (Decidable (_ = _))

/-- **The values an expression reads**, through the closure table (`RealizedProgram.nodesOf`). -/
@[expose] def nodesOf (e : Expr) : List ℕ := e.directNodes ++ e.refs.flatMap r.nodes

/-- **The values a predicate reads**, through the closure table (`RealizedProgram.predNodesM`). -/
@[expose] def predNodesM (b : PredBody) : List ℕ :=
  b.exprs.flatMap (PReader.nodesOf ·.2) ++ ir.tableCols b

end PReader

end GordieHowe.RealizedProgram
