-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.CellsLowering
public import GordieHoweNative.Language.RealizedProgram.Views
public import GordieHoweNative.Language.RealizedProgram.StructureCheck

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Placement`

The definitions of `GordieHowe.Language.RealizedProgram.Placement` that the certificate checkers run (the merge with the predicates, the challenge values' pointers and the checks of the structure records that read no value), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/Placement.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

open Twin

/-- **A merge of the predicates `ps` (from index `pid`) with a list `rs` keyed by predicate**:
a predicate that needs an entry (`need`) takes the next entry, which must be keyed by it and pass
`check` (else the failure `missing`); an entry keyed by a predicate that needs none, or left over,
fails `extra`. -/
def mergeE {β : Type} (need : Predicate → Bool)
    (check : ℕ → Predicate → β → Except StructFailure Unit) (missing extra : StructReason) :
    ℕ → List Predicate → List (ℕ × β) → Except StructFailure Unit
  | _, [], [] => .ok ()
  | _, [], kr :: _ => .error ⟨kr.1, 0, extra⟩
  | pid, pr :: ps, rs =>
    if need pr then
      match rs with
      | kr :: rs' =>
        if kr.1 = pid then
          seqE (check pid pr kr.2) (mergeE need check missing extra (pid + 1) ps rs')
        else .error ⟨pid, 0, missing⟩
      | [] => .error ⟨pid, 0, missing⟩
    else
      match rs with
      | kr :: _ =>
        if kr.1 = pid then .error ⟨pid, 0, extra⟩
        else mergeE need check missing extra (pid + 1) ps rs
      | [] => mergeE need check missing extra (pid + 1) ps rs

namespace Structure

/-- **The value holding challenge `j`**, read at the structure records' pointer (`chalValues`). -/
def chalOf (S : Structure) (j : ℕ) : Option ℕ := (NatTrie.ofList S.chalValues).get? j

end Structure

/-- **The routes into batch `b`**, in the routes' order: each one's predicate and part. -/
def Structure.batchRoutes (S : Structure) (b : ℕ) : List (ℕ × ℕ) :=
  S.routes.filterMap fun r =>
    match r.2 with
    | .batch b' j => if b' = b then some (r.1, j) else none
    | _ => none

section

variable (ir : RealizedProgram)

/-- **The realized route of predicate body `b`**: a field `equal` or a `mod_0` of a domain of the
program whose target is `realized q`, admitted at the conversions `js` (`realizedAdmitsAtB`). -/
def realizedRouteB (b : PredBody) (q : ℕ) (js : List ℕ) : Bool :=
  match b with
  | .equal d e e' (.realized q') =>
    q' == q && decide (d < ir.domains.length) && ir.realizedAdmitsAtB d e e' q js
  | .mod d 0 e e' real =>
    (match real.target with
      | some (.realized q') => q' == q
      | _ => false) && decide (d < ir.domains.length) && ir.realizedAdmitsAtB d e e' q js
  | _ => false

/-- **The batch routes, checked**: the routes into each batch are its parts with their indices, in
order (failure `batchRoutes`); one walk of the routes per batch. -/
def batchRoutesE (S : Structure) : Except StructFailure Unit :=
  allE (fun b B => guardE (S.batchRoutes b == B.parts.zipIdx) ⟨b, 0, .batchRoutes⟩) 0 ir.batches

/-- **The tables' groups in order**: `(t, g)` for `t` below the tables' count, `g` below `t`'s
group count. -/
def groupKeys : List (ℕ × ℕ) :=
  (List.range ir.tables.length).flatMap fun t => (List.range (ir.groupCountOf t)).map (t, ·)

/-- **Entry `k` of circuit `c` is the realization circuit `rc`**, `c` a circuit of a domain of the
program. -/
def hostAtB (c k : ℕ) (rc : RealCircuit) : Bool :=
  decide (c < ir.circuits.length) && decide ((ir.circuit c).domain < ir.domains.length) &&
    decide ((ir.circuit c).entries[k]? = some (.realization rc))

/-- **The LogUp hosts, checked**: their keys are the tables' groups in order (failure
`logupKeys`), each host the group's LogUp identity at its circuit entry (failure `logupPointer`). -/
def logupHostsE (S : Structure) : Except StructFailure Unit :=
  seqE (guardE (decide (S.logupHosts.map (·.1) = ir.groupKeys)) ⟨0, 0, .logupKeys⟩)
    (allE (fun _ h => guardE (ir.hostAtB h.2.1 h.2.2 (.logup h.1.1 h.1.2))
      ⟨h.1.1, h.1.2, .logupPointer⟩) 0 S.logupHosts)

/-- **The H halves' hosts, checked**: one merge of the predicates with the sorted `macHosts`; a
predicate whose H half needs a host (`PredBody.needsH`) has its own, the H half at its circuit
entry (failure `macHPointer`); failure `macHKeys` for a missing or an extra host. -/
def macHostsE (S : Structure) : Except StructFailure Unit :=
  mergeE (·.body.needsH)
    (fun pid _ h => guardE (ir.hostAtB h.1 h.2 (.macH pid)) ⟨pid, h.1, .macHPointer⟩)
    .macHKeys .macHKeys 0 ir.predicates S.macHosts

/-- **A value of `α`'s field holds every table's challenge**, read at the challenge values
(failure `alpha`). -/
def alphasE (S : Structure) : Except StructFailure Unit :=
  allE (fun t T => guardE (match S.chalOf T.alpha with
    | some v => decide (ir.valueField v = ir.chalField T.alpha)
    | none => false) ⟨t, T.alpha, .alpha⟩) 0 ir.tables

/-- **The H half of cross-field `equal` `p` is the compiler's own circuit, with a value holding
its key**, the key's value read through `ch` (`MacHNode`). -/
def macHNodeWithB (ch : ℕ → Option ℕ) (p : ℕ) : Bool :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real =>
    match real.hPredicate, real.blindX, ch real.key with
    | none, none, some v => decide (ir.valueField v = ir.chalField real.key)
    | _, _, _ => false
  | _ => false

/-- **An entry of a GKR circuit the honest prover covers** (`EntryOk`), the challenges' values
read through `ch`. -/
def entryOkWithB (ch : ℕ → Option ℕ) : CircuitEntry → Bool
  | .typeCheck p => decide (p < ir.predicates.length)
  | .alignment _ => true
  | .pred p => decide (p < ir.predicates.length)
  | .realization (.logup t g) => decide (t < ir.tables.length) && decide (g < ir.groupCountOf t)
  | .realization (.macH p) => decide (p < ir.predicates.length) && ir.macHNodeWithB ch p
  | .realization (.named _) => true
  | .realization (.unmodeled _) => true

/-- **Every entry of every circuit is covered**, read at the challenge values (failure `entry`,
naming the circuit and the entry). -/
def entriesE (S : Structure) : Except StructFailure Unit :=
  allE (fun c C => allE (fun k e => guardE (ir.entryOkWithB S.chalOf e) ⟨c, k, .entry⟩) 0
    C.entries) 0 ir.circuits

end

end GordieHowe.RealizedProgram
