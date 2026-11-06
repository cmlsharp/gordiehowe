-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# Checked source-value roles

The source's honest-value classifier is separate from the compiler's realization role.
A role has one flat tag and an application-defined slot. The slot identifies the particular
witness component (for example a norm digit column); it is not a program value index.
The role records contain no field elements, prover programs, or certificate witnesses.
-/

public section

namespace GordieHowe.RealizedProgram

/-- **The flat classes of source values used by honest strategies.** -/
inductive SourceRole where
  | hashWord | hashBit | selection | aWitness | ringSigma | carry | stmtMember | input
  deriving Repr, DecidableEq, Inhabited

/-- **One source value's role**, tied to its field and packing position. -/
structure SourceRoleEntry where
  value : Nat
  role : SourceRole
  slot : Nat
  field : Nat
  node : Option NodeRef
  deriving Repr, DecidableEq, Inhabited

/-- **The role lookup table**, constructed once and shared by the checker or honest strategy. -/
@[expose] def sourceRoleTable (rs : List SourceRoleEntry) : NatTrie SourceRoleEntry :=
  rs.foldl (fun t r => t.set r.value r) .nil

/-- **An already constructed source-role classifier.** Store this record in the honest
strategy so a lookup never reconstructs its table from the original list. -/
structure SourceRoleClassifier where
  table : NatTrie SourceRoleEntry

/-- **Construct the shared classifier once**, before evaluating witness values. -/
@[expose] def sourceRoleClassifier (rs : List SourceRoleEntry) : SourceRoleClassifier :=
  ⟨sourceRoleTable rs⟩

/-- **Read a tag and slot from the stored table.** Missing entries stay absent. -/
@[expose] def SourceRoleClassifier.lookup (c : SourceRoleClassifier) (v : Nat) :
    Option (SourceRole × Nat) :=
  (c.table.get? v).map (fun r => (r.role, r.slot))

/-- **Role records are in strictly increasing value order.** This checks adjacent keys only. -/
@[expose] def sourceRolesOrderedB : List SourceRoleEntry → Bool
  | [] => true
  | [_] => true
  | a :: b :: rs => decide (a.value < b.value) && sourceRolesOrderedB (b :: rs)

/-- **A role record agrees with the actual source value.** The supplied value table and count are shared. -/
@[expose] def SourceRoleEntry.check (ir : RealizedProgram) (values : NatTrie Value)
    (valueCount : Nat) (r : SourceRoleEntry) : Bool :=
  let x := values.getD r.value default
  decide (r.value < valueCount) && decide (x.role = .source) &&
    decide (ir.fieldOfV x = r.field) && decide (x.node = r.node)

/-- **Whether a source value requires an honest role.** Bit and public expression views are derived;
private and bound source values require an explicit assignment, including explicit `input` roles. -/
@[expose] def Value.needsSourceRole (x : Value) : Bool :=
  decide (x.role = .source) && match x.kind with | .priv | .bound _ => true | _ => false

/-- **Every private or bound source value has exactly one correctly placed role.**
No missing entry defaults to `input`; unsorted or duplicate assignments are rejected. -/
@[expose] def sourceRolesB (ir : RealizedProgram) (rs : List SourceRoleEntry) : Bool :=
  let values := ir.valT
  let roles := sourceRoleTable rs
  let count := ir.values.length
  sourceRolesOrderedB rs && rs.all (SourceRoleEntry.check ir values count) &&
    allIdxC (fun v x => !x.needsSourceRole || (roles.get? v).isSome) ir.values 0

/-- **The optional role part.** An absent table makes no coverage claim; a present table
must classify every private or bound source value. -/
@[expose] def sourceRolesPartB (ir : RealizedProgram)
    (rs : Option (List SourceRoleEntry)) : Bool :=
  match rs with
  | none => true
  | some roles => sourceRolesB ir roles

end GordieHowe.RealizedProgram
