-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Export
public import GordieHoweNative.Data
public import GordieHowe.Language.RealizedProgram.NatTrie
public import GordieHoweNative.Language.RealizedProgram

@[expose] public section

/-!
# GordieHowe: the plan's program, a deep embedding

The realized program of a compiled plan (its values, predicates, lookups, challenges and messages,
and GKR circuits), as plain data an exporter writes as Lean terms, like the generated plan files
(`GordieHowe/Generated/*`). The meaning of the data is `GordieHowe/Language/RealizedProgram/Semantics.lean`; the
checks of `Plan.Valid` that read it are `GordieHowe/Language/RealizedProgram/Valid.lean`.

**Identifiers.** Every table of the program is a list, and an identifier is a position in its
list: value `v` is `values[v]`, predicate `p` is `predicates[p]`, and so on for fields, domains,
challenges, lookup tables, batches and circuits. The names are provenance only. Value identifiers
are in declaration order, which the message order `MsgBefore` refines (lexicographic in phase, then
identifier).

**Coordinates.** A value is a tensor; its coordinates are numbered row-major, `0` to
`Value.size - 1`. An expression denotes a vector of coordinates of one field
(`Expr.len`); views (slices, rotations, index maps, broadcasting, reshapes) are written as
`Expr.reindex` with the explicit index map, a zero coordinate indexing a constant zero value
concatenated last.

**Shared expressions.** An expression is a DAG: each node read more than once, and each derived
value (a value with no storage: an affine view, a wiring view, a value bound to its digits), is an
entry of `GordieHowe.RealizedProgram.exprs`, read as `Expr.ref k`; entry `k` reads only entries of smaller index.

**Named operators** (`NamedOp`) are the C++ `OpSpec`s exported by name; their meanings are
`GordieHowe/Language/RealizedProgram/Ops.lean`.

**Phases** are numbered from `1`, as in the exported plan; phase `0` holds the values committed
before any challenge.

The definitions are in `GordieHoweNative/Language/RealizedProgram.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Expressions -/

namespace IndexMap

/-- **Entry `i` is the `i`-th entry of the concatenated runs.** -/
theorem entry_eq_getD_toList : ∀ (m : IndexMap) (i : Nat), m.entry i = m.toList.getD i 0
  | [], i => by simp [entry, toList]
  | (s, d, c) :: rest, i => by
    have ih := entry_eq_getD_toList rest (i - c)
    simp only [toList] at ih
    simp only [entry, toList, List.flatMap_cons]
    rw [List.getD_eq_getElem?_getD] at ih ⊢
    by_cases h : i < c
    · rw [if_pos h, List.getElem?_append_left (by simpa using h)]
      simp [h]
    · rw [if_neg h, List.getElem?_append_right (by simpa using Nat.le_of_not_lt h)]
      simpa using ih

end IndexMap

/-! ## Values -/

/-- Whether a kind is `priv`. -/
def Kind.isPriv : Kind → Bool
  | .priv => true
  | _ => false

/-- The packing-tree node of a value type (`bit`, or the subfield's name); none for `Field`. -/
def VType.nodeName : VType → Option String
  | .bit => some "bit"
  | .sub E => some E
  | .field => none

/-! ## Predicates -/

/-- Whether a role is `source`. -/
def PredRole.isSource : PredRole → Bool
  | .source => true
  | _ => false

/-- The degree of a predicate in challenge `c`, `0` when not listed. -/
def Predicate.deg (p : Predicate) (c : Nat) : Nat := (p.degree.lookup c).getD 0

/-! ## Lookups, challenges, messages, batches and circuits -/

/-- A C++ name read as a realization circuit (`RealCircuit.named`). -/
instance : Coe String RealCircuit := ⟨.named⟩

/-- A C++ name read as a realization input (`RealPub.named`). -/
instance : Coe String RealPub := ⟨.named⟩

namespace InputBlock

/-- **Block `b` holds input `q`**: `q` lies in `[first, first + len)`. -/
def Holds (q : Nat) (b : InputBlock) : Prop := b.first ≤ q ∧ q < b.first + b.len

end InputBlock

/-! ## The program -/

/-- **The bound of a member check on its entries**: `some q` for a check that accepts a member
whose every coordinate is below `q` (`MemberCheck.Kind.below`), `none` for any other. -/
def MemberCheck.entryBound? (m : MemberCheck) : Option Nat :=
  match m.kind? with
  | some (.below q _) => some q
  | _ => none

/-- **The coefficient `a = −3` of P-256**, as the natural `p − 3` (SEC 2 v2.0, §2.4.2, `secp256r1`;
`third_party/longfellow/lib/ec/p256.cc`). -/
def p256A : Nat :=
  115792089210356248762697446949407573530086143415290314195533631308867097853948

/-- **The coefficient `b` of P-256** (SEC 2 v2.0, §2.4.2, `secp256r1`;
`third_party/longfellow/lib/ec/p256.cc`). -/
def p256B : Nat :=
  41058363725152142129326129780047268409114441015993725554835256314039467401291

section

variable (ir : RealizedProgram)

/-! The trie a lookup reads is a closed term the kernel evaluates once per program. Compiled code
receives the program as an argument, so it would build the trie again at every call, a pass over
the list per lookup. Compiled code reads the list instead (`value_csimp`, `predicate_csimp`,
`expr_csimp`): a walk to the entry, with no allocation. -/

/-- **A value of a kind that lies in its domain has its domain's field.** -/
theorem valueField_of_allowsField {v : Nat} (hk : (ir.value v).kind.allowsField = false) :
    ir.valueField v = ir.domainField (ir.value v).domain := by
  simp [valueField, hk]

/-- **A value outside every domain has its domain's field.** -/
theorem valueField_of_field_none {v : Nat} (h : (ir.value v).field = none) :
    ir.valueField v = ir.domainField (ir.value v).domain := by
  unfold valueField
  rw [h]
  split <;> simp_all

/-- **A value of a field no domain commits has that field.** -/
theorem valueField_of_field_some {v f : Nat} (hk : (ir.value v).kind.allowsField = true)
    (h : (ir.value v).field = some f) : ir.valueField v = f := by
  simp [valueField, hk, h]

/-- **The value of the statement member `member`**: the first value that is it (`isMemberOf`). -/
def memberValue? (member : String) : Option Nat :=
  (List.range ir.values.length).find? (ir.isMemberOf member)

end

end GordieHowe.RealizedProgram
