-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Export
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.MaskRow.Layout
public import GordieHowe.ProofSystem.Program.Transcript.Format

@[expose] public section

/-!
# GordieHowe: plan validity

`Plan.Valid P` is the plan-level validity of a compiled plan (`GordieHowe.RealizedProgram.Export.Plan`):
decidable conditions on the plan's data, each a predicate of its own. The validity of a plan with
its program (`GordieHowe.RealizedProgram.Valid`, `GordieHowe/Language/RealizedProgram/WithPlan.lean`)
includes them, and each configuration's exported validity proof decides them, but no proof step of
the plan-level theorem (`thm:backend`) reads them. The proofs consume the following conditions:

* the program's well-formedness, challenge order and pad order (`valid.program.wellFormed`,
  `valid.program.order` and `valid.program.pads`, fields of `GordieHowe.RealizedProgram.ValidAtNodes`);
* the realization's valid derivations (`GordieHowe.RealizedProgram.Derivable`), with the
  validity of each table (`GordieHowe.RealizedProgram.TableOk`);
* the checks of each domain (`GordieHowe.RealizedProgram.fieldOkB`): its packing edges and tree, placements,
  views, circuit inputs, batches and quadratic triples, and its Ligero certificate;
* the layout facts of each domain's Ligero tableau (`L.valid`, `Ligero.Relative.Shape.Valid`).

The conditions at `Plan.schemaVersion = 3`:

* `Plan.PackingAdmissible`: every domain's packing tree is admissible;
* `Plan.FieldsDecode`: every field decodes to a field of the registry `fieldRegistry`;
* `Plan.LookupsFit`: the lookup groups fit their domain's characteristic;
* `Plan.NoWrapHolds`: the no-wrap conditions of the certify conditions, the MAC equalities, the
  modular equalities and the filtered permutations;
* `Plan.LigeroShapesValid`: each domain's Ligero numbers satisfy the layout facts;
* `Plan.TranscriptFits`: the extended Fiat–Shamir points follow the stream rule and the
  transcript's sizes fit the setting's bounds;
* `Plan.MessageSpacesValid`: every late message's spaces are nodes of its domain's tree.

`GordieHowe.RealizedProgram.ChallengeOrder`, `GordieHowe.RealizedProgram.PadOrderValid`, `GordieHowe.RealizedProgram.TypeSources` and
`GordieHowe.RealizedProgram.TargetsAdmit` read the value table and the predicates of the realized program (`GordieHowe.RealizedProgram`,
`GordieHowe/Language/RealizedProgram/Valid.lean`, combined with this file's conditions in `GordieHowe.RealizedProgram.Valid`). No
condition bounds the challenges' degrees: the frontend's lowerings read the exported per-predicate
degrees.

**Data the plan does not carry**, so the conditions above cannot check it:
* for `Plan.LigeroShapesValid`: the line certificate's agreement threshold `A`, exceptional count
  `B` and Johnson certificate `(m, B_j, H)`, and the profile's target error, which the column bound
  reads (`GordieHowe/Applications/Shared/Tableaux.lean`, e.g. `gold4K512Line`, `gold4K512Column_le`); the
  evaluation-point domain size `q` (the registry supplies it per field);
* for `Plan.TranscriptFits`: the round count of the circuit proofs
  (`GordieHowe.SPBCS.ProofSystemTranscript.Bounds.n_le`, `≤ 20795`), which needs the GKR circuits' round structure; the
  skip phase's index bits;
* the MAC's reduction taps: the plan exports the MAC's `convMax` itself, and no condition
  recomputes it with `Conv.convMax`.
-/

namespace GordieHowe.RealizedProgram.Export

/-! ## Lookups by name -/

/-- **The characteristic floor of a domain**: `characteristicFloor`, or the characteristic when the
exporter writes `0`. No condition checks the exported value against the characteristic: the
conditions that read the floor trust it. The C++ exporter writes the characteristic `p`. -/
def Domain.floor (d : Domain) : Nat :=
  if d.characteristicFloor = 0 then d.field.characteristic else d.characteristicFloor

/-- The characteristic of the field of domain `name`; `0` when there is no such domain, so every
condition `x < P.charOf name` fails. -/
def Plan.charOf (P : Plan) (name : String) : Nat :=
  ((P.domain name).map (·.field.characteristic)).getD 0

/-- The characteristic floor of domain `name`; `0` when there is no such domain. -/
def Plan.floorOf (P : Plan) (name : String) : Nat := ((P.domain name).map Domain.floor).getD 0

/-- The established bound of the range request named `name`. -/
def Plan.bound? (P : Plan) (name : String) : Option Nat :=
  (P.request name).map (·.realization.bound)

/-! ## The packing trees -/

/-- **Every domain's packing tree is admissible** (`Domain.WellFormed`: the edges form a tree in
processing order and every edge is realizable). Consumed by the tree domain's construction from the
plan's tree: `TreeSpec` and `TreeSpec.layoutDomain` (`GordieHowe/ProofSystem/RingSwitching/TreeLayoutDomain.lean`) take the
tree's stages and their modes, `MaskScheme.squaringChainOver` the squaring-chain counts. -/
def Plan.PackingAdmissible (P : Plan) : Prop := ∀ d ∈ P.domains, d.WellFormed

instance (P : Plan) : Decidable P.PackingAdmissible :=
  inferInstanceAs (Decidable (∀ d ∈ P.domains, _))

/-! ## The field registry -/

/-- **A subfield the Lean has**, as the plan writes it: its specification and the bytes of one of
its elements in the C++ encoding (`kBytes` of its class; `0`: the C++ writes no element of this
subfield on its own). -/
structure SubfieldEntry where
  /-- The specification. -/
  spec : FieldSpec
  /-- The bytes of an element. -/
  bytes : Nat
  deriving Repr, DecidableEq

/-- **A field the Lean has**: its specification as the plan writes it, the bytes of an element in
the C++ encoding (`F::kBytes`), the size `q` of the evaluation-point domain on which the Lean's
points are injective (`Ligero.Relative.Shape.Valid`), and the subfields the Lean has in it. -/
structure FieldEntry where
  /-- The specification. -/
  spec : FieldSpec
  /-- The bytes of an element. -/
  bytes : Nat
  /-- The size of the evaluation-point domain. -/
  points : Nat
  /-- The subfields. -/
  subfields : List SubfieldEntry
  deriving Repr, DecidableEq

/-- The prime subfield `GF(2)` of a binary field, as the node `bit` (`⊥`, the image of `ZMod 2`). -/
def bitSubfield : SubfieldEntry := ⟨{ name := "bit", characteristic := 2, degree := 1 }, 0⟩

/-- The prime subfield `F_p` of an odd-characteristic field (`⊥`, the image of `ZMod p` under
`algebraMap`), whose elements the C++ writes in `bytes` bytes. -/
def primeSubfield (p bytes : Nat) : SubfieldEntry :=
  ⟨{ name := "GF(p^1)", characteristic := p, degree := 1 }, bytes⟩

/-- **`GF(2^16)` in `GF(2^128)`**: the Lean `gf2_128Subfield` (`GordieHowe/Foundations/Fields/GF2_128Selection.lean`,
the fixed field of the `2^16`-power Frobenius), with the modulus the C++ exports (the minimal
polynomial of its subfield generator), which the Lean does not state. -/
def gf2_16In128 : FieldSpec :=
  { name := "GF(2^16)", characteristic := 2, degree := 16,
    modulus := [16, 15, 13, 12, 11, 9, 8, 7, 5, 4, 0] }

/-- **`GF(2^16)` in `GF(2^256)`**: the Lean `gf2_256Subfield` (`GordieHowe/Foundations/Fields/GF2_256Selection.lean`),
with the modulus the C++ exports, which the Lean does not state. -/
def gf2_16In256 : FieldSpec :=
  { name := "GF(2^16)", characteristic := 2, degree := 16,
    modulus := [16, 14, 13, 12, 9, 8, 5, 3, 0] }

/-- **`GF(2^128)`**: the Lean `GF2_128` (`GordieHowe/Foundations/Fields/GF2_128.lean`), `GF(2)[X]/(X^128 + X^7 + X^2 +
X + 1)`, `16` bytes, points `2^16`; subfields `bit` and `GF(2^16)`, the Lean `gf2_128Subfield`
(`GordieHowe/Foundations/Fields/GF2_128Selection.lean`, the fixed field of the `2^16`-power Frobenius). The subfield's
modulus is the one the C++ exports (the minimal polynomial of its subfield generator); the Lean
does not state it. -/
def gf2_128Entry : FieldEntry where
  spec := { name := "GF(2^128)", characteristic := 2, degree := 128,
            modulus := [128, 7, 2, 1, 0] }
  bytes := 16
  points := 2 ^ 16
  subfields := [bitSubfield, ⟨gf2_16In128, 0⟩]

/-- **`GF(2^256)`**: the Lean `GF2_256` (`GordieHowe/Foundations/Fields/GF2_256.lean`), `GF(2)[X]/(X^256 + X^10 + X^5 +
X^2 + 1)`, `32` bytes, points `2^16`; subfields `bit` and `GF(2^16)`, the Lean `gf2_256Subfield`
(`GordieHowe/Foundations/Fields/GF2_256Selection.lean`), its modulus as the C++ exports it. -/
def gf2_256Entry : FieldEntry where
  spec := { name := "GF(2^256)", characteristic := 2, degree := 256,
            modulus := [256, 10, 5, 2, 0] }
  bytes := 32
  points := 2 ^ 16
  subfields := [bitSubfield, ⟨gf2_16In256, 0⟩]

/-- **`F_q^9`**, `q = 12289`: the Lean `FalconNativeField9` (`GordieHowe/Applications/Falcon512/Native/Fields/FalconNative9.lean`),
`ZMod 12289 [X]/(X^9 - 2)` (the plan writes the coefficients `1, q - 2`), `18` bytes (`Fp14_N`,
`9 · 2`), points `q`; subfield `GF(p^1)`, `2` bytes. -/
def falconNative9Entry : FieldEntry where
  spec := { name := "F_q^9", characteristic := 12289, degree := 9, modulus := [9, 0],
            modulusCoeffs := [1, 12287] }
  bytes := 18
  points := 12289
  subfields := [primeSubfield 12289 2]

/-- **`F_q^20`**, `q = 12289`: the Lean `FalconNativeField20` (`GordieHowe/Applications/Falcon512/Native/Fields/FalconNative20.lean`), the
tower `u^4 = 11`, `v^5 = u + 2`, `35` bytes (`NativeWide`, `⌈20 · 14 / 8⌉`), points `q`; subfield
`GF(p^1)`, `2` bytes. -/
def falconNative20Entry : FieldEntry where
  spec := { name := "F_q^20", characteristic := 12289, degree := 20,
            tower := [{ name := "u", degree := 4, relation := [(11, [0])] },
              { name := "v", degree := 5, relation := [(1, [1, 0]), (2, [0, 0])] }] }
  bytes := 35
  points := 12289
  subfields := [primeSubfield 12289 2]

/-- **`F_q^6`**, `q = 8380417`: the Lean `MLDSANativeField6` (`GordieHowe/Applications/MLDSA44/Native/Fields/MLDSANative6.lean`),
`ZMod q [X]/(X^6 - 7)`, `18` bytes (`Fp24_6`, `6 · 3`), points `q`; subfield `GF(p^1)`, `3`
bytes. -/
def mldsaNative6Entry : FieldEntry where
  spec := { name := "F_q^6", characteristic := 8380417, degree := 6, modulus := [6, 0],
            modulusCoeffs := [1, 8380410] }
  bytes := 18
  points := 8380417
  subfields := [primeSubfield 8380417 3]

/-- **`F_q^11`**, `q = 8380417`: the Lean `MLDSANativeField11` (`GordieHowe/Applications/MLDSA44/Native/Fields/MLDSANative11.lean`),
`ZMod q [X]/(X^11 - 2)`, `32` bytes (`NativeWide`, `⌈11 · 23 / 8⌉`), points `q`; subfield
`GF(p^1)`, `3` bytes. -/
def mldsaNative11Entry : FieldEntry where
  spec := { name := "F_q^11", characteristic := 8380417, degree := 11, modulus := [11, 0],
            modulusCoeffs := [1, 8380415] }
  bytes := 32
  points := 8380417
  subfields := [primeSubfield 8380417 3]

/-- **Goldilocks²**: the Lean `GoldilocksExt2` (`GordieHowe/Foundations/Fields/Goldilocks.lean`), `ZMod p [X]/(X^2 - 7)`,
`16` bytes, points `2^32` (the Goldilocks subgroup encoder); subfield `GF(p^1)`, `8` bytes. -/
def goldilocksExt2Entry : FieldEntry where
  spec := { name := "Goldilocks^2", characteristic := 18446744069414584321, degree := 2,
            modulus := [2, 0], modulusCoeffs := [1, 18446744069414584314] }
  bytes := 16
  points := 2 ^ 32
  subfields := [primeSubfield 18446744069414584321 8]

/-- **Goldilocks⁴**: the Lean `GoldilocksExt4` (`GordieHowe/Foundations/Fields/GoldilocksQuartic.lean`),
`ZMod p [X]/(X^4 - 7)`, `32` bytes, points `2^32`; subfield `GF(p^1)`, `8` bytes. -/
def goldilocksExt4Entry : FieldEntry where
  spec := { name := "Goldilocks^4", characteristic := 18446744069414584321, degree := 4,
            modulus := [4, 0], modulusCoeffs := [1, 18446744069414584314] }
  bytes := 32
  points := 2 ^ 32
  subfields := [primeSubfield 18446744069414584321 8]

/-- **The P-256 base field** `ZMod p256`: `32` bytes, points `p256`; no subfield. -/
def p256Entry : FieldEntry where
  spec := { name := "F_p256",
            characteristic :=
              115792089210356248762697446949407573530086143415290314195533631308867097853951,
            degree := 1 }
  bytes := 32
  points := 115792089210356248762697446949407573530086143415290314195533631308867097853951
  subfields := []

/-- **The prime field `Fp128`** `ZMod p`, `p = 2^128 − 2^108 + 1` (the C++ `Fp128`, RSA's prime
field): `16` bytes, points `2^108` (the subgroup encoder on its roots of unity,
`p − 1 = 2^108 (2^20 − 1)`; `lib/gordiehowe/instances.h`, `RsFp128`); no subfield. -/
def fp128Entry : FieldEntry where
  spec := { name := "Fp128", characteristic := 340282042402384805036647824275747635201,
            degree := 1 }
  bytes := 16
  points := 2 ^ 108
  subfields := []

/-- **The field registry**: the fields the Lean has, each with the Lean type named in its entry's
docstring. -/
def fieldRegistry : List FieldEntry :=
  [gf2_128Entry, gf2_256Entry, falconNative9Entry, falconNative20Entry, mldsaNative6Entry,
    mldsaNative11Entry, goldilocksExt2Entry, goldilocksExt4Entry, p256Entry, fp128Entry]

/-- The registry entry of a domain's field: the first entry whose specification is the field's. -/
def Domain.entry? (d : Domain) : Option FieldEntry := fieldRegistry.find? (·.spec = d.field)

/-- **The degree of a node of a domain's tree** by name: the field's, or a declared subfield's. -/
def Domain.nodeDegree (d : Domain) (name : String) : Option Nat :=
  if name = d.field.name then some d.field.degree
  else (d.subfields.find? (·.name = name)).map (·.degree)

/-- **A domain's fields decode against the registry entry `e`**: the field is `e`'s, every declared
subfield is one of `e`'s subfields with the field's characteristic and a degree dividing the
field's, the masking subfield is the field or a declared subfield, and every declared node of the
packing tree has the degree the edges write. -/
structure FieldEntry.Decodes (e : FieldEntry) (d : Domain) : Prop where
  /-- The field is the entry's. -/
  field : e.spec = d.field
  /-- Every declared subfield is a subfield of the entry. -/
  subfields : ∀ s ∈ d.subfields, ∃ se ∈ e.subfields, se.spec = s
  /-- Every declared subfield has the field's characteristic. -/
  char_eq : ∀ s ∈ d.subfields, s.characteristic = d.field.characteristic
  /-- Every declared subfield's degree divides the field's. -/
  degree_dvd : ∀ s ∈ d.subfields, s.degree ∣ d.field.degree
  /-- The masking subfield is the field or a declared subfield. -/
  masking : d.maskingSubfield = d.field.name ∨ ∃ s ∈ d.subfields, s.name = d.maskingSubfield
  /-- Every declared child of an edge has the degree the edge writes. -/
  children : ∀ pe ∈ d.packing, pe.declared = true → d.nodeDegree pe.child = some pe.childDegree
  /-- Every edge into the field has the field's degree as its parent's. -/
  roots : ∀ pe ∈ d.packing, pe.parent = d.field.name → pe.parentDegree = d.field.degree

theorem FieldEntry.decodes_iff (e : FieldEntry) (d : Domain) : e.Decodes d ↔
    e.spec = d.field ∧ (∀ s ∈ d.subfields, ∃ se ∈ e.subfields, se.spec = s) ∧
      (∀ s ∈ d.subfields, s.characteristic = d.field.characteristic) ∧
      (∀ s ∈ d.subfields, s.degree ∣ d.field.degree) ∧
      (d.maskingSubfield = d.field.name ∨ ∃ s ∈ d.subfields, s.name = d.maskingSubfield) ∧
      (∀ pe ∈ d.packing, pe.declared = true → d.nodeDegree pe.child = some pe.childDegree) ∧
      (∀ pe ∈ d.packing, pe.parent = d.field.name → pe.parentDegree = d.field.degree) :=
  ⟨fun h => ⟨h.field, h.subfields, h.char_eq, h.degree_dvd, h.masking, h.children, h.roots⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩

instance (e : FieldEntry) (d : Domain) : Decidable (e.Decodes d) :=
  decidable_of_iff _ (e.decodes_iff d).symm

/-- **A domain's fields decode**: the domain has a registry entry and decodes against it. -/
def Domain.FieldsDecode (d : Domain) : Prop :=
  match d.entry? with
  | some e => e.Decodes d
  | none => False

instance (d : Domain) : Decidable d.FieldsDecode := by
  unfold Domain.FieldsDecode
  split <;> infer_instance

/-- **Every field decodes** to a field of the registry, with its subfields and their degrees.
Consumed by every instance's field data: the domain field, the masking subfield (`MaskSubfield`,
e.g. `MLDSA44.Native.mldsa6Mask`), the packing subfields (`gf2_256Subfield`) and the characteristic `p`
of `[CharP F p]` that `Plan.LookupsFit` and `Plan.NoWrapHolds` compare against. -/
def Plan.FieldsDecode (P : Plan) : Prop := ∀ d ∈ P.domains, d.FieldsDecode

instance (P : Plan) : Decidable P.FieldsDecode :=
  inferInstanceAs (Decidable (∀ d ∈ P.domains, _))

/-! ## The lookups -/

/-- **A lookup group fits the characteristic `p`** of its domain's field: fewer needles than `p`, the
table embeds into the field, the late support within the table (`Range.rangeArgument_sound`'s
`hSdyn`), and the needles within the group's capacity when it has one. -/
structure Table.Fits (p : Nat) (t : Table) : Prop where
  /-- Fewer needles than the characteristic. -/
  needles_lt : t.staticNeedles + t.lateNeedles < p
  /-- The table embeds into the field. -/
  size_le : t.size ≤ p
  /-- The late support lies in the table. -/
  sdyn_le : t.sdyn ≤ t.size
  /-- The needles fit the capacity (`0`: unbounded). -/
  capacity : t.capacity = 0 ∨ t.staticNeedles + t.lateNeedles ≤ t.capacity

theorem Table.fits_iff (p : Nat) (t : Table) : t.Fits p ↔
    t.staticNeedles + t.lateNeedles < p ∧ t.size ≤ p ∧ t.sdyn ≤ t.size ∧
      (t.capacity = 0 ∨ t.staticNeedles + t.lateNeedles ≤ t.capacity) :=
  ⟨fun h => ⟨h.needles_lt, h.size_le, h.sdyn_le, h.capacity⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

instance (p : Nat) (t : Table) : Decidable (t.Fits p) := decidable_of_iff _ (t.fits_iff p).symm

/-- **A request's late needles lie in its group's late support**: a request with late needles names
a group of its domain whose late support covers its honest bound. -/
def Plan.LateSupported (P : Plan) (r : Request) : Prop :=
  0 < r.realization.lateNeedles →
    ∃ t ∈ P.tables[r.realization.table]?, t.domain = r.domain ∧ r.honest ≤ t.sdyn

instance (P : Plan) (r : Request) : Decidable (P.LateSupported r) := by
  unfold Plan.LateSupported
  infer_instance

/-- **The lookups fit**: every table group fits the characteristic of its domain's field, and every
request with late needles lies in its group's late support. -/
structure Plan.LookupsFit (P : Plan) : Prop where
  /-- Every group fits its domain's characteristic. -/
  tables : ∀ t ∈ P.tables, t.Fits (P.charOf t.domain)
  /-- Every late request lies in its group's late support. -/
  late : ∀ r ∈ P.requests, P.LateSupported r

theorem Plan.lookupsFit_iff (P : Plan) : P.LookupsFit ↔
    (∀ t ∈ P.tables, t.Fits (P.charOf t.domain)) ∧ ∀ r ∈ P.requests, P.LateSupported r :=
  ⟨fun h => ⟨h.tables, h.late⟩, fun h => ⟨h.1, h.2⟩⟩

instance (P : Plan) : Decidable P.LookupsFit := decidable_of_iff _ P.lookupsFit_iff.symm

/-! ## The no-wrap conditions -/

/-- **The natural number of an exported `certify` value**: the exporter writes each side of a
`certify` condition exactly, as a nonnegative integer, so the value is the integer itself. -/
def certValue (z : Int) : Nat := z.toNat

/-- **A comparison of a `certify` condition holds**: `lhs < rhs` (`op = 0`), `lhs ≤ rhs`
(`op = 1`) or `lhs = rhs` (`op = 2`). -/
def CertOp (op : Int) (lhs rhs : Nat) : Prop :=
  (op = 0 ∧ lhs < rhs) ∨ (op = 1 ∧ lhs ≤ rhs) ∨ (op = 2 ∧ lhs = rhs)

instance (op : Int) (lhs rhs : Nat) : Decidable (CertOp op lhs rhs) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- **A `certify` condition holds**: its comparison holds on the exported values (`certValue`); a
condition without `lhs`, `rhs` or `op` does not hold. -/
def GadgetParams.CertifyHolds (g : GadgetParams) : Prop :=
  match g.params.lookup "lhs" with
  | none => False
  | some l =>
    match g.params.lookup "rhs" with
    | none => False
    | some r =>
      match g.params.lookup "op" with
      | none => False
      | some op => CertOp op (certValue l) (certValue r)

instance (g : GadgetParams) : Decidable g.CertifyHolds := by
  unfold GadgetParams.CertifyHolds
  split
  · infer_instance
  · split
    · infer_instance
    · split <;> infer_instance

/-- **A request's established bound is admissible**: its honest bound is at most its established
bound, which is at most its maximum. -/
def Request.Admits (r : Request) : Prop :=
  r.honest ≤ r.realization.bound ∧ r.realization.bound ≤ r.max

instance (r : Request) : Decidable r.Admits := inferInstanceAs (Decidable (_ ∧ _))

/-- **The limbs' maximum** of a single-group MAC at the integer bound `p` and low radix `B`:
`(p - 2) / (2 + 2 B) + 1`. -/
def macDmax (p B : Nat) : Nat := (p - 2) / (2 + 2 * B) + 1

/-- **The maximum of `mac.low`'s bound**: `(p - 1) / 2` when the limbs are searched jointly
(`macDmax p B < max B (acc_max / (2 B) + 1)`), else `macDmax`. -/
def macLowMax (p B accMax : Nat) : Nat :=
  if macDmax p B < max B (accMax / (2 * B) + 1) then (p - 1) / 2 else macDmax p B

/-- **The maximum of `mac.high`'s bound**: `(p - 1) / (2 B)` when the limbs are searched jointly,
else `macDmax`. -/
def macHighMax (p B accMax : Nat) : Nat :=
  if macDmax p B < max B (accMax / (2 * B) + 1) then (p - 1) / (2 * B) else macDmax p B

/-- **The numbers of a single-group MAC equality**: the integer bound `p`, the low radix `B`, the
accumulator bound `acc_max` and the established bounds of `mac.low`, `mac.high` and `mac.nowrap`. -/
structure SingleMACNumbers where
  /-- The integer bound (the characteristic floor). -/
  p : Nat
  /-- The low radix `B`. -/
  radix : Nat
  /-- The accumulator bound. -/
  accMax : Nat
  /-- The established bound of `mac.low`. -/
  low : Nat
  /-- The established bound of `mac.high`. -/
  high : Nat
  /-- The established bound of `mac.nowrap`. -/
  nowrap : Nat

/-- **The conditions of a single-group MAC equality** on the numbers: `B ≥ 1`, `acc_max < p`,
the limbs' worst case below `p`, and the established bounds admissible against the honest bounds
`B`, `acc_max / (2 B) + 1`, `acc_max + 1` and maxima `macLowMax`, `macHighMax`, `p - 1`. -/
structure SingleMACNumbers.Valid (n : SingleMACNumbers) : Prop where
  radix_pos : 0 < n.radix
  accMax_lt : n.accMax < n.p
  limbs_lt : 2 * (n.low - 1) + 2 * n.radix * (n.high - 1) < n.p
  low_ge : n.radix ≤ n.low
  low_le : n.low ≤ macLowMax n.p n.radix n.accMax
  high_ge : n.accMax / (2 * n.radix) + 1 ≤ n.high
  high_le : n.high ≤ macHighMax n.p n.radix n.accMax
  nowrap_ge : n.accMax + 1 ≤ n.nowrap
  nowrap_le : n.nowrap ≤ n.p - 1

theorem SingleMACNumbers.valid_iff (n : SingleMACNumbers) : n.Valid ↔
    0 < n.radix ∧ n.accMax < n.p ∧ 2 * (n.low - 1) + 2 * n.radix * (n.high - 1) < n.p ∧
      n.radix ≤ n.low ∧ n.low ≤ macLowMax n.p n.radix n.accMax ∧
      n.accMax / (2 * n.radix) + 1 ≤ n.high ∧ n.high ≤ macHighMax n.p n.radix n.accMax ∧
      n.accMax + 1 ≤ n.nowrap ∧ n.nowrap ≤ n.p - 1 :=
  ⟨fun h => ⟨h.radix_pos, h.accMax_lt, h.limbs_lt, h.low_ge, h.low_le, h.high_ge, h.high_le,
      h.nowrap_ge, h.nowrap_le⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩⟩

instance (n : SingleMACNumbers) : Decidable n.Valid := decidable_of_iff _ n.valid_iff.symm

/-- **A single-group MAC record is valid** (two quotient digits): its accumulator bound is
`nch · convMax + 1`, the high limb's coefficient is twice the low radix `B = nLow`, and the
numbers at the characteristic floor of the accumulator domain with the established bounds of
`<name>.low`, `.high`, `.nowrap` satisfy `SingleMACNumbers.Valid`. -/
def MAC.SingleValid (P : Plan) (m : MAC) : Prop :=
  match P.bound? (m.name ++ ".low") with
  | none => False
  | some l =>
    match P.bound? (m.name ++ ".high") with
    | none => False
    | some h =>
      match P.bound? (m.name ++ ".nowrap") with
      | none => False
      | some w =>
        m.accMax = m.nch * m.convMax + 1 ∧ m.radixValue = 2 * m.nLow ∧
          (SingleMACNumbers.mk (P.floorOf m.accDomain) m.nLow m.accMax l h w).Valid

instance (P : Plan) (m : MAC) : Decidable (m.SingleValid P) := by
  unfold MAC.SingleValid
  split
  · infer_instance
  · split
    · infer_instance
    · split <;> infer_instance

/-- **Chunk runs start at `pos` and follow each other**: each run `(first, count)` starts where
the previous one ends. -/
def RunsFrom : List (Nat × Nat) → Nat → Prop
  | [], _ => True
  | (first, count) :: rest, pos => first = pos ∧ RunsFrom rest (pos + count)

instance decidableRunsFrom : (l : List (Nat × Nat)) → (pos : Nat) → Decidable (RunsFrom l pos)
  | [], _ => isTrue trivial
  | (first, count) :: rest, pos =>
    have := decidableRunsFrom rest (pos + count)
    inferInstanceAs (Decidable (first = pos ∧ RunsFrom rest (pos + count)))

/-- **The conditions of a grouped MAC equality** for the record `m` at the characteristic `p`
of its accumulator domain, the established bounds `digit` of `<name>.gq` and `final` of
`<name>.final.q`, and the maximum `finalMax` of `<name>.final.q`: the groups are runs of
consecutive chunks covering the `nch` chunks, one per group; every group's
bound `|g| · convMax` is at most the group bound (`groupMax_le`), which is below `p`
(`groupBound_lt`) and below `2 T^digits` (`groupBound_lt_quot`); the residue tail below `p`
(`tail_lt`); the final sum's no-wrap conditions (`final_left`, `final_right`: the interval
`[-1, groups + 1]` with `m = 2`, `qlo = 0`); the established bounds admissible against the honest
bounds `T` and `⌊(groups + 1) / 2⌋ + 1`, the final one at most `finalMax`. -/
structure MAC.GroupedBounds (m : MAC) (p digit final finalMax : Nat) : Prop where
  runs : RunsFrom m.groupChunks 0
  runs_cover : (m.groupChunks.map Prod.snd).sum = m.nch
  runs_length : m.groupChunks.length = m.groups
  groupMax_le : ∀ run ∈ m.groupChunks, run.2 * m.convMax ≤ m.groupBound
  groupBound_lt : m.groupBound < p
  groupBound_lt_quot : m.groupBound < 2 * m.quotientBase ^ m.quotientDigits
  tail_lt : 2 * (digit ^ m.quotientDigits - 1) + 1 < p
  final_left : m.groups + 1 < p
  final_right : 2 * (final - 1) + 1 < p
  digit_ge : m.quotientBase ≤ digit
  digit_le : digit ≤ m.quotientBase
  final_ge : (m.groups + 1) / 2 + 1 ≤ final
  final_le : final ≤ finalMax

theorem MAC.groupedBounds_iff (m : MAC) (p digit final finalMax : Nat) :
    m.GroupedBounds p digit final finalMax ↔
      RunsFrom m.groupChunks 0 ∧ (m.groupChunks.map Prod.snd).sum = m.nch ∧
      m.groupChunks.length = m.groups ∧
      (∀ run ∈ m.groupChunks, run.2 * m.convMax ≤ m.groupBound) ∧ m.groupBound < p ∧
      m.groupBound < 2 * m.quotientBase ^ m.quotientDigits ∧
      2 * (digit ^ m.quotientDigits - 1) + 1 < p ∧ m.groups + 1 < p ∧
      2 * (final - 1) + 1 < p ∧ m.quotientBase ≤ digit ∧ digit ≤ m.quotientBase ∧
      (m.groups + 1) / 2 + 1 ≤ final ∧ final ≤ finalMax :=
  ⟨fun h => ⟨h.runs, h.runs_cover, h.runs_length, h.groupMax_le, h.groupBound_lt,
      h.groupBound_lt_quot, h.tail_lt, h.final_left, h.final_right, h.digit_ge, h.digit_le,
      h.final_ge, h.final_le⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩⟩

instance (m : MAC) (p digit final finalMax : Nat) :
    Decidable (m.GroupedBounds p digit final finalMax) :=
  decidable_of_iff _ (m.groupedBounds_iff p digit final finalMax).symm

/-- **A grouped MAC record is valid**: the requests `<name>.gq` and `<name>.final.q`
exist and the record satisfies `MAC.GroupedBounds` at the characteristic of its accumulator domain
with their established bounds and the final quotient's maximum. -/
def MAC.GroupedValid (P : Plan) (m : MAC) : Prop :=
  match P.request (m.name ++ ".gq") with
  | none => False
  | some d =>
    match P.request (m.name ++ ".final.q") with
    | none => False
    | some f =>
      m.GroupedBounds (P.charOf m.accDomain) d.realization.bound f.realization.bound f.max

instance (P : Plan) (m : MAC) : Decidable (m.GroupedValid P) := by
  unfold MAC.GroupedValid
  split
  · infer_instance
  · split <;> infer_instance

/-- **The conditions of a single-group MAC equality with one derived quotient digit** for the
record `m` at the integer bound `p` (the characteristic floor of its accumulator domain), the
established bound `digit` of `<name>.q` and its maximum `digitMax`: the accumulator bound is
`nch · convMax + 1`; the quotient's honest bound `n_high` is `⌊acc_max / 2⌋ + 1` (the C++'s
`Qmax + 1` at `m = 2`, `qlo = 0`, `compiler/mod.h`, `quotient`); the two sides of
`acc = bits(T) + 2 q` lie below `p`: `acc_max < p` (`.leftSpan`) and `2 (digit − 1) + 1 < p`
(`.rightSpan`, `.cap`); the established bound is admissible against `n_high` and at most `digitMax`.
The integer equality follows (`MAC.OneDigitBounds.eq_of_modEq`). -/
structure MAC.OneDigitBounds (m : MAC) (p digit digitMax : Nat) : Prop where
  accMax_eq : m.accMax = m.nch * m.convMax + 1
  high_eq : m.nHigh = m.accMax / 2 + 1
  accMax_lt : m.accMax < p
  digit_lt : 2 * (digit - 1) + 1 < p
  digit_ge : m.nHigh ≤ digit
  digit_le : digit ≤ digitMax

theorem MAC.oneDigitBounds_iff (m : MAC) (p digit digitMax : Nat) :
    m.OneDigitBounds p digit digitMax ↔
      m.accMax = m.nch * m.convMax + 1 ∧ m.nHigh = m.accMax / 2 + 1 ∧ m.accMax < p ∧
        2 * (digit - 1) + 1 < p ∧ m.nHigh ≤ digit ∧ digit ≤ digitMax :=
  ⟨fun h => ⟨h.accMax_eq, h.high_eq, h.accMax_lt, h.digit_lt, h.digit_ge, h.digit_le⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

instance (m : MAC) (p digit digitMax : Nat) : Decidable (m.OneDigitBounds p digit digitMax) :=
  decidable_of_iff _ (m.oneDigitBounds_iff p digit digitMax).symm

/-- **The one-digit lowering is an integer equality**: under `MAC.OneDigitBounds`, an accumulator
`acc ≤ acc_max`, a bit `t ≤ 1` and a quotient digit `q < digit` whose field equation
`acc ≡ t + 2 q` holds modulo `p` satisfy it over the naturals: both sides lie below `p`. -/
theorem MAC.OneDigitBounds.eq_of_modEq {m : MAC} {p digit digitMax : Nat}
    (h : m.OneDigitBounds p digit digitMax) {acc t q : Nat} (hacc : acc ≤ m.accMax)
    (ht : t ≤ 1) (hq : q < digit) (heq : acc % p = (t + 2 * q) % p) :
    acc = t + 2 * q := by
  have h1 : acc < p := lt_of_le_of_lt hacc h.accMax_lt
  have h2 : t + 2 * q < p := by have := h.digit_lt; omega
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at heq

/-- **A single-group MAC record with one derived quotient digit is valid**: the request `<name>.q`
exists and the record satisfies `MAC.OneDigitBounds` at the characteristic floor of its
accumulator domain with its established bound and maximum. -/
def MAC.OneDigitValid (P : Plan) (m : MAC) : Prop :=
  match P.request (m.name ++ ".q") with
  | none => False
  | some d => m.OneDigitBounds (P.floorOf m.accDomain) d.realization.bound d.max

instance (P : Plan) (m : MAC) : Decidable (m.OneDigitValid P) := by
  unfold MAC.OneDigitValid
  split <;> infer_instance

/-- **A MAC record has a lowering whose plan conditions hold**: the single-group form with two
quotient digits (`MAC.SingleValid`), the single-group form with one derived quotient digit (the
C++'s one-digit quotient when `Qmax + 1` fits a table; `MAC.OneDigitValid`), or the grouped form
with at least three groups and one derived final digit (the C++'s one-digit final quotient,
`Qmax = ⌊(groups + 1) / 2⌋ ≥ 2`; `MAC.GroupedValid`). -/
def MAC.Lowerable (P : Plan) (m : MAC) : Prop :=
  (m.groups = 1 ∧ m.tail = .digits ∧ m.tailDigits = 2 ∧ m.SingleValid P) ∨
    (m.groups = 1 ∧ m.tail = .oneDigit ∧ m.OneDigitValid P) ∨
    (2 < m.groups ∧ m.tail = .oneDigit ∧ m.GroupedValid P)

instance (P : Plan) (m : MAC) : Decidable (m.Lowerable P) := by
  unfold MAC.Lowerable
  infer_instance

/-- **The quotient's lower end** `qlo = ⌈lo / m⌉` of a modular equality. -/
def ModEquality.qlo (e : ModEquality) : Int := -((-e.intervalLo) / (e.modulus : Int))

/-- **The quotient's span** `Qmax = ⌊hi / m⌋ - qlo`. -/
def ModEquality.qmax (e : ModEquality) : Nat := (e.intervalHi / (e.modulus : Int) - e.qlo).toNat

/-- **The no-wrap conditions** of a modular equality at the characteristic `p` for a quotient below
`Q`: `hi - m qlo < p` and `m (Q - 1) + (m qlo - lo) < p`. -/
structure ModEquality.NoWrapAt (e : ModEquality) (p Q : Nat) : Prop where
  left : e.intervalHi - e.modulus * e.qlo < p
  right : ((e.modulus * (Q - 1) : Nat) : Int) + (e.modulus * e.qlo - e.intervalLo) < p

instance (e : ModEquality) (p Q : Nat) : Decidable (e.NoWrapAt p Q) :=
  decidable_of_iff (e.intervalHi - e.modulus * e.qlo < p ∧
      ((e.modulus * (Q - 1) : Nat) : Int) + (e.modulus * e.qlo - e.intervalLo) < p)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.left, h.right⟩⟩

/-- **The bound of a weighted sum of limbs** in radix `R`, limb `j` below `N[j]`:
`Σ_j R^j (N[j] - 1) + 1`. -/
def limbsBoundList (R : Nat) (N : List Nat) : Nat :=
  ((N.zipIdx.map fun (n, j) => R ^ j * (n - 1)).sum) + 1

/-- **The decimal digits of `n`**, most significant first, with `fuel` steps (`decimal` takes
`n + 1`, enough for every `n`). -/
def decimalDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    (if n < 10 then [] else decimalDigits fuel (n / 10)) ++ [Char.ofNat (48 + n % 10)]

/-- **The decimal numeral of `n`** (the digits of `Nat.repr n`, written with definitions the kernel
reduces in a module, where `Nat.repr` does not). -/
def decimal (n : Nat) : String := String.ofList (decimalDigits (n + 1) n)

/-- **The range requests of a modular equality's quotient digits**, by the C++ names
(`compiler/mod.h`, `quotient`, `digits`, `committed_digits`): one derived digit `<name>.q`; two
digits `<name>.low`, `<name>.high`; `k ≥ 3` derived digits `<name>.d0`, …, `<name>.d(k-2)`,
`<name>.high`; one committed digit `<name>.q` (`committed_digits`, the committed-quotient form);
`k ≥ 2` committed digits `<name>.d0`, …, `<name>.d(k-1)`. -/
def ModEquality.digitRequests (e : ModEquality) : List String :=
  if e.topDerived then
    if e.digits = 1 then [e.name ++ ".q"]
    else if e.digits = 2 then [e.name ++ ".low", e.name ++ ".high"]
    else ((List.range (e.digits - 1)).map fun j => e.name ++ ".d" ++ decimal j) ++
      [e.name ++ ".high"]
  else if e.digits = 1 then [e.name ++ ".q"]
  else (List.range e.digits).map fun j => e.name ++ ".d" ++ decimal j

/-- **A modular equality's form is valid** at the characteristic `p`, with the established bounds
`N` of its digit requests (`none`: a request is missing): the field equality has `m = p`; the
constant and Bit quotients have `Qmax` `0` and `1`, `m` positive and not a multiple of `p`, and no
wrap at `1` and `2`; the digit forms have `m` positive, `m · B^(k-1)` not a multiple of `p`, a
positive base, no wrap at `limbsBoundList B N`, and in the committed form `Qmax < B^k`. -/
def ModEquality.FormValid (p : Nat) (N : Option (List Nat)) (e : ModEquality) : Prop :=
  match e.quotient with
  | .fieldEquality => e.modulus = p
  | .constant => 0 < e.modulus ∧ ¬ p ∣ e.modulus ∧ e.qmax = 0 ∧ e.NoWrapAt p 1
  | .bit => 0 < e.modulus ∧ ¬ p ∣ e.modulus ∧ e.qmax = 1 ∧ e.NoWrapAt p 2
  | .digits =>
    match N with
    | some N => 0 < e.modulus ∧ ¬ p ∣ e.modulus * e.base ^ (e.digits - 1) ∧ 0 < e.base ∧
        e.NoWrapAt p (limbsBoundList e.base N) ∧ (e.topDerived = false → e.qmax < e.base ^ e.digits)
    | none => False

instance (p : Nat) (N : Option (List Nat)) (e : ModEquality) : Decidable (e.FormValid p N) := by
  unfold ModEquality.FormValid
  split
  · infer_instance
  · infer_instance
  · infer_instance
  · split <;> infer_instance

/-- **A modular equality is lowered**: it is a MAC's tail, which the MAC's lowering realizes
(`Plan.NoWrapHolds.macs`), or its form is valid at the characteristic of its domain with the
established bounds of its digit requests. -/
def ModEquality.Lowered (P : Plan) (e : ModEquality) : Prop :=
  e.name ∈ P.macs.map (·.name) ∨
    e.FormValid (P.charOf e.domain) (e.digitRequests.mapM P.bound?)

instance (P : Plan) (e : ModEquality) : Decidable (e.Lowered P) := by
  unfold ModEquality.Lowered
  infer_instance

/-- **A filtered permutation's windows do not wrap** (`end - first + L ≤ ord(α)` at
`ord(α) = 2^bits - 1`): in the exported fields `last - first + 2 · len ≤ 2^bits - 1`
(`last = end - len`); and the offset field is a declared subfield of the domain of degree `bits`
(the position generator's field). -/
structure FilteredPermutation.NoWrapIn (d : Domain) (f : FilteredPermutation) : Prop where
  /-- The windows do not wrap. -/
  windows : ∀ w ∈ f.windows, w.last - w.first + 2 * w.len ≤ 2 ^ f.positionBits - 1
  /-- The offset field is a declared subfield of degree `bits`. -/
  offsetField : ∃ s ∈ d.subfields, s.name = f.offsetField ∧ s.degree = f.positionBits

theorem FilteredPermutation.noWrapIn_iff (d : Domain) (f : FilteredPermutation) :
    f.NoWrapIn d ↔
      (∀ w ∈ f.windows, w.last - w.first + 2 * w.len ≤ 2 ^ f.positionBits - 1) ∧
        ∃ s ∈ d.subfields, s.name = f.offsetField ∧ s.degree = f.positionBits :=
  ⟨fun h => ⟨h.windows, h.offsetField⟩, fun h => ⟨h.1, h.2⟩⟩

instance (d : Domain) (f : FilteredPermutation) : Decidable (f.NoWrapIn d) :=
  decidable_of_iff _ (f.noWrapIn_iff d).symm

/-- **The no-wrap conditions hold**: every `certify` condition holds (the C++ certificates the
lowerings' parameter conditions follow from: the modular equalities' no-wrap conditions from
`.leftSpan`, `.rightSpan`, `.cap`, `.digits`; the range groups' bound by the characteristic from
`.counts`); every request's established bound is admissible (`Request.Admits`); every MAC record has
a lowering whose conditions hold (`MAC.Lowerable`); every modular equality is lowered
(`ModEquality.Lowered`); and every filtered permutation's windows do not wrap in its domain
(`FilteredPermutation.NoWrapIn`). -/
structure Plan.NoWrapHolds (P : Plan) : Prop where
  /-- Every `certify` condition holds. -/
  certified : ∀ g ∈ P.gadgets, g.kind = "certify" → g.CertifyHolds
  /-- Every established bound is admissible. -/
  admits : ∀ r ∈ P.requests, r.Admits
  /-- Every MAC record is lowerable. -/
  macs : ∀ m ∈ P.macs, m.Lowerable P
  /-- Every modular equality is lowered. -/
  modEqualities : ∀ e ∈ P.modEqualities, e.Lowered P
  /-- Every filtered permutation's windows do not wrap. -/
  windows : ∀ f ∈ P.filteredPermutations, ∃ d ∈ P.domains, d.name = f.domain ∧ f.NoWrapIn d

theorem Plan.noWrapHolds_iff (P : Plan) : P.NoWrapHolds ↔
    (∀ g ∈ P.gadgets, g.kind = "certify" → g.CertifyHolds) ∧ (∀ r ∈ P.requests, r.Admits) ∧
      (∀ m ∈ P.macs, m.Lowerable P) ∧ (∀ e ∈ P.modEqualities, e.Lowered P) ∧
      ∀ f ∈ P.filteredPermutations, ∃ d ∈ P.domains, d.name = f.domain ∧ f.NoWrapIn d :=
  ⟨fun h => ⟨h.certified, h.admits, h.macs, h.modEqualities, h.windows⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

instance (P : Plan) : Decidable P.NoWrapHolds := decidable_of_iff _ P.noWrapHolds_iff.symm

/-! ## The Ligero tableaus -/

/-- **A tableau's numbers are valid** at the evaluation-point domain of size `q` and the relative
degree `D` (the field's degree over the masking subfield): the exported `k` and `N` are the C++'s
`k = (block_enc + 1) / (2 + rate)` and `N = block_enc - (2k - 1)` (`ligero_param.h:275, 303`),
the layout facts of the packing tree's layout `Ligero.MaskRow.TreeLayout.Valid` hold (at most
`r` queries for the blinding width `r`, so `t ≤ k − ℓ` for the `ℓ = k − r` entries per row, and
`ℓ ≥ 1`), with the mask test `2t ≤ k` (`Ligero.MaskTest.hidingOf`'s `t_le_half`), and the tableau
fits the transcript's size bounds (`k ≤ 2^12`, `D ≤ 2^10`, rows `≤ 2^20`). The tree size `N`
has no fixed bound: the zero-knowledge games take the configuration's own proof bound
(`Configuration.proofBound`).

No condition bounds the subfield masks by the row width: the compiler commits a domain's
subfield masks, the prefix cells of every subfield-masks edge of its tree, in `⌈np / w⌉` whole
prefix rows (`lib/gordiehowe/compiler/tree_zk.h`, `prefix_padded`; the prefix-row test
`PrefixSubfieldTest`, `compiler/packing.h`), which the tree layout models (`TreeLayout.prefixRows`).
The one-row bound `D² ≤ k − t` belongs to the one-level relative layout
(`Ligero.Relative.Shape.Valid.masks_le`), whose instances check it themselves. -/
structure Ligero.Valid (l : Ligero) (q D : Nat) : Prop where
  k_eq : l.k = (l.blockEnc + 1) / (2 + l.rate)
  N_eq : l.N = l.blockEnc - (2 * l.k - 1)
  enc_le_domain : l.blockEnc ≤ q
  t_pos : 0 < l.t
  t_le_r : l.t ≤ l.r
  r_lt_k : l.r < l.k
  split_cover : l.masking = .split → 2 * l.t ≤ l.k
  D_pos : 0 < D
  rate_lt : 2 * l.k < l.N
  t_le_N : l.t ≤ l.N
  k_le : l.k ≤ 2 ^ 12
  D_le : D ≤ 2 ^ 10
  rows_le : l.nrow ≤ 2 ^ 20
  ldtReps_pos : 0 < l.ldtReps

theorem Ligero.valid_iff (l : Ligero) (q D : Nat) : l.Valid q D ↔
    l.k = (l.blockEnc + 1) / (2 + l.rate) ∧ l.N = l.blockEnc - (2 * l.k - 1) ∧
      l.blockEnc ≤ q ∧ 0 < l.t ∧ l.t ≤ l.r ∧ l.r < l.k ∧ (l.masking = .split → 2 * l.t ≤ l.k) ∧
      0 < D ∧ 2 * l.k < l.N ∧ l.t ≤ l.N ∧ l.k ≤ 2 ^ 12 ∧ D ≤ 2 ^ 10 ∧
      l.nrow ≤ 2 ^ 20 ∧ 0 < l.ldtReps :=
  ⟨fun h => ⟨h.k_eq, h.N_eq, h.enc_le_domain, h.t_pos, h.t_le_r, h.r_lt_k, h.split_cover,
      h.D_pos, h.rate_lt, h.t_le_N, h.k_le, h.D_le, h.rows_le, h.ldtReps_pos⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩⟩

instance (l : Ligero) (q D : Nat) : Decidable (l.Valid q D) :=
  decidable_of_iff _ (l.valid_iff q D).symm

/-- **A domain's tableau is valid** at its registry entry's point domain and its relative degree
`[field : masking subfield]`. -/
def Domain.LigeroValid (d : Domain) : Prop :=
  match d.entry? with
  | some e => d.ligero.Valid e.points (d.field.degree / d.maskingDegree)
  | none => False

instance (d : Domain) : Decidable d.LigeroValid := by
  unfold Domain.LigeroValid
  split <;> infer_instance

/-- **Every domain's Ligero tableau is valid** (`Ligero.Valid`): the conditions of
`Ligero.MaskRow.TreeLayout.Valid` and `Ligero.MaskTest.hidingOf`, and the transcript's size bounds. The
line certificate and the column bound at the profile's target read numbers the plan does not export
(see the module docstring). -/
def Plan.LigeroShapesValid (P : Plan) : Prop := ∀ d ∈ P.domains, d.LigeroValid

instance (P : Plan) : Decidable P.LigeroShapesValid :=
  inferInstanceAs (Decidable (∀ d ∈ P.domains, _))

/-! ## The transcript -/

/-- **The digest bytes of a protocol hash** (`SPBCS.ProofSystemTranscript.k`): `32` for SHA-256, `48` for
SHA-384; `none` for any other name. -/
def hashBytes (name : String) : Option Nat :=
  if name = "SHA-256" then some 32 else if name = "SHA-384" then some 48 else none

/-- **A domain's streams fit at `k`-byte digests**: its extended Fiat–Shamir points follow the
C++ rule at the default budget `k + fsExtraBytes` and its registry entry's element bytes
(`Domain.FollowsStreamRule`; `SPBCS.ProofSystemTranscript.stream`, `StreamRows.grants`), and those bytes
are at most `35`. -/
def Domain.StreamsFit (k : Nat) (d : Domain) : Prop :=
  match d.entry? with
  | some e => d.FollowsStreamRule (k + SPBCS.Configurations.fsExtraBytes) e.bytes ∧ e.bytes ≤ 35
  | none => False

instance (k : Nat) (d : Domain) : Decidable (d.StreamsFit k) := by
  unfold Domain.StreamsFit
  split <;> infer_instance

/-- **The transcript fits at `k`-byte digests**: the digest has at most `2^10` bytes
(`SPBCS.ProofSystemTranscript.Bounds.k_le`); every domain's streams fit (`Domain.StreamsFit`); there are at
most two circuits; at most `2^10` columns are opened; the late messages have at most `2^20` bytes. -/
structure Plan.TranscriptFitsAt (P : Plan) (k : Nat) : Prop where
  digest_le : k ≤ 2 ^ 10
  streams : ∀ d ∈ P.domains, d.StreamsFit k
  circuits_le : P.domains.length ≤ 2
  queries_le : (P.domains.map (·.ligero.t)).sum ≤ 2 ^ 10
  messages_le : (P.messages.map (·.bytes)).sum ≤ 2 ^ 20

theorem Plan.transcriptFitsAt_iff (P : Plan) (k : Nat) : P.TranscriptFitsAt k ↔
    k ≤ 2 ^ 10 ∧ (∀ d ∈ P.domains, d.StreamsFit k) ∧ P.domains.length ≤ 2 ∧
      (P.domains.map (·.ligero.t)).sum ≤ 2 ^ 10 ∧ (P.messages.map (·.bytes)).sum ≤ 2 ^ 20 :=
  ⟨fun h => ⟨h.digest_le, h.streams, h.circuits_le, h.queries_le, h.messages_le⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

instance (P : Plan) (k : Nat) : Decidable (P.TranscriptFitsAt k) :=
  decidable_of_iff _ (P.transcriptFitsAt_iff k).symm

/-- **The transcript fits** at the digest bytes of the plan's hash. -/
def Plan.TranscriptFits (P : Plan) : Prop :=
  match hashBytes P.hash with
  | some k => P.TranscriptFitsAt k
  | none => False

instance (P : Plan) : Decidable P.TranscriptFits := by
  unfold Plan.TranscriptFits
  split <;> infer_instance

/-! ## The message spaces -/

/-- **The nodes of a domain's tree**: the field and every edge's child and parent. -/
def Domain.treeNodes (d : Domain) : List String :=
  d.field.name :: d.packing.flatMap fun e => [e.child, e.parent]

/-- **The element bytes of node `name`** of a registry entry: the field's, or a subfield's; `0`
when the entry has no such node. -/
def FieldEntry.bytesOf (e : FieldEntry) (name : String) : Nat :=
  if name = e.spec.name then e.bytes
  else ((e.subfields.find? (·.spec.name = name)).map (·.bytes)).getD 0

/-- **The space a message's elements are written in**: its pad space when it is a subfield message,
else the field (`Field`) or the masking subfield (`Subfield`). -/
def Message.space (d : Domain) (m : Message) : String :=
  if m.subfieldMessage then m.padSpace
  else if m.maskingSpace = "Field" then d.field.name else d.maskingSubfield

/-- **A message's spaces are valid in domain `d`** with registry entry `e`: the masking space is
`Field` or `Subfield`; the pad space is the default (`""`) or a node of the tree (the pad's space,
`Export.Message.padSpace`); a subfield message has a pad space that is a node of the tree, other
than the field unless the field has degree `1` (a prime field is its own prime subfield; the
verifier refuses an encoding outside the pad space); and the message's bytes are its size times the
element bytes of its space (the codec's `Codec.FieldBytes`). -/
structure Message.SpaceIn (d : Domain) (e : FieldEntry) (m : Message) : Prop where
  maskingSpace : m.maskingSpace = "Field" ∨ m.maskingSpace = "Subfield"
  padSpace : m.padSpace = "" ∨ m.padSpace ∈ d.treeNodes
  subfield : m.subfieldMessage = true →
    m.padSpace ∈ d.treeNodes ∧ (m.padSpace ≠ d.field.name ∨ d.field.degree = 1)
  bytes_pos : 0 < e.bytesOf (m.space d)
  bytes_eq : m.bytes = m.size * e.bytesOf (m.space d)

theorem Message.spaceIn_iff (d : Domain) (e : FieldEntry) (m : Message) : m.SpaceIn d e ↔
    (m.maskingSpace = "Field" ∨ m.maskingSpace = "Subfield") ∧
      (m.padSpace = "" ∨ m.padSpace ∈ d.treeNodes) ∧
      (m.subfieldMessage = true →
        m.padSpace ∈ d.treeNodes ∧ (m.padSpace ≠ d.field.name ∨ d.field.degree = 1)) ∧
      0 < e.bytesOf (m.space d) ∧ m.bytes = m.size * e.bytesOf (m.space d) :=
  ⟨fun h => ⟨h.maskingSpace, h.padSpace, h.subfield, h.bytes_pos, h.bytes_eq⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

instance (d : Domain) (e : FieldEntry) (m : Message) : Decidable (m.SpaceIn d e) :=
  decidable_of_iff _ (m.spaceIn_iff d e).symm

/-- **A message's spaces are valid**: its domain exists, has a registry entry, and the message's
spaces are valid in it. -/
def Message.SpaceValid (P : Plan) (m : Message) : Prop :=
  match P.domain m.domain with
  | some d =>
    match d.entry? with
    | some e => m.SpaceIn d e
    | none => False
  | none => False

instance (P : Plan) (m : Message) : Decidable (m.SpaceValid P) := by
  unfold Message.SpaceValid
  split
  · split <;> infer_instance
  · infer_instance

/-- **Every late message's spaces are valid** (`Message.SpaceIn`). Consumed by the late values'
masking spaces (the pads drawn in the pad space) and the message codecs. -/
def Plan.MessageSpacesValid (P : Plan) : Prop := ∀ m ∈ P.messages, m.SpaceValid P

instance (P : Plan) : Decidable P.MessageSpacesValid :=
  inferInstanceAs (Decidable (∀ m ∈ P.messages, _))

/-! ## The plan -/

/-- **A plan is valid**: the conditions on the plan's data hold. The conditions on the program
(`RealizedProgram.ChallengeOrder`, `RealizedProgram.PadOrderValid`, `RealizedProgram.TypeSources`, `RealizedProgram.TargetsAdmit`)
are in `RealizedProgram.Valid`. -/
structure Plan.Valid (P : Plan) : Prop where
  /-- The packing trees are admissible. -/
  packing : P.PackingAdmissible
  /-- Every field decodes. -/
  fields : P.FieldsDecode
  /-- The lookups fit. -/
  lookups : P.LookupsFit
  /-- The no-wrap conditions hold. -/
  noWrap : P.NoWrapHolds
  /-- The Ligero tableaus are valid. -/
  ligero : P.LigeroShapesValid
  /-- The transcript fits. -/
  transcript : P.TranscriptFits
  /-- The message spaces are valid. -/
  messages : P.MessageSpacesValid

theorem Plan.valid_iff (P : Plan) : P.Valid ↔
    P.PackingAdmissible ∧ P.FieldsDecode ∧ P.LookupsFit ∧ P.NoWrapHolds ∧
      P.LigeroShapesValid ∧ P.TranscriptFits ∧ P.MessageSpacesValid :=
  ⟨fun h => ⟨h.packing, h.fields, h.lookups, h.noWrap, h.ligero, h.transcript, h.messages⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

instance (P : Plan) : Decidable P.Valid := decidable_of_iff _ P.valid_iff.symm

end GordieHowe.RealizedProgram.Export
