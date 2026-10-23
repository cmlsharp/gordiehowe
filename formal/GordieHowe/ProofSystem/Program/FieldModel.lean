-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.CellsLowering
public import GordieHowe.Language.Realizations.MaskSubfield

@[expose] public section

/-!
# GordieHowe: the model of a program's fields

The proof system (`GordieHowe.RealizedProgram.ProofSystem`) reads facts about the interpretation of a program (`Interp`): the
registry, lawful integer readings, the MAC fields, linear readings, additive bit coordinates and
`{0, 1}` bit nodes. Each is a property of a field's representation in Lean together with a
decidable fact about the program. This module separates the two:

* **the model of a field** (`FieldInterp.Model F primes bits`), proved once per field next to the
  field's definition: its registry entry, characteristic and cardinality, its integer readings, the
  cast of the integer reading at its prime-subfield nodes `primes`, its bit nodes `bits` read as
  `{0, 1}`, additive bit coordinates. An odd field read through a coordinate onto its prime field
  has the model at `GF(p^1)` (`FieldInterp.model_of_primeCoord`);
* **the field models of an interpretation** (`Interp.Models I primes bits`): every field identifier
  has its field's model, read off the interpretation's shape (`Interp.models_const`,
  `mldsaInterpOf_models`, `falconInterpOf_models`);
* **the program's checks**, decided: the interpretation's names and characteristics are the
  program's (`Interp.SpecsMatch`), every prime-subfield node of a domain is one of its field's
  (`GordieHowe.RealizedProgram.NodesIn`), every node-typed `Bit` value is at one of its field's bit nodes
  (`GordieHowe.RealizedProgram.BitNodesIn`), and the opaque `Bit` values return bits (`Interp.OpaqueBit`);
* **the interpretation facts from the models**: `Interp.registered_of_models`,
  `Interp.lawful_of_models`, `Interp.bitNodes_of_models`, `Interp.bitsAdditive_of_models`; the MAC
  model (`Interp.macModel_of_tails`, at a field's `FieldInterp.MacFieldOk`) and the field-form
  model (`Interp.fieldFormModel_of_field`, at a field's `FieldInterp.ReadLinear`) are per field;
* **the model of a program's interpretation** (`Interp.Model I P ir orng`), the bundle the proof system
  reads, from the models and the checks (`Interp.Model.of_models`).
-/

namespace GordieHowe.RealizedProgram

open Export RelativePacking

/-! ## The model of a field -/

/-- **The model of a field of the programs** at the prime-subfield nodes `primes` and the bit nodes
`bits` (a property of the field's representation in Lean): the specification is a registry entry's,
of the Lean field's characteristic and cardinality; the integer reading of an element is below the
characteristic in odd characteristic and inverts the cast of a natural below it; a constant below
the characteristic decodes to its cast; an element of a prime-subfield node is the cast of its
integer reading; the node of the field's own name is the whole field; a bit node is `{0, 1}`; the
bit coordinates are additive. -/
structure FieldInterp.Model (F : FieldInterp) (primes bits : List String) : Prop where
  /-- The specification is a registry entry's. -/
  entry : ∃ e ∈ fieldRegistry, e.spec = F.spec
  /-- The Lean field has the specification's characteristic. -/
  ringChar : _root_.ringChar F.K = F.spec.characteristic
  /-- The Lean field has the specification's cardinality. -/
  card : Fintype.card F.K = F.spec.characteristic ^ F.spec.degree
  /-- The integer reading is below the characteristic, in odd characteristic. -/
  toNat_lt : 2 < F.spec.characteristic → ∀ x : F.K, F.toNat x < F.spec.characteristic
  /-- The integer reading inverts the cast of a natural below the characteristic. -/
  toNat_natCast : ∀ k < F.spec.characteristic, F.toNat (k : F.K) = k
  /-- A constant below the characteristic decodes to its cast. -/
  decode_natCast : ∀ c < F.spec.characteristic, F.decode c = (c : F.K)
  /-- An element of a prime-subfield node is the cast of its integer reading. -/
  natCast_toNat : ∀ E ∈ primes, ∀ x ∈ F.node E, ((F.toNat x : ℕ) : F.K) = x
  /-- The node of the field's own name is the whole field (the root of its packing tree). -/
  rootNode : F.node F.spec.name = ⊤
  /-- A bit node is `{0, 1}`. -/
  bitNode : ∀ E ∈ bits, ∀ x ∈ F.node E, x = 0 ∨ x = 1
  /-- The bit coordinates are additive. -/
  bitsAdditive : F.BitsAdditive

/-- **An odd field read through a coordinate onto its prime field has the model at `GF(p^1)`**: the
field `K` of characteristic `p` with the registry specification `spec`, constants decoded as casts,
the integer reading the value of the coordinate `c` (which takes the cast of a natural to its cast
and inverts the prime field's `algebraMap`), the node `GF(p^1)` in the prime subfield, the node of
the field's own name the whole field, and no bit coordinates. -/
theorem FieldInterp.model_of_primeCoord {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] [CharP K p] [ExpChar K p] {spec : FieldSpec}
    {node : String → AddSubgroup K} {memDec : ∀ s, DecidablePred (· ∈ node s)} {c : K → ZMod p}
    (entry : ∃ e ∈ fieldRegistry, e.spec = spec) (hchar : spec.characteristic = p)
    (hcard : Fintype.card K = p ^ spec.degree) (hnat : ∀ n : ℕ, c n = n)
    (halg : ∀ z, c (algebraMap (ZMod p) K z) = z)
    (hnode : ∀ x ∈ node "GF(p^1)", x ∈ fixedField K p 1) (hroot : node spec.name = ⊤) :
    (FieldInterp.mk spec K (fun n => (n : K)) (fun x => (c x).val) node memDec
      fun _ _ _ => false).Model ["GF(p^1)"] [] where
  entry := entry
  ringChar := by
    change _root_.ringChar K = spec.characteristic
    rw [hchar]
    exact ringChar.eq K p
  card := by
    change Fintype.card K = spec.characteristic ^ spec.degree
    rw [hchar]
    exact hcard
  toNat_lt _ x := by
    change (c x).val < spec.characteristic
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    rw [hchar]
    exact ZMod.val_lt (c x)
  toNat_natCast k hk := by
    change (c (k : K)).val = k
    change k < spec.characteristic at hk
    rw [hchar] at hk
    rw [hnat, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  decode_natCast _ _ := rfl
  natCast_toNat E hE x hx := by
    rw [List.mem_singleton] at hE
    subst hE
    exact GordieHowe.natCast_val_eq_of_mem_fixedField halg (hnode x hx)
  rootNode := hroot
  bitNode _ hE := absurd hE List.not_mem_nil
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl

/-! ## The field models of an interpretation -/

/-- **The field models of an interpretation**: every field identifier `f` (an interpretation is
total) has its field's model at the prime-subfield nodes `primes f` and the bit nodes `bits f`. -/
def Interp.Models (I : Interp) (primes bits : ℕ → List String) : Prop :=
  ∀ f, (I f).Model (primes f) (bits f)

/-- **The field models of an interpretation by one field**: every identifier has `F`'s model. -/
theorem Interp.models_const {F : FieldInterp} {ops : String → List (ℕ → ℕ) → ℕ → ℕ}
    {primes bits : List String} (h : F.Model primes bits) :
    Interp.Models ⟨fun _ => F, ops⟩ (fun _ => primes) (fun _ => bits) :=
  fun _ => h

/-- **The node lists of a two-field interpretation**: `a` at field `0`, `b` at every other field
identifier (the shape of `mldsaInterpOf` and `falconInterpOf`). -/
def twoFieldNodes (a b : List String) : ℕ → List String
  | 0 => a
  | _ + 1 => b

/-! ## The program's checks -/

/-- **The interpretation's fields have the program's names and characteristics** (decided). -/
def Interp.SpecsMatch (I : Interp) (ir : RealizedProgram) : Prop :=
  ∀ f < ir.fields.length, (I f).spec.name = (ir.field f).name ∧
    (I f).spec.characteristic = (ir.field f).characteristic

instance (I : Interp) (ir : RealizedProgram) : Decidable (I.SpecsMatch ir) := by
  unfold Interp.SpecsMatch
  infer_instance

/-- **Every node `nodes d` of each domain `d` is a node `fieldNodes f` of its field `f`** (decided;
at the plan's prime-subfield nodes `primeNodesOf` and the fields' prime-subfield nodes). -/
def NodesIn (ir : RealizedProgram) (nodes fieldNodes : ℕ → List String) : Prop :=
  ∀ d < ir.domains.length, ∀ E ∈ nodes d, E ∈ fieldNodes (ir.domainField d)

instance (ir : RealizedProgram) (nodes fieldNodes : ℕ → List String) :
    Decidable (ir.NodesIn nodes fieldNodes) := by
  unfold RealizedProgram.NodesIn
  infer_instance

/-- **Every node-typed `Bit` value is at a bit node `bits f` of its field `f`** (decided). -/
def BitNodesIn (ir : RealizedProgram) (bits : ℕ → List String) : Prop :=
  ∀ v < ir.values.length, (ir.value v).type = .bit → (ir.value v).typeSource = .node →
    ((ir.value v).node.all fun nr => nr.name ∈ bits (ir.valueField v)) = true

instance (ir : RealizedProgram) (bits : ℕ → List String) : Decidable (ir.BitNodesIn bits) := by
  unfold RealizedProgram.BitNodesIn
  infer_instance

/-- **The opaque `Bit` values computed from arguments return `0` or `1`** (the program's part of
`Interp.Lawful.opaqueBit`). -/
def Interp.OpaqueBit (I : Interp) (ir : RealizedProgram) : Prop :=
  ∀ v < ir.values.length, ∀ name args, (ir.value v).kind = .pub (.opaque name args) →
    args ≠ [] → (ir.value v).type = .bit → ∀ xs i, I.opaqueFn name xs i < 2

/-- **Opaque functions returning bits return bits at every opaque `Bit` value** (`targetBitsFn`,
`targetBitsFn_lt_two`; the opaque functions `fun _ _ _ => 0` of the programs whose opaque values
take no arguments). -/
theorem Interp.opaqueBit_of_lt_two {I : Interp} {ir : RealizedProgram}
    (h : ∀ nm xs i, I.opaqueFn nm xs i < 2) : I.OpaqueBit ir :=
  fun _ _ nm _ _ _ _ xs i => h nm xs i

/-! ## The interpretation facts from the models -/

variable {I : Interp} {ir : RealizedProgram} {primes bits : ℕ → List String}

/-- **The interpretation follows the registry** when its fields have their models and the program's
names and characteristics. -/
theorem Interp.registered_of_models (hM : I.Models primes bits) (hs : I.SpecsMatch ir) :
    I.Registered ir where
  registry f _ := (hM f).entry
  name f hf := (hs f hf).1
  characteristic f hf := (hs f hf).2
  ringChar f _ := (hM f).ringChar
  card f _ := (hM f).card

/-- **The integer readings are lawful** at the nodes `primeNodes` when the fields have their models
and the program's characteristics, every node `primeNodes d` of a domain is a prime-subfield node of
its field, and the opaque `Bit` values return bits. -/
theorem Interp.lawful_of_models {primeNodes : ℕ → List String} (hM : I.Models primes bits)
    (hs : I.SpecsMatch ir) (hp : ir.NodesIn primeNodes primes) (hop : I.OpaqueBit ir) :
    I.Lawful ir primeNodes where
  toNat_lt f hf h2 x := by
    rw [← (hs f hf).2] at h2 ⊢
    exact (hM f).toNat_lt h2 x
  toNat_natCast f hf k hk := (hM f).toNat_natCast k ((hs f hf).2 ▸ hk)
  decode_natCast f hf c hc := (hM f).decode_natCast c ((hs f hf).2 ▸ hc)
  natCast_toNat d hd E hE x hx := (hM _).natCast_toNat E (hp d hd E hE) x hx
  rootNode f hf := (hs f hf).1 ▸ (hM f).rootNode
  opaqueBit := hop

/-- **The nodes of the node-typed `Bit` values are `{0, 1}`** when the fields have their models and
every such value is at a bit node of its field. -/
theorem Interp.bitNodes_of_models (hM : I.Models primes bits) (hb : ir.BitNodesIn bits) :
    I.BitNodes ir := by
  intro v hv hty hsrc nr hnr x hx
  have h := hb v hv hty hsrc
  rw [hnr] at h
  exact (hM _).bitNode nr.name (of_decide_eq_true h) x hx

/-- **The domains with batches on bits read additive bit coordinates** when the fields have their
models. -/
theorem Interp.bitsAdditive_of_models (hM : I.Models primes bits) : ir.BitsBatchAdditive I :=
  fun _ _ _ => (hM _).bitsAdditive

/-! ## The model of a program's interpretation -/

/-- **The model of the interpretation `I` of the program `ir` of the plan `P`**, with the opaque
ranges `orng` (a property of the interpretation): it follows the registry (`Interp.Registered`),
its integer readings are lawful at the plan's prime-subfield nodes (`Interp.Lawful`,
`primeNodesOf`), its MAC fields have polynomial bases (`Interp.MacModel`), the fields of the
field-form `mod_q`s read linearly (`Interp.FieldFormModel`), the domains with batches on bits read
additive bit coordinates (`RealizedProgram.BitsBatchAdditive`), the nodes of the node-typed `Bit` values are
`{0, 1}` (`Interp.BitNodes`), and the opaque functions have the ranges `orng`
(`RealizedProgram.OpaqueRanges`). -/
structure Interp.Model (I : Interp) (P : Plan) (ir : RealizedProgram) (orng : List (ℕ × ℕ)) : Prop where
  /-- The interpretation follows the registry. -/
  registered : I.Registered ir
  /-- The integer readings of the fields are lawful at the plan's prime-subfield nodes. -/
  lawful : I.Lawful ir (primeNodesOf P ir)
  /-- The MAC fields have polynomial bases and the MAC targets' bits are their arguments' bits. -/
  macModel : I.MacModel ir
  /-- The fields of the field-form `mod_q`s have linear integer readings. -/
  fieldForm : I.FieldFormModel ir
  /-- The fields of the domains with batches on bits have additive bit coordinates. -/
  bitsAdditive : ir.BitsBatchAdditive I
  /-- The nodes of the node-typed `Bit` values are `{0, 1}`. -/
  bitNodes : I.BitNodes ir
  /-- The opaque functions have the ranges `orng`. -/
  opaqueModel : ir.OpaqueRanges I orng

/-- **The model's fields decode `0` to `0`** (`Interp.zeroDecodes_of_lawful`). -/
theorem Interp.Model.zeroDecodes {orng : List (ℕ × ℕ)} {P : Plan} (hM : I.Model P ir orng) :
    ir.ZeroDecodes I :=
  Interp.zeroDecodes_of_lawful hM.registered hM.lawful

/-- **The model of a program's interpretation from its fields' models**, with no opaque ranges: the
fields' models (`hM`), the checks of the program (`hs`: names and characteristics; `hp`: the plan's
prime-subfield nodes; `hb`: the bit nodes; `hop`: the opaque `Bit` values), the MAC model and the
field-form model. -/
theorem Interp.Model.of_models {P : Plan} (hM : I.Models primes bits) (hs : I.SpecsMatch ir)
    (hp : ir.NodesIn (primeNodesOf P ir) primes) (hb : ir.BitNodesIn bits) (hop : I.OpaqueBit ir)
    (hmac : I.MacModel ir) (hff : I.FieldFormModel ir) : I.Model P ir [] where
  registered := Interp.registered_of_models hM hs
  lawful := Interp.lawful_of_models hM hs hp hop
  macModel := hmac
  fieldForm := hff
  bitsAdditive := Interp.bitsAdditive_of_models hM
  bitNodes := Interp.bitNodes_of_models hM hb
  opaqueModel := RealizedProgram.opaqueRanges_nil

end GordieHowe.RealizedProgram
