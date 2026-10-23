-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldClaimSupport

@[expose] public section

/-!
# GordieHowe: the circuit proof of any domain of a valid realized program

The circuit proof of domain `d` of a program (`GordieHowe.RealizedProgram.fieldProof`), one construction for every
domain of every program that passes the decidable checks (`GordieHowe.RealizedProgram.fieldOkB`), from the plan's
packing tree and Ligero numbers and the field's packing facts (`FieldInterp.Packing`):

* **the ready data** (`GordieHowe.RealizedProgram.FieldReady`): the field's packing facts, a Ligero certificate whose
  shape is the plan's, and the checks, decided per program (`fieldOkB`: the tree, the cells'
  nodes, the viewed words, every circuit's input layout, the covered batches, the Ligero numbers);
* **the tree domain** (`GordieHowe.RealizedProgram.fieldDomain`): the plan's tree (`fieldTree`, every
  edge's stage combining the claims that read its child, `claimReads`, with no combination when at
  most one does) on the tree layout with Ligero at the certified numbers (`TreeSpec.layoutDomain`),
  the masked reduction of the domain's batches, circuits and rows (`fieldMaskedReduction`);
* **the circuit proof** (`GordieHowe.RealizedProgram.fieldProof`): of the domain's predicate under the compiler trust
  (`Domain.guard`), the witness the committed cells, the domain's cells decoded from them
  (`treeDecode`); its soundness (`GordieHowe.RealizedProgram.fieldSound`);
* **the errors** (`GordieHowe.RingSwitching.TreeFieldProof.knowledgeError`, `GordieHowe.RingSwitching.TreeFieldProof.sum_commitError`): each covered batch's
  phase errors, each circuit's GKR error `numerator/|K|`, `1/|K|` per combination of the tree (at
  most one per edge, `combinations_fieldTreeOf_le`), and the tree layout's proof-phase error; the
  commit error the certified bound.
-/

namespace GordieHowe.RealizedProgram

open Export PEdge BatchedZerocheck IOP Ligero.MaskRow
open scoped NNReal

section

variable (ir : RealizedProgram) {I : Interp}

/-- **The packing edges of the plan's domain of `d`** (none when the plan has no such domain). -/
def planPacking (P : Export.Plan) (d : ℕ) : List PackingEdge :=
  ((P.domain (ir.domain d).name).map (·.packing)).getD []

/-- **The plan's Ligero numbers of `d` are the certificate's.** -/
def planLigeroB (P : Export.Plan) (d : ℕ) (c : LigeroCert) : Bool :=
  ((P.domain (ir.domain d).name).map fun pd => c.matchesB pd.ligero).getD false

variable (d : ℕ)

/-- **The realized edges of domain `d`**: the plan's edges with the field's kits. -/
abbrev fieldEdgesOf (P : Export.Plan) (Pk : (I (ir.domainField d)).Packing) :
    List (REdge (I (ir.domainField d)) Pk) :=
  realizedEdges Pk (ir.planPacking P d)

/-- **The checks of domain `d`** (see the module docstring), as a test. -/
def fieldOkB (P : Export.Plan) (Pk : (I (ir.domainField d)).Packing) (c : LigeroCert) : Bool :=
  (ir.fieldEdgesOf d P Pk).length == (ir.planPacking P d).length &&
    treeOkB ((ir.fieldEdgesOf d P Pk).map REdge.plan) Pk.n &&
    ir.placeOkB d Pk ((ir.fieldEdgesOf d P Pk).map REdge.plan) &&
    ir.viewsOkB d ((ir.fieldEdgesOf d P Pk).map REdge.plan) &&
    (ir.circs d).all (fun c => decide (ir.InputsT d c)) &&
    ir.batchesOkB d Pk && decide (ir.QuadsOk d) && c.validB Pk.q && ir.planLigeroB P d c

variable (I) in
/-- **The ready data of domain `d`** (see the module docstring). -/
structure FieldReady (P : Export.Plan) where
  /-- The field's packing facts. -/
  Pk : (I (ir.domainField d)).Packing
  /-- The Ligero certificate. -/
  cert : LigeroCert
  /-- The checks. -/
  ok : ir.fieldOkB d P Pk cert = true
  /-- The program is well formed (`RealizedProgram.WellFormed`, proved per program). -/
  wf : ir.WellFormed

variable {ir d} {P : Export.Plan}

namespace FieldReady

variable (R : ir.FieldReady I d P)

/-- The realized edges. -/
abbrev rs : List (REdge (I (ir.domainField d)) R.Pk) := ir.fieldEdgesOf d P R.Pk

theorem valid : R.cert.validB R.Pk.q = true := by
  have h := R.ok
  simp only [fieldOkB, Bool.and_eq_true] at h
  exact h.1.2

theorem claimOk : ir.ClaimOk R.rs := by
  have h := R.ok
  simp only [fieldOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, ht⟩, hp⟩, hv⟩, hc⟩, hb⟩, hq⟩, -⟩, -⟩ := h
  exact ⟨TreeOk.of_treeOkB ht, PlaceOk.of_placeOkB ir hp, ir.realizedOk_realizedEdges _,
    ViewsOk.of_viewsOkB ir d hv, hc, BatchesOk.of_batchesOkB hb, hq, R.wf⟩

/-- **The tree layout's Ligero numbers** at the certificate and the field's points. -/
abbrev numbers : TreeLayout.Numbers (I (ir.domainField d)).K R.Pk.S0 :=
  R.Pk.numbers R.cert R.valid

end FieldReady

variable (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)

/-- **The packing tree of domain `d`** at the masked reduction's claims and the nodes they read
(`claimReads`). -/
abbrev fieldTreeOf :=
  ir.fieldTree d R.rs (ir.ClaimPads d src R.Pk) (ir.claimCount (d := d) (Pk := R.Pk))
    (claimReads R.rs) R.claimOk.tree

/-- **The tree domain of domain `d`** (`TreeSpec.layoutDomain`). -/
def fieldDomain :
    RingSwitching.TreeFieldProof (I (ir.domainField d)).K R.Pk.p (ir.FCell src R.Pk R.rs) (ir.FLog src R.Pk R.rs)
      (ir.DomainPub I) (ir.claimCount (d := d) (Pk := R.Pk)) :=
  (ir.fieldTreeOf src R).layoutDomain R.numbers (ir.fieldMaskedReduction src R.rs)
    (routes_path _ 0 _ _ _ _ (readsOnly_fieldMaskedReduction src R.rs))

variable (ir I) in
/-- **What domain `d`'s proof proves** on the committed cells `x`: given the compiler trust, the
domain's predicate on the decoded cells. -/
abbrev FieldHolds (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) {d : ℕ}
    {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge (I (ir.domainField d)) Pk))
    (p : ir.DomainPub I) (x : ir.FCell src Pk rs → (I (ir.domainField d)).K) : Prop :=
  ir.CircuitsEnforce I src →
    (ir.domainOf I d).Holds p.stmt (ir.treeDecode d rs (ir.ClaimPads d src Pk) x) p.run

/-- **The relation of domain `d`'s tree domain**: the masked reduction's relation (`FieldSat`) on the
committed cells, which are the witness; it gives the domain's predicate on the decoded cells under
the compiler trust (`holds_of_fieldSat`).

Running time of the readout: it returns the committed cells unchanged.
This running time is argued here, not proved in Lean. -/
def fieldRelation : (ir.fieldDomain src R).Relation (ir.FieldHolds I src R.rs) where
  sat := ir.FieldSat src R.rs
  readout x := x
  readout_sound p x _ h T := ir.holds_of_fieldSat src R.rs R.claimOk T p x h

/-- **The circuit proof of domain `d` under the compiler trust** (see the module docstring). -/
def fieldProof :
    DomainProof (ir.layout I) (ir.Valuation I) ((ir.domainOf I d).guard (ir.CircuitsEnforce I src)) where
  Pub := ir.DomainPub I
  Wit := ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K
  holds := ir.FieldHolds I src R.rs
  proof := (ir.fieldDomain src R).proof (ir.fieldRelation src R)
  pub x r := ⟨x, r⟩
  decode := ir.treeDecode d R.rs (ir.ClaimPads d src R.Pk)
  enforce _ _ _ h := GordieHowe.Domain.holds_guard_iff.2 h

/-- **The masked reduction's soundness at the tree's level** (`fieldClaimSound`, the level independent of
the claims, `path_level_eq`). -/
noncomputable def fieldClaimSoundAt :
    (ir.fieldMaskedReduction src R.rs).Sound (ir.fieldDomain src R).path.level.view
      (ir.fieldRelation src R).sat (ir.fieldClaimError src R.rs) :=
  (congrArg Level.view (path_level_eq (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.claimCount (d := d) (Pk := R.Pk)) Fin.elim0 (claimReads R.rs))) ▸
      ir.fieldClaimSound src R.rs

/-- **The soundness of domain `d`'s circuit proof** (`RingSwitching.TreeFieldProof.sound`). -/
noncomputable def fieldSound : (ir.fieldProof src R).proof.Sound :=
  (ir.fieldDomain src R).sound (ir.fieldRelation src R) (ir.fieldClaimSoundAt src R)

/-- **The plan's tree combines at most once per edge.** -/
theorem combinations_fieldTreeOf_le : (ir.fieldTreeOf src R).path.combinations ≤ R.rs.length := by
  change (PEdge.path _ 0 (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) _ _).combinations ≤ _
  have h := combinations_path_le (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) _ (claimReads R.rs)
  rwa [length_fieldEdges] at h

/-- **Every round charge of domain `d`'s proof is at most `δ`**: the commit bound, the covered
batches' phase errors together (`batchesError`), a GKR round's charge `max 3 (2 · gkrWidth)/|K|` (`gkrRoundError`),
the combinations' `|rs|/|K|`, the test bound, and the column bound with, when the prefix is
nonempty, the joint subfield term `(k − 1)_t/(N)_t`. Each round of the forked proof is charged
one of them (`ProofSystem.fieldForkError_le`). -/
structure FieldRoundsLe (δ : ℝ≥0) : Prop where
  /-- The commit round. -/
  commit : R.numbers.bounds.commit ≤ δ
  /-- The covered batches' phase errors together. -/
  batches : ir.batchesError d R.Pk ≤ δ
  /-- A GKR round, each challenge charged alone. -/
  gkr : ir.gkrRoundError I d ≤ δ
  /-- The combinations, `1/|K|` each. -/
  combinations : (R.rs.length : ℝ≥0) / Fintype.card (I (ir.domainField d)).K ≤ δ
  /-- Ligero's constraint challenge. -/
  test : R.numbers.bounds.test ≤ δ
  /-- Ligero's column query with the joint subfield term. -/
  column : R.numbers.bounds.column +
    (if npOf R.Pk R.rs = 0 then 0 else
      Ligero.SubfieldTest.jointSubfieldError R.numbers.Sh.block R.numbers.Sh.N R.numbers.Sh.nreq) ≤ δ

end

end GordieHowe.RealizedProgram
