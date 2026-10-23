-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedReduction
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.FieldProof.MaskedRowReduction
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.FieldProof.UniformSim
public import GordieHowe.Headline
public import GordieHowe.ProofSystem.FieldProof.ClaimSupport

@[expose] public section

/-!
# The source GKR with its input claim on a level of logical coordinates

GordieHowe's GKR (`lib/gordiehowe/compiler/tree_zk.h`, header: "GKR (zk_common.h's layer rows, then
the input row, whose packed bits are an eq-structured part)") ends in the input row, which reads the
circuit inputs; some inputs are bits packed into words, so the input row is a claim on logical
coordinates, opened by the packing tree (`GordieHowe/ProofSystem/RingSwitching/PackingTree.lean`), not a row on the
committed cells.

`GordieHowe.GKR.LayeredCircuit.maskedReduction` is the masked source GKR (CHVY25 Figure 1) with its
input forms on the coordinates `Z` of a level `L` over the cells (`Level`): the finalization rows
of every layer and the claim-pad products stay rows on the cells (the pads are cells), and the
input row (`GKR.SourceInput.inputForm`, at the pads renamed into `Z` by `L.cell`) is the one claim.
Its soundness (`maskedReductionSound`) is the source GKR's reduction on the logical assignment `L.view x`;
its honest prover (`maskedReductionHonest`) is the source GKR prover on a logical assignment, accepted on
every cells whose logical assignment gives the same circuit input and whose pad cells hold the
pads. Its simulator is the uniform simulator, so the masked reduction is honest-verifier zero knowledge
with error `0` with respect to it (`hvzk`, paper `def:red-sec` (c)).
-/

namespace GordieHowe.GKR.LayeredCircuit

open IOP LayeredCircuit
open scoped NNReal

variable {F ι Z Pub : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] {d : ℕ}

/-- **The source GKR with its input claim on a level** (`tree_zk.h`, the GKR input row as a claim
on the logical coordinates): the rows on the cells are the finalization rows of every layer and
the claim-pad products, at the pads `pad`; the claim is the input row on `Z`, the input forms `I`
weighted by the claim coefficients minus the terminal claim with its masking pads (read through
`L.cell`). -/
def maskedReduction (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) (I : SourceInput.InputForms F Z Pub d)
    (pad : S.PadIdx → ι) (L : Level F ι Z) : FieldProof.MaskedReduction F ι Pub (ι → F) id Z 1 where
  n := (S.interaction nodes).n
  spec := (S.interaction nodes).spec
  Lin := Fin (S.tail.depth + 1)
  linear _ tr l :=
    (Transcript.finalExpr S.padLayout ((S.interaction nodes).transcript tr) pad l).form
  Q := Fin (S.tail.depth + 1)
  products := TranscriptRouting.products S.padLayout pad
  claims p tr _ := SourceInput.inputForm I (L.cell ∘ pad) (S.interaction nodes) p tr

/-- **The input claim reads what the input forms read and the cells.** -/
theorem readsOnly_maskedReduction [DecidableEq Z] (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F Z Pub d) (pad : S.PadIdx → ι) (L : Level F ι Z) {T : Z → Prop}
    (hI : ∀ p x, (I.form p x).ReadsOnly T) (hT : ∀ i, T (L.cell i)) :
    (maskedReduction S nodes I pad L).ReadsOnly fun _ => T := fun p tr _ =>
  SourceInput.readsOnly_inputForm I (L.cell ∘ pad) (S.interaction nodes) hI (fun _ => hT _) p tr

omit [Fintype ι] in
/-- **The simulated source GKR transcript is bijective** in the challenges and the sent values
(`GKR.HonestTranscript.valueFamily_bijective`). -/
theorem valueFamily_bijective (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι) :
    CausalTranscript.ValuesBijective (valueFamily S nodes I pad) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact HonestTranscript.valueFamily_bijective _

/-- The message types of the source GKR interaction are finite. -/
instance interaction_typeFintype (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    ∀ i, Fintype ((S.interaction nodes).spec.Type i) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact Schedule.spec_typeFintype (.layer Q tail)

/-- The message types of the source GKR interaction are nonempty. -/
instance interaction_typeNonempty (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    ∀ i, Nonempty ((S.interaction nodes).spec.Type i) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact Schedule.spec_typeNonempty (.layer Q tail)

variable (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) (I : SourceInput.InputForms F Z Pub d)
  (pad : S.PadIdx → ι) (L : Level F ι Z)

omit [Fintype F] [DecidableEq F] in
/-- **The finalization rows hold exactly when the pad equations do** (`PadOK` on the pad
values). -/
theorem rowsHold_finals_iff {PadIdx : Type} {Ld : ℕ} (layout : Transcript.Layout PadIdx Ld)
    (tr : GKR.Transcript F PadIdx Ld layout) (coord : PadIdx → ι) (x : ι → F) :
    RowsHold (fun l => (Transcript.finalExpr layout tr coord l).form)
        (TranscriptRouting.products layout coord) x ↔
      Transcript.PadOK layout tr (x ∘ coord) := by
  rw [rowsHold_iff_sourceSystem (poly := TranscriptRouting.finals layout tr coord)
    (fun l => Transcript.Affine.toMvPolynomial_form _) _
    (TranscriptRouting.finals_degree layout tr coord)]
  exact TranscriptRouting.sourceSystem_holds_iff layout tr coord x

/-- **The output of the GKR masked reduction**: the pad equations on the pad cells and the input
equation on the logical assignment. -/
theorem maskedReduction_outHolds_iff (p : Pub)
    (tr : (S.interaction nodes).spec.Transcript (Fin.last (S.interaction nodes).n))
    (x : ι → F) :
    (maskedReduction S nodes I pad L).OutHolds L.view p tr x ↔
      Transcript.PadOK S.padLayout ((S.interaction nodes).transcript tr) (x ∘ pad) ∧
        ∑ y : Fin (2 ^ d), PackedClaim.claimCoeff ((S.interaction nodes).g0 tr)
            ((S.interaction nodes).g1 tr) ((S.interaction nodes).transcript tr).inputAlpha y *
            I.input p (L.view x) y =
          Transcript.value S.padLayout ((S.interaction nodes).transcript tr) (x ∘ pad) := by
  have hcomp : L.view x ∘ (L.cell ∘ pad) = x ∘ pad := funext fun j => L.view_cell x (pad j)
  have hclaim : (SourceInput.inputForm I (L.cell ∘ pad) (S.interaction nodes) p tr).eval
      (L.view x) = ∑ y : Fin (2 ^ d), PackedClaim.claimCoeff ((S.interaction nodes).g0 tr)
            ((S.interaction nodes).g1 tr) ((S.interaction nodes).transcript tr).inputAlpha y *
            I.input p (L.view x) y -
          Transcript.value S.padLayout ((S.interaction nodes).transcript tr) (x ∘ pad) := by
    rw [← AffineForm.eval_toMvPolynomial, SourceInput.toMvPolynomial_inputForm,
      SourceInput.inputPolynomial_eval, hcomp]
  constructor
  · intro h
    refine ⟨(rowsHold_finals_iff _ _ pad x).mp h.rows, ?_⟩
    have hc := h.claims 0
    change (SourceInput.inputForm I (L.cell ∘ pad) (S.interaction nodes) p tr).eval
      (L.view x) = 0 at hc
    rw [hclaim] at hc
    exact sub_eq_zero.mp hc
  · rintro ⟨hpad, hin⟩
    refine ⟨(rowsHold_finals_iff _ _ pad x).mpr hpad, fun _ => ?_⟩
    change (SourceInput.inputForm I (L.cell ∘ pad) (S.interaction nodes) p tr).eval
      (L.view x) = 0
    rw [hclaim, hin, sub_self]

/-- **Soundness of the GKR masked reduction**: the source GKR's reduction from satisfaction of the source
circuit on the input of the logical assignment, with the source GKR's errors. -/
noncomputable def maskedSound :
    (maskedReduction S nodes I pad L).Sound L.view (fun p x => S.Satisfied (I.input p (L.view x)))
      (S.error nodes) where
  reduction := (S.sound nodes (fun p x => I.input p (L.view x)) (fun x => x ∘ pad)
    (fun p x => S.Satisfied (I.input p (L.view x))) fun _ _ h => h).reduction.comap
      fun c : FieldProof.MaskedRowReduction.Instance Pub (ι → F) => (c.pub, c.wit)
  claim_iff p x := (S.sound nodes (fun p x => I.input p (L.view x)) (fun x => x ∘ pad)
    (fun p x => S.Satisfied (I.input p (L.view x))) fun _ _ h => h).claim_iff p x
  claimOut_iff p x tr := ((S.sound nodes (fun p x => I.input p (L.view x)) (fun x => x ∘ pad)
    (fun p x => S.Satisfied (I.input p (L.view x))) fun _ _ h => h).claimOut_iff p x tr).trans
      (maskedReduction_outHolds_iff S nodes I pad L p tr x).symm

/-- **The cells commit a logical assignment and the GKR pads**: the pad cells hold the pad values
of the free pads, and the logical assignment of the cells gives the same circuit input. -/
structure ClaimCommits (p : Pub) (z : Z → F) (π : PadTranslation.FreePads S.circuit) (x : ι → F) :
    Prop where
  /-- The pad cells hold the pads. -/
  pads : x ∘ pad = padValues S π
  /-- The logical assignment gives the circuit input of `z`. -/
  input : I.input p (L.view x) = I.input p z

/-- **The simulator of the GKR masked reduction**: the source GKR's (`valueFamily`) on free pads.

Running time: that of `GKR.LayeredCircuit.valueFamily`, linear in the GKR transcript.
This running time is argued here, not proved in Lean. -/
def maskedSim : (maskedReduction S nodes I pad L).Sim where
  SimCoins := PadTranslation.FreePads S.circuit
  sim _ ch v := (valueFamily S nodes I (L.cell ∘ pad) v).transcript ch

/-- **The honest GKR masked reduction**: the source GKR prover on a logical assignment `z` whose
circuit input satisfies the source circuit (`GKR.LayeredCircuit.family` at the pads renamed into
`Z`); it reads `z` only through the circuit input (`family_congr`). It is simulated by `maskedSim`,
with the law of the honest transcript (`family_identDistrib`). -/
def maskedHonest :
    (maskedReduction S nodes I pad L).Honest L.view (Z → F) (fun p z => S.Satisfied (I.input p z))
      (maskedSim S nodes I pad L) where
  Pads := PadTranslation.FreePads S.circuit
  prover p z π := family S nodes I (L.cell ∘ pad) p z π
  Commits p z π x := ClaimCommits S I pad L p z π x
  complete p z hz π x hx ch := by
    have hcomp : L.view x ∘ (L.cell ∘ pad) = padValues S π := by
      rw [← hx.pads]
      exact funext fun j => L.view_cell x (pad j)
    have h := claimOut S nodes I (L.cell ∘ pad) p (L.view x) π hcomp (hx.input ▸ hz) ch
    rw [family_congr S nodes I (L.cell ∘ pad) hx.input π] at h
    have h' := ((soundIP S nodes I (L.cell ∘ pad)).claimOut_iff p (L.view x) _).mp h
    have hc : L.view x ∘ (L.cell ∘ pad) = x ∘ pad := funext fun j => L.view_cell x (pad j)
    rw [hc] at h'
    exact (maskedReduction_outHolds_iff S nodes I pad L p _ x).mpr h'
  identDistrib p z ch := family_identDistrib S nodes I (L.cell ∘ pad) p z ch

/-- The message types of the GKR masked reduction are finite. -/
instance maskedReduction_typeFintype : ∀ i, Fintype ((maskedReduction S nodes I pad L).spec.Type i) :=
  interaction_typeFintype S nodes

/-- The message types of the GKR masked reduction are nonempty. -/
instance maskedReduction_typeNonempty : ∀ i, Nonempty ((maskedReduction S nodes I pad L).spec.Type i) :=
  interaction_typeNonempty S nodes

/-- The GKR masked reduction's simulator is a bijection onto the full transcripts. -/
theorem maskedReductionHonest_simBijective : (maskedHonest S nodes I pad L).SimBijective := fun _ =>
  valueFamily_bijective S nodes I (L.cell ∘ pad)

/-- **Paper `lem:gkr` (3)**: the GKR masked reduction is honest-verifier zero knowledge with error `0` with
respect to the uniform simulator (paper `def:red-sec` (c)): at every public input and every
logical assignment, the honest transcript under uniform challenges and uniform free pads is a
uniform full transcript. -/
@[headline]
theorem hvzk : (maskedHonest S nodes I pad L).UniformHVZK :=
  (maskedReductionHonest_simBijective S nodes I pad L).uniformHVZK

end GordieHowe.GKR.LayeredCircuit
