-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.ClaimReduction
public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Foundations.Algebra.AffineForm
public import Mathlib.Logic.Equiv.Finset

@[expose] public section

/-!
# Masked interactive proofs (commit-and-prove)

A **masked row reduction** is a public-coin algebraic interactive proof run inside Longfellow's
commit-and-prove construction: every prover message is sent masked by a one-time pad
committed in the Ligero witness before the first challenge, as a non-oracle message, and
the IP verifier's checks are deferred to Ligero as rows on the committed cells. The rows
have Ligero's two forms: affine rows that may depend on the public input and the
transcript (Ligero's linear test), each an `AffineForm` (a list of terms and a constant,
computed by the verifier), and product triples `x[a] · x[b] = x[c]` fixed before
commitment (Ligero's quadratic test). `rowsHold_iff` relates the rows to the quadratic
system `Ligero.Routing.sourceSystem`; instances whose row semantics is proved on polynomial
expressions use `rowsHold_iff_sourceSystem`. For GKR these are one linear row and one product
of two pads per layer, with the input row as a claim (`GordieHowe.GKR.LayeredCircuit.maskedReduction`, a masked reduction); for
the univariate-skip sumcheck of a field batch they are the terminal row, the
reveal rows, the opening row, the terminal-pad product and the mask chains
(`GordieHowe.BatchedZerocheck.AffineBatch.ip`, a masked reduction closed by `MaskedReduction.close`).

Origin. The form is Frigo–shelat's Protocol 2.5 (ePrint 2024/2010, p. 9: "P sends
`t′_i ← m_i + pad_i`", pads committed beforehand, verifier checks as Ligero constraints)
and CHVY25's "masked GKR transcript" (Figure 1 and Theorem 4.1: the masked prover
messages `T' = T + pad`, perfect ZK and RBR knowledge soundness). Both treat GKR only;
the interface here is the general form.

The interface states three obligations once. `MaskedRowReduction` itself is the computational part (the
protocol and the rows); the obligations that carry errors are separate, so that a concrete
instance's protocol, rows and simulator are computable definitions:
* **soundness** (`MaskedRowReduction.Sound`): a `ClaimReduction` from the IP's relation on the committed
  cells to the rows on the cells, with per-round error `ε` (its contribution to the RBR
  knowledge error), `claim_iff` and `claimOut_iff`;
* **completeness** (`MaskedRowReduction.Honest.complete`): the honest prover's transcript satisfies
  the rows on every committed witness that holds its input and pads;
* **HVZK of the masked transcript** (`MaskedRowReduction.Honest.identDistrib`): at fixed challenges, the
  honest transcript under uniform pads has the law of a named simulator that reads the
  public input and the challenges only. The commit-and-prove system hides the pads
  (`CommitProve.Honest.hides`), so this is the IP's whole contribution to the view
  (`GordieHowe.FieldProof.hvzk`).

Generic constructions: `MaskedRowReduction.append` (two masked row reductions on the same cells in sequence, rows side
by side) and `MaskedRowReduction.static` (fixed rows with no rounds).
-/

namespace GordieHowe
open IOP

open scoped NNReal
open MvPolynomial ProtocolSpec

/-! ### Deferred rows -/

variable {F ι : Type} [Field F] [Fintype ι]

/-- **The deferred rows hold** on the cells `x`: every affine row vanishes and every product
triple holds. These are what Ligero's linear and quadratic tests check. -/
structure RowsHold {Lin Q : Type} (linear : Lin → AffineForm F ι)
    (products : Ligero.Routing.ProductLayout ι Q) (x : ι → F) : Prop where
  linear : ∀ l, (linear l).eval x = 0
  products : Ligero.Routing.SourceProducts products x

/-- **The rows as a quadratic system**: the affine rows as polynomials of total degree at most
one (`AffineForm.toMvPolynomial`) and the product triples, the form Ligero's constraint test
consumes. -/
noncomputable def rowsSystem {Lin Q : Type} [Fintype Lin] [Fintype Q]
    (linear : Lin → AffineForm F ι) (products : Ligero.Routing.ProductLayout ι Q) :
    QuadraticSystem F ι :=
  Ligero.Routing.sourceSystem products (fun l => (linear l).toMvPolynomial)
    fun l => (linear l).totalDegree_toMvPolynomial_le

theorem rowsHold_iff {Lin Q : Type} [Fintype Lin] [Fintype Q] (linear : Lin → AffineForm F ι)
    (products : Ligero.Routing.ProductLayout ι Q) (x : ι → F) :
    RowsHold linear products x ↔ (rowsSystem linear products).Holds x := by
  rw [rowsSystem, Ligero.Routing.sourceSystem_holds_iff]
  simp only [AffineForm.eval_toMvPolynomial]
  exact ⟨fun h => ⟨h.linear, h.products⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Rows read through their polynomials**: affine forms whose polynomials are `poly` hold
exactly when the polynomials' source system holds. The instances whose row semantics is proved
on polynomial expressions carry their proofs over through this. -/
theorem rowsHold_iff_sourceSystem {Lin Q : Type} [Fintype Lin] [Fintype Q]
    {linear : Lin → AffineForm F ι} {poly : Lin → MvPolynomial ι F}
    (h : ∀ l, (linear l).toMvPolynomial = poly l) (products : Ligero.Routing.ProductLayout ι Q)
    (hpoly : ∀ l, (poly l).totalDegree ≤ 1) (x : ι → F) :
    RowsHold linear products x ↔ (Ligero.Routing.sourceSystem products poly hpoly).Holds x := by
  rw [Ligero.Routing.sourceSystem_holds_iff]
  simp only [← h, AffineForm.eval_toMvPolynomial]
  exact ⟨fun h => ⟨h.linear, h.products⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Rows side by side hold exactly when each family holds. -/
@[simp]
theorem rowsHold_sum {Lin₁ Lin₂ Q₁ Q₂ : Type} (linear₁ : Lin₁ → AffineForm F ι)
    (linear₂ : Lin₂ → AffineForm F ι) (products₁ : Ligero.Routing.ProductLayout ι Q₁)
    (products₂ : Ligero.Routing.ProductLayout ι Q₂) (x : ι → F) :
    RowsHold (Sum.elim linear₁ linear₂) (products₁.sum products₂) x ↔
      RowsHold linear₁ products₁ x ∧ RowsHold linear₂ products₂ x := by
  constructor
  · intro h
    have hp := (Ligero.Routing.sourceProducts_sum products₁ products₂ x).mp h.products
    exact ⟨⟨fun l => h.linear (.inl l), hp.1⟩, ⟨fun l => h.linear (.inr l), hp.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Sum.rec h₁.linear h₂.linear,
      (Ligero.Routing.sourceProducts_sum products₁ products₂ x).mpr ⟨h₁.products, h₂.products⟩⟩

/-! ### The interface -/

/-- **A masked row reduction** on witnesses `Wit` whose committed cells are `cells`: a public-coin
interactive proof `spec` whose prover messages are sent masked by pads committed in the cells,
with its verifier's checks deferred to rows on the cells: the linear rows `linear p tr` at the
public input and the full transcript (affine forms the verifier computes), and the product
triples `products`, fixed before commitment. Frigo–shelat Protocol 2.5 (p. 9) and CHVY25
Figure 1 for GKR; see the module docstring.

This is the computational part: the protocol and the rows. Its soundness for a relation, with
its round errors, is `MaskedRowReduction.Sound`; the honest prover and the simulator are
`MaskedRowReduction.Honest`. Keeping the errors out of this structure keeps the projections of a concrete
instance computable. -/
structure FieldProof.MaskedRowReduction (F ι : Type) [Field F] [Fintype ι] (Pub Wit : Type) (cells : Wit → ι → F) where
  /-- The number of rounds. -/
  n : ℕ
  /-- The interactive proof. -/
  spec : ProtocolSpec n
  [fintype : ∀ i, Fintype (spec.Challenge i)]
  [decEq : ∀ i, DecidableEq (spec.Challenge i)]
  [nonempty : ∀ i, Nonempty (spec.Challenge i)]
  /-- The linear rows' index. -/
  Lin : Type
  [finLin : Fintype Lin]
  /-- The linear rows' encoding, which numbers them (`Encodable.fintypeEquivFin`). -/
  [encLin : Encodable Lin]
  /-- The affine rows the verifier computes from the public input and the transcript. -/
  linear : Pub → spec.Transcript (Fin.last n) → Lin → AffineForm F ι
  /-- The product triples' index. -/
  Q : Type
  [finQ : Fintype Q]
  /-- The product triples' encoding, which numbers them (`Encodable.fintypeEquivFin`). -/
  [encQ : Encodable Q]
  /-- The product triples, fixed before commitment. -/
  products : Ligero.Routing.ProductLayout ι Q

attribute [instance] FieldProof.MaskedRowReduction.fintype FieldProof.MaskedRowReduction.decEq FieldProof.MaskedRowReduction.nonempty FieldProof.MaskedRowReduction.finLin FieldProof.MaskedRowReduction.finQ
  FieldProof.MaskedRowReduction.encLin FieldProof.MaskedRowReduction.encQ

namespace FieldProof.MaskedRowReduction

/-- **An instance of a masked row reduction's relation**: the public input and the witness whose cells are
committed. -/
structure Instance (Pub Wit : Type) where
  /-- The public input. -/
  pub : Pub
  /-- The witness. -/
  wit : Wit

variable {Pub Wit : Type} {cells : Wit → ι → F} {sat s₁ s₂ : Pub → Wit → Prop}

/-- **Soundness of a masked row reduction** for the relation `sat`, with per-round errors `ε`:
`reduction` reduces `sat` (`claim_iff`) to the rows on the cells (`claimOut_iff`), round by
round with error `ε i` at challenge round `i`; the masks do not enter, since the reduction is
stated on the cells, which hold the pads. -/
structure Sound (M : MaskedRowReduction F ι Pub Wit cells) (sat : Pub → Wit → Prop)
    (ε : M.spec.ChallengeIdx → ℝ≥0) where
  /-- The reduction from `sat` to the rows. -/
  reduction : ClaimReduction M.spec (Instance Pub Wit) ε
  claim_iff : ∀ p w, reduction.claim ⟨p, w⟩ ↔ sat p w
  claimOut_iff : ∀ p w tr,
    reduction.claimOut ⟨p, w⟩ tr ↔ RowsHold (M.linear p tr) M.products (cells w)

/-- **The context of a masked row reduction's rows**: the public input and the full transcript, on which
the verifier computes the affine rows (`rowsAt`). -/
structure Context (M : MaskedRowReduction F ι Pub Wit cells) where
  /-- The public input. -/
  pub : Pub
  /-- The full transcript. -/
  transcript : M.spec.Transcript (Fin.last M.n)

/-- The affine rows at a context. -/
abbrev rowsAt (M : MaskedRowReduction F ι Pub Wit cells) (c : M.Context) : M.Lin → AffineForm F ι :=
  M.linear c.pub c.transcript

/-- **Sequential composition.** Two masked row reductions on the same cells, run one after the other:
the rows stand side by side. -/
def append (A B : MaskedRowReduction F ι Pub Wit cells) : MaskedRowReduction F ι Pub Wit cells where
  n := A.n + B.n
  spec := A.spec ++ B.spec
  Lin := A.Lin ⊕ B.Lin
  linear p tr := Sum.elim (A.linear p tr.left) (B.linear p tr.right)
  Q := A.Q ⊕ B.Q
  products := A.products.sum B.products

/-! ### The honest prover and the simulator -/

/-- **An honest input with the pads of an earlier phase**: the honest input of the second of two
masked row reductions run in sequence (`Honest.append`), which may commit data derived from the first
phase's pads. -/
structure WithPads (In Pads : Type) where
  /-- The honest input. -/
  input : In
  /-- The first phase's pads. -/
  pads : Pads

/-- **A simulator of a masked row reduction's transcript** (`IOP.TranscriptSim`): coins, and the
transcript simulated from the public input and the challenges only. It is data apart from the
honest prover (`Honest`), which states that its transcript has this simulator's law. -/
abbrev Sim (M : MaskedRowReduction F ι Pub Wit cells) : Type 1 := IOP.TranscriptSim Pub M.spec

/-- **The honest prover of a masked row reduction**, on honest inputs `In` in the domain `dom`,
simulated by `S`. The prover draws pads `Pads` and runs `prover`, a causal transcript family whose
messages are its unmasked messages minus the pads. `Commits p x π w` says that the committed
witness `w` holds the honest input `x` and the pads `π`; the committed witness itself is built
by the field instance, which may hold the pads of several masked row reductions.

Completeness (`complete`): on the domain, the honest transcript satisfies the rows on every
such witness, for every challenge. HVZK of the masked transcript (`identDistrib`): at fixed
challenges the honest transcript under uniform pads has the law of `S.sim`, which reads the
public input and the challenges only (CHVY25 Theorem 4.1's simulation of the masked
transcript; Frigo–shelat Theorem 6). The pads must also be hidden by the commitment: that is
the commit-and-prove system's `CommitProve.Honest.hides`, stated at each fixed vector of cells,
and `FieldProof.hvzk` composes the two. -/
structure Honest (M : MaskedRowReduction F ι Pub Wit cells) (In : Type) (dom : Pub → In → Prop)
    (S : M.Sim) where
  /-- The pads. -/
  Pads : Type
  [fintype : Fintype Pads]
  [nonempty : Nonempty Pads]
  /-- The honest prover's transcript family. -/
  prover : Pub → In → Pads → CausalTranscript M.spec
  /-- The committed witness holds the honest input and the pads. -/
  Commits : Pub → In → Pads → Wit → Prop
  /-- The honest transcript satisfies the rows. -/
  complete : ∀ p x, dom p x → ∀ π w, Commits p x π w → ∀ ch,
    RowsHold (M.linear p ((prover p x π).transcript ch)) M.products (cells w)
  /-- The honest transcript has the simulator's law. -/
  identDistrib : ∀ p x, dom p x → ∀ ch, (fun π => (prover p x π).transcript ch) =ᵈ S.sim p ch

attribute [instance] Honest.fintype Honest.nonempty

/-! ### Rows with no rounds -/

/-- The protocol with no moves. -/
def noRounds : ProtocolSpec 0 := ⟨Fin.elim0, Fin.elim0⟩

instance (i : noRounds.ChallengeIdx) : Fintype (noRounds.Challenge i) := i.1.elim0
instance (i : noRounds.ChallengeIdx) : Nonempty (noRounds.Challenge i) := i.1.elim0
instance (i : noRounds.ChallengeIdx) : DecidableEq (noRounds.Challenge i) := i.1.elim0

/-- **Rows with no interaction** as a masked row reduction: no IP rounds and no pads; Ligero checks the
rows `linear p` and `products` directly. The application's own rows on a field instance (the
scheme rows of an A circuit) are this instance. -/
def static {Lin Q : Type} [Fintype Lin] [Fintype Q] [Encodable Lin] [Encodable Q]
    (linear : Pub → Lin → AffineForm F ι)
    (products : Ligero.Routing.ProductLayout ι Q) : MaskedRowReduction F ι Pub Wit cells where
  n := 0
  spec := noRounds
  Lin := Lin
  linear p _ := linear p
  Q := Q
  products := products

end FieldProof.MaskedRowReduction

end GordieHowe
