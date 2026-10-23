-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedRowReduction
public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.Model.IOP.CommitPhase

@[expose] public section

/-!
# Commit-and-prove systems for quadratic constraints

A **commit-and-prove system** (Thaler 2023, ch. 13 p. 197: "a technique often called
commit-and-prove"; LegoSNARK p. 1) for quadratic constraints on cells `ι → F`:

* a **commit phase** commits to a vector of cells: in round 0 one oracle message `Com`, read by
  the verifier as a table of `nLeaves` leaves (`leaf`), a Merkle tree's leaves once compiled
  (BCS16 §3.2 p. 15), then the rounds `commitRounds` (none for a one-message commitment; FRI's
  commit phase is interactive in the same way, BCIKS20 §8.2), every message of which is read in
  full;
* later, given a context `c` fixed after the commit phase (with the oracle message and the commit
  rounds, a `CommitProve.Input`), a proof phase `spec` proves that the rows `rows c` (affine forms
  chosen from the context, `AffineForm`) and the product triples `products` (fixed before the
  commitment, `Ligero.Routing.ProductLayout`) hold on the cells the commit phase determines:
  `RowsHold (rows c) products (extract O tr)`.

`CommitProve` is the computational part: the oracle message, its leaves, the commit rounds, the
cells extracted from the commit phase (`extract`, part of every extractor built on the system, so
an instance must give a computable, polynomial-time one), the oracle structure that the BCS
compilation reads (the leaves and the queried leaves `queries ch`; the byte serialization of a
leaf is the BCS format's leaf codec, `BCS.Format.leaf`), the proof phase and its verifier `V`,
with the locality of the verdict (`reads`: the verdict depends on the oracle message only through
the queried leaves, `SameLeavesAt`, and every other message is read in full, a non-oracle message
in the sense of CY24 p. 259). Its soundness with commit-phase errors `εc` and proof-phase errors
`ε` is `CommitProve.Sound`: commit-phase events `commitEvent` of probability at most `εc i` at
their rounds, and a `ClaimProof` on inputs with verifier `V`, round-by-round sound relative to
"the commit phase was bad (`CommitBad`) or the rows hold on the extracted cells". The errors are
kept out of `CommitProve` so that the projections of a concrete instance are computable
definitions.

`CommitProve.Honest` states the honest prover: the honest oracle message, commit rounds and proof
from the cells and the prover's coins, completeness on admissible cells satisfying the rows
(`Admits`), and honest-verifier zero knowledge (`hides`): at every fixed vector of admissible
cells satisfying the rows, the verifier's view (`CommitProve.View`: the queried leaves, the commit
rounds and the proof-phase transcript) has the law of a named simulator that reads the context
and the challenges only. Because the cells are fixed in that statement, the view hides every cell
beyond the rows holding; in particular it hides the one-time pads of a masked row reduction committed among
the cells, which is what the masked-row-reduction simulation consumes (`GordieHowe.FieldProof.hvzk`).

Ligero (CHVY25 §4; Frigo–shelat §2) at agreement threshold `A` is the instance
(`GordieHowe.Ligero.AgreementThreshold.commitProve`, `GordieHowe.Ligero.MaskTest.Pieces.commitProve`, and their relatively packed forms
`GordieHowe.Ligero.MaskRow.Setup.commitProve`).
-/

namespace GordieHowe
open IOP

open ProtocolSpec
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι]

/-- **The input of a commit-and-prove proof phase**: the context, fixed after the commit phase,
the oracle message and the rest of the commit phase. -/
structure FieldProof.CommitProve.Input (Ctx Com R : Type) where
  /-- The context. -/
  ctx : Ctx
  /-- The oracle message. -/
  com : Com
  /-- The rest of the commit phase. -/
  rounds : R

/-- **Two commitments agree at the leaves `s`**: their leaves are equal at every position of
`s`. -/
def FieldProof.CommitProve.SameLeavesAt {Com Leaf : Type} {N : ℕ} (leaf : Com → Fin N → Leaf)
    (s : Finset (Fin N)) (O O' : Com) : Prop :=
  ∀ j ∈ s, leaf O j = leaf O' j

/-- **A commit-and-prove system for quadratic constraints** on cells `ι → F`, for the rows
`rows c` (affine forms chosen from the context `c`) and the product triples `products` (fixed
before the commitment): the computational part. Its soundness is `CommitProve.Sound`, its
honest prover `CommitProve.Honest`. See the module docstring. -/
structure FieldProof.CommitProve (F ι : Type) [Field F] [Fintype ι] {Lin Q : Type} [Fintype Lin]
    [Fintype Q] (products : Ligero.Routing.ProductLayout ι Q) (Ctx : Type)
    (rows : Ctx → Lin → AffineForm F ι) where
  /-- The oracle message of the commit phase. -/
  Com : Type
  /-- The number of leaves of the oracle message. -/
  nLeaves : ℕ
  /-- The leaf type. -/
  Leaf : Type
  /-- The leaves of an oracle message. -/
  leaf : Com → Fin nLeaves → Leaf
  /-- The leaves determine the oracle message. -/
  leaf_injective : Function.Injective leaf
  /-- The oracle message with the given leaves. Every table of leaves is an oracle message: the
  compiled commitment is a Merkle tree over any table, and the extractor of the compiled proof
  reads an oracle message back from the leaves it finds (`BCS.IOP.parts`). -/
  ofLeaves : (Fin nLeaves → Leaf) → Com
  leaf_ofLeaves : ∀ l, leaf (ofLeaves l) = l
  /-- The leaf read where a leaf is missing or does not parse. -/
  leafDefault : Leaf
  /-- The number of rounds of the commit phase after the oracle message. -/
  nc : ℕ
  /-- The rounds of the commit phase after the oracle message (none for a one-message
  commitment). -/
  commitRounds : ProtocolSpec nc
  [commitFintype : ∀ i, Fintype (commitRounds.Challenge i)]
  [commitDecEq : ∀ i, DecidableEq (commitRounds.Challenge i)]
  [commitNonempty : ∀ i, Nonempty (commitRounds.Challenge i)]
  /-- The cells extracted from the commit phase. It is part of the extractor of every protocol
  built on the system (`MultiCircuitIOP.extractor`), so an instance must give a computable
  definition that runs in polynomial time, with a "Running time" docstring. -/
  extract : Com → commitRounds.Transcript (Fin.last nc) → ι → F
  /-- The number of rounds of the proof phase. -/
  n : ℕ
  /-- The proof phase. -/
  spec : ProtocolSpec n
  [fintype : ∀ i, Fintype (spec.Challenge i)]
  [decEq : ∀ i, DecidableEq (spec.Challenge i)]
  [nonempty : ∀ i, Nonempty (spec.Challenge i)]
  /-- The proof phase draws a challenge (the column query, for Ligero). -/
  [nonemptyIdx : Nonempty spec.ChallengeIdx]
  /-- The verifier's decision on the input and the proof-phase transcript. -/
  V : CommitProve.Input Ctx Com (commitRounds.Transcript (Fin.last nc)) →
    spec.Transcript (Fin.last n) → Bool
  /-- The leaves the verifier queries at the challenges `ch`. -/
  queries : spec.Challenges → Finset (Fin nLeaves)
  /-- **Query locality**: at the challenges `ch`, the verdict depends on the oracle message only
  through its leaves at `queries ch`. The commit rounds and every proof-phase message are read in
  full. -/
  reads : ∀ c ch (O O' : Com) r (tr : spec.Transcript (Fin.last n)),
    (∀ i : spec.ChallengeIdx, tr i.1 = ch i) → CommitProve.SameLeavesAt leaf (queries ch) O O' →
    V ⟨c, O, r⟩ tr = V ⟨c, O', r⟩ tr

attribute [instance] FieldProof.CommitProve.commitFintype FieldProof.CommitProve.commitDecEq FieldProof.CommitProve.commitNonempty
  FieldProof.CommitProve.fintype FieldProof.CommitProve.decEq FieldProof.CommitProve.nonempty FieldProof.CommitProve.nonemptyIdx

namespace FieldProof.CommitProve

variable {Lin Q : Type} [Fintype Lin] [Fintype Q] {products : Ligero.Routing.ProductLayout ι Q}
  {Ctx : Type} {rows : Ctx → Lin → AffineForm F ι}

/-- The full transcript of the commit rounds. -/
abbrev Rounds (CP : CommitProve F ι products Ctx rows) : Type :=
  CP.commitRounds.Transcript (Fin.last CP.nc)

/-- **The commit phase was bad**: the commit-phase event of some challenge round occurred, on the
commit rounds up to and including it (`EventOccurs`). -/
def CommitBad (CP : CommitProve F ι products Ctx rows)
    (commitEvent : (i : CP.commitRounds.ChallengeIdx) → CP.Com →
      CP.commitRounds.Transcript i.1.succ → Prop) (O : CP.Com) (tr : CP.Rounds) : Prop :=
  EventOccurs commitEvent O tr

/-- **Soundness of a commit-and-prove system** with commit-phase errors `εc` and proof-phase
errors `ε`: commit-phase events, the event of round `i` a function of the oracle message and the
commit rounds up to and including that challenge, of probability at most `εc i` over the
challenge at every prefix (`commitEvent_bound`, `ProtocolSpec.EventBound`); and a claim-proving phase with the system's
verifier (`V_eq`), round-by-round sound relative to "the commit phase was bad or the rows hold on
the extracted cells" (`claim_iff`). -/
structure Sound (CP : CommitProve F ι products Ctx rows)
    (εc : CP.commitRounds.ChallengeIdx → ℝ≥0) (ε : CP.spec.ChallengeIdx → ℝ≥0) where
  /-- The commit-phase event at challenge `i`: a function of the oracle message and the commit
  rounds up to and including that challenge. -/
  commitEvent : (i : CP.commitRounds.ChallengeIdx) → CP.Com →
    CP.commitRounds.Transcript i.1.succ → Prop
  /-- At every oracle message and every prefix, the event of round `i` has probability at most
  `εc i` over the challenge of round `i`. -/
  commitEvent_bound : CP.commitRounds.EventBound commitEvent εc
  /-- Round-by-round soundness of the proof phase. -/
  proof : ClaimProof CP.spec (Input Ctx CP.Com CP.Rounds) ε
  /-- Its verifier is the system's. -/
  V_eq : ∀ c tr, proof.V c tr = CP.V c tr
  /-- The claim is a bad commit phase or the rows on the extracted cells. -/
  claim_iff : ∀ c, proof.claim c ↔
    CP.CommitBad commitEvent c.com c.rounds ∨
      RowsHold (rows c.ctx) products (CP.extract c.com c.rounds)

variable {CP : CommitProve F ι products Ctx rows} {εc : CP.commitRounds.ChallengeIdx → ℝ≥0}
  {ε : CP.spec.ChallengeIdx → ℝ≥0}

/-- The claim-proving phase of a sound system, with the system's verifier `V` itself. -/
def Sound.claimProof (S : CP.Sound εc ε) : ClaimProof CP.spec (Input Ctx CP.Com CP.Rounds) ε :=
  S.proof.withV CP.V S.V_eq

@[simp] theorem Sound.claimProof_V (S : CP.Sound εc ε) : S.claimProof.V = CP.V := rfl

/-- **The commit-phase events as a state** (`BadState.ofEvents`): bad exactly when the commit
phase was bad (`CommitBad`). -/
def Sound.commitState (S : CP.Sound εc ε) : BadState CP.commitRounds CP.Com εc :=
  BadState.ofEvents S.commitEvent S.commitEvent_bound

@[simp] theorem Sound.commitState_bad (S : CP.Sound εc ε) (O : CP.Com) (tr : CP.Rounds) :
    S.commitState.bad O tr ↔ CP.CommitBad S.commitEvent O tr :=
  Iff.rfl

/-- **How the verifier reads an oracle message**: its leaves, at the queried leaves. -/
def comView (CP : CommitProve F ι products Ctx rows) :
    MessageView CP.Com CP.spec.Challenges (Fin CP.nLeaves) CP.Leaf where
  read := CP.leaf
  read_injective := CP.leaf_injective
  queries := CP.queries

/-- Two oracle messages agree at the queried leaves exactly when the verifier sees the same of
them. -/
theorem sameLeavesAt_iff_see (CP : CommitProve F ι products Ctx rows) {ch : CP.spec.Challenges}
    {O O' : CP.Com} :
    SameLeavesAt CP.leaf (CP.queries ch) O O' ↔ CP.comView.see ch O = CP.comView.see ch O' := by
  constructor
  · intro h
    funext j
    by_cases hj : j ∈ CP.queries ch
    · rw [MessageView.see_of_mem _ hj, MessageView.see_of_mem _ hj]
      exact congrArg some (h j hj)
    · simp only [MessageView.see, comView, hj, ↓reduceIte]
  · intro h j hj
    have hj' := congrFun h j
    rw [MessageView.see_of_mem _ hj, MessageView.see_of_mem _ hj] at hj'
    exact Option.some_injective _ hj'

/-- **What the verifier sees** (the IOP verifier's view, CY24 Definition 23.1.7, p. 261, without
the statement and the challenges): the queried leaves of the oracle message, the commit rounds
and the proof-phase transcript, every message of the latter two read in full. -/
structure View (CP : CommitProve F ι products Ctx rows) where
  /-- The oracle message's leaves at the queried positions, `none` elsewhere. -/
  leaves : Fin CP.nLeaves → Option CP.Leaf
  /-- The commit rounds. -/
  rounds : CP.Rounds
  /-- The proof-phase transcript. -/
  transcript : CP.spec.Transcript (Fin.last CP.n)

/-- The view of an oracle message, the commit rounds and a proof-phase transcript at the
challenges `ch`. -/
def view (CP : CommitProve F ι products Ctx rows) (ch : CP.spec.Challenges)
    (O : CP.Com) (r : CP.Rounds) (tr : CP.spec.Transcript (Fin.last CP.n)) : CP.View :=
  ⟨CP.comView.see ch O, r, tr⟩

/-- Equal views of two oracle messages give equal verdicts. -/
theorem V_eq_of_see (CP : CommitProve F ι products Ctx rows) (c : Ctx) {O O' : CP.Com}
    {r : CP.Rounds} {ch : CP.spec.Challenges} {tr : CP.spec.Transcript (Fin.last CP.n)}
    (htr : ∀ i : CP.spec.ChallengeIdx, tr i.1 = ch i)
    (h : CP.comView.see ch O = CP.comView.see ch O') :
    CP.V ⟨c, O, r⟩ tr = CP.V ⟨c, O', r⟩ tr :=
  CP.reads c ch O O' r tr htr (CP.sameLeavesAt_iff_see.mpr h)

/-- **The honest prover may commit to the cells `x` for the rows `rows`**: the cells are
admissible (`Admissible`, a property of the honest cells) and satisfy the rows. -/
structure Admits {Lin' : Type} (Admissible : (ι → F) → Prop) (rows : Lin' → AffineForm F ι)
    (products : Ligero.Routing.ProductLayout ι Q) (x : ι → F) : Prop where
  admissible : Admissible x
  rowsHold : RowsHold rows products x

/-- **A simulator of a commit-and-prove system's view**: coins drawn uniformly, and the view simulated
from the context and the challenges only. It is data apart from the honest prover (`Honest`), which
states that its view has this simulator's law. -/
structure Sim (CP : CommitProve F ι products Ctx rows) where
  /-- The simulator's coins. -/
  SimCoins : Type
  [simFintype : Fintype SimCoins]
  [simNonempty : Nonempty SimCoins]
  /-- The simulator, on the context and the challenges only. -/
  sim : Ctx → CP.commitRounds.Challenges → CP.spec.Challenges → SimCoins → CP.View

attribute [instance] Sim.simFintype Sim.simNonempty

/-- **The honest prover of a commit-and-prove system**, simulated by `S`: the honest oracle message
and commit rounds from the cells with the prover's coins, fixed before the context, and the honest
proof on a context and the commit rounds; completeness on admissible cells satisfying the rows;
and honest-verifier zero knowledge at the simulator `S`. `Admissible` holds the facts about
the honest cells that the hiding argument needs (for Ligero, that the cells lie in their rows'
blinding fields).

`hides` is CY24 Definition 23.1.8 (p. 261) with perfect simulation, stated at every fixed
vector of cells: the view hides every cell beyond the rows holding, including the pads of a
masked row reduction committed among the cells, which is what the masked-row-reduction simulation consumes. -/
structure Honest (CP : CommitProve F ι products Ctx rows) (S : CP.Sim) where
  /-- The prover's coins (its blinding). -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The honest oracle message for the cells. -/
  commit : (ι → F) → Coins → CP.Com
  /-- The honest commit rounds for the cells. -/
  commitRounds : (ι → F) → Coins → CausalTranscript CP.commitRounds
  /-- The honest proof on a context and the commit rounds. -/
  prove : Ctx → (ι → F) → Coins → CP.Rounds → CausalTranscript CP.spec
  /-- The cells the honest prover may commit to. -/
  Admissible : (ι → F) → Prop
  /-- On admissible cells satisfying the rows, the verifier accepts the honest proof at every
  challenge. -/
  complete : ∀ c x, Admits Admissible (rows c) products x → ∀ ρ chc ch,
    CP.V ⟨c, commit x ρ, (commitRounds x ρ).transcript chc⟩
      ((prove c x ρ ((commitRounds x ρ).transcript chc)).transcript ch) = true
  /-- At every fixed admissible cell vector satisfying the rows, the honest view under uniform
  coins has the simulator's law. -/
  hides : ∀ c x, Admits Admissible (rows c) products x → ∀ chc ch,
    (fun ρ => CP.view ch (commit x ρ) ((commitRounds x ρ).transcript chc)
      ((prove c x ρ ((commitRounds x ρ).transcript chc)).transcript ch)) =ᵈ S.sim c chc ch

attribute [instance] Honest.fintype Honest.nonempty

/-! ### Soundness with a condition on the extracted cells -/

/-- **Soundness with a condition `Good` on the extracted cells**: as `Sound`, with the claim "the
commit phase was bad, or the rows hold on the extracted cells and `Good` holds there". Ligero with
the prefix-row subfield test is sound in this form, with `Good` "every prefix cell lies in the
subfield" (`Ligero.MaskRow.Setup.sound`). -/
structure SoundOn (CP : CommitProve F ι products Ctx rows) (Good : (ι → F) → Prop)
    (εc : CP.commitRounds.ChallengeIdx → ℝ≥0) (ε : CP.spec.ChallengeIdx → ℝ≥0) where
  /-- The commit-phase event at challenge `i`. -/
  commitEvent : (i : CP.commitRounds.ChallengeIdx) → CP.Com →
    CP.commitRounds.Transcript i.1.succ → Prop
  /-- At every oracle message and every prefix, the event of round `i` has probability at most
  `εc i` over the challenge of round `i`. -/
  commitEvent_bound : CP.commitRounds.EventBound commitEvent εc
  /-- Round-by-round soundness of the proof phase. -/
  proof : ClaimProof CP.spec (Input Ctx CP.Com CP.Rounds) ε
  /-- Its verifier is the system's. -/
  V_eq : ∀ c tr, proof.V c tr = CP.V c tr
  /-- The claim is a bad commit phase, or the rows and `Good` on the extracted cells. -/
  claim_iff : ∀ c, proof.claim c ↔
    CP.CommitBad commitEvent c.com c.rounds ∨
      (RowsHold (rows c.ctx) products (CP.extract c.com c.rounds) ∧
        Good (CP.extract c.com c.rounds))

/-- **The system with its extracted cells confined by `proj`**: the same oracle message, rounds,
proof phase and verifier; the extracted cells are `proj` of the system's. An instance's `proj`
must be computable and polynomial-time, since it becomes part of the extractor. -/
def confine (CP : CommitProve F ι products Ctx rows) (proj : (ι → F) → ι → F) :
    CommitProve F ι products Ctx rows :=
  { CP with extract := fun O r => proj (CP.extract O r) }

/-- **`proj` confines the cells to `Good`**: every confined vector satisfies `Good`, and `proj`
fixes the vectors that already do. -/
structure Confines (Good : (ι → F) → Prop) (proj : (ι → F) → ι → F) : Prop where
  /-- Every confined vector satisfies `Good`. -/
  good : ∀ x, Good (proj x)
  /-- `proj` fixes the vectors satisfying `Good`. -/
  fixes : ∀ x, Good x → proj x = x

/-- **A system sound on `Good` is sound once its extracted cells are confined to `Good`**: when
the extracted cells satisfy the rows and `Good`, `proj` fixes them, so the confined cells satisfy
the rows (`ClaimProof.weaken`). -/
def SoundOn.confine {Good : (ι → F) → Prop} {proj : (ι → F) → ι → F} (S : CP.SoundOn Good εc ε)
    (h : Confines Good proj) : (CP.confine proj).Sound εc ε where
  commitEvent := S.commitEvent
  commitEvent_bound := S.commitEvent_bound
  proof := S.proof.weaken (fun c => CP.CommitBad S.commitEvent c.com c.rounds ∨
      RowsHold (rows c.ctx) products (proj (CP.extract c.com c.rounds)))
    fun c hc => ((S.claim_iff c).mp hc).imp id fun hg => by
      rw [h.fixes _ hg.2]
      exact hg.1
  V_eq := S.V_eq
  claim_iff _ := Iff.rfl

/-- A view of the system as a view of the confined system (the same leaves, rounds and
transcript). -/
def viewConfine (CP : CommitProve F ι products Ctx rows) (proj : (ι → F) → ι → F) (v : CP.View) :
    (CP.confine proj).View :=
  ⟨v.leaves, v.rounds, v.transcript⟩

end FieldProof.CommitProve

end GordieHowe
