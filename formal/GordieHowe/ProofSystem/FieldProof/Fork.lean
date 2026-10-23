-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.CircuitShape
public import GordieHowe.Model.IOP.ClaimReduction
public import GordieHowe.ProofSystem.FieldProof.CommitProve

@[expose] public section

/-!
# A circuit proof forked into branches and a join

The proof system runs a domain's proof phase as a fork (`lib/gordiehowe/transcript_fork.h`; the term
of `GordieHowe/ProofSystem/Program/ForkJoinShape.lean`): after the commit phase and the application phase, each of the
domain's batches and its GKR run as a branch of their own, side by side, each leaving claims on
the committed cells; the join part then reads the branches' transcripts and runs the domain's
packing stages and its commit-and-prove proof.

* `GordieHowe.FieldProof.BranchShape`: the computational part. The oracle message and the commit rounds of the commit
  phase with the witness extracted from them (as `GordieHowe.FieldProof.Shape`), `nb` branch protocols, the join
  protocol, and the verdict on the public input, the commit phase, the branches' transcripts and
  the join's transcript.
* `GordieHowe.FieldProof.BranchShape.Sound`: the commit phase's bad events (`BadState`), a claim reduction per branch on
  the statement (`GordieHowe.FieldProof.Shape.Statement`: the public input and the commit phase), a claim-proving
  phase of the join on the statement and the branches' transcripts with the verdict, and a fixed
  claim on the statement alone (the domain's rows that no branch proves). The join's claim gives
  every branch's output claim and the fixed claim (`join_claim`); the branches' input claims with
  the fixed claim give "the commit phase was bad or `holds` on the extracted witness"
  (`claim_imp`).
-/

namespace GordieHowe
open IOP IOP.ProtocolSpec
open scoped NNReal

/-- **The computational part of a forked circuit proof** (module docstring). -/
structure FieldProof.BranchShape (Pub Wit : Type) where
  /-- The oracle message of the commit phase. -/
  Com : Type
  /-- The number of rounds of the commit phase after the oracle message. -/
  nc : ℕ
  /-- The rounds of the commit phase after the oracle message. -/
  commitRounds : ProtocolSpec nc
  [commitFintype : ∀ i, Fintype (commitRounds.Challenge i)]
  [commitDecEq : ∀ i, DecidableEq (commitRounds.Challenge i)]
  [commitNonempty : ∀ i, Nonempty (commitRounds.Challenge i)]
  /-- The witness extracted from the commit phase. It is part of every extractor built on the
  proof, so an instance must give a computable, polynomial-time definition. -/
  ext : Com → commitRounds.Transcript (Fin.last nc) → Wit
  /-- The number of branches. -/
  nb : ℕ
  /-- There is a branch (every domain has its GKR branch). -/
  nb_pos : 0 < nb
  /-- The number of rounds of each branch. -/
  bn : Fin nb → ℕ
  /-- The branches. -/
  branch : (b : Fin nb) → ProtocolSpec (bn b)
  [branchFintype : ∀ b i, Fintype ((branch b).Challenge i)]
  [branchDecEq : ∀ b i, DecidableEq ((branch b).Challenge i)]
  [branchNonempty : ∀ b i, Nonempty ((branch b).Challenge i)]
  /-- The number of rounds of the join. -/
  jn : ℕ
  /-- The join. -/
  join : ProtocolSpec jn
  [joinFintype : ∀ i, Fintype (join.Challenge i)]
  [joinDecEq : ∀ i, DecidableEq (join.Challenge i)]
  [joinNonempty : ∀ i, Nonempty (join.Challenge i)]
  /-- The join draws a challenge (the column query, for Ligero). -/
  [joinNonemptyIdx : Nonempty join.ChallengeIdx]
  /-- The verdict on the public input, the commit phase, the branches' transcripts and the join's
  transcript. -/
  V : Pub → Com → commitRounds.Transcript (Fin.last nc) →
    ((b : Fin nb) → (branch b).Transcript (Fin.last (bn b))) → join.Transcript (Fin.last jn) → Bool

attribute [instance] FieldProof.BranchShape.commitFintype FieldProof.BranchShape.commitDecEq FieldProof.BranchShape.commitNonempty
  FieldProof.BranchShape.branchFintype FieldProof.BranchShape.branchDecEq FieldProof.BranchShape.branchNonempty FieldProof.BranchShape.joinFintype
  FieldProof.BranchShape.joinDecEq FieldProof.BranchShape.joinNonempty FieldProof.BranchShape.joinNonemptyIdx

variable {Pub Wit : Type}

namespace FieldProof.BranchShape

variable (sh : BranchShape Pub Wit)

/-- The full transcript of the commit rounds. -/
abbrev Rounds : Type := sh.commitRounds.Transcript (Fin.last sh.nc)

/-- The statement of the branches: the public input and the commit phase. -/
abbrev Stmt : Type := Shape.Statement Pub sh.Com sh.Rounds

/-- The full transcripts of the branches. -/
abbrev BranchTrs : Type := (b : Fin sh.nb) → (sh.branch b).Transcript (Fin.last (sh.bn b))

/-- The statement of the join: the branches' statement and the branches' full transcripts. -/
structure JoinStmt where
  /-- The branches' statement. -/
  stmt : sh.Stmt
  /-- The branches' full transcripts. -/
  trs : sh.BranchTrs

/-- **Soundness of a forked circuit proof** relative to `holds` (module docstring). -/
structure Sound (holds : Pub → Wit → Prop) where
  /-- The commit phase's round errors. -/
  εc : sh.commitRounds.ChallengeIdx → ℝ≥0
  /-- The commit phase's bad events. -/
  commit : BadState sh.commitRounds sh.Com εc
  /-- Each branch's round errors. -/
  εb : (b : Fin sh.nb) → (sh.branch b).ChallengeIdx → ℝ≥0
  /-- Each branch's claim reduction on the statement. -/
  red : (b : Fin sh.nb) → ClaimReduction (sh.branch b) sh.Stmt (εb b)
  /-- The join's round errors. -/
  εj : sh.join.ChallengeIdx → ℝ≥0
  /-- The join's claim-proving phase. -/
  proof : ClaimProof sh.join sh.JoinStmt εj
  /-- The join's verifier is the verdict. -/
  V_eq : ∀ s tr, proof.V s tr = sh.V s.stmt.pub s.stmt.com s.stmt.rounds s.trs tr
  /-- The claim on the statement alone that no branch proves. -/
  fixed : sh.Stmt → Prop
  /-- The join's claim gives every branch's output claim and the fixed claim. -/
  join_claim : ∀ s, proof.claim s → (∀ b, (red b).claimOut s.stmt (s.trs b)) ∧ fixed s.stmt
  /-- The branches' input claims and the fixed claim give a bad commit phase or the relation on
  the extracted witness. -/
  claim_imp : ∀ s, (∀ b, (red b).claim s) → fixed s →
    commit.bad s.com s.rounds ∨ holds s.pub (sh.ext s.com s.rounds)

/-- **How a forked circuit proof's verdict reads its oracle message**: the oracle message is a
table of leaves (`leaf`, every table an oracle message, `ofLeaves`), read at the leaves `queries`
drawn by the join's challenges; the commit rounds, the branches' messages and the join's messages
are read in full (`reads`). -/
structure Oracle where
  /-- The number of leaves of the oracle message. -/
  nLeaves : ℕ
  /-- The leaf type. -/
  Leaf : Type
  /-- The leaves of an oracle message. -/
  leaf : sh.Com → Fin nLeaves → Leaf
  /-- The leaves determine the oracle message. -/
  leaf_injective : Function.Injective leaf
  /-- The oracle message with the given leaves. -/
  ofLeaves : (Fin nLeaves → Leaf) → sh.Com
  leaf_ofLeaves : ∀ l, leaf (ofLeaves l) = l
  /-- The leaf read where a leaf is missing or does not parse. -/
  leafDefault : Leaf
  /-- The leaves the verdict reads at the join's challenges. -/
  queries : sh.join.Challenges → Finset (Fin nLeaves)
  /-- **Query locality**: at the join's challenges `ch`, the verdict depends on the oracle message
  only through its leaves at `queries ch`. -/
  reads : ∀ p (O O' : sh.Com) r trs ch (tr : sh.join.Transcript (Fin.last sh.jn)),
    (∀ i : sh.join.ChallengeIdx, tr i.1 = ch i) → CommitProve.SameLeavesAt leaf (queries ch) O O' →
    sh.V p O r trs tr = sh.V p O' r trs tr

/-- An oracle message as its table of leaves. -/
def Oracle.leafEquiv {sh : BranchShape Pub Wit} (Or : sh.Oracle) : sh.Com ≃ (Fin Or.nLeaves → Or.Leaf) where
  toFun := Or.leaf
  invFun := Or.ofLeaves
  left_inv O := Or.leaf_injective (Or.leaf_ofLeaves _)
  right_inv := Or.leaf_ofLeaves

/-! ### The honest prover -/

/-- **An honest forked circuit prover** on inputs of type `In`: an oracle message and commit rounds
from the input and the coins, fixed before the public input; each branch's causal strategy on the
public input and the commit rounds; the join's causal strategy on them and the branches'
transcripts. -/
structure Honest (In : Type) where
  /-- The prover's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The oracle message for the input. -/
  commit : In → Coins → sh.Com
  /-- The commit rounds for the input. -/
  commitRounds : In → Coins → CausalTranscript sh.commitRounds
  /-- Each branch on the public input and the commit rounds. -/
  branch : (b : Fin sh.nb) → Pub → In → Coins → sh.Rounds → CausalTranscript (sh.branch b)
  /-- The join on the public input, the commit rounds and the branches' transcripts. -/
  join : Pub → In → Coins → sh.Rounds → sh.BranchTrs → CausalTranscript sh.join

attribute [instance] Honest.fintype Honest.nonempty

variable {sh}

/-- The honest commit rounds at the commit-round challenges `chc`. -/
abbrev Honest.rounds {In : Type} (Hon : sh.Honest In) (w : In) (ρ : Hon.Coins)
    (chc : sh.commitRounds.Challenges) : sh.Rounds :=
  (Hon.commitRounds w ρ).transcript chc

/-- The honest branches' transcripts at the branches' challenges `chb`. -/
abbrev Honest.trs {In : Type} (Hon : sh.Honest In) (p : Pub) (w : In) (ρ : Hon.Coins) (r : sh.Rounds)
    (chb : (b : Fin sh.nb) → (sh.branch b).Challenges) : sh.BranchTrs :=
  fun b => (Hon.branch b p w ρ r).transcript (chb b)

/-- **The honest forked prover is accepted on the domain `dom`**: at every coin value and every
challenge of the commit rounds, the branches and the join. -/
def Honest.Accepts {In : Type} (Hon : sh.Honest In) (dom : Pub → In → Prop) : Prop :=
  ∀ p w, dom p w → ∀ ρ chc (chb : (b : Fin sh.nb) → (sh.branch b).Challenges) chj,
    sh.V p (Hon.commit w ρ) (Hon.rounds w ρ chc) (Hon.trs p w ρ (Hon.rounds w ρ chc) chb)
      ((Hon.join p w ρ (Hon.rounds w ρ chc) (Hon.trs p w ρ (Hon.rounds w ρ chc) chb)).transcript
        chj) = true

/-- **What a forked circuit's verdict sees**: the oracle message's leaves at the queried positions,
the commit rounds, the branches' transcripts and the join's transcript (read in full). -/
structure Oracle.View (Or : sh.Oracle) where
  /-- The oracle message's leaves at the queried positions, `none` elsewhere. -/
  com : Fin Or.nLeaves → Option Or.Leaf
  /-- The commit rounds. -/
  rounds : sh.Rounds
  /-- The branches' transcripts. -/
  trs : sh.BranchTrs
  /-- The join's transcript. -/
  join : sh.join.Transcript (Fin.last sh.jn)

/-- The oracle message as a message view queried by the join's challenges. -/
def Oracle.comView (Or : sh.Oracle) : MessageView sh.Com sh.join.Challenges (Fin Or.nLeaves) Or.Leaf where
  read := Or.leaf
  read_injective := Or.leaf_injective
  queries := Or.queries

/-- The view at the join's challenges `chj`. -/
def Oracle.view (Or : sh.Oracle) (chj : sh.join.Challenges) (O : sh.Com) (r : sh.Rounds)
    (trs : sh.BranchTrs) (tr : sh.join.Transcript (Fin.last sh.jn)) : Or.View :=
  ⟨Or.comView.see chj O, r, trs, tr⟩

/-- **A simulator of a forked circuit's view**: from the public input, the challenges of the
commit rounds, of the branches and of the join, and its own uniform coins. It reads no honest
input. -/
structure Simulator (Or : sh.Oracle) where
  /-- The simulator's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The simulated view. -/
  sim : Pub → sh.commitRounds.Challenges → ((b : Fin sh.nb) → (sh.branch b).Challenges) →
    sh.join.Challenges → Coins → Or.View

attribute [instance] Simulator.fintype Simulator.nonempty

/-- **Perfect simulation** of the honest forked prover `Hon` by `S` on the domain `dom`: at every
public input and honest input of `dom` and every challenge vector, the honest view under uniform
coins has the law of the simulated view. -/
def Simulator.Perfect {In : Type} {Or : sh.Oracle} (S : Simulator Or) (Hon : sh.Honest In)
    (dom : Pub → In → Prop) : Prop :=
  ∀ p w, dom p w → ∀ chc chb chj,
    (fun ρ => Or.view chj (Hon.commit w ρ) (Hon.rounds w ρ chc)
      (Hon.trs p w ρ (Hon.rounds w ρ chc) chb)
      ((Hon.join p w ρ (Hon.rounds w ρ chc) (Hon.trs p w ρ (Hon.rounds w ρ chc) chb)).transcript
        chj)) =ᵈ S.sim p chc chb chj

end FieldProof.BranchShape

end GordieHowe
