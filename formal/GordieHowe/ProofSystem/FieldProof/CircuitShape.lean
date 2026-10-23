-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.AppendNView
public import GordieHowe.Model.IOP.RBRStable
public import GordieHowe.Model.IOP.CommitPhase

@[expose] public section

/-!
# The computational part of a circuit proof

The completeness and zero-knowledge arguments of a protocol built from circuit proofs read only
the computational part of each circuit proof: the oracle message and the commit rounds of its
commit phase, the witness extracted from them, the proof phase and the verdict
(`GordieHowe.FieldProof.Shape`). Stating them on that part keeps the honest prover, the views and the simulators
of a concrete protocol free of the round errors, so they are computable definitions when their
parts are (an error in `ℝ≥0` computed by a division is a noncomputable term, and any definition
that takes it as an argument is noncomputable).

* `GordieHowe.FieldProof.Shape`: oracle message, commit rounds, extracted witness, proof phase, verdict.
* `GordieHowe.FieldProof.Shape.Sound`: the commit phase's bad events (`BadState`) with their errors, and round
  errors and a claim-proving phase with the circuit's verdict, round-by-round sound relative to
  "the commit phase was bad or the circuit's relation holds on the extracted witness"; it gives
  round-by-round knowledge soundness for that relation (`relation`) at the extractor that reads
  the commit phase (`Sound.rbrKnowledgeSoundness`).
* `GordieHowe.FieldProof.Shape.Honest`, `GordieHowe.FieldProof.Shape.Oracle` (how the verdict reads the oracle message, the
  commit rounds and the messages, `Reading`, with the verdict a function of the view),
  `GordieHowe.FieldProof.Shape.Simulator`, `Simulator.Perfect`.
* `GordieHowe.FieldProof.Shape.pi`: `m` circuits over one transcript, with the family of oracle messages in one
  round, the commit rounds in order and the proof phases in order; its soundness (`Sound.pi`, the
  circuits' errors and bad events), honest prover, oracle and simulator (`Honest.pi`,
  `Oracle.pi`, `Simulator.pi`, `Simulator.Perfect.pi`).
-/

namespace GordieHowe
open IOP

open ProtocolSpec
open scoped NNReal

/-- **The computational part of a circuit proof**: the oracle message and the rounds of the
commit phase, the witness extracted from them (`ext`, part of every extractor built on the
circuit, so an instance must give a computable, polynomial-time definition), the proof phase and
the verdict on the public input, the commit phase and the proof-phase transcript. -/
structure FieldProof.Shape (Pub Wit : Type) where
  /-- The oracle message of the commit phase. -/
  Com : Type
  /-- The number of rounds of the commit phase after the oracle message. -/
  nc : ℕ
  /-- The rounds of the commit phase after the oracle message. -/
  commitRounds : ProtocolSpec nc
  [commitFintype : ∀ i, Fintype (commitRounds.Challenge i)]
  [commitDecEq : ∀ i, DecidableEq (commitRounds.Challenge i)]
  [commitNonempty : ∀ i, Nonempty (commitRounds.Challenge i)]
  /-- The witness extracted from the commit phase. -/
  ext : Com → commitRounds.Transcript (Fin.last nc) → Wit
  /-- The number of rounds of the proof phase. -/
  n : ℕ
  /-- The proof phase. -/
  spec : ProtocolSpec n
  [fintype : ∀ i, Fintype (spec.Challenge i)]
  [decEq : ∀ i, DecidableEq (spec.Challenge i)]
  [nonempty : ∀ i, Nonempty (spec.Challenge i)]
  /-- The verdict on the public input, the commit phase and the proof-phase transcript. -/
  V : Pub → Com → commitRounds.Transcript (Fin.last nc) → spec.Transcript (Fin.last n) → Bool

attribute [instance] FieldProof.Shape.commitFintype FieldProof.Shape.commitDecEq
  FieldProof.Shape.commitNonempty FieldProof.Shape.fintype FieldProof.Shape.decEq FieldProof.Shape.nonempty

variable {Pub Wit : Type} {holds : Pub → Wit → Prop}

namespace FieldProof.Shape

variable (sh : Shape Pub Wit)

/-- The full transcript of the commit rounds. -/
abbrev Rounds : Type := sh.commitRounds.Transcript (Fin.last sh.nc)

/-- An honest circuit prover on inputs of type `In`: an oracle message and commit rounds from the
input and the coins, fixed before the public input, and a causal proof-phase strategy on the
public input and the commit rounds. -/
structure Honest (In : Type) where
  /-- The prover's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The oracle message for the input. -/
  commit : In → Coins → sh.Com
  /-- The commit rounds for the input. -/
  commitRounds : In → Coins → CausalTranscript sh.commitRounds
  /-- The proof phase on the public input and the commit rounds. -/
  prove : Pub → In → Coins → sh.Rounds → CausalTranscript sh.spec

attribute [instance] Honest.fintype Honest.nonempty

variable {sh} in
/-- The honest commit rounds at the commit-round challenges `chc`. -/
abbrev Honest.rounds {In : Type} (Hon : sh.Honest In) (w : In) (ρ : Hon.Coins)
    (chc : sh.commitRounds.Challenges) : sh.Rounds :=
  (Hon.commitRounds w ρ).transcript chc

/-- **How a circuit's verdict reads** its oracle message and its proof-phase messages: each as a
table read at positions fixed by the challenges (`MessageView`); the commit rounds are read in
full. -/
structure Reading where
  /-- Positions of the oracle message. -/
  Idx : Type
  /-- Entries of the oracle message. -/
  Ans : Type
  /-- The oracle message as an oracle, queried by the circuit's challenges. -/
  com : MessageView sh.Com sh.spec.Challenges Idx Ans
  /-- Positions of each proof-phase message. -/
  MIdx : sh.spec.MessageIdx → Type
  /-- Entries of each proof-phase message. -/
  MAns : sh.spec.MessageIdx → Type
  /-- How each proof-phase message is read. -/
  msg : ∀ i : sh.spec.MessageIdx, MessageView (sh.spec.Type i.1) sh.spec.Challenges (MIdx i) (MAns i)

variable {sh}

/-- **What a circuit's verdict sees** (the IOP verifier's view, CY24 Definition 23.1.7, p. 261,
without the statement and the challenges): the oracle message's queried entries, the commit
rounds and the views of the proof-phase messages. -/
structure Reading.View (R : sh.Reading) where
  /-- The oracle message's entries at the queried positions, `none` elsewhere. -/
  com : R.Idx → Option R.Ans
  /-- The commit rounds, read in full. -/
  rounds : sh.Rounds
  /-- Each proof-phase message's entries at its queried positions. -/
  msgs : ∀ i : sh.spec.MessageIdx, R.MIdx i → Option (R.MAns i)

/-- The view of an oracle message, the commit rounds and a proof-phase transcript at the
challenges `ch`. -/
def Reading.view (R : sh.Reading) (ch : sh.spec.Challenges) (O : sh.Com) (r : sh.Rounds)
    (tr : sh.spec.Transcript (Fin.last sh.n)) : R.View :=
  ⟨R.com.see ch O, r, fun i => (R.msg i).see ch (tr i.1)⟩

variable (sh) in
/-- **How a circuit's verdict reads, with query locality**: a `Reading` such that the verdict is
a function of the view: two commit phases and two transcripts with the challenges `ch` and the
same view get the same verdict. -/
structure Oracle extends sh.Reading where
  /-- The verdict depends only on the view. -/
  reads : ∀ p ch (O O' : sh.Com) (r r' : sh.Rounds) (tr tr' : sh.spec.Transcript (Fin.last sh.n)),
    (∀ i : sh.spec.ChallengeIdx, tr i.1 = ch i) → (∀ i : sh.spec.ChallengeIdx, tr' i.1 = ch i) →
    toReading.view ch O r tr = toReading.view ch O' r' tr' → sh.V p O r tr = sh.V p O' r' tr'

/-- Equal views are equal oracle-message views, equal commit rounds and equal message views. -/
theorem Reading.view_eq_iff {R : sh.Reading} {ch : sh.spec.Challenges} {O O' : sh.Com}
    {r r' : sh.Rounds} {tr tr' : sh.spec.Transcript (Fin.last sh.n)} :
    R.view ch O r tr = R.view ch O' r' tr' ↔ R.com.see ch O = R.com.see ch O' ∧ r = r' ∧
      ∀ i, (R.msg i).see ch (tr i.1) = (R.msg i).see ch (tr' i.1) := by
  constructor
  · intro h
    exact ⟨congrArg View.com h, congrArg View.rounds h, fun i => congrFun (congrArg View.msgs h) i⟩
  · rintro ⟨hc, hr, hm⟩
    simp only [view, hc, hr, funext hm]

/-- **A simulator of the circuit's view**: from the public input, the circuit's challenges (of
the commit rounds and of the proof phase) and its own uniform coins, a view of the circuit. It
reads no honest input. -/
structure Simulator (Or : sh.Oracle) where
  /-- The simulator's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The simulated view on the public input, the circuit's challenges and the coins. -/
  sim : Pub → sh.commitRounds.Challenges → sh.spec.Challenges → Coins → Or.View

attribute [instance] Simulator.fintype Simulator.nonempty

/-- **Perfect simulation** of the honest circuit prover `Hon` by `S` on the domain `dom`: for
every public input and honest input in `dom` and every challenge vector of the circuit, the
honest view under uniform coins has the law of the simulated view under uniform simulator
coins. -/
def Simulator.Perfect {In : Type} {Or : sh.Oracle} (S : Simulator Or) (Hon : sh.Honest In)
    (dom : Pub → In → Prop) : Prop :=
  ∀ p w, dom p w → ∀ chc ch,
    (fun ρ => Or.view ch (Hon.commit w ρ) (Hon.rounds w ρ chc)
      ((Hon.prove p w ρ (Hon.rounds w ρ chc)).transcript ch)) =ᵈ S.sim p chc ch

/-! ### Soundness -/

/-- **The statement of a circuit's proof phase**: the public input and the commit phase. -/
structure Statement (Pub Com R : Type) where
  /-- The public input. -/
  pub : Pub
  /-- The oracle message. -/
  com : Com
  /-- The commit rounds. -/
  rounds : R

variable (sh) in
/-- **Soundness of a circuit** relative to `holds`: the commit phase's bad events with their
errors `εc` (`commit`), and round errors and a claim-proving phase on the statement with the
circuit's verdict (`V_eq`), round-by-round sound relative to "the commit phase was bad or `holds`
on the extracted witness" (`claim_imp`). -/
structure Sound (holds : Pub → Wit → Prop) where
  /-- The commit phase's round errors. -/
  εc : sh.commitRounds.ChallengeIdx → ℝ≥0
  /-- The commit phase's bad events. -/
  commit : BadState sh.commitRounds sh.Com εc
  /-- The proof phase's round errors. -/
  ε : sh.spec.ChallengeIdx → ℝ≥0
  /-- Round-by-round soundness relative to the claim. -/
  proof : ClaimProof sh.spec (Statement Pub sh.Com sh.Rounds) ε
  /-- Its verifier is the circuit's verdict. -/
  V_eq : ∀ s tr, proof.V s tr = sh.V s.pub s.com s.rounds tr
  /-- The claim gives a bad commit phase or the relation on the extracted witness. -/
  claim_imp : ∀ s, proof.claim s →
    commit.bad s.com s.rounds ∨ holds s.pub (sh.ext s.com s.rounds)

variable (sh) in
/-- **The verifier of a circuit's proof phase**: the verdict on the statement. -/
def verifier : Verifier sh.spec (Statement Pub sh.Com sh.Rounds) :=
  fun s tr => sh.V s.pub s.com s.rounds tr

variable (sh) in
/-- **The relation a circuit's proof phase proves**: the commit phase was bad (`bad`) or `holds`
at the statement's public input. -/
def relation (holds : Pub → Wit → Prop) (bad : sh.Com → sh.Rounds → Prop) :
    Set (Statement Pub sh.Com sh.Rounds × Wit) :=
  {sw | bad sw.1.com sw.1.rounds ∨ holds sw.1.pub sw.2}

variable (sh) in
/-- **The extractor of a circuit**: the witness extracted from the statement's commit phase
(`ext`); it reads no transcript.

Running time: one call of `ext` (polynomial, by the docstring of `Shape.ext` at the
instance). This running time is argued here, not proved in Lean. -/
def extractor : Extractor sh.spec (Statement Pub sh.Com sh.Rounds) Wit where
  extract _ s _ := sh.ext s.com s.rounds

/-- **The state function of a circuit's proof phase**: that of its claim-proving phase
(`ClaimProof.stateFn`). Not required to be efficient. -/
def Sound.stateFn [Nonempty sh.spec.ChallengeIdx] (S : sh.Sound holds) :
    KnowledgeStateFunction sh.verifier :=
  (S.proof.withV sh.verifier S.V_eq).stateFn

/-- **Round-by-round knowledge soundness of a circuit's proof phase** for "the commit phase was
bad or `holds`" at the statement, at the extractor that reads the commit phase and the state
function `stateFn`, with the round errors `ε`. -/
theorem Sound.rbrKnowledgeSoundness [Nonempty sh.spec.ChallengeIdx] (S : sh.Sound holds) :
    IOP.rbrKnowledgeSoundness (sh.relation holds S.commit.bad) sh.verifier sh.extractor
      S.stateFn S.ε :=
  ClaimProof.rbrKnowledgeSoundness _ _ fun _ s _ h => S.claim_imp s h

/-- The extractor of a circuit is stable: it reads no transcript. -/
theorem extractor_stable {bad : sh.Com → sh.Rounds → Prop} :
    sh.extractor.StableAtChallenges (sh.relation holds bad) :=
  fun _ _ _ h => h

end FieldProof.Shape

/-! ### `m` circuits over one transcript -/

namespace FieldProof.Shape

variable {m : ℕ} {Pub Wit : Fin m → Type}

section Pi

variable (sh : ∀ i, Shape (Pub i) (Wit i))

/-- **`m` circuits over one transcript, as one circuit**: the oracle message is the family of the
circuits' oracle messages, the commit rounds are the circuits' commit rounds in order, the
witness is extracted circuit by circuit; the proof phase runs the circuits' proof phases in
order, each on its own public input and commit phase; the verdict accepts when every circuit's
verdict accepts its part of the transcript. -/
def pi : Shape (∀ i, Pub i) (∀ i, Wit i) where
  Com := ∀ i, (sh i).Com
  nc := lenN m fun i => (sh i).nc
  commitRounds := appendN m fun i => (sh i).commitRounds
  ext O r i := (sh i).ext (O i) (Transcript.part m r i)
  n := lenN m fun i => (sh i).n
  spec := appendN m fun i => (sh i).spec
  V p O r tr := decide (∀ i, (sh i).V (p i) (O i) (Transcript.part m r i)
    (Transcript.part m tr i) = true)

@[simp] theorem pi_ext (O : (pi sh).Com) (r : (pi sh).Rounds) (i : Fin m) :
    (pi sh).ext O r i = (sh i).ext (O i) (Transcript.part m r i) := rfl

/-- The composed verdict accepts exactly when every circuit's verdict accepts its part of the
transcript. -/
theorem pi_V (p : ∀ i, Pub i) (O : (pi sh).Com) (r : (pi sh).Rounds)
    (tr : (pi sh).spec.Transcript (Fin.last (pi sh).n)) :
    (pi sh).V p O r tr = true ↔
      ∀ i, (sh i).V (p i) (O i) (Transcript.part m r i) (Transcript.part m tr i) = true :=
  decide_eq_true_iff

end Pi

variable {sh : ∀ i, Shape (Pub i) (Wit i)} {In : Fin m → Type}

section PiSound

variable {holds : ∀ i, Pub i → Wit i → Prop}

/-- Circuit `i`'s statement in a statement of the composed circuit. -/
def Statement.part (s : Statement (∀ i, Pub i) (Shape.pi sh).Com (Shape.pi sh).Rounds)
    (i : Fin m) : Statement (Pub i) (sh i).Com (sh i).Rounds :=
  ⟨s.pub i, s.com i, Transcript.part m s.rounds i⟩

/-- **Soundness of `m` circuits over one transcript**: the circuits' bad events in sequence
(`BadState.orN`: the commit phase is bad when some circuit's is), and the circuits'
claim-proving phases in sequence (`ClaimProof.andN`), each on its own statement, proving the
conjunction of the circuits' claims; every challenge round keeps the error of its circuit
(`errN`). -/
def Sound.pi (S : ∀ i, (sh i).Sound (holds i)) :
    (Shape.pi sh).Sound (AllHold holds) where
  εc := ProtocolSpec.errN m fun i => (S i).εc
  commit := BadState.orN m fun i => (S i).commit.comap fun O => O i
  ε := ProtocolSpec.errN m fun i => (S i).ε
  proof := ClaimProof.andN m fun i => (S i).proof.comap fun s => s.part i
  V_eq s tr := by
    refine Bool.eq_iff_iff.mpr ((ClaimProof.andN_V m _ s tr).trans ?_)
    refine Iff.trans ?_ (pi_V sh s.pub s.com s.rounds tr).symm
    exact forall_congr' fun i => by rw [ClaimProof.comap_V, (S i).V_eq]; rfl
  claim_imp s h := by
    classical
    by_cases hall : AllHold holds s.pub ((Shape.pi sh).ext s.com s.rounds)
    · exact .inr hall
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      refine .inl (BadState.bad_orN_of m _ s.com s.rounds i ?_)
      exact ((S i).claim_imp (s.part i) ((ClaimProof.andN_claim m _ s).mp h i)).resolve_right hi

end PiSound

/-- **The honest circuit provers in sequence**: independent coins for every circuit; each
commits to its input with its coins, runs its commit rounds, and runs its proof phase on its own
public input and commit rounds. -/
def Honest.pi (Hon : ∀ i, (sh i).Honest (In i)) : (Shape.pi sh).Honest (∀ i, In i) where
  Coins := ∀ i, (Hon i).Coins
  commit w ρ i := (Hon i).commit (w i) (ρ i)
  commitRounds w ρ := CausalTranscript.appendN m fun i => (Hon i).commitRounds (w i) (ρ i)
  prove p w ρ r := CausalTranscript.appendN m fun i =>
    (Hon i).prove (p i) (w i) (ρ i) (Transcript.part m r i)

/-- The honest commit rounds in sequence join the circuits' honest commit rounds, each at its own
challenges. -/
theorem Honest.part_pi_rounds (Hon : ∀ i, (sh i).Honest (In i)) (w : ∀ i, In i)
    (ρ : (Honest.pi Hon).Coins) (chc : (Shape.pi sh).commitRounds.Challenges) (i : Fin m) :
    Transcript.part m ((Honest.pi Hon).rounds w ρ chc) i = (Hon i).rounds (w i) (ρ i) (chN m chc i) := by
  have e := congrArg (fun tr => Transcript.part m tr i)
    (CausalTranscript.appendN_transcript m (fun i => (Hon i).commitRounds (w i) (ρ i)) chc)
  simp only [part_joinN] at e
  exact e

/-- The honest proof phases in sequence join the circuits' honest proofs, each on its part of the
commit rounds and at its own challenges. -/
theorem Honest.part_pi_prove (Hon : ∀ i, (sh i).Honest (In i)) (p : ∀ i, Pub i) (w : ∀ i, In i)
    (ρ : (Honest.pi Hon).Coins) (r : (Shape.pi sh).Rounds)
    (ch : (Shape.pi sh).spec.Challenges) (i : Fin m) :
    Transcript.part m (((Honest.pi Hon).prove p w ρ r).transcript ch) i =
      ((Hon i).prove (p i) (w i) (ρ i) (Transcript.part m r i)).transcript (chN m ch i) := by
  have e := congrArg (fun tr => Transcript.part m tr i)
    (CausalTranscript.appendN_transcript m
      (fun i => (Hon i).prove (p i) (w i) (ρ i) (Transcript.part m r i)) ch)
  simp only [part_joinN] at e
  exact e

/-- On the honest runs, the composed verdict accepts exactly when every circuit's verdict accepts
its honest run at its own challenges. -/
theorem pi_V_honest (Hon : ∀ i, (sh i).Honest (In i)) (p : ∀ i, Pub i) (w : ∀ i, In i)
    (ρ : (Honest.pi Hon).Coins) (chc : (Shape.pi sh).commitRounds.Challenges)
    (ch : (Shape.pi sh).spec.Challenges) :
    (Shape.pi sh).V p ((Honest.pi Hon).commit w ρ) ((Honest.pi Hon).rounds w ρ chc)
        (((Honest.pi Hon).prove p w ρ ((Honest.pi Hon).rounds w ρ chc)).transcript ch) = true ↔
      ∀ i, (sh i).V (p i) ((Hon i).commit (w i) (ρ i)) ((Hon i).rounds (w i) (ρ i) (chN m chc i))
        (((Hon i).prove (p i) (w i) (ρ i) ((Hon i).rounds (w i) (ρ i) (chN m chc i))).transcript
          (chN m ch i)) = true := by
  rw [pi_V]
  refine forall_congr' fun i => ?_
  rw [Honest.part_pi_prove, Honest.part_pi_rounds]
  rfl

/-- **How the composed circuit's verdict reads**: the oracle messages as one table
(`MessageView.pi`, positions `CircuitPos`) at the circuits' oracle positions, the commit rounds
in full, and the proof-phase messages as the circuits read them (`msgN`); each circuit at its own
challenges (`chN`). -/
def Oracle.pi (Or : ∀ i, (sh i).Oracle) : (Shape.pi sh).Oracle where
  Idx := CircuitPos fun i => (Or i).Idx
  Ans := CircuitEntry fun i => (Or i).Ans
  com := MessageView.pi fun i => (Or i).com.comap fun ch => chN m ch i
  MIdx := famN m fun i => (Or i).MIdx
  MAns := famN m fun i => (Or i).MAns
  msg := msgN m fun i j => ((Or i).msg j).comap fun ch => chN m ch i
  reads p ch O O' r r' tr tr' htr htr' hview := by
    obtain ⟨hcom, hr, hmsg⟩ := Reading.view_eq_iff.mp hview
    subst hr
    have hv := (viewEquivN_see_part _ ch tr).symm.trans
      ((congrArg (viewEquivN m) (funext hmsg)).trans (viewEquivN_see_part _ ch tr'))
    have hc := (MessageView.see_pi_eq_iff _ ch O O').1 hcom
    have key : ∀ i, (sh i).V (p i) (O i) (Transcript.part m r i) (Transcript.part m tr i) =
        (sh i).V (p i) (O' i) (Transcript.part m r i) (Transcript.part m tr' i) :=
      fun i => (Or i).reads (p i) (chN m ch i) (O i) (O' i) _ _ _ _ (part_challenge m htr i)
        (part_challenge m htr' i)
        (Reading.view_eq_iff.mpr ⟨hc i, rfl, fun j => congrFun (congrFun hv i) j⟩)
    refine Bool.eq_iff_iff.mpr ((pi_V sh p O r tr).trans
      (Iff.trans ?_ (pi_V sh p O' r tr').symm))
    exact forall_congr' fun i => by rw [key i]

/-- The composed circuit's view from the circuits' views. -/
def Oracle.piView (Or : ∀ i, (sh i).Oracle) (v : ∀ i, (Or i).View) : (Oracle.pi Or).View :=
  ⟨fun x => ((v x.circuit).com x.pos).map (CircuitEntry.mk x.circuit),
    joinN m fun i => (v i).rounds, (viewEquivN m).symm fun i => (v i).msgs⟩

/-- **The composed view is the family of the circuits' views**, each at its own challenges, of
its own oracle message and its parts of the commit rounds and of the transcript. -/
theorem Oracle.view_pi (Or : ∀ i, (sh i).Oracle) (ch : (Shape.pi sh).spec.Challenges)
    (O : (Shape.pi sh).Com) (r : (Shape.pi sh).Rounds)
    (tr : (Shape.pi sh).spec.Transcript (Fin.last (Shape.pi sh).n)) :
    (Oracle.pi Or).view ch O r tr =
      Oracle.piView Or fun i => (Or i).view (chN m ch i) (O i) (Transcript.part m r i)
        (Transcript.part m tr i) := by
  change (⟨_, _, _⟩ : (Oracle.pi Or).View) = ⟨_, _, _⟩
  congr 1
  · exact funext fun x => MessageView.see_pi _ ch O x
  · exact (joinN_part m r).symm
  · exact (Equiv.eq_symm_apply _).mpr (viewEquivN_see_part _ ch tr)

/-- **The simulator of the composed circuit**: each circuit's simulator on its own public input,
its own challenges and its own coins; the views are assembled by `Oracle.piView`.

Running time: one call of each circuit's simulator; the challenge vectors are split and the view
entries are copied, linear in their sizes. This running time is argued here, not proved in Lean. -/
def Simulator.pi {Or : ∀ i, (sh i).Oracle} (S : ∀ i, Simulator (Or i)) :
    Simulator (Oracle.pi Or) where
  Coins := ∀ i, (S i).Coins
  sim p chc ch ρ := Oracle.piView Or fun i => (S i).sim (p i) (chN m chc i) (chN m ch i) (ρ i)

/-- **Zero-knowledge of the composed circuit**: perfect simulators of the circuits on domains
`dom i` give a perfect simulator of the composed circuit on the inputs that lie in every
circuit's domain. The circuits' coins are independent (`IdentDistrib.pi`). -/
theorem Simulator.Perfect.pi {Or : ∀ i, (sh i).Oracle} {Hon : ∀ i, (sh i).Honest (In i)}
    {dom : ∀ i, Pub i → In i → Prop} {S : ∀ i, Simulator (Or i)}
    (hS : ∀ i, (S i).Perfect (Hon i) (dom i)) :
    (Simulator.pi S).Perfect (Honest.pi Hon) fun p w => ∀ i, dom i (p i) (w i) := by
  intro p w hw chc ch
  refine IdentDistrib.trans (IdentDistrib.of_equiv (Equiv.refl _) fun ρ => ?_)
    ((IdentDistrib.pi fun i => hS i (p i) (w i) (hw i) (chN m chc i) (chN m ch i)).comp
      (Oracle.piView Or))
  rw [Oracle.view_pi]
  change _ = Oracle.piView Or fun i => (Or i).view (chN m ch i) ((Hon i).commit (w i) (ρ i))
    ((Hon i).rounds (w i) (ρ i) (chN m chc i))
    (((Hon i).prove (p i) (w i) (ρ i) ((Hon i).rounds (w i) (ρ i) (chN m chc i))).transcript
      (chN m ch i))
  congr 2
  funext i
  rw [Honest.part_pi_prove, Honest.part_pi_rounds]
  rfl

end FieldProof.Shape

end GordieHowe
