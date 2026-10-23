-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.ProofSystem.FieldProof.Basic
public import GordieHowe.Model.IOP.AppendNView
public import GordieHowe.Headline

@[expose] public section

/-!
# Multi-circuit IOPs and their soundness

A **multi-circuit IOP** (`MultiCircuitIOP`) proves a relation `rel` with `m` circuit proofs
(`GordieHowe.FieldProof`: a masked row reduction and a commit-and-prove system each) and an application phase
(`GordieHowe.RealizedProgram.ProofSystem.PhaseStep`):

| part | rounds |
|---|---|
| commitment | the family of the circuits' oracle messages, one round (`commitSpec`) |
| commit rounds | the `m` circuits' commit rounds in order (none for a one-message commitment) |
| application phase | `app.spec` |
| circuit proofs | the `m` circuits' proof phases in order (`GordieHowe.FieldProof.Shape.pi`, `appendN`) |

Each circuit proof runs on the public input the application phase fixes (`app.pub i`) and its own
commit phase. Longfellow's protocol is the instance with two circuits (H and A) and the
proof-of-possession phase; the ML-DSA ring is another.

The protocol, the verifier, the extractor, the honest prover, the view and the simulator are
defined on the computational parts of the circuits (`GordieHowe.FieldProof.Shape`, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullVerifier` and
the definitions after it), so that none of them reads a round error; soundness reads the
circuits' soundness (`GordieHowe.FieldProof.Shape.Sound`, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.rbrKnowledgeSoundness_full`). For a
`MultiCircuitIOP` the errors are in `MultiCircuitIOP.Sound`, and the protocol, the extractor,
the honest prover and the simulator read `MultiCircuitIOP` only.

**The state function** (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullStateFn`): during the commit phase, the circuits' commit
bad events (`BadState`); during the application phase, a bad commit phase or the phase's state
(`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.committedState`); afterwards, a bad commit phase, or, once the protocol has drawn a
challenge (of the application phase, or of the circuit proofs when the phase has none,
`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.drawn`), the phase's condition (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.cond`) or the circuit proofs' state. So an
application phase with no challenge round of its own needs no extra round: its condition switches
on at the first challenge of the circuit proofs, where a flip of the state is a flip of the
circuit proofs' state (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.rbrKnowledgeSoundness_full`). The commit events enter the round
errors at the commit rounds.

**Soundness**: `MultiCircuitIOP.rbr_knowledge_soundness` (round-by-round knowledge soundness at the
named extractor and state function, with the commit rounds' errors, the application phase's errors
and every circuit proof's errors). The extractor reads the cells from the commit phases with the
commit-and-prove systems' `extract`, reads every circuit's witness with its `readout`, and applies
the application phase's `extract` (`extractor_of_le`); it reads no challenge after the commit phase,
so it is stable after the commit rounds (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullExtractor_of_le`).
`MultiCircuitIOP.completeness` and `MultiCircuitIOP.hvzk` (named simulator, exception event the
application phase's completeness events) complete it.
-/

namespace GordieHowe
open IOP

open ProtocolSpec
open scoped NNReal

variable {Stmt W : Type} {rel : Set (Stmt × W)} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop}

namespace RealizedProgram.ProofSystem.PhaseStep

variable (A : PhaseStep Stmt W rel Pub Wit holds) (sh : ∀ i, FieldProof.Shape (Pub i) (Wit i))

/-! ### The protocol -/

/-- The protocol: the commit phase (the commitment round, then the circuits' commit rounds), the
application phase, the circuits' proof phases. -/
abbrev fullSpec :
    ProtocolSpec (1 + ((FieldProof.Shape.pi sh).nc + A.n) + (FieldProof.Shape.pi sh).n) :=
  A.committedSpec (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds ++
    (FieldProof.Shape.pi sh).spec

/-- The prefix lengths of the protocol. -/
abbrev FullIdx : Type := Fin (1 + ((FieldProof.Shape.pi sh).nc + A.n) + (FieldProof.Shape.pi sh).n + 1)

/-- **The commit phase is in the prefix** of length `k`: the commitment round and the circuits'
commit rounds. -/
abbrev AfterCommit (k : A.FullIdx sh) : Prop := 1 + (FieldProof.Shape.pi sh).nc ≤ (k : ℕ)

/-- The context after the commit phase and the application phase. -/
abbrev Context : Type := A.CommittedContext (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds

/-- **The circuits' statement after the application phase**: every circuit's public input, the
committed family and the circuits' commit rounds. -/
def circuitsStatement (c : A.Context sh) :
    FieldProof.Shape.Statement (∀ i, Pub i) (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).Rounds :=
  ⟨fun i => A.pub i c.stmt c.app, c.com, c.rounds⟩

/-- The verifier's check after the application phase. -/
def circuitsOk (c : A.Context sh) : Bool := A.ok c.stmt c.app

/-- **The verdict after the application phase**: the verifier's check, then every circuit's
verdict on its public input and commit phase. -/
def circuitsV (c : A.Context sh)
    (tr : (FieldProof.Shape.pi sh).spec.Transcript (Fin.last (FieldProof.Shape.pi sh).n)) : Bool :=
  A.circuitsOk sh c && (FieldProof.Shape.pi sh).verifier (A.circuitsStatement sh c) tr

/-- **The verifier**: the application phase's check and every circuit's verdict on the context
the application phase fixes. -/
def fullVerifier : Verifier (A.fullSpec sh) Stmt :=
  fun x tr => A.circuitsV sh ⟨x, tr.left⟩ tr.right

section Soundness

variable [Inhabited W]

/-- **The extractor**: the application phase's extractor (read the circuits' witnesses from the
commit phase with the circuits' `ext`, then `extract`) on the commit phase and application part of
the transcript.

Running time: one call of every circuit's `ext` and one of `extract` (`PhaseStep.extractor`);
reading the prefix copies at most `1 + (nc + A.n)` messages.
This running time is argued here, not proved in Lean. -/
def fullExtractor : Extractor (A.fullSpec sh) Stmt W :=
  (A.extractor (FieldProof.Shape.pi sh).ext).appendLeft

/-- The commitment in a transcript that contains the commit phase. -/
def fullCom {k : A.FullIdx sh} (tr : (A.fullSpec sh).Transcript k) (h : A.AfterCommit sh k) :
    (FieldProof.Shape.pi sh).Com :=
  comOf (tr.fst ⟨1 + (FieldProof.Shape.pi sh).nc, by omega⟩ h) (by simp)

/-- The circuits' commit rounds in a transcript that contains the commit phase. -/
def fullRounds {k : A.FullIdx sh} (tr : (A.fullSpec sh).Transcript k) (h : A.AfterCommit sh k) :
    (FieldProof.Shape.pi sh).Rounds :=
  roundsOf (tr.fst ⟨1 + (FieldProof.Shape.pi sh).nc, by omega⟩ h) le_rfl

/-- Once the commit phase is in the prefix, the extractor is `witnessOf` of the witnesses read
from it. -/
theorem fullExtractor_of_le {k : A.FullIdx sh} (x : Stmt) (tr : (A.fullSpec sh).Transcript k)
    (h : A.AfterCommit sh k) :
    A.fullExtractor sh k x tr =
      A.witnessOf ((FieldProof.Shape.pi sh).ext (A.fullCom sh tr h) (A.fullRounds sh tr h)) := by
  unfold fullExtractor
  by_cases hk : (k : ℕ) ≤ 1 + ((FieldProof.Shape.pi sh).nc + A.n)
  · rw [Extractor.appendLeft_of_le _ x tr hk]
    exact extractor_of_le _ x _ h
  · rw [show (A.extractor (FieldProof.Shape.pi sh).ext).appendLeft k x tr =
      (A.extractor (FieldProof.Shape.pi sh).ext) (Fin.last _) x
        (tr.fst (Fin.last _) (by simp only [Fin.val_last]; omega)) from dite_eq_right hk]
    exact extractor_of_le _ x _ (by simp only [Fin.val_last]; omega)

/-- **The commit rounds of the protocol**: its challenge rounds before the end of the commit
phase. -/
abbrev CommitRound (i : (A.fullSpec sh).ChallengeIdx) : Prop :=
  (i.1 : ℕ) < 1 + (FieldProof.Shape.pi sh).nc

/-! ### Soundness, from the circuits' soundness -/

variable {sh} (S : ∀ i, (sh i).Sound (holds i))

/-- **The circuits' proofs after the application phase**: the verifier's check, then every
circuit's proof on its public input and commit phase (`FieldProof.Shape.Sound.pi`), with the verdict
`circuitsV`. -/
def circuitsProof : ClaimProof (FieldProof.Shape.pi sh).spec (A.Context sh) (FieldProof.Shape.Sound.pi S).ε :=
  (((FieldProof.Shape.Sound.pi S).proof.comap (A.circuitsStatement sh)).guard
    (A.circuitsOk sh)).withV (A.circuitsV sh) fun c tr =>
      congrArg (A.circuitsOk sh c && ·) ((FieldProof.Shape.Sound.pi S).V_eq _ tr)

omit [Inhabited W] in
/-- The circuits prove the application phase's claim, or the commit phase was bad. -/
theorem circuitsProof_claim_imp {c : A.Context sh} (h : (A.circuitsProof S).claim c) :
    c.Bad (FieldProof.Shape.Sound.pi S).commit ∨ A.committedClaim (FieldProof.Shape.pi sh).ext c := by
  obtain ⟨hok, hc⟩ := h
  exact ((FieldProof.Shape.Sound.pi S).claim_imp _ hc).imp
    ((FieldProof.Shape.Sound.pi S).commit.full _ _) fun hall => ⟨hok, hall⟩

variable (sh) in
/-- **A challenge has been drawn** at the prefix of length `k` of the circuits' proof phases: the
application phase has a challenge round (all of them are before the circuits), or a challenge
round of the circuits precedes `k`. -/
def drawn (k : Fin ((FieldProof.Shape.pi sh).n + 1)) : Prop :=
  Nonempty A.spec.ChallengeIdx ∨ ChallengeDrawn (FieldProof.Shape.pi sh).spec k

variable (sh) in
/-- **The protocol has a challenge round**, in the application phase or in the circuits. -/
def HasChallenge : Prop :=
  Nonempty A.spec.ChallengeIdx ∨ Nonempty (FieldProof.Shape.pi sh).spec.ChallengeIdx

/-- **The state of the protocol**: during the commit phase and the application phase, the
commit phase's bad state, then the commit phase was bad or the phase's state; afterwards, the
commit phase was bad, or a challenge has been drawn and the phase's condition or the circuits'
state holds. Not required to be efficient. -/
def fullState (k : A.FullIdx sh) (x : Stmt) (tr : (A.fullSpec sh).Transcript k) : Prop :=
  appendState (fun k => A.committedState (FieldProof.Shape.pi sh).ext (FieldProof.Shape.Sound.pi S).commit k x)
    (fun trF k₂ trH => (⟨x, trF⟩ : A.Context sh).Bad (FieldProof.Shape.Sound.pi S).commit ∨
      (A.drawn sh k₂ ∧ (A.committedCond (FieldProof.Shape.pi sh).ext ⟨x, trF⟩ ∨
        (A.circuitsProof S).S k₂ ⟨x, trF⟩ trH)))
    k tr

/-- The state of the circuits' part at its start gives the state after the application phase:
the circuits' state there gives their claim, hence a bad commit phase or the phase's condition. -/
theorem fullState_zero_le (x : Stmt)
    (trF : (A.committedSpec (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds).Transcript
      (Fin.last (1 + ((FieldProof.Shape.pi sh).nc + A.n))))
    (trH : (FieldProof.Shape.pi sh).spec.Transcript 0)
    (h : (⟨x, trF⟩ : A.Context sh).Bad (FieldProof.Shape.Sound.pi S).commit ∨
      (A.drawn sh 0 ∧ (A.committedCond (FieldProof.Shape.pi sh).ext ⟨x, trF⟩ ∨
        (A.circuitsProof S).S 0 ⟨x, trF⟩ trH))) :
    A.committedState (FieldProof.Shape.pi sh).ext (FieldProof.Shape.Sound.pi S).commit (Fin.last _) x
      trF := by
  refine (A.committedState_last_iff _ _ ⟨x, trF⟩).mpr ?_
  rcases h with hb | ⟨hd, hc⟩
  · exact .inl hb
  have hne : Nonempty A.spec.ChallengeIdx := hd.resolve_right fun ⟨j, hj⟩ => by
    rw [Fin.le_def] at hj
    simp at hj
  rcases hc with hc | hS
  · exact .inr ⟨hne, hc⟩
  · exact (A.circuitsProof_claim_imp S ((A.circuitsProof S).claim_of_S hS)).imp id
      fun hcl => ⟨hne, A.committedCond_of_claim _ hcl⟩

/-- **The state function** of the protocol (`fullState`), when the protocol has a challenge
round. Not required to be efficient. -/
def fullStateFn (hch : A.HasChallenge sh) : KnowledgeStateFunction (A.fullVerifier sh) where
  toFun k x tr := A.fullState S k x tr
  toFun_empty x tr h := by
    unfold fullState at h
    rw [appendState_iff_of_lt (k₁ := 0) rfl (by simp)] at h
    exact A.committedState_zero _ _ x _ h
  toFun_next k hdir x tr msg hnot := by
    induction k using Fin.addCases with
    | left j =>
      intro h
      unfold fullState at hnot h
      have hflip := appendState_flip_castAdd (A.fullState_zero_le S x) j tr msg hnot h
      exact A.committedState_next _ _ j (by simpa using hdir) x _ _ hflip.1 hflip.2
    | right j =>
      intro h
      unfold fullState at hnot h
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, h⟩
      obtain ⟨hd, hs⟩ := hs.resolve_left fun hb => hn (.inl hb)
      have hdir' : (FieldProof.Shape.pi sh).spec.dir j = .P_to_V := by
        simpa using hdir
      have hd' : A.drawn sh j.castSucc := hd.imp id (challengeDrawn_succ_of_message hdir')
      rcases hs with hc | hS
      · exact hn (.inr ⟨hd', .inl hc⟩)
      · refine hn (.inr ⟨hd', .inr ?_⟩)
        by_contra hS'
        exact (A.circuitsProof S).next j hdir' _ _ _ hS' hS
  toFun_full x tr h := by
    unfold fullState
    rw [appendState_iff_of_eq_add (k₂ := Fin.last _) (by simp)]
    exact .inr ⟨hch.imp id fun ⟨j⟩ => ⟨j, Fin.le_last _⟩,
      .inr ((A.circuitsProof S).full ⟨x, tr.left⟩ tr.right h)⟩

/-- **The round errors**: the circuits' commit rounds' errors, the application phase's errors
`ε`, then every circuit's. -/
def fullError (ε : A.spec.ChallengeIdx → ℝ≥0) : (A.fullSpec sh).ChallengeIdx → ℝ≥0 :=
  appendError (A.committedError (FieldProof.Shape.pi sh).commitRounds (FieldProof.Shape.Sound.pi S).εc ε)
    (FieldProof.Shape.Sound.pi S).ε

open Classical in
/-- **The state flips at a challenge round before the circuits' proof phases** only on that
round's event: at a commit round whatever the extractor returns, at a round of the application
phase while the extractor fails (`committedState_flip_card`). -/
theorem fullState_flip_card_inl {ε : A.spec.ChallengeIdx → ℝ≥0} (hε : A.EventBound ε) (x : Stmt)
    (j : (A.committedSpec (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds).ChallengeIdx)
    (tr : (A.fullSpec sh).Transcript (ChallengeIdx.inl (P₂ := (FieldProof.Shape.pi sh).spec) j).1.castSucc) :
    ((Finset.univ.filter fun c : (A.fullSpec sh).Challenge (ChallengeIdx.inl j) =>
        (A.CommitRound sh (ChallengeIdx.inl j) ∨
          (x, A.fullExtractor sh (ChallengeIdx.inl j).1.castSucc x tr) ∉ rel) ∧
        ¬ A.fullState S _ x tr ∧ A.fullState S _ x ((A.fullSpec sh).concat tr c)).card : ℝ≥0) ≤
      A.fullError S ε (ChallengeIdx.inl j) *
        Fintype.card ((A.fullSpec sh).Challenge (ChallengeIdx.inl j)) := by
  rw [fullError, appendError_inl]
  refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun c hc => ?_)
    (A.committedState_flip_card (FieldProof.Shape.pi sh).ext (FieldProof.Shape.Sound.pi S).commit hε x j
      (tr.fst j.1.castSucc (by simp)))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨hE, hnot, hpost⟩ := hc
  unfold fullState at hnot hpost
  have hflip := appendState_flip_castAdd (A.fullState_zero_le S x) j.1 tr c hnot hpost
  refine ⟨hE.imp (fun h => ?_) fun h => ?_, hflip.1, hflip.2⟩
  · simpa using h
  · have hle : ((ChallengeIdx.inl (P₂ := (FieldProof.Shape.pi sh).spec) j).1.castSucc : ℕ) ≤
        1 + ((FieldProof.Shape.pi sh).nc + A.n) := by simp
    unfold fullExtractor at h
    rwa [Extractor.appendLeft_of_le _ x tr hle] at h

open Classical in
/-- **Round-by-round knowledge soundness over circuits**, at `fullExtractor` and `fullStateFn`,
with the circuits' commit-phase errors, the application phase's errors `ε` (`hε`) and every
circuit's own errors. At a commit round the state flips only on that round's bad event; at a
challenge of the application phase only on that round's event; at a challenge of the circuits
only when the circuits' state flips, including at the first challenge of the circuits when the
application phase has none: there a true circuits' state gives the circuits' claim, hence a bad
commit phase or the phase's condition, which without events is the extracted witness in the
relation. -/
theorem rbrKnowledgeSoundness_full {ε : A.spec.ChallengeIdx → ℝ≥0} (hε : A.EventBound ε)
    (hch : A.HasChallenge sh) :
    rbrKnowledgeSoundness rel (A.fullVerifier sh) (A.fullExtractor sh) (A.fullStateFn S hch)
      (A.fullError S ε) := by
  refine rbrKnowledgeSoundness_iff_count.mpr ?_
  intro x i tr
  rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun c hc => ?_))
      (A.fullState_flip_card_inl S hε x j tr)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨.inr hc.1, hc.2⟩
  · rw [fullError, appendError_inr]
    refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun c hc => ?_)
      ((A.circuitsProof S).rbr ⟨x, tr.fst (Fin.last _) (by simp)⟩ j
        (tr.snd j.1.castSucc (by simp)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    change (x, _) ∉ rel ∧ ¬ A.fullState S _ x tr ∧ A.fullState S _ x _ at hc
    unfold fullState at hc
    obtain ⟨hE, hflip⟩ := hc
    obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 tr c).mp hflip
    have hnb := fun hb => hn (.inl hb)
    obtain ⟨-, hs⟩ := hs.resolve_left hnb
    rw [A.fullExtractor_of_le _ x tr (by simp; omega)] at hE
    have hE' : (x, A.witnessOf ((FieldProof.Shape.pi sh).ext
        (⟨x, tr.fst (Fin.last _) (by simp)⟩ : A.Context sh).com
        (⟨x, tr.fst (Fin.last _) (by simp)⟩ : A.Context sh).rounds)) ∉ rel := hE
    have hpost : (A.circuitsProof S).S j.1.succ ⟨x, tr.fst (Fin.last _) (by simp)⟩
        (((FieldProof.Shape.pi sh).spec).concat (tr.snd j.1.castSucc (by simp))
          (cast (append_Challenge_inr j) c)) :=
      hs.resolve_left fun hc => hn (.inr ⟨.inl (A.nonempty_of_cond hE' hc), .inl hc⟩)
    refine ⟨fun hpre => ?_, hpost⟩
    by_cases hdpre : A.drawn sh j.1.castSucc
    · exact hn (.inr ⟨hdpre, .inr hpre⟩)
    · have hnapp : ¬ Nonempty A.spec.ChallengeIdx := fun h => hdpre (.inl h)
      have hclaim := (A.circuitsProof S).claim_of_S_before
        (le_of_not_challengeDrawn fun h => hdpre (.inr h)) hpre
      rcases A.circuitsProof_claim_imp S hclaim with hb | hcl
      · exact hnb hb
      · exact hnapp (A.nonempty_of_cond hE' (A.committedCond_of_claim _ hcl))

end Soundness

/-! ### The honest prover and completeness -/

section Honest

variable {I : Type} {relI : Set (Stmt × I)} {In : Fin m → Type} {dom : ∀ i, Pub i → In i → Prop}
  {SA : A.Sim} (Ah : A.Honest I relI In dom SA) {sh} (Hon : ∀ i, (sh i).Honest (In i))

/-- **The honest prover's coins**: the application phase's pads and every circuit's coins. -/
structure Coins where
  /-- The application phase's pads. -/
  pads : Ah.Pads
  /-- Every circuit's coins. -/
  circuits : (FieldProof.Shape.Honest.pi Hon).Coins

/-- The coins as a pair. -/
def coinsEquiv : A.Coins Ah Hon ≃ Ah.Pads × (FieldProof.Shape.Honest.pi Hon).Coins where
  toFun c := (c.pads, c.circuits)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (A.Coins Ah Hon) := Fintype.ofEquiv _ (A.coinsEquiv Ah Hon).symm
instance : Nonempty (A.Coins Ah Hon) := (A.coinsEquiv Ah Hon).nonempty

/-- The honest commitment round: the commitment `O`. -/
def commitFamily {Com : Type} (O : Com) : CausalTranscript (commitSpec Com) :=
  CausalTranscript.oneMessage O

/-- The honest transcript of the commit phase and the application phase: the commitment to the
circuits' honest inputs, the circuits' honest commit rounds, the application phase's honest
prover. -/
def committedFamily (y : I) (c : A.Coins Ah Hon) (x : Stmt) :
    CausalTranscript (A.committedSpec (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds) :=
  (commitFamily ((FieldProof.Shape.Honest.pi Hon).commit (fun i => Ah.wit i y c.pads) c.circuits)).append
    fun _ => ((FieldProof.Shape.Honest.pi Hon).commitRounds (fun i => Ah.wit i y c.pads) c.circuits).append
      fun _ => Ah.prover x y c.pads

/-- **The honest transcript family** at the honest input `y` and the coins `c`: the honest commit
phase and application phase, then every circuit's honest proof on the public input the
application transcript fixes and its commit rounds. -/
def fullFamily (y : I) (c : A.Coins Ah Hon) (x : Stmt) : CausalTranscript (A.fullSpec sh) :=
  (A.committedFamily Ah Hon y c x).append fun trF =>
    (FieldProof.Shape.Honest.pi Hon).prove (A.circuitsStatement sh ⟨x, trF⟩).pub
      (fun i => Ah.wit i y c.pads) c.circuits (A.circuitsStatement sh ⟨x, trF⟩).rounds

/-- **The honest prover** at the honest input `y` and the coins `c`, running `fullFamily`
(`CausalTranscript.realize`: the strategy reads no future challenge). -/
noncomputable def fullHonest (y : I) (c : A.Coins Ah Hon) : Prover (A.fullSpec sh) Stmt :=
  CausalTranscript.realize (A.fullFamily Ah Hon y c)

variable (sh) in
/-- The application part of the protocol's challenges. -/
def appChallenge (ch : (A.fullSpec sh).Challenges) : A.spec.Challenges := ch.left.right.right

/-- **The protocol's challenge of round `j` of the application phase** has the phase's type. -/
theorem appChallenge_type (j : A.spec.ChallengeIdx) :
    (A.fullSpec sh).Challenge (ChallengeIdx.inl (ChallengeIdx.inr (ChallengeIdx.inr j))) =
      A.spec.Challenge j :=
  (append_Challenge_inl _).trans ((append_Challenge_inr _).trans (append_Challenge_inr j))

variable (sh) in
/-- **Updating the protocol's challenge of round `j` of the application phase** updates the
application part of the challenges at `j`. -/
theorem appChallenge_update (ch : (A.fullSpec sh).Challenges) (j : A.spec.ChallengeIdx)
    (c : (A.fullSpec sh).Challenge (ChallengeIdx.inl (ChallengeIdx.inr (ChallengeIdx.inr j)))) :
    A.appChallenge sh
        (Function.update ch (ChallengeIdx.inl (ChallengeIdx.inr (ChallengeIdx.inr j))) c) =
      Function.update (A.appChallenge sh ch) j (cast (A.appChallenge_type j) c) := by
  simp only [appChallenge, Challenges.left_update_inl, Challenges.right_update_inr, cast_cast]

variable (sh) in
/-- The circuits' commit-round part of the protocol's challenges. -/
def commitChallenge (ch : (A.fullSpec sh).Challenges) :
    (FieldProof.Shape.pi sh).commitRounds.Challenges :=
  ch.left.right.left

/-- The application phase's honest transcript at the protocol's challenges. -/
abbrev honestAppTranscript (y : I) (π : Ah.Pads) (x : Stmt) (ch : (A.fullSpec sh).Challenges) :
    A.spec.Transcript (Fin.last A.n) :=
  (Ah.prover x y π).transcript (A.appChallenge sh ch)

/-- Circuit `i`'s honest commit rounds at the protocol's challenges. -/
abbrev honestRounds (y : I) (c : A.Coins Ah Hon) (ch : (A.fullSpec sh).Challenges) (i : Fin m) :
    (sh i).Rounds :=
  (Hon i).rounds (Ah.wit i y c.pads) (c.circuits i) (chN m (A.commitChallenge sh ch) i)

/-- **The verifier's checks pass on an honest run**: the application phase's check on its honest
transcript and every circuit's verdict on its honest commit rounds and its honest proof at the
public input that transcript fixes. -/
structure HonestChecksPass (y : I) (c : A.Coins Ah Hon) (x : Stmt)
    (ch : (A.fullSpec sh).Challenges) : Prop where
  ok : A.ok x (A.honestAppTranscript Ah y c.pads x ch) = true
  circuits : ∀ i, (sh i).V (A.pub i x (A.honestAppTranscript Ah y c.pads x ch))
    ((Hon i).commit (Ah.wit i y c.pads) (c.circuits i)) (A.honestRounds Ah Hon y c ch i)
    (((Hon i).prove (A.pub i x (A.honestAppTranscript Ah y c.pads x ch)) (Ah.wit i y c.pads)
      (c.circuits i) (A.honestRounds Ah Hon y c ch i)).transcript (chN m ch.right i)) = true

/-- The verdict on the honest transcript is the checks on the honest run. -/
theorem fullVerifier_family (y : I) (c : A.Coins Ah Hon) (x : Stmt)
    (ch : (A.fullSpec sh).Challenges) :
    A.fullVerifier sh x ((A.fullFamily Ah Hon y c x).transcript ch) = true ↔
      A.HonestChecksPass Ah Hon y c x ch := by
  unfold fullVerifier fullFamily
  simp only [circuitsV, circuitsOk, circuitsStatement, FieldProof.Shape.verifier, committedFamily,
    CommittedContext.app, CommittedContext.com, CommittedContext.rounds,
    CausalTranscript.append_left, CausalTranscript.append_right, Bool.and_eq_true]
  exact ⟨fun h => ⟨h.1, (FieldProof.Shape.pi_V_honest Hon _ _ c.circuits _ ch.right).mp h.2⟩,
    fun h => ⟨h.ok, (FieldProof.Shape.pi_V_honest Hon _ _ c.circuits _ ch.right).mpr h.circuits⟩⟩

omit Hon in
/-- **The application phase's challenges among uniform protocol challenges are uniform**: an event
on them has the probability it has over the application phase's challenges
(`QROM.probUniform_restrict`). -/
theorem prob_appChallenge (E : A.spec.Challenges → Prop) :
    Pr[ch ← (A.fullSpec sh).Challenges : E (A.appChallenge sh ch)] =
      Pr[a ← A.spec.Challenges : E a] := by
  classical
  have h : ∀ ch : (A.fullSpec sh).Challenges, A.appChallenge sh ch =
      fun j => Equiv.cast (A.appChallenge_type j)
        (ch (ChallengeIdx.inl (ChallengeIdx.inr (ChallengeIdx.inr j)))) := fun ch => by
    funext j
    simp only [appChallenge, Challenges.left, Challenges.right, cast_cast, Equiv.cast_apply]
  simp only [h]
  refine QROM.probUniform_restrict
    (fun j : A.spec.ChallengeIdx => ChallengeIdx.inl (ChallengeIdx.inr (ChallengeIdx.inr j)))
    (fun j j' e => ?_) (fun j => Equiv.cast (A.appChallenge_type j)) E
  exact ChallengeIdx.inr_injective (ChallengeIdx.inr_injective (ChallengeIdx.inl_injective e))

omit Hon in
/-- **The completeness events of the application phase**, read on the protocol's challenges,
have probability at most its completeness error `e` (`hE`). -/
theorem prob_not_avoids {e : ℝ≥0} (hE : Ah.ErrorBound fun _ => e) (x : Stmt) (y : I)
    (hy : (x, y) ∈ relI) :
    Pr[ch ← (A.fullSpec sh).Challenges : ¬ Ah.Avoids x y (A.appChallenge sh ch)] ≤ e :=
  (A.prob_appChallenge (sh := sh) _).trans_le (hE x y hy)

/-- **Completeness over circuits**: at every value of the prover's coins, the honest prover is
rejected with probability at most the application phase's completeness error `e` (`hE`).
`haccept`: every circuit's verdict accepts its honest commit rounds and proof on its domain. -/
theorem completenessAt_full (c : A.Coins Ah Hon) {e : ℝ≥0} (hE : Ah.ErrorBound fun _ => e)
    (haccept : ∀ i p x, dom i p x → ∀ ρ chc ch,
      (sh i).V p ((Hon i).commit x ρ) ((Hon i).rounds x ρ chc)
        (((Hon i).prove p x ρ ((Hon i).rounds x ρ chc)).transcript ch) = true) :
    completenessAt relI (A.fullVerifier sh) (fun y => A.fullHonest Ah Hon y c) e := by
  classical
  refine completenessAt_of_causal relI (A.fullVerifier sh) e
    (fun y => A.fullHonest Ah Hon y c) (fun y x => A.fullFamily Ah Hon y c x)
    (fun y x ch => CausalTranscript.run_realize _ ch x)
    (fun x y ch => ¬ Ah.Avoids x y (A.appChallenge sh ch)) (fun x y hy ch hch => ?_)
    (fun x y hy => by
      have h := (card_le_iff_probUniform_le _ _ _).mpr (A.prob_not_avoids (sh := sh) Ah hE x y hy)
      convert h using 3
      all_goals congr)
  have hgood : Ah.Avoids x y (A.appChallenge sh ch) := not_not.mp hch
  exact (A.fullVerifier_family Ah Hon y c x ch).mpr ⟨Ah.ok_honest x y hy c.pads _ hgood,
    fun i => haccept i _ _ (Ah.dom_honest x y hy c.pads _ hgood i) _ _ _⟩

/-- **The honest transcript**: the honest commit phase and application phase, then the circuits'
honest proofs on the public inputs and commit rounds it fixes. -/
theorem fullFamily_transcript (y : I) (c : A.Coins Ah Hon) (x : Stmt)
    (ch : (A.fullSpec sh).Challenges) :
    (A.fullFamily Ah Hon y c x).transcript ch =
      Transcript.join ((A.committedFamily Ah Hon y c x).transcript ch.left)
        (((FieldProof.Shape.Honest.pi Hon).prove
          (fun i => A.pub i x (A.honestAppTranscript Ah y c.pads x ch))
          (fun i => Ah.wit i y c.pads) c.circuits
          ((FieldProof.Shape.Honest.pi Hon).rounds (fun i => Ah.wit i y c.pads) c.circuits
            (A.commitChallenge sh ch))).transcript ch.right) := by
  change Transcript.join _ (((FieldProof.Shape.Honest.pi Hon).prove (fun i => A.pub i x
    ((A.committedFamily Ah Hon y c x).transcript ch.left).right.right) _ c.circuits
      ((A.committedFamily Ah Hon y c x).transcript ch.left).right.left).transcript
      ch.right) = _
  rw [committedFamily, CausalTranscript.append_right, CausalTranscript.append_right,
    CausalTranscript.append_left]
  rfl

/-! ### How the verifier reads, and the simulator -/

variable (Or : ∀ i, (sh i).Oracle)

/-- How the verifier reads the commit phase and the application phase: the committed family at
the circuits' queried positions (`FieldProof.Shape.Oracle.pi`), every commit-round and application
message in full. -/
def committedMsg : ∀ j : (A.committedSpec (FieldProof.Shape.pi sh).Com
      (FieldProof.Shape.pi sh).commitRounds).MessageIdx,
    MessageView ((A.committedSpec (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds).Type j.1)
      (A.fullSpec sh).Challenges
      (appendFamily (fun _ => (FieldProof.Shape.Oracle.pi Or).Idx) (fun _ => Unit) j)
      (appendFamily (fun _ => (FieldProof.Shape.Oracle.pi Or).Ans)
        (fun j => ((FieldProof.Shape.pi sh).commitRounds ++ A.spec).Type j.1) j) :=
  appendMsg (fun _ => (FieldProof.Shape.Oracle.pi Or).com.comap Challenges.right)
    fun _ => MessageView.plain _ _

/-- The view of the commit phase and the application phase is the commitment's view and the
commit-round and application messages. -/
theorem committedMsg_see_split (ch : (A.fullSpec sh).Challenges)
    (trF : (A.committedSpec (FieldProof.Shape.pi sh).Com (FieldProof.Shape.pi sh).commitRounds).Transcript
      (Fin.last (1 + ((FieldProof.Shape.pi sh).nc + A.n)))) :
    appendViewEquiv (fun j : (A.committedSpec (FieldProof.Shape.pi sh).Com
        (FieldProof.Shape.pi sh).commitRounds).MessageIdx =>
        (A.committedMsg Or j).see ch (trF j.1)) =
      (fun j : (commitSpec (FieldProof.Shape.pi sh).Com).MessageIdx =>
          ((FieldProof.Shape.Oracle.pi Or).com.comap Challenges.right).see ch (trF.left j.1),
        fun j : ((FieldProof.Shape.pi sh).commitRounds ++ A.spec).MessageIdx =>
          (MessageView.plain (((FieldProof.Shape.pi sh).commitRounds ++ A.spec).Type j.1)
            (A.fullSpec sh).Challenges).see ch (trF.right j.1)) :=
  appendViewEquiv_see_left_right _ _ ch trF

/-- **The protocol as an IOP**: the verifier `fullVerifier`, reading the commitment at the
circuits' queried positions, the commit-round and application messages in full, and the circuits'
proof-phase messages as the circuits read them. -/
def fullIOP : IOP.IOP (A.fullSpec sh) Stmt where
  V := A.fullVerifier sh
  Idx := appendFamily (appendFamily (fun _ => (FieldProof.Shape.Oracle.pi Or).Idx) (fun _ => Unit))
    (FieldProof.Shape.Oracle.pi Or).MIdx
  Ans := appendFamily (appendFamily (fun _ => (FieldProof.Shape.Oracle.pi Or).Ans)
    (fun j => ((FieldProof.Shape.pi sh).commitRounds ++ A.spec).Type j.1))
    (FieldProof.Shape.Oracle.pi Or).MAns
  msg := appendMsg (A.committedMsg Or) fun j =>
    ((FieldProof.Shape.Oracle.pi Or).msg j).comap Challenges.right
  reads := TranscriptView.reads_of fun x ch tr tr' htr htr' hview => by
    have hv := congrArg appendViewEquiv (funext hview)
    rw [appendViewEquiv_see_left_right, appendViewEquiv_see_left_right, Prod.mk.injEq] at hv
    obtain ⟨hF, hHv⟩ := hv
    have hF2 := (A.committedMsg_see_split Or ch tr.left).symm.trans
      ((congrArg appendViewEquiv hF).trans (A.committedMsg_see_split Or ch tr'.left))
    rw [Prod.mk.injEq] at hF2
    obtain ⟨hC, hA⟩ := hF2
    have hchF := Transcript.left_challenge htr
    have hchF' := Transcript.left_challenge htr'
    have hRA : tr.left.right = tr'.left.right :=
      Transcript.ext_of_messages (Transcript.right_challenge hchF)
        (Transcript.right_challenge hchF') fun j =>
          MessageView.eq_of_see_plain (congrFun hA j)
    have hcom := congrFun hC ⟨0, rfl⟩
    simp only [fullVerifier, circuitsV, circuitsOk, circuitsStatement, FieldProof.Shape.verifier,
      CommittedContext.app, CommittedContext.com, CommittedContext.rounds]
    rw [hRA]
    congr 1
    exact (FieldProof.Shape.Oracle.pi Or).reads _ ch.right _ _ _ _ _ _ (Transcript.right_challenge htr)
      (Transcript.right_challenge htr')
      (FieldProof.Shape.Reading.view_eq_iff.mpr ⟨hcom, rfl, fun j => congrFun hHv j⟩)

/-- The protocol's view from the application transcript and the circuits' view (whose commit
rounds are read in full). -/
def assembleFull (trA : A.spec.Transcript (Fin.last A.n)) (v : (FieldProof.Shape.Oracle.pi Or).View) :
    (A.fullIOP Or).View :=
  appendViewEquiv.symm (appendViewEquiv.symm
    (fun _ => v.com, fun j _ => some (Transcript.join v.rounds trA j.1)), v.msgs)

/-- **The view of a joined transcript** is assembled from the application transcript and the
circuits' view of the commitment, the commit rounds and their proof-phase transcript. -/
theorem view_join (ch : (A.fullSpec sh).Challenges)
    (trC : (commitSpec (FieldProof.Shape.pi sh).Com).Transcript (Fin.last 1))
    (trR : (FieldProof.Shape.pi sh).Rounds)
    (trA : A.spec.Transcript (Fin.last A.n))
    (trH : (FieldProof.Shape.pi sh).spec.Transcript (Fin.last (FieldProof.Shape.pi sh).n)) :
    (A.fullIOP Or).view ch (Transcript.join (Transcript.join trC (Transcript.join trR trA)) trH) =
      A.assembleFull Or trA ((FieldProof.Shape.Oracle.pi Or).view ch.right (com₀ trC) trR trH) := by
  unfold assembleFull
  refine (Equiv.eq_symm_apply _).mpr ((appendViewEquiv_see _ _ ch _ trH).trans ?_)
  refine Prod.ext ((Equiv.eq_symm_apply _).mpr ((appendViewEquiv_see _ _ ch trC _).trans ?_)) rfl
  refine Prod.ext (funext fun j => ?_)
    (funext fun j => MessageView.see_plain ch (Transcript.join trR trA j.1))
  have hj : j = ⟨0, rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
  subst hj
  rfl

/-- **The simulator over circuits**: the application phase's simulator `SA` at the application
challenges, then the circuits' simulators (`FieldProof.Shape.Simulator.pi`) on the public inputs the
simulated transcript fixes, at their own challenges (of their commit rounds and of their proof
phases); the view is assembled (`assembleFull`).

Running time: one run of the application simulator and of every circuit's simulator, the
verifier's computation of the public inputs (`pub`), and the assembly, which copies view
entries. This running time is argued here, not proved in Lean. -/
def fullSimulator (SA : A.Sim) (S : ∀ i, FieldProof.Shape.Simulator (Or i)) :
    (A.fullIOP Or).Simulator where
  Coins := SA.SimCoins × (FieldProof.Shape.Simulator.pi S).Coins
  sim x ch s := A.assembleFull Or (SA.sim x (A.appChallenge sh ch) s.1)
    ((FieldProof.Shape.Simulator.pi S).sim (fun i => A.pub i x (SA.sim x (A.appChallenge sh ch) s.1))
      (A.commitChallenge sh ch) ch.right s.2)

/-- **Honest-verifier zero knowledge over circuits** at `fullSimulator`, with error the application
phase's completeness error `e` (`hE`) and its completeness events as the exception event: outside them the application transcript has the simulator's law
(`PhaseStep.Honest.identDistrib`), and at each value of the pads the circuits' views have the law of their
simulators on the public inputs it fixes (`FieldProof.Shape.Simulator.Perfect.pi` on the domains
`Honest.dom_honest`), composed by `IdentDistrib.dependent`. `hS`: perfect simulators of the
circuits. -/
theorem hvzk_full {S : ∀ i, FieldProof.Shape.Simulator (Or i)}
    (hS : ∀ i, (S i).Perfect (Hon i) (dom i)) {e : ℝ≥0} (hE : Ah.ErrorBound fun _ => e) :
    (A.fullIOP Or).HVZKOffExceptions relI (A.fullHonest Ah Hon) (A.fullSimulator Or SA S) e
      fun x y ch => ¬ Ah.Avoids x y (A.appChallenge sh ch) where
  bad_le x y hy := A.prob_not_avoids Ah hE x y hy
  simulates x y hy ch hch := by
    have hgood : Ah.Avoids x y (A.appChallenge sh ch) := not_not.mp hch
    have key := (IdentDistrib.dependent
      (f₁ := fun π => (Ah.prover x y π).transcript (A.appChallenge sh ch)) (g₁ := SA.sim x (A.appChallenge sh ch))
      (f₂ := fun π ρ => (FieldProof.Shape.Oracle.pi Or).view ch.right
        ((FieldProof.Shape.Honest.pi Hon).commit (fun i => Ah.wit i y π) ρ)
        ((FieldProof.Shape.Honest.pi Hon).rounds (fun i => Ah.wit i y π) ρ (A.commitChallenge sh ch))
        (((FieldProof.Shape.Honest.pi Hon).prove
          (fun i => A.pub i x ((Ah.prover x y π).transcript (A.appChallenge sh ch)))
          (fun i => Ah.wit i y π) ρ
          ((FieldProof.Shape.Honest.pi Hon).rounds (fun i => Ah.wit i y π) ρ
            (A.commitChallenge sh ch))).transcript ch.right))
      (g₂ := fun trA => (FieldProof.Shape.Simulator.pi S).sim (fun i => A.pub i x trA)
        (A.commitChallenge sh ch) ch.right)
      (Ah.identDistrib x y hy _) fun π =>
        FieldProof.Shape.Simulator.Perfect.pi hS _ _ (fun i => Ah.dom_honest x y hy π _ hgood i)
          (A.commitChallenge sh ch) ch.right).comp
      fun v => A.assembleFull Or v.1 v.2
    refine IdentDistrib.trans (IdentDistrib.of_equiv (A.coinsEquiv Ah Hon) fun c => ?_)
      (key.trans (IdentDistrib.of_equiv (Equiv.refl _) fun _ => rfl))
    change (A.fullIOP Or).view ch ((CausalTranscript.realize (A.fullFamily Ah Hon y c)).run x
      ch) = _
    rw [CausalTranscript.run_realize, fullFamily_transcript]
    exact A.view_join Or ch _ _ _ _

end Honest

end RealizedProgram.ProofSystem.PhaseStep

/-! ### Multi-circuit IOPs -/

/-- **A multi-circuit IOP** for the relation `rel`: `m ≥ 1` circuit proofs (`FieldProof`: a masked row
reduction and a commit-and-prove system each), proving the relations `holds i` on their witnesses, and an
application phase (`RealizedProgram.ProofSystem.PhaseStep`) linking them to the statement. This is the computational part; the
errors and the soundness of the parts are `MultiCircuitIOP.Sound`. See the module docstring. -/
structure MultiCircuitIOP (Stmt W : Type) (rel : Set (Stmt × W)) where
  /-- The number of circuits. -/
  m : ℕ
  /-- There is a circuit. -/
  [neZero : NeZero m]
  /-- The circuits' public inputs. -/
  Pub : Fin m → Type
  /-- The circuits' witnesses. -/
  Wit : Fin m → Type
  /-- The circuits' relations. -/
  holds : ∀ i, Pub i → Wit i → Prop
  /-- The circuit proofs. -/
  circuit : ∀ i, FieldProof (Pub i) (Wit i) (holds i)
  /-- The application phase. -/
  app : RealizedProgram.ProofSystem.PhaseStep Stmt W rel Pub Wit holds

attribute [instance] MultiCircuitIOP.neZero

namespace MultiCircuitIOP

variable (C : MultiCircuitIOP Stmt W rel)

/-- The computational parts of the circuit proofs. -/
abbrev shapes (i : Fin C.m) : FieldProof.Shape (C.Pub i) (C.Wit i) := (C.circuit i).toShape

/-- The number of rounds: the commitment round, the commit rounds, the application phase, the
circuit proofs. -/
abbrev n : ℕ := 1 + ((FieldProof.Shape.pi C.shapes).nc + C.app.n) + (FieldProof.Shape.pi C.shapes).n

/-- The protocol: the commitment round, the circuits' commit rounds, the application phase, the
circuit proofs. -/
abbrev spec : ProtocolSpec C.n := C.app.fullSpec C.shapes

/-- **The verifier**: the application phase's check, then every circuit proof's verdict on the
public input the application phase fixes. -/
def verifier : Verifier C.spec Stmt := C.app.fullVerifier C.shapes

/-- **The extractor**: read the cells from every circuit's commit phase with the commit-and-prove
systems' `extract`, read every circuit's witness with its `readout`, and apply the application
phase's `extract` (`extractor_of_le`). It reads no challenge after the commit phase.

Running time: one call of every circuit's `cp.extract` and `readout` and one of `app.extract`
(their docstrings); reading the prefix copies at most `1 + (nc + app.n)` messages.
This running time is argued here, not proved in Lean. -/
def extractor [Inhabited W] : Extractor C.spec Stmt W := C.app.fullExtractor C.shapes

/-- How the verifier reads each circuit proof. -/
def oracle (i : Fin C.m) : (C.shapes i).Oracle := (C.circuit i).oracle

/-- **The protocol as an IOP**: the verifier `verifier`, reading the round-0 oracle messages at
the commit-and-prove systems' queried leaves and every other message in full. -/
def iop : IOP C.spec Stmt := C.app.fullIOP C.oracle

theorem iop_V : C.iop.V = C.verifier := rfl

/-! ### Soundness -/

/-- **The soundness of a multi-circuit IOP**: every circuit proof's errors and soundness, and
the application phase's errors `appε` with their bound. -/
structure Sound where
  /-- Every circuit proof's errors and soundness. -/
  circuitSound : ∀ i, (C.circuit i).Sound
  /-- The application phase's round errors. -/
  appε : C.app.spec.ChallengeIdx → ℝ≥0
  /-- The event of round `j` has probability at most `appε j`. -/
  appBound : C.app.EventBound appε

variable {C}

/-- The circuit proofs' soundness, on their computational parts. -/
def Sound.circuits (S : C.Sound) (i : Fin C.m) : (C.shapes i).Sound (C.holds i) :=
  (S.circuitSound i).toShape

variable (C) in
/-- The circuit proofs draw a challenge: circuit `0`'s commit-and-prove system does. -/
theorem hasChallenge : C.app.HasChallenge C.shapes := by
  obtain ⟨j⟩ := (C.circuit 0).cp.nonemptyIdx
  exact .inr ⟨(chIdxEquivN C.m fun i => (C.shapes i).spec).symm ⟨0, ChallengeIdx.inr j⟩⟩

/-- **The state function**: the application phase's state, then, from the first challenge of
the protocol, the phase's condition or the circuit proofs' states (`RealizedProgram.ProofSystem.PhaseStep.fullStateFn`). Not
required to be efficient. -/
def stateFn [Inhabited W] (S : C.Sound) : KnowledgeStateFunction C.verifier :=
  C.app.fullStateFn S.circuits (hasChallenge C)

/-- **The round errors**: every circuit's commit-and-prove commit-phase errors at its commit
rounds, the application phase's at its challenge rounds, then every circuit proof's: its masked row
reduction's, then its commit-and-prove system's. -/
def error (S : C.Sound) : C.spec.ChallengeIdx → ℝ≥0 := C.app.fullError S.circuits S.appε

/-- **Round-by-round knowledge soundness of a multi-circuit IOP**: the multi-circuit IOP is
round-by-round knowledge sound for `rel` at the named extractor `extractor` and state function
`stateFn`, with round errors `error` (every commit-and-prove system's commit-phase events, the
application phase's events, every masked row reduction's reduction errors and every commit-and-prove system's
errors). -/
theorem rbr_knowledge_soundness [Inhabited W] (S : C.Sound) :
    rbrKnowledgeSoundness rel C.verifier C.extractor (C.stateFn S) (C.error S) :=
  C.app.rbrKnowledgeSoundness_full S.circuits S.appBound (hasChallenge C)

/-! ### Completeness and zero knowledge -/

variable (C) in
/-- **The simulator data of a multi-circuit IOP**: the application phase's simulator and every
circuit proof's simulator data (`simulator` assembles them). Data apart from the honest prover
(`Honest`). -/
structure SimData where
  /-- The application phase's simulator. -/
  app : C.app.Sim
  /-- Every circuit proof's simulator data. -/
  circuit : ∀ i, (C.circuit i).Sim

variable (C) in
/-- **The honest prover of a multi-circuit IOP**, simulated by `S`, on honest inputs `I` related to
statements by `relI`: the circuits' honest inputs `In i` and domains `dom i`, the application
phase's honest prover and every circuit proof's honest prover. -/
structure Honest (S : C.SimData) (I : Type) (relI : Set (Stmt × I)) where
  /-- The circuits' honest inputs. -/
  In : Fin C.m → Type
  /-- The circuits' domains. -/
  dom : ∀ i, C.Pub i → In i → Prop
  /-- The application phase's honest prover. -/
  app : C.app.Honest I relI In dom S.app
  /-- The circuit proofs' honest provers. -/
  circuit : ∀ i, (C.circuit i).Honest (S.circuit i) (In i) (dom i)

variable {S : C.SimData} {I : Type} {relI : Set (Stmt × I)}

/-- The honest prover's coins: the application pads and every circuit proof's coins. -/
abbrev Honest.Coins (Hc : C.Honest S I relI) : Type :=
  C.app.Coins Hc.app fun i => (Hc.circuit i).toShape

/-- **The honest prover** at the honest input `y` and the coins: commit to the circuits' cells,
run the application phase's honest prover, then every circuit proof's honest prover. Future
challenges are never read (`CausalTranscript.realize`). -/
noncomputable def honest (Hc : C.Honest S I relI) (y : I) (c : Hc.Coins) : Prover C.spec Stmt :=
  C.app.fullHonest Hc.app (fun i => (Hc.circuit i).toShape) y c

/-- **The simulator**: the application phase's simulator, then every circuit proof's simulator
(`FieldProof.simulator`) on the public input the simulated transcript fixes.

Running time: one run of the application simulator and of every circuit proof's simulator (their
docstrings), the verifier's computation of the public inputs, and the assembly of the view.
This running time is argued here, not proved in Lean. -/
def simulator (S : C.SimData) : C.iop.Simulator :=
  C.app.fullSimulator C.oracle S.app fun i => FieldProof.simulator (S.circuit i)

variable (C) in
/-- The application part of the protocol's challenges. -/
abbrev appChallenges (ch : C.spec.Challenges) : C.app.spec.Challenges := C.app.appChallenge C.shapes ch

/-- **Completeness of a multi-circuit IOP**: at every value of the prover's coins, the honest prover
is rejected with probability at most the application phase's completeness error `e` (`hE`: its
completeness events together have probability at most `e`); the circuit proofs are perfectly
complete on their domains. -/
theorem completeness (Hc : C.Honest S I relI) (c : Hc.Coins) {e : ℝ≥0}
    (hE : Hc.app.ErrorBound fun _ => e) :
    completenessAt relI C.verifier (fun y => C.honest Hc y c) e :=
  C.app.completenessAt_full Hc.app (fun i => (Hc.circuit i).toShape) c hE
    fun i _ _ hx ρ chc ch => FieldProof.completeness (Hc.circuit i) hx ρ chc ch

/-- **Honest-verifier zero knowledge of a multi-circuit IOP** at the named simulator `simulator`,
with error the application phase's completeness error `e` (`hE`) and exception event its
completeness events:
outside them the simulation is perfect (the application phase's simulation, and every circuit
proof's: the masked row reduction's and the commit-and-prove system's, `FieldProof.hvzk`). -/
theorem hvzk (Hc : C.Honest S I relI) {e : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => e) :
    C.iop.HVZKOffExceptions relI (C.honest Hc) (C.simulator S) e
      fun x y ch => ¬ Hc.app.Avoids x y (C.appChallenges ch) :=
  C.app.hvzk_full Hc.app (fun i => (Hc.circuit i).toShape) C.oracle
    (fun i => FieldProof.hvzk (Hc.circuit i)) hE

end MultiCircuitIOP

end GordieHowe
