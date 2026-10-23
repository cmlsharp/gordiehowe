-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.AppendNView
public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.Model.IOP.CommitPhase
public import GordieHowe.Model.QROM.Instability

@[expose] public section

/-!
# The application phase of a multi-circuit protocol

A multi-circuit protocol (`MultiCircuitIOP`) commits to the witnesses of `m` circuits in a commit
phase (round 0, then the circuits' commit rounds), runs an **application phase** (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep`;
compare LegoSNARK p. 5 "a (lightweight) linking of" component proofs, FS24 p. 4 "witness consistency
protocol", CHVY25 p. 7 "cross-field authentication"), and then the `m` circuit proofs on public
inputs the application phase fixes. The application phase states what links the circuits to the
statement:

* `ok`: the verifier's own check on the statement and the phase's transcript;
* `pub i`: the context map, the public input of circuit `i`;
* `extract`: the witness of the statement from the circuits' witnesses (computable);
* `event j`: the event charged at challenge round `j`, a function of the circuits' witnesses and
  the transcript up to and including the challenge (`tr.upTo j`);
* `sound`: on a transcript the verifier's check passes, if every circuit's relation holds at its
  public input then `extract` gives a witness in the relation (`Extracts`) or one of the events
  occurred.

The phase may have no challenge round of its own (`n = 0`, or prover messages only).

`GordieHowe.RealizedProgram.ProofSystem.PhaseStep` is the computational part with the events; the errors are separate:
`RealizedProgram.ProofSystem.PhaseStep.EventBound A ε` states that the event of round `j` has probability at most `ε j` over
the challenge of round `j`. Keeping the errors out of `GordieHowe.RealizedProgram.ProofSystem.PhaseStep` keeps the projections of a
concrete instance (its extraction, its public inputs) computable.

The phase's state (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.state`): a challenge of the phase has been drawn, and the extracted
witness is in the relation or the event of a drawn challenge occurred. On the full transcript the
second part is `cond`. After the commit phase (`committedSpec`: the commitment round, the commit
rounds `R`, then the phase) these are `committedState` and `committedCond` at the witnesses read
from the commit phase; during the commit rounds the state is their bad state (`BadState`), and
afterwards a bad commit phase (`CommittedContext.Bad`) keeps it true. The state function of the
whole protocol, which switches the phase's condition on at the first challenge of the protocol,
whether of the phase or of the circuit proofs, is `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullStateFn`
(`GordieHowe/ProofSystem/Program/Basic.lean`). Its extractor reads the witnesses from the commit phase and
applies `extract`; it reads no challenge after the commit phase (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.extractor`).

The honest prover (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest`): pads drawn before the commitment fix the circuits' honest
inputs and the phase's honest prover; completeness events `bad j` charged to round `j`, which
may read every challenge, with their probabilities over round `j`'s challenge (whatever the
others) in `Honest.BadBound`, outside which (`Honest.Avoids`) the honest run
passes; and a named simulator of the phase's transcript with the honest law at every challenge
vector. The phase's prover messages are read in full.
-/

namespace GordieHowe
open IOP

open ProtocolSpec
open scoped NNReal

/-- **The commitment round**: one prover message of type `Com`. -/
def commitSpec (Com : Type) : ProtocolSpec 1 := ⟨fun _ => .P_to_V, fun _ => Com⟩

namespace commitSpec

variable {Com : Type}

/-- The commitment round has no challenge. -/
theorem not_challengeIdx (i : (commitSpec Com).ChallengeIdx) : False := by
  cases i.2

instance (i : (commitSpec Com).ChallengeIdx) : Fintype ((commitSpec Com).Challenge i) :=
  (not_challengeIdx i).elim

instance (i : (commitSpec Com).ChallengeIdx) : Nonempty ((commitSpec Com).Challenge i) :=
  (not_challengeIdx i).elim

instance (i : (commitSpec Com).ChallengeIdx) : DecidableEq ((commitSpec Com).Challenge i) :=
  (not_challengeIdx i).elim

end commitSpec

/-- **`extract` gives a witness of `x`**: it returns a witness in the relation. -/
def RealizedProgram.ProofSystem.PhaseStep.Extracts {Stmt W V : Type} (rel : Set (Stmt × W)) (extract : V → Option W)
    (x : Stmt) (w : V) : Prop :=
  ∃ w', extract w = some w' ∧ (x, w') ∈ rel

/-- **An application phase** for the relation `rel` between statements `Stmt` and witnesses
`W`, linking `m` circuits with public inputs `Pub i`, witnesses `Wit i` and relations
`holds i`: the computational part with the events. See the module docstring. `extract` is part
of the extractor (`MultiCircuitIOP.extractor`), so an instance must give a computable,
polynomial-time definition; its docstring argues the running time. -/
structure RealizedProgram.ProofSystem.PhaseStep (Stmt W : Type) (rel : Set (Stmt × W)) {m : ℕ} (Pub Wit : Fin m → Type)
    (holds : ∀ i, Pub i → Wit i → Prop) where
  /-- The number of rounds. -/
  n : ℕ
  /-- The rounds after the commitments and before the circuit proofs. -/
  spec : ProtocolSpec n
  [fintype : ∀ i, Fintype (spec.Challenge i)]
  [decEq : ∀ i, DecidableEq (spec.Challenge i)]
  [nonempty : ∀ i, Nonempty (spec.Challenge i)]
  /-- The verifier's check on the statement and the phase's transcript. -/
  ok : Stmt → spec.Transcript (Fin.last n) → Bool
  /-- The public input of circuit `i`. -/
  pub : (i : Fin m) → Stmt → spec.Transcript (Fin.last n) → Pub i
  /-- The witness extracted from the circuits' witnesses. -/
  extract : (∀ i, Wit i) → Option W
  /-- The event charged at challenge round `j`, given the circuits' witnesses, the statement
  and the transcript up to and including the challenge. -/
  event : (j : spec.ChallengeIdx) → (∀ i, Wit i) → Stmt → spec.Transcript j.1.succ → Prop
  /-- The circuits' relations at their public inputs give the relation on the extracted witness
  or an event. -/
  sound : ∀ x w tr, ok x tr = true → AllHold holds (fun i => pub i x tr) w →
    PhaseStep.Extracts rel extract x w ∨ ∃ j : spec.ChallengeIdx, event j w x (tr.upTo j)

attribute [instance] RealizedProgram.ProofSystem.PhaseStep.fintype RealizedProgram.ProofSystem.PhaseStep.decEq RealizedProgram.ProofSystem.PhaseStep.nonempty

namespace RealizedProgram.ProofSystem.PhaseStep

variable {Stmt W : Type} {rel : Set (Stmt × W)} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop} (A : PhaseStep Stmt W rel Pub Wit holds)

open Classical in
/-- **The errors of an application phase**: at every prefix, the event of round `j` has
probability at most `ε j` over the challenge of round `j`. -/
def EventBound (ε : A.spec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ j w x (tr : A.spec.Transcript j.1.castSucc),
    Pr[c ← A.spec.Challenge j : A.event j w x (A.spec.concat tr c)] ≤ ε j

variable {A} in
open Classical in
/-- `EventBound` as a count: at most `ε j · |C_j|` challenges make the event occur. -/
theorem EventBound.card_le {ε : A.spec.ChallengeIdx → ℝ≥0} (h : A.EventBound ε) (j w x)
    (tr : A.spec.Transcript j.1.castSucc) :
    ((Finset.univ.filter fun c => A.event j w x (A.spec.concat tr c)).card : ℝ≥0) ≤
      ε j * Fintype.card (A.spec.Challenge j) :=
  (card_le_iff_probUniform_le _ _ _).mpr (h j w x tr)

/-! ### The phase after the commit phase -/

variable (Com : Type) {nR : ℕ} (R : ProtocolSpec nR)

/-- The protocol of the commit phase (the commitment round, then the commit rounds `R`) followed
by the phase. -/
abbrev committedSpec : ProtocolSpec (1 + (nR + A.n)) := commitSpec Com ++ (R ++ A.spec)

/-- The prefix lengths of the commit phase followed by the phase. -/
abbrev CommittedIdx : Type := Fin (1 + (nR + A.n) + 1)

/-- **The context after the commit phase and the phase**: the statement and the full transcript
of the commit phase and the phase. -/
structure CommittedContext where
  /-- The statement. -/
  stmt : Stmt
  /-- The transcript of the commit phase and the phase. -/
  transcript : (A.committedSpec Com R).Transcript (Fin.last (1 + (nR + A.n)))

variable {Com}

/-- The commitment of a full commitment-round transcript. -/
def com₀ (tr₁ : (commitSpec Com).Transcript (Fin.last 1)) : Com := tr₁ ⟨0, Nat.zero_lt_one⟩

variable {A R}

/-- The commitment of a context. -/
abbrev CommittedContext.com (c : A.CommittedContext Com R) : Com := com₀ c.transcript.left

/-- The commit rounds of a context. -/
abbrev CommittedContext.rounds (c : A.CommittedContext Com R) : R.Transcript (Fin.last nR) :=
  c.transcript.right.left

/-- The phase's transcript in a context. -/
abbrev CommittedContext.app (c : A.CommittedContext Com R) : A.spec.Transcript (Fin.last A.n) :=
  c.transcript.right.right

variable (A R)

/-- The errors of the phase after the commit phase: the commit rounds' errors `εR`, then the
phase's `ε` (the commitment round has none). -/
def committedError (εR : R.ChallengeIdx → ℝ≥0) (ε : A.spec.ChallengeIdx → ℝ≥0) :
    (A.committedSpec Com R).ChallengeIdx → ℝ≥0 :=
  appendError (fun i => (commitSpec.not_challengeIdx i).elim) (appendError εR ε)

variable {A R}

/-- A bound on the commit rounds' and the phase's errors bounds every error after the commitment
round. -/
theorem committedError_le {εR : R.ChallengeIdx → ℝ≥0} {ε : A.spec.ChallengeIdx → ℝ≥0} {δ : ℝ≥0}
    (hR : ∀ j, εR j ≤ δ) (h : ∀ j, ε j ≤ δ) (i : (A.committedSpec Com R).ChallengeIdx) :
    A.committedError R εR ε i ≤ δ :=
  appendError_le (fun c => (commitSpec.not_challengeIdx c).elim) (appendError_le hR h) i

variable (A R)

section Extraction

variable [Inhabited W]

/-- The extracted witness, or the fixed `default` when `extract` fails.

Running time: one call of `extract`. This running time is argued here, not proved in Lean. -/
def witnessOf (w : ∀ i, Wit i) : W := (A.extract w).getD default

/-- A witness `extract` gives is the extracted witness. -/
theorem mem_of_extracts {x : Stmt} {w : ∀ i, Wit i} (h : Extracts rel A.extract x w) :
    (x, A.witnessOf w) ∈ rel := by
  obtain ⟨w', he, hrel⟩ := h
  rw [witnessOf, he]
  exact hrel

/-! ### The state function -/

/-- **The condition of the phase** on a full transcript, given the circuits' witnesses `w`: the
extracted witness is in the relation or the event of some challenge round occurred. Not required
to be efficient. -/
def cond (w : ∀ i, Wit i) (x : Stmt) (tr : A.spec.Transcript (Fin.last A.n)) : Prop :=
  (x, A.witnessOf w) ∈ rel ∨ ∃ j : A.spec.ChallengeIdx, A.event j w x (tr.upTo j)

/-- The condition holds on a full transcript whose verifier check passes and on which every
circuit's relation holds: the phase's `sound`. -/
theorem cond_of_sound (w : ∀ i, Wit i) (x : Stmt) (tr : A.spec.Transcript (Fin.last A.n))
    (hok : A.ok x tr = true) (hw : AllHold holds (fun i => A.pub i x tr) w) : A.cond w x tr :=
  (A.sound x w tr hok hw).imp A.mem_of_extracts id

/-- An event needs a challenge round. -/
theorem nonempty_of_cond {w : ∀ i, Wit i} {x : Stmt} {tr : A.spec.Transcript (Fin.last A.n)}
    (hrel : (x, A.witnessOf w) ∉ rel) (h : A.cond w x tr) : Nonempty A.spec.ChallengeIdx := by
  obtain ⟨j, -⟩ := h.resolve_left hrel
  exact ⟨j⟩

/-- Without a challenge round, the condition is the relation on the extracted witness. -/
theorem mem_of_cond {w : ∀ i, Wit i} {x : Stmt} {tr : A.spec.Transcript (Fin.last A.n)}
    (hno : ¬ Nonempty A.spec.ChallengeIdx) (h : A.cond w x tr) : (x, A.witnessOf w) ∈ rel :=
  h.resolve_right fun ⟨j, _⟩ => hno ⟨j⟩

/-- **The state of the phase** at a prefix of length `k`, given the circuits' witnesses `w`: a
challenge has been drawn, and the extracted witness is in the relation or the event of a drawn
challenge occurred. Not required to be efficient. -/
def state (w : ∀ i, Wit i) (k : Fin (A.n + 1)) (x : Stmt) (tr : A.spec.Transcript k) : Prop :=
  ChallengeDrawn A.spec k ∧
    ((x, A.witnessOf w) ∈ rel ∨ ∃ j : A.spec.ChallengeIdx, ∃ h : j.1.succ ≤ k,
      A.event j w x (tr.take j.1.succ h))

theorem state_zero (w : ∀ i, Wit i) (x : Stmt) (tr : A.spec.Transcript 0) :
    ¬ A.state w 0 x tr := by
  rintro ⟨⟨j, hj⟩, -⟩
  exact absurd hj (by simp)

/-- On a full transcript the state is a challenge round of the phase and the condition. -/
theorem state_last_iff (w : ∀ i, Wit i) (x : Stmt) (tr : A.spec.Transcript (Fin.last A.n)) :
    A.state w (Fin.last A.n) x tr ↔ Nonempty A.spec.ChallengeIdx ∧ A.cond w x tr :=
  and_congr ⟨fun ⟨j, _⟩ => ⟨j⟩, fun ⟨j⟩ => ⟨j, Fin.le_last _⟩⟩
    (or_congr Iff.rfl ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩, fun ⟨j, h⟩ => ⟨j, Fin.le_last _, h⟩⟩)

/-- A prover message does not make the state true. -/
theorem state_next (w : ∀ i, Wit i) (k : Fin A.n) (hk : A.spec.dir k = .P_to_V) (x : Stmt)
    (tr : A.spec.Transcript k.castSucc) (msg : A.spec.Type k)
    (hnot : ¬ A.state w k.castSucc x tr) : ¬ A.state w k.succ x (A.spec.concat tr msg) := by
  rintro ⟨hd, h⟩
  refine hnot ⟨challengeDrawn_succ_of_message hk hd, h.imp id ?_⟩
  rintro ⟨j', hj', he⟩
  have hj'' := ProtocolSpec.succ_le_castSucc_of_message hk hj'
  refine ⟨j', hj'', ?_⟩
  rwa [← ProtocolSpec.take_concat tr msg j'.1.succ hj'']

open Classical in
/-- **The state flips at challenge round `j`** while the extractor fails only on the event of
round `j`. -/
theorem state_flip_card {ε : A.spec.ChallengeIdx → ℝ≥0} (hε : A.EventBound ε) (w : ∀ i, Wit i)
    (x : Stmt) (j : A.spec.ChallengeIdx) (tr : A.spec.Transcript j.1.castSucc) :
    ((Finset.univ.filter fun c : A.spec.Challenge j =>
        (x, A.witnessOf w) ∉ rel ∧ ¬ A.state w j.1.castSucc x tr ∧
          A.state w j.1.succ x (A.spec.concat tr c)).card : ℝ≥0) ≤
      ε j * Fintype.card (A.spec.Challenge j) := by
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun c hc => ?_)) (hε.card_le j w x tr)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨hrel, hnot, -, hs⟩ := hc
  obtain ⟨j', hj', he⟩ := hs.resolve_left hrel
  by_cases e : j' = j
  · subst e
    exact he
  · exfalso
    have hle : j'.1.succ ≤ j.1.castSucc := by
      have hne : (j'.1 : ℕ) ≠ j.1 := fun h => e (Subtype.ext (Fin.ext h))
      rw [Fin.le_def] at hj' ⊢
      simp only [Fin.val_succ, Fin.val_castSucc] at hj' ⊢
      omega
    refine hnot ⟨⟨j', hle⟩, .inr ⟨j', hle, ?_⟩⟩
    rwa [← ProtocolSpec.take_concat tr c j'.1.succ hle]

variable {A R}

/-- The commitment in a transcript that contains round 0. -/
def comOf {k : A.CommittedIdx} (tr : (A.committedSpec Com R).Transcript k) (h : 1 ≤ (k : ℕ)) :
    Com :=
  com₀ (tr.fst (Fin.last 1) h)

/-- The commit rounds in a transcript that contains the commit phase. -/
def roundsOf {k : A.CommittedIdx} (tr : (A.committedSpec Com R).Transcript k)
    (h : 1 + nR ≤ (k : ℕ)) : R.Transcript (Fin.last nR) :=
  (tr.snd ⟨nR, by omega⟩ h).fst (Fin.last nR) le_rfl

variable (ext : Com → R.Transcript (Fin.last nR) → ∀ i, Wit i)

variable (A) in
/-- **The extractor of the phase**: once the commit phase is in the prefix, read the circuits'
witnesses from it with `ext` and apply `extract` (`witnessOf`); before, `default`. It reads no
challenge after the commit phase.

Running time: one call of `ext` and one of `extract`. This running time is argued here, not proved
in Lean. -/
def extractor : Extractor (A.committedSpec Com R) Stmt W where
  extract k _ tr :=
    if h : 1 + nR ≤ (k : ℕ) then A.witnessOf (ext (comOf tr (by omega)) (roundsOf tr h))
    else default

theorem extractor_of_le {k : A.CommittedIdx} (x : Stmt) (tr : (A.committedSpec Com R).Transcript k)
    (h : 1 + nR ≤ (k : ℕ)) :
    A.extractor ext k x tr = A.witnessOf (ext (comOf tr (by omega)) (roundsOf tr h)) :=
  dite_eq_left h

/-- On the full transcript the extractor gives the witness extracted from the context's commit
phase. -/
theorem extractor_last (c : A.CommittedContext Com R) :
    A.extractor ext (Fin.last _) c.stmt c.transcript = A.witnessOf (ext c.com c.rounds) :=
  extractor_of_le ext _ _ (by simp)

variable (A) in
/-- The claim the circuit proofs prove after the phase: the verifier's check and every
circuit's relation at its public input on the witnesses read from the commit phase. -/
def committedClaim (c : A.CommittedContext Com R) : Prop :=
  A.ok c.stmt c.app = true ∧ AllHold holds (fun i => A.pub i c.stmt c.app) (ext c.com c.rounds)

variable (A) in
/-- The condition of the phase on the full transcript after the commit phase, at the witnesses
read from the commit phase. -/
def committedCond (c : A.CommittedContext Com R) : Prop :=
  A.cond (ext c.com c.rounds) c.stmt c.app

/-- The claim gives the condition (`cond_of_sound`). -/
theorem committedCond_of_claim {c : A.CommittedContext Com R} (h : A.committedClaim ext c) :
    A.committedCond ext c :=
  A.cond_of_sound _ _ _ h.1 h.2

/-! ### The state after the commit phase -/

variable [∀ i, Fintype (R.Challenge i)] {εR : R.ChallengeIdx → ℝ≥0} (cs : BadState R Com εR)

/-- **The commit phase of a context was bad**: the commit rounds' bad state is true at their
end. -/
def CommittedContext.Bad (c : A.CommittedContext Com R) : Prop :=
  cs.S (Fin.last nR) c.com c.rounds

variable (A) in
/-- The state after the commitment round at the commitment `O`: the commit rounds' bad state,
then the commit phase was bad or the phase's state at the witnesses read from the commit
phase. Not required to be efficient. -/
def phaseState (O : Com) (k : Fin (nR + A.n + 1)) (x : Stmt) (tr : (R ++ A.spec).Transcript k) :
    Prop :=
  appendState (fun k trR => cs.S k O trR)
    (fun trR k trA => cs.S (Fin.last nR) O trR ∨ A.state (ext O trR) k x trA) k tr

/-- At the start of the phase, the state is the commit rounds' final bad state: the phase's own
state is false there. -/
theorem bad_of_phaseState_start (O : Com) (x : Stmt) (trR : R.Transcript (Fin.last nR))
    (trA : A.spec.Transcript 0) (h : cs.S (Fin.last nR) O trR ∨ A.state (ext O trR) 0 x trA) :
    cs.S (Fin.last nR) O trR :=
  h.resolve_right (A.state_zero _ x trA)

/-- The state is false on the empty transcript. -/
theorem phaseState_zero (O : Com) (x : Stmt) (tr : (R ++ A.spec).Transcript 0) :
    ¬ A.phaseState ext cs O 0 x tr := fun h =>
  cs.start O _ (appendState_of_le (A.bad_of_phaseState_start ext cs O x) (k₁ := 0) rfl h)

/-- A prover message does not make the state true. -/
theorem phaseState_next (O : Com) (k : Fin (nR + A.n)) (hdir : (R ++ A.spec).dir k = .P_to_V)
    (x : Stmt) (tr : (R ++ A.spec).Transcript k.castSucc) (msg : (R ++ A.spec).Type k)
    (hnot : ¬ A.phaseState ext cs O k.castSucc x tr) :
    ¬ A.phaseState ext cs O k.succ x ((R ++ A.spec).concat tr msg) := by
  induction k using Fin.addCases with
  | left j =>
    intro h
    have hflip := appendState_flip_castAdd (A.bad_of_phaseState_start ext cs O x) j tr msg hnot h
    exact cs.next j (by simpa using hdir) O _ _ hflip.1 hflip.2
  | right j =>
    intro h
    obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, h⟩
    exact A.state_next _ j (by simpa using hdir) x _ _ (fun h' => hn (.inr h'))
      (hs.resolve_left fun h' => hn (.inl h'))

/-- On the full transcript the state is a bad commit phase, or a challenge round of the phase and
the condition. -/
theorem phaseState_last_iff (O : Com) (x : Stmt)
    (tr : (R ++ A.spec).Transcript (Fin.last (nR + A.n))) :
    A.phaseState ext cs O (Fin.last _) x tr ↔
      cs.S (Fin.last nR) O tr.left ∨ (Nonempty A.spec.ChallengeIdx ∧ A.cond (ext O tr.left) x tr.right) := by
  unfold phaseState
  rw [appendState_iff_of_eq_add (k₂ := Fin.last A.n) (by simp)]
  exact or_congr Iff.rfl (A.state_last_iff _ _ _)

variable (A) in
/-- The state after the commit phase: false during round 0, then `phaseState` at the
commitment. Not required to be efficient. -/
def committedState (k : A.CommittedIdx) (x : Stmt) (tr : (A.committedSpec Com R).Transcript k) :
    Prop :=
  appendState (fun _ _ => False) (fun tr₁ k tr₂ => A.phaseState ext cs (com₀ tr₁) k x tr₂) k tr

/-- The state is false on the empty transcript. -/
theorem committedState_zero (x : Stmt) (tr : (A.committedSpec Com R).Transcript 0) :
    ¬ A.committedState ext cs 0 x tr := by
  unfold committedState
  rw [appendState_iff_of_lt (k₁ := 0) rfl (by norm_num)]
  exact id

/-- On the full transcript the state is a bad commit phase, or a challenge round of the phase and
the condition. -/
theorem committedState_last_iff (c : A.CommittedContext Com R) :
    A.committedState ext cs (Fin.last _) c.stmt c.transcript ↔
      c.Bad cs ∨ (Nonempty A.spec.ChallengeIdx ∧ A.committedCond ext c) := by
  unfold committedState
  rw [appendState_iff_of_eq_add (k₂ := Fin.last (nR + A.n)) (by simp)]
  exact A.phaseState_last_iff ext cs _ _ _

/-- A prover message does not make the state true. -/
theorem committedState_next (k : Fin (1 + (nR + A.n)))
    (hdir : (A.committedSpec Com R).dir k = .P_to_V) (x : Stmt)
    (tr : (A.committedSpec Com R).Transcript k.castSucc)
    (msg : (A.committedSpec Com R).Type k) (hnot : ¬ A.committedState ext cs k.castSucc x tr) :
    ¬ A.committedState ext cs k.succ x ((A.committedSpec Com R).concat tr msg) := by
  induction k using Fin.addCases with
  | left j =>
    intro h
    unfold committedState at hnot h
    exact (appendState_flip_castAdd (S₁ := fun _ _ => False)
      (S₂ := fun tr₁ k tr₂ => A.phaseState ext cs (com₀ tr₁) k x tr₂)
      (fun tr₁ tr₂ h => A.phaseState_zero ext cs _ x tr₂ h) j tr msg hnot h).2
  | right j =>
    intro h
    unfold committedState at hnot h
    obtain ⟨hn, hs⟩ := (appendState_flip_natAdd (S₁ := fun _ _ => False)
      (S₂ := fun tr₁ k tr₂ => A.phaseState ext cs (com₀ tr₁) k x tr₂) j tr msg).mp ⟨hnot, h⟩
    exact A.phaseState_next ext cs _ j (by simpa using hdir) x _ _ hn hs

open Classical in
/-- **The state flips at a challenge round after the commitment round** only on that round's
event: at a commit round (before the end of the commit phase) whatever the extractor returns,
at a round of the phase while the extractor fails; with the commit rounds' and the phase's
errors. -/
theorem committedState_flip_card {ε : A.spec.ChallengeIdx → ℝ≥0} (hε : A.EventBound ε) (x : Stmt)
    (i : (A.committedSpec Com R).ChallengeIdx)
    (tr : (A.committedSpec Com R).Transcript i.1.castSucc) :
    ((Finset.univ.filter fun c : (A.committedSpec Com R).Challenge i =>
        ((i.1 : ℕ) < 1 + nR ∨ (x, A.extractor ext i.1.castSucc x tr) ∉ rel) ∧
          ¬ A.committedState ext cs i.1.castSucc x tr ∧
          A.committedState ext cs i.1.succ x ((A.committedSpec Com R).concat tr c)).card : ℝ≥0) ≤
      A.committedError R εR ε i * Fintype.card ((A.committedSpec Com R).Challenge i) := by
  rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j', rfl⟩
  · exact (commitSpec.not_challengeIdx j).elim
  rw [committedError, appendError_inr]
  refine card_le_of_mapsTo_cast (append_Challenge_inr j')
    (t := Finset.univ.filter fun c : (R ++ A.spec).Challenge j' =>
      ((j'.1 : ℕ) < nR ∨ (x, A.extractor ext (ChallengeIdx.inr j').1.castSucc x tr) ∉ rel) ∧
      ¬ A.phaseState ext cs (com₀ (tr.fst (Fin.last 1) (by simp))) j'.1.castSucc x
        (tr.snd j'.1.castSucc (by simp)) ∧
      A.phaseState ext cs (com₀ (tr.fst (Fin.last 1) (by simp))) j'.1.succ x
        ((R ++ A.spec).concat (tr.snd j'.1.castSucc (by simp)) c)) (fun c hc => ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    obtain ⟨hE, hflip⟩ := hc
    unfold committedState at hflip
    obtain ⟨hn, hs⟩ := (appendState_flip_natAdd (S₁ := fun _ _ => False)
      (S₂ := fun tr₁ k tr₂ => A.phaseState ext cs (com₀ tr₁) k x tr₂) j'.1 tr c).mp hflip
    refine ⟨hE.imp (fun h => ?_) id, hn, ?_⟩
    · simp only [ChallengeIdx.val_inr, Fin.val_natAdd] at h
      omega
    · exact hs
  rcases ChallengeIdx.inl_or_inr j' with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [appendError_inl]
    refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun c hc => ?_)
      (cs.rbr (com₀ (tr.fst (Fin.last 1) (by simp))) j
        ((tr.snd (ChallengeIdx.inl (P₂ := A.spec) j).1.castSucc (by simp)).fst j.1.castSucc
          (by simp)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact appendState_flip_castAdd (A.bad_of_phaseState_start ext cs _ x) j.1 _ c hc.2.1 hc.2.2
  · rw [appendError_inr]
    refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun c hc => ?_)
      (A.state_flip_card hε (ext (com₀ (tr.fst (Fin.last 1) (by simp)))
        ((tr.snd (ChallengeIdx.inr (P₁ := R) j).1.castSucc (by simp)).fst (Fin.last nR) (by simp))) x j
        ((tr.snd (ChallengeIdx.inr (P₁ := R) j).1.castSucc (by simp)).snd j.1.castSucc (by simp)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    obtain ⟨hE, hflip⟩ := hc
    obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 _ c).mp hflip
    have hE' := hE.resolve_left (by simp)
    rw [extractor_of_le ext x tr (by simp)] at hE'
    exact ⟨hE', fun h' => hn (.inr h'), hs.resolve_left fun h' => hn (.inl h')⟩

end Extraction

/-! ### The honest prover -/

/-- **The challenges avoid every completeness event** `bad j` at the statement `x` and the
honest input `y`. -/
def AvoidsEvents {I : Type} {n : ℕ} {P : ProtocolSpec n}
    (bad : (j : P.ChallengeIdx) → Stmt → I → P.Challenges → Prop) (x : Stmt) (y : I)
    (ch : P.Challenges) : Prop :=
  ∀ j, ¬ bad j x y ch

/-- **A simulator of an application phase's transcript** (`IOP.TranscriptSim`), on the statement and
the challenges only: data apart from the honest prover (`Honest`). -/
abbrev Sim : Type 1 := IOP.TranscriptSim Stmt A.spec

/-- **The honest prover of an application phase**, simulated by `S`, on honest inputs `I` related to
statements by `relI`, for circuits with honest inputs `In i` in the domains `dom i`: pads drawn before the
commitment fix every circuit's honest input (`wit`) and the phase's honest prover (`prover`);
completeness events `bad j` charged to round `j`, which may read every challenge (their
probabilities over round `j`'s challenge, whatever the others, are `Honest.BadBound`), outside
which (`AvoidsEvents`) the verifier's check passes and every
circuit's honest input lies in its domain at its public input; and a simulator of the phase's
transcript (`sim`, on the statement and the challenges only) with the honest law at every
challenge vector (`identDistrib`). -/
structure Honest (I : Type) (relI : Set (Stmt × I)) (In : Fin m → Type)
    (dom : ∀ i, Pub i → In i → Prop) (S : A.Sim) where
  /-- The pads, drawn before the commitment. -/
  Pads : Type
  [fintype : Fintype Pads]
  [nonempty : Nonempty Pads]
  /-- Circuit `i`'s honest input. -/
  wit : (i : Fin m) → I → Pads → In i
  /-- The phase's honest prover. -/
  prover : Stmt → I → Pads → CausalTranscript A.spec
  /-- The completeness event charged to round `j`, at the challenge vector. -/
  bad : (j : A.spec.ChallengeIdx) → Stmt → I → A.spec.Challenges → Prop
  /-- Outside the events, the verifier's check passes. -/
  ok_honest : ∀ x y, (x, y) ∈ relI → ∀ π ch, AvoidsEvents bad x y ch →
    A.ok x ((prover x y π).transcript ch) = true
  /-- Outside the events, every circuit's honest input lies in its domain at its public
  input. -/
  dom_honest : ∀ x y, (x, y) ∈ relI → ∀ π ch, AvoidsEvents bad x y ch → ∀ i,
    dom i (A.pub i x ((prover x y π).transcript ch)) (wit i y π)
  /-- The honest transcript has the simulator's law. -/
  identDistrib : ∀ x y, (x, y) ∈ relI → ∀ ch, (fun π => (prover x y π).transcript ch) =ᵈ S.sim x ch

attribute [instance] Honest.fintype Honest.nonempty

variable {A} {I : Type} {relI : Set (Stmt × I)} {In : Fin m → Type}
  {dom : ∀ i, Pub i → In i → Prop} {S : A.Sim}

/-- The challenges avoid every completeness event of the honest phase `Ah`. -/
abbrev Honest.Avoids (Ah : A.Honest I relI In dom S) (x : Stmt) (y : I) (ch : A.spec.Challenges) :
    Prop :=
  AvoidsEvents Ah.bad x y ch

open Classical in
/-- **The probabilities of the completeness events**: on the relation, at every challenge vector
`ch`, the event of round `j` has probability at most `δ j` over the challenge of round `j` with the
other challenges those of `ch` (so the event may depend on every challenge, and the union bound
over the rounds still gives `∑ j, δ j`). -/
def Honest.BadBound (Ah : A.Honest I relI In dom S) (δ : A.spec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ j x y, (x, y) ∈ relI → ∀ ch : A.spec.Challenges,
    Pr[c ← A.spec.Challenge j : Ah.bad j x y (Function.update ch j c)] ≤ δ j

open Classical in
/-- `BadBound` as a count: at every challenge vector `ch`, at most `δ j · |C_j|` challenges of
round `j` make the event of round `j` occur. -/
theorem Honest.BadBound.card_le {Ah : A.Honest I relI In dom S} {δ : A.spec.ChallengeIdx → ℝ≥0}
    (h : Ah.BadBound δ) (j x y) (hy : (x, y) ∈ relI) (ch : A.spec.Challenges) :
    ((Finset.univ.filter fun c => Ah.bad j x y (Function.update ch j c)).card : ℝ≥0) ≤
      δ j * Fintype.card (A.spec.Challenge j) :=
  (card_le_iff_probUniform_le _ _ _).mpr (h j x y hy ch)

/-- **The completeness error of the honest phase** `e`: on the relation, the challenges meet some
completeness event with probability at most `e` (the events taken together, whatever the rounds
they are charged to). -/
def Honest.ErrorBound (Ah : A.Honest I relI In dom S) (e : Stmt → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relI → Pr[ch ← A.spec.Challenges : ¬ Ah.Avoids x y ch] ≤ e x

/-- **The completeness error of the honest phase over the prover's coins** `e`, for honest inputs
`J` related to statements by `relJ` and read with uniform coins `ω` as the honest inputs
`inp y ω`: on `relJ`, over uniform coins and challenges, the input with its coins is off `relI` or
the challenges meet some completeness event with probability at most `e`. -/
def Honest.CoinErrorBound (Ah : A.Honest I relI In dom S) {J Ω : Type} [Fintype Ω] [Nonempty Ω]
    (relJ : Set (Stmt × J)) (inp : J → Ω → I) (e : Stmt → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relJ → Pr[u ← (Ω × A.spec.Challenges) :
    (x, inp y u.1) ∉ relI ∨ ¬ Ah.Avoids x (inp y u.1) u.2] ≤ e x

end RealizedProgram.ProofSystem.PhaseStep

end GordieHowe
