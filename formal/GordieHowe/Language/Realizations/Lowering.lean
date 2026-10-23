-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Phased
public import GordieHowe.Foundations.Probability.ChallengeEventCount

@[expose] public section

/-!
# Lowerings

A **lowering** rewrites a source constraint into a lowered constraint over an extended assignment,
adding variables, constraints and challenges. It sends no message of its own and needs no
zero-knowledge argument. The constraints are predicates (a shallow embedding).

**The model** (as in the C++ core): every committed cell, pads included, is fixed at the
commitment, before the first phase; a late value is read as its message minus its pad; the
challenges come in the phase rounds of a `PhaseLayout`. A constraint (`PhaseLayout.Constraint`)
is therefore a predicate on the statement, the committed assignment and the run (the challenges
and the messages).

**The soundness data** (`Lowering src tgt`): a projection from the lowered assignment to the
source assignment, an event per phase obeying the challenge-use rule (`PhaseLayout.ChallengeUse`),
and soundness: where the lowered constraint holds at a run, the source constraint holds on the
projection or some phase's event occurred. The events' probabilities are `Lowering.EventBound`
(over the phase's challenge, everything else fixed, as `Phased.EventBound`).

**Composition** (errors add per phase): sequential, `Lowering.comp`, lowers the output of a
lowering again (`eventBound_comp`). A lowering with no event has error `0`
(`eventBound_of_not_event`), and a lowering of a guarded constraint lowers the unguarded one with
the statement check added (`Lowering.check`, `eventBound_check`).

**The connection to `Phased`**: a lowering from the application relation, with the core's
enforcement of the lowered constraint (`Enforcement`: the verifier's check and the circuits'
relations give the lowered constraint on the decoded assignment), is a phased application phase
(`Lowering.toPhased`, `eventBound_toPhased`).
-/

namespace GordieHowe
open IOP
open scoped NNReal ENNReal

/-! ### Constraints -/

namespace RealizedProgram.ProofSystem.PhaseLayout

variable {K : ℕ} (L : PhaseLayout K)

/-- **A constraint** on assignments of type `A`: a predicate on the statement, the committed
assignment (every committed cell, pads included) and the run (the challenges and the messages; a
late value is read as its message minus its pad). -/
abbrev Constraint (Stmt A : Type) : Type := Stmt → A → L.Run → Prop

variable {L}

namespace Constraint

variable {Stmt A A₁ A₂ B₁ B₂ : Type}

/-- **The constraint of a relation**: `(x, a) ∈ rel`, reading no challenge or message. -/
def ofRel (rel : Set (Stmt × A)) : L.Constraint Stmt A := fun x a _ => (x, a) ∈ rel

/-- **Two constraints on one assignment.** -/
def and (R₁ R₂ : L.Constraint Stmt A) : L.Constraint Stmt A := fun x a r => R₁ x a r ∧ R₂ x a r

/-- **A constraint guarded by a statement check**: `R` at the statements the check `ok` accepts,
nothing at the others. At the check accepting every statement it is `R` by definition
(`bif true then R else True` reduces to `R`), so a system without a statement check lowers its
relation unchanged. -/
def guard (ok : Stmt → Bool) (R : L.Constraint Stmt A) : L.Constraint Stmt A :=
  fun x a r => bif ok x then R x a r else True

/-- **The statement check as a constraint**: `ok x = true`, reading no assignment or run. -/
def check (ok : Stmt → Bool) : L.Constraint Stmt A := fun x _ _ => ok x = true

/-- A guarded constraint gives the constraint where the check accepts. -/
theorem guard_of_check {ok : Stmt → Bool} {R : L.Constraint Stmt A} {x : Stmt} {a : A}
    {r : L.Run} (hok : ok x = true) (h : guard ok R x a r) : R x a r := by
  unfold guard at h
  rwa [hok, Bool.cond_true] at h

/-- Where the check accepts, the constraint gives the guarded one. -/
theorem guard_of {ok : Stmt → Bool} {R : L.Constraint Stmt A} {x : Stmt} {a : A} {r : L.Run}
    (h : ok x = true → R x a r) : guard ok R x a r := by
  unfold guard
  cases hok : ok x
  · exact trivial
  · exact h hok

end Constraint

end RealizedProgram.ProofSystem.PhaseLayout

/-! ### Lowerings -/

open RealizedProgram.ProofSystem.PhaseLayout

/-- **A lowering** from the source constraint `src` on assignments `A` to the lowered constraint
`tgt` on assignments `B`, on the layout `L`: the projection to the source assignment, the event of
each phase (read from the statement, the lowered assignment and the run; the challenge-use rule),
and soundness. The events' probabilities are `Lowering.EventBound`. -/
structure Lowering {K : ℕ} (L : RealizedProgram.ProofSystem.PhaseLayout K) {Stmt A B : Type} (src : L.Constraint Stmt A)
    (tgt : L.Constraint Stmt B) where
  /-- The source assignment of a lowered assignment. -/
  proj : B → A
  /-- The event charged at the challenge of phase `k`. -/
  event : Fin K → Stmt → B → L.Run → Prop
  /-- The challenge-use rule: the event of phase `k` reads the run only through what is fixed
  when the challenge of phase `k` is drawn and that challenge. -/
  challengeUse : ∀ x b, L.ChallengeUse fun k => event k x b
  /-- The lowered constraint gives the source constraint on the projection, or an event. -/
  sound : ∀ x b r, tgt x b r → src x (proj b) r ∨ ∃ k, event k x b r

namespace Lowering

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt A B C : Type} {src : L.Constraint Stmt A}
  {tgt : L.Constraint Stmt B}

/-- **The errors of a lowering**: at every run, the event of phase `k` has probability at most
`ε k` over the challenge of phase `k`. -/
def EventBound (Lw : Lowering L src tgt) (ε : Fin K → ℝ≥0) : Prop :=
  ∀ k x b (r : L.Run), Pr[c ← L.Ch k : Lw.event k x b (r.setChal k c)] ≤ ε k

/-! ### Sequential composition -/

section Comp

variable {mid : L.Constraint Stmt B} {tgt' : L.Constraint Stmt C} {hsrc : L.Constraint Stmt A}
  {hmid : L.Constraint Stmt B} {htgt : L.Constraint Stmt C}

/-- **Sequential composition**: `Lw₂` lowers the output of `Lw₁`. The events of a phase are those
of both. -/
def comp (Lw₂ : Lowering L mid tgt') (Lw₁ : Lowering L src mid) : Lowering L src tgt' where
  proj c := Lw₁.proj (Lw₂.proj c)
  event k x c r := Lw₂.event k x c r ∨ Lw₁.event k x (Lw₂.proj c) r
  challengeUse x c k _ _ h := or_congr (Lw₂.challengeUse x c k h) (Lw₁.challengeUse x _ k h)
  sound x c r h := (Lw₂.sound x c r h).elim
    (fun h' => (Lw₁.sound x _ r h').imp id fun ⟨k, hk⟩ => ⟨k, Or.inr hk⟩)
    fun ⟨k, hk⟩ => Or.inr ⟨k, Or.inl hk⟩

/-- **The errors of a sequential composition add per phase.** -/
theorem eventBound_comp {Lw₂ : Lowering L mid tgt'} {Lw₁ : Lowering L src mid}
    {ε₁ ε₂ : Fin K → ℝ≥0} (h₁ : Lw₁.EventBound ε₁) (h₂ : Lw₂.EventBound ε₂) :
    (Lw₂.comp Lw₁).EventBound (ε₁ + ε₂) := by
  intro k x c r
  rw [Pi.add_apply, add_comm]
  exact probUniform_or_le_add (h₂ k x c r) (h₁ k x _ r)

end Comp

/-! ### Lowerings with no event -/

section Frame

/-- No event: probability `0` at every phase. -/
theorem eventBound_of_not_event {Lw : Lowering L src tgt} (h : ∀ k x b r, ¬ Lw.event k x b r) :
    Lw.EventBound 0 := by
  intro k x b r
  have : {c : L.Ch k | Lw.event k x b (r.setChal k c)} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun c => h k x b _
  simp [probUniform, this]

end Frame

end Lowering

namespace Lowering

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt A B : Type} {src : L.Constraint Stmt A}
  {tgt : L.Constraint Stmt B}

/-- **The statement check of a lowering**: a lowering of the guarded constraint `guard ok src` is a
lowering of `src` itself to the lowered constraint with the check added; same projection and
events. The verifier's check (`Enforcement.ok`) supplies the added conjunct, so a rejected
statement never reaches the source. -/
def check (ok : Stmt → Bool) (Lw : Lowering L (Constraint.guard ok src) tgt) :
    Lowering L src (Constraint.and (Constraint.check ok) tgt) where
  proj := Lw.proj
  event := Lw.event
  challengeUse := Lw.challengeUse
  sound x b r h := (Lw.sound x b r h.2).imp (Constraint.guard_of_check h.1) id

/-- The statement check adds no error. -/
theorem eventBound_check {ok : Stmt → Bool} {Lw : Lowering L (Constraint.guard ok src) tgt}
    {ε : Fin K → ℝ≥0} (h : Lw.EventBound ε) : (Lw.check ok).EventBound ε :=
  h

end Lowering

/-! ### The connection to phased application phases -/

/-- **The core's enforcement of a constraint** `tgt` through `m` circuits: the verifier's check and
the circuits' public inputs, read from the statement and the run; the decoding of an assignment from
the circuits' witnesses; and enforcement: where the check passes and every circuit's relation holds
at its public input, `tgt` holds on the decoded assignment. -/
structure Enforcement {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt B : Type} (tgt : L.Constraint Stmt B)
    {m : ℕ} (Pub Wit : Fin m → Type) (holds : ∀ i, Pub i → Wit i → Prop) where
  /-- The verifier's check on the statement and the run. -/
  ok : Stmt → L.Run → Bool
  /-- The public input of circuit `i`. -/
  pub : (i : Fin m) → Stmt → L.Run → Pub i
  /-- The assignment decoded from the circuits' witnesses. It is part of the extraction, so each
  instance must give a computable, polynomial-time decoding (an obligation of the instance; the
  field itself is any function). -/
  decode : (∀ i, Wit i) → B
  /-- The check and the circuits' relations give `tgt` on the decoded assignment. -/
  enforce : ∀ x w r, ok x r = true → AllHold holds (fun i => pub i x r) w → tgt x (decode w) r

namespace Lowering

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt W B : Type} {rel : Set (Stmt × W)}
  {tgt htgt : L.Constraint Stmt B} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop}

/-- **A lowering of the application relation as a phased application phase**: the verifier's
check and the public inputs of the enforcement, the extraction `proj ∘ decode`, and the lowering's
events on the decoded assignment. -/
def toPhased (Lw : Lowering L (Constraint.ofRel rel) tgt) (E : Enforcement tgt Pub Wit holds) :
    RealizedProgram.ProofSystem.Phased Stmt W rel Pub Wit holds L where
  ok := E.ok
  pub := E.pub
  extract w := some (Lw.proj (E.decode w))
  event k w x r := Lw.event k x (E.decode w) r
  challengeUse w x := Lw.challengeUse x (E.decode w)
  sound x w r hok hw := (Lw.sound x _ r (E.enforce x w r hok hw)).imp (fun h => ⟨_, rfl, h⟩) id

/-- The errors of the phased application phase are the lowering's. -/
theorem eventBound_toPhased {Lw : Lowering L (Constraint.ofRel rel) tgt}
    {E : Enforcement tgt Pub Wit holds} {ε : Fin K → ℝ≥0} (h : Lw.EventBound ε) :
    (Lw.toPhased E).EventBound ε :=
  fun k w x r => h k x (E.decode w) r

end Lowering

end GordieHowe
