-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.Model.IOP.PadMasked
public import GordieHowe.Headline

@[expose] public section

/-!
# Phased application phases

A **phased application phase** (the GordieHowe core's phases, the paper's Section 5.3, Phases and
late values) has `K` phases. Phase `k` is a challenge round, drawing one challenge of type `Ch k`
(the product of the phase's named challenges), followed by one message round, in which the prover
sends `t = x + P` for every late value `x` of phase `k`, with `P` its pad, uniform over the value's
masking space and committed before the first challenge. The layout of the rounds is `PhaseLayout`:
the challenge types, the late values (`Late`, in declaration order), the phase of each late value
and its masking space. A run of the phase is a `PhaseLayout.Run`: the challenges and the messages.

The data of an application phase (`Phased`) are read from the run: the verifier's check, the
public inputs of the circuits, the extraction, an event per phase (supplied by the lowerings),
and soundness. `Phased.toAppPhase` is the `GordieHowe.RealizedProgram.ProofSystem.PhaseStep` on the protocol `PhaseLayout.spec` of `2 · K`
rounds (round `2k` is the challenge of phase `k`, round `2k + 1` its message), with the errors
`PhaseLayout.error` (`Phased.eventBound_toAppPhase`).

Phases enter as data, and the conditions the GordieHowe core checks on them are named predicates
on the data:

* **The challenge-use rule** (`PhaseLayout.ChallengeUse`, a field of `Phased`): the event of phase
  `k` reads only the values fixed before the challenge of phase `k` is drawn (the committed
  witnesses, the challenges of earlier phases and the messages of earlier phases) and the
  challenge itself. It is the Lean form of the core's challenge-use rule
  (`lib/gordiehowe/system.h`, the challenge-use check): a constraint that reads a challenge reads
  only values fixed before it or computed from it, so the event bounds a value the prover chose
  before seeing the challenge; the challenge's inferred tests are what its event reads.
* **Late values are computed after their phase's challenge** (`PhaseLayout.ChallengeCausal`, a
  field of `Phased.Honest`): the honest value of a late value of phase `k` reads only the
  challenges of phases at most `k` (the core's phase inference: a value's phase is the largest
  phase among the challenges it depends on).
* **The pad order** (`PhaseLayout.PadOrder`, a field of `Phased.Honest`): the honest value of each
  late value reads only the pads of the messages before it, in the order of the messages by phase
  and then declaration (`PhaseLayout.MsgBefore`; the core's pad-dependency check).

The honest prover (`Phased.Honest`) gives the honest late values as functions of the honest input,
the challenges and the pads. Its simulator (`Phased.Honest.toAppHonest`) sends uniform messages at
the given challenges; it has the honest law by `PadMasked.uniform`, generically.
-/

namespace GordieHowe
open IOP IOP.ProtocolSpec
open scoped NNReal

/-! ### The layout -/

/-- **The layout of a phased application phase** with `K` phases: phase `k` draws a challenge of
type `Ch k` (uniform; the product of the phase's named challenges), then sends the masked late
values of phase `k`. The late values are `Late`, in declaration order; late value `l` belongs to
phase `phase l` and is masked by a pad uniform over its masking space `Mask l` (an additive group:
the field, a subfield, or bits in characteristic 2). -/
structure RealizedProgram.ProofSystem.PhaseLayout (K : ℕ) where
  /-- The challenge of phase `k`. -/
  Ch : Fin K → Type
  [chFintype : ∀ k, Fintype (Ch k)]
  [chDecEq : ∀ k, DecidableEq (Ch k)]
  [chNonempty : ∀ k, Nonempty (Ch k)]
  /-- The late values. -/
  Late : Type
  [lateFintype : Fintype Late]
  /-- The declaration order of the late values. -/
  [lateOrder : LinearOrder Late]
  /-- The phase of a late value. -/
  phase : Late → Fin K
  /-- The masking space of a late value: its pad and its message lie in it. -/
  Mask : Late → Type
  [maskGroup : ∀ l, AddGroup (Mask l)]
  [maskFintype : ∀ l, Fintype (Mask l)]

attribute [instance] RealizedProgram.ProofSystem.PhaseLayout.chFintype RealizedProgram.ProofSystem.PhaseLayout.chDecEq RealizedProgram.ProofSystem.PhaseLayout.chNonempty
  RealizedProgram.ProofSystem.PhaseLayout.lateFintype RealizedProgram.ProofSystem.PhaseLayout.lateOrder RealizedProgram.ProofSystem.PhaseLayout.maskGroup RealizedProgram.ProofSystem.PhaseLayout.maskFintype

namespace RealizedProgram.ProofSystem.PhaseLayout

variable {K : ℕ} (L : PhaseLayout K)

/-- The pads: one for each late value, in its masking space. -/
abbrev Pads : Type := ∀ l, L.Mask l

/-- **A run of the phase**: the challenge of every phase and the message of every late value. -/
@[ext]
structure Run where
  /-- The challenge of phase `k`. -/
  chal : ∀ k, L.Ch k
  /-- The message `x + P` of late value `l`. -/
  msg : ∀ l, L.Mask l

variable {L}

/-- The run with the challenge of phase `k` replaced by `c`. -/
def Run.setChal (r : L.Run) (k : Fin K) (c : L.Ch k) : L.Run :=
  ⟨Function.update r.chal k c, r.msg⟩

@[simp] theorem Run.setChal_chal_self (r : L.Run) (k : Fin K) (c : L.Ch k) :
    (r.setChal k c).chal k = c :=
  Function.update_self k c r.chal

theorem Run.setChal_chal_of_ne (r : L.Run) {k k' : Fin K} (c : L.Ch k) (h : k' ≠ k) :
    (r.setChal k c).chal k' = r.chal k' :=
  Function.update_of_ne h c r.chal

@[simp] theorem Run.setChal_msg (r : L.Run) (k : Fin K) (c : L.Ch k) :
    (r.setChal k c).msg = r.msg :=
  rfl

/-- **Two runs agree through the challenge of phase `k`**: on the challenges of phases at most `k`
and on the messages of phases before `k`, the values fixed when the challenge of phase `k` is
drawn. -/
structure Run.EqThrough (k : Fin K) (r r' : L.Run) : Prop where
  /-- The challenges of phases at most `k` agree. -/
  chal : ∀ k' ≤ k, r.chal k' = r'.chal k'
  /-- The messages of phases before `k` agree. -/
  msg : ∀ l, L.phase l < k → r.msg l = r'.msg l

variable (L)

/-- **The challenge-use rule**: the event `ev k` of phase `k` reads only what is fixed when the
challenge of phase `k` is drawn and that challenge (`Run.EqThrough`). See the module docstring for
the C++ check it mirrors. -/
def ChallengeUse (ev : Fin K → L.Run → Prop) : Prop :=
  ∀ k ⦃r r' : L.Run⦄, r.EqThrough k r' → (ev k r ↔ ev k r')

/-- **Late values are computed after their phase's challenge**: the value `f c l` of a late value
of phase `k` reads only the challenges `c k'` of phases `k' ≤ k`. -/
def ChallengeCausal (f : (∀ k, L.Ch k) → ∀ l, L.Mask l) : Prop :=
  ∀ l ⦃c c' : ∀ k, L.Ch k⦄, (∀ k ≤ L.phase l, c k = c' k) → f c l = f c' l

/-- **The order of the messages**: by phase, then by declaration. -/
def MsgBefore (l l' : L.Late) : Prop :=
  toLex (L.phase l, l) < toLex (L.phase l', l')

/-- The order of the messages is well founded (the late values are finite). -/
theorem msgBefore_wellFounded : WellFounded L.MsgBefore :=
  InvImage.wf (fun l => toLex (L.phase l, l)) wellFounded_lt

/-- **The pad order**: at every challenge vector, the value of each late value reads only the
pads of the messages before it (`PadMasked` along `MsgBefore`). -/
def PadOrder (late : (∀ k, L.Ch k) → L.Pads → ∀ l, L.Mask l) : Prop :=
  ∀ c, PadMasked L.MsgBefore fun l π => late c π l

/-- **The honest run**: the challenges `c` and, for every late value, its value plus its pad. -/
def honestRun (late : (∀ k, L.Ch k) → L.Pads → ∀ l, L.Mask l) (c : ∀ k, L.Ch k) (π : L.Pads) :
    L.Run :=
  ⟨c, PadMasked.messages (fun l π => late c π l) π⟩

variable {L} in
/-- Under the pad order, the honest messages at fixed challenges are uniform. -/
theorem PadOrder.uniform {late : (∀ k, L.Ch k) → L.Pads → ∀ l, L.Mask l} (h : L.PadOrder late)
    (c : ∀ k, L.Ch k) : Uniform fun π => (L.honestRun late c π).msg :=
  (h c).uniform L.msgBefore_wellFounded

/-- **The runs as pairs** of the challenges and the messages. -/
def Run.equivProd : L.Run ≃ (∀ k, L.Ch k) × L.Pads where
  toFun r := (r.chal, r.msg)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The runs are finite. -/
instance Run.instFintype : Fintype L.Run := Fintype.ofEquiv _ (Run.equivProd L).symm

/-- The runs are nonempty: every masking space has a zero. -/
instance Run.instNonempty : Nonempty L.Run := ⟨⟨fun _ => Classical.arbitrary _, fun _ => 0⟩⟩

variable {L} in
/-- **Paper `lem:phases` (3)**: under the pad order, the honest run under uniform challenges and
uniform pads has the law of the uniform simulator, which draws the challenge of every phase and the
message of every late value (in its masking space, the space of its pad) uniformly and
independently: the honest run is uniform on the runs. At fixed challenges the messages are uniform
(`PadOrder.uniform`, from `PadMasked.uniform`). -/
@[headline]
theorem PadOrder.honestRun_uniform {late : (∀ k, L.Ch k) → L.Pads → ∀ l, L.Mask l}
    (h : L.PadOrder late) : Uniform fun x : (∀ k, L.Ch k) × L.Pads => L.honestRun late x.1 x.2 := by
  have h₁ := IdentDistrib.dependent (f₁ := fun c : ∀ k, L.Ch k => c) (g₁ := fun c => c)
    (f₂ := fun c π => (L.honestRun late c π).msg) (g₂ := fun _ (m : L.Pads) => m)
    (IdentDistrib.refl _) fun c => h.uniform c
  exact (h₁.comp (Run.equivProd L).symm).trans
    (IdentDistrib.of_equiv (Run.equivProd L).symm fun _ => rfl)

variable {L} in
/-- The honest messages are computed after their phase's challenge when the values are. -/
theorem ChallengeCausal.honestRun {late : (∀ k, L.Ch k) → L.Pads → ∀ l, L.Mask l} (π : L.Pads)
    (h : L.ChallengeCausal fun c => late c π) :
    L.ChallengeCausal fun c => (L.honestRun late c π).msg :=
  fun l _ _ hc => congrArg (· + π l) (h l hc)

/-! ### The protocol -/

/-- The phase of round `i`: rounds `2k` and `2k + 1` belong to phase `k`. -/
def roundPhase (i : Fin (2 * K)) : Fin K := ⟨i / 2, by omega⟩

/-- The challenge round of phase `k`. -/
def chalRound (k : Fin K) : Fin (2 * K) := ⟨2 * k, by omega⟩

/-- The message round of phase `k`. -/
def msgRound (k : Fin K) : Fin (2 * K) := ⟨2 * k + 1, by omega⟩

@[simp] theorem roundPhase_chalRound (k : Fin K) : roundPhase (chalRound k) = k :=
  Fin.ext (by simp only [roundPhase, chalRound]; omega)

@[simp] theorem roundPhase_msgRound (k : Fin K) : roundPhase (msgRound k) = k :=
  Fin.ext (by simp only [roundPhase, msgRound]; omega)

/-- The message of phase `k`: one masked value for every late value of phase `k`. -/
def PhaseMsg (k : Fin K) : Type := (l : {l : L.Late // L.phase l = k}) → L.Mask l

instance (k : Fin K) : Nonempty (L.PhaseMsg k) := inferInstanceAs (Nonempty (∀ _, _))

/-- **The protocol of the phase**: round `2k` is the challenge of phase `k`, round `2k + 1` its
message. -/
def spec : ProtocolSpec (2 * K) where
  dir i := if (i : ℕ) % 2 = 0 then .V_to_P else .P_to_V
  «Type» i := if (i : ℕ) % 2 = 0 then L.Ch (roundPhase i) else L.PhaseMsg (roundPhase i)

variable {L}

theorem spec_dir_eq_V_to_P_iff (i : Fin (2 * K)) : L.spec.dir i = .V_to_P ↔ (i : ℕ) % 2 = 0 := by
  simp only [spec]
  split_ifs with h <;> simp [h]

theorem spec_type_of_even (i : Fin (2 * K)) (h : (i : ℕ) % 2 = 0) :
    L.spec.Type i = L.Ch (roundPhase i) :=
  ite_eq_left h

theorem spec_type_of_odd (i : Fin (2 * K)) (h : ¬ (i : ℕ) % 2 = 0) :
    L.spec.Type i = L.PhaseMsg (roundPhase i) :=
  ite_eq_right h

theorem spec_type_chalRound (k : Fin K) : L.spec.Type (chalRound k) = L.Ch k := by
  rw [spec_type_of_even _ (by simp [chalRound]), roundPhase_chalRound]

theorem spec_type_msgRound (k : Fin K) : L.spec.Type (msgRound k) = L.PhaseMsg k := by
  rw [spec_type_of_odd _ (by simp [msgRound]), roundPhase_msgRound]

theorem spec_challenge_eq (j : L.spec.ChallengeIdx) :
    L.spec.Challenge j = L.Ch (roundPhase j.1) :=
  spec_type_of_even j.1 ((spec_dir_eq_V_to_P_iff j.1).mp j.2)

instance (j : L.spec.ChallengeIdx) : Fintype (L.spec.Challenge j) :=
  Fintype.ofEquiv _ (Equiv.cast (spec_challenge_eq j)).symm

instance (j : L.spec.ChallengeIdx) : DecidableEq (L.spec.Challenge j) :=
  (Equiv.cast (spec_challenge_eq j)).decidableEq

instance (j : L.spec.ChallengeIdx) : Nonempty (L.spec.Challenge j) :=
  (Equiv.cast (spec_challenge_eq j)).nonempty

instance (i : Fin (2 * K)) : Nonempty (L.spec.Type i) := by
  by_cases h : (i : ℕ) % 2 = 0
  · rw [spec_type_of_even i h]
    infer_instance
  · rw [spec_type_of_odd i h]
    infer_instance

variable (L) in
/-- The challenge round of phase `k`, as a challenge round of the protocol. -/
def chalIdx (k : Fin K) : L.spec.ChallengeIdx :=
  ⟨chalRound k, (spec_dir_eq_V_to_P_iff _).mpr (by simp [chalRound])⟩

variable (L) in
/-- **The challenge rounds of the protocol are the phases.** -/
def chalIdxEquiv : Fin K ≃ L.spec.ChallengeIdx where
  toFun := L.chalIdx
  invFun j := roundPhase j.1
  left_inv := roundPhase_chalRound
  right_inv j := by
    have h := (spec_dir_eq_V_to_P_iff j.1).mp j.2
    exact Subtype.ext (Fin.ext (by simp only [chalIdx, chalRound, roundPhase]; omega))

theorem chalIdx_injective : Function.Injective L.chalIdx := L.chalIdxEquiv.injective

theorem exists_chalIdx_eq (j : L.spec.ChallengeIdx) : ∃ k, L.chalIdx k = j :=
  L.chalIdxEquiv.surjective j

theorem exists_msgRound_eq (i : L.spec.MessageIdx) : ∃ k, msgRound k = i.1 := by
  have h : ¬ (i.1 : ℕ) % 2 = 0 := fun h => by
    have := (spec_dir_eq_V_to_P_iff (L := L) i.1).mpr h
    rw [i.2] at this
    cases this
  exact ⟨roundPhase i.1, Fin.ext (by simp only [msgRound, roundPhase]; omega)⟩

/-- A challenge of round `j`, read as the challenge of the phase `k` whose challenge round it is. -/
def castCh {j : L.spec.ChallengeIdx} {k : Fin K} (h : L.chalIdx k = j) (c : L.spec.Challenge j) :
    L.Ch k :=
  cast (h ▸ spec_type_chalRound k) c

/-! ### Runs and transcripts -/

variable (L)

/-- The run of a full transcript. -/
def runOf (tr : L.spec.Transcript (Fin.last (2 * K))) : L.Run where
  chal k := cast (spec_type_chalRound k) (tr (chalRound k))
  msg l := cast (spec_type_msgRound (L.phase l)) (tr (msgRound (L.phase l))) ⟨l, rfl⟩

/-- The message of round `i` of the transcript of a run. -/
def roundValue (r : L.Run) (i : Fin (2 * K)) : L.spec.Type i :=
  if h : (i : ℕ) % 2 = 0 then cast (spec_type_of_even i h).symm (r.chal (roundPhase i))
  else cast (spec_type_of_odd i h).symm fun l => r.msg l.1

/-- The full transcript of a run. -/
def transcriptOf (r : L.Run) : L.spec.Transcript (Fin.last (2 * K)) := fun i => L.roundValue r i

/-- The challenge of every phase, read from the challenges of the protocol. -/
def chOf (ch : L.spec.Challenges) : ∀ k, L.Ch k := fun k => L.castCh rfl (ch (L.chalIdx k))

variable {L}

/-- **Updating the challenge round of phase `k`** updates the challenge of phase `k` (at any
decidable equality of the rounds and the phases). -/
theorem chOf_update [DecidableEq L.spec.ChallengeIdx] [DecidableEq (Fin K)] (ch : L.spec.Challenges)
    (k : Fin K) (c : L.spec.Challenge (L.chalIdx k)) :
    L.chOf (Function.update ch (L.chalIdx k) c) =
      Function.update (L.chOf ch) k (L.castCh rfl c) := by
  funext k'
  by_cases h : k' = k
  · subst h
    simp only [chOf, Function.update_self]
  · simp only [chOf, Function.update_of_ne h,
      Function.update_of_ne fun e => h (chalIdx_injective e)]

theorem roundValue_chalRound (r : L.Run) (k : Fin K) :
    L.roundValue r (chalRound k) = cast (spec_type_chalRound k).symm (r.chal k) := by
  have hk : ∀ k' (h : k' = k) (h₁ : L.Ch k' = L.spec.Type (chalRound k)),
      cast h₁ (r.chal k') = cast (spec_type_chalRound k).symm (r.chal k) := by
    rintro k' rfl h₁
    rfl
  rw [roundValue, dite_eq_left (by simp [chalRound])]
  exact hk _ (roundPhase_chalRound k) _

theorem roundValue_msgRound (r : L.Run) (k : Fin K) :
    L.roundValue r (msgRound k) = cast (spec_type_msgRound k).symm fun l => r.msg l.1 := by
  have hk : ∀ k' (h : k' = k) (h₁ : L.PhaseMsg k' = L.spec.Type (msgRound k)),
      cast h₁ (fun l : {l // L.phase l = k'} => r.msg l.1) =
        cast (spec_type_msgRound k).symm fun l => r.msg l.1 := by
    rintro k' rfl h₁
    rfl
  rw [roundValue, dite_eq_right (by simp [msgRound])]
  exact hk _ (roundPhase_msgRound k) _

@[simp] theorem runOf_transcriptOf (r : L.Run) : L.runOf (L.transcriptOf r) = r := by
  ext k
  · change cast _ (L.roundValue r (chalRound k)) = _
    rw [roundValue_chalRound, cast_cast, cast_eq]
  · change (cast (spec_type_msgRound (L.phase k)) (L.roundValue r (msgRound (L.phase k))))
      ⟨k, rfl⟩ = _
    rw [roundValue_msgRound]
    have e : ∀ (f : L.PhaseMsg (L.phase k))
        (h₁ : L.PhaseMsg (L.phase k) = L.spec.Type (msgRound (L.phase k))) h₂,
        cast h₂ (cast h₁ f) = f := fun f h₁ h₂ => by rw [cast_cast, cast_eq]
    exact congrFun (e (fun l => r.msg l.1) _ _) ⟨k, rfl⟩

/-- **Runs of transcripts agreeing through the challenge of phase `k`**: two full transcripts whose
prefixes up to the challenge round of phase `k` are the same prefix followed by `c` and by `c'`
give runs that agree through phase `k` once the second run's challenge of phase `k` is set to
`c`. -/
theorem runOf_eqThrough {k : Fin K} {trp : L.spec.Transcript (L.chalIdx k).1.castSucc}
    {c c' : L.spec.Challenge (L.chalIdx k)} {tr tr' : L.spec.Transcript (Fin.last (2 * K))}
    (h : tr.upTo (L.chalIdx k) = L.spec.concat trp c)
    (h' : tr'.upTo (L.chalIdx k) = L.spec.concat trp c') :
    (L.runOf tr).EqThrough k ((L.runOf tr').setChal k (L.castCh rfl c)) where
  chal k' hk' := by
    rcases eq_or_ne k' k with rfl | hne
    · rw [Run.setChal_chal_self]
      exact congrArg (cast _) (Transcript.apply_of_upTo_eq_concat_self h)
    · rw [Run.setChal_chal_of_ne _ _ hne]
      have hlt : (chalRound k' : ℕ) < (L.chalIdx k).1 := by
        have : (k' : ℕ) < k := lt_of_le_of_ne hk' (fun e => hne (Fin.ext e))
        simp only [chalIdx, chalRound]
        omega
      exact congrArg (cast _) ((Transcript.apply_of_upTo_eq_concat h _ hlt).trans
        (Transcript.apply_of_upTo_eq_concat h' _ hlt).symm)
  msg l hl := by
    have hlt : (msgRound (L.phase l) : ℕ) < (L.chalIdx k).1 := by
      have : (L.phase l : ℕ) < k := hl
      simp only [chalIdx, chalRound, msgRound]
      omega
    exact congrFun (congrArg (cast _) ((Transcript.apply_of_upTo_eq_concat h _ hlt).trans
      (Transcript.apply_of_upTo_eq_concat h' _ hlt).symm)) _

/-- **The transcripts of runs computed from the challenges**: the run with the challenges `c` and
the messages `msg c`, as a causal transcript family. The messages must be computed after their
phase's challenge (`ChallengeCausal`). -/
def family (msg : (∀ k, L.Ch k) → ∀ l, L.Mask l) (h : L.ChallengeCausal msg) :
    CausalTranscript L.spec where
  transcript ch := L.transcriptOf ⟨L.chOf ch, msg (L.chOf ch)⟩
  challenge ch j := by
    obtain ⟨k, rfl⟩ := exists_chalIdx_eq j
    change L.roundValue _ (chalRound k) = _
    rw [roundValue_chalRound]
    change cast _ (cast _ (ch (L.chalIdx k))) = _
    rw [cast_cast]
    exact eq_of_heq (cast_heq _ _)
  causal i ch ch' hch := by
    obtain ⟨k, hk⟩ := exists_msgRound_eq i
    have hc : ∀ k' ≤ k, L.chOf ch k' = L.chOf ch' k' := fun k' hk' => by
      refine congrArg (L.castCh rfl) (hch (L.chalIdx k') ?_)
      rw [← hk]
      change (2 * (k' : ℕ)) < 2 * (k : ℕ) + 1
      have : (k' : ℕ) ≤ k := hk'
      omega
    rw [← hk]
    change L.roundValue _ (msgRound k) = L.roundValue _ (msgRound k)
    rw [roundValue_msgRound, roundValue_msgRound]
    congr 1
    funext l
    change msg (L.chOf ch) l.1 = msg (L.chOf ch') l.1
    exact h l.1 fun k' hk' => hc k' (l.2 ▸ hk')

theorem family_transcript (msg : (∀ k, L.Ch k) → ∀ l, L.Mask l) (h : L.ChallengeCausal msg)
    (ch : L.spec.Challenges) :
    (L.family msg h).transcript ch = L.transcriptOf ⟨L.chOf ch, msg (L.chOf ch)⟩ :=
  rfl

variable (L) in
/-- The errors of the protocol by challenge round, from errors `ε k` by phase. -/
def error (ε : Fin K → ℝ≥0) (j : L.spec.ChallengeIdx) : ℝ≥0 := ε (L.chalIdxEquiv.symm j)

@[simp] theorem error_chalIdx (ε : Fin K → ℝ≥0) (k : Fin K) : L.error ε (L.chalIdx k) = ε k :=
  congrArg ε (L.chalIdxEquiv.symm_apply_apply k)

/-- The errors of the protocol sum to the errors of the phases. -/
theorem sum_error (ε : Fin K → ℝ≥0) : ∑ j, L.error ε j = ∑ k, ε k :=
  Fintype.sum_equiv L.chalIdxEquiv.symm _ _ fun _ => rfl

end RealizedProgram.ProofSystem.PhaseLayout

/-! ### The phased application phase -/

/-- **A phased application phase** for the relation `rel`, linking `m` circuits, on the layout
`L`: the verifier's check, the circuits' public inputs, the extraction (computable, polynomial
time), the event of each phase, all read from the run; the challenge-use rule for the events;
and soundness: on a run the verifier's check passes, if every circuit's relation holds at its
public input then `extract` gives a witness in the relation or the event of some phase occurred.
The events' probabilities are `Phased.EventBound`. -/
structure RealizedProgram.ProofSystem.Phased (Stmt W : Type) (rel : Set (Stmt × W)) {m : ℕ} (Pub Wit : Fin m → Type)
    (holds : ∀ i, Pub i → Wit i → Prop) {K : ℕ} (L : PhaseLayout K) where
  /-- The verifier's check on the statement and the run. -/
  ok : Stmt → L.Run → Bool
  /-- The public input of circuit `i`. -/
  pub : (i : Fin m) → Stmt → L.Run → Pub i
  /-- The witness extracted from the circuits' witnesses. -/
  extract : (∀ i, Wit i) → Option W
  /-- The event charged at the challenge of phase `k`, given the circuits' witnesses, the
  statement and the run. -/
  event : Fin K → (∀ i, Wit i) → Stmt → L.Run → Prop
  /-- The challenge-use rule: the event of phase `k` reads the run only through `Run.EqThrough` at
  phase `k`, that is the challenges of phases at most `k` and the messages of phases before `k`. -/
  challengeUse : ∀ w x, L.ChallengeUse fun k => event k w x
  /-- The circuits' relations at their public inputs give the relation on the extracted witness
  or an event. -/
  sound : ∀ x w r, ok x r = true → AllHold holds (fun i => pub i x r) w →
    PhaseStep.Extracts rel extract x w ∨ ∃ k, event k w x r

namespace RealizedProgram.ProofSystem.Phased

variable {Stmt W : Type} {rel : Set (Stmt × W)} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop} {K : ℕ} {L : PhaseLayout K}
  (P : Phased Stmt W rel Pub Wit holds L)

open Classical in
/-- **The errors of a phased application phase**: at every run, the event of phase `k` has
probability at most `ε k` over the challenge of phase `k`. By the challenge-use rule, only the
values fixed before that challenge matter. -/
def EventBound (ε : Fin K → ℝ≥0) : Prop :=
  ∀ k w x (r : L.Run), Pr[c ← L.Ch k : P.event k w x (r.setChal k c)] ≤ ε k

/-- **The phased application phase as an application phase**, on the protocol `L.spec`. The event
of a challenge round `j` is the event of its phase on any full transcript that extends the prefix;
by the challenge-use rule the choice of extension does not matter. -/
def toAppPhase : PhaseStep Stmt W rel Pub Wit holds where
  n := 2 * K
  spec := L.spec
  ok x tr := P.ok x (L.runOf tr)
  pub i x tr := P.pub i x (L.runOf tr)
  extract := P.extract
  event j w x trp := ∃ k, L.chalIdx k = j ∧
    ∃ tr : L.spec.Transcript (Fin.last (2 * K)), tr.upTo j = trp ∧ P.event k w x (L.runOf tr)
  sound x w tr hok hw := (P.sound x w (L.runOf tr) hok hw).imp id
    fun ⟨k, hk⟩ => ⟨L.chalIdx k, k, rfl, tr, rfl, hk⟩

/-- The event of the challenge round of phase `k` is the event of phase `k` on a full transcript
extending the prefix. -/
theorem toAppPhase_event_chalIdx_iff (k : Fin K) (w : ∀ i, Wit i) (x : Stmt)
    (trp : L.spec.Transcript (L.chalIdx k).1.succ) :
    P.toAppPhase.event (L.chalIdx k) w x trp ↔
      ∃ tr : L.spec.Transcript (Fin.last (2 * K)), tr.upTo (L.chalIdx k) = trp ∧
        P.event k w x (L.runOf tr) := by
  refine ⟨fun ⟨k', hk', h⟩ => ?_, fun h => ⟨k, rfl, h⟩⟩
  obtain rfl := PhaseLayout.chalIdx_injective hk'
  exact h

/-- **The errors of the phased application phase as an application phase**: `L.error ε`. -/
theorem eventBound_toAppPhase {ε : Fin K → ℝ≥0} (h : P.EventBound ε) :
    P.toAppPhase.EventBound (L.error ε) := by
  intro j w x trp
  obtain ⟨k, rfl⟩ := PhaseLayout.exists_chalIdx_eq j
  have hext : ∀ c, ∃ tr : L.spec.Transcript (Fin.last (2 * K)),
      tr.upTo (L.chalIdx k) = L.spec.concat trp c := fun c => Transcript.exists_take_eq _
  choose ext hext using hext
  let r₀ := L.runOf (ext (Classical.arbitrary _))
  have key : ∀ c, P.toAppPhase.event (L.chalIdx k) w x (L.spec.concat trp c) ↔
      P.event k w x (r₀.setChal k (L.castCh rfl c)) := fun c => by
    rw [toAppPhase_event_chalIdx_iff]
    constructor
    · rintro ⟨tr, htr, hev⟩
      exact (P.challengeUse w x k (PhaseLayout.runOf_eqThrough htr (hext _))).mp hev
    · intro hev
      exact ⟨ext c, hext c,
        (P.challengeUse w x k (PhaseLayout.runOf_eqThrough (hext c) (hext _))).mpr hev⟩
  change Pr[c ← L.spec.Challenge (L.chalIdx k) : _] ≤ L.error ε (L.chalIdx k)
  rw [PhaseLayout.error_chalIdx]
  calc Pr[c ← L.spec.Challenge (L.chalIdx k) :
        P.toAppPhase.event (L.chalIdx k) w x (L.spec.concat trp c)]
      = Pr[c ← L.spec.Challenge (L.chalIdx k) : P.event k w x (r₀.setChal k (L.castCh rfl c))] := by
        congr 1
        funext c
        exact propext (key c)
    _ = Pr[c ← L.Ch k : P.event k w x (r₀.setChal k c)] :=
        probUniform_cast (α := L.spec.Challenge (L.chalIdx k)) (PhaseLayout.spec_type_chalRound k)
          fun c => P.event k w x (r₀.setChal k c)
    _ ≤ ε k := h k w x r₀

/-! ### The honest prover -/

/-- **The honest prover of a phased application phase**, on honest inputs `I` related to statements
by `relI`, for circuits with honest inputs `In i` in the domains `dom i`: the pads (`L.Pads`, drawn
before the commitment) fix every circuit's honest input (`wit`, which may commit pad copies); the
honest value of every late value (`late`), computed after its phase's challenge
(`challengeCausal`) and reading only the pads of earlier messages (`padOrder`); completeness
events `bad k` charged to phase `k`, which may read the challenges of every phase (probabilities
over phase `k`'s challenge, whatever the others, `Honest.BadBound`), outside which the verifier's
check passes and every circuit's honest input lies in its domain on the honest run. -/
structure Honest (I : Type) (relI : Set (Stmt × I)) (In : Fin m → Type)
    (dom : ∀ i, Pub i → In i → Prop) where
  /-- Circuit `i`'s honest input. -/
  wit : (i : Fin m) → I → L.Pads → In i
  /-- The honest value of every late value, from the honest input, the challenges and the pads. -/
  late : I → (∀ k, L.Ch k) → L.Pads → ∀ l, L.Mask l
  /-- Every late value is computed after its phase's challenge. -/
  challengeCausal : ∀ y π, L.ChallengeCausal fun c => late y c π
  /-- Every late value reads only the pads of earlier messages. -/
  padOrder : ∀ y, L.PadOrder (late y)
  /-- The completeness event charged to phase `k`, at the challenges of every phase. -/
  bad : (k : Fin K) → Stmt → I → (∀ k, L.Ch k) → Prop
  /-- Outside the events, the verifier's check passes on the honest run. -/
  ok_honest : ∀ x y, (x, y) ∈ relI → ∀ π c, (∀ k, ¬ bad k x y c) →
    P.ok x (L.honestRun (late y) c π) = true
  /-- Outside the events, every circuit's honest input lies in its domain on the honest run. -/
  dom_honest : ∀ x y, (x, y) ∈ relI → ∀ π c, (∀ k, ¬ bad k x y c) → ∀ i,
    dom i (P.pub i x (L.honestRun (late y) c π)) (wit i y π)

variable {P} {I : Type} {relI : Set (Stmt × I)} {In : Fin m → Type}
  {dom : ∀ i, Pub i → In i → Prop}

open Classical in
/-- **The probabilities of the completeness events**: on the relation, at the challenges `c` of
every phase, the event of phase `k` has probability at most `δ k` over the challenge of phase `k`
with the other phases' challenges those of `c` (an event may depend on the challenges of earlier
phases, through the late values they fix; the union bound over the phases gives `∑ k, δ k`). -/
def Honest.BadBound (Ph : P.Honest I relI In dom) (δ : Fin K → ℝ≥0) : Prop :=
  ∀ k x y, (x, y) ∈ relI → ∀ c : ∀ k, L.Ch k,
    Pr[c' ← L.Ch k : Ph.bad k x y (Function.update c k c')] ≤ δ k

/-- **The completeness error of the honest phased prover** `e`: on the relation, the challenges of
the phases meet some completeness event with probability at most `e` (the events taken together,
whatever the phases they are charged to). -/
def Honest.ErrorBound (Ph : P.Honest I relI In dom) (e : Stmt → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relI → Pr[c ← (∀ k, L.Ch k) : ∃ k, Ph.bad k x y c] ≤ e x

/-- **The completeness error of the honest phased prover over the prover's coins** `e`
(`PhaseStep.Honest.CoinErrorBound`): on `relJ`, over uniform coins `ω` and uniform challenges of the
phases, the input `inp y ω` is off `relI` or the challenges meet some completeness event with
probability at most `e`. -/
def Honest.CoinErrorBound (Ph : P.Honest I relI In dom) {J Ω : Type} [Fintype Ω] [Nonempty Ω]
    (relJ : Set (Stmt × J)) (inp : J → Ω → I) (e : Stmt → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relJ → Pr[u ← (Ω × ∀ k, L.Ch k) :
    (x, inp y u.1) ∉ relI ∨ ∃ k, Ph.bad k x (inp y u.1) u.2] ≤ e x

/-- **The simulator of a phased application phase**: it sends its coins (one element of each late
value's masking space) as the messages, at the given challenges.

Running time: it writes the challenges and its coins into the transcript. This running time is
argued here, not proved in Lean. -/
def appSim : P.toAppPhase.Sim where
  SimCoins := L.Pads
  sim _ ch s := (L.family (fun _ => s) fun _l _c _c' _h => rfl).transcript ch

/-- **The honest prover as that of an application phase.** The honest prover sends the honest run's
messages; it is simulated by `appSim`, whose law is the honest one by `PadMasked.uniform` (the pad
order). -/
def Honest.toAppHonest (Ph : P.Honest I relI In dom) : P.toAppPhase.Honest I relI In dom P.appSim where
  Pads := L.Pads
  wit := Ph.wit
  prover _ y π := L.family (fun c => (L.honestRun (Ph.late y) c π).msg)
    ((Ph.challengeCausal y π).honestRun π)
  bad j x y ch := ∃ k, L.chalIdx k = j ∧ Ph.bad k x y (L.chOf ch)
  ok_honest x y hy π ch hch := by
    change P.ok x (L.runOf (L.transcriptOf _)) = true
    rw [PhaseLayout.runOf_transcriptOf]
    exact Ph.ok_honest x y hy π (L.chOf ch) fun k hk => hch (L.chalIdx k) ⟨k, rfl, hk⟩
  dom_honest x y hy π ch hch i := by
    change dom i (P.pub i x (L.runOf (L.transcriptOf _))) _
    rw [PhaseLayout.runOf_transcriptOf]
    exact Ph.dom_honest x y hy π (L.chOf ch) (fun k hk => hch (L.chalIdx k) ⟨k, rfl, hk⟩) i
  identDistrib _ y _ ch :=
    ((Ph.padOrder y).uniform (L.chOf ch)).comp fun s => L.transcriptOf ⟨L.chOf ch, s⟩

/-- The completeness event of the challenge round of phase `k` is the event of phase `k`. -/
theorem Honest.toAppHonest_bad_chalIdx_iff (Ph : P.Honest I relI In dom) (k : Fin K) (x : Stmt)
    (y : I) (ch : L.spec.Challenges) :
    Ph.toAppHonest.bad (L.chalIdx k) x y ch ↔ Ph.bad k x y (L.chOf ch) := by
  change (∃ k', L.chalIdx k' = L.chalIdx k ∧ Ph.bad k' x y (L.chOf ch)) ↔ _
  refine ⟨fun ⟨k', hk', h⟩ => ?_, fun h => ⟨k, rfl, h⟩⟩
  obtain rfl := PhaseLayout.chalIdx_injective hk'
  exact h

/-- **The completeness error of the honest phase as an application phase** is its own: the
challenges of the phases are uniform among the challenges of the application phase
(`QROM.probUniform_restrict` at the challenge rounds). -/
theorem Honest.errorBound_toAppHonest {Ph : P.Honest I relI In dom} {e : Stmt → ℝ≥0}
    (h : Ph.ErrorBound e) : Ph.toAppHonest.ErrorBound e := by
  classical
  intro x y hy
  have hE : ∀ ch : L.spec.Challenges,
      ¬ Ph.toAppHonest.Avoids x y ch ↔ ∃ k, Ph.bad k x y (L.chOf ch) := fun ch => by
    unfold PhaseStep.Honest.Avoids PhaseStep.AvoidsEvents
    push Not
    exact ⟨fun ⟨j, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨L.chalIdx k, k, rfl, hk⟩⟩
  refine (QROM.probUniform_mono fun ch hc => (hE ch).1 hc).trans (le_of_eq_of_le ?_ (h x y hy))
  exact QROM.probUniform_restrict L.chalIdx PhaseLayout.chalIdx_injective
    (fun k => Equiv.cast (PhaseLayout.spec_type_chalRound k)) fun c => ∃ k, Ph.bad k x y c

/-- **The completeness error over the coins of the honest phase as an application phase** is its
own (as `errorBound_toAppHonest`, at every value of the coins). -/
theorem Honest.coinErrorBound_toAppHonest {Ph : P.Honest I relI In dom} {J Ω : Type} [Fintype Ω]
    [Nonempty Ω] {relJ : Set (Stmt × J)} {inp : J → Ω → I} {e : Stmt → ℝ≥0}
    (h : Ph.CoinErrorBound relJ inp e) : Ph.toAppHonest.CoinErrorBound relJ inp e := by
  classical
  intro x y hy
  have hE : ∀ (ω : Ω) (ch : L.spec.Challenges),
      ¬ Ph.toAppHonest.Avoids x (inp y ω) ch ↔ ∃ k, Ph.bad k x (inp y ω) (L.chOf ch) :=
    fun ω ch => by
      unfold PhaseStep.Honest.Avoids PhaseStep.AvoidsEvents
      push Not
      exact ⟨fun ⟨j, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨L.chalIdx k, k, rfl, hk⟩⟩
  refine le_of_eq_of_le (probUniform_prod_congr_snd fun ω => ?_) (h x y hy)
  have hp : (fun c => (x, inp y ω) ∉ relI ∨ ¬ Ph.toAppHonest.Avoids x (inp y ω) c) =
      fun c => (x, inp y ω) ∉ relI ∨ ∃ k, Ph.bad k x (inp y ω) (L.chOf c) :=
    funext fun c => propext (or_congr Iff.rfl (hE ω c))
  refine (congrArg (fun E => Pr[c ← L.spec.Challenges : E c]) hp).trans ?_
  exact QROM.probUniform_restrict L.chalIdx PhaseLayout.chalIdx_injective
    (fun k => Equiv.cast (PhaseLayout.spec_type_chalRound k))
    fun c => (x, inp y ω) ∉ relI ∨ ∃ k, Ph.bad k x (inp y ω) c

/-- **The probabilities of the honest phase as an application phase**: `L.error δ`. -/
theorem Honest.badBound_toAppHonest (Ph : P.Honest I relI In dom) {δ : Fin K → ℝ≥0}
    (h : Ph.BadBound δ) : Ph.toAppHonest.BadBound (L.error δ) := by
  intro j x y hy ch
  obtain ⟨k, rfl⟩ := PhaseLayout.exists_chalIdx_eq j
  change Pr[c ← L.spec.Challenge (L.chalIdx k) : _] ≤ L.error δ (L.chalIdx k)
  rw [PhaseLayout.error_chalIdx]
  calc Pr[c ← L.spec.Challenge (L.chalIdx k) :
        Ph.toAppHonest.bad (L.chalIdx k) x y (Function.update ch (L.chalIdx k) c)]
      = Pr[c ← L.spec.Challenge (L.chalIdx k) :
          Ph.bad k x y (Function.update (L.chOf ch) k (L.castCh rfl c))] := by
        congr 1
        funext c
        exact propext ((Ph.toAppHonest_bad_chalIdx_iff k x y _).trans
          (Iff.of_eq (congrArg (Ph.bad k x y) (PhaseLayout.chOf_update (L := L) ch k c))))
    _ = Pr[c ← L.Ch k : Ph.bad k x y (Function.update (L.chOf ch) k c)] :=
        probUniform_cast (α := L.spec.Challenge (L.chalIdx k)) (PhaseLayout.spec_type_chalRound k)
          fun c => Ph.bad k x y (Function.update (L.chOf ch) k c)
    _ ≤ δ k := h k x y hy (L.chOf ch)

end RealizedProgram.ProofSystem.Phased

end GordieHowe
