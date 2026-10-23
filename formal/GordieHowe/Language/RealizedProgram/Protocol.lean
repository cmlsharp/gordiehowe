-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Source
public import GordieHowe.Model.IOP.Append

@[expose] public section

/-!
# GordieHowe: the source protocol `Π_P₀` of a program

The public-coin protocol the source program denotes (paper, `def:o-semantics`, at the source
program `P₀` of `thm:backend`: the part of role `source` of the realized program, read in place,
`GordieHowe/Language/RealizedProgram/Source.lean`), as a `GordieHowe.IOP.ProtocolSpec` with a deterministic
`GordieHowe.IOP.Verifier` (`GordieHowe/Model/IOP/RBR.lean`):

* the prover sends the phase-`0` values (`Round.commit`: the committed assignment, the committed
  values and the pads of the late values, `def:o-late`; a value bound to its digits is a committed
  source value);
* for each phase `k = 1, …, n`, the verifier sends the source challenges of phase `k`
  (`GordieHowe.RealizedProgram.IsSourceChal`), one per round in declaration order (`Round.chal j`), then the prover
  sends the source late values of phase `k` (`Round.late k`, in the clear,
  `GordieHowe.RealizedProgram.IsSourceLate`); the realization challenges (a table's `α`, a MAC key) and the
  realization late values are not rounds of `Π_P₀`;
* the verifier sends a last challenge `γ_end` from a set of one element (`Round.final`), and accepts
  if the statement passes the program's member checks (`GordieHowe.RealizedProgram.StatementOk`), every source
  predicate holds and every node-typed source value lies in its type (`GordieHowe.RealizedProgram.SourceSatAt`),
  reading every value (`GordieHowe.RealizedProgram.envOf`: the environment of a transcript).

`GordieHowe.RealizedProgram.rounds` lists the rounds; `GordieHowe.RealizedProgram.rank` orders them (strictly increasing along the list,
`GordieHowe.RealizedProgram.rounds_pairwise`).

The bridge to the proof system's event form on the phase layout of the realized program
(`GordieHowe.RealizedProgram.layout`, whose phases carry every challenge and late value; `GordieHowe.RealizedProgram.SourcePred`):

* `GordieHowe.RealizedProgram.loweringOfRbr`: round-by-round knowledge soundness of `Π_P₀` (CMS19 Def. 8.5, worst case
  per prefix, `rbrKnowledgeSoundness`), at the extractor that reads the statement and the phase-`0`
  values (`GordieHowe.RealizedProgram.sourceExtractor`), gives a lowering from the relation to `SourcePred` whose event
  at a phase is the union over its source challenges of "the state flips at this challenge while
  the extractor fails"; `GordieHowe.RealizedProgram.eventBound_loweringOfRbr` bounds it by the sum of that phase's
  errors. It reads `Π_P₀`'s transcript off a run of the layout (`GordieHowe.RealizedProgram.transcriptOf`), which
  carries what the source program reads when the source part is well formed
  (`GordieHowe.RealizedProgram.SourceValid`, `GordieHowe.RealizedProgram.sourceVerifier_transcriptOf`);
* `GordieHowe.RealizedProgram.rbr_of_events`: per-challenge events on environments, each reading only the values
  fixed when its challenge is drawn and of probability at most `ε j`, with "every source predicate
  holds and no event occurred implies the relation at the extractor's witness", give round-by-round
  knowledge soundness of `Π_P₀`, at the state function `GordieHowe.RealizedProgram.eventState` ("past the first
  challenge, and the extractor succeeds or an event occurred at a challenge so far") and the
  errors `ε j` at the rounds of the source challenges and `0` at `γ_end`.
-/

namespace GordieHowe.IOP

variable {n : ℕ} {P : ProtocolSpec n} {StmtIn : Type}

/-- **The prover replaying a full transcript**: it sends the transcript's message at each of its
rounds, whatever it has seen. -/
def Prover.replay (tr : P.Transcript (Fin.last n)) : Prover P StmtIn :=
  fun i _ _ => tr ⟨i.1, by simp⟩

/-- **The replaying prover runs the transcript**: on the transcript's challenges, its first `k`
rounds are the transcript's. -/
theorem Prover.runTo_replay (tr : P.Transcript (Fin.last n)) (x : StmtIn) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (Prover.replay tr).runTo x tr.challenges k hk =
        tr.take ⟨k, by omega⟩ (Fin.le_last _)
  | 0, _ => funext fun i => i.elim0
  | k + 1, hk => by
    rw [Prover.runTo]
    have ih := Prover.runTo_replay tr x k (by omega)
    split <;>
    · simp only [ih]
      exact P.concat_take_succ (j := ⟨k, by omega⟩) (tr.take ⟨k + 1, by omega⟩ (Fin.le_last _))

/-- **A full transcript's first `i + 1` rounds** are its first `i` rounds and its round `i`. -/
theorem ProtocolSpec.concat_take_castSucc (tr : P.Transcript (Fin.last n)) (i : Fin n) :
    P.concat (tr.take i.castSucc (Fin.le_last _)) (tr ⟨i, by simp⟩) =
      tr.take i.succ (Fin.le_last _) :=
  P.concat_take_succ (tr.take i.succ (Fin.le_last _))

/-- **The state flips at challenge round `i`** of the full transcript `tr`: false on the first `i`
rounds, true on the first `i + 1`. -/
def KnowledgeStateFunction.Flips {V : Verifier P StmtIn} (S : KnowledgeStateFunction V)
    (i : P.ChallengeIdx) (x : StmtIn) (tr : P.Transcript (Fin.last n)) : Prop :=
  ¬ S.toFun i.1.castSucc x (tr.take i.1.castSucc (Fin.le_last _)) ∧
    S.toFun i.1.succ x (tr.take i.1.succ (Fin.le_last _))

/-- **Flipping reads the first `i + 1` rounds.** -/
theorem KnowledgeStateFunction.flips_congr {V : Verifier P StmtIn} (S : KnowledgeStateFunction V)
    {i : P.ChallengeIdx} {x : StmtIn} {tr tr' : P.Transcript (Fin.last n)}
    (h : tr.take i.1.succ (Fin.le_last _) = tr'.take i.1.succ (Fin.le_last _)) :
    S.Flips i x tr ↔ S.Flips i x tr' := by
  have h' : tr.take i.1.castSucc (Fin.le_last _) = tr'.take i.1.castSucc (Fin.le_last _) :=
    congrArg (fun t => t.take i.1.castSucc (Fin.castSucc_le_succ i.1)) h
  unfold Flips
  rw [h, h']

/-- **A state true on a full transcript flips at some challenge round of it**
(`KnowledgeStateFunction.exists_flip` at the prover replaying the transcript). -/
theorem KnowledgeStateFunction.exists_flips {V : Verifier P StmtIn} (S : KnowledgeStateFunction V)
    {x : StmtIn} {tr : P.Transcript (Fin.last n)} (h : S.toFun (Fin.last n) x tr) :
    ∃ i : P.ChallengeIdx, S.Flips i x tr := by
  have hrun : (Prover.replay tr).run x tr.challenges = tr := by
    rw [Prover.run, Prover.runTo_replay]
    rfl
  obtain ⟨i, h1, h2⟩ := S.exists_flip (prv := Prover.replay tr) (ch := tr.challenges)
    (hrun ▸ h)
  refine ⟨i, ?_, ?_⟩
  · rwa [Prover.runTo_replay] at h1
  · rw [Prover.runTo_replay] at h2
    have hc : P.concat (tr.take i.1.castSucc (Fin.le_last _)) (tr.challenges i) =
        tr.take i.1.succ (Fin.le_last _) :=
      P.concat_take_succ (j := i.1) (tr.take i.1.succ (Fin.le_last _))
    rw [← hc]
    exact h2

end GordieHowe.IOP

namespace GordieHowe.Lowering

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt A B : Type} {src src' : L.Constraint Stmt A}
  {tgt : L.Constraint Stmt B}

open scoped NNReal

/-- **A lowering to a weaker source constraint**: the same projection and events, the source
constraint weakened along `h`. -/
def weaken (Lw : Lowering L src tgt) (h : ∀ x a r, src x a r → src' x a r) :
    Lowering L src' tgt where
  proj := Lw.proj
  event := Lw.event
  challengeUse := Lw.challengeUse
  sound x b r ht := (Lw.sound x b r ht).imp_left (h x _ r)

/-- **Weakening the source constraint keeps the errors.** -/
theorem eventBound_weaken {Lw : Lowering L src tgt} {h : ∀ x a r, src x a r → src' x a r}
    {ε : Fin K → ℝ≥0} (hε : Lw.EventBound ε) : (Lw.weaken h).EventBound ε :=
  hε

end GordieHowe.Lowering

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP IOP.ProtocolSpec
open scoped NNReal

/-- **A round of `Π_P₀`**: the phase-`0` values, challenge `j`, the late values of phase `k`, or the
last challenge `γ_end`. -/
inductive Round where
  /-- The phase-`0` values. -/
  | commit
  /-- Challenge `j`. -/
  | chal (j : ℕ)
  /-- The late values of phase `k`. -/
  | late (k : ℕ)
  /-- The last challenge `γ_end`. -/
  | final
  deriving DecidableEq, Repr

/-- **Who sends a round**: the verifier the challenges, the prover the values. -/
def Round.dir : Round → Direction
  | .commit => .P_to_V
  | .chal _ => .V_to_P
  | .late _ => .P_to_V
  | .final => .V_to_P

section

variable (ir : RealizedProgram)

/-! ## The rounds -/

/-- **A challenge of a phase the program has** (`1 ≤ phase ≤ phases`), a challenge of the layout. -/
def IsPhaseChal (j : ℕ) : Prop :=
  j < ir.challenges.length ∧ 1 ≤ (ir.challenge j).phase ∧ (ir.challenge j).phase ≤ ir.phases

instance (j : ℕ) : Decidable (ir.IsPhaseChal j) := by unfold IsPhaseChal; infer_instance

/-- **A challenge of `Π_P₀`**: a source challenge (`RealizedProgram.chalIsSource`) of a phase the program
has. -/
def IsSourceChal (j : ℕ) : Prop :=
  j < ir.challenges.length ∧ 1 ≤ (ir.challenge j).phase ∧ (ir.challenge j).phase ≤ ir.phases ∧
    ir.chalIsSource j = true

instance (j : ℕ) : Decidable (ir.IsSourceChal j) := by unfold IsSourceChal; infer_instance

/-- **A late value of `Π_P₀`**: a late value of the layout of role `source`. -/
def IsSourceLate (v : ℕ) : Prop := ir.IsLate v ∧ ir.IsSourceValue v

instance (v : ℕ) : Decidable (ir.IsSourceLate v) := by unfold IsSourceLate; infer_instance

/-- **The source challenges of phase `p`**, in declaration order. -/
def chalsOf (p : ℕ) : List ℕ :=
  (List.range ir.challenges.length).filter fun j =>
    (ir.challenge j).phase == p && ir.chalIsSource j

/-- **The rounds of phase `k + 1`**: its challenges, then its late values. -/
def phaseRounds (k : ℕ) : List Round := (ir.chalsOf (k + 1)).map .chal ++ [.late (k + 1)]

/-- **The rounds of `Π_P₀`**: the phase-`0` values, the rounds of phases `1, …, n`, and `γ_end`. -/
def rounds : List Round :=
  .commit :: ((List.range ir.phases).flatMap ir.phaseRounds ++ [.final])

/-- **The rank of a round**: phase `k`'s challenges between `(2k − 1) B` and `2k B` in declaration
order, its late values at `2k B`, `B` one more than the number of challenges; the rounds are listed
by increasing rank (`rounds_pairwise`). -/
def rank : Round → ℕ
  | .commit => 0
  | .chal j => (2 * (ir.challenge j).phase - 1) * (ir.challenges.length + 1) + j + 1
  | .late k => 2 * k * (ir.challenges.length + 1)
  | .final => (2 * ir.phases + 1) * (ir.challenges.length + 1)

theorem mem_chalsOf {p j : ℕ} : j ∈ ir.chalsOf p ↔
    j < ir.challenges.length ∧ (ir.challenge j).phase = p ∧ ir.chalIsSource j = true := by
  simp [chalsOf]

theorem mem_phaseRounds {k : ℕ} {rd : Round} : rd ∈ ir.phaseRounds k ↔
    (∃ j, rd = .chal j ∧ j < ir.challenges.length ∧ (ir.challenge j).phase = k + 1 ∧
      ir.chalIsSource j = true) ∨
      rd = .late (k + 1) := by
  simp only [phaseRounds, List.mem_append, List.mem_map, mem_chalsOf, List.mem_singleton]
  constructor
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact .inl ⟨j, rfl, hj⟩
    · exact .inr rfl
  · rintro (⟨j, rfl, hj⟩ | rfl)
    · exact .inl ⟨j, hj, rfl⟩
    · exact .inr rfl

/-- **The rounds are listed by strictly increasing rank.** -/
theorem rounds_pairwise : ir.rounds.Pairwise fun a b => ir.rank a < ir.rank b := by
  have hB : ∀ j, j < ir.challenges.length → j + 1 < ir.challenges.length + 1 + 1 := fun j hj => by
    omega
  -- The ranks of the rounds of phase `k + 1` lie in `((2k + 1) B, (2k + 2) B]`.
  have hlo : ∀ k rd, rd ∈ ir.phaseRounds k →
      (2 * k + 1) * (ir.challenges.length + 1) < ir.rank rd ∧
        ir.rank rd ≤ (2 * k + 2) * (ir.challenges.length + 1) := by
    intro k rd hrd
    have hBk : (2 * k + 2) * (ir.challenges.length + 1) =
        (2 * k + 1) * (ir.challenges.length + 1) + (ir.challenges.length + 1) := by ring
    rcases (ir.mem_phaseRounds).1 hrd with ⟨j, rfl, hj, hp⟩ | rfl
    · simp only [rank, hp, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      omega
    · simp only [rank, show 2 * (k + 1) = 2 * k + 2 by omega]
      omega
  have hblock : ∀ k, (ir.phaseRounds k).Pairwise fun a b => ir.rank a < ir.rank b := by
    intro k
    simp only [phaseRounds, List.pairwise_append, List.pairwise_map, List.pairwise_singleton,
      List.mem_map, List.mem_singleton, true_and]
    refine ⟨?_, ?_⟩
    · refine ((List.pairwise_lt_range).filter _).imp_of_mem fun {a b} ha hb hab => ?_
      rw [mem_chalsOf] at ha hb
      simp only [rank, ha.2, hb.2]
      omega
    · rintro _ ⟨j, hj, rfl⟩ _ rfl
      rw [mem_chalsOf] at hj
      have hBk : 2 * (k + 1) * (ir.challenges.length + 1) =
          (2 * k + 1) * (ir.challenges.length + 1) + (ir.challenges.length + 1) := by ring
      simp only [rank, hj.2, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      omega
  simp only [rounds, List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap,
    List.mem_append, List.mem_flatMap, List.mem_singleton, List.mem_range]
  refine ⟨?_, ⟨fun k _ => hblock k, ?_⟩, by simp, ?_⟩
  · rintro rd (⟨k, -, hrd⟩ | rfl)
    · exact lt_of_le_of_lt (Nat.zero_le _) (hlo k rd hrd).1
    · simp only [rank]
      positivity
  · refine (List.pairwise_lt_range).imp fun {k k'} hkk' a ha b hb => ?_
    have h1 := (hlo k a ha).2
    have h2 := (hlo k' b hb).1
    have : (2 * k + 2) * (ir.challenges.length + 1) ≤ (2 * k' + 1) * (ir.challenges.length + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rintro a ⟨k, hk, ha⟩ b rfl
    have h1 := (hlo k a ha).2
    have hf : ir.rank .final = (2 * ir.phases + 1) * (ir.challenges.length + 1) := rfl
    have : (2 * k + 2) * (ir.challenges.length + 1) < (2 * ir.phases + 1) * (ir.challenges.length + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    rw [hf]
    omega

/-- The rounds are distinct. -/
theorem rounds_nodup : ir.rounds.Nodup :=
  ir.rounds_pairwise.imp fun h e => (e ▸ h).ne rfl

/-- **The rank orders positions**: a round of smaller rank comes earlier. -/
theorem lt_of_rank_lt {a b : Fin ir.rounds.length}
    (h : ir.rank (ir.rounds.get a) < ir.rank (ir.rounds.get b)) : a < b := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact hab
  · exact absurd h (lt_irrefl _)
  · exact absurd (ir.rounds_pairwise.rel_get_of_lt hab) (not_lt.2 h.le)

/-- **Earlier positions have smaller rank.** -/
theorem rank_le_of_le {a b : Fin ir.rounds.length} (h : a ≤ b) :
    ir.rank (ir.rounds.get a) ≤ ir.rank (ir.rounds.get b) := by
  rcases h.lt_or_eq with hab | rfl
  · exact (ir.rounds_pairwise.rel_get_of_lt hab).le
  · exact le_rfl

theorem commit_mem_rounds : Round.commit ∈ ir.rounds := List.mem_cons_self ..

theorem final_mem_rounds : Round.final ∈ ir.rounds := by simp [rounds]

theorem chal_mem_rounds {j : ℕ} : Round.chal j ∈ ir.rounds ↔ ir.IsSourceChal j := by
  simp only [rounds, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
    reduceCtorEq, false_or, List.not_mem_nil, or_false, mem_phaseRounds, Round.chal.injEq,
    exists_eq_left', IsSourceChal]
  constructor
  · rintro ⟨k, hk, hj, hp, hs⟩
    exact ⟨hj, by omega, by omega, hs⟩
  · rintro ⟨hj, h1, h2, hs⟩
    exact ⟨(ir.challenge j).phase - 1, by omega, hj, by omega, hs⟩

theorem late_mem_rounds {k : ℕ} : Round.late k ∈ ir.rounds ↔ 1 ≤ k ∧ k ≤ ir.phases := by
  simp only [rounds, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
    reduceCtorEq, false_or, List.not_mem_nil, or_false, mem_phaseRounds, Round.late.injEq]
  constructor
  · rintro ⟨k', hk, ⟨j, hj, -⟩ | rfl⟩
    · exact absurd hj (by simp)
    · omega
  · rintro ⟨h1, h2⟩
    exact ⟨k - 1, by omega, .inr (by omega)⟩

/-- **The position of round `rd`** in `rounds`. -/
def pos (rd : Round) : ℕ := ir.rounds.idxOf rd

theorem pos_lt_iff {rd : Round} : ir.pos rd < ir.rounds.length ↔ rd ∈ ir.rounds :=
  List.idxOf_lt_length_iff

theorem get_pos {rd : Round} (h : ir.pos rd < ir.rounds.length) :
    ir.rounds.get ⟨ir.pos rd, h⟩ = rd :=
  List.getElem_idxOf h

theorem pos_get (i : Fin ir.rounds.length) : ir.pos (ir.rounds.get i) = i :=
  ir.rounds_nodup.idxOf_getElem i i.2

/-- **Distinct rounds have distinct positions.** -/
theorem pos_injective {rd rd' : Round} (h : rd ∈ ir.rounds) (h' : rd' ∈ ir.rounds)
    (e : ir.pos rd = ir.pos rd') : rd = rd' := by
  rw [← ir.get_pos (ir.pos_lt_iff.2 h), ← ir.get_pos (ir.pos_lt_iff.2 h')]
  exact congrArg _ (Fin.ext e)

/-- The phase-`0` values come first. -/
theorem pos_commit : ir.pos .commit = 0 := by simp [pos, rounds]

/-! ## The protocol -/

variable (I : Interp)

/-- **The source late values of phase `k`** as the prover sends them: every coordinate of every
late value of role `source` of phase `k`, in its value's field. -/
def LateMsg (k : ℕ) : Type :=
  (l : {l : ir.Late // (ir.value l.1).phase = k ∧ ir.IsSourceValue l.1}) →
    Fin (ir.value l.1.1).size → (I (ir.valueField l.1.1)).K

/-- **The message type of a round**: the committed assignment, a challenge's value, the late values
of a phase, or the one element of `γ_end`. -/
def RoundTy : Round → Type
  | .commit => ir.Assignment I
  | .chal j => ir.ChalVal I j
  | .late k => ir.LateMsg I k
  | .final => Unit

/-- **The source protocol `Π_P₀`** (paper, `def:o-semantics` at the source program): round `i`
is `rounds[i]`. -/
def sourceSpec : ProtocolSpec ir.rounds.length where
  dir i := (ir.rounds.get i).dir
  «Type» i := ir.RoundTy I (ir.rounds.get i)

/-- The challenge rounds are finite. -/
abbrev roundFintype : (rd : Round) → rd.dir = .V_to_P → Fintype (ir.RoundTy I rd)
  | .chal j, _ => inferInstanceAs (Fintype (ir.ChalVal I j))
  | .final, _ => inferInstanceAs (Fintype Unit)
  | .commit, h => nomatch h
  | .late _, h => nomatch h

/-- The challenge rounds are nonempty. -/
theorem roundNonempty : (rd : Round) → rd.dir = .V_to_P → Nonempty (ir.RoundTy I rd)
  | .chal _, _ => ⟨fun _ => default⟩
  | .final, _ => ⟨()⟩
  | .commit, h => nomatch h
  | .late _, h => nomatch h

instance (i : (ir.sourceSpec I).ChallengeIdx) : Fintype ((ir.sourceSpec I).Challenge i) :=
  ir.roundFintype I _ i.2

instance (i : (ir.sourceSpec I).ChallengeIdx) : Nonempty ((ir.sourceSpec I).Challenge i) :=
  ir.roundNonempty I _ i.2

/-- **The value of round `rd` in a transcript of the first `m` rounds**, when `rd` is among
them. -/
def roundAt {m : Fin (ir.rounds.length + 1)} (tr : (ir.sourceSpec I).Transcript m) (rd : Round) :
    Option (ir.RoundTy I rd) :=
  if h : ir.pos rd < m then
    some (cast (congrArg (ir.RoundTy I) (ir.get_pos (by omega))) (tr ⟨ir.pos rd, h⟩))
  else none

/-- **The environment of a transcript** of the first `m` rounds at the statement `x`: the
committed assignment of round `commit`, each source challenge from its round and each source late
value from its phase's round (`0` for the rounds not yet sent, and for the challenges and late
values `Π_P₀` does not have). -/
def envOf {m : Fin (ir.rounds.length + 1)} (x : ir.Valuation I)
    (tr : (ir.sourceSpec I).Transcript m) :
    ir.Env I where
  stmt := x
  asg := (ir.roundAt I tr .commit).getD ⟨0, 0⟩
  chal j c :=
    match ir.roundAt I tr (.chal j) with
    | some v =>
      if h : c < (ir.challenge j).size then (I (ir.chalField j)).samplerVal _ (v ⟨c, h⟩) else 0
    | none => 0
  late v c :=
    match ir.roundAt I tr (.late (ir.value v).phase) with
    | some msg =>
      if h : v < ir.values.length ∧ ir.IsSourceLate v ∧ c < (ir.value v).size then
        msg ⟨⟨⟨v, h.1⟩, h.2.1.1⟩, rfl, h.2.1.2⟩ ⟨c, h.2.2⟩
      else 0
    | none => 0

/-- **The verifier of `Π_P₀`**: it accepts when the statement passes the program's member checks
(`RealizedProgram.stmtOk`, rejecting a statement a check refuses before reading the transcript), every
source predicate holds and every node-typed source value lies in its type (`RealizedProgram.SourceSatAt`),
in the environment of the transcript. -/
def sourceVerifier : Verifier (ir.sourceSpec I) (ir.Valuation I) :=
  fun x tr => ir.stmtOk I x && decide (ir.SourceSatAt (ir.envOf I x tr))

/-- **The extractor of `Π_P₀` that reads the statement and the phase-`0` values**: `proj` at the
statement and the committed assignment (the zero assignment before it is sent).

Running time: one read of the transcript's first round and one call of `proj`; polynomial when
`proj` is (for the proof-of-possession relations, a decoding of committed values).
This running time is argued here, not proved in Lean. -/
def sourceExtractor {W : Type} (proj : ir.Valuation I → ir.Assignment I → W) :
    Extractor (ir.sourceSpec I) (ir.Valuation I) W where
  extract _ x tr := proj x ((ir.roundAt I tr .commit).getD ⟨0, 0⟩)

/-! ## The transcript of a run of the layout -/

/-- **The message of round `rd` of a run of the layout** with the committed assignment `a`: the
assignment, the run's challenges, the late values as messages minus pads, `γ_end`'s element. -/
def roundOf (a : ir.Assignment I) (r : (ir.layout I).Run) : (rd : Round) → ir.RoundTy I rd
  | .commit => a
  | .chal j =>
    if h : ir.IsSourceChal j then
      r.chal ⟨(ir.challenge j).phase - 1, by have := h.2.1; have := h.2.2; omega⟩
        ⟨⟨j, h.1⟩, by have := h.2.1; simp only; omega⟩
    else fun _ => default
  | .late _ => fun l c => ir.msgRead I r l.1.1 c - a.pad l.1.1 c
  | .final => ()

/-- **The transcript of `Π_P₀` of a run of the layout** with the committed assignment `a`. -/
def transcriptOf (a : ir.Assignment I) (r : (ir.layout I).Run) :
    (ir.sourceSpec I).Transcript (Fin.last _) :=
  fun _ => ir.roundOf I a r _

variable {ir I}

/-- A cast of a round's message along an equality of rounds. -/
theorem cast_roundOf (a : ir.Assignment I) (r : (ir.layout I).Run) {rd rd' : Round} (e : rd' = rd)
    (h : ir.RoundTy I rd' = ir.RoundTy I rd) : cast h (ir.roundOf I a r rd') = ir.roundOf I a r rd :=
  by subst e; rfl

/-- **The challenge round of the layout's transcript** is the run's challenge. -/
theorem roundOf_chal (a : ir.Assignment I) (r : (ir.layout I).Run) {j : ℕ} (hj : ir.IsSourceChal j) :
    ir.roundOf I a r (.chal j) =
      r.chal ⟨(ir.challenge j).phase - 1, by have := hj.2.1; have := hj.2.2; omega⟩
        ⟨⟨j, hj.1⟩, by have := hj.2.1; simp only; omega⟩ :=
  dif_pos hj

/-- A challenge of no phase reads as `0`. -/
theorem roundOf_chal_of_not (a : ir.Assignment I) (r : (ir.layout I).Run) {j : ℕ}
    (hj : ¬ ir.IsSourceChal j) : ir.roundOf I a r (.chal j) = fun _ => default :=
  dif_neg hj

/-- **A round of the layout's transcript** is the round's message (`none` for a round `Π_P₀`
does not have). -/
theorem roundAt_transcriptOf (a : ir.Assignment I) (r : (ir.layout I).Run) (rd : Round) :
    ir.roundAt I (ir.transcriptOf I a r) rd =
      if rd ∈ ir.rounds then some (ir.roundOf I a r rd) else none := by
  unfold roundAt
  by_cases h : rd ∈ ir.rounds
  · have hp : ir.pos rd < ir.rounds.length := ir.pos_lt_iff.2 h
    rw [dif_pos (by simpa using hp), if_pos h]
    exact congrArg some (cast_roundOf a r (ir.get_pos hp) _)
  · rw [dif_neg (by simpa [ir.pos_lt_iff] using h), if_neg h]

/-- **The environment of the layout's transcript agrees with the layout's environment on the
source reads**: the statement, the committed assignment, the source challenges and the source late
values. -/
theorem agreeOnSource_envOf_transcriptOf (x : ir.Valuation I) (a : ir.Assignment I)
    (r : (ir.layout I).Run) :
    Env.AgreeOnSource (ir.envOf I x (ir.transcriptOf I a r)) (ir.layoutEnv I x a r) where
  stmt := rfl
  asg := by
    change (ir.roundAt I (ir.transcriptOf I a r) .commit).getD ⟨0, 0⟩ = a
    rw [roundAt_transcriptOf, if_pos ir.commit_mem_rounds]
    rfl
  chal j hsrc := by
    funext c
    simp only [envOf, layoutEnv]
    rw [roundAt_transcriptOf]
    by_cases hj : ir.IsSourceChal j
    · rw [if_pos (ir.chal_mem_rounds.2 hj)]
      simp only [chalRead, roundOf_chal a r hj]
      by_cases hc : c < (ir.challenge j).size
      · rw [dif_pos hc, dif_pos ⟨hj.1, hj.2.1, hj.2.2.1, hc⟩]
      · rw [dif_neg hc, dif_neg fun h => hc h.2.2.2]
    · rw [if_neg (fun h => hj (ir.chal_mem_rounds.1 h))]
      simp only [chalRead]
      rw [dif_neg fun h => hj ⟨h.1, h.2.1, h.2.2.1, hsrc⟩]
  late v hsrc := by
    funext c
    simp only [envOf, layoutEnv]
    rw [roundAt_transcriptOf]
    by_cases hv : v < ir.values.length ∧ ir.IsLate v ∧ c < (ir.value v).size
    · have hmem : Round.late (ir.value v).phase ∈ ir.rounds :=
        ir.late_mem_rounds.2 ⟨hv.2.1.2.1, hv.2.1.2.2⟩
      have hv' : v < ir.values.length ∧ ir.IsSourceLate v ∧ c < (ir.value v).size :=
        ⟨hv.1, ⟨hv.2.1, hsrc⟩, hv.2.2⟩
      rw [if_pos hmem, if_pos hv]
      simp only [roundOf, dif_pos hv']
    · have hv' : ¬ (v < ir.values.length ∧ ir.IsSourceLate v ∧ c < (ir.value v).size) :=
        fun h => hv ⟨h.1, h.2.1.1, h.2.2⟩
      rw [if_neg hv]
      split <;> simp only [dif_neg hv']

variable (I) in
/-- **The source program as a phased constraint** on the layout: `RealizedProgram.SourceSatAt` at the
layout's environment. -/
def SourcePred : (ir.layout I).Constraint (ir.Valuation I) (ir.Assignment I) :=
  fun x a r => ir.SourceSatAt (ir.layoutEnv I x a r)

/-- **The realized program's constraint gives the source program's.** -/
theorem Pred.toSource {x : ir.Valuation I} {a : ir.Assignment I} {r : (ir.layout I).Run}
    (h : ir.Pred I x a r) : ir.SourcePred I x a r :=
  SatAt.toSource h

/-- **`Π_P₀`'s verifier accepts the layout's transcript exactly when the statement is admissible
(`StatementIn`: the member checks and the declared bounds) and the source program holds** (`SourceValid`: the source program reads only what the
transcript carries). -/
theorem sourceVerifier_transcriptOf (hs : ir.SourceValid) (x : ir.Valuation I)
    (a : ir.Assignment I) (r : (ir.layout I).Run) :
    ir.sourceVerifier I x (ir.transcriptOf I a r) = true ↔
      ir.StatementIn I x ∧ ir.SourcePred I x a r := by
  simp only [sourceVerifier, Bool.and_eq_true, stmtOk_iff, decide_eq_true_iff]
  exact and_congr_right fun _ => sourceSatAt_congr hs (agreeOnSource_envOf_transcriptOf x a r)

end

/-! ## Prefixes and the order of the rounds -/

section

variable {ir : RealizedProgram} {I : Interp}

/-- **A round among the first `m` reads as in the longer transcript.** -/
theorem roundAt_take {m m' : Fin (ir.rounds.length + 1)} (hm : m ≤ m')
    (tr : (ir.sourceSpec I).Transcript m') {rd : Round} (h : ir.pos rd < m) :
    ir.roundAt I (tr.take m hm) rd = ir.roundAt I tr rd := by
  have hm' := Fin.le_iff_val_le_val.1 hm
  unfold roundAt
  rw [dif_pos h, dif_pos (by omega)]
  rfl

/-- **A challenge round comes after the phase-`0` values.** -/
theorem pos_lt_of_challenge (i : (ir.sourceSpec I).ChallengeIdx) : 0 < (i.1 : ℕ) := by
  by_contra h0
  have e : i.1 = ⟨0, by have := i.1.2; omega⟩ := Fin.ext (by simp only; omega)
  have hi := i.2
  rw [e] at hi
  simp [sourceSpec, rounds, Round.dir] at hi

/-- **A challenge round is a source challenge or `γ_end`.** -/
theorem chal_or_final (i : (ir.sourceSpec I).ChallengeIdx) :
    (∃ j, ir.rounds.get i.1 = .chal j ∧ ir.IsSourceChal j) ∨ ir.rounds.get i.1 = .final := by
  have hi : (ir.rounds.get i.1).dir = .V_to_P := i.2
  have hmem : ir.rounds.get i.1 ∈ ir.rounds := List.get_mem _ _
  generalize ir.rounds.get i.1 = rd at hi hmem
  cases rd with
  | commit => simp [Round.dir] at hi
  | chal j => exact .inl ⟨j, rfl, ir.chal_mem_rounds.1 hmem⟩
  | late k => simp [Round.dir] at hi
  | final => exact .inr rfl

variable (I) in
/-- **The phase of a challenge round** (`0` for `γ_end`). -/
def chalPhase (i : (ir.sourceSpec I).ChallengeIdx) : ℕ :=
  match ir.rounds.get i.1 with
  | .chal j => (ir.challenge j).phase
  | _ => 0

/-- **The extractor on a prefix of the layout's transcript** past the phase-`0` values reads the
committed assignment. -/
theorem extractor_take {W : Type} (proj : ir.Valuation I → ir.Assignment I → W)
    (x : ir.Valuation I) (a : ir.Assignment I) (r : (ir.layout I).Run)
    {m : Fin (ir.rounds.length + 1)} (hm : 0 < (m : ℕ)) :
    ir.sourceExtractor I proj m x ((ir.transcriptOf I a r).take m (Fin.le_last _)) = proj x a := by
  change proj x ((ir.roundAt I _ .commit).getD ⟨0, 0⟩) = proj x a
  rw [roundAt_take _ _ (by rw [pos_commit]; exact hm), roundAt_transcriptOf,
    if_pos ir.commit_mem_rounds]
  rfl

/-- **An earlier challenge has no later phase.** -/
theorem phase_le_of_rank_le {j j' : ℕ} (hj : ir.IsSourceChal j)
    (h : ir.rank (.chal j') ≤ ir.rank (.chal j)) :
    (ir.challenge j').phase ≤ (ir.challenge j).phase := by
  by_contra hlt
  have hm : (2 * (ir.challenge j).phase - 1 + 2) * (ir.challenges.length + 1) ≤
      (2 * (ir.challenge j').phase - 1) * (ir.challenges.length + 1) :=
    Nat.mul_le_mul_right _ (by have := hj.2.1; omega)
  rw [Nat.add_mul] at hm
  simp only [rank] at h
  have := hj.1
  omega

/-- **Late values before a challenge are of an earlier phase.** -/
theorem late_lt_of_rank_le {j k : ℕ} (hj : ir.IsSourceChal j)
    (h : ir.rank (.late k) ≤ ir.rank (.chal j)) : k < (ir.challenge j).phase := by
  by_contra hlt
  have hm : 2 * (ir.challenge j).phase * (ir.challenges.length + 1) ≤
      2 * k * (ir.challenges.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have he : 2 * (ir.challenge j).phase * (ir.challenges.length + 1) =
      (2 * (ir.challenge j).phase - 1) * (ir.challenges.length + 1) + (ir.challenges.length + 1) := by
    have : 2 * (ir.challenge j).phase = (2 * (ir.challenge j).phase - 1) + 1 := by
      have := hj.2.1
      omega
    conv_lhs => rw [this]
    rw [Nat.add_mul, one_mul]
  simp only [rank] at h
  have := hj.1
  omega

/-- **Runs agreeing through phase `k + 1` give the same rounds up to a challenge of that phase.** -/
theorem roundOf_eq_of_eqThrough (a : ir.Assignment I) {r r' : (ir.layout I).Run}
    {k : Fin ir.phases} (h : r.EqThrough k r') {j : ℕ} (hj : ir.IsSourceChal j)
    (hk : (ir.challenge j).phase = k + 1) {rd : Round} (hrd : rd ∈ ir.rounds)
    (hle : ir.rank rd ≤ ir.rank (.chal j)) : ir.roundOf I a r rd = ir.roundOf I a r' rd := by
  cases rd with
  | commit => rfl
  | final => rfl
  | chal j' =>
    have hj' := ir.chal_mem_rounds.1 hrd
    have hp := phase_le_of_rank_le hj hle
    rw [roundOf_chal a r hj', roundOf_chal a r' hj',
      h.chal _ (Fin.le_def.2 (by simp only; omega))]
  | late k' =>
    have hlt := late_lt_of_rank_le hj hle
    funext l c
    simp only [roundOf]
    rw [msgRead_eq_of_lt h.msg (u := l.1.1) (by rw [l.2.1]; omega)]

/-- **Runs agreeing through phase `k + 1` give the same transcript up to a challenge round of that
phase.** -/
theorem take_transcriptOf_eq (a : ir.Assignment I) {r r' : (ir.layout I).Run} {k : Fin ir.phases}
    (h : r.EqThrough k r') {i : (ir.sourceSpec I).ChallengeIdx} (hi : ir.chalPhase I i = k + 1) :
    (ir.transcriptOf I a r).take i.1.succ (Fin.le_last _) =
      (ir.transcriptOf I a r').take i.1.succ (Fin.le_last _) := by
  rcases chal_or_final i with ⟨j, hget, hj⟩ | hget
  · have hk : (ir.challenge j).phase = k + 1 := by
      unfold chalPhase at hi
      rwa [hget] at hi
    funext m
    refine roundOf_eq_of_eqThrough a h hj hk (List.get_mem _ _) ?_
    rw [← hget]
    exact ir.rank_le_of_le (Fin.le_def.2 (by
      have := m.2
      simp only [Fin.val_castLE, Fin.val_succ] at this ⊢
      omega))
  · unfold chalPhase at hi
    rw [hget] at hi
    simp at hi

/-- **The relation as a constraint of the layout** on witnesses read from the statement: `(x, f x)`
lies in the relation. -/
def relConstraint {W : Type} (rel : Set (ir.Valuation I × W)) :
    (ir.layout I).Constraint (ir.Valuation I) (ir.Valuation I → W) :=
  fun x f _ => (x, f x) ∈ rel

/-! ## From round-by-round knowledge soundness of `Π_P₀` to the proof system's events -/

variable (I) in
/-- **`Π_P₀` is round-by-round knowledge sound with no error at `γ_end`**: round-by-round knowledge
soundness for `rel` at the extractor reading the statement and the phase-`0` values
(`RealizedProgram.sourceExtractor proj`) and the state function `S`, at some errors that are `0` at
`γ_end`. A proposition, so the lowering built from it (`loweringOfRbr`) reads no error as data. -/
def SourceRbr {W : Type} (rel : Set (ir.Valuation I × W)) (proj : ir.Valuation I → ir.Assignment I → W)
    (S : KnowledgeStateFunction (ir.sourceVerifier I)) : Prop :=
  ∃ ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0,
    rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε ∧
      ∀ i : (ir.sourceSpec I).ChallengeIdx, ir.rounds.get i.1 = .final → ε i = 0

variable (I) in
/-- **The events of `Π_P₀`'s round-by-round knowledge soundness on the layout** (the forward bridge
of paper `lem:phases`): for round-by-round knowledge soundness of `Π_P₀` for `rel` at the extractor
reading the statement and the phase-`0` values (`RealizedProgram.sourceExtractor proj`) and the state
function `S`, at errors that are `0` at `γ_end` (`hS`, `SourceRbr`), the lowering from `rel` at the statements that pass the
member checks (`Constraint.guard`: `Π_P₀`'s verifier rejects the others) to the source program
(`SourcePred`) projecting the committed assignment by `proj`, whose event at phase `k + 1` is "the
extractor fails and the state flips at a source challenge of phase `k + 1`" on the layout's
transcript (`RealizedProgram.transcriptOf`). Its challenge-use rule holds because a flip reads only the
rounds up to its challenge; its soundness is `KnowledgeStateFunction.exists_flip` with
`sourceVerifier_transcriptOf` (`hs`: the source part is well formed), a flip at `γ_end` being
excluded by its error `0`. The events' bound is `eventBound_loweringOfRbr`. -/
def loweringOfRbr {W : Type} {rel : Set (ir.Valuation I × W)} (hs : ir.SourceValid)
    (proj : ir.Valuation I → ir.Assignment I → W) (S : KnowledgeStateFunction (ir.sourceVerifier I))
    (hS : ir.SourceRbr I rel proj S) :
    Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (ir.relConstraint rel))
      (ir.SourcePred I) where
  proj a x := proj x a
  event k x a r := (x, proj x a) ∉ rel ∧
    ∃ i : (ir.sourceSpec I).ChallengeIdx, ir.chalPhase I i = k + 1 ∧
      S.Flips i x (ir.transcriptOf I a r)
  challengeUse x a k r r' hr := and_congr_right fun _ => exists_congr fun i =>
    and_congr_right fun hi => S.flips_congr (take_transcriptOf_eq a hr hi)
  sound x a r hP := by
    by_cases hok : ir.stmtOk I x = true
    swap
    · exact .inl (Constraint.guard_of fun h => absurd h hok)
    by_cases hrel : (x, proj x a) ∈ rel
    · exact .inl (Constraint.guard_of fun _ => hrel)
    right
    have hV := (sourceVerifier_transcriptOf hs x a r).2 ⟨stmtOk_iff.1 hok, hP⟩
    obtain ⟨i, hflip⟩ := S.exists_flips (S.toFun_full x _ hV)
    rcases chal_or_final i with ⟨j, hget, hj⟩ | hget
    · refine ⟨⟨(ir.challenge j).phase - 1, by have := hj.2.1; have := hj.2.2; omega⟩, hrel, i,
        ?_, hflip⟩
      unfold chalPhase
      rw [hget]
      have := hj.2.1
      simp only
      omega
    · exfalso
      obtain ⟨ε, h, hend⟩ := hS
      have hc := rbrKnowledgeSoundness_iff_count.1 h x i
        ((ir.transcriptOf I a r).take i.1.castSucc (Fin.le_last _))
      rw [hend i hget, zero_mul] at hc
      have hE := extractor_take proj x a r (m := i.1.castSucc) (pos_lt_of_challenge i)
      classical
      have hmem : (ir.transcriptOf I a r) ⟨i.1, i.1.2⟩ ∈ Finset.univ.filter fun c =>
          (x, ir.sourceExtractor I proj i.1.castSucc x
              ((ir.transcriptOf I a r).take i.1.castSucc (Fin.le_last _))) ∉ rel ∧
            ¬ S.toFun i.1.castSucc x ((ir.transcriptOf I a r).take i.1.castSucc (Fin.le_last _)) ∧
            S.toFun i.1.succ x
              ((ir.sourceSpec I).concat
                ((ir.transcriptOf I a r).take i.1.castSucc (Fin.le_last _)) c) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hE ▸ hrel, hflip.1, ?_⟩
        rw [ProtocolSpec.concat_take_castSucc]
        exact hflip.2
      have hpos := Finset.card_pos.2 ⟨_, hmem⟩
      exact absurd hc (not_le.2 (by exact_mod_cast hpos))

/-! ## The events' bound -/

/-- **Setting a phase's challenges keeps the other challenges' values** apart from the one set:
updating coordinate `jj` of the challenge of index `k` changes no other challenge. -/
theorem setChal_update_chal (r : (ir.layout I).Run) {k : Fin ir.phases}
    (f : (ir.layout I).Ch k) (jj : ir.ChalAt k) (v v' : ir.ChalVal I jj.1) (k' : Fin ir.phases)
    (jj' : ir.ChalAt k') (hne : (jj'.1 : ℕ) ≠ jj.1) :
    (r.setChal k (Function.update f jj v)).chal k' jj' =
      (r.setChal k (Function.update f jj v')).chal k' jj' := by
  by_cases hk : k' = k
  · subst hk
    have hjj : jj' ≠ jj := fun e => hne (by rw [e])
    rw [Run.setChal_chal_self, Run.setChal_chal_self, Function.update_of_ne hjj,
      Function.update_of_ne hjj]
  · rw [Run.setChal_chal_of_ne _ _ hk, Run.setChal_chal_of_ne _ _ hk]

/-- **The coordinate set is read back.** -/
theorem setChal_update_chal_self (r : (ir.layout I).Run) {k : Fin ir.phases}
    (f : (ir.layout I).Ch k) (jj : ir.ChalAt k) (v : ir.ChalVal I jj.1) (k' : Fin ir.phases)
    (jj' : ir.ChalAt k') (hk : k' = k) (hj : (jj'.1 : ℕ) = jj.1) :
    (r.setChal k (Function.update f jj v)).chal k' jj' ≍ v := by
  subst hk
  obtain rfl : jj' = jj := Subtype.ext (Fin.ext hj)
  rw [Run.setChal_chal_self, Function.update_self]

/-- **Updating one challenge changes no other round.** -/
theorem roundOf_setChal_update (a : ir.Assignment I) (r : (ir.layout I).Run) {k : Fin ir.phases}
    (f : (ir.layout I).Ch k) (jj : ir.ChalAt k) (v v' : ir.ChalVal I jj.1) {rd : Round}
    (hrd : rd ≠ .chal jj.1) :
    ir.roundOf I a (r.setChal k (Function.update f jj v)) rd =
      ir.roundOf I a (r.setChal k (Function.update f jj v')) rd := by
  cases rd with
  | commit => rfl
  | final => rfl
  | late _ => rfl
  | chal j' =>
    by_cases hj' : ir.IsSourceChal j'
    · rw [roundOf_chal a _ hj', roundOf_chal a _ hj']
      exact setChal_update_chal r f jj v v' _ _ fun e => hrd (by rw [← e])
    · rw [roundOf_chal_of_not a _ hj', roundOf_chal_of_not a _ hj']

open Classical in
/-- **One challenge round's events have probability at most its error** (in counting form): over the
challenge of phase `k + 1`, the state flips at a challenge round of that phase for at most
`ε i · |Ch k|` values, when the extractor fails. -/
theorem card_flips_le {W : Type} {rel : Set (ir.Valuation I × W)}
    {proj : ir.Valuation I → ir.Assignment I → W} {S : KnowledgeStateFunction (ir.sourceVerifier I)}
    {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    {k : Fin ir.phases} {x : ir.Valuation I} {a : ir.Assignment I} (r : (ir.layout I).Run)
    (hrel : (x, proj x a) ∉ rel) {i : (ir.sourceSpec I).ChallengeIdx}
    (hi : ir.chalPhase I i = k + 1) :
    (((Finset.univ.filter fun c : (ir.layout I).Ch k =>
        S.Flips i x (ir.transcriptOf I a (r.setChal k c))).card : ℕ) : ℝ≥0) ≤
      ε i * Fintype.card ((ir.layout I).Ch k) := by
  classical
  obtain ⟨j, hget, hj⟩ : ∃ j, ir.rounds.get i.1 = .chal j ∧ ir.IsSourceChal j := by
    rcases chal_or_final i with h' | hget
    · exact h'
    · unfold chalPhase at hi
      rw [hget] at hi
      simp at hi
  have hk : (ir.challenge j).phase = k + 1 := by
    unfold chalPhase at hi
    rwa [hget] at hi
  let jj : ir.ChalAt k := ⟨⟨j, hj.1⟩, by simp only; omega⟩
  have hT : ir.RoundTy I (.chal j) = ir.RoundTy I (ir.rounds.get i.1) := congrArg _ hget.symm
  refine card_le_of_card_update_le (β := fun jj : ir.ChalAt k => ir.ChalVal I jj.1) jj
    fun f => ?_
  -- The transcript at each value of the coordinate `jj`.
  let T : ir.ChalVal I j → (ir.sourceSpec I).Transcript (Fin.last _) := fun v =>
    ir.transcriptOf I a (r.setChal k (Function.update f jj v))
  let pre := (T (f jj)).take i.1.castSucc (Fin.le_last _)
  have hpre : ∀ v, (T v).take i.1.castSucc (Fin.le_last _) = pre := by
    intro v
    funext m
    refine roundOf_setChal_update a r f jj v (f jj) fun e => ?_
    have hm : ir.rounds.get (Fin.castLE (by simp) (Fin.castLE (Fin.le_last _) m)) =
        ir.rounds.get i.1 := by rw [e, hget]
    have := Fin.ext_iff.1 ((List.Nodup.get_inj_iff ir.rounds_nodup).1 hm)
    have hm2 := m.2
    simp only [Fin.val_castLE, Fin.val_castSucc] at this hm2
    omega
  have hat : ∀ v, T v ⟨i.1, i.1.2⟩ = cast hT v := by
    intro v
    change ir.roundOf I a _ (ir.rounds.get i.1) = _
    rw [← cast_roundOf a _ hget.symm hT, roundOf_chal a _ hj]
    congr 1
    exact eq_of_heq (setChal_update_chal_self r f jj v _ _ (Fin.ext (by simp only; omega)) rfl)
  have hflip : ∀ v, S.Flips i x (T v) ↔
      ¬ S.toFun i.1.castSucc x pre ∧
        S.toFun i.1.succ x ((ir.sourceSpec I).concat pre (cast hT v)) := by
    intro v
    unfold KnowledgeStateFunction.Flips
    rw [hpre v, ← ProtocolSpec.concat_take_castSucc, hpre v, hat v]
    exact Iff.rfl
  have hE : ir.sourceExtractor I proj i.1.castSucc x pre = proj x a :=
    extractor_take proj x a _ (pos_lt_of_challenge i)
  have hcount := rbrKnowledgeSoundness_iff_count.1 h x i pre
  rw [hE] at hcount
  calc ((Finset.univ.filter fun v : ir.ChalVal I jj.1 =>
          Function.update f jj v ∈ Finset.univ.filter fun c : (ir.layout I).Ch k =>
            S.Flips i x (ir.transcriptOf I a (r.setChal k c))).card : ℝ≥0)
      ≤ ((Finset.univ.filter fun c : (ir.sourceSpec I).Challenge i =>
          (x, proj x a) ∉ rel ∧ ¬ S.toFun i.1.castSucc x pre ∧
            S.toFun i.1.succ x ((ir.sourceSpec I).concat pre c)).card : ℝ≥0) := by
        refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun v => cast hT v) ?_ ?_)
        · intro v hv
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hv ⊢
          exact ⟨hrel, (hflip v).1 hv⟩
        · intro v _ v' _ e
          exact (cast_inj hT).1 e
    _ ≤ ε i * Fintype.card ((ir.sourceSpec I).Challenge i) := hcount
    _ = ε i * Fintype.card (ir.ChalVal I jj.1) := by
        rw [Fintype.card_congr
          (Equiv.cast hT.symm : (ir.sourceSpec I).Challenge i ≃ ir.ChalVal I jj.1)]

variable (I) in
/-- **The events of `loweringOfRbr` have the phase's errors**: the event at phase `k + 1` has
probability at most the sum of `ε` over the challenge rounds of that phase (the union bound over
its challenges, each bounded by `Π_P₀`'s round-by-round error at its round, `card_flips_le`). -/
theorem eventBound_loweringOfRbr {W : Type} {rel : Set (ir.Valuation I × W)} (hs : ir.SourceValid)
    (proj : ir.Valuation I → ir.Assignment I → W) (S : KnowledgeStateFunction (ir.sourceVerifier I))
    {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hS : ir.SourceRbr I rel proj S) :
    (ir.loweringOfRbr I hs proj S hS).EventBound fun k =>
      ∑ i ∈ Finset.univ.filter (fun i : (ir.sourceSpec I).ChallengeIdx => ir.chalPhase I i = k + 1),
        ε i := by
  classical
  intro k x a r
  change Pr[c ← (ir.layout I).Ch k : (x, proj x a) ∉ rel ∧
    ∃ i : (ir.sourceSpec I).ChallengeIdx, ir.chalPhase I i = k + 1 ∧
      S.Flips i x (ir.transcriptOf I a (r.setChal k c))] ≤ _
  rw [← card_le_iff_probUniform_le]
  by_cases hrel : (x, proj x a) ∈ rel
  · simp [hrel]
  let s := Finset.univ.filter fun i : (ir.sourceSpec I).ChallengeIdx => ir.chalPhase I i = k + 1
  have hsub : (Finset.univ.filter fun c : (ir.layout I).Ch k => (x, proj x a) ∉ rel ∧
      ∃ i : (ir.sourceSpec I).ChallengeIdx, ir.chalPhase I i = k + 1 ∧
        S.Flips i x (ir.transcriptOf I a (r.setChal k c))) ⊆
      s.biUnion fun i => Finset.univ.filter fun c : (ir.layout I).Ch k =>
        S.Flips i x (ir.transcriptOf I a (r.setChal k c)) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨-, i, hi, hf⟩ := hc
    exact Finset.mem_biUnion.2 ⟨i, by simp [s, hi], by simp [hf]⟩
  calc _ ≤ ((s.biUnion fun i => Finset.univ.filter fun c : (ir.layout I).Ch k =>
          S.Flips i x (ir.transcriptOf I a (r.setChal k c))).card : ℝ≥0) :=
        Nat.cast_le.2 (Finset.card_le_card hsub)
    _ ≤ ∑ i ∈ s, ((Finset.univ.filter fun c : (ir.layout I).Ch k =>
          S.Flips i x (ir.transcriptOf I a (r.setChal k c))).card : ℝ≥0) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ i ∈ s, ε i * Fintype.card ((ir.layout I).Ch k) :=
        Finset.sum_le_sum fun i hi => card_flips_le h r hrel (Finset.mem_filter.1 hi).2
    _ = (∑ i ∈ s, ε i) * Fintype.card ((ir.layout I).Ch k) := (Finset.sum_mul ..).symm

/-! ## From per-challenge events to round-by-round knowledge soundness of `Π_P₀` -/

/-- **Challenge `j'` is drawn no later than challenge `j`**: of an earlier phase, or of the same
phase and declared no later. -/
def ChalBefore (j' j : ℕ) : Prop :=
  (ir.challenge j').phase < (ir.challenge j).phase ∨
    ((ir.challenge j').phase = (ir.challenge j).phase ∧ j' ≤ j)

/-- **Two environments agree on what is fixed when challenge `j` is drawn, and on `j`**: the
statement, the committed assignment, the challenges drawn no later than `j` (`ChalBefore`), and the
late values of the phases before `j`'s. -/
structure Env.EqUpTo (j : ℕ) (e e' : ir.Env I) : Prop where
  /-- The statements agree. -/
  stmt : e.stmt = e'.stmt
  /-- The committed assignments agree. -/
  asg : e.asg = e'.asg
  /-- The challenges drawn no later than `j` agree. -/
  chal : ∀ j', ir.ChalBefore j' j → e.chal j' = e'.chal j'
  /-- The late values of the phases before `j`'s agree. -/
  late : ∀ v, (ir.value v).phase < (ir.challenge j).phase → e.late v = e'.late v

variable (ir I) in
/-- **The challenge-use rule for per-challenge events** on environments: the event at challenge
`j` reads only what is fixed when `j` is drawn, and `j` (`Env.EqUpTo`). -/
def ChallengeUseAt (ev : ℕ → ir.Env I → Prop) : Prop :=
  ∀ j ⦃e e' : ir.Env I⦄, Env.EqUpTo j e e' → (ev j e ↔ ev j e')

/-- **The environment with challenge `j` set to `c`.** -/
def Env.setChal (e : ir.Env I) (j : ℕ) (c : ir.ChalVal I j) : ir.Env I :=
  { e with chal := Function.update e.chal j fun i =>
      if h : i < (ir.challenge j).size then (I (ir.chalField j)).samplerVal _ (c ⟨i, h⟩) else 0 }

variable (I) in
/-- **The errors of `Π_P₀` from per-challenge errors**: `ε j` at the round of challenge `j`, `0` at
`γ_end`. -/
def roundError (ε : ℕ → ℝ≥0) (i : (ir.sourceSpec I).ChallengeIdx) : ℝ≥0 :=
  match ir.rounds.get i.1 with
  | .chal j => ε j
  | _ => 0

/-- A round `Π_P₀` does not have is in no transcript. -/
theorem roundAt_of_not_mem {m : Fin (ir.rounds.length + 1)} (tr : (ir.sourceSpec I).Transcript m)
    {rd : Round} (h : rd ∉ ir.rounds) : ir.roundAt I tr rd = none := by
  have hp : ¬ ir.pos rd < ir.rounds.length := fun h' => h (ir.pos_lt_iff.1 h')
  have hm := m.2
  unfold roundAt
  rw [dif_neg (by omega)]

/-- **Appending a round keeps the earlier rounds.** -/
theorem roundAt_concat_of_lt {m : Fin ir.rounds.length}
    (tr : (ir.sourceSpec I).Transcript m.castSucc)
    (msg : (ir.sourceSpec I).Type m) {rd : Round} (h : ir.pos rd < m) :
    ir.roundAt I ((ir.sourceSpec I).concat tr msg) rd = ir.roundAt I tr rd := by
  unfold roundAt
  rw [dif_pos (by simp only [Fin.val_succ]; omega),
    dif_pos (show ir.pos rd < (m.castSucc : ℕ) from h),
    ProtocolSpec.concat_apply_of_lt tr msg _ h]

/-- **The appended challenge is read at its round.** -/
theorem roundAt_concat_chal {i : Fin ir.rounds.length}
    (tr : (ir.sourceSpec I).Transcript i.castSucc)
    (c : (ir.sourceSpec I).Type i) {j : ℕ} (hget : ir.rounds.get i = .chal j) :
    ir.roundAt I ((ir.sourceSpec I).concat tr c) (.chal j) =
      some (cast (congrArg (ir.RoundTy I) hget) c) := by
  have hp : ir.pos (.chal j) = i := by rw [← hget, pos_get]
  unfold roundAt
  rw [dif_pos (by simp only [Fin.val_succ]; omega)]
  congr 1
  have key : ∀ (q : ℕ) (hq : q = i) (hlt : q < i.succ)
      (p : (ir.sourceSpec I).Type (Fin.castLE (Fin.is_le i.succ) ⟨q, hlt⟩) =
        ir.RoundTy I (.chal j)),
      cast p ((ir.sourceSpec I).concat tr c ⟨q, hlt⟩) = cast (congrArg (ir.RoundTy I) hget) c := by
    rintro q rfl hlt p
    rw [(ir.sourceSpec I).concat_apply_last tr c]
    rfl
  exact key _ hp _ _

/-- **The challenge round of challenge `j`.** -/
def chalIdx {j : ℕ} (hj : ir.IsSourceChal j) : (ir.sourceSpec I).ChallengeIdx :=
  ⟨⟨ir.pos (.chal j), ir.pos_lt_iff.2 (ir.chal_mem_rounds.2 hj)⟩, by
    change (ir.rounds.get _).dir = _
    rw [ir.get_pos]
    rfl⟩

/-- **The challenge rounds of a round before position `p`**: a challenge drawn no later than `j`
is at a position no later than `j`'s. -/
theorem pos_le_of_chalBefore {j j' : ℕ} (hj : ir.IsSourceChal j) (hj' : ir.IsSourceChal j')
    (h : ir.ChalBefore j' j) : ir.pos (.chal j') ≤ ir.pos (.chal j) := by
  have hp := ir.pos_lt_iff.2 (ir.chal_mem_rounds.2 hj)
  have hp' := ir.pos_lt_iff.2 (ir.chal_mem_rounds.2 hj')
  by_contra hlt
  have := ir.rounds_pairwise.rel_get_of_lt (a := ⟨_, hp⟩) (b := ⟨_, hp'⟩)
    (Fin.lt_def.2 (by simp only; omega))
  rw [ir.get_pos, ir.get_pos] at this
  simp only [rank] at this
  have hj1 := hj.1
  have hj1' := hj'.1
  rcases h with h | ⟨h1, h2⟩
  · have hm : (2 * (ir.challenge j').phase - 1 + 2) * (ir.challenges.length + 1) ≤
        (2 * (ir.challenge j).phase - 1) * (ir.challenges.length + 1) :=
      Nat.mul_le_mul_right _ (by have := hj'.2.1; omega)
    rw [Nat.add_mul] at hm
    omega
  · rw [h1] at this
    omega

/-- **The late values of an earlier phase come before a challenge.** -/
theorem pos_lt_of_late {j k : ℕ} (hj : ir.IsSourceChal j) (hk : 1 ≤ k)
    (h : k < (ir.challenge j).phase) : ir.pos (.late k) < ir.pos (.chal j) := by
  have hp := ir.pos_lt_iff.2 (ir.chal_mem_rounds.2 hj)
  have hl := ir.pos_lt_iff.2 (ir.late_mem_rounds.2 ⟨hk, by have := hj.2.2; omega⟩)
  refine Fin.lt_def.1 (ir.lt_of_rank_lt (a := ⟨_, hl⟩) (b := ⟨_, hp⟩) ?_)
  rw [ir.get_pos, ir.get_pos]
  simp only [rank]
  have hm : (2 * k + 1) * (ir.challenges.length + 1) ≤
      (2 * (ir.challenge j).phase - 1) * (ir.challenges.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at hm
  omega

/-- **Transcripts that agree on the rounds up to challenge `j`'s give environments agreeing up to
`j`.** -/
theorem envOf_eqUpTo {m m' : Fin (ir.rounds.length + 1)} (x : ir.Valuation I)
    (tr : (ir.sourceSpec I).Transcript m) (tr' : (ir.sourceSpec I).Transcript m') {j : ℕ}
    (hj : ir.IsSourceChal j)
    (h : ∀ rd, ir.pos rd ≤ ir.pos (.chal j) → ir.roundAt I tr rd = ir.roundAt I tr' rd) :
    Env.EqUpTo j (ir.envOf I x tr) (ir.envOf I x tr') where
  stmt := rfl
  asg := by
    simp only [envOf]
    rw [h _ (by rw [pos_commit]; omega)]
  chal j' hj' := by
    simp only [envOf]
    by_cases hs : ir.IsSourceChal j'
    · rw [h _ (pos_le_of_chalBefore hj hs hj')]
    · rw [roundAt_of_not_mem tr (fun e => hs (ir.chal_mem_rounds.1 e)),
        roundAt_of_not_mem tr' (fun e => hs (ir.chal_mem_rounds.1 e))]
  late v hv := by
    simp only [envOf]
    by_cases hk : 1 ≤ (ir.value v).phase
    · rw [h _ (pos_lt_of_late hj hk hv).le]
    · have hn : Round.late (ir.value v).phase ∉ ir.rounds := fun e =>
        hk (ir.late_mem_rounds.1 e).1
      rw [roundAt_of_not_mem tr hn, roundAt_of_not_mem tr' hn]

variable (I) in
/-- **The state function of per-challenge events** (paper, `def:o-semantics`, the state after the
library functions' events): true on a prefix past the first challenge round on which the extractor
succeeds or the event of a challenge drawn so far occurs. It is a state function
(`KnowledgeStateFunction`, CMS19 Def. 8.3) when the events obey the challenge-use rule (`huse`) and,
at a statement that passes the member checks, every source predicate holding with no event gives
the relation at the extractor's witness (`hsound`). It need not be efficient. -/
def eventState {W : Type} (rel : Set (ir.Valuation I × W))
    (proj : ir.Valuation I → ir.Assignment I → W) (ev : ℕ → ir.Env I → Prop)
    (huse : ChallengeUseAt ir I ev)
    (hsound : ∀ e : ir.Env I, ir.StatementOk I e.stmt → ir.SourceSatAt e →
      (∀ j, ir.IsSourceChal j → ¬ ev j e) → (e.stmt, proj e.stmt e.asg) ∈ rel) :
    KnowledgeStateFunction (ir.sourceVerifier I) where
  toFun m x tr := (∃ i : (ir.sourceSpec I).ChallengeIdx, (i.1 : ℕ) < m) ∧
    ((x, ir.sourceExtractor I proj m x tr) ∈ rel ∨
      ∃ j, ir.IsSourceChal j ∧ ir.pos (.chal j) < m ∧ ev j (ir.envOf I x tr))
  toFun_empty _ _ := fun ⟨⟨i, hi⟩, _⟩ => by simp at hi
  toFun_next m hdir x tr msg hS := by
    rintro ⟨⟨i, hi⟩, hS'⟩
    -- Round `m` is the prover's, so no challenge round is at `m`.
    have hne : ∀ i : (ir.sourceSpec I).ChallengeIdx, (i.1 : ℕ) ≠ m := fun i e => by
      have := i.2
      rw [show i.1 = m from Fin.ext e, hdir] at this
      cases this
    have hi' : (i.1 : ℕ) < m := by
      have := hne i
      simp only [Fin.val_succ] at hi
      omega
    have hm : 0 < (m : ℕ) := lt_of_le_of_lt (Nat.zero_le _) ((pos_lt_of_challenge i).trans hi')
    refine hS ⟨⟨i, by simp only [Fin.coe_castSucc]; exact hi'⟩, ?_⟩
    have hE : ir.sourceExtractor I proj m.succ x ((ir.sourceSpec I).concat tr msg) =
        ir.sourceExtractor I proj m.castSucc x tr := by
      change proj x _ = proj x _
      rw [roundAt_concat_of_lt tr msg (by rw [pos_commit]; exact hm)]
    rcases hS' with hrel | ⟨j, hj, hpos, hev⟩
    · exact .inl (hE ▸ hrel)
    · have hpos' : ir.pos (.chal j) < m := by
        have := hne (chalIdx hj)
        simp only [Fin.val_succ] at hpos
        simp only [chalIdx] at this
        omega
      refine .inr ⟨j, hj, hpos', (huse j (envOf_eqUpTo x _ _ hj fun rd hrd => ?_)).1 hev⟩
      exact roundAt_concat_of_lt tr msg (by omega)
  toFun_full x tr hV := by
    obtain ⟨hok, hsat⟩ := Bool.and_eq_true _ _ ▸ hV
    have hsat : ir.SourceSatAt (ir.envOf I x tr) := of_decide_eq_true hsat
    refine ⟨⟨⟨⟨ir.pos .final, ir.pos_lt_iff.2 ir.final_mem_rounds⟩, by
      change (ir.rounds.get _).dir = _
      rw [ir.get_pos]
      rfl⟩, ir.pos_lt_iff.2 ir.final_mem_rounds⟩, ?_⟩
    by_cases hev : ∃ j, ir.IsSourceChal j ∧ ev j (ir.envOf I x tr)
    · obtain ⟨j, hj, he⟩ := hev
      exact .inr ⟨j, hj, by simpa using ir.pos_lt_iff.2 (ir.chal_mem_rounds.2 hj), he⟩
    · push Not at hev
      exact .inl (hsound _ (stmtOk_iff.1 hok).1 hsat hev)

open Classical in
variable (I) in
/-- **Per-challenge events give round-by-round knowledge soundness of `Π_P₀`** (the converse bridge,
used by the library lemmas; paper, `def:o-semantics`): events `ev j` on environments, one per
challenge, each reading only what is fixed when its challenge is drawn and that challenge
(`ChallengeUseAt`), of probability at most `ε j` over the challenge (`hbound`), such that, at a
statement that passes the member checks (`StatementOk`), every source predicate holding with no
event gives the relation at `proj` of the statement and the phase-`0` values (`hsound`), give
round-by-round knowledge soundness of `Π_P₀` for `rel` at the
extractor `RealizedProgram.sourceExtractor proj`, the state function `eventState` and the errors `ε j` at
the source challenges' rounds and `0` at `γ_end` (`roundError`). -/
theorem rbr_of_events {W : Type} (rel : Set (ir.Valuation I × W))
    (proj : ir.Valuation I → ir.Assignment I → W) (ev : ℕ → ir.Env I → Prop) (ε : ℕ → ℝ≥0)
    (huse : ChallengeUseAt ir I ev)
    (hbound : ∀ j, ir.IsSourceChal j → ∀ e : ir.Env I,
      Pr[c ← ir.ChalVal I j : ev j (e.setChal j c)] ≤ ε j)
    (hsound : ∀ e : ir.Env I, ir.StatementOk I e.stmt → ir.SourceSatAt e →
      (∀ j, ir.IsSourceChal j → ¬ ev j e) → (e.stmt, proj e.stmt e.asg) ∈ rel) :
    rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj)
      (ir.eventState I rel proj ev huse hsound) (ir.roundError I ε) := by
  rw [rbrKnowledgeSoundness_iff_count]
  intro x i tr
  have hi0 := pos_lt_of_challenge i
  have hE : ∀ c, ir.sourceExtractor I proj i.1.succ x ((ir.sourceSpec I).concat tr c) =
      ir.sourceExtractor I proj i.1.castSucc x tr := fun c => by
    change proj x _ = proj x _
    rw [roundAt_concat_of_lt tr c (by rw [pos_commit]; exact hi0)]
  -- A flip at round `i` with the extractor failing is the event of `i`'s challenge.
  have hflip : ∀ c, (x, ir.sourceExtractor I proj i.1.castSucc x tr) ∉ rel →
      ¬ (ir.eventState I rel proj ev huse hsound).toFun i.1.castSucc x tr →
      (ir.eventState I rel proj ev huse hsound).toFun i.1.succ x ((ir.sourceSpec I).concat tr c) →
      ∃ j, ir.rounds.get i.1 = .chal j ∧ ir.IsSourceChal j ∧
        ev j (ir.envOf I x ((ir.sourceSpec I).concat tr c)) := by
    intro c hrel hS ⟨_, hS'⟩
    rcases hS' with h | ⟨j, hj, hpos, hev⟩
    · exact absurd ((hE c) ▸ h) hrel
    · by_cases hji : ir.pos (.chal j) = i.1
      · refine ⟨j, ?_, hj, hev⟩
        rw [← ir.get_pos (ir.pos_lt_iff.2 (ir.chal_mem_rounds.2 hj))]
        exact congrArg _ (Fin.ext hji.symm)
      · exfalso
        have hlt : ir.pos (.chal j) < i.1 := by
          simp only [Fin.val_succ] at hpos
          omega
        refine hS ⟨⟨chalIdx hj, by simpa [chalIdx] using hlt⟩, .inr ⟨j, hj, hlt, ?_⟩⟩
        exact (huse j (envOf_eqUpTo x _ _ hj fun rd hrd =>
          roundAt_concat_of_lt tr c (by omega))).1 hev
  rcases chal_or_final i with ⟨j, hget, hj⟩ | hget
  · have herr : ir.roundError I ε i = ε j := by
      unfold roundError
      rw [hget]
    rw [herr]
    have hT : ir.RoundTy I (ir.rounds.get i.1) = ir.ChalVal I j := congrArg _ hget
    -- The event of `j` in the prefix's environment with `j` set to the appended challenge.
    have hset : ∀ c, ev j (ir.envOf I x ((ir.sourceSpec I).concat tr c)) ↔
        ev j ((ir.envOf I x tr).setChal j (cast hT c)) := by
      intro c
      have hp : ir.pos (.chal j) = i.1 := by rw [← hget, pos_get]
      have hasg : (ir.envOf I x ((ir.sourceSpec I).concat tr c)).asg = (ir.envOf I x tr).asg := by
        simp only [envOf]
        rw [roundAt_concat_of_lt tr c (by rw [pos_commit]; exact hi0)]
      have hchal : ∀ j', ir.ChalBefore j' j →
          (ir.envOf I x ((ir.sourceSpec I).concat tr c)).chal j' =
          ((ir.envOf I x tr).setChal j (cast hT c)).chal j' := by
        intro j' hj'
        by_cases hjj : j' = j
        · subst hjj
          funext q
          simp only [envOf, Env.setChal, Function.update_self]
          rw [roundAt_concat_chal tr c hget]
          rfl
        · have hupd : ((ir.envOf I x tr).setChal j (cast hT c)).chal j' =
              (ir.envOf I x tr).chal j' := Function.update_of_ne hjj _ _
          rw [hupd]
          simp only [envOf]
          by_cases hs : ir.IsSourceChal j'
          · have hle := pos_le_of_chalBefore hj hs hj'
            have hne : ir.pos (.chal j') ≠ ir.pos (.chal j) := fun e =>
              hjj (Round.chal.inj (ir.pos_injective (ir.chal_mem_rounds.2 hs)
                (ir.chal_mem_rounds.2 hj) e))
            rw [roundAt_concat_of_lt tr c (by omega)]
          · rw [roundAt_of_not_mem _ (fun e => hs (ir.chal_mem_rounds.1 e)),
              roundAt_of_not_mem tr (fun e => hs (ir.chal_mem_rounds.1 e))]
      have hlate : ∀ v, (ir.value v).phase < (ir.challenge j).phase →
          (ir.envOf I x ((ir.sourceSpec I).concat tr c)).late v =
            ((ir.envOf I x tr).setChal j (cast hT c)).late v := by
        intro v hv
        show (ir.envOf I x _).late v = (ir.envOf I x tr).late v
        simp only [envOf]
        by_cases hk : 1 ≤ (ir.value v).phase
        · rw [roundAt_concat_of_lt tr c (by have := pos_lt_of_late hj hk hv; omega)]
        · have hn : Round.late (ir.value v).phase ∉ ir.rounds := fun e =>
            hk (ir.late_mem_rounds.1 e).1
          rw [roundAt_of_not_mem _ hn, roundAt_of_not_mem tr hn]
      exact huse j { stmt := rfl, asg := hasg, chal := hchal, late := hlate }
    have hb := (card_le_iff_probUniform_le _ _ _).2 (hbound j hj (ir.envOf I x tr))
    calc (((Finset.univ.filter fun c : (ir.sourceSpec I).Challenge i =>
            (x, ir.sourceExtractor I proj i.1.castSucc x tr) ∉ rel ∧
              ¬ (ir.eventState I rel proj ev huse hsound).toFun i.1.castSucc x tr ∧
              (ir.eventState I rel proj ev huse hsound).toFun i.1.succ x
                ((ir.sourceSpec I).concat tr c)).card : ℕ) : ℝ≥0)
        ≤ ((Finset.univ.filter fun c : ir.ChalVal I j =>
            ev j ((ir.envOf I x tr).setChal j c)).card : ℝ≥0) := by
          refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun c => cast hT c) ?_ ?_)
          · intro c hc
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
            obtain ⟨j', hget', -, hev⟩ := hflip c hc.1 hc.2.1 hc.2.2
            obtain rfl : j' = j := by rw [hget] at hget'; exact (Round.chal.inj hget').symm
            exact (hset c).1 hev
          · intro c _ c' _ e
            exact (cast_inj hT).1 e
      _ ≤ ε j * Fintype.card (ir.ChalVal I j) := hb
      _ = ε j * Fintype.card ((ir.sourceSpec I).Challenge i) := by
          rw [Fintype.card_congr
            (Equiv.cast hT.symm : ir.ChalVal I j ≃ (ir.sourceSpec I).Challenge i)]
  · have herr : ir.roundError I ε i = 0 := by
      unfold roundError
      rw [hget]
    rw [herr, zero_mul]
    refine le_of_eq (Nat.cast_eq_zero.2 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_)))
    intro c _ hc
    obtain ⟨j', hget', -, -⟩ := hflip c hc.1 hc.2.1 hc.2.2
    rw [hget] at hget'
    cases hget'

end

end GordieHowe.RealizedProgram
