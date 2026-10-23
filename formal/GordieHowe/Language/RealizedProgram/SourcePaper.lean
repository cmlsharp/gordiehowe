-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.RealizedProgram.Protocol
public import GordieHowe.Model.IOP.MsgMap

@[expose] public section

/-!
# GordieHowe: the source program in the paper's form

The paper's language definitions (`def:o-preds`, `def:o-ip`, `def:o-honest`, `def:o-guarantees`)
against the source part of the realized program (`GordieHowe/Language/RealizedProgram/Source.lean`,
`GordieHowe/Language/RealizedProgram/Protocol.lean`, `GordieHowe/Language/Honest/Exec.lean`):

* **Sharing of bits**. The cross-field `equal` of the realized program
  (`GordieHowe.RealizedProgram.HoldsWith`) states that every reading of `y` is below `2^w` and that the readings of
  `x` and `y` agree where every reading of `x` is below `2^w`. Where both operands read bits, it
  is the paper's `pshare`, and `pshare` implies it in
  every environment. An accepting environment of the source
  program reads bits at both operands (`SourceAcceptingAt.crossBits`), so every source cross-field
  `equal` holds there as `pshare`.
* **The interactive proof of the source program** (`def:o-ip`, `GordieHowe.RealizedProgram.paperSpec`). The source
  protocol `Π_P₀` of the realized program (`GordieHowe.RealizedProgram.sourceSpec`) sends the committed assignment in its first
  message: the phase-`0` values and the pads of the late values. The paper's first message is the
  phase-`0` values alone. `GordieHowe.RealizedProgram.paperSpec` is the paper's protocol: the same rounds, the first
  message the phase-`0` values (`GordieHowe.RealizedProgram.PaperRoundTy`), the verifier `GordieHowe.RealizedProgram.paperVerifier`
  reading the transcript with zero pads, and the extractor `GordieHowe.RealizedProgram.paperExtractor` reading the
  statement and the phase-`0` values. Round-by-round knowledge soundness transfers in both
  directions with the same errors (`GordieHowe.RealizedProgram.rbr_paper_of_source`, `GordieHowe.RealizedProgram.rbr_source_of_paper`):
  the source program never reads a pad when no source value is a message (`GordieHowe.RealizedProgram.SrcNoMessage`,
  `Env.AgreeOnSourceVals.sourceSatAt_congr`), so the pads in the first message are data that the
  verifier ignores, which a prover may fill with anything.
* **The honest prover and the execution** (`def:o-honest`, `def:o-semantics`,
  `def:o-guarantees` (1)). `GordieHowe.RealizedProgram.SourceProver` is an honest prover of the source program with
  coins `Ω`; its execution draws the coins and the challenges uniformly. `GordieHowe.RealizedProgram.SourceComplete`
  is the paper's completeness with error `errc`: on the relation, the execution fails to accept
  with probability at most `errc` over the coins and the challenges. The plan-level execution
  `GordieHowe.RealizedProgram.SourceExecution`, the completeness hypothesis of the proof system, is the special case with no
  coins and the error the sum of its per-phase errors.
  Conversely, at every error `errc`, completeness gives an execution of the inputs with their coins
  (`GordieHowe.RealizedProgram.SourceComplete.toExecutionCore`, on `GordieHowe.RealizedProgram.execRel`) whose events have together
  probability at most `errc` over the coins and the challenges
  (`GordieHowe.RealizedProgram.SourceComplete.coinComplete`), the completeness hypothesis of the proof system for an honest
  prover with coins (`HonestCore.CoinComplete`).
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

section

variable (ir : RealizedProgram) {I : Interp}

/-! ## Sharing of bits -/

variable {ir}

/-! ## The interactive proof of the source program, first message without pads -/

variable (ir I)

/-- **The message type of a round of the paper's `Π_P₀`** (`def:o-ip`): the phase-`0` values, a
challenge's value, the late values of a phase, or the one element of `γ_end`. The source protocol's
first message also carries the pads (`RealizedProgram.RoundTy`). -/
def PaperRoundTy : Round → Type
  | .commit => ir.Valuation I
  | .chal j => ir.ChalVal I j
  | .late k => ir.LateMsg I k
  | .final => Unit

/-- **The paper's `Π_P₀`** (`def:o-ip`, under the exported phases): the rounds of `Π_P₀`
(`RealizedProgram.rounds`), the first message the phase-`0` values. -/
def paperSpec : ProtocolSpec ir.rounds.length where
  dir i := (ir.rounds.get i).dir
  «Type» i := ir.PaperRoundTy I (ir.rounds.get i)

/-- The challenge rounds of the paper's `Π_P₀` are finite. -/
abbrev paperFintype : (rd : Round) → rd.dir = .V_to_P → Fintype (ir.PaperRoundTy I rd)
  | .chal j, _ => inferInstanceAs (Fintype (ir.ChalVal I j))
  | .final, _ => inferInstanceAs (Fintype Unit)
  | .commit, h => nomatch h
  | .late _, h => nomatch h

/-- The challenge rounds of the paper's `Π_P₀` are nonempty. -/
theorem paperNonempty : (rd : Round) → rd.dir = .V_to_P → Nonempty (ir.PaperRoundTy I rd)
  | .chal _, _ => ⟨fun _ => default⟩
  | .final, _ => ⟨()⟩
  | .commit, h => nomatch h
  | .late _, h => nomatch h

instance (i : (ir.paperSpec I).ChallengeIdx) : Fintype ((ir.paperSpec I).Challenge i) :=
  ir.paperFintype I _ i.2

instance (i : (ir.paperSpec I).ChallengeIdx) : Nonempty ((ir.paperSpec I).Challenge i) :=
  ir.paperNonempty I _ i.2

/-- **A round's message without its pads**: the committed assignment's values; every other
message as it is. -/
def forgetRound : (rd : Round) → ir.RoundTy I rd → ir.PaperRoundTy I rd
  | .commit, a => a.val
  | .chal _, c => c
  | .late _, m => m
  | .final, u => u

/-- **A round's message with zero pads**: the phase-`0` values with the pads `0`; every other
message as it is. -/
def zeroRound : (rd : Round) → ir.PaperRoundTy I rd → ir.RoundTy I rd
  | .commit, v => ⟨v, 0⟩
  | .chal _, c => c
  | .late _, m => m
  | .final, u => u

/-- **A round's message with its pads replaced by `0`.** -/
def padsZero (rd : Round) (a : ir.RoundTy I rd) : ir.RoundTy I rd :=
  ir.zeroRound I rd (ir.forgetRound I rd a)

/-- Dropping the pads is a bijection at a challenge round (the identity). -/
theorem forgetRound_bijective :
    (rd : Round) → rd.dir = .V_to_P → Function.Bijective (ir.forgetRound I rd)
  | .chal _, _ => Function.bijective_id
  | .final, _ => Function.bijective_id
  | .commit, h => nomatch h
  | .late _, h => nomatch h

/-- Zero pads are a bijection at a challenge round (the identity). -/
theorem zeroRound_bijective :
    (rd : Round) → rd.dir = .V_to_P → Function.Bijective (ir.zeroRound I rd)
  | .chal _, _ => Function.bijective_id
  | .final, _ => Function.bijective_id
  | .commit, h => nomatch h
  | .late _, h => nomatch h

/-- **Dropping the pads**: a transcript of `Π_P₀` read as one of the paper's `Π_P₀`. -/
def forgetPads : (ir.sourceSpec I).MsgMap (ir.paperSpec I) where
  dir_eq _ := rfl
  map i := ir.forgetRound I (ir.rounds.get i)
  bijective i := ir.forgetRound_bijective I (ir.rounds.get i)

/-- **Zero pads**: a transcript of the paper's `Π_P₀` read as one of `Π_P₀` with the pads `0`. -/
def zeroPads : (ir.paperSpec I).MsgMap (ir.sourceSpec I) where
  dir_eq _ := rfl
  map i := ir.zeroRound I (ir.rounds.get i)
  bijective i := ir.zeroRound_bijective I (ir.rounds.get i)

/-- **The environment of a transcript of the paper's `Π_P₀`** at the statement `x`: the environment
of the transcript of `Π_P₀` with zero pads (`RealizedProgram.envOf`). -/
def paperEnvOf {m : Fin (ir.rounds.length + 1)} (x : ir.Valuation I)
    (tr : (ir.paperSpec I).Transcript m) : ir.Env I :=
  ir.envOf I x ((ir.zeroPads I).transcript tr)

/-- **The verifier of the paper's `Π_P₀`**: it accepts when the statement passes the program's
member checks, every source predicate holds and every node-typed source value lies in its type, in
the environment of the transcript (`RealizedProgram.paperEnvOf`). -/
def paperVerifier : Verifier (ir.paperSpec I) (ir.Valuation I) :=
  fun x tr => ir.stmtOk I x && decide (ir.SourceSatAt (ir.paperEnvOf I x tr))

/-- **The extractor of the paper's `Π_P₀` that reads the statement and the phase-`0` values**:
`proj` at the statement and the phase-`0` values of the first message (`0` before it is sent).

Running time: one read of the transcript's first round and one call of `proj`; polynomial when
`proj` is. This running time is argued here, not proved in Lean. -/
def paperExtractor {W : Type} (proj : ir.Valuation I → ir.Valuation I → W) :
    Extractor (ir.paperSpec I) (ir.Valuation I) W :=
  (ir.sourceExtractor I fun x a => proj x a.val).comap (ir.zeroPads I)

variable {ir I}

/-- **Reading a round of a transcript mapped round by round**: the round's message mapped. -/
theorem roundAt_map (f : ∀ rd, ir.RoundTy I rd → ir.RoundTy I rd)
    {m : Fin (ir.rounds.length + 1)} (tr : (ir.sourceSpec I).Transcript m) (rd : Round) :
    ir.roundAt I (fun i => f _ (tr i)) rd = (ir.roundAt I tr rd).map (f rd) := by
  have key : ∀ (r : Round) (e : r = rd) (z : ir.RoundTy I r),
      cast (congrArg (ir.RoundTy I) e) (f r z) = f rd (cast (congrArg (ir.RoundTy I) e) z) := by
    rintro _ rfl z
    rfl
  unfold roundAt
  split_ifs
  · exact congrArg some (key _ (ir.get_pos (by omega)) _)
  · rfl

/-- **Zero pads after dropping the pads replace the pads by `0`.** -/
theorem zeroPads_forgetPads {m : Fin (ir.rounds.length + 1)}
    (tr : (ir.sourceSpec I).Transcript m) :
    (ir.zeroPads I).transcript ((ir.forgetPads I).transcript tr) =
      fun i => ir.padsZero I _ (tr i) :=
  rfl

/-- **Replacing the pads by `0` keeps a transcript with zero pads.** -/
theorem padsZero_zeroRound : ∀ (rd : Round) (z : ir.PaperRoundTy I rd),
    ir.padsZero I rd (ir.zeroRound I rd z) = ir.zeroRound I rd z
  | .commit, _ => rfl
  | .chal _, _ => rfl
  | .late _, _ => rfl
  | .final, _ => rfl

/-- **A transcript with zero pads keeps them** when its pads are replaced by `0`. -/
theorem padsZero_zeroPads {m : Fin (ir.rounds.length + 1)}
    (tr : (ir.paperSpec I).Transcript m) :
    (fun i => ir.padsZero I _ ((ir.zeroPads I).transcript tr i)) =
      (ir.zeroPads I).transcript tr :=
  funext fun _ => padsZero_zeroRound _ _

/-- **The committed values of a transcript do not change when its pads are replaced by `0`.** -/
theorem commit_val_padsZero {m : Fin (ir.rounds.length + 1)}
    (tr : (ir.sourceSpec I).Transcript m) :
    ((ir.roundAt I (fun i => ir.padsZero I _ (tr i)) .commit).getD ⟨0, 0⟩).val =
      ((ir.roundAt I tr .commit).getD ⟨0, 0⟩).val := by
  rw [roundAt_map]
  cases ir.roundAt I tr .commit <;> rfl

/-- **The committed assignment of a transcript with its pads replaced by `0`** is its committed
values with the pads `0`. -/
theorem commit_padsZero {m : Fin (ir.rounds.length + 1)}
    (tr : (ir.sourceSpec I).Transcript m) :
    (ir.roundAt I (fun i => ir.padsZero I _ (tr i)) .commit).getD ⟨0, 0⟩ =
      ⟨((ir.roundAt I tr .commit).getD ⟨0, 0⟩).val, 0⟩ := by
  rw [roundAt_map]
  cases ir.roundAt I tr .commit <;> rfl

/-- **Replacing the pads by `0` keeps the source values**: the environments of a transcript and of
the transcript with its pads replaced by `0` have one statement, the same challenges, the same late
values and the same committed values. -/
theorem agreeOnSourceVals_padsZero (x : ir.Valuation I) {m : Fin (ir.rounds.length + 1)}
    (tr : (ir.sourceSpec I).Transcript m) :
    Env.AgreeOnSourceVals (ir.envOf I x tr) (ir.envOf I x fun i => ir.padsZero I _ (tr i)) where
  stmt := rfl
  chal j _ := by
    funext c
    simp only [envOf]
    rw [roundAt_map]
    cases ir.roundAt I tr (.chal j) <;> rfl
  late u _ := by
    funext c
    simp only [envOf]
    rw [roundAt_map]
    cases ir.roundAt I tr (.late (ir.value u).phase) <;> rfl
  val u _ := by
    simp only [envOf]
    rw [commit_val_padsZero]

/-- **The paper's verifier accepts a transcript of `Π_P₀` without its pads** where `Π_P₀`'s verifier
accepts it, when the source part is well formed and no source value is a message: the source
program reads no pad. -/
theorem paperVerifier_forgetPads (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    (x : ir.Valuation I) (tr : (ir.sourceSpec I).Transcript (Fin.last _))
    (h : ir.sourceVerifier I x tr = true) :
    ir.paperVerifier I x ((ir.forgetPads I).transcript tr) = true := by
  simp only [sourceVerifier, paperVerifier, paperEnvOf, zeroPads_forgetPads, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  exact ⟨h.1, decide_eq_true (((agreeOnSourceVals_padsZero x tr).sourceSatAt_congr hs hnm).1 h.2)⟩

/-- **The source extractor of a projection reading the pads as `0`, on a transcript with zero
pads, is the paper's extractor.** -/
theorem sourceExtractor_comap_zeroPads {W : Type} (proj : ir.Valuation I → ir.Assignment I → W) :
    (ir.sourceExtractor I proj).comap (ir.zeroPads I) =
      ir.paperExtractor I fun x v => proj x ⟨v, 0⟩ := by
  unfold paperExtractor Extractor.comap sourceExtractor
  congr 1
  funext m x tr
  change proj x ((ir.roundAt I ((ir.zeroPads I).transcript tr) .commit).getD ⟨0, 0⟩) =
    proj x ⟨((ir.roundAt I ((ir.zeroPads I).transcript tr) .commit).getD ⟨0, 0⟩).val, 0⟩
  conv_lhs => rw [← padsZero_zeroPads tr]
  rw [commit_padsZero]

/-- **The paper's extractor, on a transcript of `Π_P₀` without its pads, is the source extractor of
the projection reading the committed values.** -/
theorem paperExtractor_comap_forgetPads {W : Type} (proj : ir.Valuation I → ir.Valuation I → W) :
    (ir.paperExtractor I proj).comap (ir.forgetPads I) =
      ir.sourceExtractor I fun x a => proj x a.val := by
  unfold paperExtractor Extractor.comap sourceExtractor
  congr 1
  funext m x tr
  change proj x ((ir.roundAt I (fun i => ir.padsZero I _ (tr i)) .commit).getD ⟨0, 0⟩).val =
    proj x ((ir.roundAt I tr .commit).getD ⟨0, 0⟩).val
  rw [commit_val_padsZero]

/-- **Round-by-round knowledge soundness of `Π_P₀` gives that of the paper's `Π_P₀`** (`def:o-ip`,
`def:o-guarantees` (2)): at the extractor reading the statement and the phase-`0` values with the
pads `0`, the state function read with zero pads and the same error at each challenge round. -/
theorem rbr_paper_of_source {W : Type} {rel : Set (ir.Valuation I × W)}
    {proj : ir.Valuation I → ir.Assignment I → W} {S : KnowledgeStateFunction (ir.sourceVerifier I)}
    {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε) :
    rbrKnowledgeSoundness rel (ir.paperVerifier I) (ir.paperExtractor I fun x v => proj x ⟨v, 0⟩)
      (S.comap (ir.zeroPads I) fun _ _ h => h) fun i => ε ((ir.zeroPads I).chalIdx i) := by
  have h' := h.comap (ir.zeroPads I) (V' := ir.paperVerifier I) fun _ _ h => h
  rwa [sourceExtractor_comap_zeroPads] at h'

/-- **Round-by-round knowledge soundness of the paper's `Π_P₀` gives that of `Π_P₀`**
(`def:o-ip`, `def:o-guarantees` (2)), when the source part is well formed and no source value is a
message: at the extractor reading the statement and the committed values, the state function read
without the pads and the same error at each challenge round. The pads in the first message of
`Π_P₀` are data that its verifier does not read (`paperVerifier_forgetPads`). -/
theorem rbr_source_of_paper (hs : ir.SourceValid) (hnm : ir.SrcNoMessage) {W : Type}
    {rel : Set (ir.Valuation I × W)} {proj : ir.Valuation I → ir.Valuation I → W}
    {S : KnowledgeStateFunction (ir.paperVerifier I)} {ε : (ir.paperSpec I).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel (ir.paperVerifier I) (ir.paperExtractor I proj) S ε) :
    rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I fun x a => proj x a.val)
      (S.comap (ir.forgetPads I) (paperVerifier_forgetPads hs hnm))
      fun i => ε ((ir.forgetPads I).chalIdx i) := by
  have h' := h.comap (ir.forgetPads I) (paperVerifier_forgetPads hs hnm)
  rwa [paperExtractor_comap_forgetPads] at h'

/-! ## The honest prover and the execution -/

variable (ir I)

/-- **An honest prover of the source program** (paper, `def:o-honest`) on honest inputs `Inp`, with
coins `Ω`: the statement of an input, and the source program's phase-`0` values and its late
values as functions of the coins and the challenges, the late values reading only their exported
challenges. The realized program does not state the randomized functions of a program (`priv(f, y)`,
`def:o-programs`), so the prover is supplied, not computed from the program. -/
structure SourceProver (Inp Ω : Type) where
  /-- The statement of an honest input. -/
  stmtOf : Inp → ir.Valuation I
  /-- The phase-`0` values, from the coins. -/
  val : Inp → Ω → ir.Valuation I
  /-- The late values, from the coins and the challenges. -/
  late : Inp → Ω → (∀ k, (ir.layout I).Ch k) → ir.Valuation I
  /-- The late values read only their exported challenges. -/
  respects : ∀ y ω, ir.SourceRespectsReads I (late y ω)

/-- **An execution accepts** in the environment `e`: the source program accepts
(`SourceAcceptingAt`, the paper's accepting assignment), the source `mod_q`s in the field
form hold as their field equations (`FieldEqsAt`), and the packing of every table packed at a
challenge is injective on its records (`PackFreeAt`, automatic for a program with no such table). -/
structure ExecutionAccepts (e : ir.Env I) : Prop where
  /-- The source program accepts. -/
  accepting : ir.SourceAcceptingAt I e
  /-- The field-form `mod_q`s hold as field equations. -/
  fieldEqs : ir.FieldEqsAt I e
  /-- The packings of the tables packed at a challenge are injective on their records. -/
  packFree : ir.PackFreeAt I e

variable {ir I}

/-- **The environment of the execution of an honest prover** (`def:o-semantics`, `Exec_{P₀}`) at the
statement `x`, the input `y`, the coins `ω` and the challenges `c`. -/
def SourceProver.execEnvAt {Inp Ω : Type} (H : ir.SourceProver I Inp Ω) (x : ir.Valuation I)
    (y : Inp) (ω : Ω) (c : ∀ k, (ir.layout I).Ch k) : ir.Env I :=
  ir.execEnv I x (H.val y ω) (H.late y ω c) c

variable (ir I) in
/-- **The source program is complete for `relH` with error `errc` at the honest prover `H`** (paper,
`def:o-guarantees` (1)): on the relation, the input's statement is the statement, the statement
lies in `Stmt_P₀` (`checks`, `bounded`), and the execution, with uniform coins and challenges,
fails to accept with probability at most `errc`. -/
structure SourceComplete {Inp Ω : Type} [Fintype Ω] [Nonempty Ω]
    (relH : Set (ir.Valuation I × Inp)) (H : ir.SourceProver I Inp Ω) (errc : ℝ≥0) : Prop where
  /-- The statement of a related input is its statement. -/
  stmt : ∀ x y, (x, y) ∈ relH → x = H.stmtOf y
  /-- The honest statements pass the program's member checks. -/
  checks : ∀ x y, (x, y) ∈ relH → ir.StatementOk I x
  /-- The honest statements lie within the declared bounds. -/
  bounded : ∀ x y, (x, y) ∈ relH → ir.StmtBounded I x
  /-- The execution fails to accept with probability at most `errc`. -/
  accepting : ∀ x y, (x, y) ∈ relH →
    Pr[ωc ← (Ω × ∀ k, (ir.layout I).Ch k) : ¬ ir.ExecutionAccepts I (H.execEnvAt x y ωc.1 ωc.2)] ≤ errc

/-- **An honest input with its coins.** -/
structure WithCoins (Inp Ω : Type) where
  /-- The honest input. -/
  input : Inp
  /-- The prover's coins. -/
  coins : Ω

variable (ir I) in
/-- **The inputs with coins of an honest prover's execution**: a statement and an input with coins,
where the statement and the input are related and, for a program without phases, the execution
accepts at the coins. With a phase the second condition holds whatever the coins. Without one the
challenges are trivial, a failed execution has no phase to charge its event to, and the input with
these coins is left off the relation (`HonestCore.CoinComplete` charges it). -/
def execRel {Inp Ω : Type} (relH : Set (ir.Valuation I × Inp)) (H : ir.SourceProver I Inp Ω) :
    Set (ir.Valuation I × WithCoins Inp Ω) :=
  {xy | (xy.1, xy.2.input) ∈ relH ∧
    (ir.phases = 0 → ∀ c, ir.ExecutionAccepts I (H.execEnvAt xy.1 xy.2.input xy.2.coins c))}

/-- **An execution with no completeness event accepts**: with a phase, the event of phase `0` is
the failure; without one, the relation says so (`execRel`). -/
theorem execAccepts_of_execRel {Inp Ω : Type} {relH : Set (ir.Valuation I × Inp)}
    {H : ir.SourceProver I Inp Ω} {x : ir.Valuation I} {y : WithCoins Inp Ω}
    (hy : (x, y) ∈ ir.execRel I relH H) {c : ∀ k, (ir.layout I).Ch k}
    (hc : ∀ _k : Fin ir.phases, ¬ ¬ ir.ExecutionAccepts I (H.execEnvAt x y.input y.coins c)) :
    ir.ExecutionAccepts I (H.execEnvAt x y.input y.coins c) := by
  by_cases h0 : ir.phases = 0
  · exact hy.2 h0 c
  · exact not_not.mp (hc ⟨0, Nat.pos_of_ne_zero h0⟩)

/-- **The execution of an honest prover** (`SourceExecutionCore`) on the inputs with their coins
(`execRel`): the prover's values at the input's coins, and at every phase the completeness event
that the execution fails to accept. -/
def SourceProver.toExecutionCore {Inp Ω : Type} {relH : Set (ir.Valuation I × Inp)}
    (H : ir.SourceProver I Inp Ω) (hstmt : ∀ x y, (x, y) ∈ relH → x = H.stmtOf y)
    (hchecks : ∀ x y, (x, y) ∈ relH → ir.StatementOk I x)
    (hbounded : ∀ x y, (x, y) ∈ relH → ir.StmtBounded I x) :
    ir.SourceExecutionCore I (ir.execRel I relH H) where
  stmtOf y := H.stmtOf y.input
  stmt x y hy := hstmt x y.input hy.1
  val y := H.val y.input y.coins
  late y := H.late y.input y.coins
  respects y := H.respects y.input y.coins
  bad _ x y c := ¬ ir.ExecutionAccepts I (H.execEnvAt x y.input y.coins c)
  checks x y hy := hchecks x y.input hy.1
  bounded x y hy := hbounded x y.input hy.1
  accepting x y hy c hc := (execAccepts_of_execRel hy hc).accepting
  fieldEqs x y hy c hc := (execAccepts_of_execRel hy hc).fieldEqs
  packFree x y hy c hc := (execAccepts_of_execRel hy hc).packFree

/-- **The execution of a complete program** (`SourceProver.toExecutionCore` at the statement facts of
`SourceComplete`). -/
def SourceComplete.toExecutionCore {Inp Ω : Type} [Fintype Ω] [Nonempty Ω]
    {relH : Set (ir.Valuation I × Inp)} {H : ir.SourceProver I Inp Ω} {errc : ℝ≥0}
    (h : ir.SourceComplete I relH H errc) : ir.SourceExecutionCore I (ir.execRel I relH H) :=
  H.toExecutionCore h.stmt h.checks h.bounded

/-- **A program complete with error `errc` has an execution with completeness error `errc` over
the coins** (`def:o-guarantees` (1) to `SourceExecutionCore.CoinComplete`): on the relation, over
uniform coins and challenges, the input with its coins is off `execRel` or meets a completeness
event only where the execution fails to accept, which has probability at most `errc`. Off
`execRel` the program has no phase, so the challenges are trivial and the failure at some
challenge is the failure at every one. -/
theorem SourceComplete.coinComplete {Inp Ω : Type} [Fintype Ω] [Nonempty Ω]
    {relH : Set (ir.Valuation I × Inp)} {H : ir.SourceProver I Inp Ω} {errc : ℝ≥0}
    (h : ir.SourceComplete I relH H errc) : h.toExecutionCore.CoinComplete relH WithCoins.mk fun _ => errc := by
  intro x y hy
  refine le_trans (QROM.probUniform_mono fun u hu => ?_) (h.accepting x y hy)
  rcases hu with hu | ⟨_, hk⟩
  · have hn : ir.phases = 0 ∧ ∃ c, ¬ ir.ExecutionAccepts I (H.execEnvAt x y u.1 c) := by
      by_contra hn
      refine hu ⟨hy, fun h0 c => ?_⟩
      by_contra hc
      exact hn ⟨h0, c, hc⟩
    obtain ⟨h0, c, hc⟩ := hn
    have hu2 : u.2 = c := funext fun k => absurd k.2 (by omega)
    rw [hu2]
    exact hc
  · exact hk

end

end GordieHowe.RealizedProgram
