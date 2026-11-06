-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.CertifiedProgram
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.ProofSystem.Program.EndToEnd
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHoweNative.Language.ProgramData

public section

/-!
# A configuration from a certified program and a frontend

A configuration under spBCS (`GordieHowe.Configuration`) is built from the certified data the
compiler emits for its program (`GordieHowe.RealizedProgram.CertifiedProgram`) and an
application's frontend:

* `GordieHowe.Configuration.SourceFront`: the source program's soundness (the relation, the
  extractor's projection, the state function, the source challenges' errors, round-by-round
  knowledge soundness of `Π_P₀`, the errors' bound by the generated fractions) and the honest
  nodes' `1`;
* `GordieHowe.Configuration.Frontend`: the statement's codec and its program statement, the headline
  relation and the witness map, the honest relation and the source program's execution, the
  statement of an honest input and the label. `GordieHowe.Configuration.FrontendWith` adds a check
  of the statement (the ring configurations, `IOP.comapWith`). Their facts are Prop structures
  (`Frontend.Facts`, `FrontendWith.Facts`) of named application theorems.

The statement, witness and honest-input types are parameters of the frontend, never fields.

`GordieHowe.Configuration.ofCertified` (`ofCertifiedWith`) is the configuration, a structure
literal over the templates below, and `ofCertified_grantedFacts` (`ofCertifiedWith_grantedFacts`)
its facts, with `ofCertified_facts` (`ofCertifiedWith_facts`) when the transcript grants no
extended stream. The templates (`@[config_template]`) are instantiated once per application,
before the configuration's own templates, in four families:

* `CertifiedSource`: the lowering, the ready data of the honest strategy, and the plan-level
  headlines at the proof system (`iop_rbr_knowledge_soundness`, `iop_completeness`, `iop_hvzk`);
* `CertifiedHonest`: the honest strategy at the frontend's execution;
* `CertifiedFront`: the IOP read through the statement map, its soundness data, its transcript and
  the honest relation at the statements;
* `CertifiedFrontWith`: the same with the statement check.

The configuration's own instances then name these instances in their statements
(`instantiate_config` folds an earlier instance of the namespace).
-/

namespace GordieHowe.Configuration

open IOP RealizedProgram RealizedProgram.ProofSystem RealizedProgram.ProofSystem.PhaseLayout
  GordieHowe.SPBCS SPBCS.Configurations GordieHowe.QROM
open scoped NNReal ENNReal

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp}

attribute [config_record] RealizedProgram.CertifiedProgram ProgramData RuntimeInputs CompletionInputs
  FiguresData

/-- **The source program's soundness at a certified program** (module docstring): round-by-round
knowledge soundness of `Π_P₀` for `rel` at the extractor reading the statement and the phase-`0`
values through `proj`, the state function `S` and the errors `ε` at the source challenges
(`roundError eps`), which vanish at `γ_end` and are within the generated fractions; and the honest
nodes contain `1`. The state function is a parameter, so that the statements read it as the
application states it (it contains the frontend's soundness proofs). -/
@[config_record]
structure SourceFront (cp : CertifiedProgram P ir I) (W : Type)
    (S : KnowledgeStateFunction (ir.sourceVerifier I)) where
  /-- The relation of the source program. -/
  rel : Set (ir.Valuation I × W)
  /-- The extractor's projection of the committed assignment. -/
  proj : ir.Valuation I → ir.Assignment I → W
  /-- The source challenges' errors. -/
  eps : ℕ → ℝ≥0
  /-- Round-by-round knowledge soundness of `Π_P₀`. -/
  sound : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S
    (ir.roundError I eps)
  /-- The errors vanish at `γ_end`. -/
  final : ∀ i, ir.rounds.get i.1 = .final → ir.roundError I eps i = 0
  /-- The errors are within the generated fractions. -/
  eps_le : ∀ j, ir.IsSourceChal j → eps j ≤ ((cp.sourceErrors j).1 : ℝ≥0) / (cp.sourceErrors j).2
  /-- The honest nodes contain `1`. -/
  oneNodes : OneNodes I cp.nodes

/-- **An application's frontend at a certified program** (module docstring): the statement's codec,
its program statement, the headline relation and the witness map, the honest relation, the source
program's execution at the ready data of the honest strategy, the statement of an honest input
and the label. -/
@[config_record]
structure Frontend (cp : CertifiedProgram P ir I) {W : Type}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} (_src : SourceFront cp W S)
    (Stmt W' HonestIn : Type) where
  /-- The codec of a statement. -/
  codec : Codec Stmt
  /-- The program statement of a statement. -/
  stmtOf : Stmt → ir.Valuation I
  /-- The headline relation. -/
  rel' : Set (Stmt × W')
  /-- The witness map. -/
  g : Stmt → (ir.Valuation I → W) → W'
  /-- The honest relation at the program statements. -/
  relH : Set (ir.Valuation I × HonestIn)
  /-- The execution of the source program at the ready data of the honest strategy. -/
  exec : cp.Ready → ir.SourceExecution I relH
  /-- The statement of an honest input. -/
  keyStmtOf : HonestIn → Stmt
  /-- The label. -/
  label : List Byte

/-- **A frontend with a statement check** (`IOP.comapWith`): `Frontend` and the check `ok`. -/
@[config_record]
structure FrontendWith (cp : CertifiedProgram P ir I) {W : Type}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} (src : SourceFront cp W S)
    (Stmt W' HonestIn : Type) extends Frontend cp src Stmt W' HonestIn where
  /-- The statement check. -/
  ok : Stmt → Bool

variable {cp : CertifiedProgram P ir I} {W : Type} {S : KnowledgeStateFunction (ir.sourceVerifier I)}
  {src : SourceFront cp W S}
  {Stmt W' HonestIn : Type}

/-- **The facts of a frontend**: the statement's writes within `2^20` bytes, the label within
`2^10` bytes, the witness map into the headline relation, no completeness event of the execution,
and every honest input honest at its statement. -/
structure Frontend.Facts (F : Frontend cp src Stmt W' HonestIn) : Prop where
  /-- The statement's writes have at most `2^20` bytes. -/
  codec_le : ∀ x, (F.codec.ser x).length ≤ 2 ^ 20
  /-- The label has at most `2^10` bytes. -/
  label_le : F.label.length ≤ 2 ^ 10
  /-- The witness map sends the relation at the program statements into the headline relation. -/
  mem_rel' : ∀ x w, (F.stmtOf x, w) ∈ relOf src.rel → (x, F.g x w) ∈ F.rel'
  /-- The execution has no completeness event. -/
  exec_δ : ∀ R, ∑ k, (F.exec R).δ k = 0
  /-- An honest input is honest at its statement. -/
  keyStmtOf_mem : ∀ y, (F.stmtOf (F.keyStmtOf y), y) ∈ F.relH

/-- **The facts of a frontend with a statement check** (`Frontend.Facts`, the relations at the
statements that pass the check). -/
structure FrontendWith.Facts (F : FrontendWith cp src Stmt W' HonestIn) : Prop where
  /-- The statement's writes have at most `2^20` bytes. -/
  codec_le : ∀ x, (F.codec.ser x).length ≤ 2 ^ 20
  /-- The label has at most `2^10` bytes. -/
  label_le : F.label.length ≤ 2 ^ 10
  /-- The witness map sends the relation at the checked program statements into the headline
  relation. -/
  mem_rel' : ∀ x w, F.ok x = true ∧ (F.stmtOf x, w) ∈ relOf src.rel → (x, F.g x w) ∈ F.rel'
  /-- The execution has no completeness event. -/
  exec_δ : ∀ R, ∑ k, (F.exec R).δ k = 0
  /-- An honest input's statement passes the check and is honest. -/
  keyStmtOf_mem : ∀ y, F.ok (F.keyStmtOf y) = true ∧ (F.stmtOf (F.keyStmtOf y), y) ∈ F.relH

/-! ## The source family -/

namespace CertifiedSource

variable (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)

/-- **The lowering of the soundness theorem** on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
@[config_template]
abbrev forkLowering (C : ir.ProofSystem P I) :=
  (C.withFieldProofs cp.ready).lowering ⟨_, src.sound, src.final⟩

/-- **The ready data of the honest strategy** (`RealizedProgram.CompletionReady.ofGenerated`): the
generated facts and the honest nodes, which contain `1`. -/
@[config_template, expose]
def completionReady : cp.Ready :=
  cp.completionReady src.oneNodes

/-- **Soundness at the realized program, in the series–parallel order of `prot:backend`**
(`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of the proof system): the series–parallel composite is
round-by-round knowledge sound for the source relation at the proof system's extractor
(`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's witness map at the
realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the
phase's challenges of `Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`),
at every other challenge the error of that challenge in its domain's commit rounds, branches or
join part. -/
@[config_template headline]
theorem iop_rbr_knowledge_soundness [Inhabited W] (C : ir.ProofSystem P I) :
    CausalRBRKnowledgeSound src.rel
      ((C.fieldBranches cp.ready).soundIOP src.sound src.final).verifier
      ((C.fieldBranches cp.ready).extractor src.sound src.final)
      ((C.fieldBranches cp.ready).soundIOPSound (C.fieldBranchesSound cp.ready) src.sound
        src.final).stateFn
      ((C.fieldBranches cp.ready).soundIOPSound (C.fieldBranchesSound cp.ready) src.sound
        src.final).error :=
  (C.fieldBranches cp.ready).causal_rbr_knowledge_soundness (C.fieldBranchesSound cp.ready)
    src.sound src.final

/-- **Completeness at the realized program** (`ProofSystem.FieldBranches.completeness` at the
forked domains `ProofSystem.fieldBranches` of the proof system, the domains' honest provers
`RealizedProgram.ProofSystem.fieldHonestDomains`): in the series–parallel order of
`prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the
statement) (`hc`), then at every value of the coins, on every honest input, the honest prover is
rejected with probability at most `errc`. -/
@[config_template headline]
theorem iop_completeness (C : ir.ProofSystem P I) {Inp : Type}
    {relH : Set (ir.Valuation I × Inp)} (H : ir.HonestCore I relH)
    {errc : ir.Valuation I → ℝ≥0} (hc : H.Complete errc)
    (c : (C.fieldForkHonest cp.ready H).Coins) :
    CausalCompleteStmt relH (C.fieldBranches cp.ready).protocol.verifier
      (fun y => RealizedProgram.ProofSystem.IOP.honest (C.fieldForkHonest cp.ready H) y c) errc :=
  (C.fieldBranches cp.ready).completeness (C.fieldHonestDomains cp.ready) _ H hc c

/-- **Honest-verifier zero knowledge at the realized program** (`ProofSystem.FieldBranches.hvzk`
at the forked domains of the proof system): in the series–parallel order of `prot:backend`, if the
honest prover `H` has completeness error `errc` (a function of the statement) (`hc`), the
simulator of the series–parallel composite is honest-verifier zero knowledge for the honest
prover with error `errc`. -/
@[config_template headline]
theorem iop_hvzk (C : ir.ProofSystem P I) {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
    (H : ir.HonestCore I relH) {errc : ir.Valuation I → ℝ≥0} (hc : H.Complete errc) :
    CausalHVZKStmt (C.fieldBranches cp.ready).protocol.toCausalIOP.views relH
      (RealizedProgram.ProofSystem.IOP.honest (C.fieldForkHonest cp.ready H)) id
      (RealizedProgram.ProofSystem.IOP.simulator
        ((C.fieldBranches cp.ready).simData (C.fieldForkSims cp.ready))) errc :=
  (C.fieldBranches cp.ready).hvzk (C.fieldHonestDomains cp.ready) _ H hc

end CertifiedSource

/-! ## The honest strategy -/

namespace CertifiedHonest

variable (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)
  (F : Frontend cp src Stmt W' HonestIn)

/-- **The honest strategy** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the frontend's
execution of the source program at the ready data). -/
@[config_template keep_binders, expose]
noncomputable def honestStrategy : ir.HonestStrategy I F.relH :=
  HonestStrategy.ofCompletionReady (CertifiedSource.completionReady cp src)
    (F.exec (CertifiedSource.completionReady cp src))

end CertifiedHonest

/-! ## The frontend family -/

namespace CertifiedFront

variable (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)
  (F : Frontend cp src Stmt W' HonestIn)

/-- **The multi-circuit IOP with forked domains at the statements**: the generic per-field domain
proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
source program's round-by-round knowledge soundness, the statement read as its program statement. -/
@[config_template]
abbrev forkIop (C : ir.ProofSystem P I) :
    RealizedProgram.ProofSystem.IOP Stmt (ir.Valuation I → W)
      {p | (F.stmtOf p.1, p.2) ∈ relOf src.rel} :=
  C.fieldIop cp.ready (CertifiedSource.forkLowering cp src C) F.stmtOf

/-- **The soundness data of `forkIop`** (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`,
`RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
@[config_template]
noncomputable abbrev forkIopSound (C : ir.ProofSystem P I) : (forkIop cp src F C).Sound :=
  ((C.fieldBranches cp.ready).soundIOPSound (C.fieldBranchesSound cp.ready) src.sound
    src.final).comap F.stmtOf

/-- **The C++ series–parallel transcript** (`RealizedProgram.ProofSystem.fieldForkTranscript`):
the label, the generated digest length, the statement's writes, every branch named by its domain's
field, the phases' codecs (`RealizedProgram.appWrites`) and readers (`RealizedProgram.appReaders`),
every domain's at the generated numbers, and the largest grant of a round. -/
@[config_template]
abbrev forkTranscript (C : ir.ProofSystem P I) : ProofSystemTranscript (forkIop cp src F C) :=
  C.fieldForkTranscript cp.ready (CertifiedSource.forkLowering cp src C) F.stmtOf cp.numbers.cod
    (cp.numbers.fits C.enforce) F.label cp.figures.k F.codec (fun a => cp.branchName a.1)
    (ir.appWrites cp.fieldBytes cp.msgB_le)
    (ir.appReaders cp.samplerReaders (fun _ => cp.chalLoadMax) cp.chalLoad_le) cp.grantMax

/-- **The honest inputs at the statements**: the strategy's honest inputs at the statements'
program statements. -/
@[config_template keep_binders]
abbrev keyHonestRel {Inp : Type} (relH : Set (ir.Valuation I × Inp)) : Set (Stmt × Inp) :=
  {p | (F.stmtOf p.1, p.2) ∈ relH}

/-- **The largest round error of the series–parallel composite** is at most
`errorMax / 2^errorExp` (`RealizedProgram.ProofSystem.fieldForkError_le`): every domain's round
charges and every phase's error (`RealizedProgram.ProgramFigures.Check.fieldRoundsLe`,
`RealizedProgram.ProgramFigures.Check.phaseError_le`). -/
@[config_template]
theorem maxRoundError_le [Inhabited W] (C : ir.ProofSystem P I) :
    maxError (CertifiedFront.forkIopSound cp src F C).error ≤
      (cp.figures.errorMax : ℝ≥0) / 2 ^ cp.figures.errorExp :=
  maxError_le_iff.2 (C.fieldForkError_le cp.ready F.stmtOf src.sound src.final
    (cp.figuresOk.fieldRoundsLe cp.fieldCard)
    (fun _ => cp.figuresOk.phaseError_le cp.fieldCard src.eps src.eps_le _))

end CertifiedFront

/-! ## The frontend family with a statement check -/

namespace CertifiedFrontWith

variable (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)
  (F : FrontendWith cp src Stmt W' HonestIn)

/-- **The multi-circuit IOP with forked domains at the checked statements**: the generic per-field
domain proofs with the proof system's application phase, the statement read as its program
statement and checked (`RealizedProgram.ProofSystem.IOP.comapWith`). -/
@[config_template]
abbrev forkIop (C : ir.ProofSystem P I) :
    RealizedProgram.ProofSystem.IOP Stmt (ir.Valuation I → W)
      {p | F.ok p.1 = true ∧ (F.stmtOf p.1, p.2) ∈ relOf src.rel} :=
  C.fieldIopWith cp.ready (CertifiedSource.forkLowering cp src C) F.stmtOf F.ok

/-- **The soundness data of `forkIop`** (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`,
`RealizedProgram.ProofSystem.IOP.Sound.comapWith`). -/
@[config_template]
noncomputable abbrev forkIopSound (C : ir.ProofSystem P I) : (forkIop cp src F C).Sound :=
  ((C.fieldBranches cp.ready).soundIOPSound (C.fieldBranchesSound cp.ready) src.sound
    src.final).comapWith F.stmtOf F.ok

/-- **The C++ series–parallel transcript at the checked statements**
(`RealizedProgram.ProofSystem.fieldForkTranscriptWith`, as `CertifiedFront.forkTranscript`). -/
@[config_template]
abbrev forkTranscript (C : ir.ProofSystem P I) : ProofSystemTranscript (forkIop cp src F C) :=
  C.fieldForkTranscriptWith cp.ready (CertifiedSource.forkLowering cp src C) F.stmtOf
    cp.numbers.cod (cp.numbers.fits C.enforce) F.ok F.label cp.figures.k F.codec
    (fun a => cp.branchName a.1) (ir.appWrites cp.fieldBytes cp.msgB_le)
    (ir.appReaders cp.samplerReaders (fun _ => cp.chalLoadMax) cp.chalLoad_le) cp.grantMax

/-- **The honest inputs at the checked statements**: statements that pass the check and whose
program statement is related to the input. -/
@[config_template keep_binders]
abbrev ringHonestRel {Inp : Type} (relH : Set (ir.Valuation I × Inp)) : Set (Stmt × Inp) :=
  {p | F.ok p.1 = true ∧ (F.stmtOf p.1, p.2) ∈ relH}

/-- **The largest round error at the checked statements** (`CertifiedFront.maxRoundError_le` with
`RealizedProgram.ProofSystem.fieldForkErrorWith_le`). -/
@[config_template]
theorem maxRoundError_le [Inhabited W] (C : ir.ProofSystem P I) :
    maxError (CertifiedFrontWith.forkIopSound cp src F C).error ≤
      (cp.figures.errorMax : ℝ≥0) / 2 ^ cp.figures.errorExp :=
  maxError_le_iff.2 (C.fieldForkErrorWith_le cp.ready F.stmtOf src.sound src.final
    (cp.figuresOk.fieldRoundsLe cp.fieldCard)
    (fun _ => cp.figuresOk.phaseError_le cp.fieldCard src.eps src.eps_le _))

end CertifiedFrontWith

/-! ## The configurations -/

/-- **The configuration of a certified program at a frontend** (module docstring): the IOP, its
soundness data and transcript (`CertifiedFront`), `kS`-byte salts, the headline relation and the
witness map, the honest prover on the generic per-field domain proofs at a strategy, the honest
strategy and the generated figures, with the query caps `qQ` (quantum) and `2^64` (classical). -/
@[expose] noncomputable def ofCertified [DecidableEq Stmt] [Inhabited W]
    (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)
    (F : Frontend cp src Stmt W' HonestIn) (kS qQ : ℕ) : Configuration where
  ProofSystem := ir.ProofSystem P I
  Stmt := Stmt
  Wit := ir.Valuation I → W
  rel := {p | (F.stmtOf p.1, p.2) ∈ relOf src.rel}
  iop C := CertifiedFront.forkIop cp src F C
  sound C := CertifiedFront.forkIopSound cp src F C
  T C := CertifiedFront.forkTranscript cp src F C
  kS := kS
  Wit' := W'
  rel' := F.rel'
  g := F.g
  Val := ir.Valuation I
  Strategy _ relH := ir.HonestStrategy I relH
  hrel relH := CertifiedFront.keyHonestRel cp src F relH
  sim C := C.fieldIopSimData (CertifiedSource.forkLowering cp src C) F.stmtOf
  honest C _ _ H := C.fieldIopHonest (CertifiedSource.forkLowering cp src C) F.stmtOf
    H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := HonestIn
  relH := F.relH
  strategy := CertifiedHonest.honestStrategy cp src F
  keyStmtOf := F.keyStmtOf
  inh := inferInstance
  rounds := cp.figures.rounds
  chernoff := cp.figures.chernoff
  N := cp.figures.N
  nq := cp.figures.nq
  kq := cp.figures.kq
  errorMax := cp.figures.errorMax
  errorExp := cp.figures.errorExp
  D := cp.figures.D
  qQ := qQ
  qR := 2 ^ 64
  pos := cp.figures.pos
  k := cp.figures.k

/-- **The configuration of a certified program at a frontend with a statement check**
(`ofCertified` with `CertifiedFrontWith`). -/
@[expose] noncomputable def ofCertifiedWith [DecidableEq Stmt] [Inhabited W]
    (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)
    (F : FrontendWith cp src Stmt W' HonestIn) (kS qQ : ℕ) : Configuration where
  ProofSystem := ir.ProofSystem P I
  Stmt := Stmt
  Wit := ir.Valuation I → W
  rel := {p | F.ok p.1 = true ∧ (F.stmtOf p.1, p.2) ∈ relOf src.rel}
  iop C := CertifiedFrontWith.forkIop cp src F C
  sound C := CertifiedFrontWith.forkIopSound cp src F C
  T C := CertifiedFrontWith.forkTranscript cp src F C
  kS := kS
  Wit' := W'
  rel' := F.rel'
  g := F.g
  Val := ir.Valuation I
  Strategy _ relH := ir.HonestStrategy I relH
  hrel relH := CertifiedFrontWith.ringHonestRel cp src F relH
  sim C := C.fieldIopWithSimData (CertifiedSource.forkLowering cp src C) F.stmtOf F.ok
  honest C _ _ H := C.fieldIopWithHonest (CertifiedSource.forkLowering cp src C) F.stmtOf F.ok
    H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := HonestIn
  relH := F.relH
  strategy := CertifiedHonest.honestStrategy cp src F.toFrontend
  keyStmtOf := F.keyStmtOf
  inh := inferInstance
  rounds := cp.figures.rounds
  chernoff := cp.figures.chernoff
  N := cp.figures.N
  nq := cp.figures.nq
  kq := cp.figures.kq
  errorMax := cp.figures.errorMax
  errorExp := cp.figures.errorExp
  D := cp.figures.D
  qQ := qQ
  qR := 2 ^ 64
  pos := cp.figures.pos
  k := cp.figures.k

/-! ## The facts -/

section Facts

variable [DecidableEq Stmt] [Inhabited W] (cp : CertifiedProgram P ir I) (src : SourceFront cp W S)

/-- **The facts the setting with merges is built from** (`ProgramFigures.Check.transcript_bounds`:
the statement's writes, the label and the branch names) at `kS`-byte salts. -/
theorem mergeBounds {F : Frontend cp src Stmt W' HonestIn} (hF : F.Facts) {kS : ℕ}
    (hkS : kS ≤ 2 ^ 10) (C : ir.ProofSystem P I) :
    (CertifiedFront.forkTranscript cp src F C).MergeBounds kS :=
  ⟨cp.figuresOk.transcript_bounds hF.codec_le hF.label_le (fun a => cp.branchName_le a.1), hkS⟩

/-- **The facts the setting with merges is built from at the checked statements**
(`ProgramFigures.Check.transcriptWith_bounds`). -/
theorem mergeBoundsWith {F : FrontendWith cp src Stmt W' HonestIn} (hF : F.Facts) {kS : ℕ}
    (hkS : kS ≤ 2 ^ 10) (C : ir.ProofSystem P I) :
    (CertifiedFrontWith.forkTranscript cp src F C).MergeBounds kS :=
  ⟨cp.figuresOk.transcriptWith_bounds F.ok hF.codec_le hF.label_le
    (fun a => cp.branchName_le a.1), hkS⟩

/-- **The facts of `ofCertified`** with granted points (`Configuration.GrantedFacts`): the setting's
facts (`mergeBounds`), the end-to-end theorem at the configuration's IOP
(`RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`,
`RealizedProgram.ProofSystem.FieldBranches.e2e`, at the frontend's witness map and the domains'
generic honest provers), the figures' bounds from the generated check
(`RealizedProgram.ProgramFigures.Check.figures`, `RealizedProgram.ProgramFigures.Check.loadsGranted`,
`CertifiedFront.maxRoundError_le`) and the honest strategy's (`Frontend.Facts.exec_δ`). -/
theorem ofCertified_grantedFacts {F : Frontend cp src Stmt W' HonestIn} (hF : F.Facts) {kS : ℕ}
    (hkS : kS ≤ 2 ^ 10) (qQ : ℕ) : (ofCertified cp src F kS qQ).GrantedFacts where
  hb := mergeBounds cp src hF hkS
  knowledge C _ hkq := (C.fieldBranches cp.ready).e2e_knowledge (C.fieldBranchesSound cp.ready)
    src.sound src.final F.stmtOf (CertifiedFront.forkTranscript cp src F C) kS
    (mergeBounds cp src hF hkS C) hF.mem_rel' hkq
  e2e C _ _ H _ hkq hf := (C.fieldBranches cp.ready).e2e (C.fieldBranchesSound cp.ready) src.sound
    src.final F.stmtOf (CertifiedFront.forkTranscript cp src F C) kS (mergeBounds cp src hF hkS C)
    hF.mem_rel' hkq hf (C.fieldHonestDomains cp.ready) (C.fieldForkHonestDomains cp.ready)
    H.toHonestCore H.complete
  rounds_le C := (cp.figuresOk.figures (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)).rounds_le
  loadsGranted C := cp.figuresOk.loadsGranted (B := C)
    (Lw := CertifiedSource.forkLowering cp src C) (f := F.stmtOf)
  leaves_le C := (cp.figuresOk.figures (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)).leaves_le
  queries_le C := (cp.figuresOk.figures (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)).queries_le
  kq_ge C := (cp.figuresOk.figures (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)).kq_ge
  kq_le := cp.figuresOk.kq_le
  error_le := CertifiedFront.maxRoundError_le cp src F
  digests_le C := (cp.figuresOk.figures (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)).digests_le
  pos_eq C := (cp.figuresOk.figures (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)).pos_eq
  k_eq _ := rfl
  exact := by
    change ∑ k, (CertifiedHonest.honestStrategy cp src F).δ k = 0
    rw [CertifiedHonest.honestStrategy, HonestStrategy.ofCompletionReady_δ]
    exact hF.exec_δ _
  keyStmtOf_mem := hF.keyStmtOf_mem

/-- **The facts of `ofCertified` without granted points** (`Configuration.Facts`): every round's
load passes the Chernoff test on the default stream (`RealizedProgram.ProgramFigures.Check.loads`
at `hl`). -/
theorem ofCertified_facts {F : Frontend cp src Stmt W' HonestIn} (hF : F.Facts) {kS : ℕ}
    (hkS : kS ≤ 2 ^ 10) (qQ : ℕ) (hl : cp.figures.DefaultLoadsOk cp.numbers) :
    (ofCertified cp src F kS qQ).Facts where
  toGrantedFacts := ofCertified_grantedFacts cp src hF hkS qQ
  loads C := cp.figuresOk.loads hl (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf)

/-- **The facts of `ofCertifiedWith`** with granted points (`ofCertified_grantedFacts` at the
checked statements, `RealizedProgram.ProofSystem.FieldBranches.e2eWith_knowledge`,
`RealizedProgram.ProofSystem.FieldBranches.e2eWith`). -/
theorem ofCertifiedWith_grantedFacts {F : FrontendWith cp src Stmt W' HonestIn} (hF : F.Facts)
    {kS : ℕ} (hkS : kS ≤ 2 ^ 10) (qQ : ℕ) : (ofCertifiedWith cp src F kS qQ).GrantedFacts where
  hb := mergeBoundsWith cp src hF hkS
  knowledge C _ hkq := (C.fieldBranches cp.ready).e2eWith_knowledge (C.fieldBranchesSound cp.ready)
    src.sound src.final F.stmtOf F.ok (CertifiedFrontWith.forkTranscript cp src F C) kS
    (mergeBoundsWith cp src hF hkS C) hF.mem_rel' hkq
  e2e C _ _ H _ hkq hf := (C.fieldBranches cp.ready).e2eWith (C.fieldBranchesSound cp.ready)
    src.sound src.final F.stmtOf F.ok (CertifiedFrontWith.forkTranscript cp src F C) kS
    (mergeBoundsWith cp src hF hkS C) hF.mem_rel' hkq hf (C.fieldHonestDomains cp.ready)
    (C.fieldForkHonestDomains cp.ready) H.toHonestCore H.complete
  rounds_le C := (cp.figuresOk.figuresWith (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf) F.ok).rounds_le
  loadsGranted C := cp.figuresOk.loadsGrantedWith (B := C)
    (Lw := CertifiedSource.forkLowering cp src C) (f := F.stmtOf) F.ok
  leaves_le C := (cp.figuresOk.figuresWith (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf) F.ok).leaves_le
  queries_le C := (cp.figuresOk.figuresWith (B := C)
    (Lw := CertifiedSource.forkLowering cp src C) (f := F.stmtOf) F.ok).queries_le
  kq_ge C := (cp.figuresOk.figuresWith (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf) F.ok).kq_ge
  kq_le := cp.figuresOk.kq_le
  error_le := CertifiedFrontWith.maxRoundError_le cp src F
  digests_le C := (cp.figuresOk.figuresWith (B := C)
    (Lw := CertifiedSource.forkLowering cp src C) (f := F.stmtOf) F.ok).digests_le
  pos_eq C := (cp.figuresOk.figuresWith (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf) F.ok).pos_eq
  k_eq _ := rfl
  exact := by
    change ∑ k, (CertifiedHonest.honestStrategy cp src F.toFrontend).δ k = 0
    rw [CertifiedHonest.honestStrategy, HonestStrategy.ofCompletionReady_δ]
    exact hF.exec_δ _
  keyStmtOf_mem := hF.keyStmtOf_mem

/-- **The facts of `ofCertifiedWith` without granted points** (`ofCertified_facts` at the checked
statements, `RealizedProgram.ProgramFigures.Check.loadsWith`). -/
theorem ofCertifiedWith_facts {F : FrontendWith cp src Stmt W' HonestIn} (hF : F.Facts) {kS : ℕ}
    (hkS : kS ≤ 2 ^ 10) (qQ : ℕ) (hl : cp.figures.DefaultLoadsOk cp.numbers) :
    (ofCertifiedWith cp src F kS qQ).Facts where
  toGrantedFacts := ofCertifiedWith_grantedFacts cp src hF hkS qQ
  loads C := cp.figuresOk.loadsWith hl (B := C) (Lw := CertifiedSource.forkLowering cp src C)
    (f := F.stmtOf) F.ok

end Facts

end GordieHowe.Configuration
