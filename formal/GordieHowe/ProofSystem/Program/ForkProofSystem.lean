-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the proof system of a program with forked domains

The proof system's domains as forked circuit proofs (`GordieHowe.FieldProof.BranchShape`, the proof system's transcript schedule,
`lib/gordiehowe/transcript_fork.h`): every domain proof's public input, witness and relation, with a
forked circuit proof of that relation, its soundness and the reading of its oracle message
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches`). With the proof system's application phase at a lowering `Lw` (`GordieHowe.RealizedProgram.ProofSystem.iopOf`),
they are a multi-circuit IOP with forked domains (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.iopOf`): at the soundness theorem's
lowering (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.soundIOP`, its soundness `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`) and at the honest prover's
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.honestAt`: the proof system's phased honest prover, every forked domain's honest prover,
accepted, with a perfect simulator).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp}
  (proof : DomainProofs ir I) (fork : ∀ d, FieldProof.BranchShape (proof d).Pub (proof d).Wit)
  (oracle : ∀ d, (fork d).Oracle)

/-- **The multi-circuit IOP with forked domains of the domain proofs at the lowering `Lw`**: the
forked circuit proofs `fork` of the domain proofs' relations, the readings `oracle` of their
oracle messages, and the domain proofs' application phase at `Lw` (as `RealizedProgram.iopOfProofs`).
`hm`: the program has a domain. -/
def forkIopOfProofs (hm : ir.domains.length ≠ 0) {W : Type} {rel : Set (ir.Valuation I × W)}
    (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
      (GordieHowe.Domain.lowered (ir.domainsOf I))) :
    ProofSystem.IOP (ir.Valuation I) W rel where
  m := ir.domains.length
  neZero := ⟨hm⟩
  Pub d := (proof d).Pub
  Wit d := (proof d).Wit
  holds d := (proof d).holds
  circuit := fork
  oracle := oracle
  app := ((Lw.check (ir.stmtOk I)).toPhased (enforcementOf proof)).toAppPhase

end

section

open Classical in
/-- **The summed errors of an honest strategy are a completeness error** (`HonestCore.Complete`;
the union bound over the phases, `Phased.Honest.BadBound.errorBound`). -/
theorem HonestStrategy.complete {ir : RealizedProgram} {I : Interp} {Inp : Type}
    {relH : Set (ir.Valuation I × Inp)} (H : ir.HonestStrategy I relH) :
    H.Complete fun _ => ∑ k, H.δ k := fun x y hy =>
  (QROM.probUniform_exists_le fun k c => H.bad k x y c).trans
    ((Finset.sum_le_sum fun k _ => probUniform_pi_le_of_update k _ fun f =>
      H.badBound k x y hy f).trans_eq (ENNReal.ofNNReal_finsetSum _ _).symm)

end

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)

/-- **The forked domain proofs of a proof system** (module docstring): for every domain, a forked
circuit proof of the domain proof's relation and the reading of its oracle message. Their soundness
is `FieldBranches.Sound`, apart from this data. -/
structure FieldBranches where
  /-- Every domain's forked circuit proof. -/
  fork : ∀ d, FieldProof.BranchShape (B.proof d).Pub (B.proof d).Wit
  /-- How every forked circuit proof's verdict reads its oracle message. -/
  oracle : ∀ d, (fork d).Oracle

variable {B} (F : B.FieldBranches)

/-- **The soundness of the forked domain proofs**: every forked circuit proof's soundness for its
domain proof's relation. -/
abbrev FieldBranches.Sound : Type := ∀ d, (F.fork d).Sound (B.proof d).holds

/-- **The multi-circuit IOP with forked domains at the lowering `Lw`**: the forked domain proofs,
and the proof system's application phase at `Lw` (as `ProofSystem.iopOf`; `RealizedProgram.forkIopOfProofs` at the
proof system's proofs). -/
abbrev FieldBranches.iopOf {W : Type} {rel : Set (ir.Valuation I × W)}
    (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
      (GordieHowe.Domain.lowered B.domains)) :
    IOP (ir.Valuation I) W rel :=
  forkIopOfProofs B.proof F.fork F.oracle B.domains_ne_zero Lw

variable {W : Type} {rel : Set (ir.Valuation I × W)} {proj : ir.Valuation I → ir.Assignment I → W}
  {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}

/-- **The multi-circuit IOP with forked domains of the soundness theorem**: `iopOf` at the
soundness theorem's lowering (`ProofSystem.lowering`). Replaced by `iopOf` at
`ProofSystem.soundLowering`; kept for the configuration template and Ring. -/
abbrev FieldBranches.soundIOP
    (h : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    IOP (ir.Valuation I) (ir.Valuation I → W) (relOf rel) :=
  F.iopOf (B.lowering ⟨_, h, hend⟩)

/-- **The soundness of the forked soundness IOP**: the forked domain proofs' soundness `FS` and the
phases' errors at their challenge rounds (`eventBound_lowering`). Replaced by
`FieldBranches.soundAt`; kept for the configuration template and Ring. -/
noncomputable def FieldBranches.soundIOPSound (FS : F.Sound)
    (h : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    (F.soundIOP h hend).Sound where
  circuit := FS
  εapp := (ir.layout I).error (ir.phaseError I ε)
  eventBound := Phased.eventBound_toAppPhase _
    (Lowering.eventBound_toPhased (Lowering.eventBound_check (B.eventBound_lowering h hend)))

/-- **The protocol with forked domains**: the multi-circuit IOP with forked domains at the
protocol's lowering (`ProofSystem.baseLowering`, no event and no soundness data). Its rounds are run as
the series–parallel composite (`IOP.term`). -/
abbrev FieldBranches.protocol : IOP (ir.Valuation I) (ir.Valuation I → Unit) Set.univ :=
  F.iopOf (B.baseLowering fun _ _ => ())

/-- **The soundness of the forked IOP at the soundness lowering** (`ProofSystem.soundLowering`):
the forked domain proofs' soundness `FS` and the phases' errors at their challenge rounds
(`eventBound_soundLowering`). -/
noncomputable def FieldBranches.soundAt (FS : F.Sound) (hS : ir.SourceSound I rel proj S ε) :
    (F.iopOf (B.soundLowering hS)).Sound where
  circuit := FS
  εapp := (ir.layout I).error (ir.phaseError I ε)
  eventBound := Phased.eventBound_toAppPhase _
    (Lowering.eventBound_toPhased (Lowering.eventBound_check (B.eventBound_soundLowering hS)))

/-- **The extractor of the forked IOP reads the lowering only through its projection.** -/
theorem FieldBranches.extractor_iopOf_congr [Inhabited W] {rel₁ rel₂ : Set (ir.Valuation I × W)}
    (Lw₁ : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel₁))
      (GordieHowe.Domain.lowered B.domains))
    (Lw₂ : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel₂))
      (GordieHowe.Domain.lowered B.domains))
    (h : Lw₁.proj = Lw₂.proj) : (F.iopOf Lw₁).extractor = (F.iopOf Lw₂).extractor := by
  obtain ⟨p₁, e₁, c₁, s₁⟩ := Lw₁
  obtain ⟨p₂, e₂, c₂, s₂⟩ := Lw₂
  obtain rfl : p₁ = p₂ := h
  rfl

/-! ## The soundness of the proof system in its series–parallel order -/

/-- **The verifier of the protocol with forked domains**: every domain's verdict and the statement
check (`IOP.verifier`), at the protocol (`FieldBranches.protocol`). It reads no lowering
(`FieldBranches.verifier_iopOf`). -/
abbrev FieldBranches.verifier :
    ir.Valuation I → FullTr F.protocol.P F.protocol.term → Bool :=
  F.protocol.verifier

/-- **The forked IOP's verifier at every lowering is the protocol's.** -/
theorem FieldBranches.verifier_iopOf {W : Type} {rel : Set (ir.Valuation I × W)}
    (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
      (GordieHowe.Domain.lowered B.domains)) :
    (F.iopOf Lw).verifier = F.verifier :=
  rfl

/-- **The causal extractor of the proof system in its series–parallel order** at the projection
`proj`: the extractor of the forked IOP at the protocol's lowering at `proj`
(`ProofSystem.baseLowering`; `IOP.extractor`: the prefix's extractor at every challenge, read on
the prefix part of the causal past), applied to the statement (`CausalExtractor.mapWit`).

Running time: one call of `IOP.extractor` (its paragraph: every domain's `ext` on the
commit phase and the application phase's `extract`, which decodes the committed assignment from
the cells, one copy per cell, and applies `proj`) and its application to the statement;
polynomial when `proj` is. This running time is argued here, not proved in Lean. -/
def FieldBranches.causalExtractor [Inhabited W] (proj : ir.Valuation I → ir.Assignment I → W) :
    CausalExtractor F.protocol.P F.protocol.term (ir.Valuation I) W :=
  (F.iopOf (B.baseLowering proj)).extractor.mapWit fun x g => g x

/-- **The extractor at the soundness lowering is the causal extractor at `proj`.** -/
theorem FieldBranches.extractor_soundAt [Inhabited W] (hS : ir.SourceSound I rel proj S ε) :
    (F.iopOf (B.soundLowering hS)).extractor.mapWit (fun x g => g x) = F.causalExtractor proj := by
  rw [F.extractor_iopOf_congr _ _ (B.lowering_proj hS.sourceRbr)]
  rfl

/-- **The round errors of the proof system in its series–parallel order** at the forked domain
proofs' soundness `FS` and `Π_P₀`'s round errors `ε` (`IOP.roundError`): every domain's errors at
its commit rounds, branches and join part, and at the challenge round of phase `k + 1` the sum over
its challenges of `Π_P₀`'s error and the realization step's error (`RealizedProgram.phaseError`). -/
noncomputable def FieldBranches.roundError (FS : F.Sound) (ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0) :
    ChIdx F.protocol.P F.protocol.term → ℝ≥0 :=
  F.protocol.roundError FS ((ir.layout I).error (ir.phaseError I ε))

/-- **The state function of the proof system in its series–parallel order** at the forked domain
proofs' soundness `FS`, for a source program sound with state function `S` (`hS`): the forked IOP's
at the soundness lowering (`IOP.Sound.stateFn`), which reads `S` through the lowering's events. Not
required to be efficient. -/
noncomputable def FieldBranches.stateFn [Inhabited W] (FS : F.Sound) (hS : ir.SourceSound I rel proj S ε) :
    CausalStateFn F.protocol.P F.protocol.term (ir.Valuation I) :=
  (F.soundAt FS hS).stateFn

/-- **The plan-level theorem, soundness, in the series–parallel order of `prot:backend`** (the
paper's `thm:backend` (2) and `def:rbr`). With the proof system's domains
given as forked circuit proofs `F` with soundness `FS`, the protocol runs as the series–parallel composite
(`IOP.term`): the commitment round, every domain's commit rounds and the program's phases,
then the domains side by side, each its branches side by side followed by its join part. If the
source protocol `Π_P₀` is round-by-round knowledge sound for `rel` at the extractor reading the
statement and the phase-`0` values (`RealizedProgram.sourceExtractor proj`), with state function `S` and
errors `ε` that vanish at `γ_end` (`hS`, `SourceSound`), then the protocol's verifier
(`FieldBranches.verifier`) is causally round-by-round knowledge sound for `rel` at the causal
extractor at `proj` (`FieldBranches.causalExtractor`), with every challenge's own error
(`FieldBranches.roundError`): the forked domain proofs' errors at their commit rounds, branches and
join parts, and at the challenge of phase `k + 1` the sum over its challenges of `Π_P₀`'s error and
the realization step's error (`RealizedProgram.phaseError`). Only the state function
(`FieldBranches.stateFn`) is built from `hS`; it reads `S`. The proof system's `enforce` enters
through the lowering. -/
@[headline]
theorem FieldBranches.causal_rbr_knowledge_soundness [Inhabited W] (FS : F.Sound)
    (hS : ir.SourceSound I rel proj S ε) :
    CausalRBRKnowledgeSound rel F.verifier (F.causalExtractor proj) (F.stateFn FS hS)
      (F.roundError FS ε) := by
  rw [← F.extractor_soundAt hS]
  exact (F.soundAt FS hS).causal_rbr.mapWit (rel' := rel) (g := fun x g => g x) fun _ _ hg => hg

/-! ## The honest prover -/

/-- **The simulators of the forked domain proofs**: every forked domain's simulator. -/
abbrev FieldBranches.ForkSims : Type 1 := ∀ d, (F.fork d).Simulator (F.oracle d)

/-- **The honest prover of a forked domain proof** on the domain's honest inputs `In` in the domain
`dom`, simulated by `S`: the honest forked prover, accepted on `dom`, which `S` simulates
perfectly. -/
structure FieldBranches.ForkDomainHonest (d : Fin ir.domains.length) (In : Type) (dom : (B.proof d).Pub → In → Prop)
    (S : (F.fork d).Simulator (F.oracle d)) where
  /-- The honest forked prover. -/
  circuit : (F.fork d).Honest In
  /-- It is accepted on the domain. -/
  accepts : circuit.Accepts dom
  /-- The simulator is perfect on the domain. -/
  perfect : S.Perfect circuit dom

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
  (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
    (GordieHowe.Domain.lowered B.domains))

/-- **The simulator data of the multi-circuit IOP with forked domains at the lowering `Lw`**: the
proof system's phased application phase's simulator (`Phased.appSim`) and the forked domains'
simulators `FSm`. -/
def FieldBranches.simDataAt (FSm : F.ForkSims) : (F.iopOf Lw).SimData where
  app := ((Lw.check (ir.stmtOk I)).toPhased B.enforcement).appSim
  sim := FSm

/-- **The honest prover of the multi-circuit IOP with forked domains at the lowering `Lw`**: the
proof system's phased honest prover (`ProofSystem.phasedHonestAt`, on the domains' honest inputs and domains
of `HD`) as the application phase's, and every forked domain's honest prover (`FH`); simulated by
`simDataAt Lw FSm`. -/
def FieldBranches.honestAt {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH) : (F.iopOf Lw).Honest (F.simDataAt Lw FSm) Inp relH where
  In d := (HD d).In
  dom d := (HD d).dom
  app := (B.phasedHonestAt Lw HD H).toAppHonest
  circuit d := (FH d).circuit
  accepts d := (FH d).accepts
  perfect d := (FH d).perfect

/-- The completeness events of the honest prover at `Lw` have together the honest prover's
completeness error (`HonestCore.Complete`). -/
theorem FieldBranches.errorBound_honestAt {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH)
    {errc : ir.Valuation I → ℝ≥0} (hc : H.Complete errc) : (F.honestAt Lw HD FH H).app.ErrorBound errc :=
  Phased.Honest.errorBound_toAppHonest hc

/-- The completeness events of the honest prover at `Lw` have together, over the prover's coins, the
honest prover's completeness error over the coins (`HonestCore.CoinComplete`). -/
theorem FieldBranches.coinErrorBound_honestAt {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH)
    {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (ir.Valuation I × J)} {inp : J → Ω → Inp}
    {errc : ir.Valuation I → ℝ≥0} (hc : H.CoinComplete relJ inp errc) :
    (F.honestAt Lw HD FH H).app.CoinErrorBound relJ inp errc :=
  Phased.Honest.coinErrorBound_toAppHonest hc

/-! ## Completeness and zero knowledge in the series–parallel order -/

/-- **The simulator data of the protocol with forked domains** (`FieldBranches.simDataAt` at the
protocol's lowering). -/
abbrev FieldBranches.simData (FSm : F.ForkSims) : F.protocol.SimData :=
  F.simDataAt (B.baseLowering fun _ _ => ()) FSm

/-- **The honest prover of the protocol with forked domains** at the honest prover `H`
(`FieldBranches.honestAt` at the protocol's lowering). -/
abbrev FieldBranches.honest {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH) :
    F.protocol.Honest (F.simData FSm) Inp relH :=
  F.honestAt (B.baseLowering fun _ _ => ()) HD FH H

/-- **The honest prover at every lowering is the protocol's**: at the coins `c`, the honest causal
prover of `honestAt Lw` is that of `honest`, at the same pads and domain coins. -/
theorem FieldBranches.honest_honestAt {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH) (y : Inp) (c : (F.honestAt Lw HD FH H).Coins) :
    IOP.honest (F.honestAt Lw HD FH H) y c = IOP.honest (F.honest HD FH H) y ⟨c.pads, c.circuits⟩ :=
  rfl

/-- **The plan-level theorem, completeness, in the series–parallel order of `prot:backend`** (the
paper's `thm:backend` (1)): if the honest prover `H` has completeness error `errc`
(`hc`: on the relation, the challenges meet a completeness event with probability at most `errc`,
`def:o-guarantees` (1)), then at every value `c` of the coins, on every honest input, the honest
prover of the series–parallel composite (`IOP.honest`) is rejected with probability at most
`errc`. The domains' honest provers are `HD` and `FH`; `fieldHonestDomains` and
`fieldForkHonestDomains` build them from the proof system's `accept`. -/
@[headline]
theorem FieldBranches.completeness {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH)
    {errc : ir.Valuation I → ℝ≥0} (hc : H.Complete errc) (c : (F.honest HD FH H).Coins) :
    CausalCompleteStmt relH F.protocol.verifier
      (fun y => IOP.honest (F.honest HD FH H) y c) errc := fun x y hy =>
  IOP.completeness_of_errorBound _ (F.errorBound_honestAt _ HD FH H hc) c x y hy

/-- **The plan-level theorem, honest-verifier zero knowledge, in the series–parallel order of
`prot:backend`** (the paper's `thm:backend` (1)): if the honest prover `H` has
completeness error `errc` (`hc`), the simulator of the series–parallel composite
(`IOP.simulator`) is honest-verifier zero knowledge for the honest prover with error
`errc` (`CausalHVZKStmt`).  -/
@[headline]
theorem FieldBranches.hvzk {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH)
    {errc : ir.Valuation I → ℝ≥0} (hc : H.Complete errc) :
    CausalHVZKStmt F.protocol.toCausalIOP.views relH (IOP.honest (F.honest HD FH H)) id
      (IOP.simulator (F.simData FSm)) errc :=
  IOP.hvzk_of_errorBound _ (F.errorBound_honestAt _ HD FH H hc)

section Coins

variable {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (ir.Valuation I × J)}
  {inp : J → Ω → Inp}

/-- **The plan-level theorem, completeness, for an honest prover with coins, in the series–parallel
order of `prot:backend`** (the paper's `thm:backend` (1), at `def:iop-complete`: over
the challenges and the prover's coins): for honest inputs `J` read with uniform coins `ω` as the
honest prover's inputs `inp y ω` (the coins of the source program's randomized functions,
`def:o-honest`), if the honest prover `H` has completeness error `errc` over the coins (`hc`,
`def:o-guarantees` (1)), then at every value `c` of the honest prover's coins, on `relJ`, the honest
prover of the series–parallel composite at `inp y ω` is rejected with probability at most `errc` over
uniform coins `ω` and challenges. The domains' honest provers are `HD` and `FH`;
`fieldHonestDomains` and `fieldForkHonestDomains` build them from the proof system's `accept`. -/
@[headline]
theorem FieldBranches.completeness_coins {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH)
    {errc : ir.Valuation I → ℝ≥0} (hc : H.CoinComplete relJ inp errc) (c : (F.honest HD FH H).Coins) :
    CausalCompleteCoins relJ F.protocol.verifier
      (fun y ω => IOP.honest (F.honest HD FH H) (inp y ω) c) errc :=
  IOP.completeness_coins _ (F.coinErrorBound_honestAt _ HD FH H hc) c

/-- **The plan-level theorem, honest-verifier zero knowledge, for an honest prover with coins, in
the series–parallel order of `prot:backend`** (the paper's `thm:backend` (1)): for
honest inputs `J` read with uniform coins `ω` as the honest prover's inputs `inp y ω`, if the honest
prover `H` has completeness error `errc` over the coins (`hc`), the simulator of the series–parallel
composite (`IOP.simulator`) is honest-verifier zero knowledge for the honest prover with
coins (`IOP.coinHonest`: the coins `ω` and the honest prover's coins) with error `errc`. -/
@[headline]
theorem FieldBranches.hvzk_coins {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD d).In (HD d).dom (FSm d))
    (H : ir.HonestCore I relH)
    {errc : ir.Valuation I → ℝ≥0} (hc : H.CoinComplete relJ inp errc) :
    CausalHVZKStmt F.protocol.toCausalIOP.views relJ (IOP.coinHonest (F.honest HD FH H) inp)
      id (IOP.simulator (F.simData FSm)) errc :=
  IOP.hvzk_coins _ (F.coinErrorBound_honestAt _ HD FH H hc)

end Coins

end ProofSystem

end GordieHowe.RealizedProgram
