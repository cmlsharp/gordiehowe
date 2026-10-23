-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkProofSystem
public import GordieHowe.Language.Completeness.Check
public import GordieHowe.Language.RealizedProgram.SourcePaper
public import GordieHowe.ProofSystem.Program.Transcript.MergeGuarantees

@[expose] public section

/-!
# GordieHowe: the end-to-end theorem

The paper's `thm:e2e` for every proof system of a valid realized program (`GordieHowe.RealizedProgram.ProofSystem`) whose
domains are forked circuit proofs (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches`): spBCS at
a transcript `TD` of the proof system's multi-circuit IOP with forked domains, its statement read
through `f` (`GordieHowe.RealizedProgram.ProofSystem.IOP.comap`, or `GordieHowe.RealizedProgram.ProofSystem.IOP.comapWith` with a statement check `chk`), has the
guarantees of `GordieHowe.SPBCS.ProofSystemTranscript.Guarantees` when the source program `P₀` is

* round-by-round knowledge sound for `rel` at the extractor of `proj`, with errors `ε` that vanish
  at `γ_end` (`h`, `hend`): then the IOP is causally round-by-round knowledge sound with the round
  errors of the proof system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `thm:backend`(2)), and `errk` is their
  largest;
* complete with error `errc` at the honest prover `H` (`GordieHowe.RealizedProgram.HonestCore.Complete`, the paper's
  `def:o-guarantees` (1): the challenges meet a completeness event with probability at most
  `errc`): then the IOP's honest prover (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.honestAt`) has completeness and HVZK error
  `errc` (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.errorBound_honestAt`, `thm:backend`(1)). A strategy with per-phase errors
  `δ` is complete with `errc = ∑ k, δ k` (`HonestStrategy.complete`).

For an honest prover with coins (the coins of the source program's randomized functions,
`def:o-honest`), `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_coins` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2eWith_coins` give the guarantees of
`GordieHowe.SPBCS.ProofSystemTranscript.CoinGuarantees` at the honest prover's completeness error over the coins
(`GordieHowe.RealizedProgram.HonestCore.CoinComplete`), with the coins drawn by the honest prover.
`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_source` is the paper's statement: its hypothesis is the source program's
completeness with error `errc` (`GordieHowe.RealizedProgram.SourceComplete`, `def:o-guarantees` (1)) at an honest
prover with coins (`GordieHowe.RealizedProgram.SourceProver`), for every `errc`, and its honest prover is the one built
from the prover's execution and a completeness certificate passing the check (`GordieHowe.RealizedProgram.HonestCore.ofCompletion`
at `GordieHowe.RealizedProgram.CompletionReady` and `GordieHowe.RealizedProgram.SourceComplete.toExecutionCore`).

`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2eWith_knowledge` are part (2) alone, which needs only
the first hypothesis. The configurations' statements are instances of these theorems
(`GordieHowe.Configuration.GrantedFacts`, fields `knowledge` and `e2e`).

`T`: the program's GKR circuits enforce their entries; `A`: they accept honest inputs (trust
base).
-/

namespace GordieHowe.RealizedProgram.ProofSystem.FieldBranches

open Export PhaseLayout GordieHowe.IOP SPBCS.Configurations
open scoped NNReal

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} {B : ir.ProofSystem P I} (F : B.FieldBranches) (FS : F.Sound)
  {W : Type} [Inhabited W] {rel : Set (ir.Valuation I × W)}
  {proj : ir.Valuation I → ir.Assignment I → W} {S : KnowledgeStateFunction (ir.sourceVerifier I)}
  {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0} (T : B.CircuitsEnforce)
  (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
  (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0)
  {Stmt : Type} [DecidableEq Stmt] (f : Stmt → ir.Valuation I) {W' : Type} {rel' : Set (Stmt × W')}
  {g : Stmt → (ir.Valuation I → W) → W'} {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

section Comap

variable (TD : SPBCS.ProofSystemTranscript ((F.soundIOP T h hend).comap f)) (kS : ℕ)
  (hb : TD.MergeBounds kS)

/-- **The end-to-end theorem, knowledge soundness** (the paper's `thm:e2e`(2)): if the source
program is round-by-round knowledge sound (`h`, `hend`), then the compiled argument of the proof system's
multi-circuit IOP with forked domains, its statement read through `f`, is knowledge sound and sound
in the QROM and the ROM at the verifier with merges of query budget `kq` (`hkq`), for every relation
`rel'` into which the witness map `g` sends the IOP's relation (`hg`), with `errk` the largest round
error of the proof system (`thm:backend`(2)). `T`: trust base. -/
@[headline]
theorem e2e_knowledge (hg : ∀ x w, (f x, w) ∈ relOf rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : TD.QueryBudget kS hb kq) :
    TD.KnowledgeGuarantees kS hb ((F.soundIOPSound FS T h hend).comap f) rel' g hkq :=
  SPBCS.ProofSystemTranscript.knowledgeGuarantees _ hg hkq

/-- **The end-to-end theorem** (the paper's `thm:e2e`): if the source program is round-by-round
knowledge sound (`h`, `hend`) and the honest prover `H` has completeness error `errc` (`hc`, the
paper's `def:o-guarantees` (1)), then the compiled argument of the proof system's multi-circuit IOP with
forked domains, its statement read through `f`, has parts (1)–(5) of
`SPBCS.ProofSystemTranscript.Guarantees`, at the verifier with merges of query budget `kq` (`hkq`), for
every relation `rel'` into which the witness map `g` sends the IOP's relation (`hg`): with `errk`
the largest round error of the proof system (`thm:backend`(2)), and with `errc` as the completeness and
HVZK error (`thm:backend`(1)), at the honest prover `FieldBranches.honestAt` of the domains' honest
provers `HD` and `FH`. `T`, `A`: trust base. -/
@[headline]
theorem e2e (hg : ∀ x w, (f x, w) ∈ relOf rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : TD.QueryBudget kS hb kq) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD A d).In (HD A d).dom (FSm d)) (H : ir.HonestCore I relH)
    {errc : ℝ≥0} (hc : H.Complete fun _ => errc) :
    TD.Guarantees kS hb ((F.soundIOPSound FS T h hend).comap f) rel' g hkq hf
      ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comap f) errc :=
  SPBCS.ProofSystemTranscript.guarantees ((F.soundIOPSound FS T h hend).comap f) hg hkq hf
    ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comap f)
    ((F.errorBound_honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H hc).comap f)

/-- **The end-to-end theorem for an honest prover with coins** (the paper's `thm:e2e`, with the
honest prover's coins drawn): if the source program is round-by-round knowledge sound (`h`,
`hend`) and the honest prover `H`, for honest inputs `J` read with uniform coins `ω` as its inputs
`inp y ω`, has completeness error `errc` over the coins (`hc`, `def:o-guarantees` (1)), then the
compiled argument of the proof system's multi-circuit IOP with forked domains, its statement read
through `f`, has parts (1)–(5) of `SPBCS.ProofSystemTranscript.CoinGuarantees` (as `e2e`, with completeness,
everlasting zero knowledge and witness indistinguishability at the honest prover with coins), with `errc` as
the completeness and HVZK error. `T`, `A`: trust base. -/
@[headline]
theorem e2e_coins (hg : ∀ x w, (f x, w) ∈ relOf rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : TD.QueryBudget kS hb kq) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD A d).In (HD A d).dom (FSm d)) (H : ir.HonestCore I relH)
    {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (ir.Valuation I × J)} {inp : J → Ω → Inp}
    {errc : ℝ≥0} (hc : H.CoinComplete relJ inp fun _ => errc) :
    TD.CoinGuarantees kS hb ((F.soundIOPSound FS T h hend).comap f) rel' g hkq hf
      ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comap f) {p | (f p.1, p.2) ∈ relJ} inp errc :=
  SPBCS.ProofSystemTranscript.coinGuarantees ((F.soundIOPSound FS T h hend).comap f) hg hkq hf
    ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comap f)
    ((F.coinErrorBound_honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H hc).comap f)

/-- **The end-to-end theorem from the source program's guarantees** (the paper's `thm:e2e`, with
its hypotheses as in `def:o-guarantees`): if the source program is round-by-round knowledge sound
(`h`, `hend`) and complete for `relH` with error `errc` at the honest prover `Hs` with coins `Ω`
(`hs`, `def:o-guarantees` (1): the execution with uniform coins and challenges fails to accept
with probability at most `errc`), then the compiled argument has parts (1)–(5) of
`SPBCS.ProofSystemTranscript.CoinGuarantees` with `errc` as the completeness and HVZK error, at the honest
prover of the prover's execution (`HonestCore.ofCompletion` at `SourceComplete.toExecutionCore`: the
realizations' values added by the completeness certificate `R` (generators `G`, derivations `D`)
of a program passing the completeness check, `CompletionReady`), on the honest inputs `relH` with
the prover's coins drawn uniformly. `T`, `A`: trust base. -/
@[headline]
theorem e2e_source (hg : ∀ x w, (f x, w) ∈ relOf rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : TD.QueryBudget kS hb kq) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD A d).In (HD A d).dom (FSm d)) {primeNodes : ℕ → List String}
    {G : Gens} {D : CDerivations} (R : ir.CompletionReady I primeNodes G D) {Ω : Type} [Fintype Ω] [Nonempty Ω]
    {Hs : ir.SourceProver I Inp Ω} {errc : ℝ≥0} (hs : ir.SourceComplete I relH Hs errc) :
    TD.CoinGuarantees kS hb ((F.soundIOPSound FS T h hend).comap f) rel' g hkq hf
      ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH
        (HonestCore.ofCompletion R.model R.macsRealizable R.facts hs.toExecutionCore)).comap f)
      {p | (f p.1, p.2) ∈ relH} WithCoins.mk errc :=
  F.e2e_coins FS T h hend f TD kS hb hg hkq hf A HD FH _
    (HonestCore.ofCompletion_coinComplete R.model R.macsRealizable R.facts _ hs.coinComplete)

end Comap

section ComapWith

variable (chk : Stmt → Bool) (TD : SPBCS.ProofSystemTranscript ((F.soundIOP T h hend).comapWith f chk))
  (kS : ℕ) (hb : TD.MergeBounds kS)

/-- **The end-to-end theorem, knowledge soundness, with a statement check** (`e2e_knowledge` with
the statement read through `f` and checked by `chk`, `IOP.comapWith`). `T`: trust base. -/
@[headline]
theorem e2eWith_knowledge
    (hg : ∀ x w, chk x = true ∧ (f x, w) ∈ relOf rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : TD.QueryBudget kS hb kq) :
    TD.KnowledgeGuarantees kS hb ((F.soundIOPSound FS T h hend).comapWith f chk) rel' g hkq :=
  SPBCS.ProofSystemTranscript.knowledgeGuarantees _ hg hkq

/-- **The end-to-end theorem with a statement check** (`e2e` with the statement read through `f`
and checked by `chk`, `IOP.comapWith`). `T`, `A`: trust base. -/
@[headline]
theorem e2eWith (hg : ∀ x w, chk x = true ∧ (f x, w) ∈ relOf rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : TD.QueryBudget kS hb kq) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD A d).In (HD A d).dom (FSm d)) (H : ir.HonestCore I relH)
    {errc : ℝ≥0} (hc : H.Complete fun _ => errc) :
    TD.Guarantees kS hb ((F.soundIOPSound FS T h hend).comapWith f chk) rel' g hkq hf
      ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comapWith f chk) errc :=
  SPBCS.ProofSystemTranscript.guarantees ((F.soundIOPSound FS T h hend).comapWith f chk) hg hkq hf
    ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comapWith f chk)
    ((F.errorBound_honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H hc).comapWith f chk)

/-- **The end-to-end theorem for an honest prover with coins, with a statement check** (`e2e_coins`
with the statement read through `f` and checked by `chk`, `IOP.comapWith`). `T`, `A`:
trust base. -/
@[headline]
theorem e2eWith_coins (hg : ∀ x w, chk x = true ∧ (f x, w) ∈ relOf rel → (x, g x w) ∈ rel')
    {kq : ℕ} (hkq : TD.QueryBudget kS hb kq) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    {FSm : F.ForkSims} (FH : ∀ d, F.ForkDomainHonest d (HD A d).In (HD A d).dom (FSm d)) (H : ir.HonestCore I relH)
    {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (ir.Valuation I × J)} {inp : J → Ω → Inp}
    {errc : ℝ≥0} (hc : H.CoinComplete relJ inp fun _ => errc) :
    TD.CoinGuarantees kS hb ((F.soundIOPSound FS T h hend).comapWith f chk) rel' g hkq hf
      ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comapWith f chk)
      {p | chk p.1 = true ∧ (f p.1, p.2) ∈ relJ} inp errc :=
  SPBCS.ProofSystemTranscript.coinGuarantees ((F.soundIOPSound FS T h hend).comapWith f chk) hg hkq hf
    ((F.honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H).comapWith f chk)
    ((F.coinErrorBound_honestAt (B.lowering T ⟨_, h, hend⟩) A HD FH H hc).comapWith f chk)

end ComapWith

end GordieHowe.RealizedProgram.ProofSystem.FieldBranches
