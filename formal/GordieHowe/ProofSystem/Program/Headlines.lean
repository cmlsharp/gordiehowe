-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Basic

@[expose] public section

/-!
# GordieHowe: the plan-level theorem

The proof system of a program (`GordieHowe.RealizedProgram.ProofSystem`) compiles its realized program to a multi-circuit IOP
(`GordieHowe.RealizedProgram.ProofSystem.protocol`), and the paper's Theorem 5.2 (`thm:backend`) gives:

* **round-by-round knowledge soundness** (`GordieHowe.RealizedProgram.ProofSystem.rbr_knowledge_soundness`): round-by-round
  knowledge soundness of the source protocol `Π_P₀` (`GordieHowe.RealizedProgram.sourceVerifier`: the source program,
  the part of role `source`, with the source challenges as its rounds) for `rel` at the extractor
  reading the statement and the phase-`0` values (`RealizedProgram.sourceExtractor proj`), with errors `ε`
  (`0` at `γ_end`), gives round-by-round knowledge soundness of the protocol for `rel` at the
  proof system's extractor (`GordieHowe.RealizedProgram.ProofSystem.extractor`), with the round errors `RealizedProgram.ProofSystem.roundError BS ε`
  (`GordieHowe/ProofSystem/Program/Errors.lean`): at a phase's challenge round, the sum over its source
  challenges of `ε` at the challenge's round of `Π_P₀`, and over all its challenges of the
  realization step's error; at a domain's rounds, the domain proof's errors. `T`: the compiler correspondence (trust
  base);
* **completeness** and **honest-verifier zero knowledge** (`GordieHowe.RealizedProgram.ProofSystem.completeness`, `GordieHowe.RealizedProgram.ProofSystem.hvzk`):
  at every completeness error `errc` of the honest prover (`GordieHowe.RealizedProgram.HonestCore.Complete`, the paper's
  `def:o-guarantees` (1)), with error `errc`. `A`: the compiler's completeness (trust base), which the domains' honest provers read
  (`GordieHowe.RealizedProgram.ProofSystem.HonestDomains`).

These are stated in one total order of the messages. The paper's series–parallel order of
`prot:backend` is `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` (every challenge with its own error),
`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk` (at the honest prover's completeness error `errc`,
`HonestCore.Complete`) in `GordieHowe/ProofSystem/Program/ForkProofSystem.lean`; the configurations' plan-level
headlines use those.

The protocol, its verifier, its honest prover and its simulator do not depend on the soundness data
(`rel`, `S`, `h`, `T`). The verifier first makes the program's member checks on the statement
(`GordieHowe.RealizedProgram.stmtOk`), as `Π_P₀`'s does, and rejects a statement that fails them; the honest
statements pass them (`HonestCore.checks`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)

/-- **The plan-level theorem, soundness** (the paper's Theorem 5.2 (2), `thm:backend`): if the
source protocol `Π_P₀` is round-by-round knowledge sound for `rel` at the extractor reading the
statement and the phase-`0` values (`RealizedProgram.sourceExtractor proj`), with state function `S` and
errors `ε` that vanish at `γ_end` (`hend`), then the proof system's protocol is round-by-round knowledge
sound for `rel` (the verifier rejects a statement outside the declared bounds, `RealizedProgram.stmtOk`) at
the proof system's extractor (`extractor proj`: `proj` at the realized assignment of the committed
cells), with the round errors `roundError BS ε`: every domain proof's errors (its soundness `BS`) at its rounds, and at the
challenge round of phase `k + 1` the sum over its challenges of `Π_P₀`'s error at the challenge
(`chalError ε`: `ε` at a source challenge's round, `0` at a realization challenge) and the
realization step's error (`RealizedProgram.realError`). `T`: the program's GKR circuits enforce their
entries (trust base). -/
@[headline]
theorem rbr_knowledge_soundness (BS : B.Sound) (T : B.CircuitsEnforce) {W : Type} [Inhabited W]
    {rel : Set (ir.Valuation I × W)} {proj : ir.Valuation I → ir.Assignment I → W}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    rbrKnowledgeSoundness rel B.verifier (B.extractor proj) (B.stateFn BS T h hend)
      (B.roundError BS ε) := by
  have hs := ((B.soundIOP T h hend).rbr_knowledge_soundness (B.soundIOPSound BS T h hend)).mapWit
    (f := fun x g => g x) fun _ _ hg => hg
  have he : B.extractor proj = (B.soundIOP T h hend).extractor.mapWit fun x g => g x := by
    rw [B.extractor_eq T h hend]
    rfl
  rw [he]
  exact hs

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The plan-level theorem, completeness** (the paper's Theorem 5.2 (1), `thm:backend`): if the
honest prover `H` has completeness error `errc` (`hc`: on the relation, the challenges meet a
completeness event with probability at most `errc`, `def:o-guarantees` (1)), then at every value
of the coins, on every honest input, the honest prover is rejected with probability at most
`errc`. `A`: the program's GKR circuits accept honest inputs (trust base), read by the domains'
honest provers `HD`. -/
@[headline]
theorem completeness (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS) (H : ir.HonestCore I relH)
    {errc : ℝ≥0} (hc : H.Complete fun _ => errc) (c : B.Coins A HD H) :
    completenessAt relH B.verifier (fun y => B.prover A HD H y c) errc :=
  B.protocol.completeness (B.honest A HD H) c (B.errorBound_honest A HD H hc)

/-- **The plan-level theorem, honest-verifier zero knowledge** (the paper's Theorem 5.2 (1),
`thm:backend`): if the honest prover `H` has completeness error `errc` (`hc`), the proof system's
simulator (`simulator`) is perfect outside the honest prover's completeness events (`exception`),
with error `errc`. `A`: the program's GKR circuits accept honest inputs (trust base), read by the
domains' honest provers `HD`. -/
@[headline]
theorem hvzk (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS) (H : ir.HonestCore I relH)
    {errc : ℝ≥0} (hc : H.Complete fun _ => errc) :
    B.iop.HVZKOffExceptions relH (B.prover A HD H) (B.simulator DS) errc
      (B.exception A HD H) :=
  B.protocol.hvzk (B.honest A HD H) (B.errorBound_honest A HD H hc)

end ProofSystem

end GordieHowe.RealizedProgram
