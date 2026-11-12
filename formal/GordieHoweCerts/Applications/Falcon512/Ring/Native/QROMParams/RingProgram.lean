-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Ring.Native.QROMParams.RingScheme

@[expose] public section

/-!
# The program form of the Falcon-512 rings of `Falcon512.Ring.Native.QROMParams`

The hypotheses of the program form of the ring signature
(`GordieHowe/Applications/Ring/Program.lean`, `GordieHowe/Applications/Ring/ProgramBase.lean`) at
the configuration's realized program:

* `ringProgramHypotheses G C`: the plan-level hypotheses (`Ring.ProgramHypotheses`) at the
  forked domain proofs of the configuration's proof system, the ring relation `Ring.rel`, its
  projection `Ring.proj`, the honest relation `Ring.relH` and completeness error `0`. They are the
  configuration's facts: the forked domains' soundness, the source protocol's round-by-round
  knowledge soundness (`source_rbr_knowledge_soundness`), the domains' honest provers and
  simulators, and the honest strategy `ringHonestStrategy G` with summed errors `0`. `enforce`
  and `accept` are the proof system's facts, proved from the certificate.
* `ringBaseVerifies G bmsg`: the program verifies base signatures of `falconBaseSigner G bmsg` for
  the ring relation on rings of `64` keys (`Ring.BaseVerifiesRing`), at the program statement
  `stmtOf (toRStmt x)` checked by `ringOk`, with the soundness and honest inputs of
  `Falcon512.Ring.ringVerifies`.
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram RealizedProgram.ProofSystem GordieHowe.Ring GordieHowe.RingSignature
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Generated.Falcon512.Ring.Native.QROMParams (interp ready ProofSystems)
open _root_.GordieHowe.Falcon512.Ring.Native (CoreWit)
open _root_.GordieHowe.Falcon512.Ring (toRStmt toRWit ofRWit adm64)
open scoped NNReal ENNReal

variable {msgLen : ℕ} (G : Signer msgLen) (C : ProofSystems)

variable [Fintype G.KeyCoins] [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins]
  [DecidableEq G.SignCoins] [Nonempty G.SignCoins]

/-- **The honest strategy's prover is complete with error `0`** (`HonestStrategy.complete`,
`ringHonestStrategy_delta`). -/
theorem ringHonestStrategy_complete : (ringHonestStrategy G).toHonestCore.Complete fun _ => 0 := by
  have h := (ringHonestStrategy G).complete
  rwa [ringHonestStrategy_delta] at h

omit [Fintype G.KeyCoins] [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins]
  [DecidableEq G.SignCoins] [Nonempty G.SignCoins] in
/-- **The plan-level hypotheses of the program form at `Falcon512.Ring.Native.QROMParams`**
(`Ring.ProgramHypotheses`, the paper's Theorem 5.2): the forked domain proofs of the
configuration's proof system (`fieldBranches`, sound by `fieldBranchesSound`), the source
protocol's round-by-round knowledge soundness for `Ring.rel` at `Ring.proj`
(`source_rbr_knowledge_soundness`, its errors vanishing at `γ_end` by `sourceError_final`), the
domains' and forked domains' simulators and honest provers (`fieldSims`, `fieldHonestDomains`,
`fieldForkSims`, `fieldForkHonestDomains`), and the honest strategy `ringHonestStrategy G` with
completeness error `0` (`ringHonestStrategy_complete`). -/
noncomputable def ringProgramHypotheses :
    ProgramHypotheses (C.fieldBranches ready) Ring.rel Ring.proj
      (Ring.relH G program interp) 0 where
  forkSound := C.fieldBranchesSound ready
  stateFn := _
  sourceError := _
  source_rbr := source_rbr_knowledge_soundness
  sourceError_final := sourceError_final
  domainSims := C.fieldSims ready
  honestDomains := C.fieldHonestDomains ready
  forkSims := C.fieldForkSims ready
  forkHonest := C.fieldForkHonestDomains ready
  honest := (ringHonestStrategy G).toHonestCore
  complete := ringHonestStrategy_complete G

variable {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  (bmsg : KeyRing PublicKey 64 → RMsg → (Fin msgLen → UInt8)) {Xo Yo : Type}

/-- **Membership in `ringRel64 G` is decided** (`Ring.ringRelDecidable` at the rings of `64` keys and
the bound message `bindMsg`). -/
@[instance_reducible]
def ringRel64Decidable : DecidablePred (· ∈ ringRel64 G) := by
  unfold ringRel64
  exact GordieHowe.Ring.ringRelDecidable _ _

/-- **The configuration's program verifies the base signatures of `falconBaseSigner G bmsg`** for
the ring relation on rings of `64` keys (`Ring.BaseVerifiesRing`): the program statement of the
read ring statement `toRStmt x` (`Ring.stmtOf`), checked by `ringOk`; a witness of `Ring.rel` gives
the ring witness of the signature encoded from the extracted `s2` with the statement's salt
(`CoreWit.withSalt`, `ringRel_of_rel`); the honest input of a pair of the ring relation is the
honest pair `(toRStmt x, toRWit w)` (`RingIn`), none off the ring relation. -/
def ringBaseVerifies :
    BaseVerifiesRing program interp Ring.rel (Ring.relH G program interp)
      (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg) adm64 where
  stmt x := Ring.stmtOf (toRStmt G bmsg x)
  check x := Ring.ringOk (toRStmt G bmsg x)
  wit x w := ofRWit G bmsg (w.withSalt (G := G) x.pub)
  sound H x _ hx hw := (Falcon512.Ring.mem_ringRel64_iff H x _).1 (Ring.ringRel_of_rel hx hw)
  input x w :=
    haveI := ringRel64Decidable G
    if h : (toRStmt G bmsg x, toRWit G bmsg w) ∈ ringRel64 G then some ⟨_, _, h⟩ else none
  check_eq_true H x w h :=
    Ring.RingIn.ringOk_x (G := G)
      ⟨toRStmt G bmsg x, toRWit G bmsg w, (Falcon512.Ring.mem_ringRel64_iff H x w).2 h⟩
  input_mem H x w h := by
    have h' := (Falcon512.Ring.mem_ringRel64_iff H x w).2 h
    exact ⟨⟨toRStmt G bmsg x, toRWit G bmsg w, h'⟩, by simp [h'], rfl⟩

end GordieHowe.Falcon512.Ring.Native.QROMParams
