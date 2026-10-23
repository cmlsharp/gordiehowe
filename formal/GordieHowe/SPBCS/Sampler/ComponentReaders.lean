-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.Language.Realizations.MAC

@[expose] public section

/-!
# The challenge readers of the protocol components

The C++ draws of every challenge round of the components the circuits are built from, given the
reader `r` of one element of the circuit's field (`CReader.prime`, `binary`, `ext`). The challenge
points are those of `lib/random/transcript.h` (a point is the run of draws between two writes);
the draws are on the prover's transcript `tsp` and mirrored by the verifier.

- GKR (`GKR.Schedule.spec`, read by `gkrSpec`; `lib/sumcheck/transcript_sumcheck.h`, `lib/zk/zk_common.h`):
  `initial`, the `d` elements of the initial point for the output dimension `d` (the C++
  `begin_circuit`, lines 49–52, draws `40 + 40` elements `Q`, `G` with `ts_.elt(Q, kMaxBindings)`
  and reads the first `d` of `G`; the Lean draws the point of `F^d`); each layer's `alpha`, `beta`
  (`begin_layer`, lines 54–57); one element per sumcheck round (`round`, lines 64–67); the input
  binding `alpha` (`zk_common.h` line 319). In the C++ the initial elements and layer 0's `alpha`,
  `beta` are one point; the Lean protocol has two challenge rounds there, each with its reader.
- The univariate skip (`lib/sumcheck/keccak_skip_circuit_link.h`,
  `keccak_skip_argument.h`): `ρ`, `n` elements; `r`, one; each sumcheck round's `s_i`, one; `u`,
  three.
- The batching challenge of a relatively packed Ligero step (`ExtensionForms`,
  `lib/zk/zk_extension_packed.h` lines 357–367): `nl` elements.
- The prepared Ligero test (`Ligero.LongfellowOrder.spec`, a `TwoStageTest.spec`;
  `lib/ligero/ligero_prover.h` lines 100–131, `ligero_transcript.h`): one point with `uldt`
  (`nwqrow` elements), `alphal` (`nl`), `alphaq` (`3 nq`) and `uquad` (`nqtriples`), read as the
  Lean challenge `(Fin R → F) × (Fin nL → F) × (Fin nQ → F)` in that order (`R = nwqrow`,
  `nL = nl + 3 nq`, `nQ = nqtriples`); then a second point, `choose(N, nreq)` (`gen_idx`, lines
  60–68).
- The MAC phase: `Kmac` and the final challenge, each a reader given by the scheme.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP IOP.ProtocolSpec

namespace SpecReaders

/-! ### GKR -/

section GKR

variable {F : Type} [Field F] [Fintype F] (r : CReader F)

/-- The sumcheck rounds of one GKR layer: per round the prover's polynomial, then one element. -/
def gkrRounds : (k : ℕ) → SpecReaders (GKR.Schedule.rounds F k)
  | 0 => empty
  | k + 1 => oneP (F × F) ++ (one F r ++ gkrRounds k)

/-- The GKR rounds of a circuit, output layer first: per layer `alpha`, `beta`, the sumcheck
rounds, the prover's wire claims; at the input, the binding element. -/
def gkrCircuit : {d : ℕ} → (C : GKR.Circuit F d) → SpecReaders (GKR.Schedule.circuit F C)
  | _, .input _ => one F r
  | _, .layer (inDim := b) _ tail =>
    one (F × F) (r.prod r) ++
      (gkrRounds r (2 * b) ++ (oneP (F × F) ++ gkrCircuit tail))

/-- **The GKR rounds of a circuit**: the `d` elements of the initial point, then `gkrCircuit`. -/
def gkrSpec {d : ℕ} (C : GKR.Circuit F d) : SpecReaders (GKR.Schedule.spec F C) :=
  one (Fin d → F) (CReader.pi d r) ++ (gkrCircuit r C)

/-- The largest GKR load of a circuit of output dimension `d`: `max d 2` elements, the initial
point's `d` or a layer's `alpha`, `beta`. -/
def gkrLoad (d : ℕ) : Load := r.load.nsmul (max d 2)

theorem gkrRounds_allLoads (m k : ℕ) : (gkrRounds r k).AllLoads (· ≤ (gkrLoad r m)) := by
  induction k with
  | zero => exact empty_allLoads _
  | succ k ih =>
    refine append_allLoads (oneP_allLoads _ _) (append_allLoads (one_allLoads _ ?_) ih)
    exact ⟨by simp only [gkrLoad, Load.nsmul]; nlinarith [r.load.draws.zero_le, le_max_right m 2],
      le_rfl⟩

theorem gkrCircuit_allLoads (m : ℕ) {d : ℕ} (C : GKR.Circuit F d) :
    (gkrCircuit r C).AllLoads (· ≤ (gkrLoad r m)) := by
  induction C with
  | input d =>
    refine one_allLoads _ ⟨?_, le_rfl⟩
    simp only [gkrLoad, Load.nsmul]
    nlinarith [r.load.draws.zero_le, le_max_right m 2]
  | layer Q tail ih =>
    refine append_allLoads (one_allLoads _ ⟨?_, ?_⟩)
      (append_allLoads (gkrRounds_allLoads r m _) (append_allLoads (oneP_allLoads _ _) ih))
    · simp only [CReader.prod_load, Load.add, gkrLoad, Load.nsmul]
      nlinarith [r.load.draws.zero_le, le_max_right m 2]
    · simp [gkrLoad, Load.add, Load.nsmul]

theorem gkrSpec_allLoads {d : ℕ} (C : GKR.Circuit F d) :
    (gkrSpec r C).AllLoads (· ≤ (gkrLoad r d)) := by
  refine append_allLoads (one_allLoads _ ⟨?_, ?_⟩) (gkrCircuit_allLoads r d C)
  · simp only [CReader.pi_load, Load.nsmul, gkrLoad]
    exact Nat.mul_le_mul_right _ (le_max_left d 2)
  · simp [gkrLoad, Load.nsmul]

end GKR

/-! ### Ligero -/

section Ligero

variable {K : Type} [Fintype K] (r : CReader K)

/-- **The two challenge rounds of a two-stage test** from the readers of the test challenge and
of the query. -/
def twoStage {Aux C Resp Q : Type} (rC : CReader C) (rQ : CReader Q) :
    SpecReaders (Ligero.TwoStageTest.spec Aux C Resp Q)
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [Ligero.TwoStageTest.spec])
  | ⟨⟨1, _⟩, _⟩ => rC
  | ⟨⟨2, _⟩, h⟩ => absurd h (by simp [Ligero.TwoStageTest.spec])
  | ⟨⟨3, _⟩, _⟩ => rQ

theorem twoStage_allLoads {Aux C Resp Q : Type} (rC : CReader C) (rQ : CReader Q)
    {good : Load → Prop} (hC : good rC.load) (hQ : good rQ.load) :
    (twoStage (Aux := Aux) (Resp := Resp) rC rQ).AllLoads good
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [Ligero.TwoStageTest.spec])
  | ⟨⟨1, _⟩, _⟩ => hC
  | ⟨⟨2, _⟩, h⟩ => absurd h (by simp [Ligero.TwoStageTest.spec])
  | ⟨⟨3, _⟩, _⟩ => hQ

end Ligero

end SpecReaders

end GordieHowe.SPBCS
