-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Applications.MLDSA44.Gadgets.SelectFirstTau

@[expose] public section

/-!
# ML-DSA: the rising-threshold selection lowering

Used by both ML-DSA configurations.

ML-DSA's lowering: the selection takes ML-DSA-44's `τ = 39` samples (`SampleInBall`), shared by
ML-DSA native and emulated; it is not part of the generic stack.

ML-DSA's `SampleInBall` selection (`SelectFirstTau`): this file states the lowering's source
predicate; the circuit, its soundness and its honest values are the gadget `SelectFirstTau`'s.
GordieHowe implements it as `select_first` (`lib/gordiehowe/lib/select.h`, with the circuit
`h2c.sample.select.route`) with the scan `SampleInBallScan`
(`lib/gordiehowe/examples/mldsa/sample_in_ball.h`). The constraints transcribed by
`SelectFirstTau.run` are those of the circuit `assert_sample_in_ball_gp`
(`lib/schemes/ml_dsa/ml_dsa_hash_circuit.h`, variant `kSibGpMemScalar`, report
label `ml-native`) with the threshold encoding `SibThresholdEncoding`
(`lib/schemes/ml_dsa/ml_dsa_sib_threshold.h`), which the C++ `SampleInBallScan` restates
(state bits `6`, initial `N - τ`, `leq` acceptance, `done = !thr[7]`, increment, label
`as_subfield(thr)`, output label `N - τ + k`).

* **Source** (`RisingSelection.Selects`): the claimed outputs `out` are the greedy scan's first `τ`
  samples, sample `i` accepted at rank `t` when it is at most `256 - τ + t`
  (`SelectScan.scanFirst (SelectFirstTau.accept (256 - τ))`, which
  `SelectFirstTau.scanFirst_accept` identifies with `GordieHowe.MLDSA44.acceptState`), with the stream and the
  outputs bit vectors.
* **Lowered**: the committed low threshold bits (`h2c.sample.select.threshold`,
  `SibThresholdEncoding::kLowBits` bits per sample) and the circuit at the challenge `δ` of its
  phase, the wire-level gadget `SelectFirstTau.run`, with the stream, the outputs and the low bits
  bit vectors.
* **Event**: `δ` is a root of the fingerprint polynomial of the filtered permutation check
  (`SelectFirstTau.badEvent`, degree `S`), from `SelectFirstTau.sound`; bound `S / |KH|` at `δ`'s
  phase.
* **Honest prover**: the low bits `SelectFirstTau.honestLow` of the honest thresholds
  `(256 - τ + rank) mod 256` (`examples/mldsa/sample_in_ball.h`; `SibThresholdEncoding::fill`,
  `ml_dsa_sib_threshold.h:48-52`), by `SelectFirstTau.complete`; no late value and no completeness
  event. The honest source assumes the scan selects `τ` samples; its failure is a failure of the
  honest input, charged where the stream is drawn.
-/

namespace GordieHowe
open IOP RealizedProgram.ProofSystem.PhaseLayout SelectScan
open scoped NNReal ENNReal

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {A KH : Type} [Field KH] [DecidableEq KH]

namespace MLDSA44.RisingSelection

/-- **The outputs are the greedy scan's selection** (on the data: a stream of `S` bytes and `τ`
outputs): the stream and the outputs are bit vectors, and the outputs are the first `τ` samples
accepted against the rising threshold `256 - τ + t`. -/
structure Selects {S τ : ℕ} (stream : Fin S → BitWires KH 8) (out : Fin τ → BitWires KH 8) :
    Prop where
  streamBool : ∀ i, Bits.AllBool (stream i)
  outBool : ∀ j, Bits.AllBool (out j)
  first : scanFirst (SelectFirstTau.accept (256 - τ)) (fun i => Bits.natOfBits (stream i))
    τ = some fun j => Bits.natOfBits (out j)

end MLDSA44.RisingSelection

end GordieHowe
