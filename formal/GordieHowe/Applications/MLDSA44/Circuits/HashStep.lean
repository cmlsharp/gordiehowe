-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Circuits.HashBatched
public import GordieHowe.Applications.Keccak.HashCircuit.Relation

@[expose] public section

/-!
# The honest outputs of the ML-DSA batched H

The batched H circuit runs its SHAKE256 calls as the sponge over one batch of Keccak-f
permutations (the C++ `KeccakSponge::hash`, `lib/circuits/keccak/keccak_sponge.h`). `honestMu`
and `honestCommit` are the squeezes of the honest `μ` and `c̃'` permutations:
Keccak-f on the sponge starts (`KeccakTrace.spongeStart`) of the honest inputs
`GordieHowe.MLDSA44.HashCircuit.muInput` and `GordieHowe.MLDSA44.HashCircuit.commitInput`.
-/

namespace GordieHowe.MLDSA44.HashBatchedCircuit

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakHook GordieHowe.PackedClaim GordieHowe.KeccakBatch GordieHowe.KeccakSponge
open GordieHowe.HashCircuit (statesOf statesOfBits wordBits packStates statesOf_packStates stateWords_packStates statesOf_allBool)
open HashCircuit.KeccakOperands (wordIdx stateOf stateWords)
open Falcon512.HashCircuit (byteWires byteWires_allBool wiresOfByteVec wiresOfBytes)

variable {K : Type} [Field K] [DecidableEq K]

variable {mw ctxLen msgLen : ℕ}

section Honest

variable (trW : BitWires K (8 * 64)) (ctxW : BitWires K (8 * ctxLen)) (msgW : BitWires K (8 *
    msgLen))
  (w1W : BitWires K (8 * 768))

/-- The honest `μ` output: the squeeze of the honest `μ` permutations. -/
-- spec-side
def honestMu : Fin 64 → BitWires K 8 :=
  squeezeOut fun k : Fin (nMu ctxLen msgLen) => keccakF (spongeStart .shake256 (HashCircuit.muInput
      trW ctxW msgW) k)

/-- The honest `c̃'` output. -/
-- spec-side
def honestCommit : Fin 32 → BitWires K 8 :=
  squeezeOut fun k : Fin nCommit =>
    keccakF (spongeStart .shake256 (HashCircuit.commitInput (honestMu trW ctxW msgW) w1W) k)

end Honest

end GordieHowe.MLDSA44.HashBatchedCircuit
