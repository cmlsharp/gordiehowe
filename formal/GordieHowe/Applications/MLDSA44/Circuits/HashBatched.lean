-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Circuits.Hash
public import GordieHowe.Applications.Keccak.Gadgets.Sponge
public import GordieHowe.Applications.Keccak.HashCircuit.KeccakOperands

@[expose] public section

/-!
# ML-DSA-44: the permutation counts of the H circuit over the circuit's sponge

The H circuit of the flagship native ML-DSA-44 system (`mldsa_hash_side`,
`lib/gordiehowe/examples/mldsa/mldsa_hash.h`) hashes as `MLDSAHashVerify` with a `KeccakSponge` does:
its SHAKE256 calls share one Keccak batch. SampleInBall reads the `c̃'` output (`assert_hash_side`
with a sponge, `ml_dsa_hash_circuit.h` lines 629-643 and 658-667), so ML-DSA's check `c̃ = c̃'`
holds by construction and `c̃` is no circuit input.

Calls, in circuit order (`ml_dsa_derive_mu`, `ml_dsa_mu.h` lines 115-121; `c_tilde_prime`,
`ml_dsa_hash_circuit.h` lines 585-600; `sample_in_ball`):

* `μ = SHAKE256(tr ‖ 0 ‖ |ctx| ‖ ctx ‖ msg, 64)` on `muLen ctxLen msgLen` bytes:
  `nMu ctxLen msgLen = (202 + ctxLen + msgLen) / 136` permutations (`nMu_eq`);
* `c̃' = SHAKE256(μ ‖ w1_tilde, 32)`: `nCommit = 7` permutations (`nCommit_eq`);
* SampleInBall's `SHAKE256(c̃', 136)`: one permutation.
-/

namespace GordieHowe.MLDSA44.HashBatchedCircuit

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakHook GordieHowe.PackedClaim GordieHowe.KeccakBatch GordieHowe.KeccakSponge
open Falcon512.HashCircuit (byteWires)
open HashCircuit.KeccakOperands (wordIdx stateWords)

variable {K : Type} [Field K] [DecidableEq K]

/-! ### Permutation counts -/

/-- The `μ` input length, `64 + 2 + ctxLen + msgLen` bytes. -/
abbrev muLen (ctxLen msgLen : ℕ) : ℕ := 64 + (2 + (ctxLen + msgLen))

/-- Permutations of the `μ` sponge. -/
abbrev nMu (ctxLen msgLen : ℕ) : ℕ := Shake256.numBlocks .shake256 (muLen ctxLen msgLen) 64

/-- Permutations of the `c̃'` sponge. -/
abbrev nCommit : ℕ := Shake256.numBlocks .shake256 (64 + 768) 32

theorem nMu_eq (ctxLen msgLen : ℕ) : nMu ctxLen msgLen = (202 + ctxLen + msgLen) / 136 := by
  show (64 + (2 + (ctxLen + msgLen))) / 136 + 1 + (if 64 = 0 then 0 else (64 - 1) / 136) = _
  norm_num
  omega

theorem nCommit_eq : nCommit = 7 := rfl

end GordieHowe.MLDSA44.HashBatchedCircuit
