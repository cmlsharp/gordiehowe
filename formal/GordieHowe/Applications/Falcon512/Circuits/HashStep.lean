-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Circuits.Hash
public import GordieHowe.Applications.Keccak.HashCircuit.Relation

@[expose] public section

/-!
# Falcon's batched-Keccak H permutation count

The permutation count of Falcon's batched-Keccak H circuit. The H circuit (`hash_to_point`,
`lib/gordiehowe/examples/falcon/falcon_hash.h`) hashes the committed `salt ‖ message` with SHAKE256 in
one Keccak batch, forms the sample stream from the `2S` output bytes (big-endian: bits `0…7` from
byte `2i + 1`, bits `8…15` from byte `2i`, `GordieHowe.Falcon512.HashCircuit.sampleAt`), and runs the selection
circuit.

* `falconLen msgLen`: the SHAKE256 input length, the salt then the message.
* `falconExtra msgLen`: the absorb permutations beyond the first, so that
  `A = falconExtra msgLen + 1` absorb permutations are followed by nine squeezes:
  `falconPerms msgLen = A + 9` permutations.
-/

namespace GordieHowe.HashCircuit

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch GordieHowe.KeccakSponge PackedClaim

variable {K : Type} [Field K]

/-! ### Falcon's batch -/

/-- Falcon's SHAKE256 input length on a `msgLen`-byte message: the salt, then the message. -/
abbrev falconLen (msgLen : ℕ) : ℕ := falcon512.saltBytes + msgLen

/-- The absorb permutations beyond the first: `(40 + msgLen) / 136`. -/
abbrev falconExtra (msgLen : ℕ) : ℕ := falconLen msgLen / SpongeSpec.shake256.rate

/-- Falcon's permutations: the absorbs and nine squeezes. -/
def falconPerms (msgLen : ℕ) : ℕ := falconExtra msgLen + 10

end GordieHowe.HashCircuit
