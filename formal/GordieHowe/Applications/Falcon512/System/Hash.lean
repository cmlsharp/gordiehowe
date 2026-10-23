-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Circuits.HashStep
public import GordieHowe.Applications.Keccak.Gadgets.WordAbsorb
public import GordieHowe.Applications.Falcon512.Spec.Decoded

@[expose] public section

/-!
# Falcon: the hash-to-point inputs of domain H

The SHAKE256 call of Falcon emulated (`lib/gordiehowe/examples/falcon/falcon_hash.h`, `hash_to_point`,
lines 46-60; `lib/gordiehowe/lib/keccak.h`, `shake256`, at `W = 16`):
`SHAKE256(nonce ‖ message)` squeezed to `2 · 639` bytes over one batch of Keccak-f permutations, and
the sample stream read from the output bytes. Sample `i` reads byte `2i + 1` as bits `0 … 7` and
byte `2i` as bits `8 … 15` (`falcon_hash.h:54-57`, the reshape to `[639][2][8]` reversed on the
middle axis; `GordieHowe.Falcon512.HashCircuit.sampleAt`).

This file states the objects both Falcon configurations read on this call:

* **The trace words** (`Words`, node `h2p.shake.states`): `HashCircuit.Word` of the
  `falconPerms msgLen` permutations, `100` words of `GF(2^16)` per state; word `4 (5x + y) + c` of a
  state holds bits `16c … 16c + 15` of lane `(x, y)` (`keccak.h`, `Shake256::start_word`,
  `round_word`). For a `msgLen`-byte message there are `blocks = (40 + msgLen) / 136 + 1` absorbed
  blocks and `perms = blocks + 9` permutations (`falconPerms`).
* **The SHAKE256 input** (`seed`): the nonce bytes, then the message bytes, Boolean when the nonce
  and message bits are (`seed_allBool`).
* **The extracted bytes** (`bytesOf`, `nonceOf`, `messageOf`, `bytesOf_wiresOfByteVec`,
  `nonceOf_toNat`, `messageOf_toNat`): the nonce and message bit wires read back as bytes.
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch GordieHowe.KeccakSponge GordieHowe.PackedClaim
  GordieHowe.HashCircuit

variable {KH : Type} [Field KH] {msgLen : ℕ}

variable (KH msgLen) in
/-- **The words of the Keccak trace** (`h2p.shake.states`): `HashCircuit.Word` of the
`falconPerms msgLen` permutations with `falconExtra msgLen` absorbed blocks after the first. -/
abbrev Words : Type := HashCircuit.Word (falconPerms msgLen) (falconExtra msgLen) → KH

/-- **The SHAKE256 input**: the `40` nonce bytes, then the `msgLen` message bytes, each byte's bit
`j` at index `8k + j` of its bit vector (`nonce_message`, the concatenation view). -/
def seed (nonce : BitWires KH (8 * falcon512.saltBytes)) (message : BitWires KH (8 * msgLen)) :
    Fin (falconLen msgLen) → BitWires KH 8 :=
  Fin.append (HashCircuit.byteWires nonce) (HashCircuit.byteWires message)

variable [DecidableEq KH]

/-- The bytes of a bit vector, as naturals. -/
-- spec-side
def bytesOf {m : ℕ} (bits : BitWires KH (8 * m)) : List ℕ :=
  List.ofFn fun i => natOfBits (HashCircuit.byteWires bits i)

/-- The bytes of the bit wires of bytes are the bytes. -/
theorem bytesOf_wiresOfByteVec {m : ℕ} {v : Fin m → ℕ}
    (hv : ∀ i, v i < 256) : bytesOf (HashCircuit.wiresOfByteVec (K := KH) v) = List.ofFn v := by
  rw [bytesOf]
  exact congrArg List.ofFn (funext fun i => HashCircuit.natOfBits_byteWires_wiresOfByteVec hv i)

variable [CharP KH 2] {B : PackedBasis KH 4}
  {nonce : BitWires KH (8 * falcon512.saltBytes)} {message : BitWires KH (8 * msgLen)}
  {states : Words KH msgLen}

omit [DecidableEq KH] [CharP KH 2] in
/-- The seed bytes are Boolean when the nonce and message bits are. -/
theorem seed_allBool (hn : AllBool nonce) (hm : AllBool message) (i : Fin (falconLen msgLen)) :
    AllBool (seed nonce message i) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [seed, Fin.append_left]
    exact HashCircuit.byteWires_allBool hn i
  · rw [seed, Fin.append_right]
    exact HashCircuit.byteWires_allBool hm i

/-! ### The extracted bytes -/

/-- **The extracted nonce**: the nonce bytes as `UInt8`. -/
-- spec-side
def nonceOf (nonce : BitWires KH (8 * falcon512.saltBytes)) : Vector UInt8 falcon512.saltBytes :=
  Vector.ofFn fun i => (natOfBits (HashCircuit.byteWires nonce i)).toUInt8

/-- **The extracted message**: the message bytes as `UInt8`. -/
-- spec-side
def messageOf (message : BitWires KH (8 * msgLen)) : Fin msgLen → UInt8 :=
  fun i => (natOfBits (HashCircuit.byteWires message i)).toUInt8

omit [CharP KH 2] in
theorem nonceOf_toNat (nonce : BitWires KH (8 * falcon512.saltBytes)) :
    (nonceOf nonce).toList.map UInt8.toNat = bytesOf nonce := by
  apply List.ext_getElem
  · simp [nonceOf, bytesOf]
  · intro i hi hj
    simp only [nonceOf, bytesOf, Vector.toList_ofFn, List.getElem_map, List.getElem_ofFn]
    rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Bits.natOfBits_lt _)]

omit [CharP KH 2] in
theorem messageOf_toNat (message : BitWires KH (8 * msgLen)) :
    (List.ofFn (messageOf message)).map UInt8.toNat = bytesOf message := by
  rw [bytesOf, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, messageOf]
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Bits.natOfBits_lt _)]

end GordieHowe.Falcon512.Emulated
