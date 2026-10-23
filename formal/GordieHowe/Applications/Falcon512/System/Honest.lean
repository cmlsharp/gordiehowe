-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.System.Source
public import GordieHowe.Language.Realizations.MACEquality
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Applications.Falcon512.Gadgets.SelectFirstN
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Applications.Falcon512.System.Algebra
public import GordieHowe.Applications.Falcon512.PoP.Relation
public import GordieHowe.Applications.Falcon512.PoP.Configuration
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebraHonest

@[expose] public section

/-!
# Falcon: the honest values of domain H

The honest values of domain H that both Falcon configurations compute from an honest input
(`GordieHowe.Falcon512.PoP.HonestInput`), following the C++ generators (`falcon_witness`,
`lib/gordiehowe/examples/falcon/falcon_emulated.h`): the SHAKE256 input of the nonce and message bytes
(`honestSeed`) and the selected samples as bits (`sampleBits`), with the facts the honest provers
read: the samples are `16`-bit (`samples_lt`), and the sample bits are Boolean and read back the
samples (`sampleBits_bool`, `natOfBits_sampleBits`). Domain A's honest values are each
configuration's.
-/

namespace GordieHowe.Falcon512.Emulated

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch
  GordieHowe.KeccakSponge GordieHowe.PackedClaim GordieHowe.HashCircuit Params

variable {KH F : Type} [Field KH] [DecidableEq KH] [Field F] {msgLen : ℕ}

/-! ### The honest assignment -/

/-- **The honest SHAKE256 input**: the bit wires of the nonce bytes, then of the message bytes. -/
-- spec-side
def honestSeed (y : Falcon512.PoP.HonestInput msgLen) : Fin (falconLen msgLen) → BitWires KH 8 :=
  seed (HashCircuit.wiresOfByteVec y.nonce) (HashCircuit.wiresOfByteVec y.message)

/-- **The bits of the samples**: bit `b` of sample `i` is bit `b` of `c i` (`select.raw`, `c_A`). -/
-- spec-side
def sampleBits {K : Type} [Field K] (c : Fin falcon512.n → ℕ) :
    Fin falcon512.n → BitWires K falconSampleBits :=
  fun i b => constBit (c i) b

/-! ### Domain H -/

/-- The samples of a supported honest input are below `5q`, hence `16`-bit. -/
theorem samples_lt {y : Falcon512.PoP.HonestInput msgLen} (hy : y.Valid) (j : Fin falcon512.n) :
    y.samples j < 2 ^ falconSampleBits :=
  Nat.lt_trans (of_decide_eq_true (firstAccepted_accept hy.samples j)) falcon512.bound_lt

/-- The bits of a `16`-bit sample read back the sample. -/
theorem natOfBits_sampleBits {K : Type} [Field K] [DecidableEq K] {c : Fin falcon512.n → ℕ}
    (hc : ∀ j, c j < 2 ^ falconSampleBits) (j : Fin falcon512.n) :
    natOfBits (sampleBits (K := K) c j) = c j := by
  change natOfBits (fun b : Fin falconSampleBits => constBit (K := K) (c j) b) = c j
  rw [natOfBits_constBit, Nat.mod_eq_of_lt (hc j)]

/-- The sample bits are bits. -/
theorem sampleBits_bool {K : Type} [Field K] (c : Fin falcon512.n → ℕ) (i : Fin falcon512.n)
    (b : Fin falconSampleBits) : sampleBits (K := K) c i b = 0 ∨ sampleBits (K := K) c i b = 1 :=
  constBit_bool _ _

end GordieHowe.Falcon512.Emulated
