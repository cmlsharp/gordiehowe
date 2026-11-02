-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.ChallengeEventCount
public import GordieHowe.Applications.Falcon512.Circuits.Hash
public import GordieHowe.Applications.Falcon512.Spec.Decoded
public import GordieHowe.Applications.Falcon512.Spec.Encoding
public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Applications.Configuration.Witness

@[expose] public section

/-!
# The Falcon-512 proof-of-possession relation

`PoP.Falcon512.rel msgLen` is the relation a Falcon-512 proof of possession proves: the
serialized verifier `Falcon512.verify` accepts the witness's `msgLen` message bytes and signature
(`GordieHowe.Falcon512.PoP.Witness`) under the public key.
-/

namespace GordieHowe.Falcon512.PoP

open IOP
open scoped NNReal

/-- The empty signature, returned by the extractor when decoding fails. -/
instance instInhabitedSignature_pQ : Inhabited _root_.Falcon.Signature := ⟨⟨Vector.replicate 40 0, []⟩⟩

end GordieHowe.Falcon512.PoP

namespace GordieHowe.Falcon512.PoP

/-- **The witness of a Falcon-512 proof of possession**: `msgLen` message bytes and a Falcon-512
signature (`PoP.Witness`). -/
abbrev Witness (msgLen : ℕ) : Type := Configuration.Witness msgLen _root_.Falcon.Signature

/-- **The Falcon-512 proof-of-possession relation**: the serialized verifier `Falcon512.verify`
(Falcon specification v1.2, Algorithm 16, at the vendored primitives) accepts the witness's
message bytes and signature under the public key. -/
def rel (msgLen : ℕ) :
    Set (_root_.Falcon.PublicKey _root_.Falcon.Concrete.params512 × Witness msgLen) :=
  {p | Falcon512.verify p.1 (List.ofFn p.2.message) p.2.signature}

/-- **The Falcon-512 relation at the signatures the circuits sample**: the pairs of `rel` whose
`HashToPoint` succeeds on the H circuit's fixed stream of `S = 717` samples
(`Falcon512.acceptedCandidates`), the restriction of the honest prover's completeness. The
verifier `Falcon512.verify` draws up to `1024` samples; a signature outside this set (its salt
and message give fewer than `512` samples below `5q` among the first `717`) has no honest input.
Over a uniform `2 · 717`-byte stream the excluded fraction is at most `2^-256`
(`Falcon512.unsupportedFraction_le`). -/
def relSupported (msgLen : ℕ) :
    Set (_root_.Falcon.PublicKey _root_.Falcon.Concrete.params512 × Witness msgLen) :=
  {p | p ∈ rel msgLen ∧ (Falcon512.acceptedCandidates falcon512 shake256
    (p.2.signature.salt.toList.map UInt8.toNat) ((List.ofFn p.2.message).map UInt8.toNat)).isSome}

end GordieHowe.Falcon512.PoP
