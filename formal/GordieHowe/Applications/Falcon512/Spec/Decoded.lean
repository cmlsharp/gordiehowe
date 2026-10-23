-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.Basic

@[expose] public section

/-!
# Falcon verification after decoding

`verifyDecoded` is the relation the arithmetic circuits establish: the vendored verification
core after decoding, with its hash-to-point function and its norm check, on a decoded signature
polynomial. The serialized verifier `Falcon.verify` follows from it together with a constructive
encoding of the signature, whose success follows from the circuits' encodability checks; no codec
validity is assumed as a circuit fact.
-/

namespace GordieHowe.Falcon512

/-- The relation the circuits establish on the message bytes `msg`,
using the vendored hash and norm check with the signature polynomial already decoded: the hash
succeeds (its candidate budget is not exhausted) and its point passes the norm check. -/
def verifyDecoded (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512)
    (msg : List UInt8) (salt : _root_.Falcon.Bytes 40) (s₂ : _root_.Falcon.Rq 512) : Prop :=
  ∃ c, prims512.hashToPoint salt (prims512.publicKeyBytes pk.h) msg = some c ∧
    algebraOk falcon512 pk.h c s₂

/-- Successful fixed-stream sampling and the algebraic relation imply decoded
verification. The sampler reads the salt and message bytes as naturals. -/
theorem verifyDecoded_of_acceptedCandidates
    {pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512}
    {msg : List UInt8} {salt : _root_.Falcon.Bytes 40} {s₂ : _root_.Falcon.Rq 512}
    {c : Fin falcon512.n → ℕ}
    (hc : acceptedCandidates falcon512 shake256 (salt.toList.map UInt8.toNat) (msg.map UInt8.toNat)
      = some c)
    (ha : algebraOk falcon512 pk.h (ofCoeff fun i => (c i : _root_.Falcon.Coeff)) s₂) :
    verifyDecoded pk msg salt s₂ := by
  exact ⟨_, fixedStreamChallenge_agree hc (prims512.publicKeyBytes pk.h), ha⟩

/-- Exact codec bridge. The decompression equality is a condition on a supplied
serialized signature, not a fact claimed by either circuit. A final
signature-extraction theorem must derive it from circuit acceptance. -/
theorem verify_iff_verifyDecoded
    (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512)
    (msg : List UInt8) (sig : _root_.Falcon.Signature) :
    verify pk msg sig ↔ ∃ s₂Int,
      prims512.decompress sig.compressedS2 _root_.Falcon.Concrete.params512.sbytelen = some s₂Int
        ∧ verifyDecoded pk msg sig.salt (_root_.Falcon.IntPoly.toRq s₂Int) :=
  (verify_iff_algebraOk pk msg sig).trans <| exists_congr fun _ =>
    ⟨fun ⟨c, hd, hh, ha⟩ => ⟨hd, c, hh, ha⟩, fun ⟨hd, c, hh, ha⟩ => ⟨c, hd, hh, ha⟩⟩

end GordieHowe.Falcon512
