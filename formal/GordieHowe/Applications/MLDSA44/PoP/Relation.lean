-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.ChallengeEventCount
public import GordieHowe.Applications.MLDSA44.PoP.Compose
public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.Language.Realizations.MAC

@[expose] public section

/-!
# The ML-DSA-44 proof-of-possession relation

* The statement `MLDSA44.PoP.Statement ctxLen` is an encoded public key `key` (the 1312 bytes
  `pkEncode(ρ, t₁)` the C++ absorbs first after the two circuit ids)
  and a context `ctx` of `ctxLen` bytes; the witness `MLDSA44.PoP.Witness msgLen` is `msgLen`
  message bytes and the signature bytes.
* The relation `GordieHowe.MLDSA44.PoP.rel`: `GordieHowe.MLDSA44.VerifiesBytes` (FIPS 204 Algorithm 3,
  with `ExpandA` within `1008` SHAKE128 bytes per `RejNTTPoly` call (`ExpandAWithin`) and
  `SampleInBall` within `272` SHAKE256 bytes) holds for the witness's message bytes and signature
  bytes under the decoded key `GordieHowe.MLDSA44.pkDecode44`
  (Algorithm 23) and the context, so the relation is defined only at keys FIPS 204 can encode.
* The relation `GordieHowe.MLDSA44.PoP.relUpTo nm` of the paper: the empty context and a message of
  at most `nm` bytes, for a fixed public maximal length `nm` (the witness `VarWitness nm` carries
  its length).
-/

namespace GordieHowe

namespace MLDSA44

/-- **The vendored ML-DSA-44 parameter set** (`_root_.MLDSA.mldsa44`, FIPS 204 Table 1), named so
that statements need not write the `_root_` path that `GordieHowe.mldsa44` (the circuits' parameter
record) forces. -/
abbrev fipsParams : _root_.MLDSA.Params := _root_.MLDSA.mldsa44

end MLDSA44

namespace MLDSA44.PoP

/-- **The statement of the ML-DSA-44 proof of possession**: the encoded public key
`pkEncode(ρ, t₁)` (`MLDSA44.EncodedKey44`, 1312 bytes) and the `ctxLen`-byte context. -/
structure Statement (ctxLen : ℕ) where
  /-- The encoded public key. -/
  key : MLDSA44.EncodedKey44
  /-- The context bytes. -/
  ctx : Fin ctxLen → UInt8
deriving DecidableEq

/-- **The witness of an ML-DSA-44 proof of possession**: `msgLen` message bytes and the
signature bytes (`PoP.Witness`). -/
abbrev Witness (msgLen : ℕ) : Type := Configuration.Witness msgLen ByteArray

/-- **The ML-DSA-44 proof-of-possession relation**: `MLDSA44.VerifiesBytes` (FIPS 204
Algorithm 3, `ML-DSA.Verify`, with `ExpandA` within `1008` SHAKE128 bytes per `RejNTTPoly` call
(`ExpandAWithin`) and `SampleInBall` within `272` SHAKE256 bytes) holds for the witness's message
bytes and signature bytes under the decoded key and the context. -/
def rel (ctxLen msgLen : ℕ) : Set (Statement ctxLen × Witness msgLen) :=
  Function.uncurry fun s w =>
    MLDSA44.VerifiesBytes (MLDSA44.pkDecode44 s.key) (List.ofFn s.ctx) (List.ofFn w.message) w.signature

/-- **A witness of a message of at most `nm` bytes**: its length `L ≤ nm` and a witness at
`L` (`Configuration.VarWitness` at the signature bytes). -/
abbrev VarWitness (nm : ℕ) : Type := Configuration.VarWitness nm ByteArray

instance (nm : ℕ) : Inhabited (VarWitness nm) := ⟨⟨0, default⟩⟩

/-- **The ML-DSA-44 proof-of-possession relation for messages of at most `nm` bytes**, the
paper's `R_ML-DSA = {(pk, (m, σ)) : ML-DSA.Verify(pk, m, σ)}` for ML-DSA-44 with the empty
context and messages of at most `nm` bytes, for a fixed public maximal length `nm`: the witness's
message, of its length `L ≤ nm`, and signature are in `rel 0 L` (`Configuration.relUpTo`). -/
def relUpTo (nm : ℕ) : Set (Statement 0 × VarWitness nm) :=
  Configuration.relUpTo (rel 0) nm

/-- **`ExpandA(ρ)` of the decoded key finishes within the byte budget**: within `rejNTTByteBudget`
SHAKE128 bytes per `RejNTTPoly` call (`MLDSA44.ExpandAWithin`). -/
abbrev Statement.ExpandAWithin (s : Statement 0) : Prop :=
  MLDSA44.ExpandAWithin fipsParams (MLDSA44.pkDecode44 s.key).rho

/-- **The statements of the proofs of possession**: encoded ML-DSA-44 public keys (with the empty
context) whose decoded key's `ExpandA` finishes within the byte budget. At the other keys no
signature verifies (`relUpTo_expandAWithin`). -/
abbrev KeyStmt : Type := {s : Statement 0 // s.ExpandAWithin}

/-- **`relUpTo nm` (the paper's `R_ML-DSA`) on the statements `KeyStmt`**: a pair is in the relation
when its key, read as an encoded key, and its witness are in `relUpTo nm`. -/
def relOnKeys (nm : ℕ) : Set (KeyStmt × VarWitness nm) :=
  Prod.map Subtype.val id ⁻¹' relUpTo nm

/-- **Restricting `relUpTo` to `KeyStmt` loses no pair**: the key of every pair of `relUpTo nm`
has its `ExpandA` within the byte budget (`MLDSA44.Verifies.expandA`). -/
theorem relUpTo_expandAWithin {nm : ℕ} {p : Statement 0 × VarWitness nm} (h : p ∈ relUpTo nm) :
    p.1.ExpandAWithin := by
  have hv : MLDSA44.VerifiesBytes (MLDSA44.pkDecode44 p.1.key) (List.ofFn p.1.ctx)
      (List.ofFn p.2.2.message) p.2.2.signature := h
  obtain ⟨_, _, _, _, hv⟩ := hv.decode
  exact hv.expandA

end MLDSA44.PoP

open MLDSA44.PoP (Statement)

end GordieHowe
