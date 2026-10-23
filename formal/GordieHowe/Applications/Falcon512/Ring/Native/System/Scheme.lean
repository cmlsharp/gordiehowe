-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.Applications.Falcon512.Spec.Encoding
public import GordieHowe.Foundations.ToMathlib.FintypeBytes

@[expose] public section

/-!
# Falcon-512 as the base scheme of the ring signature

Falcon-512 as a `Ring.SigScheme`, the base scheme of the Falcon ring signature
(`lib/gordiehowe/examples/rings/falcon_ring.h`):

* the public keys (`PublicKey`, the vendored `Falcon.PublicKey` at `params512`), the messages of
  `msgLen` bytes, and the public value of a signature, its 40-byte salt `r` (`Salt`);
* the signatures (`Sig`): the vendored `Falcon.Signature`s whose compressed `s2` has the
  `sbytelen = 625` bytes the verifier decompresses (every signature the verifier accepts has that
  length, `compressedS2_length_of_verify`), a finite type;
* verification: the vendored serialized verifier `Falcon.verify` (Algorithm 16) at the keyless
  primitives `prims512` (`GordieHowe.Falcon512.verify`).

Key generation and signing are not specified in Lean: they are the parameter `Signer`, and the
scheme is `scheme G` for a signer `G`. The ring relation reads only the verifier; the
properties of the signer (`SigScheme.Correct`, which includes the salt condition: a signature
carries the drawn salt) are hypotheses of the ring corollaries only.

The extraction of a signature from the decoded values (`extractSig`): the salt and the centered
`s2` encoded by the explicit encoder `GordieHowe.Falcon512.encodeSignature`; on encoding bounds and decoded
verification it is a signature the serialized verifier accepts, carrying the salt
(`extractSig_spec`).

`HashToPoint(r ‖ m)` (`ringChallenge`) is the vendored `Falcon.Concrete.hashToPoint` with an empty
verification-key string, the keyless primitive of `prims512`: it does not depend on the ring member,
so it is computed once per statement, outside the circuit, as the C++ does (`falcon_ring.h:5-6`).
-/

namespace GordieHowe.Falcon512.Ring.Native

open GordieHowe.Ring

/-! ### Keys, salts and signatures -/

/-- **A Falcon-512 public key** (`Falcon.PublicKey` at `params512`). -/
abbrev PublicKey : Type := _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512

/-- A public key is its polynomial `h`, a vector of `512` coefficients modulo `q`. -/
def PublicKey.equiv : PublicKey ≃ Vector (ZMod 12289) 512 where
  toFun pk := pk.h
  invFun h := ⟨h⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype PublicKey := Fintype.ofEquiv _ PublicKey.equiv.symm

instance : DecidableEq PublicKey := PublicKey.equiv.decidableEq

instance : Inhabited PublicKey := ⟨⟨Vector.replicate 512 0⟩⟩

/-- **The salt** `r` of a signature, 40 bytes. -/
abbrev Salt : Type := _root_.Falcon.Bytes 40

/-- The bytes of the compressed `s2` the verifier decompresses, `sbytelen = 625`. -/
abbrev sigBytes : ℕ := _root_.Falcon.Concrete.params512.sbytelen

/-- **A Falcon-512 signature of the ring scheme**: a vendored signature whose compressed `s2` has
`sbytelen` bytes. -/
abbrev Sig : Type := {σ : _root_.Falcon.Signature // σ.compressedS2.length = sigBytes}

/-- A signature is its salt and its compressed `s2`. -/
def Sig.equiv : Sig ≃ Salt × Vector UInt8 sigBytes where
  toFun σ := (σ.1.salt, ⟨σ.1.compressedS2.toArray, by simp [σ.2]⟩)
  invFun p := ⟨⟨p.1, p.2.toList⟩, by simp⟩
  left_inv σ := by
    obtain ⟨⟨s, c⟩, h⟩ := σ
    simp
  right_inv p := by
    obtain ⟨s, c⟩ := p
    simp [Vector.toList]

instance : Fintype Sig := Fintype.ofEquiv _ Sig.equiv.symm

instance : DecidableEq Sig := Sig.equiv.decidableEq

instance : Inhabited Sig := ⟨Sig.equiv.symm (Vector.replicate 40 0, Vector.replicate sigBytes 0)⟩

/-- **Every signature the verifier accepts has `sbytelen` compressed bytes**: the decompression
rejects any other length. -/
theorem compressedS2_length_of_verify {pk : PublicKey} {msg : List UInt8}
    {σ : _root_.Falcon.Signature} (h : GordieHowe.Falcon512.verify pk msg σ) :
    σ.compressedS2.length = sigBytes := by
  obtain ⟨s, hd, -⟩ := (GordieHowe.Falcon512.verify_iff_verifyDecoded pk msg σ).mp h
  by_contra hne
  have hnone := _root_.Falcon.Concrete.decompress_eq_none_of_length_ne 512 σ.compressedS2 625 hne
  change _root_.Falcon.Concrete.decompress 512 σ.compressedS2 625 = some s at hd
  rw [hnone] at hd
  exact absurd hd (by simp)

/-- **A vendored signature as a signature of the scheme**: itself when it has `sbytelen` compressed
bytes, the default signature otherwise (computable). -/
def toSig (σ : _root_.Falcon.Signature) : Sig :=
  if h : σ.compressedS2.length = sigBytes then ⟨σ, h⟩ else default

theorem toSig_val {σ : _root_.Falcon.Signature} (h : σ.compressedS2.length = sigBytes) :
    (toSig σ).1 = σ := by
  simp only [toSig, h, dite_true]

/-! ### The verifier and the scheme -/

variable {msgLen : ℕ}

/-- **Falcon-512 verification of a ring scheme signature** (`GordieHowe.Falcon512.verify`, the vendored
`Falcon.verify` at `prims512`) on the bytes of an `msgLen`-byte message. -/
def verifySig (pk : PublicKey) (m : Fin msgLen → UInt8) (σ : Sig) : Bool :=
  _root_.Falcon.verify _root_.Falcon.Concrete.params512 GordieHowe.Falcon512.prims512 pk (List.ofFn m) σ.1

theorem verifySig_eq_true_iff {pk : PublicKey} {m : Fin msgLen → UInt8} {σ : Sig} :
    verifySig pk m σ = true ↔ GordieHowe.Falcon512.verify pk (List.ofFn m) σ.1 :=
  Iff.rfl

variable (msgLen) in
/-- **Falcon-512 key generation and signing**, which the Lean does not specify: secret keys, the
coins of key generation and the private coins of signing (finite), key generation from its coins,
and signing of a message with a drawn salt and private coins (Falcon specification v1.2,
Algorithms 1 and 10). The scheme's properties are hypotheses where used (`SigScheme.Correct`). -/
structure Signer where
  /-- Secret keys. -/
  SK : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- The private coins of signing. -/
  SignCoins : Type
  [instFintypeKeyCoins : Fintype KeyCoins]
  [instDecEqKeyCoins : DecidableEq KeyCoins]
  [instNonemptyKeyCoins : Nonempty KeyCoins]
  [instFintypeSignCoins : Fintype SignCoins]
  [instDecEqSignCoins : DecidableEq SignCoins]
  [instNonemptySignCoins : Nonempty SignCoins]
  /-- Key generation from its coins. -/
  keyGen : KeyCoins → PublicKey × SK
  /-- Signing with a drawn salt and private coins. -/
  signWith : SK → (Fin msgLen → UInt8) → Salt → SignCoins → Sig

attribute [instance] Signer.instFintypeKeyCoins Signer.instDecEqKeyCoins
  Signer.instNonemptyKeyCoins Signer.instFintypeSignCoins Signer.instDecEqSignCoins
  Signer.instNonemptySignCoins

/-- **Falcon-512 as a signature scheme** with the signer `G`: verification is the vendored
serialized verifier on `msgLen`-byte messages, the public value of a signature is its salt. -/
abbrev scheme (G : Signer msgLen) : SigScheme where
  PK := PublicKey
  SK := G.SK
  Msg := Fin msgLen → UInt8
  Sig := Sig
  Pub := Salt
  KeyCoins := G.KeyCoins
  SignCoins := G.SignCoins
  keyGen := G.keyGen
  pub σ := σ.1.salt
  signWith := G.signWith
  verify := verifySig

/-! ### The statement's challenge and the extracted signature -/

/-- **`HashToPoint(r ‖ m)` of a salt and a message** (the keyless primitive of `prims512`): the
challenge polynomial `c`, or `none` when the bounded rejection loop runs out of candidates. -/
def ringChallenge (r : Salt) (m : Fin msgLen → UInt8) : Option (_root_.Falcon.Rq 512) :=
  _root_.Falcon.Concrete.hashToPoint 512 r ByteArray.empty (List.ofFn m)

/-- The verifier's hash-to-point is `ringChallenge`, whatever the key. -/
theorem hashToPoint_eq_ringChallenge (r : Salt) (key : ByteArray) (m : Fin msgLen → UInt8) :
    GordieHowe.Falcon512.prims512.hashToPoint r key (List.ofFn m) = ringChallenge r m :=
  rfl

/-- **The signature extracted from a salt and an integer `s2`**: the encoding of
`Falcon512.encodeSignature` (the default signature if it fails or has another length).

Running time: the vendored `compress` on `512` coefficients, linear in `512`.
This running time is argued here, not proved in Lean. -/
-- spec-side
def extractSig (r : Salt) (s : _root_.Falcon.IntPoly 512) : Sig :=
  match GordieHowe.Falcon512.encodeSignature falcon512 r s with
  | some σ => toSig σ
  | none => default

/-- **The extracted signature verifies and carries the salt** on the encoding bounds and decoded
verification of `s2` at the salt. -/
theorem extractSig_spec {pk : PublicKey} {msg : List UInt8} {r : Salt}
    {s : _root_.Falcon.IntPoly 512} (hb : GordieHowe.Falcon512.EncodingBounds falcon512 s)
    (hv : GordieHowe.Falcon512.verifyDecoded pk msg r (_root_.Falcon.IntPoly.toRq s)) :
    GordieHowe.Falcon512.verify pk msg (extractSig r s).1 ∧ (extractSig r s).1.salt = r := by
  obtain ⟨σ, henc, hver⟩ := GordieHowe.Falcon512.extract_accepted_signature hb hv
  have hσ : (extractSig r s).1 = σ := by
    simp only [extractSig, henc]
    exact toSig_val (compressedS2_length_of_verify hver)
  rw [hσ]
  exact ⟨hver, (GordieHowe.Falcon512.encodeSignature_spec henc).1⟩

end GordieHowe.Falcon512.Ring.Native
