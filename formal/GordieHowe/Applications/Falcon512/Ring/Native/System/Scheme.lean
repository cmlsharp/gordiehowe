-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.Applications.Falcon512.Spec.Signer
public import VCVio.OracleComp.Constructions.SampleableType.Basic

@[expose] public section

/-!
# Falcon-512 as the base scheme of the ring signature

Falcon-512 as a `Ring.SigScheme`, the base scheme of the Falcon ring signature
(`lib/gordiehowe/examples/rings/falcon_ring.h`): `scheme G` for a signer `G`, over the public keys,
salts, signatures and verifier `verifySig` of `GordieHowe/Applications/Falcon512/Spec/Signer.lean`
on messages of `msgLen` bytes; its signing coins are the salt and the signer's private coins, and
the public value of a signature is its salt. The ring relation reads only the verifier; the
properties of the signer (its correctness error, `SigScheme.CorrectWithin`, and
`Signer.CarriesSalt`, which gives `SigScheme.PubOfCoins` at the salt, `pubOfCoins_scheme`) are
hypotheses of the ring corollaries only.
-/

namespace GordieHowe.Falcon512.Ring.Native

open GordieHowe.Ring

/-! ### The scheme -/

variable {msgLen : ℕ}

/-- **Falcon-512 as a signature scheme** with the signer `G`: signing draws the salt and the
signer's private coins, verification is the vendored serialized verifier on `msgLen`-byte
messages, the public value of a signature is its salt. -/
abbrev scheme (G : Signer msgLen) : SigScheme where
  PK := PublicKey
  SK := G.SK
  Msg := Fin msgLen → UInt8
  Sig := Sig
  Pub := Salt
  KeyCoins := G.KeyCoins
  SignCoins := Salt × G.SignCoins
  keyGen := G.keyGen
  pub σ := σ.1.salt
  signWith sk m (c : Salt × G.SignCoins) := G.signWith sk m c.1 c.2
  verify := verifySig

/-- **The public value of an honest signature is the drawn salt** for a signer whose signatures
carry it. -/
theorem pubOfCoins_scheme {G : Signer msgLen} (hG : G.CarriesSalt) :
    (scheme G).PubOfCoins Prod.fst :=
  fun _ m (c : Salt × G.SignCoins) => hG _ m c.1 c.2

end GordieHowe.Falcon512.Ring.Native
