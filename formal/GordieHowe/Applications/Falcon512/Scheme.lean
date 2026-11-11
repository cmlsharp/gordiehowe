-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.Signer
public import GordieHowe.Model.Signature.Scheme

@[expose] public section

/-!
# Falcon-512 as a signature scheme

- `falconSchemeT G`: the types of the scheme with the signer `G`: Falcon-512 public keys, the keys
  and coins of `G`, messages of `msgLen` bytes, signatures, and the salt as the public value
  (`GordieHowe/Applications/Falcon512/Spec/Signer.lean`).
- `falconBaseScheme G`: the Falcon-512 signature scheme (`Signature.BaseScheme`): keys from `G`,
  signing `G.signWith` with the drawn salt and private coins (no refusal, no oracle query),
  verification the vendored verifier `verifySig` (no oracle), public value the salt.
-/

namespace GordieHowe.Falcon512

variable {X Y : Type}

variable {msgLen : ℕ}

/-- The types of `falconBaseScheme G`: Falcon-512 public keys, the keys and coins of `G`, base
messages of `msgLen` bytes, signatures, and the salt as the public value. -/
abbrev falconSchemeT (G : Signer msgLen) : Signature.SchemeTypes where
  PK := PublicKey
  SK := G.SK
  KeyCoins := G.KeyCoins
  BMsg := Fin msgLen → UInt8
  BSig := Sig
  Pub := Salt
  Coins := Salt × G.SignCoins

/-- **The Falcon-512 signature scheme** (FIPS 206 / Falcon specification v1.2) with the signer `G`:
keys from `G`, signing `G.signWith` on a base message with the drawn salt and private coins (no
refusal), verification the vendored Falcon-512 verifier (no oracle), public value the salt. -/
def falconBaseScheme (G : Signer msgLen) : Signature.BaseScheme X Y (falconSchemeT G) where
  keyGen := G.keyGen
  q := 0
  ssign sk bm c := .pure (some (G.signWith sk bm c.1 c.2))
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ pk bm σ := verifySig pk bm σ
  qPub := 0
  pub _ σ := .pure σ.1.salt
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

end GordieHowe.Falcon512
