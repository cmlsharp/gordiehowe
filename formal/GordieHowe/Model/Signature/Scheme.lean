-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.OracleProg

public section

/-!
# Base signature schemes with a random oracle

The base signature scheme that the ring signer of `GordieHowe/Model/RingSignature/Base.lean`
extends: the scheme's keys (FIPS 204, FIPS 206), its ordinary signer `ssign` on base messages,
base verification `bverify` at the oracle, and the public value of a base signature (`pub`:
Falcon's salt, `Unit`, or ML-DSA's `w₁` recomputed from the key and the signature), a classical
oracle program.

- `SchemeTypes`: the types of a base scheme.
- `BaseScheme X Y T`: a base scheme with the random oracle `X → Y` and the types `T`.
- `SchemeTypes.Candidate T`, `BaseScheme.Candidate`: a public key, a base message and a base
  signature (`.pk`, `.msg`, `.sig`).
-/

namespace GordieHowe.Signature

/-- **The types of a base scheme**: public keys, secret keys, the coins of key generation, base
messages, base signatures, public values and the coins of signing. A `BaseScheme` takes its types
as this parameter. The record holds types only: the finiteness and decidable equality the games
read are instance-implicit binders on its projections (`[Fintype T.Coins]`), found by instance
search on the named types of a concrete record. -/
structure SchemeTypes where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- Base messages. -/
  BMsg : Type
  /-- Base signatures. -/
  BSig : Type
  /-- Public values. -/
  Pub : Type
  /-- The coins of signing. -/
  Coins : Type

/-- **A key pair**: a public key and a secret key, as key generation returns them. -/
abbrev KeyPair (PK SK : Type) : Type := PK × SK

namespace KeyPair

variable {PK SK : Type}

/-- The public key. -/
@[simp] abbrev pk (kp : KeyPair PK SK) : PK := kp.1

/-- The secret key. -/
@[simp] abbrev sk (kp : KeyPair PK SK) : SK := kp.2

end KeyPair

/-- **A draw of the honest signing experiments**: the oracle, the draw for the keys, of a type
`Keys` (in `RingScheme.CompletenessDraw` and `BaseScheme.RefusalDraw` the members' key coins
`Fin r → KeyCoins`), and the signing coins. -/
abbrev SigningDraw (X Y Keys Coins : Type) : Type := (X → Y) × Keys × Coins

namespace SigningDraw

variable {X Y Keys Coins : Type}

/-- The oracle. -/
@[simp] abbrev oracle (d : SigningDraw X Y Keys Coins) : X → Y := d.1

/-- The draw for the keys. -/
@[simp] abbrev keys (d : SigningDraw X Y Keys Coins) : Keys := d.2.1

/-- The signing coins. -/
@[simp] abbrev coins (d : SigningDraw X Y Keys Coins) : Coins := d.2.2

end SigningDraw

/-- **A candidate forgery with the types `T`**: a public key, a base message and a base signature
`(pk, m, σ)`. -/
abbrev SchemeTypes.Candidate (T : SchemeTypes) : Type := T.PK × T.BMsg × T.BSig

namespace SchemeTypes.Candidate

variable {T : SchemeTypes}

/-- The public key. -/
@[simp] abbrev pk (f : T.Candidate) : T.PK := f.1

/-- The base message. -/
@[simp] abbrev msg (f : T.Candidate) : T.BMsg := f.2.1

/-- The base signature. -/
@[simp] abbrev sig (f : T.Candidate) : T.BSig := f.2.2

end SchemeTypes.Candidate

/-- **A base scheme** with the random oracle `X → Y` and the types `T`: the scheme's keys from
uniform coins; the ordinary signer on base messages from the secret key and uniform coins (at most
`q` queries; it may refuse); verification at the oracle; and the public value of a signature under
a key (a program with at most `qPub` queries). -/
structure BaseScheme (X Y : Type) (T : SchemeTypes) where
  /-- Key generation from its coins. -/
  keyGen : T.KeyCoins → KeyPair T.PK T.SK
  /-- The bound on the signers' queries. -/
  q : ℕ
  /-- The ordinary base signer on base messages; `none` is a refusal. -/
  ssign : T.SK → T.BMsg → T.Coins → OracleProg X Y (Option T.BSig)
  /-- It makes at most `q` queries. -/
  ssign_queries : ∀ sk bm c, (ssign sk bm c).QueriesLE q
  /-- Base verification at an oracle. -/
  bverify : (X → Y) → T.PK → T.BMsg → T.BSig → Bool
  /-- The bound on the queries of the public value. -/
  qPub : ℕ
  /-- The public value of a base signature under a key. -/
  pub : T.PK → T.BSig → OracleProg X Y T.Pub
  /-- It makes at most `qPub` queries. -/
  pub_queries : ∀ pk σ, (pub pk σ).QueriesLE qPub

namespace BaseScheme

variable {X Y : Type} {T : SchemeTypes}

/-- Public keys: those of the types `T`. -/
abbrev PK (_ : BaseScheme X Y T) : Type := T.PK

/-- Secret keys: those of the types `T`. -/
abbrev SK (_ : BaseScheme X Y T) : Type := T.SK

/-- The coins of key generation: those of the types `T`. -/
abbrev KeyCoins (_ : BaseScheme X Y T) : Type := T.KeyCoins

/-- Base messages: those of the types `T`. -/
abbrev BMsg (_ : BaseScheme X Y T) : Type := T.BMsg

/-- Base signatures: those of the types `T`. -/
abbrev BSig (_ : BaseScheme X Y T) : Type := T.BSig

/-- Public values: those of the types `T`. -/
abbrev Pub (_ : BaseScheme X Y T) : Type := T.Pub

/-- The coins of signing: those of the types `T`. -/
abbrev Coins (_ : BaseScheme X Y T) : Type := T.Coins

/-- **A candidate forgery of a base scheme**: a public key, a base message and a base signature
of its types (`BaseScheme.MUForgery`, the output of a multi-user adversary, is one). -/
abbrev Candidate (B : BaseScheme X Y T) : Type := B.PK × B.BMsg × B.BSig

end BaseScheme

end GordieHowe.Signature
