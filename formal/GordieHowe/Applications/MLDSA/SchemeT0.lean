-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Scheme
public import GordieHowe.Applications.MLDSA.Signing.Hedged

public section

/-!
# ML-DSA with `t₀` published as a signature scheme

- `T0Signer X Y p prims Msg Coins`: an ordinary signer for ML-DSA with `t₀` published, with
  signing coins `Coins`: a signing program from the secret key, the message and the coins, and a
  bound on its queries. `T0Signer.hedged src O`: one call of hedged FIPS 204 signing (`stdProg`)
  with the masks of `src`.
- `mldsaT0SchemeT`, `mldsaT0BaseScheme O enc S`: ML-DSA with the published key `(ρ, t₁, t₀)` as a
  signature scheme (`Signature.BaseScheme`) with the ordinary signer `S`: keys from `keyGen`,
  verification `ringVerify` against the commitment hash read from the oracle at the recomputed
  `w₁`, public value `w₁ = w1Of enc pk σ`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA

variable {X Y : Type} {p : Params} (prims : Primitives p) {Msg : Type}

/-- **An ordinary signer for ML-DSA with `t₀` published**, with signing coins `Coins`: a signing
program from the secret key, the message and the coins, and a bound on its queries. -/
structure T0Signer (X Y : Type) (p : Params) (prims : Primitives p) (Msg Coins : Type) where
  /-- The bound on the queries. -/
  q : ℕ
  /-- The signing program. -/
  sign : SecretKey p → Msg → Coins → OracleProg X Y (Option (FIPSSignature p prims))
  /-- It makes at most `q` queries. -/
  sign_queries : ∀ sk m c, (sign sk m c).QueriesLE q

variable (Msg) in
/-- The types of ML-DSA with `t₀` published: published keys `(ρ, t₁, t₀)`, secret keys from
32-byte seeds, messages `Msg`, FIPS 204 signatures, the public value `w₁`, signing coins. -/
abbrev mldsaT0SchemeT (Coins : Type) : Signature.SchemeTypes where
  PK := PubKey p prims
  SK := SecretKey p
  KeyCoins := Bytes 32
  BMsg := Msg
  BSig := FIPSSignature p prims
  Pub := BucketVec p
  Coins := Coins

variable [nttOps : NTTRingOps]

section Hedged

variable {prims} {T : ℕ} [NeZero (bucketCount p)] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Inhabited prims.Hint] [Nonempty (MaskBox p)]

/-- **One call of hedged FIPS 204 signing** with the masks of `src` and the oracles `O`: the
ordinary hedged signer `stdProg` at the coins of one call, with at most `1 + T · qr + T` queries
(`stdProg_queries`). -/
@[expose] def T0Signer.hedged (src : MaskSource X Y p T Msg) (O : MLDSAOracles X Y p Msg) :
    T0Signer X Y p prims Msg src.Rnd where
  q := 1 + T * src.qr + T
  sign sk m r := stdProg prims src O 1 sk m fun _ => r
  sign_queries sk m r := stdProg_queries prims src O 1 sk m fun _ => r

end Hedged

/-- **ML-DSA with `t₀` published** (FIPS 204 §5.1 public key `(ρ, t₁)` with `t₀`, which need not be
secret, §6.1), with the oracles `O`, the encoding `enc` of recomputed commitments and the ordinary
signer `S`: keys from `keyGen`, verification `ringVerify` against the commitment hash read from the
oracle at the recomputed `w₁`, public value `w₁ = w1Of enc pk σ`. -/
@[expose] def mldsaT0BaseScheme (O : MLDSAOracles X Y p Msg)
    (enc : Vector prims.High p.k → BucketVec p) {Coins : Type}
    (S : T0Signer X Y p prims Msg Coins) :
    Signature.BaseScheme X Y (mldsaT0SchemeT prims Msg Coins) where
  keyGen := keyGen prims
  q := S.q
  ssign := S.sign
  ssign_queries := S.sign_queries
  bverify H pk bm σ := ringVerify prims (O.hOrc H) enc (pubPk prims pk) bm (w1Of prims enc pk σ) σ
  qPub := 0
  pub pk σ := .pure (w1Of prims enc pk σ)
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

section Lemmas

variable {prims} (O : MLDSAOracles X Y p Msg) (enc : Vector prims.High p.k → BucketVec p)
  {Coins : Type} (S : T0Signer X Y p prims Msg Coins)

/-- The ordinary signer of `mldsaT0BaseScheme O enc S` is `S.sign`. -/
@[simp] theorem mldsaT0BaseScheme_ssign : (mldsaT0BaseScheme prims O enc S).ssign = S.sign := rfl

/-- The query bound of `mldsaT0BaseScheme O enc S` is `S.q`. -/
@[simp] theorem mldsaT0BaseScheme_q : (mldsaT0BaseScheme prims O enc S).q = S.q := rfl

/-- Key generation of `mldsaT0BaseScheme O enc S` is `keyGen`. -/
@[simp] theorem mldsaT0BaseScheme_keyGen :
    (mldsaT0BaseScheme prims O enc S).keyGen = keyGen prims := rfl

/-- Verification of `mldsaT0BaseScheme O enc S` is `ringVerify` at the recomputed `w₁`. -/
@[simp] theorem mldsaT0BaseScheme_bverify (H : X → Y) (pk : PubKey p prims) (bm : Msg)
    (σ : FIPSSignature p prims) :
    (mldsaT0BaseScheme prims O enc S).bverify H pk bm σ =
      ringVerify prims (O.hOrc H) enc (pubPk prims pk) bm (w1Of prims enc pk σ) σ := rfl

/-- The public value of `mldsaT0BaseScheme O enc S` is `w1Of enc pk σ`, read with no query. -/
@[simp] theorem mldsaT0BaseScheme_pub (pk : PubKey p prims) (σ : FIPSSignature p prims) :
    (mldsaT0BaseScheme prims O enc S).pub pk σ = .pure (w1Of prims enc pk σ) := rfl

end Lemmas

end GordieHowe.MLDSA
