-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Assumptions
public import GordieHowe.Applications.MLDSA.Flattened.Core.Attempt
public import GordieHowe.Applications.MLDSA.Signing.Cutoff
public import GordieHowe.Model.Signature.RejectionRelayCount

public section

/-!
# Unforgeability of the flattened signer

The flattened signer with the cut-off `cut` and the keep factor `g` as a single signer: one attempt
is one call of hedged FIPS 204 signing (`stdProg` at one nonce), kept by the public coin
`u < D · min(1, cut(c̃) / aw) · g(w₁, c̃, z)`, with `aw` the acceptance weight of the signer's
published `t₀` at the recomputed commitment `w₁` and the signature's `c̃`, and `z` the signature's
response. The keep decision reads the signature and the published key only, never `y` or the
secret key.

* `flatRejection`: the signer as a rejection form (`Signature.CtxRejection`) on ML-DSA with `t₀`
  published (`mldsaT0BaseScheme` at one call of hedged signing), with no check and every message
  admitted; `flatOracle`: its signing oracle with `k` attempts (`CtxRejection.oracle`).
* `muEufProbWithin_flat_le_relay`: the MU-EUF-CMA^corr game of `flatOracle` is bounded by the
  game of the standard signer, one call of hedged FIPS 204 signing with public keys
  `(ρ, t₁, t₀)` (`CtxRejection.muEufProbWithin_oracle_le_relay`).
* `muEufProbWithin_flat_le_of_t0`: **EUF-CMA of the flattened signer for every cut-off and keep
  factor** from the named assumption `MLDSAT0MUEufCmaWithin` on that game.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA GordieHowe.Quantum GordieHowe.RingSignature GordieHowe.Signature
open scoped ENNReal

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type}

section Keep

variable (prims : Primitives p) [nttOps : NTTRingOps] (cut : Cutoff p)
  (enc : Vector prims.High p.k → BucketVec p) (g : KeepFactor p (RqVec p.l))

/-- **The flattened keep weight of a signature** at a published key: `min(1, cut(c̃) / aw) · g`,
with `aw` the acceptance weight of the key's `t₀` at the recomputed commitment `w₁` and the
signature's `c̃`, and `g` read at `(w₁, c̃, z)`. -/
noncomputable def flatKeepWeight (pk : PubKey p prims) (σ : FIPSSignature p prims) : ℝ≥0∞ :=
  (NNRat.minOneDiv (cut.val σ.cTilde) (t0Weight prims pk.2.2 (w1Of prims enc pk σ, σ.cTilde)) :
    ℝ≥0∞) * g.val (w1Of prims enc pk σ, σ.cTilde, σ.z)

/-- **The flattened keep weight as a rational**, the value the keep decision computes:
`min(1, cut(c̃) / aw) · g` with `g`'s rational value (`KeepFactor.qval`). -/
def flatKeepWeightQ (pk : PubKey p prims) (σ : FIPSSignature p prims) : ℚ≥0 :=
  NNRat.minOneDiv (cut.val σ.cTilde) (t0Weight prims pk.2.2 (w1Of prims enc pk σ, σ.cTilde)) *
    g.qval (w1Of prims enc pk σ, σ.cTilde, σ.z)

/-- The rational keep weight in `ℝ≥0∞` is `flatKeepWeight`. -/
theorem coe_flatKeepWeightQ (pk : PubKey p prims) (σ : FIPSSignature p prims) :
    (flatKeepWeightQ prims cut enc g pk σ : ℝ≥0∞) = flatKeepWeight prims cut enc g pk σ := by
  rw [flatKeepWeightQ, flatKeepWeight, ENNReal.nnratCast_mul, g.val_eq]

end Keep

section Signer

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (src : MaskSource X Y p T Msg) (O : MLDSAOracles X Y p Msg)
  (cut : Cutoff p) (D : ℕ) (enc : Vector prims.High p.k → BucketVec p)
  (g : KeepFactor p (RqVec p.l))

/-- **The flattened signer as a rejection form** on ML-DSA with `t₀` published at one call of
hedged FIPS 204 signing: standard coins the nonce, keep coins `Fin D`, the standard signer one call
of hedged FIPS 204 signing (`stdProg` at one nonce), no check, the keep decision at the public key
`pk` on the signature `σ` with the coin `u` the comparison `u < D · flatKeepWeightQ pk σ` on
rationals, with no query; every message admitted, its context the public key and its base message
itself. -/
@[expose, reducible] def flatRejection :
    CtxRejection (mldsaT0BaseScheme prims O enc (T0Signer.hedged src O)) Msg (PubKey p prims) where
  StdCoins := src.Rnd
  KeepCoins := Fin D
  qStd := 1 + T * src.qr + T
  std sk m r := stdProg prims src O 1 sk m fun _ => r
  std_queries sk m r := stdProg_queries prims src O 1 sk m fun _ => r
  qCheck := 0
  check _ := .pure true
  check_queries _ := OracleProg.QueriesLE.pure _ _
  qKeep := 0
  keep pk σ u := .pure (decide (((u : ℕ) : ℚ≥0) < D * flatKeepWeightQ prims cut enc g pk σ))
  keep_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  adm _ _ := True
  admDec _ _ := instDecidableTrue
  ctx pk _ := pk
  bmsg m := m

/-- The standard signer of `flatRejection` is one call of hedged FIPS 204 signing. -/
@[simp] theorem flatRejection_std (sk : SecretKey p) (m : Msg) (r : src.Rnd) :
    (flatRejection prims src O cut D enc g).std sk m r =
      stdProg prims src O 1 sk m fun _ => r := rfl

/-- The check of `flatRejection` passes every context, with no query. -/
@[simp] theorem flatRejection_check (pk : PubKey p prims) :
    (flatRejection prims src O cut D enc g).check pk = .pure true := rfl

/-- The keep decision of `flatRejection` is the comparison `u < D · flatKeepWeightQ pk σ`. -/
@[simp] theorem flatRejection_keep (pk : PubKey p prims) (σ : FIPSSignature p prims)
    (u : Fin D) :
    (flatRejection prims src O cut D enc g).keep pk σ u =
      .pure (decide (((u : ℕ) : ℚ≥0) < D * flatKeepWeightQ prims cut enc g pk σ)) := rfl

/-- **The flattened signer with `k` attempts** as a signing oracle of ML-DSA with `t₀` published
(`CtxRejection.oracle` of `flatRejection`): on a message `m` by the key pair `(pk, sk)`, with the
coins `cs j = (r_j, u_j)` of attempt `j < k`, it runs hedged FIPS 204 signing of `m` under `sk` at
the nonce `r_j` (`stdProg` at one nonce) for `j = 0, 1, …` and returns the first signature `σ` with
`u_j < D · flatKeepWeightQ pk σ` (compared as rationals, `u_j : Fin D`), and `none` if no attempt
yields a kept signature. -/
abbrev flatOracle (k : ℕ) : SignOracle (mldsaT0BaseScheme prims O enc (T0Signer.hedged src O)) :=
  (flatRejection prims src O cut D enc g).oracle k

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] [Fintype src.Rnd] [DecidableEq src.Rnd]
  [Nonempty src.Rnd] [NeZero D] [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X]
  [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t n : ℕ} (k : ℕ)

/-- **MU-EUF-CMA^corr of the flattened signer from the standard call game**: every adversary `A`
against the flattened signer with `k` attempts, at most `Qs` signing and corruption requests among
`Q`, wins with probability at most that of the relayed adversary against one call of hedged FIPS
204 signing with public keys `(ρ, t₁, t₀)`, with `k Q` requests and `k Qs` signing and corruption
requests (`CtxRejection.muEufProbWithin_oracle_le_relay`). -/
theorem muEufProbWithin_flat_le_relay (hk : 0 < k) (i₀ : Fin n)
    (A : MUAdversary (flatOracle prims src O cut D enc g k) n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin ((flatRejection prims src O cut D enc g).relayAdversary k n hk i₀
        Sum.inl_injective A Q) (k * Q) (k * Qs) :=
  CtxRejection.muEufProbWithin_oracle_le_relay hk i₀ A Q Qs

/-- **EUF-CMA of the flattened signer from EUF-CMA of ML-DSA with `t₀` published**, for every
cut-off and keep factor: if the standard call game with `k Q` requests and `k Qs` signing and
corruption requests is `ε`-hard for a class `𝒜` containing the relayed adversary
(`MLDSAT0MUEufCmaWithin`, the named assumption), every adversary against the flattened signer with
`k` attempts has MU-EUF-CMA^corr success probability at most `ε` with at most `Qs` signing and
corruption requests among `Q` (`muEufProbWithin_flat_le_relay`). -/
theorem muEufProbWithin_flat_le_of_t0 (hk : 0 < k) (i₀ : Fin n)
    (A : MUAdversary (flatOracle prims src O cut D enc g k) n V t) (Q Qs : ℕ)
    {𝒜 : Set (MUAdversary (flatRejection prims src O cut D enc g).stdOracle n V
      (t + Q * ((flatRejection prims src O cut D enc g).qCheck +
        k * (flatRejection prims src O cut D enc g).qKeep)))}
    {ε : ℝ≥0∞} (hε : MLDSAT0MUEufCmaWithin 𝒜 (k * Q) (k * Qs) ε)
    (hmem : (flatRejection prims src O cut D enc g).relayAdversary k n hk i₀ Sum.inl_injective A Q
      ∈ 𝒜) :
    muEufProbWithin A Q Qs ≤ ε :=
  (muEufProbWithin_flat_le_relay prims src O cut D enc g k hk i₀ A Q Qs).trans
    (hε.le_muEufProbWithin hmem)

end Signer

end GordieHowe.MLDSA
