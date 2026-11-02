/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao

Vendored from VCVio LatticeCrypto/MLDSA/Scheme.lean at commit eb0f6e456a8dffee6a0ba8a2f66ca2a5b50dfd79.
adapted: `PublicKey` and `computeWApprox` dropped; they are imported verbatim from
`LatticeCrypto.MLDSA.Verify`, which replaces the `LatticeCrypto.MLDSA.Primitives` import. Imports
`VCVio.OracleComp.Constructions.SampleableType.Basic` in place of
`VCVio.OracleComp.Constructions.SampleableType` (the kept declarations sample only `Bytes 32`). `identificationScheme` and `identificationSchemeShort`
(and the `VCVio.CryptoFoundations.IdenSchemeWithAbort` import they need) and the IDS types
`SigningState`, `Commitment`, `Response` that only they use dropped: their commitment
samples the mask `y` uniformly over all of `R_q^l`, not over the FIPS 204 mask range
`[-γ₁+1, γ₁]` (ExpandMask, Algorithm 34). The module docstring is shortened to match.
-/

module
public import LatticeCrypto.MLDSA.Verify
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# ML-DSA Key Material

The semantic public and secret keys, deterministic key generation from a seed (FIPS 204
Algorithm 6), the key-validity predicates, and the key-generation algebraic identities. The
concrete FIPS 204 signing algorithm is built on top of this in `LatticeCrypto.MLDSA.Signature`.
(Upstream this file also defines the proof-level identification scheme with aborts; that part is
not vendored.)

## References

- NIST FIPS 204, Algorithms 6, 7 and 8 (for the underlying arithmetic)
-/

@[expose] public section


open OracleComp OracleSpec
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- The semantic secret key: includes the expanded public key material for efficient signing. -/
structure SecretKey where
  rho : Bytes 32
  key : Bytes 32
  tr : Bytes 64
  s1 : RqVec p.l
  s2 : RqVec p.k
  t0 : RqVec p.k

/-! ### Key Generation -/

/-- ML-DSA key generation (Algorithm 6), modeled as a deterministic function from seed.

Given a 32-byte seed `ξ`:
1. Expand to `(ρ, ρ', K)` via `H(ξ ‖ k ‖ l, 128)`
2. Generate matrix `Â = ExpandA(ρ)`
3. Generate secret vectors `(s₁, s₂) = ExpandS(ρ')`
4. Compute `t = A·s₁ + s₂`
5. Split `t` into `(t₁, t₀)` via `Power2Round`
6. Compute `tr = H(pkEncode(ρ, t₁), 64)` -/
def keyGenFromSeed (seed : Bytes 32) : PublicKey p prims × SecretKey p :=
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let aHat := prims.expandA rho
  let (s1, s2) := prims.expandS rhoPrime
  let t := aHat * s1 + s2
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, s1, s2, t0⟩
  (pk, sk)

open Classical in
/-- A key pair is valid when it is honestly generated: there is a seed `ξ` such that
`keyGenFromSeed ξ = (pk, sk)`. This captures the full key-generation relationship
(`t = A·s₁ + s₂`, `(t₁, t₀) = Power2Round(t)`, `s₁, s₂` bounded by `η`), which is what the
completeness and signing-correctness proofs require. The predicate is decidable because the
seed space `Bytes 32` is finite. -/
noncomputable def validKeyPair (pk : PublicKey p prims) (sk : SecretKey p) : Bool :=
  decide (∃ seed : Bytes 32, keyGenFromSeed p prims seed = (pk, sk))

@[simp] theorem validKeyPair_eq_true_iff (pk : PublicKey p prims) (sk : SecretKey p) :
    validKeyPair p prims pk sk = true ↔
      ∃ seed : Bytes 32, keyGenFromSeed p prims seed = (pk, sk) := by
  simp [validKeyPair]

/-! ### Short-secret idealized key validity

The idealized proof-level ML-DSA model samples the short secrets `(s₁, s₂)` directly on the
`η`-bounded box rather than deriving them deterministically from a seed. `validKeyPairShort`
is the ∃-material analogue of `validKeyPair` that such key generators satisfy by construction;
upstream it is the key relation carried by `identificationSchemeShort` and the short-model
security statements. -/

/-- A key pair is *short-valid* when it is built from bounded key material: there are seeds
`ρ`, `K` and `η`-bounded short vectors `(s₁, s₂)` such that the pair is exactly the key
assembled from that material — `t = ExpandA(ρ) · s₁ + s₂` split by `Power2Round` into the
published `t₁` and withheld `t₀`, with `tr = H(ρ, t₁)`. This is the ∃-material analogue of the
∃-seed `validKeyPair`: it captures the algebraic key relationship (`t = A·s₁ + s₂`,
`(t₁, t₀) = Power2Round(t)`, `s₁, s₂` bounded by `η`) without tying the material to a
deterministic seed derivation, so it holds for idealized key generators that sample the
material directly (e.g. `(s₁, s₂)` uniform on the `η`-bounded box). The predicate is decidable
because all material spaces are finite; the instance is supplied classically. -/
noncomputable def validKeyPairShort (pk : PublicKey p prims) (sk : SecretKey p) : Bool :=
  @decide _ <| Classical.propDecidable
    (∃ (rho key : Bytes 32) (s1 : RqVec p.l) (s2 : RqVec p.k),
    polyVecBounded s1 p.eta ∧ polyVecBounded s2 p.eta ∧
    ((⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩,
      ⟨rho, key,
        prims.hashPublicKey rho (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1,
        s1, s2, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).2⟩) :
      PublicKey p prims × SecretKey p) = (pk, sk))

@[simp] theorem validKeyPairShort_eq_true_iff (pk : PublicKey p prims) (sk : SecretKey p) :
    validKeyPairShort p prims pk sk = true ↔
      ∃ (rho key : Bytes 32) (s1 : RqVec p.l) (s2 : RqVec p.k),
        polyVecBounded s1 p.eta ∧ polyVecBounded s2 p.eta ∧
        ((⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩,
          ⟨rho, key,
            prims.hashPublicKey rho (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1,
            s1, s2, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).2⟩) :
          PublicKey p prims × SecretKey p) = (pk, sk) := by
  unfold validKeyPairShort
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-! ### Key Generation Algebraic Properties -/

/-- Keys generated by `keyGenFromSeed` satisfy `validKeyPair`. -/
theorem keyGenFromSeed_validKeyPair (seed : Bytes 32) :
    let (pk, sk) := keyGenFromSeed p prims seed
    validKeyPair p prims pk sk = true := by
  simp only [validKeyPair_eq_true_iff]
  exact ⟨seed, rfl⟩

/-- The key generation algebraic identity: `A·z - c·(t₁·2^d) = A·y - c·s₂ + c·t₀`
when `z = y + c·s₁` and the key pair comes from `keyGenFromSeed`.

This is the core identity underlying both signing correctness and the security proof.
It follows from `t = A·s₁ + s₂` (key generation), `t₁·2^d + t₀ = t` (Power2Round),
and NTT linearity. -/
theorem keyGenFromSeed_wApprox_eq {pk : PublicKey p prims} {sk : SecretKey p}
    (h_laws : Primitives.Laws prims nttOps)
    (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) :
    ∀ (c : Rq) (y : RqVec p.l),
      computeWApprox p prims (prims.expandA pk.rho) c (y + c • sk.s1) pk.t1 =
      (prims.expandA pk.rho) * y - c • sk.s2 + c • sk.t0 := by
  intro c y
  have := h_laws.transform
  let laws := h_laws.transform
  set aHat := prims.expandA pk.rho
  simp only [computeWApprox]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_add, Vector.getElem_sub,
    nttOps.hatVec_add, nttOps.unhatVec_sub, nttOps.matVecMul_add, nttOps.unhatVec_add]
  have h_kg : prims.power2RoundShiftVec pk.t1 + sk.t0 = aHat * sk.s1 + sk.s2 := by
    simp only [keyGenFromSeed, Prod.mk.injEq] at hkeygen
    obtain ⟨hpk, hsk⟩ := hkeygen
    have hrho  := congr_arg PublicKey.rho hpk.symm
    have hs1   := congr_arg SecretKey.s1 hsk.symm
    have hs2   := congr_arg SecretKey.s2 hsk.symm
    have haHat : aHat = prims.expandA (prims.expandSeed seed).1 := by simp [aHat, hrho]
    rw [show pk.t1 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).1 from by
          rw [hs1, hs2, haHat]; exact congr_arg PublicKey.t1 hpk.symm,
        show sk.t0 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).2 from by
          rw [hs1, hs2, haHat]; exact congr_arg SecretKey.t0 hsk.symm]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_add, Primitives.power2RoundShiftVec, Primitives.power2RoundVec,
      Vector.map_map, Vector.getElem_map, Function.comp]
    exact h_laws.power2Round_decomp _
  have hAs1_hat : nttOps.matVecMul aHat (nttOps.hatVec sk.s1) =
      nttOps.hatVec (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2) := by
    rw [h_kg]
    refine Vector.ext fun j hj => ?_
    simp only [hatVec, HMul.hMul, coeffMatVecMul, unhatVec, matVecMul,
               Vector.getElem_map, Vector.getElem_sub, Vector.getElem_add]
    have hcancel : (fromHat (dot nttOps aHat[j] (Vector.map toHat sk.s1)) : Rq) +
        sk.s2[j] - sk.s2[j] = fromHat (dot nttOps aHat[j] (Vector.map toHat sk.s1)) := by
      abel
    rw [hcancel, laws.toHat_fromHat]
  have hMatScalarComm : nttOps.matVecMul aHat (nttOps.hatVec (c • sk.s1)) =
      nttOps.scalarVecMul (toHat c) (nttOps.matVecMul aHat (nttOps.hatVec sk.s1)) := by
    have hNTTSmul : nttOps.hatVec (c • sk.s1) =
        nttOps.scalarVecMul (toHat c) (nttOps.hatVec sk.s1) := by
      refine Vector.ext fun j hj => ?_
      simp only [hatVec, scalarVecMul, Vector.getElem_map]
      change nttOps.toHat (nttOps.coeffScalarVecMul c sk.s1)[j] = _
      simp only [coeffScalarVecMul, unhatVec, scalarVecMul, hatVec,
                 Vector.map_map, Vector.getElem_map, Function.comp_apply, laws.toHat_fromHat]
    rw [hNTTSmul]
    refine Vector.ext fun j hj => ?_
    simp only [matVecMul, scalarVecMul, Vector.getElem_map]
    exact nttOps.dot_scalar_right (toHat c) _ _
  simp only [hMatScalarComm, hAs1_hat]
  change (aHat * y)[i] +
      (nttOps.coeffScalarVecMul c (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2))[i] -
      (nttOps.coeffScalarVecMul c (prims.power2RoundShiftVec pk.t1))[i] =
      (aHat * y)[i] -
      (nttOps.coeffScalarVecMul c sk.s2)[i] + (nttOps.coeffScalarVecMul c sk.t0)[i]
  simp only [nttOps.coeffScalarVecMul_sub, nttOps.coeffScalarVecMul_add,
             Vector.getElem_sub, Vector.getElem_add]
  abel

end MLDSA
