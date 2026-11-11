-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.RingSigner
public import GordieHowe.Applications.MLDSA.Signing.SampleInBallShape
public import GordieHowe.Applications.MLDSA.Spec.ExpandS
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# ML-DSA keys with `t₀` published

* `PubKeyOf`, `PubKey`, `pubPk`, `pubTr`: a published ML-DSA key `(ρ, t₁, t₀)` (FIPS 204 §5.1
  public key `(ρ, t₁)` with `t₀`, which need not be secret, §6.1), its FIPS 204 public key and its
  hash `tr = H(pkEncode(ρ, t₁))`.
* `sigEquiv`: the FIPS 204 signature as a triple `(c̃, z, h)`, with its finiteness, decidable
  equality and a default.
* `concreteEnc`, `concreteEnc_highBitsVec`, `verifyLaws_concrete`: the concrete encoding of
  commitments as bucket vectors, coherent with `bucketsOf`, and the verification laws of the
  concrete primitives, at every approved parameter set; `signingLaws_concreteKeyGen`,
  `verifyLaws_concreteKeyGen`, `concreteEnc_highBitsVec_keyGen`: the same with the FIPS 204
  `ExpandS` (`concretePrimitivesKeyGen`).
* `keyGen`, `keyGenFromSeed_rho`, `keyGenFromSeed_tr`: key generation with `t₀` published (FIPS
  204 Algorithm 6).
* `withExpandA`, `idealSecretKey`, `keyGen_withExpandA`, `SigningLaws.withExpandA`,
  `VerifyLaws.withExpandA`: the primitives with `ExpandA` replaced by `G`, the secret key
  assembled from key material, key generation at them, and the laws, which do not read `ExpandA`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA PMF Finset
open scoped ENNReal BigOperators

variable {p : Params} (prims : Primitives p)

/-- **A published ML-DSA key with `k` rows of `t₁` coefficients in `P`**: `(ρ, t₁, t₀)`. A named
type, so instance search stops at the name: the `BEq` of keys is the one of their decidable
equality, the instance generic constructions over a types record use. -/
def PubKeyOf (P : Type) (k : ℕ) : Type := Bytes 32 × Vector P k × RqVec k

instance {P : Type} [DecidableEq P] {k : ℕ} : DecidableEq (PubKeyOf P k) :=
  inferInstanceAs (DecidableEq (Bytes 32 × Vector P k × RqVec k))

instance {P : Type} [Fintype P] {k : ℕ} : Fintype (PubKeyOf P k) :=
  inferInstanceAs (Fintype (Bytes 32 × Vector P k × RqVec k))

instance {P : Type} [Nonempty P] {k : ℕ} : Nonempty (PubKeyOf P k) :=
  inferInstanceAs (Nonempty (Bytes 32 × Vector P k × RqVec k))

/-- **A published ML-DSA key**: `(ρ, t₁, t₀)` (FIPS 204 §5.1 public key `(ρ, t₁)` with `t₀`, which
need not be secret, §6.1). -/
abbrev PubKey (p : Params) (prims : Primitives p) : Type := PubKeyOf prims.Power2High p.k

/-- The FIPS 204 public key `(ρ, t₁)` of a published key. -/
def pubPk (x : PubKey p prims) : PublicKey p prims := ⟨x.1, x.2.1⟩

/-- The hash `tr = H(pkEncode(ρ, t₁))` of a published key (FIPS 204 Algorithm 8 line 6). -/
def pubTr (x : PubKey p prims) : Bytes 64 := prims.hashPublicKey x.1 x.2.1

/-- The FIPS 204 signature as a triple. -/
def sigEquiv : FIPSSignature p prims ≃ CommitHashBytes p × RqVec p.l × Vector prims.Hint p.k where
  toFun s := (s.cTilde, s.z, s.h)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype prims.Hint] : Fintype (FIPSSignature p prims) :=
  Fintype.ofEquiv _ (sigEquiv prims).symm

instance instDecEqFIPSSignature [DecidableEq prims.Hint] : DecidableEq (FIPSSignature p prims) :=
  (sigEquiv prims).decidableEq

instance [Inhabited prims.Hint] : Inhabited (FIPSSignature p prims) :=
  ⟨⟨Vector.replicate _ 0, 0, Vector.replicate _ default⟩⟩

/-! ### The concrete primitives -/

section Concrete

open _root_.MLDSA.Concrete

attribute [local instance] concreteNTTRingOps

/-- **The concrete encoding of commitments as bucket vectors**: each coefficient of
`w₁ ∈ R_q^k` (the concrete `HighBits` representative, FIPS 204 Algorithm 37) as its residue. -/
def concreteEnc (p : Params) [NeZero (bucketCount p)]
    (w : Vector (GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen p).High p.k) : BucketVec p :=
  fun x => Fin.ofNat _ ((w.get x.1).get x.2).val

/-- **The concrete encoding is coherent with `bucketsOf`**, at every approved parameter set. -/
theorem concreteEnc_highBitsVec {p : Params} [NeZero (bucketCount p)] (hp : p.isApproved)
    (w : RqVec p.k) :
    concreteEnc p ((GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen p).highBitsVec w) =
      bucketsOf (rqVecCoeffs w) := by
  have hsp := SigningParams.of_isApproved hp
  funext x
  have hlt := highBitsCoeff_lt_bucketCount hsp (rqVecCoeffs w x)
  have hq : bucketCount p < modulus := by
    unfold bucketCount
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num [modulus])
  simp only [concreteEnc, bucketsOf, Primitives.highBitsVec,
    GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen, concretePrimitives, highBits, Vector.get_map,
    Vector.get_ofFn]
  congr 1
  exact ZMod.val_natCast_of_lt (lt_trans hlt hq)

/-- **The concrete primitives satisfy the verification laws** at every approved parameter set. -/
theorem verifyLaws_concrete {p : Params} (hp : p.isApproved) :
    VerifyLaws (concretePrimitives p) (nttOps := concreteNTTRingOps) where
  transform := concreteNTTRingLaws
  power2Round_decomp := concretePower2Round_high_low_decomp
  useHint_makeHint z r hz := concreteRounding_useHint_correct_of_isApproved p hp z r
    (by rwa [polyNorm_eq_cInfNorm] at hz)

end Concrete

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]
  {Msg : Type} [Fintype Msg] [DecidableEq Msg]

variable [Inhabited prims.Hint] [Fintype prims.Hint]

/-- **ML-DSA key generation with `t₀` published** (FIPS 204 Algorithm 6, `keyGenFromSeed`): the
published key `(ρ, t₁, t₀)` and the secret key of a seed. -/
def keyGen (seed : Bytes 32) : PubKey p prims × SecretKey p :=
  (((keyGenFromSeed p prims seed).1.rho, (keyGenFromSeed p prims seed).1.t1,
    (keyGenFromSeed p prims seed).2.t0), (keyGenFromSeed p prims seed).2)

/-- The secret key's `ρ` is the public key's. -/
theorem keyGenFromSeed_rho (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).2.rho = (keyGenFromSeed p prims seed).1.rho := rfl

/-- The secret key's `tr` is `H(pkEncode(ρ, t₁))`. -/
theorem keyGenFromSeed_tr (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).2.tr =
      prims.hashPublicKey (keyGenFromSeed p prims seed).1.rho (keyGenFromSeed p prims seed).1.t1 :=
  rfl

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [DecidableEq prims.Hint]

section Assembly

variable (N : ℕ) (βmin : ℚ≥0) (reps tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) {n : ℕ}

section UniformKeys

open LatticeCrypto TransformOps

/-- **The primitives with `ExpandA` replaced by `G`**: the primitives of the game in which
`ExpandA` (FIPS 204 Algorithm 32) is a random oracle `G`. -/
abbrev withExpandA (G : Bytes 32 → TqMatrix p.k p.l) : Primitives p :=
  { prims with expandA := G }

/-- **The secret key assembled from key material** (FIPS 204 Algorithm 6 lines 5-9, with the
matrix `Â` in place of `ExpandA(ρ)`; the assembly of `validKeyPairShort`): `t = Â·s₁ + s₂` split
by `Power2Round` into `(t₁, t₀)`, and `tr = H(pkEncode(ρ, t₁))`. -/
def idealSecretKey (rho key : Bytes 32) (aHat : TqMatrix p.k p.l) (s : RqVec p.l × RqVec p.k) :
    SecretKey p :=
  ⟨rho, key, prims.hashPublicKey rho (prims.power2RoundVec (aHat * s.1 + s.2)).1, s.1, s.2,
    (prims.power2RoundVec (aHat * s.1 + s.2)).2⟩

/-- **Key generation with `ExpandA := G`** is the key of `ρ`, `K` from `expandSeed`, the matrix
`G ρ`, and `(s₁, s₂) = ExpandS(ρ')`. -/
theorem keyGen_withExpandA (G : Bytes 32 → TqMatrix p.k p.l) (seed : Bytes 32) :
    (keyGen (withExpandA prims G) seed).2 =
      idealSecretKey prims (prims.expandSeed seed).1 (prims.expandSeed seed).2.2
        (G (prims.expandSeed seed).1) (prims.expandS (prims.expandSeed seed).2.1) :=
  rfl

/-- The signing laws do not read `ExpandA`. -/
theorem SigningLaws.withExpandA (h : SigningLaws prims) (G : Bytes 32 → TqMatrix p.k p.l) :
    SigningLaws (withExpandA prims G) :=
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

/-- The verification laws do not read `ExpandA`. -/
theorem VerifyLaws.withExpandA (h : VerifyLaws prims) (G : Bytes 32 → TqMatrix p.k p.l) :
    VerifyLaws (withExpandA prims G) :=
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩

end UniformKeys

end Assembly

end GordieHowe.MLDSA

/-! ### The concrete primitives with the FIPS 204 `ExpandS` -/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

/-- **The concrete primitives with the FIPS 204 `ExpandS` satisfy the signing laws**: the fields
of `signingLaws_concrete`, which do not read `expandS`. -/
theorem signingLaws_concreteKeyGen (p : Params) (hp : p.isApproved) :
    SigningLaws (concretePrimitivesKeyGen p) :=
  let h := signingLaws_concrete p hp
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

/-- **The concrete primitives with the FIPS 204 `ExpandS` satisfy the verification laws**: the
fields of `verifyLaws_concrete`, which do not read `expandS`. -/
theorem verifyLaws_concreteKeyGen {p : Params} (hp : p.isApproved) :
    VerifyLaws (concretePrimitivesKeyGen p) (nttOps := concreteNTTRingOps) :=
  let h := verifyLaws_concrete hp
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩

/-- **The concrete encoding is coherent with `bucketsOf`** at the primitives with the FIPS 204
`ExpandS`, at every approved parameter set (`concreteEnc_highBitsVec`). -/
theorem concreteEnc_highBitsVec_keyGen {p : Params} [NeZero (bucketCount p)] (hp : p.isApproved)
    (w : RqVec p.k) :
    concreteEnc p ((GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen p).highBitsVec w) =
      bucketsOf (rqVecCoeffs w) :=
  concreteEnc_highBitsVec hp w

end GordieHowe.MLDSA
