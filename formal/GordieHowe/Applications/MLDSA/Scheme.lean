-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.PublishedKey
public import GordieHowe.Model.Signature.Scheme
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# ML-DSA as a signature scheme

- `publicKeyEquiv`: an ML-DSA public key `(ρ, t₁)` as a pair, with its finiteness and decidable
  equality.
- `boundedOk p ρ c̃`: the bounded-sampling acceptance check of FIPS 204 Appendix C at the concrete
  SHAKE-based `ExpandA` and `SampleInBall`.
- `fipsSignWith`: the hedged FIPS 204 signer (Algorithm 7) at the coins `rnd`, with at most
  `maxAttempts` attempts and the bounded samplers; `fipsAttemptCommit`,
  `cTilde_of_fipsSignAttempt`, `exists_attempt_of_fipsSignWith`, `boundedOk_of_fipsSignWith`: a
  signature is an attempt's signature carrying the attempt's commitment hash and passing
  `boundedOk`.
- `fipsVerify_of_fipsSignWith`, `bverify_of_fipsSignWith`: a signature of `fipsSignWith` verifies
  by FIPS 204 (Algorithm 8) under the key generated with it, and passes `boundedOk && fipsVerify`,
  given the signing and verification laws and `‖s₂‖∞ ≤ η`.
- `mldsaSchemeT`, `mldsaBaseScheme`: the ML-DSA signature scheme (`Signature.BaseScheme`): keys
  from a seed (Algorithm 6), the signer `fipsSignWith`, verification `boundedOk && fipsVerify`, no
  public value, no oracle read.
- `SigningLaws.withSigning`, `VerifyLaws.withSigning`, `keyGenFromSeed_s2_withSigning`: the laws
  and the generated `s₂` do not read `ExpandMask` (nor, for the laws, `ExpandS`).
- `w1Of`, `w1Of_attemptOutput`: the commitment `w₁ = enc(UseHint(h, Â·z − c·t₁·2^d))` recomputed
  from a published key and a signature (Algorithm 8, lines 9–10), and for an accepted attempt of
  an honest key it is the attempt's commitment.
-/

namespace GordieHowe.MLDSA

variable {X Y : Type} {N : ℕ}

section MLDSA

open _root_.MLDSA LatticeCrypto TransformOps

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- An ML-DSA public key `(ρ, t₁)` as a pair. -/
def publicKeyEquiv : PublicKey p prims ≃ Bytes 32 × Vector prims.Power2High p.k where
  toFun pk := (pk.rho, pk.t1)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype prims.Power2High] : Fintype (PublicKey p prims) :=
  Fintype.ofEquiv _ (publicKeyEquiv p prims).symm

instance [DecidableEq prims.Power2High] : DecidableEq (PublicKey p prims) :=
  (publicKeyEquiv p prims).decidableEq

/-- **The bounded-sampling acceptance check of FIPS 204 Appendix C** at the concrete primitives:
`ExpandA(ρ)` finishes within the vendored bound of every `RejNTTPoly` call (`expandA?`) and
`SampleInBall(c̃)` within its `272` SHAKE256 bytes (`sampleInBallPoly?`). The check is that of
the concrete SHAKE-based samplers at every parameter set, whatever primitives the signer uses. -/
def boundedOk (p : Params) (rho : Bytes 32) (cTilde : CommitHashBytes p) : Bool :=
  (Concrete.expandA? p rho).isSome && (Concrete.sampleInBallPoly? p cTilde).isSome

/-- **The commitment hash of a signing attempt** (FIPS 204 Algorithm 7, lines 11–15): with
`y = ExpandMask(ρ'', κ)`, `c̃ = H(µ ‖ w1Encode(HighBits(Â·y)))`, the commitment hash
`fipsSignAttempt` computes and outputs. -/
def fipsAttemptCommit (aHat : TqMatrix p.k p.l) (mu : Bytes 64) (rhoDoublePrime : Bytes 64)
    (kappa : ℕ) : CommitHashBytes p :=
  prims.hashCommitment mu (prims.w1Encode (prims.highBitsVec (aHat * prims.expandMask rhoDoublePrime
    kappa)))

/-- **A signature of an attempt carries the attempt's commitment hash.** -/
theorem cTilde_of_fipsSignAttempt {sk : SecretKey p} {aHat : TqMatrix p.k p.l} {mu rhoDoublePrime :
    Bytes 64} {kappa : ℕ} {σ : FIPSSignature p prims}
    (h : fipsSignAttempt p prims sk aHat mu rhoDoublePrime kappa = some σ) :
    σ.cTilde = fipsAttemptCommit p prims aHat mu rhoDoublePrime kappa := by
  unfold fipsSignAttempt at h
  dsimp only at h
  split_ifs at h
  rw [Option.some.injEq] at h
  subst h
  rfl

/-- **The hedged FIPS 204 signer** (Algorithm 7) at the coins `rnd`, with the bounded `ExpandA` and
`SampleInBall` of FIPS 204 Appendix C: `µ = H(tr ‖ M)`, `ρ'' = H(K ‖ rnd ‖ µ)`; abort (`none`)
when the bounded `ExpandA(ρ)` runs out of bytes; then at most `maxAttempts` attempts of the
vendored `fipsSignAttempt` (counter `κ = i · l`): an attempt whose bounded `SampleInBall` of its
commitment hash (`fipsAttemptCommit`) runs out of bytes aborts the signer (Appendix C: "return a
constant that represents an error and no other output"), and otherwise the first attempt that is
not rejected is the signature; `none` when every attempt is rejected. -/
def fipsSignWith (maxAttempts : ℕ) (sk : SecretKey p) (msg : List Byte) (rnd : Bytes 32) :
    Option (FIPSSignature p prims) :=
  if (Concrete.expandA? p sk.rho).isSome then
    ((List.range maxAttempts).findSome? fun i =>
      if (Concrete.sampleInBallPoly? p (fipsAttemptCommit p prims (prims.expandA sk.rho)
          (prims.hashMessage sk.tr msg)
          (prims.hashPrivateSeed sk.key rnd (prims.hashMessage sk.tr msg)) (i * p.l))).isSome then
        (fipsSignAttempt p prims sk (prims.expandA sk.rho) (prims.hashMessage sk.tr msg)
          (prims.hashPrivateSeed sk.key rnd (prims.hashMessage sk.tr msg)) (i * p.l)).map some
      else some none).join
  else none

/-- **A signature of the signer is an attempt's signature passing the bounded-sampling check**: it
is the output of `fipsSignAttempt` at some counter `κ = i · l`, and `boundedOk p ρ c̃` holds at the
signer's `ρ`. -/
theorem exists_attempt_of_fipsSignWith {maxAttempts : ℕ} {sk : SecretKey p} {msg : List Byte}
    {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts sk msg rnd = some σ) :
    ∃ i, fipsSignAttempt p prims sk (prims.expandA sk.rho) (prims.hashMessage sk.tr msg)
        (prims.hashPrivateSeed sk.key rnd (prims.hashMessage sk.tr msg)) (i * p.l) = some σ ∧
      boundedOk p sk.rho σ.cTilde = true := by
  unfold fipsSignWith at h
  split_ifs at h with hA
  · rw [Option.join_eq_some_iff] at h
    obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
    split_ifs at hi with hS
    · rw [Option.map_eq_some_iff] at hi
      obtain ⟨σ', hσ', hσσ'⟩ := hi
      cases hσσ'
      refine ⟨i, hσ', ?_⟩
      rw [boundedOk, cTilde_of_fipsSignAttempt p prims hσ', hA, hS, Bool.and_self]
    · simp at hi

/-- **A signature of the signer passes the bounded-sampling check** at the signer's `ρ`. -/
theorem boundedOk_of_fipsSignWith {maxAttempts : ℕ} {sk : SecretKey p} {msg : List Byte}
    {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts sk msg rnd = some σ) :
    boundedOk p sk.rho σ.cTilde = true :=
  (exists_attempt_of_fipsSignWith p prims h).choose_spec.2

/-- The types of `mldsaBaseScheme`: ML-DSA keys from 32-byte seeds, base messages of `len` bytes,
FIPS 204 signatures, no public value, 32-byte signing coins. -/
abbrev mldsaSchemeT (len : ℕ) : Signature.SchemeTypes where
  PK := PublicKey p prims
  SK := SecretKey p
  KeyCoins := Bytes 32
  BMsg := Bytes len
  BSig := FIPSSignature p prims
  Pub := Unit
  Coins := Bytes 32

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint]

/-- **The ML-DSA signature scheme** (FIPS 204) with base messages of `len` bytes: keys from a seed
(`keyGenFromSeed`, Algorithm 6), the hedged FIPS 204 signer `fipsSignWith` on a base message (it
refuses when a bounded sampler runs out of bytes or every attempt is rejected), and FIPS 204
verification (Algorithm 8 with the bounded `ExpandA` and `SampleInBall` of Appendix C): the
bounded-sampling check `boundedOk p ρ c̃` and `fipsVerify`, the shape of the vendored
`MLDSA.Concrete.verify` (`mldsaBaseSigner_bverify_concrete`). Public value `Unit`. No oracle is
read. -/
def mldsaBaseScheme (maxAttempts len : ℕ) :
    Signature.BaseScheme X Y (mldsaSchemeT p prims len) where
  keyGen := keyGenFromSeed p prims
  q := 0
  ssign sk bm rnd := .pure (fipsSignWith p prims maxAttempts sk bm.toList rnd)
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ pk bm σ := boundedOk p pk.rho σ.cTilde && fipsVerify p prims pk bm.toList σ
  qPub := 0
  pub _ _ := .pure ()
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

end MLDSA

section MLDSAFacts

open _root_.MLDSA

variable (p : Params) (prims : Primitives p) [NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]

section Correctness

open GordieHowe.MLDSA LatticeCrypto TransformOps

/-- **A signature of the hedged signer verifies by FIPS 204** (Algorithm 8, `fipsVerify`) under
the key generated with it: for the key `(pk, sk)` of `seed` (Algorithm 6) with `‖s₂‖∞ ≤ η`, every
signature `fipsSignWith` outputs is accepted, given the signing and verification laws. The
argument of the vendored `fipsSign_fipsVerify_correct'` at the kept attempt. -/
theorem fipsVerify_of_fipsSignWith {p : Params} {prims : Primitives p} (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims)
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs2 : polyVecBounded sk.s2 p.eta)
    {maxAttempts : ℕ} {msg : List Byte} {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts sk msg rnd = some σ) :
    fipsVerify p prims pk msg σ = true := by
  have hpk := congrArg Prod.fst hkeygen
  have hsk := congrArg Prod.snd hkeygen
  subst hpk hsk
  obtain ⟨i, hatt, -⟩ := exists_attempt_of_fipsSignWith p prims h
  have hrho : (keyGenFromSeed p prims seed).2.rho = (keyGenFromSeed p prims seed).1.rho := rfl
  rw [hrho] at hatt
  set aHat := prims.expandA (keyGenFromSeed p prims seed).1.rho
  set sk := (keyGenFromSeed p prims seed).2
  set pk := (keyGenFromSeed p prims seed).1
  have htr : sk.tr = prims.hashPublicKey pk.rho pk.t1 := rfl
  set mu := prims.hashMessage sk.tr msg
  set y := prims.expandMask (prims.hashPrivateSeed sk.key rnd mu) (i * p.l)
  set cT := prims.hashCommitment mu (prims.w1Encode (prims.highBitsVec (aHat * y)))
  set c := prims.sampleInBall cT
  unfold fipsSignAttempt at hatt
  dsimp only at hatt
  split_ifs at hatt with h_outer h_inner
  rw [Option.some.injEq] at hatt
  subst hatt
  obtain ⟨hz, hr0⟩ := h_outer
  obtain ⟨hct0, hw⟩ := h_inner
  have hcs2 : polyVecNorm (c • sk.s2) ≤ p.beta :=
    SigningLaws.polyVecNorm_sampleInBall_smul_le prims h_laws cT sk.s2 hs2
  have hrec : prims.useHintVec (prims.makeHintVec (-(c • sk.t0)) (aHat * y - c • sk.s2 + c • sk.t0))
      (computeWApprox p prims aHat c (y + c • sk.s1) pk.t1) = prims.highBitsVec (aHat * y) := by
    rw [hv.wApprox_eq prims (pk := pk) (sk := sk) seed rfl c y]
    refine useHintVec_makeHintVec_eq_highBitsVec p prims hv.useHint_makeHint h_laws.hide_low
      (aHat * y) (c • sk.s2) (c • sk.t0) hct0 hr0 fun j => ?_
    have hj : polyNorm ((c • sk.s2).get j) ≤ p.beta :=
      le_trans (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.s2) j) hcs2
    unfold polyNorm normOps at hj
    simpa [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView,
      LatticeCrypto.cInfNorm] using hj
  unfold fipsVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hz, ?_⟩, hw⟩
  rw [← htr]
  exact congrArg (fun w => prims.hashCommitment mu (prims.w1Encode w)) hrec

/-- **A signature of the hedged signer passes the base verification** of `mldsaBaseSigner`
(`boundedOk p ρ c̃ && fipsVerify`) under the key generated with it: the bounded-sampling check
holds at `pk.ρ = sk.ρ` by the signer's filter (`boundedOk_of_fipsSignWith`), and FIPS 204
verification by `fipsVerify_of_fipsSignWith`. -/
theorem bverify_of_fipsSignWith {p : Params} {prims : Primitives p} (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims)
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGenFromSeed p prims seed).2.s2 p.eta)
    {maxAttempts : ℕ} {msg : List Byte} {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts (keyGenFromSeed p prims seed).2 msg rnd = some σ) :
    (boundedOk p (keyGenFromSeed p prims seed).1.rho σ.cTilde &&
      fipsVerify p prims (keyGenFromSeed p prims seed).1 msg σ) = true := by
  have hrho : (keyGenFromSeed p prims seed).2.rho = (keyGenFromSeed p prims seed).1.rho := rfl
  rw [Bool.and_eq_true, ← hrho]
  exact ⟨boundedOk_of_fipsSignWith p prims h,
    fipsVerify_of_fipsSignWith h_laws hv rfl hs2 h⟩

end Correctness

end MLDSAFacts

section MLDSAConcrete

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec

variable {p : Params}

/-- **The signing laws do not read `ExpandS` or `ExpandMask`**: they hold at
`{P with expandS := eS, expandMask := eM}` when they hold at `P` (stated for an abstract bundle
`P`, so that no concrete primitive is unfolded). -/
theorem _root_.GordieHowe.MLDSA.SigningLaws.withSigning [NTTRingOps] {P : Primitives p}
    (h : SigningLaws P)    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) :
    SigningLaws { P with expandS := eS, expandMask := eM } :=
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

/-- **The verification laws do not read `ExpandS` or `ExpandMask`** (for an abstract bundle
`P`). -/
theorem _root_.GordieHowe.MLDSA.VerifyLaws.withSigning [NTTRingOps] {P : Primitives p}
    (h : VerifyLaws P)    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) :
    VerifyLaws { P with expandS := eS, expandMask := eM } :=
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩

/-- **Key generation does not read `ExpandMask`**: the secret `s₂` generated at
`{P with expandS := eS, expandMask := eM}` is the one generated at `{P with expandS := eS}` (for
an abstract bundle `P`). -/
theorem keyGenFromSeed_s2_withSigning [NTTRingOps] (P : Primitives p)
    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) (seed : Bytes 32) :
    (keyGenFromSeed p { P with expandS := eS, expandMask := eM } seed).2.s2 =
      (keyGenFromSeed p { P with expandS := eS } seed).2.s2 :=
  rfl

end MLDSAConcrete

section W1

open _root_.MLDSA

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  {Msg : Type} {reps : ℕ}

/-- **The recomputed commitment** of a signature `(c̃, z, h)` under a published key `(ρ, t₁, t₀)`:
`w₁ = enc(UseHint(h, Â·z − c·t₁·2^d))` with `Â = ExpandA(ρ)` and `c = SampleInBall(c̃)` (FIPS 204
Algorithm 8, lines 9–10). -/
def w1Of (enc : Vector prims.High p.k → BucketVec p) (pk : PubKey p prims)
    (σ : FIPSSignature p prims) : BucketVec p :=
  enc (prims.useHintVec σ.h (computeWApprox p prims (prims.expandA pk.1)
    (prims.sampleInBall σ.cTilde) σ.z pk.2.1))

end W1

section Law

open _root_.MLDSA

variable {T : ℕ} {Msg : Type} {N reps : ℕ} {p : Params}

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D]

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **The recomputed commitment of an accepted attempt is its commitment** for an honest key with
`‖s₂‖∞ ≤ η`, given the signing and verification laws and a coherent encoding
(`ringVerify_attemptOutput`). -/
theorem w1Of_attemptOutput (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta) (y : MaskBox p)
    (c : CommitHashBytes p)
    (hacc : attemptAccept prims (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho) y c =
      true) :
    w1Of prims enc (keyGen prims seed).1 (attemptOutput prims (keyGen prims seed).2
      (prims.expandA (keyGen prims seed).2.rho) (y, c)) =
      realBuckets (prims.expandA (keyGen prims seed).2.rho) y := by
  have hver := ringVerify_attemptOutput prims h_laws hv henc (seed := seed)
    (pk := (keyGenFromSeed p prims seed).1) (sk := (keyGenFromSeed p prims seed).2) rfl hs2
    (Msg := Unit) (fun _ => c) () y (by simpa only [keyGen, keyGenFromSeed_rho] using hacc)
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at hver
  simpa only [w1Of, keyGen, keyGenFromSeed_rho, pubPk] using hver.1.1.2

end Law

end GordieHowe.MLDSA
