-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.Signature
public import GordieHowe.Applications.MLDSA.Signing.Counting
public import GordieHowe.Foundations.ToMathlib.PMFRejection

@[expose] public section

/-!
# The idealized ML-DSA signing attempt

One attempt of FIPS 204 Algorithm 7 (ML-DSA.Sign_internal, lines 11–30) with the mask `y` and the
commitment hash `c̃` taken as inputs (`idealAttempt`). The vendored `MLDSA.fipsSignAttempt`
computes `y = ExpandMask(ρ'', κ)` and `c̃ = H(μ ‖ w1Encode(HighBits(Â·y)))`; with those inputs
`idealAttempt` is `fipsSignAttempt` by definition (`fipsSignAttempt_eq_idealAttempt`).

The idealization replaces ExpandMask by a uniform draw from its range (`MaskBox`, Algorithm 34:
every coefficient's centered representative in `[-γ₁ + 1, γ₁]`) and `H` by a random oracle, so
that on a fresh query `c̃` is uniform on `CommitHashBytes p` and independent of `y`. This is the
standard idealization of the Fiat–Shamir with aborts signing loop.

* `MaskBox`, `natCard_maskBox`: the mask range has `(2γ₁)^(256 l)` elements.
* `zCheck`, `r0Check`, `ct0Check`, `hintCheck`: the four rejection conditions of lines 23 and 28,
  `signAccept` their conjunction; `idealAttempt_eq_ite`, `idealAttempt_isSome_iff`,
  `idealAttempt_eq_some_iff`: the attempt outputs `(c̃, y + c·s₁, h)` exactly when all four pass.
* `SigningLaws`: the three `Primitives.Laws` fields the signing analysis reads
  (`Primitives.Laws.toSigningLaws`); the theorems below take them as `SigningLaws.*`, with
  `Primitives.Laws` wrappers under the old names.
* `highBitsVec_sub_eq_of_isSome`: on acceptance `HighBits(Â·y - c·s₂) = HighBits(Â·y)`, given the
  primitive laws and `‖s₂‖∞ ≤ η`.
* `smul_eq_coeffScalarVecMul`, `polyVecNorm_challenge_smul_le`, `polyVecNorm_sampleInBall_smul_le`:
  the product `c • s` of Algorithm 7 is `coeffScalarVecMul c s`, of norm at most `τη`.
* `idealAttemptLaw_eq`: the law of one idealized attempt is `PMF.rejectionAttempt` with proposal
  uniform on `MaskBox`, challenge `c̃`, and acceptance `signAccept`, mapped to the signature;
  `idealLoopLaw_eq`: the bounded loop is `PMF.firstSome` of it;
  `acceptedChallenge_apply`: the accepted `c̃` has density proportional to
  `Pr_{y ← MaskBox}[signAccept y c̃]`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA LatticeCrypto TransformOps

/-! ### The mask box -/

/-- Every coefficient's centered representative lies in `[-γ₁ + 1, γ₁]`: the range of
ExpandMask (FIPS 204 Algorithm 34, with BitUnpack of Algorithm 19 giving `γ₁ - b`). -/
def InMaskBox (γ₁ : ℕ) {l : ℕ} (y : RqVec l) : Prop :=
  ∀ j i, -(γ₁ : ℤ) < centeredRepr ((y.get j).get i) ∧ centeredRepr ((y.get j).get i) ≤ γ₁

instance (γ₁ : ℕ) {l : ℕ} : DecidablePred (InMaskBox γ₁ (l := l)) := fun _ => by
  unfold InMaskBox; infer_instance

/-- The masks `y : R_q^l` that ExpandMask can output at parameter set `p` (FIPS 204
Algorithm 34). -/
abbrev MaskBox (p : Params) := {y : RqVec p.l // InMaskBox p.gamma1 y}

/-- One coefficient of the mask box: `2γ₁` residues have centered representative in
`(-γ₁, γ₁]`, when `2γ₁ < q`. -/
theorem card_maskCoeff {γ₁ : ℕ} (hq : 2 * γ₁ < modulus) :
    (Finset.univ.filter fun a : Coeff =>
      -(γ₁ : ℤ) < centeredRepr a ∧ centeredRepr a ≤ γ₁).card = 2 * γ₁ := by
  have hcr : ∀ z : ℤ, -(γ₁ : ℤ) < z → z ≤ γ₁ → centeredRepr ((z : Coeff)) = z := fun z h1 h2 =>
    centeredRepr_intCast_eq_of_natAbs_le z (b := γ₁) (by omega) hq
  have hI : (Finset.Ioc (-(γ₁ : ℤ)) γ₁).card = 2 * γ₁ := by rw [Int.card_Ioc]; omega
  rw [← hI]
  symm
  refine Finset.card_bij (fun z _ => ((z : ℤ) : Coeff)) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_Ioc] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcr z hz.1 hz.2]
    exact hz
  · intro z hz z' hz' h
    simp only [Finset.mem_Ioc] at hz hz'
    have := congrArg centeredRepr h
    rwa [hcr z hz.1 hz.2, hcr z' hz'.1 hz'.2] at this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨centeredRepr a, Finset.mem_Ioc.mpr ha, (centeredRepr_intCast a).symm⟩

/-- **The mask box has `(2γ₁)^(256 l)` elements**, when `2γ₁ < q`. -/
theorem natCard_maskBox {γ₁ l : ℕ} (hq : 2 * γ₁ < modulus) :
    Nat.card {y : RqVec l // InMaskBox γ₁ y} = (2 * γ₁) ^ (ringDegree * l) := by
  refine (natCard_vector_forall (α := Rq) (n := l) (fun _ (p : Rq) => ∀ i,
    -(γ₁ : ℤ) < centeredRepr (p.get i) ∧ centeredRepr (p.get i) ≤ γ₁)).trans ?_
  have hinner : Nat.card {p : Rq // ∀ i,
      -(γ₁ : ℤ) < centeredRepr (p.get i) ∧ centeredRepr (p.get i) ≤ γ₁} =
      (2 * γ₁) ^ ringDegree := by
    refine (natCard_vector_forall (α := Coeff) (n := ringDegree) (fun _ a =>
      -(γ₁ : ℤ) < centeredRepr a ∧ centeredRepr a ≤ γ₁)).trans ?_
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_maskCoeff hq,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [hinner, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- `MaskBox p` has `(2γ₁)^(256 l)` elements, when `2γ₁ < q` (as under `SigningParams p`). -/
theorem card_maskBox {p : Params} (hq : 2 * p.gamma1 < modulus) :
    Fintype.card (MaskBox p) = (2 * p.gamma1) ^ (ringDegree * p.l) := by
  rw [← Nat.card_eq_fintype_card]; exact natCard_maskBox hq

/-- Under `SigningParams p`, `2γ₁ < q`. -/
theorem SigningParams.two_gamma1_lt {p : Params} (hp : SigningParams p) :
    2 * p.gamma1 < modulus := by
  have := hp.gamma1_beta_lt; omega

/-- The zero mask is in the box when `γ₁ > 0`. -/
theorem maskBox_nonempty {p : Params} (hγ : 0 < p.gamma1) : Nonempty (MaskBox p) :=
  ⟨⟨0, fun j i => by
    have : ((0 : RqVec p.l).get j).get i = 0 := by
      simp [Vector.get_eq_getElem]
    rw [this, show centeredRepr (0 : Coeff) = 0 from by
      simpa using (centeredRepr_intCast_eq_of_natAbs_le (q := modulus) 0 (b := 0) le_rfl
        (by decide))]
    omega⟩⟩

/-- **The zero mask is in a nonempty box**: a mask in the box bounds `-γ₁ < c ≤ γ₁` at every
coefficient, so `γ₁ > 0` when there is a coefficient, and the zero coefficient is in range. -/
theorem zero_mem_maskBox {p : Params} [h : Nonempty (MaskBox p)] :
    InMaskBox p.gamma1 (0 : RqVec p.l) := by
  obtain ⟨y, hy⟩ := h
  intro j i
  have h0 : ((0 : RqVec p.l).get j).get i = 0 := by
    simp [Vector.get_eq_getElem]
  rw [h0, show centeredRepr (0 : Coeff) = 0 from by
    simpa using (centeredRepr_intCast_eq_of_natAbs_le (q := modulus) 0 (b := 0) le_rfl
      (by decide))]
  have := hy j i
  omega

/-- **A mask of a nonempty box**, with compiled code: the zero mask (`zero_mem_maskBox`). -/
def maskBoxPoint (p : Params) [Nonempty (MaskBox p)] : MaskBox p :=
  ⟨0, zero_mem_maskBox⟩

/-! ### One attempt with mask and challenge hash given -/

section Attempt

variable {p : Params} (prims : Primitives p) [nttOps : NTTRingOps]

/-- The z-check of FIPS 204 Algorithm 7 line 23: `‖z‖∞ < γ₁ - β`. -/
def zCheck (z : RqVec p.l) : Bool := decide (polyVecNorm z < p.gamma1 - p.beta)

/-- The r0-check of FIPS 204 Algorithm 7 line 23: `‖r₀‖∞ < γ₂ - β`, `r₀ = LowBits(w - cs₂)`. -/
def r0Check (r0 : RqVec p.k) : Bool := decide (polyVecNorm r0 < p.gamma2 - p.beta)

/-- The ct₀-check of FIPS 204 Algorithm 7 line 28: `‖ct₀‖∞ < γ₂`. -/
def ct0Check (ct0 : RqVec p.k) : Bool := decide (polyVecNorm ct0 < p.gamma2)

/-- The hint-count check of FIPS 204 Algorithm 7 line 28: at most `ω` ones in `h`. -/
def hintCheck (h : Vector prims.Hint p.k) : Bool := decide (prims.hintWeight h ≤ p.omega)

/-- The hint `h = MakeHint(-ct₀, w - cs₂ + ct₀)` of FIPS 204 Algorithm 7 line 26, with
`w = Â·y` and `c = SampleInBall(c̃)`. -/
def attemptHint (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) : Vector prims.Hint p.k :=
  prims.makeHintVec (-(prims.sampleInBall cTilde • sk.t0))
    (aHat * y - prims.sampleInBall cTilde • sk.s2 + prims.sampleInBall cTilde • sk.t0)

/-- The four checks of FIPS 204 Algorithm 7 (lines 23 and 28) on the attempt with mask `y` and
commitment hash `c̃`, with `c = SampleInBall(c̃)`. -/
def signAccept (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) : Bool :=
  zCheck (y + prims.sampleInBall cTilde • sk.s1) &&
    r0Check (prims.lowBitsVec (aHat * y - prims.sampleInBall cTilde • sk.s2)) &&
    ct0Check (prims.sampleInBall cTilde • sk.t0) &&
    hintCheck prims (attemptHint prims sk aHat y cTilde)

/-- **One signing attempt with the mask `y` and commitment hash `c̃` given**: the body of FIPS 204
Algorithm 7, lines 11–30, after ExpandMask (line 11) and the hash `c̃ = H(μ ‖ w1Encode(w₁))`
(line 15). It is the body of the vendored `MLDSA.fipsSignAttempt` with `y` and `c̃` as inputs. -/
def idealAttempt (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) : Option (FIPSSignature p prims) :=
  let w := aHat * y
  let c := prims.sampleInBall cTilde
  let cs1 := c • sk.s1
  let cs2 := c • sk.s2
  let z := y + cs1
  let r0 := prims.lowBitsVec (w - cs2)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let ct0 := c • sk.t0
    let h := prims.makeHintVec (-ct0) (w - cs2 + ct0)
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some ⟨cTilde, z, h⟩
    else
      none
  else
    none

/-- **The FIPS 204 attempt is the idealized attempt at `y = ExpandMask(ρ'', κ)` and
`c̃ = H(μ ‖ w1Encode(HighBits(Â·y)))`.** -/
theorem fipsSignAttempt_eq_idealAttempt (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    fipsSignAttempt p prims sk aHat mu rhoDoublePrime kappa =
      idealAttempt prims sk aHat (prims.expandMask rhoDoublePrime kappa)
        (prims.hashCommitment mu (prims.w1Encode
          (prims.highBitsVec (aHat * prims.expandMask rhoDoublePrime kappa)))) :=
  rfl

/-- The idealized attempt outputs `(c̃, y + c·s₁, h)` if the four checks pass, else rejects. -/
theorem idealAttempt_eq_ite (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    idealAttempt prims sk aHat y cTilde =
      if signAccept prims sk aHat y cTilde then
        some ⟨cTilde, y + prims.sampleInBall cTilde • sk.s1, attemptHint prims sk aHat y cTilde⟩
      else none := by
  unfold idealAttempt signAccept zCheck r0Check ct0Check hintCheck attemptHint
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> simp_all

/-- **An attempt accepts exactly when the four checks pass.** -/
theorem idealAttempt_isSome_iff (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    (idealAttempt prims sk aHat y cTilde).isSome ↔
      zCheck (y + prims.sampleInBall cTilde • sk.s1) ∧
        r0Check (prims.lowBitsVec (aHat * y - prims.sampleInBall cTilde • sk.s2)) ∧
        ct0Check (prims.sampleInBall cTilde • sk.t0) ∧
        hintCheck prims (attemptHint prims sk aHat y cTilde) := by
  rw [idealAttempt_eq_ite]
  split_ifs with h <;> simp_all [signAccept, and_assoc]

/-- On acceptance the attempt outputs `(c̃, y + c·s₁, h)`. -/
theorem idealAttempt_eq_some_iff (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) (sig : FIPSSignature p prims) :
    idealAttempt prims sk aHat y cTilde = some sig ↔
      signAccept prims sk aHat y cTilde ∧
        sig = ⟨cTilde, y + prims.sampleInBall cTilde • sk.s1, attemptHint prims sk aHat y cTilde⟩ := by
  rw [idealAttempt_eq_ite]
  split_ifs with h <;> simp [h, eq_comm]

/-! ### The challenge product -/

/-- The product `c • s` of FIPS 204 Algorithm 7 is the vendored coefficient-domain
`coeffScalarVecMul c s`. -/
theorem smul_eq_coeffScalarVecMul {k : ℕ} (c : Rq) (s : RqVec k) :
    c • s = nttOps.coeffScalarVecMul c s :=
  rfl

/-- **The challenge product bound**: a challenge with at most `τ` nonzero coefficients, each of
centered absolute value at most `1`, times `s` with `‖s‖∞ ≤ η` has `‖c • s‖∞ ≤ τη`, given the
transform laws. -/
theorem polyVecNorm_challenge_smul_le {τ η k : ℕ} (h_ntt : NTTRingLaws nttOps) (c : Rq)
    (s : RqVec k) (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (hs : polyVecNorm s ≤ η) : polyVecNorm (c • s) ≤ τ * η :=
  haveI := h_ntt
  norm_challenge_coeffScalarVecMul_le nttOps c s hc1 hcw hs

/-- **The primitive laws the signing analysis reads**: the transform laws, `hide_low` and the
challenge product bound, three fields of `Primitives.Laws` (`Primitives.Laws.toSigningLaws`). -/
structure SigningLaws : Prop where
  /-- Generic transform laws for the instantiated ring backend. -/
  transform : NTTRingLaws nttOps
  /-- Adding `s` with `‖s‖∞ ≤ b` keeps `HighBits(r)` when `‖LowBits(r)‖∞ + b < γ₂`. -/
  hide_low : ∀ (r s : Rq) (b : ℕ), polyNorm s ≤ b → polyNorm (prims.lowBits r) + b < p.gamma2 →
    prims.highBits (r + s) = prims.highBits r
  /-- `‖SampleInBall(c̃) · s‖∞ ≤ β` for `‖s‖∞ ≤ η`. -/
  sampleInBall_smul_bound : ∀ (cTilde : CommitHashBytes p) {k : ℕ} (s : RqVec k),
    polyVecBounded s p.eta →
    polyVecNorm (nttOps.coeffScalarVecMul (prims.sampleInBall cTilde) s) ≤ p.beta

/-- The full primitive laws give the signing laws. -/
theorem _root_.MLDSA.Primitives.Laws.toSigningLaws {prims : Primitives p}
    (h : Primitives.Laws prims nttOps) : SigningLaws prims where
  transform := h.transform
  hide_low := h.hide_low
  sampleInBall_smul_bound := h.sampleInBall_smul_bound

/-- `‖SampleInBall(c̃) • s‖∞ ≤ β` for `‖s‖∞ ≤ η`, from the signing laws. -/
theorem SigningLaws.polyVecNorm_sampleInBall_smul_le (h_laws : SigningLaws prims)
    (cTilde : CommitHashBytes p) {k : ℕ} (s : RqVec k) (hs : polyVecBounded s p.eta) :
    polyVecNorm (prims.sampleInBall cTilde • s) ≤ p.beta :=
  h_laws.sampleInBall_smul_bound cTilde s hs

/-- `SigningLaws.polyVecNorm_sampleInBall_smul_le` from the full primitive laws. -/
theorem polyVecNorm_sampleInBall_smul_le (h_laws : Primitives.Laws prims nttOps)
    (cTilde : CommitHashBytes p) {k : ℕ} (s : RqVec k) (hs : polyVecBounded s p.eta) :
    polyVecNorm (prims.sampleInBall cTilde • s) ≤ p.beta :=
  SigningLaws.polyVecNorm_sampleInBall_smul_le prims h_laws.toSigningLaws cTilde s hs

/-! ### The published commitment -/

/-- **On acceptance `HighBits(w - cs₂) = HighBits(w)`** for `w = Â·y` and `c = SampleInBall(c̃)`,
given the primitive laws and `‖s₂‖∞ ≤ η`: the r0-check keeps `w - cs₂` at least `β` away from a
`HighBits` boundary, and `‖cs₂‖∞ ≤ β`. So the commitment the verifier recovers is `HighBits(w)`. -/
theorem SigningLaws.highBitsVec_sub_eq_of_isSome (h_laws : SigningLaws prims)
    {sk : SecretKey p} (hs2 : polyVecBounded sk.s2 p.eta) {aHat : TqMatrix p.k p.l}
    {y : RqVec p.l} {cTilde : CommitHashBytes p}
    (hsome : (idealAttempt prims sk aHat y cTilde).isSome) :
    prims.highBitsVec (aHat * y - prims.sampleInBall cTilde • sk.s2) =
      prims.highBitsVec (aHat * y) := by
  obtain ⟨-, hr0, -, -⟩ := (idealAttempt_isSome_iff prims sk aHat y cTilde).mp hsome
  simp only [r0Check, decide_eq_true_eq] at hr0
  have hcs2 := polyVecNorm_sampleInBall_smul_le prims h_laws cTilde sk.s2 hs2
  set cs2 := prims.sampleInBall cTilde • sk.s2
  set w := aHat * y
  apply Vector.ext
  intro j hj
  let jj : Fin p.k := ⟨j, hj⟩
  unfold Primitives.highBitsVec
  simp only [Vector.getElem_map]
  have hs : polyNorm cs2[j] ≤ p.beta :=
    le_trans (PolyVec.component_cInfNorm_le normOps cs2 jj) hcs2
  have hlow : polyNorm (prims.lowBitsVec (w - cs2))[j] < p.gamma2 - p.beta :=
    lt_of_le_of_lt (PolyVec.component_cInfNorm_le normOps (prims.lowBitsVec (w - cs2)) jj) hr0
  simp only [Primitives.lowBitsVec, Vector.getElem_map] at hlow
  have hw : w[j] = (w - cs2)[j] + cs2[j] := by
    rw [Vector.getElem_sub]; exact (sub_add_cancel _ _).symm
  rw [hw, h_laws.hide_low _ _ p.beta hs (by omega)]

/-- `SigningLaws.highBitsVec_sub_eq_of_isSome` from the full primitive laws. -/
theorem highBitsVec_sub_eq_of_isSome (h_laws : Primitives.Laws prims nttOps)
    {sk : SecretKey p} (hs2 : polyVecBounded sk.s2 p.eta) {aHat : TqMatrix p.k p.l}
    {y : RqVec p.l} {cTilde : CommitHashBytes p}
    (hsome : (idealAttempt prims sk aHat y cTilde).isSome) :
    prims.highBitsVec (aHat * y - prims.sampleInBall cTilde • sk.s2) =
      prims.highBitsVec (aHat * y) :=
  SigningLaws.highBitsVec_sub_eq_of_isSome prims h_laws.toSigningLaws hs2 hsome

end Attempt

/-! ### The attempt law as a rejection attempt -/

/-- Mapping each accepted value commutes with the bounded loop. -/
theorem _root_.PMF.firstSome_map_optionMap {α β : Type*} (A : PMF (Option α)) (f : α → β)
    (n : ℕ) :
    PMF.firstSome (A.map (Option.map f)) n = (PMF.firstSome A n).map (Option.map f) := by
  induction n with
  | zero => simp [PMF.firstSome, PMF.pure_map]
  | succ n ih =>
    simp only [PMF.firstSome, PMF.map_bind, PMF.bind_map]
    congr 1
    funext o
    cases o with
    | none => simp [ih]
    | some a => simp [PMF.pure_map]

section Law

variable {p : Params} (prims : Primitives p) [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

/-- The idealized ExpandMask: the uniform law on the mask box. -/
noncomputable def maskUniform (p : Params) [Nonempty (MaskBox p)] : PMF (MaskBox p) :=
  PMF.uniformOfFintype (MaskBox p)

/-- The acceptance test of an idealized attempt, on masks in the box. -/
def attemptAccept (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : MaskBox p)
    (cTilde : CommitHashBytes p) : Bool :=
  signAccept prims sk aHat y.1 cTilde

/-- The signature `(c̃, y + c·s₁, h)` an accepted pair `(y, c̃)` outputs. -/
def attemptOutput (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (yc : MaskBox p × CommitHashBytes p) : FIPSSignature p prims :=
  ⟨yc.2, yc.1.1 + prims.sampleInBall yc.2 • sk.s1, attemptHint prims sk aHat yc.1.1 yc.2⟩

/-- **The law of one idealized signing attempt**: `y` uniform on the mask box, `c̃` uniform on
`CommitHashBytes p` and independent of `y` (a fresh random-oracle answer), then `idealAttempt`. -/
noncomputable def idealAttemptLaw (sk : SecretKey p) (aHat : TqMatrix p.k p.l) :
    PMF (Option (FIPSSignature p prims)) :=
  (maskUniform p).bind fun y =>
    (PMF.uniformOfFintype (CommitHashBytes p)).map (idealAttempt prims sk aHat y.1)

/-- **One idealized attempt is a rejection attempt**: proposal uniform on `MaskBox p`, challenge
`c̃`, acceptance the four checks, accepted pair mapped to its signature. -/
theorem idealAttemptLaw_eq (sk : SecretKey p) (aHat : TqMatrix p.k p.l) :
    idealAttemptLaw prims sk aHat =
      (PMF.rejectionAttempt (maskUniform p) (attemptAccept prims sk aHat)).map
        (Option.map (attemptOutput prims sk aHat)) := by
  unfold idealAttemptLaw PMF.rejectionAttempt
  rw [PMF.map_bind]
  congr 1
  funext y
  rw [PMF.map_comp]
  congr 1
  funext c
  simp only [Function.comp_apply, idealAttempt_eq_ite, attemptAccept]
  by_cases h : signAccept prims sk aHat y.1 c <;> simp [h, attemptOutput]

/-- **The idealized bounded signing loop** (FIPS 204 Algorithm 7 lines 4–31 with at most `n`
attempts): independent idealized attempts until the first acceptance. -/
noncomputable def idealLoopLaw (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (n : ℕ) :
    PMF (Option (FIPSSignature p prims)) :=
  PMF.firstSome (idealAttemptLaw prims sk aHat) n

/-- The idealized loop is the bounded rejection loop `PMF.firstSome` over the rejection attempt,
accepted pair mapped to its signature. -/
theorem idealLoopLaw_eq (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (n : ℕ) :
    idealLoopLaw prims sk aHat n =
      (PMF.firstSome (PMF.rejectionAttempt (maskUniform p) (attemptAccept prims sk aHat)) n).map
        (Option.map (attemptOutput prims sk aHat)) := by
  rw [idealLoopLaw, idealAttemptLaw_eq, PMF.firstSome_map_optionMap]

/-- **The accepted commitment hash** of an idealized attempt has density proportional to
`Pr_{y ← MaskBox}[signAccept y c̃]`: it is that probability times `|CommitHashBytes p|⁻¹`,
divided by the acceptance probability. -/
theorem acceptedChallenge_apply (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (h : PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) ≠ 0)
    (cTilde : CommitHashBytes p) :
    (PMF.condSome (PMF.rejectionAttempt (maskUniform p) (attemptAccept prims sk aHat))
        (PMF.rejectionAttempt_apply_none_ne_one h)).map Prod.snd cTilde =
      PMF.acceptProbAt (maskUniform p) (attemptAccept prims sk aHat) cTilde *
        (Fintype.card (CommitHashBytes p) : ENNReal)⁻¹ /
        PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) :=
  PMF.map_snd_condSome_rejectionAttempt_apply h cTilde

/-- `Pr_{y ← MaskBox}[signAccept y c̃]` is the number of accepted masks over `(2γ₁)^(256 l)`. -/
theorem acceptProbAt_maskUniform (hq : 2 * p.gamma1 < modulus) (sk : SecretKey p)
    (aHat : TqMatrix p.k p.l) (cTilde : CommitHashBytes p) :
    PMF.acceptProbAt (maskUniform p) (attemptAccept prims sk aHat) cTilde =
      ((Finset.univ.filter fun y : MaskBox p => attemptAccept prims sk aHat y cTilde).card :
          ENNReal) * ((2 * p.gamma1) ^ (ringDegree * p.l) : ENNReal)⁻¹ := by
  rw [PMF.acceptProbAt, maskUniform]
  simp only [PMF.uniformOfFintype_apply, card_maskBox hq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  push_cast
  rfl

end Law

end GordieHowe.MLDSA
