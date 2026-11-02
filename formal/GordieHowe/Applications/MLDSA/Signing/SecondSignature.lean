-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Model.Lattice.MLDSA
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# A second signature at a published commitment gives a Module-SIS solution

Two signatures `σ = (c̃, z, h)` and `σ' = (c̃, z', h')`, `σ ≠ σ'`, with the same commitment hash,
both accepted by `ringVerify` (FIPS 204 Algorithm 8 with the commitment hash read from a random
oracle, `RingSigner.lean`) under the same public key `(ρ, t₁)` at the same message and published
commitment `w₁`, give a short nonzero vector in the kernel of `[Â | I]`, `Â = ExpandA(ρ)`: the
strong-unforgeability step of the Dilithium specification (Version 3.1, §6.2.2; KLS18 Lemma 4.9,
§4.3). Everything is stated at the vendored FIPS 204 primitives with the FIPS 204 `ExpandS`
(`concretePrimitivesKeyGen`), the concrete NTT and the concrete encoding of commitments
(`concreteEnc`).

## `UseHint` (FIPS 204 Algorithm 40)

- `useHint_sub_bound`: `‖r − 2γ₂ · UseHint(h, r)‖∞ ≤ 2γ₂ + 1` (centered mod `q`, with
  `2γ₂ · r₁` the vendored `highBitsShift`), at every approved parameter set. This is the
  vendored `concreteRounding_useHint_bound_of_isApproved`, restated at `polyNorm`.
- `useHintCoeff_lt_bucketCount`, `val_useHint_get`: every `UseHint` coefficient is below
  `m = (q − 1)/(2γ₂)` (`bucketCount_lt_modulus`: `m < q`), so its residue is itself.
- `useHintCoeff_injective`: for `m ≥ 2` (`two_le_bucketCount`), `UseHint(0, r) ≠ UseHint(1, r)`
  coefficientwise (`mod_succ_ne_and_mod_pred_ne`); `useHint_hint_injective`,
  `useHintVec_hint_injective` (with `useHintVec_get`): two hint vectors with the same `UseHint`
  output at the same `r` are equal.
- `concreteEnc_useHintVec_injective`: the concrete encoding is injective on `UseHint` outputs.

## Norms

- `natAbs_centeredRepr_sub_le`, `polyNorm_sub_le`, `polyVecNorm_sub_le`, `polyNorm_neg_le`,
  `polyNorm_neg`, `polyVecNorm_neg`: the triangle inequality and negation for the centered
  `∞`-norm.

## The second signature

- `computeWApprox_sub`: `w'_Approx(z) − w'_Approx(z') = Â·(z − z')` at the same challenge and
  `t₁`, from the transform laws.
- `sigWApprox pk σ`: `w'_Approx = Â·z − c·t₁·2^d` of `σ` under `pk` (FIPS 204 Algorithm 8,
  line 9); `secondSigVec pk σ σ' = (z − z', −(w'_Approx(σ) − w'_Approx(σ')))`.
- `kernel_secondSigVec`: **the second-signature lemma**: for an approved parameter set, `σ ≠ σ'`
  with the same `c̃`, both accepted by `ringVerify` at the same oracle, encoding `concreteEnc`,
  key, message and `w₁`, `secondSigVec pk σ σ'` solves Module-SIS for `Â` with bounds
  `msisStrictBoundZ p = 2(γ₁ − β − 1)` and `msisBoundU p = 4γ₂ + 2` (`Lattice.Kernel`).
- `cTilde_eq_of_ringVerify`, `kernel_secondSigVec_of_ne`, `keyGenKernel_secondSigVec`: two accepted
  signatures at the same oracle, key, message and `w₁` have the same `c̃`, so `σ ≠ σ'` alone gives
  the solution; for the key of a seed `ξ` it is a solution for `Lattice.KeyGenKernel` at `ξ`.
- `exists_ringVerify`: the hypotheses are not vacuous one signature at a time: for every key,
  message and `c̃` there are an oracle and a commitment at which `(c̃, 0, 0)` is accepted.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec GordieHowe.Ring.MLDSAW1
  GordieHowe.Lattice
open LatticeCrypto TransformOps

/-! ### Norms -/

/-- The triangle inequality for centered representatives mod `q`. -/
theorem natAbs_centeredRepr_sub_le (a b : Coeff) :
    (centeredRepr (a - b)).natAbs ≤ (centeredRepr a).natAbs + (centeredRepr b).natAbs := by
  simp only [centeredRepr_eq_valMinAbs, sub_eq_add_neg]
  calc (a + -b).valMinAbs.natAbs ≤ (a.valMinAbs + (-b).valMinAbs).natAbs :=
        ZMod.natAbs_valMinAbs_add_le a (-b)
    _ ≤ a.valMinAbs.natAbs + (-b).valMinAbs.natAbs := Int.natAbs_add_le _ _
    _ = a.valMinAbs.natAbs + b.valMinAbs.natAbs := by rw [ZMod.natAbs_valMinAbs_neg]

/-- The triangle inequality for the centered `∞`-norm of a polynomial. -/
theorem polyNorm_sub_le (f g : Rq) : polyNorm (f - g) ≤ polyNorm f + polyNorm g := by
  rw [polyNorm_eq_cInfNorm, polyNorm_eq_cInfNorm, polyNorm_eq_cInfNorm]
  refine cInfNorm_le_iff.mpr fun i => ?_
  rw [Rq.get_sub]
  exact (natAbs_centeredRepr_sub_le _ _).trans
    (add_le_add (coeff_le_cInfNorm f i) (coeff_le_cInfNorm g i))

/-- The triangle inequality for the centered `∞`-norm of a polynomial vector. -/
theorem polyVecNorm_sub_le {k : ℕ} (u v : RqVec k) :
    polyVecNorm (u - v) ≤ polyVecNorm u + polyVecNorm v := by
  refine (PolyVec.cInfNorm_le_iff normOps).mpr fun j => ?_
  have h1 : (u - v).get j = u.get j - v.get j := by
    simp only [Vector.get_eq_getElem, Vector.getElem_sub]
  rw [h1]
  exact (polyNorm_sub_le _ _).trans (add_le_add (PolyVec.component_cInfNorm_le normOps u j)
    (PolyVec.component_cInfNorm_le normOps v j))

/-- Negation does not increase the centered `∞`-norm of a polynomial. -/
theorem polyNorm_neg_le (f : Rq) : polyNorm (-f) ≤ polyNorm f := by
  rw [polyNorm_eq_cInfNorm, polyNorm_eq_cInfNorm]
  refine cInfNorm_le_iff.mpr fun i => ?_
  rw [Rq.get_neg, centeredRepr_natAbs_neg]
  exact coeff_le_cInfNorm f i

/-- Negation preserves the centered `∞`-norm of a polynomial. -/
theorem polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  refine le_antisymm (polyNorm_neg_le f) ?_
  rw [polyNorm_eq_cInfNorm, polyNorm_eq_cInfNorm]
  refine cInfNorm_le_iff.mpr fun i => ?_
  have := coeff_le_cInfNorm (-f) i
  rwa [Rq.get_neg, centeredRepr_natAbs_neg] at this

/-- Negation preserves the centered `∞`-norm of a polynomial vector. -/
theorem polyVecNorm_neg {k : ℕ} (v : RqVec k) : polyVecNorm (-v) = polyVecNorm v := by
  have h1 : ∀ j : Fin k, (-v).get j = -v.get j := fun j => by
    simp only [Vector.get_eq_getElem, Vector.getElem_neg]
  unfold polyVecNorm PolyVec.cInfNorm
  congr 1
  funext j
  rw [h1, ← polyNorm, ← polyNorm]
  exact polyNorm_neg _

/-! ### `UseHint` -/

/-- **The `UseHint` bound** (FIPS 204 Algorithm 40): `‖r − 2γ₂ · UseHint(h, r)‖∞ ≤ 2γ₂ + 1`,
centered mod `q`, with `2γ₂ · r₁` the vendored `highBitsShift`, at every approved parameter set
(`concreteRounding_useHint_bound_of_isApproved`). -/
theorem useHint_sub_bound {p : Params} (hp : p.isApproved) (h : Hint) (r : Rq) :
    polyNorm (r - highBitsShift p (useHint p h r)) ≤ 2 * p.gamma2 + 1 := by
  rw [polyNorm_eq_cInfNorm]
  exact concreteRounding_useHint_bound_of_isApproved p hp r h

/-- There are at least two `HighBits` buckets. -/
theorem two_le_bucketCount {p : Params} (hp : SigningParams p) : 2 ≤ bucketCount p := by
  obtain ⟨m, hm⟩ := hp.gamma2_dvd
  have hpos : 0 < 2 * p.gamma2 := by have := hp.gamma2_pos; omega
  have hb : bucketCount p = m := by
    unfold bucketCount
    rw [hm, Nat.mul_div_cancel_left _ hpos]
  have h2 := hp.two_buckets
  rw [hm] at h2
  rw [hb]
  by_contra hlt
  interval_cases m <;> omega

/-- The number of buckets is below `q`. -/
theorem bucketCount_lt_modulus (p : Params) : bucketCount p < modulus := by
  unfold bucketCount
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num [modulus])

/-- `(r₁ + 1) mod m ≠ r₁` and `(r₁ + m − 1) mod m ≠ r₁` for `r₁ < m` and `m ≥ 2`. -/
theorem mod_succ_ne_and_mod_pred_ne {r1 m : ℕ} (hr1 : r1 < m) (hm : 2 ≤ m) :
    (r1 + 1) % m ≠ r1 ∧ (r1 + m - 1) % m ≠ r1 := by
  constructor
  · by_cases hw : r1 + 1 < m
    · rw [Nat.mod_eq_of_lt hw]; omega
    · rw [show r1 + 1 = m by omega, Nat.mod_self]; omega
  · by_cases h0 : r1 = 0
    · subst h0
      rw [show 0 + m - 1 = m - 1 by omega, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show r1 + m - 1 = r1 - 1 + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega

/-- **Every `UseHint` coefficient is a bucket**: below `m = (q − 1)/(2γ₂)`. -/
theorem useHintCoeff_lt_bucketCount {p : Params} (hp : SigningParams p) (h : Bool) (r : Coeff) :
    useHintCoeff h r p.gamma2 < bucketCount p := by
  have hlt := highBitsCoeff_lt_bucketCount hp r
  have hm := two_le_bucketCount hp
  rcases hdec : decomposeCoeff r p.gamma2 with ⟨r1, r0⟩
  have hr1 : r1 < bucketCount p := by simpa [highBitsCoeff, hdec] using hlt
  have hm' : 0 < (modulus - 1) / (2 * p.gamma2) := by unfold bucketCount at hm; omega
  unfold useHintCoeff
  simp only [hdec]
  cases h <;> split_ifs <;> first | exact hr1 | exact Nat.mod_lt _ hm'

/-- **Hint uniqueness per coefficient**: `UseHint(0, r) ≠ UseHint(1, r)`, for `m ≥ 2`
(`two_le_bucketCount`). -/
theorem useHintCoeff_injective {p : Params} (hp : SigningParams p) (r : Coeff) :
    Function.Injective fun h : Bool => useHintCoeff h r p.gamma2 := by
  have hlt := highBitsCoeff_lt_bucketCount hp r
  have hm := two_le_bucketCount hp
  rcases hdec : decomposeCoeff r p.gamma2 with ⟨r1, r0⟩
  have hr1 : r1 < bucketCount p := by simpa [highBitsCoeff, hdec] using hlt
  have hne := mod_succ_ne_and_mod_pred_ne hr1 hm
  unfold bucketCount at hne
  have htrue : useHintCoeff true r p.gamma2 ≠ useHintCoeff false r p.gamma2 := by
    simp only [useHintCoeff, hdec, ↓reduceIte, Bool.false_eq_true]
    split_ifs
    · exact hne.1
    · exact hne.2
  intro a b hab
  cases a <;> cases b
  · rfl
  · exact absurd hab.symm htrue
  · exact absurd hab htrue
  · rfl

/-- The coefficients of `UseHint(h, r)` as natural numbers. -/
theorem val_useHint_get {p : Params} (hp : SigningParams p) (h : Hint) (r : Rq)
    (i : Fin ringDegree) :
    ((useHint p h r).get i).val = useHintCoeff (h.get i) (r.get i) p.gamma2 := by
  simp only [useHint, Vector.get_ofFn]
  exact ZMod.val_natCast_of_lt
    ((useHintCoeff_lt_bucketCount hp _ _).trans (bucketCount_lt_modulus p))

/-- **Hint uniqueness per polynomial**: `UseHint(h, r) = UseHint(h', r)` gives `h = h'`. -/
theorem useHint_hint_injective {p : Params} (hp : SigningParams p) {h h' : Hint} {r : Rq}
    (heq : useHint p h r = useHint p h' r) : h = h' := by
  refine Vector.ext fun i hi => ?_
  have hv := congrArg (fun v : Rq => (v.get ⟨i, hi⟩).val) heq
  simp only [val_useHint_get hp] at hv
  simpa [Vector.get_eq_getElem] using useHintCoeff_injective hp _ hv

variable {p : Params}

/-- The components of `UseHintVec` at the concrete primitives. -/
theorem useHintVec_get {k : ℕ} (h : Vector (concretePrimitivesKeyGen p).Hint k) (r : RqVec k)
    (j : Fin k) :
    ((concretePrimitivesKeyGen p).useHintVec h r).get j = useHint p (h.get j) (r.get j) := by
  rw [Vector.get_eq_getElem]
  exact Vector.getElem_zipWith (f := (concretePrimitivesKeyGen p).useHint) (i := j.val) j.isLt

/-- **Hint uniqueness per vector**: two hint vectors with the same `UseHintVec` output at the
same `r` are equal. -/
theorem useHintVec_hint_injective (hp : SigningParams p) {k : ℕ}
    {h h' : Vector (concretePrimitivesKeyGen p).Hint k}
    {r : RqVec k}
    (heq : (concretePrimitivesKeyGen p).useHintVec h r =
      (concretePrimitivesKeyGen p).useHintVec h' r) : h = h' := by
  refine Vector.ext fun j hj => ?_
  have hc := congrArg (fun v => Vector.get v ⟨j, hj⟩) heq
  simp only [useHintVec_get] at hc
  exact useHint_hint_injective hp hc

/-- **The concrete encoding is injective on `UseHint` outputs.** -/
theorem concreteEnc_useHintVec_injective [NeZero (bucketCount p)] (hp : SigningParams p)
    {h h' : Vector (concretePrimitivesKeyGen p).Hint p.k} {r r' : RqVec p.k}
    (heq : concreteEnc p ((concretePrimitivesKeyGen p).useHintVec h r) =
      concreteEnc p ((concretePrimitivesKeyGen p).useHintVec h' r')) :
    (concretePrimitivesKeyGen p).useHintVec h r =
      (concretePrimitivesKeyGen p).useHintVec h' r' := by
  refine Vector.ext fun j hj => Vector.ext fun i hi => ?_
  have hx : ((useHint p (h.get ⟨j, hj⟩) (r.get ⟨j, hj⟩)).get ⟨i, hi⟩).val % bucketCount p =
      ((useHint p (h'.get ⟨j, hj⟩) (r'.get ⟨j, hj⟩)).get ⟨i, hi⟩).val % bucketCount p := by
    rw [← useHintVec_get, ← useHintVec_get]
    exact congrArg Fin.val (congrFun heq (⟨j, hj⟩, ⟨i, hi⟩))
  have v1 := val_useHint_get hp (h.get ⟨j, hj⟩) (r.get ⟨j, hj⟩) ⟨i, hi⟩
  have v2 := val_useHint_get hp (h'.get ⟨j, hj⟩) (r'.get ⟨j, hj⟩) ⟨i, hi⟩
  rw [v1, v2, Nat.mod_eq_of_lt (useHintCoeff_lt_bucketCount hp _ _),
    Nat.mod_eq_of_lt (useHintCoeff_lt_bucketCount hp _ _)] at hx
  show Vector.get (((concretePrimitivesKeyGen p).useHintVec h r).get ⟨j, hj⟩) ⟨i, hi⟩ =
    Vector.get (((concretePrimitivesKeyGen p).useHintVec h' r').get ⟨j, hj⟩) ⟨i, hi⟩
  rw [useHintVec_get, useHintVec_get]
  apply ZMod.val_injective
  rw [v1, v2]
  exact hx

/-! ### The second signature -/

section Second

attribute [local instance] concreteNTTRingOps

variable {prims : Primitives p}

/-- **`w'_Approx` is affine in `z`**: at the same matrix, challenge and `t₁`,
`w'_Approx(z) − w'_Approx(z') = Â·(z − z')`, from the transform laws. -/
theorem computeWApprox_sub [nttOps : NTTRingOps] (hl : NTTRingLaws nttOps)
    (aHat : TqMatrix p.k p.l) (c : Rq) (z z' : RqVec p.l) (t1 : Vector prims.Power2High p.k) :
    computeWApprox p prims aHat c z t1 - computeWApprox p prims aHat c z' t1 = aHat * (z - z') := by
  have := hl
  have hz : z = (z - z') + z' := by
    refine Vector.ext fun i _ => ?_
    simp only [Vector.getElem_add, Vector.getElem_sub]
    exact (sub_add_cancel _ _).symm
  conv_lhs => rw [hz]
  simp only [computeWApprox, HMul.hMul, coeffMatVecMul]
  rw [nttOps.hatVec_add, nttOps.matVecMul_add]
  refine Vector.ext fun i _ => ?_
  simp only [unhatVec, Vector.getElem_map, Vector.getElem_sub, Vector.getElem_add,
    nttOps.fromHat_subHat, nttOps.fromHat_addHat]
  abel

variable (p) in
/-- **`w'_Approx` of a signature** under a public key: `Â·z − c·t₁·2^d`, `Â = ExpandA(ρ)`,
`c = SampleInBall(c̃)` (FIPS 204 Algorithm 8, line 9). -/
abbrev sigWApprox (pk : PublicKey p (concretePrimitivesKeyGen p))
    (σ : FIPSSignature p (concretePrimitivesKeyGen p)) : RqVec p.k :=
  computeWApprox p (concretePrimitivesKeyGen p) ((concretePrimitivesKeyGen p).expandA pk.rho)
    ((concretePrimitivesKeyGen p).sampleInBall σ.cTilde) σ.z pk.t1

variable (p) in
/-- **The vector of two signatures**: `(z − z', −(w'_Approx(σ) − w'_Approx(σ')))`. -/
def secondSigVec (pk : PublicKey p (concretePrimitivesKeyGen p))
    (σ σ' : FIPSSignature p (concretePrimitivesKeyGen p)) : RqVec p.l × RqVec p.k :=
  (σ.z - σ'.z, -(sigWApprox p pk σ - sigWApprox p pk σ'))

/-- **A second signature at a published commitment gives a Module-SIS solution** (Dilithium
specification, Version 3.1, §6.2.2; KLS18 Lemma 4.9, §4.3): at an approved parameter set, two
distinct signatures with the same commitment hash `c̃`, both accepted by `ringVerify` with the
concrete encoding at the same oracle, public key, message and published commitment `w₁`, give `x =
(z − z', −(w'_Approx(σ) − w'_Approx(σ')))` with `x ≠ 0`, `Â·x₁ + x₂ = 0`, `‖x₁‖∞ ≤ 2(γ₁ − β − 1)`
and `‖x₂‖∞ ≤ 4γ₂ + 2`, `Â = ExpandA(ρ)`. -/
theorem kernel_secondSigVec [NeZero (bucketCount p)] (hp : p.isApproved) {Msg : Type}
    (H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p)
    (pk : PublicKey p (concretePrimitivesKeyGen p)) (m : Msg) (w1 : BucketVec p)
    {σ σ' : FIPSSignature p (concretePrimitivesKeyGen p)} (hne : σ ≠ σ')
    (hc : σ.cTilde = σ'.cTilde)
    (hv : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1 σ = true)
    (hv' : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1 σ' = true) :
    Kernel p (msisStrictBoundZ p) (msisBoundU p) ((concretePrimitivesKeyGen p).expandA pk.rho)
      (secondSigVec p pk σ σ') := by
  have hsp := SigningParams.of_isApproved hp
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at hv hv'
  obtain ⟨⟨⟨hz, hw⟩, -⟩, -⟩ := hv
  obtain ⟨⟨⟨hz', hw'⟩, -⟩, -⟩ := hv'
  have hU : (concretePrimitivesKeyGen p).useHintVec σ.h (sigWApprox p pk σ) =
      (concretePrimitivesKeyGen p).useHintVec σ'.h (sigWApprox p pk σ') :=
    concreteEnc_useHintVec_injective hsp (hw.trans hw'.symm)
  -- the two `w'_Approx` differ by `Â·(z − z')`
  have hdiff : sigWApprox p pk σ - sigWApprox p pk σ' =
      (concretePrimitivesKeyGen p).expandA pk.rho * (σ.z - σ'.z) := by
    unfold sigWApprox
    rw [hc]
    exact computeWApprox_sub concreteNTTRingLaws _ _ _ _ _
  refine KernelAI.of_fst_ne_zero ?_ ?_ ?_ ?_
  · -- `z ≠ z'`: otherwise the `w'_Approx` agree, so do the hints, and `σ = σ'`
    intro h0
    have hzz : σ.z = σ'.z := by
      refine Vector.ext fun i hi => ?_
      have := congrArg (fun v : RqVec p.l => v[i]) h0
      simp only [secondSigVec, Vector.getElem_sub] at this
      rw [Vector.getElem_zero] at this
      exact sub_eq_zero.mp this
    have hW : sigWApprox p pk σ' = sigWApprox p pk σ := by
      simp only [sigWApprox, hc, hzz]
    rw [hW] at hU
    have hh := useHintVec_hint_injective hsp hU
    apply hne
    cases σ
    cases σ'
    simp_all
  · simp only [secondSigVec]
    rw [← hdiff]
    refine Vector.ext fun i _ => ?_
    simp only [Vector.getElem_add, Vector.getElem_neg, Vector.getElem_zero]
    exact add_neg_cancel _
  · have h1 := polyVecNorm_sub_le σ.z σ'.z
    change polyVecNorm (σ.z - σ'.z) ≤ msisStrictBoundZ p
    unfold msisStrictBoundZ
    omega
  · change polyVecNorm (-(sigWApprox p pk σ - sigWApprox p pk σ')) ≤ msisBoundU p
    rw [polyVecNorm_neg]
    refine (PolyVec.cInfNorm_le_iff normOps).mpr fun j => ?_
    set U := (concretePrimitivesKeyGen p).useHintVec σ.h (sigWApprox p pk σ)
    have hj : (sigWApprox p pk σ - sigWApprox p pk σ').get j =
        ((sigWApprox p pk σ).get j - highBitsShift p (U.get j)) -
          ((sigWApprox p pk σ').get j - highBitsShift p (U.get j)) := by
      simp only [Vector.get_eq_getElem, Vector.getElem_sub]
      abel
    have hb1 := useHint_sub_bound hp (σ.h.get j) ((sigWApprox p pk σ).get j)
    have hb2 := useHint_sub_bound hp (σ'.h.get j) ((sigWApprox p pk σ').get j)
    have e1 : U.get j = useHint p (σ.h.get j) ((sigWApprox p pk σ).get j) := useHintVec_get _ _ j
    have e2 : U.get j = useHint p (σ'.h.get j) ((sigWApprox p pk σ').get j) := by
      rw [hU]; exact useHintVec_get _ _ j
    rw [← e1] at hb1
    rw [← e2] at hb2
    rw [hj]
    refine (polyNorm_sub_le _ _).trans ?_
    unfold msisBoundU
    omega

/-- **Two signatures accepted at the same oracle, public key, message and published commitment
have the same commitment hash** `c̃ = H((tr, m), w₁)`. -/
theorem cTilde_eq_of_ringVerify [NeZero (bucketCount p)] {Msg : Type}
    {H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p}
    {pk : PublicKey p (concretePrimitivesKeyGen p)} {m : Msg} {w1 : BucketVec p}
    {σ σ' : FIPSSignature p (concretePrimitivesKeyGen p)}
    (hv : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1 σ = true)
    (hv' : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1 σ' = true) :
    σ.cTilde = σ'.cTilde := by
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at hv hv'
  exact hv.1.2.symm.trans hv'.1.2

/-- **A second accepted signature gives a Module-SIS solution** (`kernel_secondSigVec` with the
equal commitment hashes from `cTilde_eq_of_ringVerify`): at an approved parameter set, two distinct
signatures accepted at the same oracle, public key, message and published commitment. -/
theorem kernel_secondSigVec_of_ne [NeZero (bucketCount p)] (hp : p.isApproved) {Msg : Type}
    {H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p}
    {pk : PublicKey p (concretePrimitivesKeyGen p)} {m : Msg} {w1 : BucketVec p}
    {σ σ' : FIPSSignature p (concretePrimitivesKeyGen p)} (hne : σ ≠ σ')
    (hv : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1 σ = true)
    (hv' : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1 σ' = true) :
    Kernel p (msisStrictBoundZ p) (msisBoundU p) ((concretePrimitivesKeyGen p).expandA pk.rho)
      (secondSigVec p pk σ σ') :=
  kernel_secondSigVec hp H pk m w1 hne (cTilde_eq_of_ringVerify hv hv') hv hv'

/-- **The key-generation form**: for the public key of the seed `ξ`, two distinct accepted
signatures at the same oracle, message and published commitment give a solution for the
key-generation matrix of `ξ` (`Lattice.KeyGenKernel`), the instance of
`Lattice.keyGenMsisMultiWinProb`. -/
theorem keyGenKernel_secondSigVec [NeZero (bucketCount p)] (hp : p.isApproved) {Msg : Type}
    {H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p} (ξ : Bytes 32) {m : Msg}
    {w1 : BucketVec p} {σ σ' : FIPSSignature p (concretePrimitivesKeyGen p)} (hne : σ ≠ σ')
    (hv : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p)
      (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 m w1 σ = true)
    (hv' : ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p)
      (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 m w1 σ' = true) :
    Lattice.KeyGenKernel p (concretePrimitivesKeyGen p) (msisStrictBoundZ p) (msisBoundU p) ξ
      (secondSigVec p (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 σ σ') :=
  kernel_secondSigVec_of_ne hp hne hv hv'

/-- **Accepted signatures exist**: for every public key, message and commitment hash `c̃`, the
signature `(c̃, 0, 0)` is accepted by `ringVerify` with the concrete encoding at the oracle
constantly `c̃` and the commitment it recomputes, at every approved parameter set. -/
theorem exists_ringVerify [NeZero (bucketCount p)] (hp : p.isApproved) {Msg : Type}
    (pk : PublicKey p (concretePrimitivesKeyGen p)) (m : Msg) (cTilde : CommitHashBytes p) :
    ∃ (H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p) (w1 : BucketVec p),
      ringVerify (concretePrimitivesKeyGen p) H (concreteEnc p) pk m w1
        ⟨cTilde, Vector.replicate p.l 0, Vector.replicate p.k (Vector.replicate ringDegree false)⟩ =
        true := by
  have hsp := SigningParams.of_isApproved hp
  refine ⟨fun _ => cTilde, concreteEnc p ((concretePrimitivesKeyGen p).useHintVec
    (Vector.replicate p.k (Vector.replicate ringDegree false))
    (computeWApprox p (concretePrimitivesKeyGen p) ((concretePrimitivesKeyGen p).expandA pk.rho)
      ((concretePrimitivesKeyGen p).sampleInBall cTilde) (Vector.replicate p.l 0) pk.t1)), ?_⟩
  have hz : polyVecNorm (Vector.replicate p.l (0 : Rq)) = 0 := by
    refine Nat.le_zero.mp ((PolyVec.cInfNorm_le_iff normOps).mpr fun j => ?_)
    rw [Vector.get_replicate]
    rw [← polyNorm, polyNorm_eq_cInfNorm]
    refine cInfNorm_le_iff.mpr fun i => ?_
    rw [Rq.get_zero]
    simp [centeredRepr_eq_valMinAbs]
  have hfold : ∀ (n acc : ℕ),
      (List.replicate n false).foldl (fun acc b => acc + cond b 1 0) acc = acc := by
    intro n
    induction n with
    | zero => intro acc; rfl
    | succ n ih => intro acc; simpa [List.replicate_succ] using ih acc
  have hw : (concretePrimitivesKeyGen p).hintWeight
      (Vector.replicate p.k (Vector.replicate ringDegree false)) = 0 := by
    have h0 : hintWeight (Vector.replicate ringDegree false) = 0 := by
      unfold hintWeight
      rw [Vector.toList_replicate]
      exact hfold _ 0
    show ((Vector.replicate p.k (Vector.replicate ringDegree false)).toList.map hintWeight).sum = 0
    rw [Vector.toList_replicate, List.map_replicate, h0, List.sum_replicate,
      smul_zero]
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq, hz, hw]
  have hβ := hsp.beta_lt_gamma1
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Nat.zero_le _⟩ <;> first | trivial | omega

end Second

end GordieHowe.MLDSA
