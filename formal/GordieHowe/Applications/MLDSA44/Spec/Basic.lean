-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Params
public import GordieHowe.Applications.Spec.Rq
public import LatticeCrypto.MLDSA.ConcretePrimitives
public import GordieHowe.Applications.MLDSA44.Spec.ExpandA
import all LatticeCrypto.MLDSA.Concrete.Encoding
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# ML-DSA-44 verification

The specification follows FIPS 204. Layer 0 for ML-DSA verification is the vendored
`_root_.MLDSA.fipsVerify` (`Vendor/LatticeCrypto/MLDSA/Verify.lean`) at the vendored
`_root_.MLDSA.Concrete.concretePrimitives` (`Vendor/LatticeCrypto/MLDSA/ConcretePrimitives.lean`),
SHAKE-based concrete primitives (`ExpandA`, `SampleInBall`, `Decompose`, `HighBits`, `UseHint`,
`w1Encode`, message hashing) at the ML-DSA-44 parameter set. `GordieHowe.mldsa44` (`GordieHowe/Applications/Params.lean`) is the
parameter record of the circuits; `mldsa44_matches` checks it against the vendored
`_root_.MLDSA.mldsa44`.

The relation target is `VerifiesBytes pk ctx msg sigBytes`: FIPS 204 Algorithm 3 on the
statement `(pk, ctx)`, serialized signature bytes and the message, with `ExpandA` within `1008`
SHAKE128 bytes per `RejNTTPoly` call (`GordieHowe/Applications/MLDSA44/Spec/ExpandA.lean`) and
`SampleInBall` within `272` SHAKE256 bytes, both bounds FIPS 204 Appendix C permits. `verifyChecks` is the vendored `fipsVerify` with `Â` given (`fipsVerify_eq_verifyChecks`). This file also states
`w′_approx = A·z − c·t₁·2^d` (`computeWApprox_get`, `coeff_computeWApprox`), which the A
circuit's signature rows target. The codec is in `GordieHowe/Applications/MLDSA44/Spec/Encoding.lean`, rounding in
`GordieHowe/Applications/MLDSA44/Spec/Rounding.lean` and the fixed-stream `SampleInBall` in `GordieHowe/Applications/MLDSA44/Spec/Sampler.lean`.
-/

namespace GordieHowe

namespace MLDSA44

/-- `GordieHowe.mldsa44`'s modulus, matrix shape, challenge weight and rounding constants
match the vendored `_root_.MLDSA.mldsa44` (and the scheme-wide `droppedBits`), the
parameter record the vendored concrete primitives are built at. -/
theorem mldsa44_matches :
    GordieHowe.mldsa44.q = _root_.MLDSA.modulus ∧
      GordieHowe.mldsa44.K = _root_.MLDSA.mldsa44.k ∧
      GordieHowe.mldsa44.L = _root_.MLDSA.mldsa44.l ∧
      GordieHowe.mldsa44.τ = _root_.MLDSA.mldsa44.tau ∧
      GordieHowe.mldsa44.γ₁ = _root_.MLDSA.mldsa44.gamma1 ∧
      GordieHowe.mldsa44.γ₂ = _root_.MLDSA.mldsa44.gamma2 ∧
      GordieHowe.mldsa44.β = _root_.MLDSA.mldsa44.beta ∧
      GordieHowe.mldsa44.ω = _root_.MLDSA.mldsa44.omega ∧
      GordieHowe.mldsa44.d = _root_.MLDSA.droppedBits := by
  decide

/-- FIPS 204 Algorithm 3's message representative
`M′ = IntegerToBytes(0, 1) ‖ IntegerToBytes(|ctx|, 1) ‖ ctx ‖ M`, over bytes. FIPS 204 takes the
message `M` as a bit string and forms `BytesToBits(0 ‖ |ctx| ‖ ctx) ‖ M`; for a byte-aligned message
this is the byte string above. The length byte is `|ctx| mod 256`; `VerifiesBytes` excludes a context
longer than 255 bytes, as Algorithm 3 does, so the reduction never applies there. -/
def frame (ctx msg : List UInt8) : List UInt8 := 0 :: ctx.length.toUInt8 :: (ctx ++ msg)

/-- **FIPS 204 Algorithm 8's checks at ML-DSA-44 with `Â` given**: the body of the vendored
`_root_.MLDSA.fipsVerify` at `concretePrimitives mldsa44`, with the matrix `aHat` in place of
`prims.expandA pk.rho` (`fipsVerify_eq_verifyChecks`). It computes `tr = H(pk)`,
`μ = H(tr ‖ M′)`, `c = SampleInBall(c̃)`, `w′ = NTT⁻¹(Â · NTT(z) − NTT(c) · NTT(t₁ · 2^d))`,
`w1 = UseHint(h, w′)` and accepts iff `‖z‖∞ < γ₁ − β`, `c̃ = H(μ ‖ w1Encode(w1))` and the hint
weight is at most `ω`. -/
def verifyChecks (aHat : _root_.MLDSA.TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l)
    (pk : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44))
    (msg : List UInt8) (sig : _root_.MLDSA.FIPSSignature _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44)) : Bool :=
  let prims := _root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44
  let tr := prims.hashPublicKey pk.rho pk.t1
  let mu := prims.hashMessage tr msg
  let c := prims.sampleInBall sig.cTilde
  let wApprox := _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 prims
    (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) aHat c sig.z pk.t1
  let w1' := prims.useHintVec sig.h wApprox
  let cTildeRecomputed := prims.hashCommitment mu (prims.w1Encode w1')
  decide (_root_.MLDSA.polyVecNorm sig.z < _root_.MLDSA.mldsa44.gamma1 - _root_.MLDSA.mldsa44.beta) &&
  decide (cTildeRecomputed = sig.cTilde) &&
  decide (prims.hintWeight sig.h ≤ _root_.MLDSA.mldsa44.omega)

/-- `verifyChecks` is the vendored `fipsVerify` with its own `Â = prims.expandA ρ`. -/
theorem fipsVerify_eq_verifyChecks (pk : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44))
    (msg : List UInt8) (sig : _root_.MLDSA.FIPSSignature _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44)) :
    _root_.MLDSA.fipsVerify _root_.MLDSA.mldsa44
        (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44) pk msg sig
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) =
      verifyChecks ((_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44).expandA pk.rho)
        pk msg sig :=
  rfl

/-- **ML-DSA-44 verification** (FIPS 204 Algorithm 8, `ML-DSA.Verify_internal`, after
`sigDecode`) of the semantic signature `sig` on the message representative `msg`: `ExpandA(ρ)`
finishes within `1008` SHAKE128 bytes per `RejNTTPoly` call (`ExpandAWithin`, at least the `894`
bytes FIPS 204 Appendix C, Table 3 requires of a bounded `RejNTTPoly`), `SampleInBall(c̃)`
finishes within the `272` SHAKE256 bytes of the vendored `sampleInBallPoly?` (`8` sign bytes and
`264` candidates, at least the `221` bytes FIPS 204 Appendix C, Table 3 requires of a bounded
`SampleInBall`), and the checks of Algorithm 8 accept at `Â = ExpandA(ρ)` (`verifyChecks` at
`expandAFull`). -/
structure Verifies (pk : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44))
    (msg : List UInt8) (sig : _root_.MLDSA.FIPSSignature _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44)) : Prop where
  /-- `ExpandA(ρ)` finishes within `1008` SHAKE128 bytes per `RejNTTPoly` call. -/
  expandA : ExpandAWithin _root_.MLDSA.mldsa44 pk.rho
  /-- `SampleInBall(c̃)` finishes within `272` SHAKE256 bytes. -/
  sampleInBall : (_root_.MLDSA.Concrete.sampleInBallPoly? _root_.MLDSA.mldsa44 sig.cTilde).isSome
  /-- Algorithm 8's checks accept at `Â = ExpandA(ρ)`. -/
  checks : verifyChecks (expandAFull _root_.MLDSA.mldsa44 pk.rho) pk msg sig = true

/-- **ML-DSA-44 verification of serialized signature bytes**, FIPS 204 Algorithm 3
`ML-DSA.Verify(pk, M, σ, ctx)`: the context is at most `255` bytes, the vendored `sigDecode`
(Algorithm 27) decodes `σ` to `(c̃, z, h)` (it returns `none` on a malformed hint), and
`Verifies` (Algorithm 8) holds on `frame ctx msg`. The public key is the vendored semantic
`PublicKey` (`ρ` and `t₁`), so Algorithm 8's `pkDecode` is not applied here. -/
structure VerifiesBytes (pk : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44))
    (ctx msg : List UInt8) (sigBytes : ByteArray) : Prop where
  /-- The context is at most `255` bytes. -/
  ctx_le : ctx.length ≤ 255
  /-- `σ` decodes to a signature that verifies on the message representative. -/
  decode : ∃ cTilde z h, _root_.MLDSA.Concrete.sigDecode _root_.MLDSA.mldsa44 sigBytes =
    some (cTilde, z, h) ∧ Verifies pk (frame ctx msg) ⟨cTilde, z, h⟩

/-- An encoded ML-DSA-44 public key, FIPS 204 `pkEncode(ρ, t₁)` (Algorithm 22):
`32 + 4 · 320 = 1312` bytes. -/
abbrev EncodedKey44 := Fin 1312 → UInt8

/-- FIPS 204 Algorithm 23 `pkDecode` at ML-DSA-44, as the vendored semantic key `(ρ, t₁)`: the
vendored `_root_.MLDSA.Concrete.pkDecode` on the 1312 bytes. It is total: `ρ` is bytes `[0, 32)`,
and `t₁[i]` is `SimpleBitUnpack` (Algorithm 18) of bytes `[32 + 320 i, 32 + 320 (i + 1))` with
the bound `2^(bitlen(q − 1) − d) − 1 = 2^10 − 1`, so every coefficient of `t₁` is below `2^10`
and the key is one FIPS 204 can encode. Irreducible: the proofs treat the decoded key as opaque,
and unfolding the 1312-byte decoder during unification is expensive. -/
@[irreducible] def pkDecode44 (b : EncodedKey44) :
    _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44) :=
  let d := _root_.MLDSA.Concrete.pkDecode _root_.MLDSA.mldsa44 ⟨Array.ofFn b⟩
  ⟨d.1, d.2⟩

/-- Every coefficient of the `t₁` the vendored `pkDecode` returns is below `2^10`, at every
parameter set: `pkDecode` unpacks each with `SimpleBitUnpack` at width
`bitlen(2^10 − 1) = 10`, and `2^10 < q`. -/
theorem pkDecode_t1_lt (p : _root_.MLDSA.Params) (bytes : ByteArray) (i : Fin p.k)
    (j : Fin _root_.MLDSA.ringDegree) :
    (((_root_.MLDSA.Concrete.pkDecode p bytes).2.get i).get j).val < 2 ^ 10 := by
  simp only [_root_.MLDSA.Concrete.pkDecode, _root_.MLDSA.Concrete.unpackPolyVector,
    Vector.get_ofFn, _root_.MLDSA.Concrete.polyT1Unpack]
  obtain ⟨v, hv, he⟩ := _root_.MLDSA.Concrete.simpleBitUnpackPoly_get _ _ j
  rw [he]
  have hw : _root_.MLDSA.Concrete.simpleWidth
      (2 ^ (Nat.log2 (_root_.MLDSA.modulus - 1) + 1 - _root_.MLDSA.droppedBits) - 1) = 10 := by
    decide
  rw [hw] at hv
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hv.trans (by decide))]
  exact hv

/-- **Every coefficient of a decoded ML-DSA-44 key's `t₁` is below `2^10`**: the key is one
FIPS 204 can encode. -/
theorem pkDecode44_t1_lt (b : EncodedKey44) (i : Fin _root_.MLDSA.mldsa44.k)
    (j : Fin _root_.MLDSA.ringDegree) : (((pkDecode44 b).t1.get i).get j).val < 2 ^ 10 := by
  unfold pkDecode44
  exact pkDecode_t1_lt _ _ i j

/-- Each centered coefficient of an ML-DSA vector is bounded by the vector's infinity norm. -/
theorem natAbs_centeredRepr_le_polyVecNorm {k : ℕ} (v : _root_.MLDSA.RqVec k) (j : Fin k)
    (i : Fin _root_.MLDSA.ringDegree) :
    (LatticeCrypto.centeredRepr ((v.get j).get i)).natAbs ≤ _root_.MLDSA.polyVecNorm v := by
  have h1 := LatticeCrypto.PolyVec.component_cInfNorm_le _root_.MLDSA.normOps v j
  have h2 : _root_.MLDSA.normOps.cInfNorm (v.get j) = LatticeCrypto.cInfNorm (v.get j) :=
    LatticeCrypto.zmodPolyNormOps_cInfNorm _
  rw [h2] at h1
  exact (LatticeCrypto.coeff_le_cInfNorm _ i).trans h1

/-- A vector whose centered coefficients are all below a positive `b` has infinity norm below
`b`. -/
theorem polyVecNorm_lt {k : ℕ} {v : _root_.MLDSA.RqVec k} {b : ℕ}
    (h : ∀ j i, (LatticeCrypto.centeredRepr ((v.get j).get i)).natAbs < b) (hb : 0 < b) :
    _root_.MLDSA.polyVecNorm v < b := by
  have hle : _root_.MLDSA.polyVecNorm v ≤ b - 1 := by
    rw [LatticeCrypto.PolyVec.cInfNorm_le_iff]
    intro j
    have h2 : _root_.MLDSA.normOps.cInfNorm (v.get j) = LatticeCrypto.cInfNorm (v.get j) :=
      LatticeCrypto.zmodPolyNormOps_cInfNorm _
    rw [h2]
    exact LatticeCrypto.cInfNorm_le_of_coeff_le fun i => Nat.le_sub_one_of_lt (h j i)
  omega

/-- A transform-domain dot product is the finite sum of the entrywise products. -/
theorem dot_eq_sum {k : ℕ} (row v : _root_.MLDSA.TqVec k) :
    _root_.MLDSA.Concrete.concreteNTTRingOps.dot row v = ∑ j : Fin k, _root_.MLDSA.Concrete.concreteNTTRingOps.mulHat (row.get j) (v.get j) := by
  unfold LatticeCrypto.TransformOps.dot
  have hz : Vector.zipWith _root_.MLDSA.Concrete.concreteNTTRingOps.mulHat row v =
      Vector.ofFn fun j => _root_.MLDSA.Concrete.concreteNTTRingOps.mulHat (row.get j) (v.get j) := by
    apply Vector.ext
    intro i hi
    simp [Vector.get]
  rw [hz, ← Vector.foldl_toList, Vector.toList_ofFn, ← List.sum_ofFn, List.sum_eq_foldl]

/-- `NTT⁻¹` distributes over a transform-domain dot product with `NTT(v)`, as the coefficient
domain sum `Σⱼ NTT⁻¹(rowⱼ) · vⱼ`. -/
theorem invNTT_dot_hatVec {k : ℕ} (row : _root_.MLDSA.TqVec k) (v : _root_.MLDSA.RqVec k) :
    _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat (_root_.MLDSA.Concrete.concreteNTTRingOps.dot row (_root_.MLDSA.Concrete.concreteNTTRingOps.hatVec v)) =
      ∑ j : Fin k, _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat (row.get j) * v.get j := by
  have := _root_.MLDSA.Concrete.concreteNTTRingLaws
  let F : _root_.MLDSA.Tq →+ _root_.MLDSA.Rq :=
    { toFun := _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
      map_zero' := by
        rw [← _root_.MLDSA.Concrete.concreteNTTRingLaws.toHat_zero, _root_.MLDSA.Concrete.concreteNTTRingLaws.fromHat_toHat]
        rfl
      map_add' := LatticeCrypto.TransformOps.fromHat_addHat _root_.MLDSA.Concrete.concreteNTTRingOps }
  rw [dot_eq_sum]
  change F _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat _ = _
  rw [LatticeCrypto.TransformOps.hatVec_get, ← _root_.MLDSA.Concrete.concreteNTTRingLaws.toHat_fromHat (row.get j),
    ← _root_.MLDSA.Concrete.concreteNTTRingLaws.toHat_mul, _root_.MLDSA.Concrete.concreteNTTRingLaws.fromHat_toHat,
    _root_.MLDSA.Concrete.concreteNTTRingLaws.fromHat_toHat]

/-- **`w′_approx` in ring form.** With the concrete NTT, `computeWApprox` (FIPS 204 Algorithm 8,
line 9) is `A·z − c·(t₁·2^d)` in `R_q`, row by row: component `i` is
`Σⱼ NTT⁻¹(Â[i][j]) · z[j] − c · power2RoundShift(t₁[i])`. -/
theorem computeWApprox_get (p : _root_.MLDSA.Params) (prims : _root_.MLDSA.Primitives p)
    (aHat : _root_.MLDSA.TqMatrix p.k p.l) (c : _root_.MLDSA.ChallengePoly)
    (z : _root_.MLDSA.RqVec p.l) (t1 : Vector prims.Power2High p.k) (i : Fin p.k) :
    (_root_.MLDSA.computeWApprox p prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) aHat c z t1).get i =
      ∑ j : Fin p.l, _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat ((aHat.get i).get j) * z.get j -
        c * prims.power2RoundShift (t1.get i) := by
  have := _root_.MLDSA.Concrete.concreteNTTRingLaws
  unfold _root_.MLDSA.computeWApprox
  rw [LatticeCrypto.TransformOps.unhatVec_sub, Vector.get_eq_getElem, Vector.getElem_sub, ← Vector.get_eq_getElem,
    ← Vector.get_eq_getElem, LatticeCrypto.TransformOps.unhatVec_get, LatticeCrypto.TransformOps.unhatVec_get]
  simp only [LatticeCrypto.TransformOps.matVecMul, LatticeCrypto.TransformOps.scalarVecMul, Vector.get_map,
    LatticeCrypto.TransformOps.hatVec_get, _root_.MLDSA.Primitives.power2RoundShiftVec]
  rw [invNTT_dot_hatVec, ← _root_.MLDSA.Concrete.concreteNTTRingLaws.toHat_mul, _root_.MLDSA.Concrete.concreteNTTRingLaws.fromHat_toHat]


/-- Reading coefficient `k` is additive. -/
def coeffHom (k : Fin _root_.MLDSA.ringDegree) : _root_.MLDSA.Rq →+ _root_.MLDSA.Coeff where
  toFun f := coeff f k
  map_zero' := _root_.MLDSA.Concrete.Rq.get_zero k
  map_add' f g := _root_.MLDSA.Concrete.Rq.get_add f g k

theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → _root_.MLDSA.Rq)
    (k : Fin _root_.MLDSA.ringDegree) : coeff (∑ j ∈ s, f j) k = ∑ j ∈ s, coeff (f j) k :=
  map_sum (coeffHom k) f s

theorem coeff_sub (f g : _root_.MLDSA.Rq) (k : Fin _root_.MLDSA.ringDegree) :
    coeff (f - g) k = coeff f k - coeff g k :=
  _root_.MLDSA.Concrete.Rq.get_sub f g k

/-- The concrete `power2RoundShift` multiplies every coefficient by `2^d`. -/
theorem coeff_power2RoundShift (x : _root_.MLDSA.Concrete.Power2High)
    (k : Fin _root_.MLDSA.ringDegree) :
    coeff (_root_.MLDSA.Concrete.power2RoundShift x) k =
      (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) * coeff x k := by
  change (_root_.MLDSA.Concrete.power2RoundShift x).get k = _ * x.get k
  simp [_root_.MLDSA.Concrete.power2RoundShift, _root_.MLDSA.Concrete.power2Scale]

/-- **`w′_approx` coefficientwise**, for the concrete primitives: coefficient `k` of component `i`
of `computeWApprox` is `Σⱼ (A[i][j] ⊛ z[j])ₖ − (c ⊛ 2^d·t₁[i])ₖ`, with `⊛` the negacyclic
convolution of coefficient vectors and `A[i][j] = NTT⁻¹(Â[i][j])`. -/
theorem coeff_computeWApprox (p : _root_.MLDSA.Params)
    (aHat : _root_.MLDSA.TqMatrix p.k p.l) (c : _root_.MLDSA.ChallengePoly)
    (z : _root_.MLDSA.RqVec p.l)
    (t1 : Vector (_root_.MLDSA.Concrete.concretePrimitives p).Power2High p.k) (i : Fin p.k)
    (k : Fin _root_.MLDSA.ringDegree) :
    coeff ((_root_.MLDSA.computeWApprox p (_root_.MLDSA.Concrete.concretePrimitives p)
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) aHat c z t1).get i) k =
      ∑ j : Fin p.l, LatticeCrypto.negacyclicConvCoeff
          (coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat ((aHat.get i).get j)))
          (coeff (z.get j)) k -
        LatticeCrypto.negacyclicConvCoeff (coeff c)
          (fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) * coeff (t1.get i) k') k := by
  rw [computeWApprox_get, coeff_sub, coeff_sum, coeff_mul]
  simp only [coeff_mul]
  congr 2
  funext k'
  exact coeff_power2RoundShift _ k'

end MLDSA44

end GordieHowe
