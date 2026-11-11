-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Frontend.Shared

@[expose] public section

/-!
# FIPS 204 verification from Algorithm 8's parts, on a message representative

The ring statements' verification is the vendored bounded verifier `MLDSA.Concrete.verify`
(FIPS 204 Algorithm 8 with the bounded `ExpandA` and `SampleInBall` of Appendix C) on the message
representative `M′` itself (`GordieHowe/Applications/MLDSA44/Ring/Scheme.lean`), where the
proofs of possession verify serialized signatures at a framed message
(`GordieHowe.MLDSA44.verifiesBytes_of_parts`). Contents:

* `verifies_of_parts`: `MLDSA44.Verifies` on a message representative from the verifier's parts
  (the body of `verifiesBytes_of_parts`, without the framing and the encoding).
* `verify_of_verifies`: `MLDSA44.Verifies` gives `MLDSA.Concrete.verify`: the bounded `ExpandA`
  succeeds within the byte budget (`expandA?_eq_of_within`) with the matrix `expandAFull`
  (`expandA_eq_expandABounded`, `expandABounded_eq_expandAFull`).
-/

namespace GordieHowe.MLDSA44

open _root_.MLDSA.Concrete (useHintCoeff)

/-- **FIPS 204 Algorithm 8 accepts from its parts** on the message representative `msg`: at a key
whose `ExpandA` finishes within the byte budget, with `c` the fixed-stream `SampleInBall` of
`SHAKE256(c̃)` (`C ≤ 264` candidates), `W = computeWApprox(Â, c, z, t1)`, `w1 = UseHint(h, W)`,
`c̃` the commitment hash of `μ = H(tr ‖ msg)` and `w1Encode(w1)`, `‖z‖∞ < γ₁ − β` and the hint
weight at most `ω`, `MLDSA44.Verifies` holds for `(c̃, z, h)`. -/
theorem verifies_of_parts {C : ℕ} {pk : PublicKey44} {msg : List UInt8}
    {cTilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44} {c : Fin mldsa44.N → ℤ}
    {z W : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l}
    {h : Vector _root_.MLDSA.Concrete.Hint _root_.MLDSA.mldsa44.k}
    {w1 : Vector _root_.MLDSA.Concrete.High _root_.MLDSA.mldsa44.k}
    (hC : C ≤ _root_.MLDSA.Concrete.sampleInBallCandidateBudget)
    (hexp : ExpandAWithin _root_.MLDSA.mldsa44 pk.rho)
    (hball : fixedStreamChallenge mldsa44
      (xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (C + 8)) = some c)
    (hW : _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk)
      (ofCoeff fun k => (c k : _root_.MLDSA.Coeff)) z pk.t1 = W)
    (huse : Native.Rows.prims.useHintVec h W = w1)
    (hcommit : _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1) msg)
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 w1) = cTilde)
    (hnorm : ∀ j k,
      (LatticeCrypto.centeredRepr ((z.get j).get k)).natAbs < mldsa44.normBound)
    (hwt : Native.Rows.prims.hintWeight h ≤ _root_.MLDSA.mldsa44.omega) :
    Verifies pk msg ⟨cTilde, z, h⟩ := by
  have hball? := fixedStreamChallenge_agree hC hball
  have hball' := fixedStreamChallenge_agree_prims hC hball
  refine ⟨hexp, by rw [SampleInBallWithin, hball?]; rfl, ?_⟩
  unfold verifyChecks
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨polyVecNorm_lt hnorm (by decide), ?_⟩, hwt⟩
  erw [hball', hW, huse]
  exact hcommit

/-- **`MLDSA44.Verifies` is the vendored bounded verifier's acceptance** (`MLDSA.Concrete.verify`):
within the byte budget the bounded `ExpandA` succeeds (`expandA?_eq_of_within`) and the vendored
`ExpandA` is `expandAFull` (`expandA_eq_expandABounded`, `expandABounded_eq_expandAFull`), so
the vendored `fipsVerify` is the checks at `expandAFull` (`fipsVerify_eq_verifyChecks`). -/
theorem verify_of_verifies
    {pk : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44)}
    {msg : List UInt8} {sig : _root_.MLDSA.FIPSSignature _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44)}
    (h : Verifies pk msg sig) :
    _root_.MLDSA.Concrete.verify _root_.MLDSA.mldsa44 pk msg sig = true := by
  have hA : (_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44).expandA pk.rho =
      expandAFull _root_.MLDSA.mldsa44 pk.rho := by
    rw [← expandABounded_eq_expandAFull h.expandA, ← expandA_eq_expandABounded h.expandA]
    rfl
  unfold _root_.MLDSA.Concrete.verify
  rw [expandA?_eq_of_within h.expandA, h.sampleInBall, fipsVerify_eq_verifyChecks, hA, h.checks]
  rfl

end GordieHowe.MLDSA44
