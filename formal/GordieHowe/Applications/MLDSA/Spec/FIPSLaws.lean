-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Spec.ExpandMask
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1

@[expose] public section

/-!
# The laws of the FIPS 204 concrete primitives

The signing laws, the verification laws and the commitment encoding at `concretePrimitivesFIPS`
(the vendored concrete primitives with the FIPS 204 `ExpandS` and `ExpandMask`), transported from
those at `concretePrimitivesKeyGen` through the abstract-bundle lemmas of `ExpandMask.lean`.

* `VerifyLaws.withExpandMask`: replacing `expandMask` in an abstract bundle keeps the
  verification laws.
* `signingLaws_concreteFIPS`, `verifyLaws_concreteFIPS`: the signing and verification laws, at
  every approved parameter set.
* `concreteEnc_highBitsVec_fips`: the concrete encoding of `HighBits` is coherent with
  `bucketsOf`.
-/

namespace GordieHowe.MLDSA.Spec

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.Ring.MLDSAW1

attribute [local instance] concreteNTTRingOps

/-- **Replacing `ExpandMask` keeps the verification laws**: none of the three fields reads
`expandMask`. -/
theorem _root_.GordieHowe.MLDSA.VerifyLaws.withExpandMask {p : Params} [NTTRingOps]
    {P : Primitives p} (h : VerifyLaws P) (eM : Bytes 64 → ℕ → RqVec p.l) :
    VerifyLaws (withExpandMask P eM) :=
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩

/-- **The concrete primitives with the FIPS 204 `ExpandS` and `ExpandMask` satisfy the signing
laws** at every approved parameter set (`signingLaws_concreteKeyGen`; the laws do not read
`expandMask`). -/
theorem signingLaws_concreteFIPS (p : Params) (hp : p.isApproved) :
    SigningLaws (concretePrimitivesFIPS p) (nttOps := concreteNTTRingOps) :=
  (signingLaws_concreteKeyGen p hp).withExpandMask (expandMask p)

/-- **The concrete primitives with the FIPS 204 `ExpandS` and `ExpandMask` satisfy the
verification laws** at every approved parameter set (`verifyLaws_concreteKeyGen`; the laws do not
read `expandMask`). -/
theorem verifyLaws_concreteFIPS {p : Params} (hp : p.isApproved) :
    VerifyLaws (concretePrimitivesFIPS p) (nttOps := concreteNTTRingOps) :=
  (verifyLaws_concreteKeyGen hp).withExpandMask (expandMask p)

/-- **The concrete encoding is coherent with `bucketsOf`** at the primitives with the FIPS 204
`ExpandS` and `ExpandMask`, at every approved parameter set (`concreteEnc_highBitsVec_keyGen`). -/
theorem concreteEnc_highBitsVec_fips {p : Params} [NeZero (bucketCount p)] (hp : p.isApproved)
    (w : RqVec p.k) :
    concreteEnc p ((concretePrimitivesFIPS p).highBitsVec w) = bucketsOf (rqVecCoeffs w) :=
  concreteEnc_highBitsVec_keyGen hp w

end GordieHowe.MLDSA.Spec
