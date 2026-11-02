-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.NTTLoop
import all LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# The vendored ML-DSA NTT of a product, coefficientwise

The NTT of a product of two polynomials of `R_q` is the pointwise product of their NTTs
(`ntt_mul_get`), and the inverse transform of `concreteNTTRingOps` is the vendored `invNTT`
(`fromHat_eq`): the vendored law `toHat_mul` of `concreteNTTRingOps` (FIPS 204's
`MultiplyNTTs`, Algorithm 45) with the pointwise kernel `loopMultiplyNTTs`
(`GordieHowe.MLDSA44.NTTLoop.multiplyNTTs_eq_loopMultiplyNTTs`). This is a Lean module so that it
can `import all` the vendored file, whose `concreteNTTRingOps` and `loopMultiplyNTTs` are not
exposed.
-/

namespace GordieHowe.MLDSA44.Ring.Native

/-- **The pointwise product kernel** (`loopMultiplyNTTs`, FIPS 204 Algorithm 45) reads the
products of the coefficients. -/
theorem loopMultiplyNTTs_get (a b : _root_.MLDSA.Tq) (k : Fin _root_.MLDSA.ringDegree) :
    (_root_.MLDSA.Concrete.loopMultiplyNTTs a b).coeffs.get k = a.coeffs.get k * b.coeffs.get k := by
  unfold _root_.MLDSA.Concrete.loopMultiplyNTTs
  exact Vector.get_ofFn _ k

/-- **The NTT of a product** is the pointwise product of the NTTs (`toHat_mul`, the pointwise
`MultiplyNTTs` of FIPS 204 Algorithm 45). -/
theorem ntt_mul_get (f g : _root_.MLDSA.Rq) (k : Fin _root_.MLDSA.ringDegree) :
    (_root_.MLDSA.Concrete.ntt (f * g)).coeffs.get k =
      (_root_.MLDSA.Concrete.ntt f).coeffs.get k * (_root_.MLDSA.Concrete.ntt g).coeffs.get k := by
  have h : _root_.MLDSA.Concrete.ntt (f * g) = _root_.MLDSA.Concrete.multiplyNTTs
      (_root_.MLDSA.Concrete.ntt f) (_root_.MLDSA.Concrete.ntt g) :=
    _root_.MLDSA.Concrete.concreteNTTRingLaws.toHat_mul f g
  rw [h, MLDSA44.NTTLoop.multiplyNTTs_eq_loopMultiplyNTTs, loopMultiplyNTTs_get]

/-- **The concrete inverse transform of the NTT ring operations** is the vendored `invNTT`. -/
theorem fromHat_eq (x : _root_.MLDSA.Tq) :
    _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat x = _root_.MLDSA.Concrete.invNTT x := by
  rfl

end GordieHowe.MLDSA44.Ring.Native
