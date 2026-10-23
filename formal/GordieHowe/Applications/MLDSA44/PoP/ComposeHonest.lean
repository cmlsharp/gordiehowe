-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.PoP.Compose

@[expose] public section

/-!
# The honest ML-DSA-44 commitment values

The specification values an honest ML-DSA-44 prover computes from the public key, the challenge
coefficients `c`, the response `z` and the hint `h`: `honestWApprox` is
`w′ = A·z − c·t₁·2^d`, `honestW1` is `w1 = UseHint(h, w′)` coefficientwise, and
`honestW1Bytes` is `w1Encode(w1)`. `coeff_honestW1` reads `honestW1` coefficientwise and
`useHintVec_honestWApprox` identifies it with the vendored `useHintVec`. None of these reads
`c̃`.
-/

namespace GordieHowe

open _root_.MLDSA.Concrete (concretePrimitives concreteNTTRingOps High Hint useHintCoeff w1Encode)

namespace MLDSA44.PoP.Compose

/-- `w′ = A·z − c·t₁·2^d` for the challenge coefficients `c` (FIPS 204 Algorithm 8, line 9, with
`Â = ExpandA(ρ)`, unbounded: `MLDSA44.expandAFull`). -/
-- spec-side
noncomputable def honestWApprox (pk : MLDSA44.PublicKey44) (c : Fin mldsa44.N → ℤ)
    (z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k :=
  _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 (concretePrimitives _root_.MLDSA.mldsa44)
    (nttOps := concreteNTTRingOps) (MLDSA44.expandAFull _root_.MLDSA.mldsa44 pk.rho)
    (MLDSA44.ofCoeff fun k => (c k : _root_.MLDSA.Coeff)) z pk.t1

/-- `w1 = UseHint(h, w′)`, coefficientwise. -/
-- spec-side
noncomputable def honestW1 (pk : MLDSA44.PublicKey44) (c : Fin mldsa44.N → ℤ)
    (z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l) (h : Vector Hint _root_.MLDSA.mldsa44.k) :
    Vector High _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun k =>
    (useHintCoeff ((h.get i).get k) (MLDSA44.coeff ((honestWApprox pk c z).get i) k)
      _root_.MLDSA.mldsa44.gamma2 : _root_.MLDSA.Coeff)

theorem coeff_honestW1 (pk : MLDSA44.PublicKey44) (c : Fin mldsa44.N → ℤ)
    (z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l) (h : Vector Hint _root_.MLDSA.mldsa44.k)
    (i : Fin _root_.MLDSA.mldsa44.k) (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff ((honestW1 pk c z h).get i) k =
      (useHintCoeff ((h.get i).get k) (MLDSA44.coeff ((honestWApprox pk c z).get i) k)
        _root_.MLDSA.mldsa44.gamma2 : _root_.MLDSA.Coeff) := by
  rw [honestW1, Vector.get_ofFn, MLDSA44.coeff_ofCoeff]

/-- The vendored `UseHint` of `honestWApprox` is `honestW1`. -/
theorem useHintVec_honestWApprox (pk : MLDSA44.PublicKey44) (c : Fin mldsa44.N → ℤ)
    (z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l) (h : Vector Hint _root_.MLDSA.mldsa44.k) :
    (concretePrimitives _root_.MLDSA.mldsa44).useHintVec h (honestWApprox pk c z) =
      honestW1 pk c z h :=
  useHintVec_eq_of_get (fun _ k => (MLDSA44.coeff_apply _ k).symm) (coeff_honestW1 pk c z h)

/-- The `768` bytes `w1Encode(w1)` of `honestW1`. -/
-- spec-side
noncomputable def honestW1Bytes (pk : MLDSA44.PublicKey44) (c : Fin mldsa44.N → ℤ)
    (z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l) (h : Vector Hint _root_.MLDSA.mldsa44.k) :
    Fin 768 → UInt8 :=
  fun p => (w1Encode _root_.MLDSA.mldsa44 (honestW1 pk c z h)).getD p 0

end MLDSA44.PoP.Compose

end GordieHowe
