-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.ZMod.Basic
public import LatticeCrypto.MLDSA.Arithmetic
public import LatticeCrypto.Falcon.Arithmetic
public import LatticeCrypto.Ring.Norms

@[expose] public section

/-!
# Coefficient views of the vendored rings

Layer 0 for `R_q` is the vendored negacyclic ring (`Vendor/LatticeCrypto/Ring/*`,
instantiated per scheme by `Vendor/LatticeCrypto/MLDSA/Arithmetic.lean` and
`Vendor/LatticeCrypto/Falcon/Arithmetic.lean`), not a ring we define ourselves. The
gadgets and linear rows work coefficientwise, so this file exposes a thin coefficient
view on each scheme's carrier: `coeff` reads a ring element's coefficient vector,
`ofCoeff` builds a ring element from one, and multiplication is the negacyclic
convolution of coefficient vectors.

Both are wrappers around `LatticeCrypto.PolyBackend.coeff`/`.build`
(`Vendor/LatticeCrypto/Ring/Core.lean`) for the scheme's own backend
(`MLDSA.polyBackend`, `Falcon.polyBackend`), so `coeff_ofCoeff`/`ofCoeff_coeff` are
the backend's own round-trip laws, and `coeff_mul` is the backend's multiplication law
(`LatticeCrypto.vectorRing_mul_apply`, `LatticeCrypto.vectorKernel_mul_get`,
`Vendor/LatticeCrypto/Ring/VectorBackend.lean`) read off through `coeff`.

Centered representatives are the vendored `LatticeCrypto.centeredRepr`; norms are the
vendored `MLDSA.polyVecNorm` (infinity norm on ML-DSA vectors) and `Falcon.pairL2NormSq`
(squared ℓ₂ norm on a Falcon signature pair). Nothing here still needs an integer lift,
a norm, or a centered representative defined from scratch.
-/

namespace GordieHowe

namespace MLDSA44

/-- The coefficient vector of an ML-DSA ring element. Wraps the vendored
`MLDSA.polyBackend`'s `coeff` (`Vendor/LatticeCrypto/MLDSA/Arithmetic.lean`, itself
`Vendor/LatticeCrypto/Ring/VectorBackend.lean`'s `Poly.get`). -/
def coeff (f : _root_.MLDSA.Rq) : Fin _root_.MLDSA.ringDegree → _root_.MLDSA.Coeff :=
  _root_.MLDSA.polyBackend.coeff f

/-- The ML-DSA ring element with the given coefficient vector. Wraps the vendored
`MLDSA.polyBackend`'s `build`. -/
def ofCoeff (c : Fin _root_.MLDSA.ringDegree → _root_.MLDSA.Coeff) : _root_.MLDSA.Rq :=
  _root_.MLDSA.polyBackend.build c

theorem coeff_ofCoeff (c : Fin _root_.MLDSA.ringDegree → _root_.MLDSA.Coeff) :
    coeff (ofCoeff c) = c :=
  funext (_root_.MLDSA.polyBackend.coeff_build c)

theorem ofCoeff_coeff (f : _root_.MLDSA.Rq) : ofCoeff (coeff f) = f :=
  _root_.MLDSA.polyBackend.build_coeff f

/-- Multiplication in `MLDSA.Rq` is the negacyclic convolution of coefficient vectors
(`LatticeCrypto.negacyclicConvCoeff`, computed by `LatticeCrypto.negacyclicMulPure`). -/
theorem coeff_mul (a b : _root_.MLDSA.Rq) (i : Fin _root_.MLDSA.ringDegree) :
    coeff (a * b) i = LatticeCrypto.negacyclicConvCoeff (coeff a) (coeff b) i := by
  show (a * b).get i = LatticeCrypto.negacyclicConvCoeff a.get b.get i
  rw [LatticeCrypto.vectorRing_mul_apply]
  exact LatticeCrypto.vectorKernel_mul_get a b i

end MLDSA44

namespace Falcon512

/-- The coefficient vector of a Falcon ring element. Wraps the vendored
`Falcon.polyBackend`'s `coeff` (`Vendor/LatticeCrypto/Falcon/Arithmetic.lean`). -/
def coeff {n : ℕ} (f : _root_.Falcon.Rq n) : Fin n → _root_.Falcon.Coeff :=
  (_root_.Falcon.polyBackend n).coeff f

/-- The Falcon ring element with the given coefficient vector. Wraps the vendored
`Falcon.polyBackend`'s `build`. -/
def ofCoeff {n : ℕ} (c : Fin n → _root_.Falcon.Coeff) : _root_.Falcon.Rq n :=
  (_root_.Falcon.polyBackend n).build c

theorem coeff_ofCoeff {n : ℕ} (c : Fin n → _root_.Falcon.Coeff) : coeff (ofCoeff c) = c :=
  funext ((_root_.Falcon.polyBackend n).coeff_build c)

theorem ofCoeff_coeff {n : ℕ} (f : _root_.Falcon.Rq n) : ofCoeff (coeff f) = f :=
  (_root_.Falcon.polyBackend n).build_coeff f

/-- Reducing an integer polynomial modulo the Falcon coefficient modulus and
then reading a coefficient recovers the corresponding integer cast. -/
theorem intPoly_toRq_coeff {n : ℕ} (f : _root_.Falcon.IntPoly n) (i : Fin n) :
    coeff f.toRq i = (f.get i : _root_.Falcon.Coeff) := by
  unfold _root_.Falcon.IntPoly.toRq _root_.Falcon.integralLift
    LatticeCrypto.vectorIntegralLift LatticeCrypto.PolyBackend.mapCoeffs coeff
  simp

/-- The squared norm of a pair sums the squared centered magnitudes of the
concatenated coefficient vector `coeff s₁ ‖ coeff s₂`. -/
theorem pairL2NormSq_eq_sum_append {n : ℕ} (s₁ s₂ : _root_.Falcon.Rq n) :
    _root_.Falcon.pairL2NormSq s₁ s₂ = ∑ i : Fin (n + n),
      (LatticeCrypto.centeredRepr (Fin.append (coeff s₁) (coeff s₂) i)).natAbs ^ 2 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rfl

/-- Multiplication in `Falcon.Rq n` is the negacyclic convolution of coefficient
vectors. -/
theorem coeff_mul {n : ℕ} (a b : _root_.Falcon.Rq n) (i : Fin n) :
    coeff (a * b) i = LatticeCrypto.negacyclicConvCoeff (coeff a) (coeff b) i := by
  show (a * b).get i = LatticeCrypto.negacyclicConvCoeff a.get b.get i
  rw [LatticeCrypto.vectorRing_mul_apply]
  exact LatticeCrypto.vectorKernel_mul_get a b i

/-- `negacyclicConvCoeff` is symmetric in its two coefficient vectors: reindexing
the defining sum over `Fin n × Fin n` by the swap equivalence turns one argument
order into the other. -/
theorem negacyclicConvCoeff_comm {R : Type*} [CommRing R] {n : ℕ} (f g : Fin n → R)
    (k : Fin n) :
    LatticeCrypto.negacyclicConvCoeff f g k = LatticeCrypto.negacyclicConvCoeff g f k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  apply Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n))
  rintro ⟨i, j⟩
  simp only [Equiv.prodComm_apply, Prod.swap, add_comm (j : ℕ) (i : ℕ), mul_comm (g j) (f i)]

/-- Multiplication in `Falcon.Rq n` commutes, for every degree `n`. The vendored
`CommRing` instance is defined by cases on `n`, so its `mul_comm` applies only
at a numeral degree; this lemma is stated for the ring's own multiplication. -/
theorem mul_comm {n : ℕ} (a b : _root_.Falcon.Rq n) : a * b = b * a := by
  rw [← ofCoeff_coeff (a * b), ← ofCoeff_coeff (b * a)]
  congr 1
  funext i
  rw [coeff_mul, coeff_mul, negacyclicConvCoeff_comm]

end Falcon512

end GordieHowe
