-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Circuits.Hash
public import GordieHowe.Applications.MLDSA44.Spec.Rounding
public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Applications.Configuration.Witness

@[expose] public section

/-!
# ML-DSA-44 proof-of-possession helpers

`GordieHowe.MLDSA44.PublicKey44` is the vendored semantic ML-DSA-44 public key `(ρ, t₁)`. `trOf` computes
`tr = H(pk)` from it, as the FIPS 204 verifier does. `useHintVec_eq_of_get` lifts a
coefficientwise UseHint fact `w1 = UseHint(h, w′)` to the vendored vector `useHintVec`.
-/

namespace GordieHowe

open _root_.MLDSA.Concrete (concretePrimitives concreteNTTRingOps High Hint hintWeightVec
  useHintCoeff sigEncode)

/-- The ML-DSA-44 public key: the vendored semantic key `(ρ, t₁)`. -/
abbrev MLDSA44.PublicKey44 :=
  _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (concretePrimitives _root_.MLDSA.mldsa44)

namespace MLDSA44.PoP.Compose

variable {K F WitA MsgA : Type} [Field K] [DecidableEq K] [Field F] [DecidableEq F] {mw : ℕ} {taps : Finset ℕ}
  {B : Conv.ConvBasis mw taps K} [mldsa44.MACWidth mw]

/-- `tr = H(pk)`, which the verifier computes from the public key. -/
-- spec-side
def trOf (pk : MLDSA44.PublicKey44) : Fin 64 → UInt8 :=
  ((concretePrimitives _root_.MLDSA.mldsa44).hashPublicKey pk.rho pk.t1).get

/-- `UseHint(h, W) = w1` for a vector `W` whose coefficients are `w′`, when `w1` is
`UseHint(h, w′)` coefficientwise. -/
theorem useHintVec_eq_of_get {h : Vector Hint _root_.MLDSA.mldsa44.k}
    {W : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k} {w1 : Vector High _root_.MLDSA.mldsa44.k}
    {wApprox : Fin _root_.MLDSA.mldsa44.k → Fin _root_.MLDSA.ringDegree → _root_.MLDSA.Coeff}
    (hW : ∀ i k, (W.get i).get k = wApprox i k)
    (hu : ∀ i k, MLDSA44.coeff (w1.get i) k =
      ((useHintCoeff ((h.get i).get k) (wApprox i k) _root_.MLDSA.mldsa44.gamma2 : ℕ) :
        _root_.MLDSA.Coeff)) :
    (concretePrimitives _root_.MLDSA.mldsa44).useHintVec h W = w1 := by
  have hcoeff : ∀ i k, MLDSA44.coeff (_root_.MLDSA.Concrete.useHint _root_.MLDSA.mldsa44 (h.get i)
      (W.get i)) k = MLDSA44.coeff (w1.get i) k := fun i k => by
    rw [MLDSA44.coeff_useHint_eq, hu i k, hW i k]
  have hpoly : ∀ i, _root_.MLDSA.Concrete.useHint _root_.MLDSA.mldsa44 (h.get i) (W.get i) = w1.get i :=
    fun i => (MLDSA44.ofCoeff_coeff _).symm.trans
      ((congrArg MLDSA44.ofCoeff (funext (hcoeff i))).trans (MLDSA44.ofCoeff_coeff _))
  apply Vector.ext
  intro i hi
  unfold _root_.MLDSA.Primitives.useHintVec
  erw [Vector.getElem_zipWith]
  have := hpoly ⟨i, hi⟩
  simp only [Vector.get_eq_getElem] at this
  exact this

end MLDSA44.PoP.Compose

end GordieHowe
