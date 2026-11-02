-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Flatten
public import GordieHowe.Applications.MLDSA.Signing.MLWE
public import GordieHowe.Applications.MLDSA.Signing.Surrogate
public import GordieHowe.Applications.MLDSA.Spec.ExpandS
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The hybrid key law and the MLWE hop on an event of `t₀`

In the hybrid key law, `t` is uniform on `R_q^k` (`hybridKeyLaw`) in place of the ML-DSA public
key `t = Â·s₁ + s₂`, and `t₀` is the low part of `(t₁, t₀) = Power2Round(t)` (FIPS 204
Algorithm 35; `t0Of`).

* `hybridKeyLaw_toReal`, `sum_hybridKeyLaw_eq`: the hybrid key law is the product of uniform
  coefficient laws, so an average over it that reads `t` through its coefficients is an average
  over independent uniform coefficients.
* `atypicalTest atyp` (`B_typ`): on an MLWE instance `(Â, t)`, the indicator of an event `atyp`
  of `t₀`. Its uniform mean is the hybrid probability `hybridEventProb p atyp`
  (`mlweUniformMean_atypicalTest`).
* `mlweRealMean_atypicalTest_le` (the MLWE hop on `B_typ`): with real keys, the probability of
  `atyp(t₀)` is at most `hybridEventProb p atyp + Adv^MLWE_S(B_typ)`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto TransformOps Finset

/-! ### The hybrid key -/

section Hybrid

variable (p : Params)

/-- **The hybrid key law**: `t` uniform on `R_q^k`, in place of `t = Â·s₁ + s₂` (the MLWE
hop). -/
noncomputable def hybridKeyLaw : PMF (RqVec p.k) :=
  PMF.uniformOfFintype (RqVec p.k)

/-- `t₀` of `t`: the low part of `(t₁, t₀) = Power2Round(t)`, as in `keyGenFromSeed`. -/
def t0Of (t : RqVec p.k) : RqVec p.k :=
  ((Spec.concretePrimitivesKeyGen p).power2RoundVec t).2

/-- The hybrid key law is the product of uniform coefficient laws. -/
theorem hybridKeyLaw_toReal (t : RqVec p.k) :
    (hybridKeyLaw p t).toReal = ∏ _x : CoeffIndex p, (1 / (modulus : ℝ)) := by
  rw [hybridKeyLaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_congr (rqVecCoeffEquiv p.k), Fintype.card_fun, ZMod.card, prod_const,
    card_univ, Nat.cast_pow, one_div, inv_pow]

/-- An average over the hybrid key law that reads `t` through its coefficients is an average
over independent uniform coefficients. -/
theorem sum_hybridKeyLaw_eq (G : (CoeffIndex p → Coeff) → ℝ) :
    ∑ t, (hybridKeyLaw p t).toReal * G (rqVecCoeffs t) =
      ∑ f : CoeffIndex p → Coeff, (∏ x, (fun _ : Coeff => 1 / (modulus : ℝ)) (f x)) * G f := by
  refine Fintype.sum_equiv (rqVecCoeffEquiv p.k) _ _ fun t => ?_
  rw [hybridKeyLaw_toReal]
  rfl

end Hybrid

/-! ### The MLWE hop on an event of `t₀` -/

section Hop

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- **`B_typ`**: on an MLWE instance `(Â, t)`, the indicator of an event `atyp` of `t₀`. -/
def atypicalTest (atyp : RqVec p.k → Prop) [DecidablePred atyp] :
    TqMatrix p.k p.l → RqVec p.k → ℝ :=
  fun _ t => if atyp (t0Of p t) then 1 else 0

omit nttOps in
/-- `B_typ` outputs a probability. -/
theorem atypicalTest_mem_Icc (atyp : RqVec p.k → Prop) [DecidablePred atyp]
    (A : TqMatrix p.k p.l) (t : RqVec p.k) : atypicalTest p atyp A t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold atypicalTest
  split <;> norm_num

/-- **The probability of `atyp` in the hybrid**: `Pr_{t uniform}[atyp(t₀)]`. -/
noncomputable def hybridEventProb (atyp : RqVec p.k → Prop) [DecidablePred atyp] : ℝ :=
  ∑ t, (hybridKeyLaw p t).toReal * if atyp (t0Of p t) then 1 else 0

omit nttOps in
/-- The uniform mean of `B_typ` is the hybrid probability of `atyp`. -/
theorem mlweUniformMean_atypicalTest (atyp : RqVec p.k → Prop) [DecidablePred atyp] :
    mlweUniformMean (atypicalTest p atyp) = hybridEventProb p atyp := by
  unfold atypicalTest
  rw [mlweUniformMean_of_vector, hybridEventProb]
  rfl

/-- **The MLWE hop on `B_typ`**: with real keys, the probability of `atyp(t₀)` is at most its
hybrid probability plus `Adv^MLWE_S(B_typ)`. -/
theorem mlweRealMean_atypicalTest_le (S : PMF (RqVec p.l × RqVec p.k))
    (atyp : RqVec p.k → Prop) [DecidablePred atyp] :
    mlweRealMean S (atypicalTest p atyp) ≤
      hybridEventProb p atyp + mlweAdvantage S (atypicalTest p atyp) := by
  have h := abs_mlweRealMean_sub_mlweUniformMean_le S (atypicalTest p atyp)
  rw [mlweUniformMean_atypicalTest] at h
  linarith [le_abs_self (mlweRealMean S (atypicalTest p atyp) - hybridEventProb p atyp)]

end Hop

end GordieHowe.MLDSA
