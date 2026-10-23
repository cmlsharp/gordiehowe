-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebra
public import GordieHowe.Model.IOP.PadMasked

@[expose] public section

/-!
# Honest advice for the intended emulated Falcon A circuit

All definitions in this file are witness generation by the prover, not circuit
operations. `witness` is independent of every verifier challenge; `response`
depends on Kmac but not the later lookup challenge. Encoding bounds are honest
signature input conditions here, never premises of circuit soundness.
Everything is generic over the scheme parameters `P` and the emulated arm `A`;
the public key is a ring element `h : Falcon.Rq P.n`.
-/

namespace GordieHowe.Falcon512.EmulatedAlgebraCircuit.Honest

variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [DecidableEq F]
  {P : Params}

/-- The verifier's reconstructed first signature polynomial `c − s₂·h`. -/
-- spec-side
def s₁Poly (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ) (s₂ : _root_.Falcon.IntPoly P.n) :
    _root_.Falcon.Rq P.n :=
  Falcon512.ofCoeff (fun i => (c i : _root_.Falcon.Coeff)) - s₂.toRq * h

/-- Canonical coefficients of the reconstructed `s₁`. -/
-- spec-side
def s₁Coeffs (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ) (s₂ : _root_.Falcon.IntPoly P.n) :
    Fin P.n → ℕ :=
  fun i => (Falcon512.coeff (s₁Poly h c s₂) i).val

/-- Canonical residues of the `s₂` coefficients, the values committed in the
signature rows. -/
-- spec-side
def s₂Coeffs (s₂ : _root_.Falcon.IntPoly P.n) : Fin P.n → ℕ :=
  fun i => (Falcon512.coeff s₂.toRq i).val

/-- `keyCoeffs` reads the same coefficient as `Falcon512.coeff` of the public key. -/
theorem keyCoeffs_eq (h : _root_.Falcon.Rq P.n) (i : Fin P.n) :
    (keyCoeffs h i : _root_.Falcon.Coeff) = Falcon512.coeff h i :=
  ZMod.natCast_zmod_val _

/-- `s₂Coeffs` reads the same coefficient as `Falcon512.coeff` of `s₂.toRq`. -/
theorem s₂Coeffs_eq (s₂ : _root_.Falcon.IntPoly P.n) (i : Fin P.n) :
    (s₂Coeffs s₂ i : _root_.Falcon.Coeff) = Falcon512.coeff s₂.toRq i :=
  ZMod.natCast_zmod_val _

/-- `s₁Coeffs` reads the same coefficient as `Falcon512.coeff` of `s₁Poly`. -/
theorem s₁Coeffs_eq (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly P.n) (i : Fin P.n) :
    (s₁Coeffs h c s₂ i : _root_.Falcon.Coeff) = Falcon512.coeff (s₁Poly h c s₂) i :=
  ZMod.natCast_zmod_val _

/-- `s₁Poly`'s coefficients: `c − h·s₂` in `R_q`, expanded via the coefficient view. -/
theorem s₁Poly_coeff_eq (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly P.n) (i : Fin P.n) :
    Falcon512.coeff (s₁Poly h c s₂) i =
      (c i : _root_.Falcon.Coeff) -
        LatticeCrypto.negacyclicConvCoeff (Falcon512.coeff h) (Falcon512.coeff s₂.toRq) i := by
  unfold s₁Poly Falcon512.coeff
  rw [LatticeCrypto.NegacyclicRing.coeff_sub (Falcon.coeffRing P.n)]
  change Falcon512.coeff (Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff)) i -
      Falcon512.coeff (s₂.toRq * h) i = _
  rw [Falcon512.coeff_ofCoeff, Falcon512.coeff_mul, Falcon512.negacyclicConvCoeff_comm]
  rfl

/-- The honest operands satisfy the row congruence: `s₁` is defined as
`c − s₂·h` in `R_q`. `hq` is a parameter condition. -/
theorem congruent_honest (hq : P.q = _root_.Falcon.modulus) (h : _root_.Falcon.Rq P.n)
    (c : Fin P.n → ℕ) (s₂ : _root_.Falcon.IntPoly P.n) :
    Emulated.Rows.Congruent P.q (keyCoeffs h) c (s₁Coeffs h c s₂) (s₂Coeffs s₂) := by
  unfold Emulated.Rows.Congruent
  rw [hq]
  intro i
  change (c i : _root_.Falcon.Coeff) =
      (s₁Coeffs h c s₂ i : _root_.Falcon.Coeff) +
        LatticeCrypto.negacyclicConvCoeff
          (fun j => (keyCoeffs h j : _root_.Falcon.Coeff))
          (fun j => (s₂Coeffs s₂ j : _root_.Falcon.Coeff)) i
  simp only [keyCoeffs_eq, s₂Coeffs_eq, s₁Coeffs_eq, s₁Poly_coeff_eq]
  exact (sub_add_cancel _ _).symm

/-- Residues of `s₁ ‖ s₂`, the values read by the norm check, indexed like its
inputs. -/
-- spec-side
def normResidues (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ) (s₂ : _root_.Falcon.IntPoly P.n)
    (i : Fin (2 * P.n)) : _root_.Falcon.Coeff :=
  Fin.append (Falcon512.coeff (s₁Poly h c s₂)) (Falcon512.coeff s₂.toRq) (Fin.cast (two_mul P.n) i)

/-- The first half of the norm residues is `s₁`. -/
theorem normResidues_of_lt (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly P.n) {i : Fin (2 * P.n)} (hi : (i : ℕ) < P.n) :
    normResidues h c s₂ i = Falcon512.coeff (s₁Poly h c s₂) ⟨i, hi⟩ := by
  unfold normResidues
  rw [show Fin.cast (two_mul P.n) i = Fin.castAdd P.n ⟨i, hi⟩ from Fin.ext rfl, Fin.append_left]

/-- The second half of the norm residues is `s₂`. -/
theorem normResidues_of_not_lt (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly P.n) {i : Fin (2 * P.n)} (hi : ¬ (i : ℕ) < P.n) :
    normResidues h c s₂ i = Falcon512.coeff s₂.toRq ⟨i - P.n, by omega⟩ := by
  unfold normResidues
  rw [show Fin.cast (two_mul P.n) i = Fin.natAdd P.n ⟨i - P.n, by omega⟩ from
    Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega), Fin.append_right]

/-- The honest squared norm is the sum over the norm check's residues. -/
theorem pairL2NormSq_eq_normResidues (h : _root_.Falcon.Rq P.n) (c : Fin P.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly P.n) :
    _root_.Falcon.pairL2NormSq (s₁Poly h c s₂) s₂.toRq =
      ∑ i, (LatticeCrypto.centeredRepr (normResidues h c s₂ i)).natAbs ^ 2 := by
  rw [Falcon512.pairL2NormSq_eq_sum_append]
  exact Fintype.sum_equiv (finCongr (two_mul P.n).symm) _ _ (fun _ => rfl)

end GordieHowe.Falcon512.EmulatedAlgebraCircuit.Honest
