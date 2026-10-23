-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.GKR.Transcript
public import Mathlib.Algebra.MvPolynomial.Degrees
public import GordieHowe.Foundations.Algebra.AffineFormCoeff

@[expose] public section

/-!
# Affine source inputs and the terminal input row

The source input is an explicitly affine readout of the committed coordinates
(`InputForms`). GKR's terminal input claim is then a vanishing affine polynomial
on those coordinates (`inputPolynomial`, of degree at most one, with its
evaluation `inputPolynomial_eval`): the input row of the masked GKR, the one
claim of `GordieHowe.GKR.LayeredCircuit.maskedReduction`.
-/

namespace GordieHowe
open IOP

open scoped NNReal
open PackedClaim MvPolynomial

namespace GKR.SourceInput

variable {F ι : Type} [Field F]

/-- **The source input as affine forms** on the committed coordinates: input `x` at the public
input `p` is the form `form p x`. This permits public constants and fixed linear
transformations without an assumed input semantics equivalence. -/
structure InputForms (F ι Pub : Type) [Field F] (d : ℕ) where
  /-- The form of each input at each public input. -/
  form : Pub → Fin (2 ^ d) → AffineForm F ι

/-- The source input the committed coordinates `w` give at the public input `p`. -/
def InputForms.input {Pub : Type} {d : ℕ}
    (I : InputForms F ι Pub d) (p : Pub) (w : ι → F) (x : Fin (2 ^ d)) : F :=
  (I.form p x).eval w

/-- The input forms as polynomials, for the proofs. -/
noncomputable def InputForms.polynomial {Pub : Type} {d : ℕ} (I : InputForms F ι Pub d) (p : Pub)
    (x : Fin (2 ^ d)) : MvPolynomial ι F :=
  (I.form p x).toMvPolynomial

theorem InputForms.degree {Pub : Type} {d : ℕ} (I : InputForms F ι Pub d) (p : Pub)
    (x : Fin (2 ^ d)) : (I.polynomial p x).totalDegree ≤ 1 :=
  (I.form p x).totalDegree_toMvPolynomial_le

theorem InputForms.input_eq_eval {Pub : Type} {d : ℕ} (I : InputForms F ι Pub d) (p : Pub)
    (w : ι → F) (x : Fin (2 ^ d)) : I.input p w x = MvPolynomial.eval w (I.polynomial p x) := by
  simp [InputForms.input, InputForms.polynomial]

variable {Pub PadIdx : Type} {d L : ℕ} (I : InputForms F ι Pub d)
    (pad : PadIdx → ι) {layout : Transcript.Layout PadIdx L}
    (G : Transcript.Interaction F PadIdx d layout)

/-- The terminal multilinear input equality, expressed as a vanishing affine
polynomial on the witness coordinates: the input forms weighted by the claim
coefficients, minus the terminal claim with its two masking pads
(`GKR.Transcript.valueExpr`). -/
noncomputable def inputPolynomial (p : Pub) (tr : G.spec.Transcript (Fin.last G.n)) :
    MvPolynomial ι F :=
  (∑ x : Fin (2 ^ d),
      C (claimCoeff (G.g0 tr) (G.g1 tr) (G.transcript tr).inputAlpha x) * I.polynomial p x) -
    (Transcript.valueExpr layout (G.transcript tr) pad).polynomial

/-- **The terminal input row as an affine form** (computable): the input forms weighted by the
claim coefficients, minus the terminal claim with its two masking pads. Its polynomial is
`inputPolynomial` (`toMvPolynomial_inputForm`). -/
def inputForm (p : Pub) (tr : G.spec.Transcript (Fin.last G.n)) : AffineForm F ι :=
  AffineForm.sumFin (fun x : Fin (2 ^ d) =>
      claimCoeff (G.g0 tr) (G.g1 tr) (G.transcript tr).inputAlpha x • I.form p x) -
    (Transcript.valueExpr layout (G.transcript tr) pad).form

theorem toMvPolynomial_inputForm (p : Pub) (tr : G.spec.Transcript (Fin.last G.n)) :
    (inputForm I pad G p tr).toMvPolynomial = inputPolynomial I pad G p tr := by
  simp [inputForm, inputPolynomial, InputForms.polynomial]

theorem inputPolynomial_degree (p : Pub) (tr : G.spec.Transcript (Fin.last G.n)) :
    (inputPolynomial I pad G p tr).totalDegree ≤ 1 := by
  unfold inputPolynomial
  apply (totalDegree_sub _ _).trans
  apply max_le _ (Transcript.Affine.polynomial_degree _)
  apply totalDegree_finsetSum_le
  intro x _
  exact (totalDegree_mul _ _).trans (by simpa using I.degree p x)

theorem inputPolynomial_eval (p : Pub) (tr : G.spec.Transcript (Fin.last G.n))
    (w : ι → F) :
    MvPolynomial.eval w (inputPolynomial I pad G p tr) =
      (∑ x : Fin (2 ^ d),
          claimCoeff (G.g0 tr) (G.g1 tr) (G.transcript tr).inputAlpha x * I.input p w x) -
        Transcript.value layout (G.transcript tr) (w ∘ pad) := by
  simp [inputPolynomial, InputForms.input, InputForms.polynomial,
    Transcript.Affine.polynomial_eval, Transcript.valueExpr_eval]

/-- **The terminal input row reads what the input forms read and the pads' coordinates.** -/
theorem readsOnly_inputForm [DecidableEq ι] {T : ι → Prop} (hI : ∀ p x, (I.form p x).ReadsOnly T)
    (hpad : ∀ q, T (pad q)) (p : Pub) (tr : G.spec.Transcript (Fin.last G.n)) :
    (inputForm I pad G p tr).ReadsOnly T := by
  have hu : ∀ (l : Fin (L + 1)) (h : Fin 2),
      (Transcript.unmaskedExpr layout (G.transcript tr) pad l h).form.ReadsOnly T := fun l h =>
    (AffineForm.ReadsOnly.ofConst _).add (AffineForm.ReadsOnly.var (hpad _))
  refine (AffineForm.ReadsOnly.sumFin fun x => (hI p x).smul _).sub ?_
  exact (hu _ _).add ((hu _ _).smul _)

end GKR.SourceInput
end GordieHowe
