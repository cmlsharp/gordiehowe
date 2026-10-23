-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebra
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebraHonest
public import GordieHowe.Applications.Falcon512.Circuits.Hash

@[expose] public section

/-!
# Honest advice for the native Falcon A circuit

All definitions in this file are witness generation by the prover, not circuit operations: the
signature rows hold on the honest signature (`rows_hold_of_eq`, `honestSignature_eq`), the pads
selected before either verifier challenge (`Pads`), and the norm's honest residues with their
squared-magnitude sum (`honestVals` and its lemmas). Encoding bounds are honest signature input
conditions here, never premises of circuit soundness. The specification's `s₁Poly`, `s₁Coeffs` and
`s₂Coeffs` are `GordieHowe.Falcon512.EmulatedAlgebraCircuit.Honest`'s, at `falcon512`.
-/

namespace GordieHowe.Falcon512.NativeAlgebraCircuit.Honest

open Falcon512.EmulatedAlgebraCircuit.Honest (s₁Poly s₁Coeffs s₂Coeffs s₁Coeffs_eq s₂Coeffs_eq s₁Poly_coeff_eq
  normResidues normResidues_of_lt normResidues_of_not_lt pairL2NormSq_eq_normResidues)

variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [DecidableEq F]

/-! ### Signature rows: the converse of `Native.Rows.establish` -/

section SignatureRows

variable {n : ℕ}

omit [DecidableEq K] [Field K] [DecidableEq F] in
open Native.Rows in
/-- **Honest-input completeness of the native signature rows.** The converse of
`establish`: given the per-coefficient identity the honest witness satisfies (`heq`,
pure ring algebra, no soundness hypothesis), every row holds. -/
theorem rows_hold_of_eq (h : _root_.Falcon.Rq n) (W : Native.Rows.Wit F n)
    (heq : ∀ k, Native.Rows.s₁ W k - Native.Rows.cCoeff k W +
      LatticeCrypto.negacyclicConvCoeff (Native.Rows.keyVec h) (Native.Rows.s₂ W) k
        = 0) :
    rowsHold (Native.Rows.rows h) W := by
  intro idx
  have hk0 : (finProdFinEquiv.symm idx).1 = (0 : Fin 1) := Subsingleton.elim _ _
  have hidx : idx = finProdFinEquiv ((0 : Fin 1), (finProdFinEquiv.symm idx).2) := by
    conv_lhs => rw [← Equiv.apply_symm_apply finProdFinEquiv idx]
    rw [← hk0]
  set k := (finProdFinEquiv.symm idx).2
  rw [hidx]
  show Row.holds (Native.Rows.rows h (finProdFinEquiv ((0 : Fin 1), k))) W
  unfold Row.holds Native.Rows.rows NativeLinear.rows
  rw [Equiv.symm_apply_apply]
  dsimp only
  have hfilt : (Native.Rows.terms (F := F) h).filter (fun t => t.row = (0 : Fin 1)) =
      Native.Rows.terms h :=
    List.filter_eq_self.mpr fun t _ => by simp [Fin.eq_zero t.row]
  rw [hfilt, List.sum_linearMap_apply, List.map_map]
  unfold Native.Rows.terms
  have hj : ∀ j : Fin n,
      LatticeCrypto.negacyclicConvCoeff (Native.Rows.keyVec h) (Pi.single j 1) k *
          Native.Rows.s₂ W j =
        Native.Rows.s₂ W j *
          LatticeCrypto.negacyclicConvCoeff (Native.Rows.keyVec h) (Pi.single j 1) k :=
    fun j => _root_.mul_comm _ _
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_apply, NativeLinear.Term.coeff, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, one_smul, smul_eq_mul, neg_one_mul, LinearMap.sum_apply, hj]
  rw [← DFT.negacyclicConvCoeff_eq_sum_mul_single (Native.Rows.keyVec h)
    (fun j => Native.Rows.s₂ W j) k]
  linear_combination heq k

omit [DecidableEq K] [Field K] [DecidableEq F] in
/-- **The honest signature relation.** The per-coefficient identity the honest signature
witness satisfies: `s₁ = c - s₂ h` in canonical residues, a ring identity transported from
`s₁Poly_coeff_eq` through the injective cast into `F`. `CharP F 12289` is a fact about the
field. -/
theorem honestSignature_eq [CharP F 12289] (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly falcon512.n) (i : Fin falcon512.n) :
    ((s₁Coeffs h c s₂ i : ℕ) : F) = (c i : F) -
      LatticeCrypto.negacyclicConvCoeff (Native.Rows.keyVec h)
        (fun j => ((s₂Coeffs s₂ j : ℕ) : F)) i := by
  have hcp : CharP F _root_.Falcon.modulus := by unfold _root_.Falcon.modulus; infer_instance
  set φ : _root_.Falcon.Coeff →+* F := ZMod.castHom (dvd_refl _root_.Falcon.modulus) F with hφdef
  have hφkey : φ ∘ Falcon512.coeff h = Native.Rows.keyVec h := by
    funext j
    show φ (Falcon512.coeff h j) = _
    rw [hφdef, ZMod.castHom_apply, ZMod.cast_eq_val]
    rfl
  have hφs₂ : φ ∘ Falcon512.coeff s₂.toRq =
      fun j => ((s₂Coeffs s₂ j : ℕ) : F) := by
    funext j
    show φ (Falcon512.coeff s₂.toRq j) = _
    rw [← s₂Coeffs_eq s₂ j, map_natCast]
  have hkey := s₁Poly_coeff_eq h c s₂ i
  have hkey' := congrArg φ hkey
  rw [← s₁Coeffs_eq h c s₂ i, map_natCast, map_sub,
    map_natCast, DFT.negacyclicConvCoeff_map, hφkey, hφs₂] at hkey'
  exact hkey'

end SignatureRows

/-! ### The norm: honest residues and their squared-magnitude sum -/

section Norm

/-- The honest residues the norm gadget reads: the canonical `s₁` residue below
`falcon512.n`, the canonical `s₂` residue from `falcon512.n` on. -/
-- spec-side
def honestVals (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly falcon512.n) (i : Fin 1024) : ℕ :=
  if hi : (i : ℕ) < falcon512.n then s₁Coeffs h c s₂ ⟨i, hi⟩
  else s₂Coeffs s₂ ⟨(i : ℕ) - falcon512.n, by have := normCoeffs_eq; omega⟩

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- The honest residues are the canonical representatives of the norm residues. -/
theorem honestVals_eq_normResidues (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly falcon512.n) (i : Fin 1024) :
    (honestVals h c s₂ i : _root_.Falcon.Coeff) =
      normResidues h c s₂ (Fin.cast normCoeffs_eq.symm i) := by
  unfold honestVals
  split_ifs with hi
  · rw [normResidues_of_lt (i := Fin.cast normCoeffs_eq.symm i) h c s₂ hi, s₁Coeffs_eq]
    rfl
  · rw [normResidues_of_not_lt (i := Fin.cast normCoeffs_eq.symm i) h c s₂ hi, s₂Coeffs_eq]
    rfl

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- The `s₂` half of the honest residues, read as a centered magnitude, agrees with the
signature's own centered magnitude, given the encoding bounds. -/
theorem honestVals_s₂_centeredRepr {s₂ : _root_.Falcon.IntPoly falcon512.n}
    (hencoding : Falcon512.EncodingBounds falcon512 s₂) (i : Fin falcon512.n) :
    (LatticeCrypto.centeredRepr ((s₂Coeffs s₂ i : ℕ) : ZMod 12289)).natAbs =
      (s₂.get i).natAbs := by
  have hbound : (s₂.get i).natAbs ≤ 2047 := by
    have h1 : (s₂.get i).natAbs < Codec.magnitudeBound := hencoding.coefficients i
    rw [Codec.magnitudeBound_eq] at h1
    omega
  show (LatticeCrypto.centeredRepr ((s₂Coeffs s₂ i : ℕ) : _root_.Falcon.Coeff)).natAbs = _
  rw [s₂Coeffs_eq, Falcon512.intPoly_toRq_coeff,
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le _ hbound (by decide)]

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- **The honest residues' squared centered-magnitude sum is the algebraic norm bound.** -/
theorem honestVals_sum_eq (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly falcon512.n) :
    ∑ i : Fin 1024, NativeNorm.honestMagNat (honestVals h c s₂) i ^ 2 =
      _root_.Falcon.pairL2NormSq (s₁Poly h c s₂) s₂.toRq := by
  rw [pairL2NormSq_eq_normResidues]
  refine Fintype.sum_equiv (finCongr normCoeffs_eq.symm) _ _ fun i => ?_
  exact congrArg (fun x : _root_.Falcon.Coeff => (LatticeCrypto.centeredRepr x).natAbs ^ 2)
    (honestVals_eq_normResidues h c s₂ i)

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- **The honest norm bound.** `halgebra` is the honest signature's algebraic check. -/
theorem honestVals_hnorm (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    (s₂ : _root_.Falcon.IntPoly falcon512.n)
    (halgebra : Falcon512.algebraOk falcon512 h (Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff))
      s₂.toRq) :
    ∑ i : Fin 1024, NativeNorm.honestMagNat (honestVals h c s₂) i ^ 2 ≤ falcon512.βSq :=
  (honestVals_sum_eq h c s₂).trans_le halgebra

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- The honest `s₂` residues' centered magnitude is the signature coefficient's magnitude,
given the encoding bounds. -/
theorem honestVals_high_magNat (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    {s₂ : _root_.Falcon.IntPoly falcon512.n} (hencoding : Falcon512.EncodingBounds falcon512 s₂)
    (i : Fin falcon512.n) :
    NativeNorm.honestMagNat (honestVals h c s₂) (highIndex i) = (s₂.get i).natAbs := by
  have hidx : honestVals h c s₂ (highIndex i) = s₂Coeffs s₂ i := by
    have hi : ¬ ((highIndex i : ℕ) < falcon512.n) := Nat.not_lt.mpr (Nat.le_add_right _ _)
    rw [honestVals, dite_eq_right hi]
    exact congrArg (s₂Coeffs s₂) (Fin.ext (Nat.add_sub_cancel_left ..))
  unfold NativeNorm.honestMagNat
  rw [hidx, honestVals_s₂_centeredRepr hencoding]

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- **The honest `s₂` residues' centered magnitude fits the encoding budget.** -/
theorem honestVals_hs₂ (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    {s₂ : _root_.Falcon.IntPoly falcon512.n} (hencoding : Falcon512.EncodingBounds falcon512 s₂) :
    ∀ i : Fin 1024, falcon512.n ≤ (i : ℕ) →
      NativeNorm.honestMagNat (honestVals h c s₂) i < Codec.magnitudeBound := by
  intro i hi
  have hidx : i = highIndex ⟨(i : ℕ) - falcon512.n, by have := normCoeffs_eq; omega⟩ :=
    Fin.ext (by simp only [highIndex]; omega)
  rw [hidx, honestVals_high_magNat h c hencoding]
  exact hencoding.coefficients _

omit [DecidableEq K] [Field K] [Field F] [DecidableEq F] in
/-- The honest `s₂` magnitudes' high parts fit the encoding budget. -/
theorem honestVals_highSum (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    {s₂ : _root_.Falcon.IntPoly falcon512.n} (hencoding : Falcon512.EncodingBounds falcon512 s₂) :
    ∑ i : Fin falcon512.n, NativeNorm.honestMagNat (honestVals h c s₂) (highIndex i) /
        Codec.lowRadix ≤ falcon512.encodingHighBudget := by
  simpa only [honestVals_high_magNat h c hencoding] using hencoding.highSum

end Norm

end GordieHowe.Falcon512.NativeAlgebraCircuit.Honest
