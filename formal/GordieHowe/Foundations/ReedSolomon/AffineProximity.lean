-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.CorrelatedLine
public import GordieHowe.ProofSystem.Ligero.AffineCodeTest
public import GordieHowe.Foundations.ReedSolomon.RowDistance
public import GordieHowe.Foundations.ReedSolomon.MatrixCombination
public import GordieHowe.Foundations.Probability.AffineLineCounting

@[expose] public section

/-!
# Affine Reed–Solomon proximity in the unique-decoding regime

The target is the finite-coefficient form of BCIKS20 Theorem 1.6 (ePrint 2020/654, version of
2021-07-03). The proof uses the unique-decoding
line theorem, finite translation averaging, and a word of maximal distance in the generated linear
space. The closest polynomial to that word determines one common set of erroneous columns. No
independence of the matrix rows is required.
-/
namespace GordieHowe.Ligero.AffineCodeTest
open Polynomial
open scoped Classical

open RSCode

variable {F : Type} [Field F] [Fintype F] {R N : ℕ}

theorem exists_rowNearby_iff (C : RSCode F N) (u : Fin N → F) :
    (∃ p, RowNearby C u p) ↔ rowDistance C u ≤ C.e := by
  rw [rowDistance_le_iff]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,hp.degree,hp.close⟩
  · rintro ⟨p,hp,he⟩
    exact ⟨p,hp,he⟩

theorem projection_eq_combination (U : RSCode.Matrix F (R+1) N) (r : Fin R → F) :
    projection U r = U 0 + RSCode.combination (fun i => U i.succ) r := by
  ext j
  simp [projection, combination_apply]

/-- Maximal minimum distance turns common agreement for pairs into one common
error set for the whole row matrix. `hline` is discharged by the proved line
theorem in `affineProximity`; it is not a premise of that final result. -/
theorem nearby_of_all_combinations (C : RSCode F N) (U : RSCode.Matrix F R N)
    (hall : ∀ r, rowDistance C (RSCode.combination U r) ≤ C.e)
    (hline : ∀ (e : ℕ) (he : 2*e+C.k≤N) (u v : Fin N → F),
      (∀ z : F, rowDistance C (u+z•v) ≤ e) →
      ∃ p q : F[X], p.natDegree<C.k ∧ q.natDegree<C.k ∧
        (errorSet C u p ∪ errorSet C v q).card ≤ e) :
    ∃ fs, Nearby C U fs := by
  obtain ⟨r, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun r : Fin R → F => rowDistance C (RSCode.combination U r)) Finset.univ_nonempty
  let w := RSCode.combination U r
  let e := rowDistance C w
  have he : e ≤ C.e := hall r
  have hradius : 2*e+C.k≤N := by have := C.radius; omega
  let p := closestPolynomial C w
  have hp : p.natDegree<C.k := closestPolynomial_degree C w
  have hep : errorCount C w p = e := closestPolynomial_errorCount C w
  have hrows : ∀ i, ∃ q : F[X], q.natDegree<C.k ∧ errorSet C (U i) q ⊆ errorSet C w p := by
    intro i
    have hz : ∀ z : F, rowDistance C (w+z•U i)≤e := by
      intro z
      have hm := hmax (r+z•Pi.single i 1) (Finset.mem_univ _)
      simpa only [map_add, map_smul, combination_single] using hm
    obtain ⟨p',q,hp',hq,hclose⟩ := hline e hradius w (U i) hz
    have hp'close : errorCount C w p' ≤ e :=
      (Finset.card_le_card Finset.subset_union_left).trans hclose
    have hsame := polynomial_unique_at C e hradius w p' p hp' hp hp'close hep.le
    subst p'
    exact ⟨q,hq,errorSet_subset_of_union_card_le C w (U i) p q (hclose.trans_eq hep.symm)⟩
  choose fs hdegree hsubset using hrows
  refine ⟨fs,hdegree,?_⟩
  have hcol : columnErrors C U fs ⊆ errorSet C w p := by
    intro j hj
    obtain ⟨i,hi⟩ := mem_columnErrors.mp hj
    exact hsubset i ((mem_errorSet C (U i) (fs i) j).mpr hi)
  exact (Finset.card_le_card hcol).trans (hep.le.trans he)

theorem correlated_line (C : RSCode F N) (u v : Fin N → F)
    (hcount : N < (Finset.univ.filter fun z : F => rowDistance C (u+z•v)≤C.e).card) :
    ∃ p q : F[X], p.natDegree<C.k ∧ q.natDegree<C.k ∧
      (errorSet C u p ∪ errorSet C v q).card ≤ C.e := by
  obtain ⟨p,q,hp,hq,hclose⟩ := CorrelatedLine.correlatedAgreement C u v (by
    simpa only [rowDistance_le_iff, errorCount, errorSet, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] using hcount)
  refine ⟨p,q,hp,hq,?_⟩
  have he : errorSet C u p ∪ errorSet C v q =
      Finset.univ.filter (fun j => u j ≠ p.eval (C.D j) ∨ v j ≠ q.eval (C.D j)) := by
    ext j
    simp [errorSet]
  rw [he]
  exact hclose

/-- Affine RS proximity is a consequence of the fixed code parameters:
`param`: distinct evaluation nodes, positive dimension, and `2*e+k ≤ N`,
carried by `C`. The matrix and coefficient vectors are unrestricted. -/
theorem _root_.GordieHowe.RSCode.affineProximity (C : GordieHowe.RSCode F N) : AffineProximity C R := by
  intro U hfar
  by_contra hbound
  have hdense0 := Nat.lt_of_not_ge hbound
  let L := RSCode.combination (fun i : Fin R => U i.succ)
  have hp : ∀ r : Fin R → F, (∃ p, RowNearby C (projection U r) p) ↔
      rowDistance C (U 0 + L r) ≤ C.e := by
    intro r
    rw [projection_eq_combination]
    exact exists_rowNearby_iff C _
  have hfilter : (Finset.univ.filter fun r : Fin R → F => ∃ p, RowNearby C (projection U r) p) =
      Finset.univ.filter (fun r : Fin R → F => rowDistance C (U 0 + L r) ≤ C.e) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp]
  rw [hfilter] at hdense0
  have hdense : N * Fintype.card (Fin R → F) <
      (Finset.univ.filter fun r : Fin R → F => rowDistance C (U 0 + L r) ≤ C.e).card *
        Fintype.card F := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using hdense0
  have hq : N < Fintype.card F := by
    have hc := Finset.card_filter_le Finset.univ (fun r : Fin R → F => rowDistance C (U 0 + L r) ≤ C.e)
    simp only [Finset.card_univ] at hc
    have hx := hdense.trans_le (Nat.mul_le_mul_right (Fintype.card F) hc)
    rw [Nat.mul_comm (Fintype.card (Fin R → F))] at hx
    exact Nat.lt_of_mul_lt_mul_right hx
  have hline : ∀ u v : Fin N → F,
      N < (Finset.univ.filter fun z : F => rowDistance C (u+z•v)≤C.e).card →
      rowDistance C v ≤ C.e := by
    intro u v hc
    obtain ⟨p,q,_,hq,hclose⟩ := correlated_line C u v hc
    exact (rowDistance_le_iff C v C.e).mpr
      ⟨q,hq,(Finset.card_le_card Finset.subset_union_right).trans hclose⟩
  have hhom : ∀ (s : F) (r : Fin R → F), rowDistance C (s • U 0 + L r) ≤ C.e := by
    apply AffineLineCounting.homogeneous_near
      (fun u : Fin N → F => rowDistance C u ≤ C.e) N ?_ ?_ L (U 0)
    · convert hdense using 1
      congr 2
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro u v hc
      apply hline u v
      convert hc using 1
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro s hs w
      rw [rowDistance_smul C w s hs]

  apply hfar
  apply nearby_of_all_combinations C U
  · intro r
    have hh := hhom (r 0) (Fin.tail r)
    rw [← combination_cons] at hh
    simpa only [Fin.cons_self_tail] using hh
  · intro e he u v hz
    let C' := codeWithRadius C e he
    have hz' : ∀ z : F, rowDistance C' (u+z•v)≤C'.e := hz
    have hall : (Finset.univ.filter fun z : F => rowDistance C' (u+z•v)≤C'.e) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun z _ => hz' z)
    have hc : N < (Finset.univ.filter fun z : F => rowDistance C' (u+z•v)≤C'.e).card := by
      rw [hall, Finset.card_univ]
      exact hq
    exact correlated_line C' u v hc

end GordieHowe.Ligero.AffineCodeTest
