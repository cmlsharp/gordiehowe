-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Views

@[expose] public section

/-!
# GordieHowe: facts about bit views and rows on views

The affine form of a linear map and a constant on finitely many variables (`affineOn`), the values
the sides of a row predicate on views read (`GordieHowe.RealizedProgram.viewExprOk_sides`,
`GordieHowe.RealizedProgram.viewValueOk_of_mem`), and the summed operands of a merged batch, on columns
(`GordieHowe.RealizedProgram.mergedOpAt`, affine in the cells, `isAff_mergedOpAt`) and on bits
(`GordieHowe.RealizedProgram.mergedBitsOpAt`, affine in the bit operands' variables, `isAff_mergedBitsOpAt`).
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **The affine form of a linear form and a constant** on finitely many variables: `ofLinear`
through the numbering of the variables by their encoding (`Encodable.fintypeEquivFin`). -/
def affineOn {F V : Type} [CommRing F] [Fintype V] [Encodable V] (f : (V → F) →ₗ[F] F) (c : F) :
    AffineForm F V :=
  (AffineForm.ofLinear (f ∘ₗ LinearMap.funLeft F F (Encodable.fintypeEquivFin (α := V))) c).rename
    (Encodable.fintypeEquivFin (α := V)).symm

@[simp] theorem eval_affineOn {F V : Type} [CommRing F] [Fintype V] [Encodable V] (f : (V → F)
    →ₗ[F] F) (c : F)
    (x : V → F) : (affineOn f c).eval x = f x + c := by
  have hx : LinearMap.funLeft F F (Encodable.fintypeEquivFin (α := V)) (x ∘
      (Encodable.fintypeEquivFin (α := V)).symm) = x := by
    funext v
    simp [LinearMap.funLeft_apply]
  rw [affineOn, AffineForm.eval_rename, AffineForm.eval_ofLinear, LinearMap.comp_apply, hx]

section

variable {ir : RealizedProgram} {I : Interp}

variable (I) in
/-- **The value of operand `o` of a merged batch at coordinate `t`** read from the cells `z` alone:
the parts' operands `o` summed (one part's slice holds `o`, `sum_instOperand_slice`). -/
def mergedOpAt (d b : ℕ) (z : ir.Cell d → (I (ir.domainField d)).K) (o t : ℕ) :
    (I (ir.domainField d)).K :=
  ∑ p : Fin (ir.batch b).parts.length,
    ir.opValAt I d (ir.cellReader I d z) (ir.instOperand ir.atomB d b p o) t

/-- **The operands of a covered batch's parts are affine in the cells**, summed. -/
theorem isAff_mergedOpAt {d b : ℕ} (hb : ir.PartsOk ir.atomB d b) (o t : ℕ) :
    IsAff fun z => ir.mergedOpAt I d b z o t := by
  refine IsAff.sum _ fun p _ => ?_
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hb.exists_part p
  have hk : (ir.partShape ir.atomB d b p).k = pf.operands.length := by rw [hsh]; rfl
  exact isAff_opValAt (instOperand_atoms hpf hops hk o) t

variable (I) in
/-- **The value of operand `o` of a merged batch on bits at coordinate `t`** read from the variables
`z` of the bit operands (the cells, their bits, the statement): the parts' operands `o` summed. -/
def mergedBitsOpAt (d b : ℕ) (z : ir.BitsVar d → (I (ir.domainField d)).K) (o t : ℕ) :
    (I (ir.domainField d)).K :=
  ∑ p : Fin (ir.batch b).parts.length,
    ir.opValAt I d (ir.bitsReader I d z) (ir.instOperand (ir.bitsAtomB d) d b p o) t

/-- **The operands of a covered batch on bits are affine in the variables**, summed over its
parts. -/
theorem isAff_mergedBitsOpAt {d b : ℕ} (hb : ir.PartsOk (ir.bitsAtomB d) d b) (o t : ℕ) :
    IsAff fun z => ir.mergedBitsOpAt I d b z o t := by
  refine IsAff.sum _ fun p _ => ?_
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hb.exists_part p
  have hk : (ir.partShape (ir.bitsAtomB d) d b p).k = pf.operands.length := by rw [hsh]; rfl
  exact isAff_bitsOperand (instOperand_atoms hpf hops hk o) t

/-- **The sides of a row predicate on views may be rows' on views.** -/
theorem viewExprOk_sides {d p : ℕ} (hp : ir.isViewRow d p = true) :
    ir.viewExprOk d (ir.rowLhs d p) = true ∧ ir.viewExprOk d (ir.rowRhs d p) = true := by
  unfold isViewRow at hp
  unfold rowLhs rowRhs
  split at hp
  · rename_i e e' h
    simp only [Bool.and_eq_true] at hp
    simp only [h, Option.map_some, Option.getD_some]
    exact ⟨hp.1.2, hp.2⟩
  · simp at hp

/-- The values a side of a row predicate on views reads may be read by a row on views. -/
theorem viewValueOk_of_mem {d : ℕ} {e : Expr} (he : ir.viewExprOk d e = true) {v : ℕ}
    (hv : v ∈ ir.exprNodes e) : ir.viewValueOk d v = true := by
  simp only [viewExprOk, Bool.and_eq_true, List.all_eq_true] at he
  exact he.1.1 v hv

end

end GordieHowe.RealizedProgram
