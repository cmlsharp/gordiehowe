-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import Mathlib.Logic.Equiv.Finset

@[expose] public section

/-!
# Fixed multiplication routing into Ligero copy rows

The product support is fixed before commitment. Three prepared coordinates
copy each multiplication's source operands and result; linear equations bind
the copies, and the product test checks them at a common message coordinate.
This is the algebra of `LigeroParam::inner_product_vector` in
`lib/ligero/ligero_param.h`: routing contributes positive copy coefficients
and negative source coefficients. It does not verify buffer offsets, row
allocation, padding, or the C++ compiler.
-/

namespace GordieHowe.Ligero.Routing

section

open MvPolynomial
open scoped BigOperators

/-- A multiplication's two operands and result, fixed independently of challenges. -/
structure ProductLayout (ι Q : Type) where
  /-- The coordinates of the operands `x`, `y` (slots `0`, `1`) and the result `z` (slot `2`) of
  each product. -/
  source : Q → Fin 3 → ι

variable {F ι Q Lin : Type} [Field F] [Fintype Q] [Fintype Lin]

/-- **The prepared coordinates**: the source coordinates and one copy of each operand and result
of each product. -/
abbrev Prepared (ι Q : Type) := Sum ι (Q × Fin 3)

/-- **A prepared linear row** of the tableau: a linear row `l` of the source system, or the
copy-routing row of operand `s` of product `q`. -/
inductive PreparedRow (Lin Q : Type) where
  /-- The source system's linear row `l`. -/
  | linear (l : Lin)
  /-- The copy-routing row of operand `s` of product `q`. -/
  | copy (q : Q) (s : Fin 3)

/-- The prepared rows as a sum of the linear rows and the copy indices. -/
def PreparedRow.equivSum {Lin Q : Type} : PreparedRow Lin Q ≃ Lin ⊕ (Q × Fin 3) where
  toFun
    | .linear l => .inl l
    | .copy q s => .inr (q, s)
  invFun
    | .inl l => .linear l
    | .inr qs => .copy qs.1 qs.2
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with l | ⟨q, s⟩ <;> rfl

instance {Lin Q : Type} [Fintype Lin] [Fintype Q] : Fintype (PreparedRow Lin Q) :=
  Fintype.ofEquiv _ PreparedRow.equivSum.symm

/-- The prepared rows are encoded as a sum (`PreparedRow.equivSum`). -/
instance {Lin Q : Type} [Encodable Lin] [Encodable Q] : Encodable (PreparedRow Lin Q) :=
  Encodable.ofEquiv _ PreparedRow.equivSum

/-- **Copy routing**: every copy of a product's operand or result equals its source coordinate. -/
def _root_.GordieHowe.Ligero.Routing (L : ProductLayout ι Q) (w : Prepared ι Q → F) : Prop :=
  ∀ q s, w (.inr (q, s)) = w (.inl (L.source q s))

/-- **The products hold on the source coordinates**: `x · y = z` for every product. -/
def SourceProducts (L : ProductLayout ι Q) (w : ι → F) : Prop :=
  ∀ q, w (L.source q 0) * w (L.source q 1) = w (L.source q 2)

/-- Two product layouts on the same coordinates, side by side. -/
def ProductLayout.sum {Q₁ Q₂ : Type} (L₁ : ProductLayout ι Q₁) (L₂ : ProductLayout ι Q₂) :
    ProductLayout ι (Q₁ ⊕ Q₂) where
  source := Sum.elim L₁.source L₂.source

omit [Fintype Q] in
@[simp] theorem sourceProducts_sum {Q₁ Q₂ : Type} (L₁ : ProductLayout ι Q₁)
    (L₂ : ProductLayout ι Q₂) (w : ι → F) :
    SourceProducts (L₁.sum L₂) w ↔ SourceProducts L₁ w ∧ SourceProducts L₂ w := by
  simp only [SourceProducts, ProductLayout.sum, Sum.forall, Sum.elim_inl, Sum.elim_inr]

/-- **The products hold on the copies**: `x · y = z` on every product's copied coordinates. -/
def CopyProducts (w : Prepared ι Q → F) : Prop :=
  ∀ q, w (.inr (q, 0)) * w (.inr (q, 1)) = w (.inr (q, 2))

omit [Fintype Q] in
theorem copyProducts_iff_sourceProducts {L : ProductLayout ι Q}
    {w : Prepared ι Q → F} (h : Routing L w) :
    CopyProducts w ↔ SourceProducts L (w ∘ Sum.inl) := by
  have hr : ∀ q s, w (.inr (q, s)) = w (.inl (L.source q s)) := h
  simp only [CopyProducts, SourceProducts, Function.comp_apply, hr]

/-- Canonical honest copies do not depend on test coefficients. -/
def honestCopies (L : ProductLayout ι Q) (w : ι → F) : Prepared ι Q → F :=
  Sum.elim w (fun qs => w (L.source qs.1 qs.2))

omit [Field F] [Fintype Q] in
theorem honestCopies_routing (L : ProductLayout ι Q) (w : ι → F) :
    Routing L (honestCopies L w) := fun _ _ => rfl

/-- **The product constraint** `x · y − z` on the cells, as a polynomial. -/
noncomputable def productPolynomial (x y z : ι) : MvPolynomial ι F := X x * X y - X z

theorem productPolynomial_degree (x y z : ι) :
    (productPolynomial (F := F) x y z).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp

@[simp] theorem eval_productPolynomial (x y z : ι) (w : ι → F) :
    eval w (productPolynomial x y z) = w x * w y - w z := by
  simp [productPolynomial]

/-- Source equations: the chosen affine equations and fixed multiplication triples. -/
noncomputable def sourceSystem (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (hlinear : ∀ l, (linear l).totalDegree ≤ 1) : QuadraticSystem F ι where
  Eq := Sum Lin Q
  polynomial := Sum.elim linear (fun q =>
    productPolynomial (L.source q 0) (L.source q 1) (L.source q 2))
  degree := by
    rintro (l | q)
    · exact (hlinear l).trans (by decide)
    · exact productPolynomial_degree _ _ _

/-- Each routing equation has coefficient +1 on a copy and -1 on its source. -/
noncomputable def routingPolynomial (L : ProductLayout ι Q) (q : Q) (s : Fin 3) :
    MvPolynomial (Prepared ι Q) F := X (.inr (q, s)) - X (.inl (L.source q s))

omit [Fintype Q] in
theorem routingPolynomial_degree (L : ProductLayout ι Q) (q : Q) (s : Fin 3) :
    (routingPolynomial (F := F) L q s).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans (by simp)

omit [Fintype Q] in
@[simp] theorem eval_routingPolynomial (L : ProductLayout ι Q) (q : Q) (s : Fin 3)
    (w : Prepared ι Q → F) :
    eval w (routingPolynomial L q s) = w (.inr (q, s)) - w (.inl (L.source q s)) := by
  simp [routingPolynomial]

/-- Affine equations on sources, copy-routing equations, and co-column products. -/
noncomputable def routedSystem (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (hlinear : ∀ l, (linear l).totalDegree ≤ 1) :
    QuadraticSystem F (Prepared ι Q) where
  Eq := Sum Lin (Sum (Q × Fin 3) Q)
  polynomial := Sum.elim (fun l => rename Sum.inl (linear l))
    (Sum.elim (fun qs => routingPolynomial L qs.1 qs.2)
      (fun q => productPolynomial (.inr (q, 0)) (.inr (q, 1)) (.inr (q, 2))))
  degree := by
    rintro (l | (⟨q, s⟩ | q))
    · exact (totalDegree_rename_le _ _).trans ((hlinear l).trans (by decide))
    · exact (routingPolynomial_degree L q s).trans (by decide)
    · exact productPolynomial_degree _ _ _

theorem sourceSystem_holds_iff (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (hlinear : ∀ l, (linear l).totalDegree ≤ 1) (w : ι → F) :
    (sourceSystem L linear hlinear).Holds w ↔
      (∀ l, eval w (linear l) = 0) ∧ SourceProducts L w := by
  simp [QuadraticSystem.Holds, sourceSystem, SourceProducts, sub_eq_zero]

theorem routedSystem_holds_iff (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (hlinear : ∀ l, (linear l).totalDegree ≤ 1) (w : Prepared ι Q → F) :
    (routedSystem L linear hlinear).Holds w ↔
      (sourceSystem L linear hlinear).Holds (w ∘ Sum.inl) ∧ Routing L w := by
  have hraw : (routedSystem L linear hlinear).Holds w ↔
      (∀ l, eval (w ∘ Sum.inl) (linear l) = 0) ∧ Routing L w ∧ CopyProducts w := by
    simp [QuadraticSystem.Holds, routedSystem, Routing, CopyProducts, eval_rename,
      sub_eq_zero]
  rw [hraw, sourceSystem_holds_iff]
  constructor
  · rintro ⟨hl, hr, hp⟩
    exact ⟨⟨hl, (copyProducts_iff_sourceProducts hr).mp hp⟩, hr⟩
  · rintro ⟨⟨hl, hp⟩, hr⟩
    exact ⟨hl, hr, (copyProducts_iff_sourceProducts hr).mpr hp⟩

theorem honestCopies_holds_iff (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (hlinear : ∀ l, (linear l).totalDegree ≤ 1) (w : ι → F) :
    (routedSystem L linear hlinear).Holds (honestCopies L w) ↔
      (sourceSystem L linear hlinear).Holds w := by
  rw [routedSystem_holds_iff]
  exact and_iff_left (honestCopies_routing L w)

/-- Random linear aggregation of the affine constraints and routing constraints. -/
noncomputable def aggregate (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (α : Lin → F) (β : Q → Fin 3 → F) : MvPolynomial (Prepared ι Q) F :=
  (∑ l, C (α l) * rename Sum.inl (linear l)) +
    ∑ q, ∑ s, C (β q s) * routingPolynomial L q s

/-- Evaluation is precisely the weighted source residuals plus each positive
copy and negative source routing term. This permits arbitrary affine source
equations while keeping the multiplication support fixed. -/
theorem eval_aggregate (L : ProductLayout ι Q) (linear : Lin → MvPolynomial ι F)
    (α : Lin → F) (β : Q → Fin 3 → F) (w : Prepared ι Q → F) :
    eval w (aggregate L linear α β) =
      (∑ l, α l * eval (w ∘ Sum.inl) (linear l)) +
        ∑ q, ∑ s, (β q s * w (.inr (q, s)) - β q s * w (.inl (L.source q s))) := by
  simp [aggregate, eval_rename, mul_sub]

end

end GordieHowe.Ligero.Routing
