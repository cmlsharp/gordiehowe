-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.ProofSystem.Ligero.ShapeEncoding

@[expose] public section

/-!
# Hiding layouts and honest cells from a Ligero placement

A `Ligero.Preparation.Placement` fixes where every source variable and every
multiplication copy sits in the tableau. This file builds, for an arbitrary
placement, the objects the honest prover and the zero-knowledge argument of
`Ligero.HVZK` consume, and proves the completeness direction of
`Ligero.Preparation.holds_source`:
* `Placement.hidingLayout`: the hiding layout from the blinding fields and the
  layout facts, as named hypotheses (parameter conditions and facts about the field);
* `Placement.fill` and `Placement.cells`: the value written at each cell (a
  placed value, or zero at an unoccupied cell), as committed `Ligero.HVZK.Cells`;
* `Ligero.Preparation.holds_zeroRows`: if the source values satisfy the source equations
  and the copies are exact, the zero-privacy rows of those cells satisfy the
  prepared linear system `Ligero.Preparation.linearSystem`.

The allocation conditions are parameter conditions on the placement:
* `Placement.AliasesAgree`: two prepared coordinates placed at one cell hold the
  same source variable under exact routing;
* `Placement.ProductsCovered`: an occupied cell of a product row lies in the
  column of a copy of that product group;
* `source_nonzero`, `source_witness`, `copy_witness`, `product_nonzero`: fields
  of `Placement` (no placed value in row 0 or a privacy column).

The constructed block layout `Ligero.Layout.Shape` is one instance
(`Shape.placement_aliasesAgree`, `Shape.placement_productsCovered`,
`Shape.hidingLayout`).
-/

namespace GordieHowe
open IOP

open Polynomial
open MvPolynomial
open scoped Classical
section

namespace Ligero.Routing

variable {F ι Q : Type}

/-- The source variable a prepared coordinate holds when the copies are exact:
a source variable holds itself, and a copy holds the operand or result it
copies. -/
def routedSource (L : ProductLayout ι Q) : Prepared ι Q → ι :=
  Sum.elim id fun qs => L.source qs.1 qs.2

/-- Under exact routing, every prepared coordinate carries the value of its
routed source variable. -/
theorem eq_routedSource {L : ProductLayout ι Q} {w : Prepared ι Q → F}
    (h : Routing L w) (z : Prepared ι Q) : w z = w (.inl (routedSource L z)) := by
  cases z with
  | inl i => rfl
  | inr qs => exact h qs.1 qs.2

/-- The honest copies carry the value of each coordinate's routed source variable. -/
theorem honestCopies_routedSource (L : ProductLayout ι Q) (w : ι → F) (z : Prepared ι Q) :
    honestCopies L w z = w (routedSource L z) := by
  cases z <;> rfl

end Ligero.Routing

namespace Ligero.Preparation.Placement

variable {F ι Q : Type} [Field F] {N R nQ : ℕ} {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  (A : Placement C P ι Q)

/-! ### Allocation conditions -/

/-- Two prepared coordinates placed at one cell hold the same source
variable under exact routing. The honest cell value is then well defined. -/
def AliasesAgree (products : Routing.ProductLayout ι Q) : Prop :=
  ∀ z z', A.location z = A.location z' →
    Routing.routedSource products z = Routing.routedSource products z'

/-- An occupied cell `(P.products g s, j)` of a product row lies in the
column `j` of a copy of the group `g`. Then the three product cells of `g` at
`j` hold that copy's operands and result, or are all unoccupied. -/
def ProductsCovered : Prop :=
  ∀ g s j z, A.location z = (P.products g s, j) → ∃ q, A.copyGroup q = g ∧ A.copyCol q = j

/-- Values of the prepared coordinates that agree wherever two coordinates share
a cell. -/
def Consistent (v : Routing.Prepared ι Q → F) : Prop :=
  ∀ z z', A.location z = A.location z' → v z = v z'

/-- Exact copies are consistent when aliased coordinates hold one source variable. -/
theorem consistent_of_routing {products : Routing.ProductLayout ι Q}
    (halias : A.AliasesAgree products) {v : Routing.Prepared ι Q → F}
    (hcopy : Ligero.Routing products v) : A.Consistent v := by
  intro z z' h
  rw [hcopy.eq_routedSource z, hcopy.eq_routedSource z', halias z z' h]

/-- Injective locations have no aliases. -/
theorem aliasesAgree_of_injective (products : Routing.ProductLayout ι Q)
    (h : Function.Injective A.location) : A.AliasesAgree products := by
  intro z z' hz
  rw [h hz]

include A in
/-- A placement with a source variable has a witness column. -/
theorem witness_nonempty [Nonempty ι] : P.witness.Nonempty :=
  ⟨(A.source (Classical.arbitrary ι)).2, A.source_witness _⟩

/-! ### Cells -/

/-- The value written at a cell: the value of a prepared coordinate placed
there, and zero at an unoccupied cell. -/
noncomputable def fill (v : Routing.Prepared ι Q → F) (row : Fin (R + 1)) (j : Fin C.k) : F :=
  if h : ∃ z, A.location z = (row, j) then v (Classical.choose h) else 0

theorem fill_of_unoccupied (v : Routing.Prepared ι Q → F) {row : Fin (R + 1)}
    {j : Fin C.k} (h : ∀ z, A.location z ≠ (row, j)) : A.fill v row j = 0 := by
  unfold fill
  split_ifs with hz
  · exact absurd (Classical.choose_spec hz) (h _)
  · rfl

theorem fill_location {v : Routing.Prepared ι Q → F} (hv : A.Consistent v)
    (z : Routing.Prepared ι Q) :
    A.fill v (A.location z).1 (A.location z).2 = v z := by
  unfold fill
  split_ifs with h
  · exact hv _ _ (Classical.choose_spec h)
  · exact absurd ⟨z, rfl⟩ h

/-- Row 0 holds no placed value. -/
@[simp] theorem fill_zero_row (v : Routing.Prepared ι Q → F) (j : Fin C.k) :
    A.fill v 0 j = 0 :=
  A.fill_of_unoccupied v fun z hz => A.location_nonzero z (congrArg Prod.fst hz)

/-- A privacy column holds no placed value. -/
theorem fill_privacy (v : Routing.Prepared ι Q → F) (row : Fin (R + 1))
    {j : Fin C.k} (hj : j ∉ P.witness) : A.fill v row j = 0 :=
  A.fill_of_unoccupied v fun z hz => hj (by simpa [hz] using A.location_witness z)

/-- The three product cells of a group at one column satisfy the product
relation when the placement covers the product rows and the copies are exact
copies of source values that satisfy the source products. -/
theorem fill_products (hcover : A.ProductsCovered)
    {products : Routing.ProductLayout ι Q} {v : Routing.Prepared ι Q → F}
    (hv : A.Consistent v) (hcopy : Ligero.Routing products v)
    (hprod : Routing.SourceProducts products (v ∘ Sum.inl)) (g : Fin nQ) (j : Fin C.k) :
    A.fill v (P.products g 2) j = A.fill v (P.products g 0) j * A.fill v (P.products g 1) j := by
  by_cases hocc : ∃ s z, A.location z = (P.products g s, j)
  · obtain ⟨s, z, hz⟩ := hocc
    obtain ⟨q, hg, hc⟩ := hcover g s j z hz
    have key : ∀ s', A.fill v (P.products g s') j = v (.inr (q, s')) := by
      intro s'
      have hloc : A.location (.inr (q, s')) = (P.products g s', j) := by
        change (P.products (A.copyGroup q) s', A.copyCol q) = _
        rw [hg, hc]
      have := A.fill_location hv (.inr (q, s'))
      rwa [hloc] at this
    rw [key, key, key, hcopy q 0, hcopy q 1, hcopy q 2]
    exact (hprod q).symm
  · simp only [not_exists] at hocc
    rw [A.fill_of_unoccupied v (hocc 2), A.fill_of_unoccupied v (hocc 0), zero_mul]

/-- The committed cells of a placement: each data row's cells as `fill` writes
them. `hmem` states that every placed value lies in its row's blinding field;
it is a condition on the honest input. -/
noncomputable def cells (Bf : HVZK.BlindingFields C P) (v : Routing.Prepared ι Q → F)
    (hmem : ∀ z (row : Fin R), (A.location z).1 = row.succ → v z ∈ Bf.field row) :
    HVZK.Cells Bf where
  cell row j := A.fill v row.succ j
  cell_mem row j _ := by
    unfold fill
    split_ifs with h
    · exact hmem _ row (congrArg Prod.fst (Classical.choose_spec h))
    · exact zero_mem _

/-- The zero-privacy rows of a placement's cells take the value `fill` writes at
every message node. -/
theorem zeroRows_cells_eval {Bf : HVZK.BlindingFields C P}
    {v : Routing.Prepared ι Q → F}
    {hmem : ∀ z (row : Fin R), (A.location z).1 = row.succ → v z ∈ Bf.field row}
    (row : Fin (R + 1)) (j : Fin C.k) :
    (HVZK.zeroRows (A.cells Bf v hmem) row).eval (P.nodes j) = A.fill v row j := by
  refine Fin.cases ?_ (fun i => ?_) row
  · simp
  · rw [HVZK.zeroRows_succ, LigeroInterpolation.interpolate_eval P.nodes_injective]
    by_cases hj : j ∈ P.witness
    · simp [hj, cells]
    · simp [hj, A.fill_privacy v i.succ hj]

/-- The honest rows of a placement's cells read back the placed source values,
for every coin value: the privacy coins sit off the witness columns. -/
theorem sourceReadout_rows_cells {hrate : 2 * C.k - 1 ≤ N} {Bf : HVZK.BlindingFields C P}
    {nrep : ℕ} [NeZero nrep]
    {v : Routing.Prepared ι Q → F} (hv : A.Consistent v)
    (hmem : ∀ z (row : Fin R), (A.location z).1 = row.succ → v z ∈ Bf.field row)
    (c : HVZK.Coins hrate Bf nrep) :
    A.sourceReadout (HVZK.rows (A.cells Bf v hmem) c) = v ∘ Sum.inl := by
  funext i
  obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr (A.source_nonzero i)
  have hw := A.source_witness i
  have key : (HVZK.rows (A.cells Bf v hmem) c (A.source i).1).eval (P.nodes (A.source i).2) =
      A.fill v (A.source i).1 (A.source i).2 := by
    rw [← hm, HVZK.rows_succ, LigeroInterpolation.interpolate_eval P.nodes_injective,
      HVZK.rowValues_of_mem _ _ _ hw]
    rfl
  exact key.trans (A.fill_location hv (.inl i))

/-- The readout of a placement's cells is the placed values. -/
theorem readout_zeroRows {Bf : HVZK.BlindingFields C P}
    {v : Routing.Prepared ι Q → F}
    {hmem : ∀ z (row : Fin R), (A.location z).1 = row.succ → v z ∈ Bf.field row}
    (hv : A.Consistent v) : A.readout (HVZK.zeroRows (A.cells Bf v hmem)) = v := by
  funext z
  rw [readout, A.zeroRows_cells_eval, A.fill_location hv]

end Ligero.Preparation.Placement

namespace Ligero.Preparation

variable {F ι Q Lin : Type} [Field F] [Fintype ι] [Fintype Q]
  {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  (A : Placement C P ι Q) (products : Routing.ProductLayout ι Q)
  (linear : Lin → MvPolynomial ι F) (hlinear : ∀ l, (linear l).totalDegree ≤ 1)
  (index : Fin nL ≃ Routing.PreparedRow Lin Q)

omit [Fintype ι] [Fintype Q] in
/-- Source values satisfying the affine source equations, with exact copies,
satisfy every prepared equation. -/
theorem equation_eval_eq_zero {v : Routing.Prepared ι Q → F}
    (haffine : ∀ l, eval (v ∘ Sum.inl) (linear l) = 0)
    (hcopy : Ligero.Routing products v) (e : Routing.PreparedRow Lin Q) :
    eval v (equation products linear e) = 0 := by
  cases e with
  | linear l => simpa [equation, eval_rename] using haffine l
  | copy q s => simp [equation, hcopy q s]

variable [Fintype Lin]

/-- **Completeness of the prepared system at a placement.** If the source values
`v ∘ Sum.inl` satisfy the source equations and the copies are exact, the
zero-privacy rows of the placement's cells satisfy `linearSystem`.
Hypotheses: `hsource` and `hcopy` are the honest input; `halias` and `hcover`
are parameter conditions on the placement. This is the converse direction of `holds_source`. -/
theorem holds_zeroRows (Bf : HVZK.BlindingFields C P) {v : Routing.Prepared ι Q → F}
    (hmem : ∀ z (row : Fin R), (A.location z).1 = row.succ → v z ∈ Bf.field row)
    (halias : A.AliasesAgree products) (hcover : A.ProductsCovered)
    (hsource : (Routing.sourceSystem products linear hlinear).Holds (v ∘ Sum.inl))
    (hcopy : Ligero.Routing products v) :
    Tableau.Holds C P (linearSystem A products linear index)
      (HVZK.zeroRows (A.cells Bf v hmem)) := by
  have hs := (Routing.sourceSystem_holds_iff products linear hlinear _).mp hsource
  have hv := A.consistent_of_routing halias hcopy
  refine ⟨fun l => ?_, fun j g => ?_⟩
  · have he := equation_eval A products linear hlinear index
      (HVZK.zeroRows (A.cells Bf v hmem)) l
    rw [A.readout_zeroRows hv, equation_eval_eq_zero products linear hs.1 hcopy] at he
    change _ = -(equation products linear (index l)).constantCoeff
    linear_combination -he
  · by_cases hj : j ∈ P.witness
    · simp only [Tableau.quadCheck, hj, ↓reduceIte, Tableau.quadPolynomials,
        LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_sub, Polynomial.eval_mul, A.zeroRows_cells_eval]
      rw [A.fill_products hcover hv hcopy hs.2 g j, sub_self]
    · simp [Tableau.quadCheck, hj]

end Ligero.Preparation

namespace Ligero.Preparation.Placement

variable {F ι Q : Type} [Field F] {N R nQ : ℕ} {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  (A : Placement C P ι Q)

/-- The hiding layout of a placement with a source variable, from its blinding
fields `Bf` and:
* `nodes_mem`, `points_mem`: facts about the field, every message node and every
  code point lies in each row's blinding field.
* `off_witness`: a parameter condition, no code point is a witness node.
* `products_ne_zero`: a parameter condition, no product group reads row 0. The placement's
  `product_nonzero` gives this for the groups a copy uses only.
The witness set is nonempty because a source variable sits in a witness
column (`witness_nonempty`). -/
def hidingLayout [Nonempty ι] [DecidableEq F] (Bf : HVZK.BlindingFields C P)
    (nodes_mem : ∀ row j, P.nodes j ∈ Bf.field row)
    (points_mem : ∀ row i, C.D i ∈ Bf.field row)
    (off_witness : ∀ i, ∀ j ∈ P.witness, C.D i ≠ P.nodes j)
    (products_ne_zero : ∀ g s, P.products g s ≠ 0) : HVZK.HidingLayout C P where
  toBlindingFields := Bf
  decEq := inferInstance
  nodes_mem := nodes_mem
  points_mem := points_mem
  off_witness := off_witness
  witness_nonempty := A.witness_nonempty
  products_ne_zero := products_ne_zero

end Ligero.Preparation.Placement

/-! ### The constructed block layout -/

namespace Ligero.Layout.Shape

variable (S : Shape) {F : Type} [Field F] {N : ℕ} (C : GordieHowe.RSCode F N)
  (hk : C.k = S.r + S.w) (nodes : Fin C.k → F) (hnodes : Function.Injective nodes)

/-- No product row is row 0. -/
theorem products_ne_zero (g : Fin S.productGroups) (s : Fin 3) : S.products g s ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 + S.witnessRows + s.val * S.productGroups + g.val = 0 at hv
  omega

/-- No product row is a source row. -/
theorem products_ne_source (g : Fin S.productGroups) (s : Fin 3) (i : Fin S.nw) :
    S.products g s ≠ (S.source C hk i).1 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 + S.witnessRows + s.val * S.productGroups + g.val = 1 + i.val / S.w at hv
  have hi : i.val / S.w < S.witnessRows := S.block_lt i.isLt
  omega

/-- Each slot's product rows are distinct across groups. -/
theorem products_left_injective {g g' : Fin S.productGroups} {s : Fin 3}
    (h : S.products g s = S.products g' s) : g = g' := by
  have hv := congrArg Fin.val h
  change 1 + S.witnessRows + s.val * S.productGroups + g.val =
    1 + S.witnessRows + s.val * S.productGroups + g'.val at hv
  exact Fin.ext (by omega)

/-- A witness column of the Shape lies after the privacy prefix. -/
theorem le_of_mem_witness {j : Fin C.k} (hj : j ∈ S.witness C) : S.r ≤ j.val := by
  simpa [witness] using hj

theorem witness_card (hk : C.k = S.r + S.w) : (S.witness C).card = S.w := by
  have h : (S.witness C).card = (Finset.univ.filter fun j : Fin C.k => S.r ≤ j.val).card :=
    rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin C.k))) (fun j : Fin C.k => S.r ≤ j.val)
  have hnot : (Finset.univ.filter fun j : Fin C.k => ¬ S.r ≤ j.val) =
      Finset.univ.filter fun j : Fin C.k => j.val < S.r := by
    ext j
    simp
  rw [hnot, Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at hsplit
  rw [h]
  omega

include hk in
/-- The Shape has `S.r` privacy positions. -/
theorem privacy_card : C.k - (S.parameters C nodes hnodes).witness.card = S.r := by
  change C.k - (S.witness C).card = S.r
  rw [S.witness_card C hk]
  omega

/-- The Shape placement has injective locations, so it has no aliases. -/
theorem placement_aliasesAgree (products : Routing.ProductLayout (Fin S.nw) (Fin S.nq)) :
    (S.placement C hk nodes hnodes).AliasesAgree products :=
  (S.placement C hk nodes hnodes).aliasesAgree_of_injective products
    (ShapeEncoding.placement_location_injective S C hk nodes hnodes)

/-- Every occupied product-row cell of the Shape placement is in the column of a
copy of that group. -/
theorem placement_productsCovered : (S.placement C hk nodes hnodes).ProductsCovered := by
  intro g s j z hz
  have hj : S.r ≤ j.val := by
    have hw := (S.placement C hk nodes hnodes).location_witness z
    rw [hz] at hw
    exact S.le_of_mem_witness C hw
  have hm := (ShapeEncoding.product_location_iff S C hk nodes hnodes g s j hj).mp ⟨z, hz⟩
  have hloc := ShapeEncoding.product_location_at S C hk nodes hnodes g s j hj hm
  exact ⟨⟨g.val * S.w + (j.val - S.r), hm⟩,
    S.products_left_injective (congrArg Prod.fst hloc), congrArg Prod.snd hloc⟩

section Indexed

variable {ι Q : Type} (sourceIndex : ι ≃ Fin S.nw) (productIndex : Q ≃ Fin S.nq)

/-- The indexed placement places each coordinate where the Shape placement places
its index. -/
theorem indexedPlacement_location (z : Routing.Prepared ι Q) :
    (S.indexedPlacement C hk sourceIndex productIndex nodes hnodes).location z =
      (S.placement C hk nodes hnodes).location
        (Sum.map sourceIndex (Prod.map productIndex id) z) := by
  cases z <;> rfl

/-- The indexed Shape placement has injective locations, so it has no aliases. -/
theorem indexedPlacement_aliasesAgree (products : Routing.ProductLayout ι Q) :
    (S.indexedPlacement C hk sourceIndex productIndex nodes hnodes).AliasesAgree products := by
  apply Preparation.Placement.aliasesAgree_of_injective
  intro z z' h
  rw [indexedPlacement_location, indexedPlacement_location] at h
  exact (Sum.map_injective.mpr ⟨sourceIndex.injective,
    productIndex.injective.prodMap Function.injective_id⟩)
    (ShapeEncoding.placement_location_injective S C hk nodes hnodes h)

/-- Every occupied product-row cell of the indexed Shape placement is in the column of
a copy of that group. -/
theorem indexedPlacement_productsCovered :
    (S.indexedPlacement C hk sourceIndex productIndex nodes hnodes).ProductsCovered := by
  intro g s j z hz
  rw [indexedPlacement_location] at hz
  obtain ⟨q, hg, hc⟩ := S.placement_productsCovered C hk nodes hnodes g s j _ hz
  refine ⟨productIndex.symm q, ?_, ?_⟩
  · change (S.placement C hk nodes hnodes).copyGroup (productIndex (productIndex.symm q)) = g
    rw [Equiv.apply_symm_apply]
    exact hg
  · change (S.placement C hk nodes hnodes).copyCol (productIndex (productIndex.symm q)) = j
    rw [Equiv.apply_symm_apply]
    exact hc

end Indexed

/-- The hiding layout of the Shape, from its blinding fields `Bf` and:
* `nodes_mem`, `points_mem`: facts about the field, every message node and every
  code point lies in each row's blinding field.
* `off_witness`: a parameter condition, no code point is a witness node.
The nonempty witness set follows from `width_pos`, and every product group
avoids row 0 (`products_ne_zero`). -/
def hidingLayout [DecidableEq F] (Bf : HVZK.BlindingFields C (S.parameters C nodes hnodes))
    (nodes_mem : ∀ row j, nodes j ∈ Bf.field row)
    (points_mem : ∀ row i, C.D i ∈ Bf.field row)
    (off_witness : ∀ i, ∀ j ∈ S.witness C, C.D i ≠ nodes j) :
    HVZK.HidingLayout C (S.parameters C nodes hnodes) where
  toBlindingFields := Bf
  decEq := inferInstance
  nodes_mem := nodes_mem
  points_mem := points_mem
  off_witness := off_witness
  witness_nonempty := ⟨⟨S.r, by have := S.width_pos; omega⟩, by
    change _ ∈ S.witness C
    simp [witness]⟩
  products_ne_zero := S.products_ne_zero

/-- The committed cells of the Shape encoding of the source values `w`. -/
noncomputable def shapeCells (Bf : HVZK.BlindingFields C (S.parameters C nodes hnodes))
    (products : Routing.ProductLayout (Fin S.nw) (Fin S.nq)) (w : Fin S.nw → F)
    (hmem : ∀ z (row : Fin S.dataRows), ((S.placement C hk nodes hnodes).location z).1 = row.succ →
      Routing.honestCopies products w z ∈ Bf.field row) : HVZK.Cells Bf :=
  (S.placement C hk nodes hnodes).cells Bf (Routing.honestCopies products w) hmem

/-- Completeness at the Shape: source values satisfying the source equations give zero-privacy Shape
cells satisfying the prepared system. The allocation conditions are discharged by
`placement_aliasesAgree` and `placement_productsCovered`; exact copies hold by
`honestCopies_routing`. -/
theorem holds_shapeCells {Lin : Type} [Fintype Lin] {nL : ℕ}
    (Bf : HVZK.BlindingFields C (S.parameters C nodes hnodes))
    (products : Routing.ProductLayout (Fin S.nw) (Fin S.nq))
    (linear : Lin → MvPolynomial (Fin S.nw) F) (hlinear : ∀ l, (linear l).totalDegree ≤ 1)
    (index : Fin nL ≃ Routing.PreparedRow Lin (Fin S.nq)) (w : Fin S.nw → F)
    (hmem : ∀ z (row : Fin S.dataRows), ((S.placement C hk nodes hnodes).location z).1 = row.succ →
      Routing.honestCopies products w z ∈ Bf.field row)
    (hsource : (Routing.sourceSystem products linear hlinear).Holds w) :
    Tableau.Holds C (S.parameters C nodes hnodes)
      (Preparation.linearSystem (S.placement C hk nodes hnodes) products linear index)
      (HVZK.zeroRows (S.shapeCells C hk nodes hnodes Bf products w hmem)) :=
  Preparation.holds_zeroRows (S.placement C hk nodes hnodes) products linear hlinear
    index Bf hmem (S.placement_aliasesAgree C hk nodes hnodes products)
    (S.placement_productsCovered C hk nodes hnodes) hsource
    (Routing.honestCopies_routing products w)

end Ligero.Layout.Shape

end

end GordieHowe
