-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Export.PackingTree
public import GordieHowe.ProofSystem.Ligero.MaskRow.Layout

@[expose] public section

/-!
# A packing tree on the C++ tree layout

A member of the class of packing trees (`TreeSpec`) whose cells are the committed cells of the C++
tree layout (`GordieHowe.Ligero.MaskRow.TreeLayout.Coord`: `[prefix | root children's words | root own]`,
`tree_zk.h:350-351`) and whose subfield masks are prefix cells (`TreeLayout.IsPrefix`) is a tree
domain (`GordieHowe.RingSwitching.TreeFieldProof`) once a masked reduction on its logical coordinates is given: the commitment is Ligero
with the prefix-row test on the layout, with untested masks or the mask test (`TreeLayout.Numbers.setup`), so every side
condition of `TreeSpec.domain` is proved from the layout (`TreeSpec.layoutDomain`): the prefix
test's subfield is `S0` and the prefix cells cover the subfield masks' cells. The honest prover's data
of the commitment comes from the layout too (`TreeSpec.layoutHiding`), and cells whose prefix lies
in `S0` are admissible (`TreeSpec.admissible_layoutDomain`).

The errors (`TreeSpec.knowledgeError_layoutDomain`): the masked reduction's, `1/|K|` per combination of the
tree, and the test and column bounds of the masking at the layout's Ligero numbers with the joint
subfield term when the prefix is nonempty (`TreeLayout.Numbers.proofError`).
-/

namespace GordieHowe

open IOP PackingStage RelativePacking Ligero.MaskRow
open scoped NNReal

namespace TreeSpec

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [ExpChar K p] {np nw : ℕ}
  {Full : Type} [Fintype Full] [DecidableEq Full] [Encodable Full] {S0 : Subfield K} [DecidablePred
      (· ∈ S0)]
  {V Pub : Type} {nc : ℕ}
  (T : TreeSpec K p (TreeLayout.Coord np nw Full) S0 (TreeLayout.IsPrefix np nw Full) V nc)
  (L : TreeLayout.Numbers K S0)
  (maskedReduction : FieldProof.MaskedReduction K (TreeLayout.Coord np nw Full) Pub (TreeLayout.Coord np nw Full → K) id V nc)
  (routes : T.path.Routes maskedReduction)

/-- **A member of the class on the C++ tree layout is a tree domain** (`TreeSpec.domain`): the masked
reduction on its logical coordinates with the routing obligations, and Ligero with the prefix-row
test, with untested masks or the mask test, on the layout at the Ligero numbers `L` (`TreeLayout.Numbers.setup`), whose
subfield is `S0` and whose prefix cells are the cells `IsPrefix` names. -/
def layoutDomain : RingSwitching.TreeFieldProof K p (TreeLayout.Coord np nw Full) V Pub nc :=
  T.domain maskedReduction routes (L.setup np nw Full (T.path.close maskedReduction).products
    (T.path.close maskedReduction).Lin)
    (by rw [TreeLayout.Numbers.pre_setup]; rfl)
    (fun _ h => by rw [TreeLayout.Numbers.pre_setup]; exact h)

/-- **The honest prover's data of the commitment** of a member on the tree layout
(`TreeLayout.Numbers.hidingData`), every field proved from the layout. -/
def layoutHiding : (T.layoutDomain L maskedReduction routes).cp.Hiding :=
  L.hidingData np nw Full (T.path.close maskedReduction).products (T.path.close maskedReduction).Lin

omit [DecidableEq Full] in
/-- **Cells whose prefix lies in `S0` are admissible** for the commitment of a member on the tree
layout (`TreeLayout.Numbers.admissible_hiding`). -/
theorem admissible_layoutDomain {x : TreeLayout.Coord np nw Full → K}
    (hx : ∀ j, x (TreeLayout.prefixCell np nw Full j) ∈ S0) :
    (T.layoutDomain L maskedReduction routes).cp.Admissible (T.layoutHiding L maskedReduction routes) x :=
  L.admissible_hiding hx

omit [DecidableEq Full] in
/-- **The knowledge error of a member on the tree layout**: the masked reduction's errors `Σ ε`, `1/|K|`
per combination of the tree, and the commitment's proof-phase error `L.proofError np`. -/
theorem knowledgeError_layoutDomain (ε : maskedReduction.spec.ChallengeIdx → ℝ≥0) :
    (T.layoutDomain L maskedReduction routes).knowledgeError ε =
      ∑ i, ε i + T.path.combinations / Fintype.card K + L.proofError np := by
  unfold RingSwitching.TreeFieldProof.knowledgeError RingSwitching.TreeFieldProof.cpError
    TreeLayout.Numbers.proofError
  erw [TreeLayout.Numbers.bounds_setup, TreeLayout.Numbers.t_setup]
  rfl

end TreeSpec

end GordieHowe
