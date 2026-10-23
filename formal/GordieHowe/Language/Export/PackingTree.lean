-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.TreeDomain

@[expose] public section

/-!
# The class of packing trees the planner builds

The planner (`PackingTree::plan`, `compiler/tree.h`) builds a rooted tree of subfields of `K` with
one stage per edge `B < T`, each edge labelled by its masking mode:

* **subfield masks** when the designated subfield `S0` lies in `B` (`stage.h:76-78`): the masks are
  `S0`-cells of the prefix (`SubfieldMasks`, whose `S0_le` is the condition `S0 ⊆ B`);
* **squaring-chain masks** in characteristic 2 (`B = GF(2)` or `S0 ⊄ B`): `σ_k` and its chain of
  `b k` squarings in root-own cells (`MaskScheme.squaringChainOver`, `B = GF(2^b)`).

The planner chooses squaring-chain masks exactly when they are available, but the theory holds for
either label whenever its condition holds; the shape rules (minimal parents, `D_max`, tie-breaks)
only select among members and play no role in soundness, completeness or hiding.

**The class `𝒯(K, S0)` as stated here** (`TreeSpec`): a tree in processing order with its routing
(`GordieHowe.RingSwitching.Tree`), nested (each stage's words are coordinates whose field lies in the stage's top `T`: a
node's words are its parent's coordinates, a root child's are cells), and a mode per stage
(`StageMode`: subfield masks over `S0` with prefix cells, or squaring-chain masks in characteristic
2). The prefix condition gives every stage's mask condition (`TreeSpec.masks_prefix`), so every
member is a `GordieHowe.RingSwitching.TreeFieldProof` once a masked reduction and a Ligero setup with the prefix-row test on the same
prefix are given (`TreeSpec.domain`).

The stages' bases are data (`StageBasis`, the field facts certified per configuration). The tree
shape of the plan data (each child once, parents the field or a child, processing order deepest
first) is checked on the exported plan (`GordieHowe.RealizedProgram.Export.Domain.IsTree`).
-/

namespace GordieHowe

open IOP PackingStage RelativePacking
open scoped NNReal

variable {K ι : Type} [Field K]

/-- **The mode of a stage's masks** (`stage.h`): subfield masks whose subfield is the designated
`S0` (`S0 ⊆ B` by `SubfieldMasks.S0_le`) and whose cells satisfy `pre` (the prefix), or
squaring-chain masks over `GF(2^m)` in characteristic 2. -/
inductive StageMode (S0 : Subfield K) (pre : ι → Prop) :
    {p m d : ℕ} → [ExpChar K p] → MaskScheme K ι p m d → Prop
  /-- Subfield masks over `S0`, in prefix cells. -/
  | subfieldMasks {p m d r : ℕ} [ExpChar K p] (L : SubfieldMasks K ι p m d r) (hS0 : L.S0 = S0)
      (hcells : ∀ k i, pre (L.cell k i)) : StageMode S0 pre (MaskScheme.subfieldMasks L)
  /-- Squaring-chain masks over `GF(2^m)`. -/
  | squaringChain {m d : ℕ} [ExpChar K 2] (C : ChainCells ι m d) :
      StageMode S0 pre (MaskScheme.squaringChainOver C)
  /-- Squaring-chain masks over `GF(2)` in the form of domain H's bit stage
  (`MaskScheme.squaringChain`). -/
  | squaringChainBit {d : ℕ} [ExpChar K 2] (C : SquaringChainCells ι d) :
      StageMode S0 pre (MaskScheme.squaringChain C)

/-- **A stage's mask condition from the prefix condition**: subfield masks' cells are prefix cells
in `S0`; squaring-chain masks need nothing. -/
theorem StageMode.valid {S0 : Subfield K} {pre : ι → Prop} {p m d : ℕ} [ExpChar K p]
    {Ms : MaskScheme K ι p m d} (h : StageMode S0 pre Ms) {x : ι → K}
    (hx : ∀ i, pre i → x i ∈ S0) : Ms.Valid x := by
  cases h with
  | subfieldMasks L hS0 hcells =>
    intro k i
    rw [hS0]
    exact hx _ (hcells k i)
  | squaringChain C => trivial
  | squaringChainBit C => trivial

namespace RingSwitching.Tree

variable {p : ℕ} [ExpChar K p]

/-- **Every stage has a mode** (`StageMode`) over `S0` with its subfield masks in `pre`. -/
def Modes (S0 : Subfield K) (pre : ι → Prop) : {V : Type} → {nc : ℕ} → Tree K p ι V nc → Prop
  | _, _, .nil => True
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest) => StageMode S0 pre S.masks ∧
      rest.Modes S0 pre
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest) => StageMode S0 pre S.masks ∧
      rest.Modes S0 pre

/-- **The prefix condition gives every stage's mask condition**. -/
theorem masksValid_of_modes {S0 : Subfield K} {pre : ι → Prop} {V : Type} {nc : ℕ}
    (P : Tree K p ι V nc) (h : P.Modes S0 pre) {x : ι → K} (hx : ∀ i, pre i → x i ∈ S0) :
    P.MasksValid x := by
  induction P with
  | nil => trivial
  | cons S rest ih => exact ⟨h.1.valid hx, ih h.2⟩
  | route S R rest ih => exact ⟨h.1.valid hx, ih h.2⟩

end RingSwitching.Tree

/-- **A packing tree of `K` over `S0`** (the class `𝒯(K, S0)` of the planner's trees, the paper's
`def:packing-tree`): the stages in processing order with the claims' routing (`path`), nested (each
stage's words lie at coordinates of field inside its top), and a mode per stage over `S0` with the
subfield masks' cells satisfying `pre` (the prefix). -/
structure TreeSpec (K : Type) [Field K] (p : ℕ) [ExpChar K p] (ι : Type) (S0 : Subfield K)
    (pre : ι → Prop) (V : Type) (nc : ℕ) where
  /-- The stages in processing order. -/
  path : RingSwitching.Tree K p ι V nc
  /-- Each stage's words lie at coordinates of field inside its top. -/
  nested : path.Nested
  /-- Every stage has a mode. -/
  modes : path.Modes S0 pre

namespace TreeSpec

variable {p : ℕ} [ExpChar K p] {S0 : Subfield K} {pre : ι → Prop} {V : Type} {nc : ℕ}
  (T : TreeSpec K p ι S0 pre V nc)

/-- **The prefix condition gives every stage's mask condition.** -/
theorem masks_prefix {x : ι → K} (hx : ∀ i, pre i → x i ∈ S0) : T.path.MasksValid x :=
  T.path.masksValid_of_modes T.modes hx

/-- **Prefix cells in `S0` give every stage's mask condition**, when the commitment's prefix cells
`P` cover `pre` and their subfield is `S0`. -/
theorem masks_prefixCells {np : ℕ} (P : Ligero.MaskRow.PrefixCells K ι np) (hE : P.E = S0)
    (hpre : ∀ i, pre i → ∃ j, P.cell j = i) {x : ι → K} (hx : P.In x) : T.path.MasksValid x :=
  T.masks_prefix fun i hi => by
    obtain ⟨j, rfl⟩ := hpre i hi
    rw [← hE]
    exact hx j

/-- **A member of the class is a tree domain** (`RingSwitching.TreeFieldProof`): given the masked reduction on its logical
coordinates with the routing obligations, and Ligero with the prefix-row test whose prefix cells
cover the subfield masks' cells and whose subfield is `S0`. -/
def domain [Fintype K] [DecidableEq K] [Fintype ι] {Pub : Type}
    (maskedReduction : FieldProof.MaskedReduction K ι Pub (ι → K) id V nc) (routes : T.path.Routes maskedReduction) {N R nQ nLr np : ℕ}
    {code : GordieHowe.RSCode K N} {tableau : Ligero.Tableau.Parameters (R := R) (nQ := nQ) code}
    (cp : Ligero.MaskRow.Setup code tableau (T.path.close maskedReduction).products
      (T.path.close maskedReduction).Lin nLr np)
    (hE : cp.pre.E = S0) (hpre : ∀ i, pre i → ∃ j, cp.pre.cell j = i) :
    RingSwitching.TreeFieldProof K p ι V Pub nc where
  path := T.path
  nested := T.nested
  maskedReduction := maskedReduction
  routes := routes
  N := N
  R := R
  nQ := nQ
  nLr := nLr
  np := np
  code := code
  tableau := tableau
  cp := cp
  masks_prefix _ hx := T.masks_prefixCells cp.pre hE hpre hx

end TreeSpec

end GordieHowe
