-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackingStage
public import GordieHowe.ProofSystem.RingSwitching.PackingRoute

@[expose] public section

/-!
# A domain's packing tree: stages composed along the tree

A GordieHowe domain packs its values along a tree of subfields of its field `K` (`tree.h`): the
root `K`, a node per declared subfield, each non-root node packed into its parent by one stage. The
proof (`tree_zk.h`, header lines 21-31) runs, after the batched relations and GKR, each non-root
node's stage from the deepest up, on the claims that read its region; each stage reveals its masked
measurements and passes its rows up as claims on its parent's region; the root children's stages
(`relative-pack/linear-batch/v1`) run as stages of the tree on the committed cells, closed into
Ligero with the prefix-row test (`GordieHowe.RingSwitching.TreeFieldProof`), as every domain's generic per-field circuit proof
does (`GordieHowe/ProofSystem/Program/FieldDomain.lean`).

**The stages in processing order** (`RingSwitching.Tree F p ι Z nc`): a list of stages, deepest first, each
peeling the child coordinates it decodes off the logical coordinates (`Z = Y ⊕ PackedCoord ng d`
for a stage on `Y`), down to the cells `ι`. `GordieHowe.RingSwitching.Tree.level` is the logical assignment of `Z` read
from the cells, decoding stage by stage. `GordieHowe.RingSwitching.Tree.run` runs every stage (`MaskedReduction.stage`:
combination with fresh coefficients, then the measurement) on a masked reduction whose claims are on `Z`,
and leaves a masked reduction whose claims are on the cells; `GordieHowe.RingSwitching.Tree.close` closes it into a masked row reduction
on the cells, the form `GordieHowe.FieldProof` and Ligero consume.

**Soundness** (`GordieHowe.RingSwitching.Tree.soundRun`, `GordieHowe.RingSwitching.Tree.soundClose`): the masked reduction's relation, given every
stage's mask condition on the cells (`MasksValid`: the subfield-mask stages' masks in `S0`, the
prefix-row test's conclusion), with the errors of the masked reduction and `1/|K|` per combination
(`GordieHowe.RingSwitching.Tree.sum_runError`).

**Routing** (`GordieHowe.RingSwitching.Tree`). The C++ stage combines the rows that read its region, selected
structurally by the nodes each row reads (`TreeRows::reads`, `tree_zk.h:956`), passes the others to
the stages above, and does not combine one touching row (`tree_zk.h:568-569`). `GordieHowe.RingSwitching.Tree` models
that: a stage is `cons` (combine every claim, the root's combination) or `route`
(`MaskedReduction.routedStage`: the touching claims, combined when two or more; the passing claims, which
read no child coordinate, become their parts on the parent's coordinates). The selection is
structural (`StageRouting`, fixed by the instance, as the C++ selection is by the rows' node sets,
`ExtraRows::nodes`), and the passing claims' avoidance of the child is the run's obligation
(`GordieHowe.RingSwitching.Tree.Routes`). The honest prover is `GordieHowe.RingSwitching.Tree.honestRun`. The planned trees of the programs route
every edge, the root's children included, by the nodes each claim reads (`PEdge.path`). The
generic domain proof over a `GordieHowe.RingSwitching.Tree` is
`GordieHowe/ProofSystem/RingSwitching/TreeDomain.lean`; the planner's class of trees is
`GordieHowe/Language/Export/PackingTree.lean`. Composed bit views (`TreeRows::Formed`) are not modeled; no
domain's tree uses them.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {p : ℕ} [ExpChar F p]

/-! ### Trees with routed stages -/

/-- **A packing tree's stages in processing order with the claims' routing** (deepest first), from
the logical coordinates `Z` down to the cells `ι`, for `nc` claims entering the first stage:
`cons S rest` runs the stage `S` combining every claim (`MaskedReduction.stage`, the root's combination,
`relative-pack/linear-batch/v1`); `route S R rest` runs it on the claims that read its child
(`MaskedReduction.routedStage`: combined when two or more touch, `tree_zk.h:568-569`), the others passing; then
the stages `rest` on `Y`. A path of `cons` stages only is the case where every stage combines
every claim. -/
inductive RingSwitching.Tree (F : Type) [Field F] (p : ℕ) [ExpChar F p] (ι : Type) : Type → ℕ → Type 1
  /-- No stage: the logical coordinates are the cells. -/
  | nil {nc : ℕ} : Tree F p ι ι nc
  /-- A stage combining every claim, then the stages on `Y`. -/
  | cons {Y : Type} {m d e ng nc : ℕ} [RelFrobeniusOrder F p m e] (S : Stage F ι p m d e ng Y)
      (rest : Tree F p ι Y (d + 1)) : Tree F p ι (Y ⊕ PackedCoord ng d) nc
  /-- A routed stage, then the stages on `Y`. -/
  | route {Y : Type} {m d e ng nc nt np : ℕ} [RelFrobeniusOrder F p m e]
      (S : Stage F ι p m d e ng Y) (R : StageRouting nc nt np)
      (rest : Tree F p ι Y (d + 1 + np)) : Tree F p ι (Y ⊕ PackedCoord ng d) nc

namespace RingSwitching.Tree

/-- **The logical assignment of the path's coordinates** read from the cells, decoding stage by
stage (`Stage.level`). -/
def level : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → Level F ι Z
  | _, _, .nil => Level.base
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest) => S.level rest.level
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest) => S.level rest.level

/-- **The field of each logical coordinate**: `K` on the cells, the base `B` of the stage that
decodes a child coordinate. -/
def field : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → Z → Subfield F
  | _, _, .nil, _ => ⊤
  | _, _, @Tree.cons _ _ _ _ _ _ m _ _ _ _ _ _ rest, z =>
    Sum.elim rest.field (fun _ => fixedField F p m) z
  | _, _, @Tree.route _ _ _ _ _ _ m _ _ _ _ _ _ _ _ _ rest, z =>
    Sum.elim rest.field (fun _ => fixedField F p m) z

/-- **Nested**: each stage's words lie at coordinates whose field is contained in the stage's top
`T` (`StageBasis.top`). For a tree this is "a node's words are its parent's coordinates, of field
the parent `T`" (root children: cells, `T = K`). -/
def Nested : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → Prop
  | _, _, .nil => True
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest) =>
    (∀ g, rest.field (S.word g) ≤ S.basis.top) ∧ rest.Nested
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest) =>
    (∀ g, rest.field (S.word g) ≤ S.basis.top) ∧ rest.Nested

/-- **Every stage's mask condition** on the cells (`MaskScheme.Valid`). -/
def MasksValid : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → (ι → F) → Prop
  | _, _, .nil, _ => True
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), x => S.masks.Valid x ∧ rest.MasksValid x
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest), x =>
    S.masks.Valid x ∧ rest.MasksValid x

/-- The number of claims after the path. -/
def outClaims : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → ℕ
  | _, nc, .nil => nc
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ rest) => rest.outClaims
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest) => rest.outClaims

/-- **The number of combinations**: every `cons` stage, and every routed stage with two or more
touching claims. -/
def combinations : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → ℕ
  | _, _, .nil => 0
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ rest) => rest.combinations + 1
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R rest) =>
    rest.combinations + R.combinations

variable [Fintype F] [DecidableEq F] {Pub Wit : Type} {cells : Wit → ι → F}

/-- **Run the stages** on a masked reduction whose claims are on the path's coordinates: each stage in
turn (`MaskedReduction.stage`, `MaskedReduction.routedStage`), its rows and passing claims the next stage's
claims. -/
def run : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    FieldProof.MaskedReduction F ι Pub Wit cells Z nc → FieldProof.MaskedReduction F ι Pub Wit cells ι P.outClaims
  | _, _, .nil, M => M
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), M => rest.run (M.stage S rest.level)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), M =>
    rest.run (M.routedStage R S rest.level)

/-- **The routing obligations of a run**: at every routed stage, the passing claims read no child
coordinate (`MaskedReduction.PassingAvoid`; structural, discharged by the instance). -/
def Routes : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    FieldProof.MaskedReduction F ι Pub Wit cells Z nc → Prop
  | _, _, .nil, _ => True
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), M => rest.Routes (M.stage S rest.level)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), M =>
    M.PassingAvoid R ∧ rest.Routes (M.routedStage R S rest.level)

/-- **The errors of the run**: the masked reduction's, then each stage's. -/
noncomputable def runError : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    (M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc) → (M.spec.ChallengeIdx → ℝ≥0) →
    (P.run M).spec.ChallengeIdx → ℝ≥0
  | _, _, .nil, _, ε => ε
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), M, ε =>
    rest.runError (M.stage S rest.level) (M.stageError S rest.level ε)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), M, ε =>
    rest.runError (M.routedStage R S rest.level) (M.routedStageError R S rest.level ε)

/-- **The run's errors are the masked reduction's plus `1/|K|` per combination**. -/
theorem sum_runError : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    (M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc) → (ε : M.spec.ChallengeIdx → ℝ≥0) →
    ∑ i, P.runError M ε i = ∑ i, ε i + P.combinations / Fintype.card F
  | _, _, .nil, _, ε => by
    simp only [combinations, Nat.cast_zero, zero_div, add_zero]
    rfl
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), M, ε => by
    refine (sum_runError rest _ _).trans ?_
    rw [FieldProof.MaskedReduction.sum_stageError, combinations]
    push_cast
    ring
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), M, ε => by
    refine (sum_runError rest _ _).trans ?_
    rw [FieldProof.MaskedReduction.sum_routedStageError, combinations]
    push_cast
    ring

/-- **Soundness of the run** (the paper's `thm:tree`, part (1)): from the masked reduction's soundness at
the path's logical assignment and the routing obligations, the run is sound at the cells for "every
stage's mask condition implies the relation", with the run's errors (`MaskedReduction.Sound.stage`,
`MaskedReduction.Sound.routedStage` per stage). -/
noncomputable def soundRun : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} → {sat : Pub → Wit → Prop} →
    {ε : M.spec.ChallengeIdx → ℝ≥0} → M.Sound P.level.view sat ε → P.Routes M →
    (P.run M).Sound (Level.base (F := F)).view (fun p w => P.MasksValid (cells w) → sat p w)
      (P.runError M ε)
  | _, _, .nil, _, _, _, H, _ => H.congr fun _ _ => ⟨fun h _ => h, fun h => h trivial⟩
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ rest), _, _, _, H, hR =>
    (rest.soundRun H.stage hR).congr fun _ _ =>
      ⟨fun h hv => h hv.2 hv.1, fun h hr hs => h ⟨hs, hr⟩⟩
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest), _, _, _, H, hR =>
    (rest.soundRun (H.routedStage hR.1) hR.2).congr fun _ _ =>
      ⟨fun h hv => h hv.2 hv.1, fun h hr hs => h ⟨hs, hr⟩⟩

/-- **The masked row reduction of the tree**: the run's claims, all on the cells, closed into rows
(`MaskedReduction.close`). -/
def close {Z : Type} {nc : ℕ} (P : Tree F p ι Z nc) (M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc) :
    FieldProof.MaskedRowReduction F ι Pub Wit cells :=
  (P.run M).close

/-- **Soundness of the tree's masked row reduction** (`soundRun`, `MaskedReduction.Sound.close`). -/
noncomputable def soundClose {Z : Type} {nc : ℕ} (P : Tree F p ι Z nc)
    {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} {sat : Pub → Wit → Prop}
    {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound P.level.view sat ε) (hR : P.Routes M) :
    (P.close M).Sound (fun p w => P.MasksValid (cells w) → sat p w) (P.runError M ε) :=
  (P.soundRun H hR).close

/-! ### The honest run -/

/-- **The honest masks of every stage** (`MaskScheme.Honest`). -/
def MaskHonest : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → Type 1
  | _, _, .nil => PUnit
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest) => S.masks.Honest × rest.MaskHonest
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest) => S.masks.Honest × rest.MaskHonest

/-- **The coordinates holding some stage's words.** -/
def IsWord : {Z : Type} → {nc : ℕ} → Tree F p ι Z nc → Z → Prop
  | _, _, .nil, _ => False
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _), .inr _ => False
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), .inl y =>
    (∃ g, S.word g = y) ∨ rest.IsWord y
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), .inr _ => False
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest), .inl y =>
    (∃ g, S.word g = y) ∨ rest.IsWord y

/-- **The simulator of the run**: each stage's simulator in turn (`MaskedReduction.Sim.stage`,
`MaskedReduction.Sim.routedStage`) after the masked reduction's simulator `SM`.

Running time: the masked reduction's simulator's, a copy of each combination challenge and of each
stage's measurement. This running time is argued here, not proved in Lean. -/
def simRun : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} → M.Sim → (P.run M).Sim
  | _, _, .nil, _, SM => SM
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), _, SM =>
    rest.simRun (FieldProof.MaskedReduction.Sim.stage S rest.level SM)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), _, SM =>
    rest.simRun (FieldProof.MaskedReduction.Sim.routedStage R S rest.level SM)

/-- **The honest run**: each stage's honest prover in turn (`MaskedReduction.Honest.stage`,
`MaskedReduction.Honest.routedStage`) with the stage's honest masks, the words' values read from `val`, a
function of the public input, the honest input and the masked reduction's pads that the committed cells
match at every word (`hval`); simulated by `simRun`. -/
def honestRun {In : Type} {dom : Pub → In → Prop} : {Z : Type} → {nc : ℕ} →
    (P : Tree F p ι Z nc) → {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} → P.Routes M →
    {SM : M.Sim} → (H : M.Honest P.level.view In dom SM) → P.MaskHonest →
    (val : Pub → In → H.Pads → Z → F) →
    (∀ p x π w, H.Commits p x π w → ∀ z, P.IsWord z → P.level.view (cells w) z = val p x π z) →
    (P.run M).Honest (Level.base (F := F)).view In dom (P.simRun SM)
  | _, _, .nil, _, _, _, H, _, _, _ => H
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), _, hR, _, H, MH, val, hval =>
    rest.honestRun hR
      (H.stage MH.1 (fun p x π g => val p x π (.inl (S.word g)))
        fun p x π w hw g => hval p x π w hw (.inl (S.word g)) (Or.inl ⟨g, rfl⟩))
      MH.2 (fun p x π y => val p x π.1 (.inl y))
      fun p x π w hw y hy => hval p x π.1 w hw.1 (.inl y) (Or.inr hy)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest), _, hR, _, H, MH, val, hval =>
    rest.honestRun hR.2
      (H.routedStage MH.1 (fun p x π g => val p x π (.inl (S.word g)))
        (fun p x π w hw g => hval p x π w hw (.inl (S.word g)) (Or.inl ⟨g, rfl⟩)) hR.1)
      MH.2 (fun p x π y => val p x π.1 (.inl y))
      fun p x π w hw y hy => hval p x π.1 w hw.1 (.inl y) (Or.inr hy)

end RingSwitching.Tree

end GordieHowe
