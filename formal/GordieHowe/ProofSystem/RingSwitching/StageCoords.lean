-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackingStage
public import GordieHowe.ProofSystem.Zerocheck.CoordSumcheckIP

public section

/-!
# The coordinate sumcheck at a packing stage

A packing stage `B ⊂ T` receives a claim on `Y ⊕ PackedCoord ng d`: the parent's coordinates `Y`
and the `d` child coordinates of each of the `ng` groups (`MaskedReduction.stage`). The child
coordinates of a group are the words of a coordinate layout (`PackedCoord.layout`), so the
coordinate sumcheck (`MaskedReduction.coordSumcheck`) runs on the stage's combined claim between
the combination and the measurement (`MaskedReduction.stageCoords`). Its output claim has
coefficients `α_g eq(ρ, j)` on the child coordinates, which the measurement reads like any other
claim.

* **Soundness** (`Sound.stageCoords`): the stage's errors, `1/|K|` at the combination, then
  `2/|K|` per round (`sum_stageCoordsError`).
* **The honest prover** (`Honest.stageCoords`): the stage's, with the honest rounds at the
  coordinates the words decode to; completeness and the simulation by `Sim.stageCoords` come from
  `Honest.coordSumcheck` and `Honest.measure`.

The planned trees run no stage-level sumcheck: the bit sumcheck of a batch on bits
(`MaskedReduction.bitSumcheck`) is the only coordinate sumcheck the programs use.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open scoped NNReal

variable {F ι : Type} [Field F] {p m d e ng r : ℕ} [ExpChar F p] {Y : Type}

/-- **The coordinate layout of a stage's child coordinates**: word `g` is group `g`, and its
coordinate `j` is the child coordinate `⟨g, j⟩`; the rounds' pads are `pad` and their nodes
`nodes`. -/
def PackedCoord.layout (pad : Fin r → Fin 2 → ι) (nodes : Sumcheck.Nodes F) :
    CoordLayout F ι (Y ⊕ PackedCoord ng d) r ng d where
  coord g j := .inr ⟨g, j⟩
  pad := pad
  nodes := nodes

namespace FieldProof.MaskedReduction

variable [Fintype ι] [Fintype F] [DecidableEq F] [DecidableEq Y] {Pub Wit : Type}
  {cells : Wit → ι → F} {nc : ℕ}

/-- **One packing stage with the coordinate sumcheck**: the combination with one fresh coefficient
per claim (`MaskedReduction.combine`), then the coordinate sumcheck over the `d` child coordinates
of each group in `r` rounds (`coordSumcheck` at `PackedCoord.layout`; in use `d ≤ 2^r`), then the
stage's measurement of its output claim. -/
def stageCoords (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (pad : Fin r → Fin 2 → ι)
    (nodes : Sumcheck.Nodes F) : MaskedReduction F ι Pub Wit cells Y (d + 1) :=
  (M.combine.coordSumcheck (PackedCoord.layout pad nodes) (S.level L)).measure S L

/-- **The errors of a stage with the coordinate sumcheck**: the masked reduction's, `1/|K|` at the
combination, `2/|K|` at each round's challenge, none at the measurement. -/
noncomputable def stageCoordsError (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (pad : Fin r → Fin 2 → ι)
    (nodes : Sumcheck.Nodes F) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    (M.stageCoords S L pad nodes).spec.ChallengeIdx → ℝ≥0 :=
  (M.combine.coordSumcheck (PackedCoord.layout pad nodes) (S.level L)).measureError S L
    (coordSumcheckError (K := F) r (M.combineError ε))

/-- **A stage with the coordinate sumcheck adds `1/|K|` and `2r/|K|`** to the errors of the masked
reduction before it. -/
theorem sum_stageCoordsError (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (pad : Fin r → Fin 2 → ι)
    (nodes : Sumcheck.Nodes F) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.stageCoordsError S L pad nodes ε i =
      ∑ i, ε i + 1 / Fintype.card F + ((2 * r : ℕ) : ℝ≥0) / Fintype.card F := by
  refine (sum_measureError _ S L _).trans ?_
  refine (sum_coordSumcheckError (K := F) (m := r) _).trans ?_
  rw [sum_combineError]

/-- **The simulator of a stage with the coordinate sumcheck**: the combination's, then uniform
round values (`Sim.coordSumcheck`), then the measurement's.

Running time: the masked reduction's simulator's, a copy of the combination challenge, of the `2r`
round values and of `d` field elements. This running time is argued here, not proved in Lean. -/
def Sim.stageCoords {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (pad : Fin r → Fin 2 → ι)
    (nodes : Sumcheck.Nodes F) (SM : M.Sim) : (M.stageCoords S L pad nodes).Sim :=
  Sim.measure S L (Sim.coordSumcheck (PackedCoord.layout pad nodes) SM.combine)

variable [RelFrobeniusOrder F p m e]

/-- **Soundness of a stage with the coordinate sumcheck**: the claims hold on the child's level,
or the combination event (`1/|K|`) or a round's event (`2/|K|` each) occurred, given the masks'
condition (`Sound.combine`, `Sound.coordSumcheck`, `Sound.measure`). -/
noncomputable def Sound.stageCoords
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {pad : Fin r → Fin 2 → ι}
    {nodes : Sumcheck.Nodes F} {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0}
    (H : M.Sound (S.level L).view sat ε) :
    (M.stageCoords S L pad nodes).Sound L.view (fun p w => S.masks.Valid (cells w) → sat p w)
      (M.stageCoordsError S L pad nodes ε) :=
  H.combine.coordSumcheck.measure

/-- **The honest prover of a stage with the coordinate sumcheck**: the combination's, then the
honest rounds at the coordinates the words decode to (`wordOf`, which `hword` ties to the cells),
then the measurement's; simulated by `Sim.stageCoords`. -/
def Honest.stageCoords {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {pad : Fin r → Fin 2 → ι}
    {nodes : Sumcheck.Nodes F} {In : Type} {dom : Pub → In → Prop} {SM : M.Sim}
    (H : M.Honest (S.level L).view In dom SM) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g) :
    (M.stageCoords S L pad nodes).Honest L.view In dom (Sim.stageCoords S L pad nodes SM) :=
  (H.combine.coordSumcheck (PackedCoord.layout pad nodes)
      fun p x π g j => S.basis.coord (wordOf p x π g) j).measure MH
    (fun p x π => wordOf p x π.1) fun p x π w h => hword p x π.1 w h.1

end FieldProof.MaskedReduction

end GordieHowe
