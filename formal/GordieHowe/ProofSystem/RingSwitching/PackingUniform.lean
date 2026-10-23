-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackingTree
public import GordieHowe.ProofSystem.FieldProof.UniformSim

@[expose] public section

/-!
# Packing stages and trees keep the uniform simulator

The packing stages' masked reductions (`MaskedReduction.measure`, `MaskedReduction.stage`, `MaskedReduction.reorder`,
`MaskedReduction.combineFirst`, `MaskedReduction.measureHead`, `MaskedReduction.routedStage`) and a run along a packing
tree (`GordieHowe.RingSwitching.Tree.run`) have finite, nonempty message types when the masked reduction before them has, and
their honest provers' simulators are bijections onto the full transcripts when the masked reduction's is
(`MaskedReduction.Honest.SimBijective`): each stage's simulator copies the combination challenge, if any,
and sends its coins as the measurement. By `MaskedReduction.Honest.SimBijective.uniformHVZK`, the honest
run is then honest-verifier zero knowledge with error `0` with respect to the uniform simulator of
paper `def:red-sec` (c).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking 
open GKR.Schedule (one)

namespace FieldProof.MaskedReduction

variable {F ι : Type} [Field F] [Fintype ι] {p m d e ng : ℕ} [ExpChar F p] {Y Z : Type}
  {Pub Wit : Type} {cells : Wit → ι → F}

/-! ### Finite message types -/

section Types

variable {nc nc' nt np : ℕ}

/-- The reordered masked reduction has the masked reduction's message types. -/
instance reorder_typeFintype {M : MaskedReduction F ι Pub Wit cells Z nc} [h : ∀ i, Fintype (M.spec.Type i)]
    {σ : Fin nc ≃ Fin nc'} : ∀ i, Fintype ((M.reorder σ).spec.Type i) := h

/-- The reordered masked reduction has the masked reduction's message types. -/
instance reorder_typeNonempty {M : MaskedReduction F ι Pub Wit cells Z nc}
    [h : ∀ i, Nonempty (M.spec.Type i)] {σ : Fin nc ≃ Fin nc'} :
    ∀ i, Nonempty ((M.reorder σ).spec.Type i) := h

/-- The masked reduction with the zero claim prepended has the masked reduction's message types. -/
instance prependZero_typeFintype {M : MaskedReduction F ι Pub Wit cells Z np}
    [h : ∀ i, Fintype (M.spec.Type i)] : ∀ i, Fintype (M.prependZero.spec.Type i) := h

/-- The masked reduction with the zero claim prepended has the masked reduction's message types. -/
instance prependZero_typeNonempty {M : MaskedReduction F ι Pub Wit cells Z np}
    [h : ∀ i, Nonempty (M.spec.Type i)] : ∀ i, Nonempty (M.prependZero.spec.Type i) := h

variable [Fintype F] [DecidableEq F]

/-- The message types of combining the first claims are finite when the masked reduction's are. -/
instance combineFirst_typeFintype {M : MaskedReduction F ι Pub Wit cells Z (nt + np)}
    [∀ i, Fintype (M.spec.Type i)] : ∀ i, Fintype (M.combineFirst.spec.Type i) :=
  ProtocolSpec.appendTypeFintype (P₁ := M.spec) (P₂ := one .V_to_P (Fin nt → F))

/-- The message types of combining the first claims are nonempty when the masked reduction's are. -/
instance combineFirst_typeNonempty {M : MaskedReduction F ι Pub Wit cells Z (nt + np)}
    [∀ i, Nonempty (M.spec.Type i)] : ∀ i, Nonempty (M.combineFirst.spec.Type i) :=
  ProtocolSpec.appendTypeNonempty (P₁ := M.spec) (P₂ := one .V_to_P (Fin nt → F))

variable {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc} {S : Stage F ι p m d e ng Y}
  {L : Level F ι Y}

/-- The message types of a measurement are finite when the masked reduction's are. -/
instance measure_typeFintype {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1}
    [∀ i, Fintype (M.spec.Type i)] : ∀ i, Fintype ((M.measure S L).spec.Type i) :=
  ProtocolSpec.appendTypeFintype (P₁ := M.spec) (P₂ := one .P_to_V (Fin d → F))

/-- The message types of a measurement are nonempty when the masked reduction's are. -/
instance measure_typeNonempty {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1}
    [∀ i, Nonempty (M.spec.Type i)] : ∀ i, Nonempty ((M.measure S L).spec.Type i) :=
  ProtocolSpec.appendTypeNonempty (P₁ := M.spec) (P₂ := one .P_to_V (Fin d → F))

/-- The message types of a measurement on the first claim are finite when the masked reduction's are. -/
instance measureHead_typeFintype {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    [∀ i, Fintype (M.spec.Type i)] : ∀ i, Fintype ((M.measureHead S L).spec.Type i) :=
  ProtocolSpec.appendTypeFintype (P₁ := M.spec) (P₂ := one .P_to_V (Fin d → F))

/-- The message types of a measurement on the first claim are nonempty when the masked reduction's
are. -/
instance measureHead_typeNonempty {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    [∀ i, Nonempty (M.spec.Type i)] : ∀ i, Nonempty ((M.measureHead S L).spec.Type i) :=
  ProtocolSpec.appendTypeNonempty (P₁ := M.spec) (P₂ := one .P_to_V (Fin d → F))

/-- The message types of a stage are finite when the masked reduction's are. -/
instance stage_typeFintype [∀ i, Fintype (M.spec.Type i)] :
    ∀ i, Fintype ((M.stage S L).spec.Type i) :=
  inferInstanceAs (∀ i, Fintype ((M.combine.measure S L).spec.Type i))

/-- The message types of a stage are nonempty when the masked reduction's are. -/
instance stage_typeNonempty [∀ i, Nonempty (M.spec.Type i)] :
    ∀ i, Nonempty ((M.stage S L).spec.Type i) :=
  inferInstanceAs (∀ i, Nonempty ((M.combine.measure S L).spec.Type i))

/-- The message types of the touching claims' combination are finite when the masked reduction's
are. -/
instance touch_typeFintype {Z : Type} {M : MaskedReduction F ι Pub Wit cells Z nc}
    [∀ i, Fintype (M.spec.Type i)] {R : StageRouting nc nt np} :
    ∀ i, Fintype ((M.touch R).spec.Type i) :=
  match R with
  | .none s => inferInstanceAs (∀ i, Fintype ((M.reorder s).prependZero.spec.Type i))
  | .single s => inferInstanceAs
      (∀ i, Fintype ((M.reorder (StageRouting.single s).order).spec.Type i))
  | .combine s h => inferInstanceAs
      (∀ i, Fintype ((M.reorder (StageRouting.combine s h).order).combineFirst.spec.Type i))

/-- The message types of the touching claims' combination are nonempty when the masked
reduction's are. -/
instance touch_typeNonempty {Z : Type} {M : MaskedReduction F ι Pub Wit cells Z nc}
    [∀ i, Nonempty (M.spec.Type i)] {R : StageRouting nc nt np} :
    ∀ i, Nonempty ((M.touch R).spec.Type i) :=
  match R with
  | .none s => inferInstanceAs (∀ i, Nonempty ((M.reorder s).prependZero.spec.Type i))
  | .single s => inferInstanceAs
      (∀ i, Nonempty ((M.reorder (StageRouting.single s).order).spec.Type i))
  | .combine s h => inferInstanceAs
      (∀ i, Nonempty ((M.reorder (StageRouting.combine s h).order).combineFirst.spec.Type i))

/-- The message types of a routed stage are finite when the masked reduction's are. -/
instance routedStage_typeFintype [∀ i, Fintype (M.spec.Type i)] {R : StageRouting nc nt np} :
    ∀ i, Fintype ((M.routedStage R S L).spec.Type i) :=
  inferInstanceAs (∀ i, Fintype (((M.touch R).measureHead S L).spec.Type i))

/-- The message types of a routed stage are nonempty when the masked reduction's are. -/
instance routedStage_typeNonempty [∀ i, Nonempty (M.spec.Type i)] {R : StageRouting nc nt np} :
    ∀ i, Nonempty ((M.routedStage R S L).spec.Type i) :=
  inferInstanceAs (∀ i, Nonempty (((M.touch R).measureHead S L).spec.Type i))

end Types

/-! ### Bijective simulators -/

namespace Honest

variable {In : Type} {dom : Pub → In → Prop}

/-- **Reordering the claims** keeps the simulator. -/
theorem SimBijective.reorder {nc nc' : ℕ} {M : MaskedReduction F ι Pub Wit cells Z nc}
    {view : (ι → F) → Z → F} {SM : M.Sim} {H : M.Honest view In dom SM} (h : H.SimBijective)
    (σ : Fin nc ≃ Fin nc') : (H.reorder σ).SimBijective :=
  h

/-- **Prepending the zero claim** keeps the simulator. -/
theorem SimBijective.prependZero {np : ℕ} {M : MaskedReduction F ι Pub Wit cells Z np}
    {view : (ι → F) → Z → F} {SM : M.Sim} {H : M.Honest view In dom SM} (h : H.SimBijective) :
    H.prependZero.SimBijective :=
  h

variable [Fintype F] [DecidableEq F]

/-- **Combining the first claims** keeps a bijective simulator: the combination challenge is
copied. -/
theorem SimBijective.combineFirst {nt np : ℕ} {M : MaskedReduction F ι Pub Wit cells Z (nt + np)}
    {view : (ι → F) → Z → F} {SM : M.Sim} {H : M.Honest view In dom SM} (h : H.SimBijective) :
    H.combineFirst.SimBijective := fun p =>
  bijective_join_unit (f₁ := fun y => SM.sim p y.1 y.2)
    (f₂ := fun y => (CausalTranscript.oneChallenge (Fin nt → F)).transcript y.1) (h p)
    (CausalTranscript.valuesBijective_oneChallenge (Fin nt → F))

variable [RelFrobeniusOrder F p m e] {S : Stage F ι p m d e ng Y} {L : Level F ι Y}

/-- **A measurement** keeps a bijective simulator: its coins are the measurement. -/
theorem SimBijective.measure {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1}
    {SM : M.Sim} {H : M.Honest (S.level L).view In dom SM} (h : H.SimBijective) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g) :
    (H.measure MH wordOf hword).SimBijective := fun p =>
  bijective_join (f₁ := fun y => SM.sim p y.1 y.2)
    (f₂ := fun y => (CausalTranscript.oneMessage (Msg := Fin d → F) y.2).transcript y.1) (h p)
    (CausalTranscript.valuesBijective_oneMessage (Fin d → F))

/-- **A measurement on the first claim** keeps a bijective simulator: its coins are the
measurement. -/
theorem SimBijective.measureHead {np : ℕ}
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    {SM : M.Sim} {H : M.Honest (S.level L).view In dom SM} (h : H.SimBijective) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g)
    (hpass : M.TailAvoids) : (H.measureHead MH wordOf hword hpass).SimBijective := fun p =>
  bijective_join (f₁ := fun y => SM.sim p y.1 y.2)
    (f₂ := fun y => (CausalTranscript.oneMessage (Msg := Fin d → F) y.2).transcript y.1) (h p)
    (CausalTranscript.valuesBijective_oneMessage (Fin d → F))

variable {nc : ℕ} {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
  {SM : M.Sim} {H : M.Honest (S.level L).view In dom SM}

/-- **A packing stage** keeps a bijective simulator. -/
theorem SimBijective.stage (h : H.SimBijective) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g) :
    (H.stage MH wordOf hword).SimBijective :=
  h.combine.measure MH wordOf hword

/-- **The touching claims' combination** keeps a bijective simulator. -/
theorem SimBijective.touch {Z : Type} {view : (ι → F) → Z → F}
    {M : MaskedReduction F ι Pub Wit cells Z nc} {SM : M.Sim} {H : M.Honest view In dom SM}
    (h : H.SimBijective)
    {nt np : ℕ} (R : StageRouting nc nt np) : (H.touch R).SimBijective :=
  match R with
  | .none s => (h.reorder s).prependZero
  | .single _ => h.reorder _
  | .combine _ _ => (h.reorder _).combineFirst

/-- **A routed stage** keeps a bijective simulator. -/
theorem SimBijective.routedStage {nt np : ℕ} {R : StageRouting nc nt np} (h : H.SimBijective)
    (MH : S.masks.Honest) (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g)
    (hpass : M.PassingAvoid R) : (H.routedStage MH wordOf hword hpass).SimBijective :=
  (h.touch R).measureHead MH wordOf hword (tailAvoids_touch hpass)

end Honest

end FieldProof.MaskedReduction

namespace RingSwitching.Tree

variable {F ι : Type} [Field F] [Fintype ι] {p : ℕ} [ExpChar F p] [Fintype F] [DecidableEq F]
  {Pub Wit : Type} {cells : Wit → ι → F}

/-- The message types of a run are finite when those of the masked reduction it starts from are. -/
def runTypeFintype : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    (M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc) → (∀ i, Fintype (M.spec.Type i)) →
    ∀ i, Fintype ((P.run M).spec.Type i)
  | _, _, .nil, _, h => h
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), M, _ =>
    runTypeFintype rest (M.stage S rest.level) inferInstance
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), M, _ =>
    runTypeFintype rest (M.routedStage R S rest.level) inferInstance

/-- The message types of a run are nonempty when those of the masked reduction it starts from are. -/
theorem runTypeNonempty : {Z : Type} → {nc : ℕ} → (P : Tree F p ι Z nc) →
    (M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc) → (∀ i, Nonempty (M.spec.Type i)) →
    ∀ i, Nonempty ((P.run M).spec.Type i)
  | _, _, .nil, _, h => h
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), M, _ =>
    runTypeNonempty rest (M.stage S rest.level) inferInstance
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S R rest), M, _ =>
    runTypeNonempty rest (M.routedStage R S rest.level) inferInstance

/-- The message types of a run are finite when those of the masked reduction it starts from are. -/
instance run_typeFintype {Z : Type} {nc : ℕ} {P : Tree F p ι Z nc}
    {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} [h : ∀ i, Fintype (M.spec.Type i)] :
    ∀ i, Fintype ((P.run M).spec.Type i) :=
  runTypeFintype P M h

/-- The message types of a run are nonempty when those of the masked reduction it starts from are. -/
instance run_typeNonempty {Z : Type} {nc : ℕ} {P : Tree F p ι Z nc}
    {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} [h : ∀ i, Nonempty (M.spec.Type i)] :
    ∀ i, Nonempty ((P.run M).spec.Type i) :=
  runTypeNonempty P M h

/-- **The honest run keeps a bijective simulator**: every stage's simulator copies its
combination challenge, if any, and sends its coins as the measurement. -/
theorem honestRun_simBijective {In : Type} {dom : Pub → In → Prop} : {Z : Type} → {nc : ℕ} →
    (P : Tree F p ι Z nc) → {M : FieldProof.MaskedReduction F ι Pub Wit cells Z nc} → (hR : P.Routes M) →
    {SM : M.Sim} → {H : M.Honest P.level.view In dom SM} → H.SimBijective → (MH : P.MaskHonest) →
    (val : Pub → In → H.Pads → Z → F) →
    (hval : ∀ p x π w, H.Commits p x π w → ∀ z, P.IsWord z →
      P.level.view (cells w) z = val p x π z) →
    (P.honestRun hR H MH val hval).SimBijective
  | _, _, .nil, _, _, _, _, h, _, _, _ => h
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), _, hR, _, _, h, MH, val, hval =>
    honestRun_simBijective rest hR (h.stage MH.1 _ _) MH.2 _ _
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest), _, hR, _, _, h, MH, val, hval =>
    honestRun_simBijective rest hR.2 (h.routedStage MH.1 _ _ hR.1) MH.2 _ _

end RingSwitching.Tree

end GordieHowe
