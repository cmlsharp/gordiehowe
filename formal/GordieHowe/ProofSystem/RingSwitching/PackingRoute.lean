-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackingStage

@[expose] public section

/-!
# Routed packing stages: combination only over the claims that read the stage

The C++ packing stage (`tree_zk.h`, `TreeRows::stage`) combines only the rows that read its region
and passes the others to the stages above; one touching row is not combined. A **routed stage**
models that: the claims entering the stage split into the touching ones and the passing ones
(`StageRouting`, a structural selection fixed by the instance, as the C++ selection is by the rows'
node sets, `ExtraRows::nodes`); the touching claims are combined with fresh coefficients when there
are two or more (`MaskedReduction.combineFirst`), taken as they are when there is one, and replaced by the
zero claim `0 = 0` when there is none (`MaskedReduction.prependZero`, the paper's `prot:tree` on an empty
`L_i`); the stage measures the result (`MaskedReduction.measureHead`); the passing claims, which read no coordinate of the stage's
child (`Avoids`), become their parts on the parent's coordinates (`restPart`, `eval_of_avoids`).

* **Soundness** (`MaskedReduction.Sound.routedStage`): from the masked reduction's soundness at the child's level,
  the routed stage is sound at the parent's level for "the stage's mask condition implies the
  relation", with the error `1/|K|` at the combination when two or more claims touch, and none
  otherwise (`MaskedReduction.sum_routedStageError`).
* **The honest prover** (`MaskedReduction.Honest.routedStage`): the combination's challenge, then the
  masked measurement with the stage's fresh masks; the simulator sends uniform measurements.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open scoped NNReal

variable {F ι : Type} [Field F] {ng d : ℕ} {Y : Type}

/-- **A claim reads no child coordinate**: its coefficient on every child coordinate is zero. -/
def Avoids (c : AffineForm F (Y ⊕ PackedCoord ng d)) : Prop :=
  ∀ g j, childCoeff c g j = 0

/-- **A claim that reads no child coordinate is its part on the parent's coordinates**
(`eval_split`). -/
theorem eval_of_avoids {c : AffineForm F (Y ⊕ PackedCoord ng d)} (h : Avoids c)
    (z : Y ⊕ PackedCoord ng d → F) : c.eval z = (restPart c).eval (z ∘ Sum.inl) := by
  rw [eval_split c z]
  simp [h _ _]

/-- **A stage's routing** (`TreeRows::stage`, the rows reading the region; structural): the
claims entering the stage split into `nt` touching and `np` passing ones. No touching claim: the
stage measures the zero claim `0 = 0` (`none`, the paper's `prot:tree` with `L_i` empty); one
touching claim is measured as it is (`single`, `tree_zk.h:568-569`); two or more are combined first
(`combine`). -/
inductive StageRouting (nc : ℕ) : ℕ → ℕ → Type
  /-- No touching claim: every claim passes. -/
  | none {np : ℕ} (split : Fin nc ≃ Fin np) : StageRouting nc 0 np
  /-- One touching claim. -/
  | single {np : ℕ} (split : Fin nc ≃ Fin 1 ⊕ Fin np) : StageRouting nc 1 np
  /-- Two or more touching claims, combined with fresh coefficients. -/
  | combine {nt np : ℕ} (split : Fin nc ≃ Fin nt ⊕ Fin np) (two_le : 2 ≤ nt) :
      StageRouting nc nt np

namespace StageRouting

variable {nc nt np : ℕ}

/-- The split of the claims into the touching and the passing ones. -/
def split : StageRouting nc nt np → (Fin nc ≃ Fin nt ⊕ Fin np)
  | .none s => s.trans (Equiv.emptySum (Fin 0) _).symm
  | .single s => s
  | .combine s _ => s

/-- The claims in the order touching, then passing. -/
def order (R : StageRouting nc nt np) : Fin nc ≃ Fin (nt + np) :=
  R.split.trans finSumFinEquiv

/-- The number of combinations of the stage: one when two or more claims touch, none
otherwise. -/
def combinations : StageRouting nc nt np → ℕ
  | .none _ => 0
  | .single _ => 0
  | .combine _ _ => 1

/-- The passing claim `i` in the touching-then-passing order is the passing claim `i` of the
split. -/
theorem order_symm_natAdd (R : StageRouting nc nt np) (i : Fin np) :
    R.order.symm (Fin.natAdd nt i) = R.split.symm (.inr i) := by
  simp [order]

end StageRouting

/-- The claims of `Fin.append a b` all hold exactly when those of `a` and those of `b` do. -/
theorem forall_eval_append_iff {Z : Type} {n₁ n₂ : ℕ} (a : Fin n₁ → AffineForm F Z)
    (b : Fin n₂ → AffineForm F Z) (z : Z → F) :
    (∀ c, (Fin.append a b c).eval z = 0) ↔ (∀ i, (a i).eval z = 0) ∧ ∀ i, (b i).eval z = 0 := by
  rw [Fin.forall_fin_add]
  simp only [Fin.append_left, Fin.append_right]

end GordieHowe

namespace GordieHowe.FieldProof.MaskedReduction

open IOP IOP.ProtocolSpec PackingStage RelativePacking 
open GKR.Schedule (one oneValue)
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {p m d e ng : ℕ} [ExpChar F p] {Y Z : Type}
  {Pub Wit : Type} {cells : Wit → ι → F}

/-! ### Reordering the claims -/

section Reorder

variable {nc nc' : ℕ}

/-- **The claims in another order** (`σ` sends each claim to its new position); no round. -/
def reorder (M : MaskedReduction F ι Pub Wit cells Z nc) (σ : Fin nc ≃ Fin nc') :
    MaskedReduction F ι Pub Wit cells Z nc' where
  toMaskedRowReduction := M.toMaskedRowReduction
  claims p tr i := M.claims p tr (σ.symm i)

theorem outHolds_reorder_iff (M : MaskedReduction F ι Pub Wit cells Z nc) (σ : Fin nc ≃ Fin nc')
    (view : (ι → F) → Z → F) (p : Pub) (tr : M.spec.Transcript (Fin.last M.n)) (x : ι → F) :
    (M.reorder σ).OutHolds view p tr x ↔ M.OutHolds view p tr x :=
  ⟨fun h => ⟨h.rows, fun c => by simpa only [reorder, Equiv.symm_apply_apply] using h.claims (σ c)⟩,
    fun h => ⟨h.rows, fun i => h.claims (σ.symm i)⟩⟩

/-- **Soundness of the reordered claims**: the same reduction and errors. -/
def Sound.reorder {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F}
    {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound view sat ε)
    (σ : Fin nc ≃ Fin nc') : (M.reorder σ).Sound view sat ε where
  reduction := H.reduction
  claim_iff := H.claim_iff
  claimOut_iff p w tr := (H.claimOut_iff p w tr).trans (outHolds_reorder_iff M σ view p tr _).symm

/-- **The honest prover of the reordered claims**: the same prover and simulator. -/
def Honest.reorder {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} {SM : M.Sim} (H : M.Honest view In dom SM) (σ : Fin nc ≃ Fin nc') :
    (M.reorder σ).Honest view In dom SM where
  Pads := H.Pads
  prover := H.prover
  Commits := H.Commits
  complete p x hx π w hw ch :=
    (outHolds_reorder_iff M σ view p _ _).mpr (H.complete p x hx π w hw ch)
  identDistrib := H.identDistrib

end Reorder

/-! ### Combining the first claims -/

section CombineFirst

variable [Fintype F] [DecidableEq F] {nt np : ℕ}

/-- **Combining the first `nt` claims** (`tree_zk.h:553-569` on the touching rows): after the masked
reduction, the verifier draws one coefficient per touching claim, which are replaced by their combination;
the other `np` claims pass unchanged. -/
def combineFirst (M : MaskedReduction F ι Pub Wit cells Z (nt + np)) : MaskedReduction F ι Pub Wit cells Z (1 + np)
    where
  n := M.n + 1
  spec := M.spec ++ one .V_to_P (Fin nt → F)
  Lin := M.Lin
  linear p tr := M.linear p tr.left
  Q := M.Q
  products := M.products
  claims p tr := Fin.append
    (fun _ => combination (oneValue tr.right) fun i => M.claims p tr.left (Fin.castAdd np i))
    fun i => M.claims p tr.left (Fin.natAdd nt i)

/-- **The errors of combining the first claims**: the masked reduction's, then `1/|F|` at the
combination. -/
noncomputable def combineFirstError (M : MaskedReduction F ι Pub Wit cells Z (nt + np))
    (ε : M.spec.ChallengeIdx → ℝ≥0) : M.combineFirst.spec.ChallengeIdx → ℝ≥0 :=
  appendError ε fun _ => 1 / Fintype.card F

theorem sum_combineFirstError (M : MaskedReduction F ι Pub Wit cells Z (nt + np))
    (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.combineFirstError ε i = ∑ i, ε i + 1 / Fintype.card F := by
  refine (sum_appendError (P₁ := M.spec) (P₂ := one .V_to_P (Fin nt → F)) ε _).trans ?_
  congr 1
  rw [Fintype.sum_equiv (GKR.Schedule.verifierIndex (Fin nt → F)) _
    (fun _ => (1 : ℝ≥0) / Fintype.card F) fun _ => rfl]
  simp

theorem outHolds_combineFirst_iff (M : MaskedReduction F ι Pub Wit cells Z (nt + np))
    (view : (ι → F) → Z → F) (p : Pub)
    (tr : M.combineFirst.spec.Transcript (Fin.last M.combineFirst.n))
    (x : ι → F) :
    M.combineFirst.OutHolds view p tr x ↔
      RowsHold (M.linear p tr.left) M.products x ∧
        ∑ i, oneValue tr.right i * (M.claims p tr.left (Fin.castAdd np i)).eval (view x) = 0 ∧
        ∀ i, (M.claims p tr.left (Fin.natAdd nt i)).eval (view x) = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (forall_eval_append_iff _ _ _).mp h.claims
    have hc := h1 0
    rw [eval_combination] at hc
    exact ⟨h.rows, hc, h2⟩
  · rintro ⟨hr, hc, hp⟩
    refine ⟨hr, (forall_eval_append_iff _ _ _).mpr ⟨fun _ => ?_, hp⟩⟩
    rw [eval_combination]
    exact hc

omit [Fintype F] [DecidableEq F] in
/-- The claims of a masked reduction on `nt + np` claims hold exactly when the first `nt` and the last `np`
do. -/
theorem outHolds_iff_castAdd_natAdd (M : MaskedReduction F ι Pub Wit cells Z (nt + np))
    {view : (ι → F) → Z → F} {p : Pub} {tr : M.spec.Transcript (Fin.last M.n)} {x : ι → F} :
    M.OutHolds view p tr x ↔ RowsHold (M.linear p tr) M.products x ∧
      (∀ i, (M.claims p tr (Fin.castAdd np i)).eval (view x) = 0) ∧
      ∀ i, (M.claims p tr (Fin.natAdd nt i)).eval (view x) = 0 :=
  ⟨fun h => ⟨h.rows, (Fin.forall_fin_add _).mp h.claims⟩,
    fun h => ⟨h.1, (Fin.forall_fin_add _).mpr h.2⟩⟩

/-- **Soundness of combining the first claims**: the masked reduction's reduction, then the combination
challenge, whose event (`CombinationBad` of the touching claims' values) has probability at most
`1/|F|` (`card_filter_combination_le`); the passing claims are carried. -/
noncomputable def Sound.combineFirst {M : MaskedReduction F ι Pub Wit cells Z (nt + np)}
    {view : (ι → F) → Z → F} {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0}
    (S : M.Sound view sat ε) : M.combineFirst.Sound view sat (M.combineFirstError ε) :=
  let vals : AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec → Fin nt → F :=
    fun c i => (M.claims c.ctx.pub c.transcript (Fin.castAdd np i)).eval (view (cells c.ctx.wit))
  let R₂ : ClaimReduction (one .V_to_P (Fin nt → F))
      (AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec) (fun _ => 1 / Fintype.card F) :=
    ChallengeEventReduction.reduction (one .V_to_P (Fin nt → F))
      (fun _ c _ ρ => CombinationBad (vals c) ρ)
      (fun c => M.OutHolds view c.ctx.pub c.transcript (cells c.ctx.wit))
      (fun c tr => RowsHold (M.linear c.ctx.pub c.transcript) M.products (cells c.ctx.wit) ∧
        ∑ i, oneValue tr i * vals c i = 0 ∧
        ∀ i, (M.claims c.ctx.pub c.transcript (Fin.natAdd nt i)).eval (view (cells c.ctx.wit)) = 0)
      (fun _ => 1 / Fintype.card F)
      (fun c _ _ => card_filter_combination_le (vals c))
      (fun c tr h => by
        by_cases hall : ∀ i, vals c i = 0
        · exact Or.inl ((outHolds_iff_castAdd_natAdd M).mpr ⟨h.1, hall, h.2.2⟩)
        · push Not at hall
          exact Or.inr ⟨⟨0, rfl⟩, Nat.one_pos, hall, h.2.1⟩)
  { reduction := S.reduction.seq R₂ fun c tr h => (S.claimOut_iff c.pub c.wit tr).mpr h
    claim_iff := S.claim_iff
    claimOut_iff := fun p w tr => (outHolds_combineFirst_iff M view p tr (cells w)).symm }

/-- **The simulator of combining the first claims**: the masked reduction's simulator, then the
combination challenge.

Running time: the masked reduction's simulator's and a copy of the challenge.
This running time is argued here, not proved in Lean. -/
def Sim.combineFirst {M : MaskedReduction F ι Pub Wit cells Z (nt + np)} (SM : M.Sim) :
    M.combineFirst.Sim where
  SimCoins := SM.SimCoins
  sim p ch s := Transcript.join (SM.sim p ch.left s)
    ((CausalTranscript.oneChallenge (Fin nt → F)).transcript ch.right)

/-- **The honest prover of combining the first claims**: the masked reduction's prover, then the
combination challenge, simulated by `Sim.combineFirst`. -/
def Honest.combineFirst {M : MaskedReduction F ι Pub Wit cells Z (nt + np)} {view : (ι → F) → Z → F}
    {In : Type} {dom : Pub → In → Prop} {SM : M.Sim} (H : M.Honest view In dom SM) :
    M.combineFirst.Honest view In dom SM.combineFirst where
  Pads := H.Pads
  prover p x π := (H.prover p x π).append fun _ => CausalTranscript.oneChallenge (Fin nt → F)
  Commits := H.Commits
  complete p x hx π w hw ch := by
    have e₁ := CausalTranscript.append_left (H.prover p x π)
      (fun _ => CausalTranscript.oneChallenge (Fin nt → F)) ch
    have h := (congrArg (fun tr => M.OutHolds view p tr (cells w)) e₁).mpr
      (H.complete p x hx π w hw ch.left)
    obtain ⟨hr, ht, hp⟩ := (outHolds_iff_castAdd_natAdd M).mp h
    refine (outHolds_combineFirst_iff M view p _ (cells w)).mpr ⟨hr, ?_, hp⟩
    exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (ht i)
  identDistrib p x ch := (H.identDistrib p x ch.left).comp fun v =>
    Transcript.join v ((CausalTranscript.oneChallenge (Fin nt → F)).transcript ch.right)

end CombineFirst

/-! ### Prepending the zero claim -/

section PrependZero

variable {np : ℕ}

/-- **The zero claim `0 = 0` before the claims** (the paper's `prot:tree` on an empty `L_i`); no
round. -/
def prependZero (M : MaskedReduction F ι Pub Wit cells Z np) : MaskedReduction F ι Pub Wit cells Z (1 + np) where
  toMaskedRowReduction := M.toMaskedRowReduction
  claims p tr := Fin.append (fun _ => 0) (M.claims p tr)

theorem outHolds_prependZero_iff (M : MaskedReduction F ι Pub Wit cells Z np) (view : (ι → F) → Z → F)
    (p : Pub) (tr : M.spec.Transcript (Fin.last M.n)) (x : ι → F) :
    M.prependZero.OutHolds view p tr x ↔ M.OutHolds view p tr x := by
  constructor
  · intro h
    exact ⟨h.rows, ((forall_eval_append_iff _ _ _).mp h.claims).2⟩
  · intro h
    exact ⟨h.rows, (forall_eval_append_iff _ _ _).mpr ⟨fun _ => AffineForm.eval_zero _, h.claims⟩⟩

/-- **Soundness with the zero claim prepended**: the same reduction and errors. -/
def Sound.prependZero {M : MaskedReduction F ι Pub Wit cells Z np} {view : (ι → F) → Z → F}
    {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound view sat ε) :
    M.prependZero.Sound view sat ε where
  reduction := H.reduction
  claim_iff := H.claim_iff
  claimOut_iff p w tr := (H.claimOut_iff p w tr).trans (outHolds_prependZero_iff M view p tr _).symm

/-- **The honest prover with the zero claim prepended**: the same prover and simulator. -/
def Honest.prependZero {M : MaskedReduction F ι Pub Wit cells Z np} {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} {SM : M.Sim} (H : M.Honest view In dom SM) :
    M.prependZero.Honest view In dom SM where
  Pads := H.Pads
  prover := H.prover
  Commits := H.Commits
  complete p x hx π w hw ch :=
    (outHolds_prependZero_iff M view p _ _).mpr (H.complete p x hx π w hw ch)
  identDistrib := H.identDistrib

end PrependZero

/-! ### Measuring the first claim, passing the others -/

section MeasureHead

variable {np : ℕ}

/-- **The measurement of a stage on the first claim**, the others passing: the prover sends
`M ∈ K^d`; the first claim is replaced by the stage's `d + 1` rows on `Y`, each passing claim by its
part on `Y` (`restPart`), and the masks' product triples join the rows on the cells. -/
def measureHead [Fintype F] [DecidableEq F]
    (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np))
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) : MaskedReduction F ι Pub Wit cells Y (d + 1 + np) where
  n := M.n + 1
  spec := M.spec ++ one .P_to_V (Fin d → F)
  Lin := M.Lin
  linear p tr := M.linear p tr.left
  Q := M.Q ⊕ S.masks.Q
  products := M.products.sum S.masks.products
  claims p tr :=
    Fin.append (S.rows L.cell (M.claims p tr.left (Fin.castAdd np 0)) (oneValue tr.right))
    fun i => restPart (M.claims p tr.left (Fin.natAdd 1 i))

/-- **The measurement's errors**: none at its round (a prover message only). -/
def measureHeadError [Fintype F] [DecidableEq F]
    (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np))
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    (M.measureHead S L).spec.ChallengeIdx → ℝ≥0 :=
  appendError ε fun _ => 0

theorem sum_measureHeadError [Fintype F] [DecidableEq F]
    (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np))
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.measureHeadError S L ε i = ∑ i, ε i := by
  refine (sum_appendError (P₁ := M.spec) (P₂ := one .P_to_V (Fin d → F)) ε _).trans ?_
  simp

/-- **The claims after the first read no child coordinate**, at every public input and
transcript. -/
def TailAvoids (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)) : Prop :=
  ∀ p tr i, Avoids (M.claims p tr (Fin.natAdd 1 i))

theorem outHolds_measureHead_iff [Fintype F] [DecidableEq F]
    (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np))
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (p : Pub)
    (tr : (M.measureHead S L).spec.Transcript (Fin.last (M.measureHead S L).n)) (x : ι → F) :
    (M.measureHead S L).OutHolds L.view p tr x ↔
      RowsHold (M.linear p tr.left) (M.products.sum S.masks.products) x ∧
        (∀ i, (S.rows L.cell (M.claims p tr.left (Fin.castAdd np 0)) (oneValue tr.right) i).eval
          (L.view x) = 0) ∧
        ∀ i, (restPart (M.claims p tr.left (Fin.natAdd 1 i))).eval (L.view x) = 0 :=
  ⟨fun h => ⟨h.rows, (forall_eval_append_iff _ _ _).mp h.claims⟩,
    fun h => ⟨h.1, (forall_eval_append_iff _ _ _).mpr h.2⟩⟩

omit [Fintype ι] in
/-- A passing claim at the child's level is its part at the parent's level. -/
theorem eval_level_of_avoids (S : Stage F ι p m d e ng Y) (L : Level F ι Y)
    {c : AffineForm F (Y ⊕ PackedCoord ng d)} (h : Avoids c) (x : ι → F) :
    c.eval ((S.level L).view x) = (restPart c).eval (L.view x) :=
  eval_of_avoids h _

variable [RelFrobeniusOrder F p m e]

/-- **Soundness of a stage's measurement on the first claim**: exact, so the errors are the
masked reduction's; the relation becomes "the masks' condition `Valid` implies the relation". The first
claim follows from the stage's rows (`Stage.claim_of_rows`), each passing claim from its part on
`Y` (`eval_level_of_avoids`). -/
noncomputable def Sound.measureHead [Fintype F] [DecidableEq F]
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {sat : Pub → Wit → Prop}
    {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound (S.level L).view sat ε) (hpass : M.TailAvoids) :
    (M.measureHead S L).Sound L.view (fun p w => S.masks.Valid (cells w) → sat p w)
      (M.measureHeadError S L ε) :=
  let R₂ : ClaimReduction (one .P_to_V (Fin d → F))
      (AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec) (fun _ => 0) :=
    ChallengeEventReduction.reduction (one .P_to_V (Fin d → F)) (fun _ _ _ _ => False)
      (fun c => S.masks.Valid (cells c.ctx.wit) →
        M.OutHolds (S.level L).view c.ctx.pub c.transcript (cells c.ctx.wit))
      (fun c tr => RowsHold (M.linear c.ctx.pub c.transcript) (M.products.sum S.masks.products)
          (cells c.ctx.wit) ∧
        (∀ i, (S.rows L.cell (M.claims c.ctx.pub c.transcript (Fin.castAdd np 0)) (oneValue tr)
          i).eval (L.view (cells c.ctx.wit)) = 0) ∧
        ∀ i, (restPart (M.claims c.ctx.pub c.transcript (Fin.natAdd 1 i))).eval
          (L.view (cells c.ctx.wit)) = 0)
      (fun _ => 0)
      (fun _ _ _ => by simp)
      (fun c tr h => by
        refine Or.inl fun hv => ?_
        have hp := (Ligero.Routing.sourceProducts_sum _ _ _).mp h.1.products
        refine (outHolds_iff_castAdd_natAdd M).mpr ⟨⟨h.1.linear, hp.1⟩, fun i => ?_,
          fun i => ?_⟩
        · rw [Subsingleton.elim i 0]
          exact Stage.claim_of_rows S L _ _ hp.2 hv h.2.1
        · rw [eval_level_of_avoids S L (hpass _ _ i)]
          exact h.2.2 i)
  { reduction := (H.reduction.imp fun c => S.masks.Valid (cells c.wit)).seq R₂
      fun c tr h hv => (H.claimOut_iff c.pub c.wit tr).mpr (h hv)
    claim_iff := fun p w => imp_congr_right fun _ => H.claim_iff p w
    claimOut_iff := fun p w tr => by
      rw [outHolds_measureHead_iff]
      constructor
      · intro h
        exact ⟨h.1, h.2.1, h.2.2⟩
      · intro h
        exact ⟨h.1, h.2.1, h.2.2⟩ }

/-- **The simulator of a stage's measurement on the first claim**: the masked reduction's simulator,
then a uniform measurement.

Running time: the masked reduction's simulator's and a copy of `d` field elements.
This running time is argued here, not proved in Lean. -/
def Sim.measureHead [Fintype F] [DecidableEq F]
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (SM : M.Sim) : (M.measureHead S L).Sim where
  SimCoins := SM.SimCoins × (Fin d → F)
  sim p ch s := Transcript.join (SM.sim p ch.left s.1)
    ((CausalTranscript.oneMessage (Msg := Fin d → F) s.2).transcript ch.right)

/-- **The honest prover of a stage's measurement on the first claim**: the masked reduction's prover, then
the masked measurement of the first claim on the words (`wordOf`, tied to the committed cells by
`hword`) with the stage's fresh masks, simulated by `Sim.measureHead` (uniform measurements). -/
def Honest.measureHead [Fintype F] [DecidableEq F]
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {In : Type} {dom : Pub → In → Prop}
    {SM : M.Sim} (H : M.Honest (S.level L).view In dom SM) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g)
    (hpass : M.TailAvoids) :
    (M.measureHead S L).Honest L.view In dom (Sim.measureHead S L SM) where
  Pads := H.Pads × MH.Pads
  prover p x π := (H.prover p x π.1).append fun tr =>
    CausalTranscript.oneMessage
      (S.measurement (M.claims p tr (Fin.castAdd np 0)) (wordOf p x π.1) (MH.sigmaOf π.2))
  Commits p x π w := H.Commits p x π.1 w ∧ MH.Commits π.2 (cells w)
  complete p x hx π w hw ch := by
    have e₁ := CausalTranscript.append_left (H.prover p x π.1) (fun tr =>
      CausalTranscript.oneMessage (S.measurement (M.claims p tr (Fin.castAdd np 0))
        (wordOf p x π.1) (MH.sigmaOf π.2))) ch
    have e₂ := CausalTranscript.append_right (H.prover p x π.1) (fun tr =>
      CausalTranscript.oneMessage (S.measurement (M.claims p tr (Fin.castAdd np 0))
        (wordOf p x π.1) (MH.sigmaOf π.2))) ch
    have hM := H.complete p x hx π.1 w hw.1 ch.left
    obtain ⟨hr, ht, hp⟩ := (outHolds_iff_castAdd_natAdd M).mp hM
    have h := (congrArg (fun tr => M.OutHolds (S.level L).view p tr (cells w)) e₁).mpr hM
    have hW : wordOf p x π.1 = fun g => L.view (cells w) (S.word g) :=
      funext fun g => (hword p x π.1 w hw.1 g).symm
    have hσ : MH.sigmaOf π.2 = fun k => (S.masks.sigma k).eval (cells w) :=
      funext fun k => (MH.sigma_eval π.2 _ hw.2 k).symm
    have hv := congrArg oneValue e₂
    refine (outHolds_measureHead_iff M S L p _ (cells w)).mpr
      ⟨⟨h.rows.linear, (Ligero.Routing.sourceProducts_sum _ _ _).mpr
        ⟨h.rows.products, MH.products _ _ hw.2⟩⟩, fun i => ?_, fun i => ?_⟩
    · have key : ∀ i, (S.rows L.cell (M.claims p ((H.prover p x π.1).transcript ch.left)
          (Fin.castAdd np 0)) (S.measurement (M.claims p ((H.prover p x π.1).transcript ch.left)
            (Fin.castAdd np 0)) (wordOf p x π.1) (MH.sigmaOf π.2)) i).eval (L.view (cells w)) =
            0 := by
        rw [hW, hσ]
        exact Stage.rows_of_claim S L _ (MH.products _ _ hw.2) (MH.valid _ _ hw.2) (ht 0)
      convert key i using 1
      exact congrArg₂ (fun a b => (S.rows L.cell (M.claims p a (Fin.castAdd np 0)) b i).eval
        (L.view (cells w))) e₁ hv
    · rw [← eval_level_of_avoids S L (hpass _ _ i)]
      exact (congrArg (fun tr => (M.claims p tr (Fin.natAdd 1 i)).eval
        ((S.level L).view (cells w)) = 0) e₁).mpr (hp i)
  identDistrib p x ch := by
    refine (IdentDistrib.dependent (f₁ := fun π₁ => (H.prover p x π₁).transcript ch.left)
      (g₁ := SM.sim p ch.left)
      (f₂ := fun π₁ π₂ => (CausalTranscript.oneMessage (S.measurement
        (M.claims p ((H.prover p x π₁).transcript ch.left) (Fin.castAdd np 0)) (wordOf p x π₁)
        (MH.sigmaOf π₂))).transcript ch.right)
      (g₂ := fun _ s => (CausalTranscript.oneMessage (Msg := Fin d → F) s).transcript ch.right)
      (H.identDistrib p x ch.left) fun π₁ => ?_).comp fun v => Transcript.join v.1 v.2
    let z : Fin d → F := fun k => ∑ g, S.basis.form e
      (childCoeff (M.claims p ((H.prover p x π₁).transcript ch.left) (Fin.castAdd np 0)) g) k *
        wordOf p x π₁ g
    have hu : (fun π₂ => z + MH.sigmaOf π₂) =ᵈ (id : (Fin d → F) → Fin d → F) :=
      (MH.uniform.comp fun v => z + v).trans (Uniform.of_equiv (Equiv.addLeft z))
    exact hu.comp fun s => (CausalTranscript.oneMessage (Msg := Fin d → F) s).transcript ch.right

end MeasureHead

/-! ### The routed stage -/

section Routed

variable [Fintype F] [DecidableEq F] {nc nt np : ℕ}

/-- **The touching claims as one claim before the passing ones** (`TreeRows::stage`): the claims
in the order touching, then passing (`reorder`); the zero claim before them when none touches
(`prependZero`), the touching claim as it is when one does, their combination when two or more do
(`combineFirst`). -/
def touch (M : MaskedReduction F ι Pub Wit cells Z nc) (R : StageRouting nc nt np) :
    MaskedReduction F ι Pub Wit cells Z (1 + np) :=
  match R with
  | .none s => (M.reorder s).prependZero
  | .single s => M.reorder (StageRouting.single s).order
  | .combine s h => (M.reorder (StageRouting.combine s h).order).combineFirst

/-- **The errors of the touching claims' combination**: the masked reduction's, then `1/|F|` at the
combination when two or more claims touch. -/
noncomputable def touchError (M : MaskedReduction F ι Pub Wit cells Z nc) (R : StageRouting nc nt np)
    (ε : M.spec.ChallengeIdx → ℝ≥0) : (M.touch R).spec.ChallengeIdx → ℝ≥0 :=
  match R with
  | .none _ => ε
  | .single _ => ε
  | .combine s h => (M.reorder (StageRouting.combine s h).order).combineFirstError ε

/-- **The combination adds `1/|F|` exactly when two or more claims touch.** -/
theorem sum_touchError (M : MaskedReduction F ι Pub Wit cells Z nc) (R : StageRouting nc nt np)
    (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.touchError R ε i = ∑ i, ε i + R.combinations / Fintype.card F := by
  cases R with
  | none s =>
    simp only [touchError, StageRouting.combinations, Nat.cast_zero, zero_div, add_zero]
    rfl
  | single s =>
    simp only [touchError, StageRouting.combinations, Nat.cast_zero, zero_div, add_zero]
    rfl
  | combine s h =>
    simp only [touchError, StageRouting.combinations, Nat.cast_one]
    exact sum_combineFirstError (M.reorder (StageRouting.combine s h).order) ε

/-- **Soundness of the touching claims' combination**: the same relation (`Sound.reorder`,
`Sound.prependZero`, `Sound.combineFirst`). -/
noncomputable def Sound.touch {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F}
    {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound view sat ε)
    (R : StageRouting nc nt np) : (M.touch R).Sound view sat (M.touchError R ε) :=
  match R with
  | .none s => (H.reorder s).prependZero
  | .single _ => H.reorder _
  | .combine _ _ => (H.reorder _).combineFirst

/-- **The simulator of the touching claims' combination**: the masked reduction's simulator, with
the combination's challenge when two or more claims touch (`Sim.combineFirst`).

Running time: the masked reduction's simulator's and a copy of the challenge.
This running time is argued here, not proved in Lean. -/
def Sim.touch {M : MaskedReduction F ι Pub Wit cells Z nc} (SM : M.Sim) (R : StageRouting nc nt np) :
    (M.touch R).Sim :=
  match R with
  | .none _ => SM
  | .single _ => SM
  | .combine _ _ => SM.combineFirst

/-- **The honest prover of the touching claims' combination**: the masked reduction's pads and
commitment; the combination's challenge when two or more claims touch (`Honest.reorder`,
`Honest.prependZero`, `Honest.combineFirst`); simulated by `Sim.touch`. -/
def Honest.touch {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} {SM : M.Sim} (H : M.Honest view In dom SM) (R : StageRouting nc nt np) :
    (M.touch R).Honest view In dom (SM.touch R) where
  Pads := H.Pads
  prover :=
    match R with
    | .none s => (H.reorder s).prependZero.prover
    | .single s => (H.reorder (StageRouting.single s).order).prover
    | .combine s h => (H.reorder (StageRouting.combine s h).order).combineFirst.prover
  Commits := H.Commits
  complete :=
    match R with
    | .none s => (H.reorder s).prependZero.complete
    | .single s => (H.reorder (StageRouting.single s).order).complete
    | .combine s h => (H.reorder (StageRouting.combine s h).order).combineFirst.complete
  identDistrib :=
    match R with
    | .none s => (H.reorder s).prependZero.identDistrib
    | .single s => (H.reorder (StageRouting.single s).order).identDistrib
    | .combine s h => (H.reorder (StageRouting.combine s h).order).combineFirst.identDistrib

/-- **The passing claims of a masked reduction read no child coordinate** under the routing `R`. -/
def PassingAvoid (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (R : StageRouting nc nt np) : Prop :=
  ∀ p tr i, Avoids (M.claims p tr (R.split.symm (.inr i)))

omit [Fintype F] [DecidableEq F] in
/-- With no touching claim, the claims after the prepended zero claim are the passing ones. -/
theorem passingAvoid_prependZero {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {s : Fin nc ≃ Fin np} (h : M.PassingAvoid (.none s)) :
    (M.reorder s).prependZero.TailAvoids := fun p tr i => by
  change Avoids (Fin.append _ _ (Fin.natAdd 1 i))
  rw [Fin.append_right]
  change Avoids (M.claims p tr (s.symm i))
  simpa [PassingAvoid, StageRouting.split] using h p tr i

omit [Fintype F] [DecidableEq F] in
/-- With one touching claim, the reordered claims after the first are the passing ones. -/
theorem passingAvoid_reorder_single {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {s : Fin nc ≃ Fin 1 ⊕ Fin np} (h : M.PassingAvoid (.single s)) :
    (M.reorder (StageRouting.single s).order).TailAvoids := fun p tr i => by
  change Avoids (M.claims p tr ((StageRouting.single s).order.symm (Fin.natAdd 1 i)))
  rw [StageRouting.order_symm_natAdd]
  exact h p tr i

/-- With two or more touching claims, the combined masked reduction's claims after the first are the
passing ones. -/
theorem passingAvoid_combineFirst {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {s : Fin nc ≃ Fin nt ⊕ Fin np} {h2 : 2 ≤ nt} (h : M.PassingAvoid (.combine s h2)) :
    (M.reorder (StageRouting.combine s h2).order).combineFirst.TailAvoids := fun p tr i => by
  change Avoids (Fin.append _ _ (Fin.natAdd 1 i))
  rw [Fin.append_right]
  change Avoids (M.claims p tr.left ((StageRouting.combine s h2).order.symm (Fin.natAdd nt i)))
  rw [StageRouting.order_symm_natAdd]
  exact h p tr.left i

/-- **The claims after the touching claims' combination are the passing ones**, which read no child
coordinate. -/
theorem tailAvoids_touch {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {R : StageRouting nc nt np} (h : M.PassingAvoid R) : (M.touch R).TailAvoids :=
  match R, h with
  | .none _, h => passingAvoid_prependZero h
  | .single _, h => passingAvoid_reorder_single h
  | .combine _ _, h => passingAvoid_combineFirst h

/-- **A routed stage** (`TreeRows::stage`): the touching claims as one claim (`touch`), then the
measurement of the stage on it, the passing claims becoming their parts on `Y`
(`measureHead`). -/
def routedStage (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (R : StageRouting nc nt np) (S : Stage F ι p m d e ng Y) (L : Level F ι Y) :
    MaskedReduction F ι Pub Wit cells Y (d + 1 + np) :=
  (M.touch R).measureHead S L

/-- **The errors of a routed stage**: the masked reduction's, `1/|K|` at the combination when two or more
claims touch, none at the measurement. -/
noncomputable def routedStageError (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (R : StageRouting nc nt np) (S : Stage F ι p m d e ng Y) (L : Level F ι Y)
    (ε : M.spec.ChallengeIdx → ℝ≥0) : (M.routedStage R S L).spec.ChallengeIdx → ℝ≥0 :=
  (M.touch R).measureHeadError S L (M.touchError R ε)

/-- **A routed stage adds `1/|K|` exactly when two or more claims touch it.** -/
theorem sum_routedStageError (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (R : StageRouting nc nt np) (S : Stage F ι p m d e ng Y) (L : Level F ι Y)
    (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.routedStageError R S L ε i = ∑ i, ε i + R.combinations / Fintype.card F :=
  (sum_measureHeadError (M.touch R) S L _).trans (sum_touchError M R ε)

variable [RelFrobeniusOrder F p m e]

/-- **Soundness of a routed stage**: from the masked reduction's soundness at the child's level and the
passing claims reading no child coordinate, the routed stage is sound at the parent's level for
"the masks' condition implies the relation", with the errors `routedStageError` (`Sound.touch`,
`Sound.measureHead`). -/
noncomputable def Sound.routedStage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {R : StageRouting nc nt np} {S : Stage F ι p m d e ng Y} {L : Level F ι Y}
    {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound (S.level L).view sat ε)
    (hpass : M.PassingAvoid R) :
    (M.routedStage R S L).Sound L.view (fun p w => S.masks.Valid (cells w) → sat p w)
      (M.routedStageError R S L ε) :=
  (H.touch R).measureHead (tailAvoids_touch hpass)

/-- **The simulator of a routed stage**: the touching claims' combination's (`Sim.touch`), then a
uniform measurement (`Sim.measureHead`).

Running time: the masked reduction's simulator's, a copy of the challenge and of `d` field
elements. This running time is argued here, not proved in Lean. -/
def Sim.routedStage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    (R : StageRouting nc nt np) (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (SM : M.Sim) :
    (M.routedStage R S L).Sim :=
  Sim.measureHead S L (SM.touch R)

/-- **The honest prover of a routed stage**: the touching claims' combination (`Honest.touch`),
then the measurement's honest prover with the stage's fresh masks; its pads are the masked
reduction's and the masks'. It is simulated by `Sim.routedStage`. -/
def Honest.routedStage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {R : StageRouting nc nt np} {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {In : Type}
    {dom : Pub → In → Prop} {SM : M.Sim} (H : M.Honest (S.level L).view In dom SM)
    (MH : S.masks.Honest) (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g)
    (hpass : M.PassingAvoid R) :
    (M.routedStage R S L).Honest L.view In dom (Sim.routedStage R S L SM) :=
  (H.touch R).measureHead MH wordOf hword (tailAvoids_touch hpass)

end Routed

end GordieHowe.FieldProof.MaskedReduction
