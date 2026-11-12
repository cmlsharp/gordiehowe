-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeBlock
public import GordieHowe.Model.Quantum.Interactive.AbortBlock
public import GordieHowe.Model.Quantum.Interactive.ComposeSwap
public import GordieHowe.Model.Quantum.Interactive.MultiRelayLogs
public import GordieHowe.Model.QROM.SimPMF

@[expose] public section

/-!
# The block hypotheses of the key-free adversary at the extraction law

For a key-free adversary `A` and other Kraus maps `st'` satisfying the block hypotheses along a
witness swap (`AdaptiveIAlg.BlockRel` along `jTrip σW sw J`, `AdaptiveIAlg.BlockNone`), the
extraction law of the simulation-extraction adversary `seAlgKF` (`simPMF` of `extAdv`) is the
same for `A.withStep st'` and `A` on the events of one block: the absorption with a table
(`BlockRel.absorbTab`), the trace-preserving form (`BlockRel.toTP`), the composition with the
simulation challenger along the swap (`KindAlg.composeBothOut_block_cw`) and the expanded run
(`simLaw_expandCoh_of_blockRel`, `simLaw_expandCoh_of_blockNone`).

- `QROM.simLaw_expandCoh_eq_of_blockRel`, `QROM.simLaw_expandCoh_eq_of_blockNone`: the block
  lemmas of the expanded run for an algorithm equal to one with other Kraus maps.
- `AdaptiveIAlg.mem_iff_of_forall₂_perm`, `AdaptiveIAlg.mem_take_requests_logFam`: a request fixed
  by an entrywise permutation of the logs is among the first requests of both logs or of neither.
- `AdaptiveIAlg.prevSeq_subset`, `AdaptiveIAlg.BlockRel.mono`, `AdaptiveIAlg.BlockNone.mono`: the
  block hypotheses on smaller sets.
- `AdaptiveIAlg.slotLogSet`, `AdaptiveIAlg.logTabSet`, `AdaptiveIAlg.afterIdx_prevIdx_self`,
  `AdaptiveIAlg.keepsSet_stepTab_logTabSet`: the well-formed states of the absorbed adversary
  whose log of the index's slot holds the adversary's request, which the absorbed steps keep.
- `AdaptiveIAlg.tTrip_mem_slotLogSet`, `AdaptiveIAlg.BlockRel.absorbTabLog`,
  `AdaptiveIAlg.BlockNone.absorbTabLog`: the block hypotheses through the absorption on those
  states.
- `AdaptiveIAlg.jTrip_refl_apply`, `AdaptiveIAlg.tripPerm_prevSeq_jTrip_refl`,
  `AdaptiveIAlg.rowGram_map_some`, `AdaptiveIAlg.rowGram_map_some_none`,
  `AdaptiveIAlg.BlockNone.mapSome`, `AdaptiveIAlg.BlockNone.toBlockRel`: the `none`-block
  hypotheses are block hypotheses at the identity swap, on the block `none` of the label read
  through `some`.
- `AdaptiveIAlg.SwapFixAway`, `AdaptiveIAlg.swapHyps_absorbTab`: the requests away from the
  recorded slot fixed by the swap, and `KindAlg.SwapHyps` for the trace-preserving form of the
  absorbed adversary.
- `AdaptiveIAlg.exists_block_composeBothOut_withStep`,
  `AdaptiveIAlg.simLaw_expand_withStep_eq_of_swapHyps`,
  `AdaptiveIAlg.simLaw_expand_withStep_mass_of_swapHyps`: from `KindAlg.SwapHyps`, the
  composition's block hypotheses and the expanded runs on one block and on its mass.
- `AdaptiveIAlg.absorbTab_mapOut_withStep`, `AdaptiveIAlg.toTPKindAlg_withStep`,
  `AdaptiveIAlg.finalSwap`: the adversary with other Kraus maps through the wrappers, and the
  final witness swap of the composed registers.
- `RingSignature.KeyFree.kfFinalSwap`, `advOut_kfFinalSwap`, `simQueryInputs_kfFinalSwap`,
  `finalAss_kfFinalSwap`, `simExtractionExpansion_next_kfFinalSwap`: the final swap of the
  extraction run of `seAlgKF` keeps the claim, the simulator's query inputs, the final assignments
  and so the extraction queries.
- `KFOutcome`, `kfLabel`, `kfSwapOut`, `simExtractionExpansion_withStep_next`: the outcomes, their
  label and final swap; the extraction queries do not read the steps.
- `simPMF_congr_shape`: the extraction laws of equal adversaries, cast to one outcome type.
- `KFSwapBlock`: the hypotheses of the block layers.
- `toOuterMeasure_extLaw_withStep_eq` (events of label `some r` kept by the final swap) and
  `toOuterMeasure_extLaw_withStep_label` (the block mass), and
  `toOuterMeasure_extLaw_withStep_label_of_blockNone` (the block mass from `BlockNone` alone).
- `kfClaim`, `kfMainLogs`, `ReadsClaimDB`, `kfLabel_kfSwapOut`, `kfClaim_kfSwapOut`,
  `mem_kfMainLogs_kfSwapOut`, `toOuterMeasure_extLaw_withStep_label_and`: events of label `some r`
  read by the claim, the database and the corruptions among the first `Q` main requests.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv KrausRel

section WithStepLaw

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {Bc Cc : Type} (e : BitStr I J ≃ Bc) (E : Expansion (Bits m) Bc Cc) (k : ℕ)

/-- **`simLaw_expandCoh_of_blockRel` for an algorithm equal to `A` with other Kraus maps**, both
outputs read with their default outputs. -/
theorem simLaw_expandCoh_eq_of_blockRel {L : Type} {Ac X : Alg (Bits m) (BitStr I J) Cc}
    {K' : Fin (Ac.depth + 1) → KrausMap Ac.R (QueryReg Ac.V 1 (Bits m) (BitStr I J))
      (QueryReg Ac.V 1 (Bits m) (BitStr I J))}
    (heq : X = { Ac with step := K' }) (hAc : Ac.TracePreserving) (hX : X.TracePreserving)
    {ℓ : Ac.V → Option L} {G G' : Fin (Ac.depth + 1) → Set Ac.V} {G₀ G₀' : Set Ac.V}
    {τ : Fin (Ac.depth + 1) → Equiv.Perm Ac.V} {τ₀ : Equiv.Perm Ac.V}
    {ρ : Fin (Ac.depth + 1) → Equiv.Perm Ac.R} {r : L}
    (h : Ac.BlockRel K' ℓ G G' G₀ G₀' τ τ₀ ρ r)
    (hE : ∀ v, E.next (Ac.out (τ (Fin.last _) v)) = E.next (Ac.out v))
    (S : Set (BaseGame.Tuple (Bits m) Bc Cc k × DB (Bits m) Bc))
    (hS : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k Ac.V) I J m
        (Ac.depth + k),
      (expOut e E k Ac.out y.1.1, slotsDB e y.2) ∈ S → ℓ y.1.1.1 = some r)
    (hSτ : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k Ac.V) I J m
        (Ac.depth + k),
      (expOut e E k Ac.out (expWorkPerm k (τ (Fin.last _)) y.1.1), slotsDB e y.2) ∈ S ↔
        (expOut e E k Ac.out y.1.1, slotsDB e y.2) ∈ S) :
    simLaw (t := X.depth + k) e (expandAdv e E k (X.toQueryAlgCoh.mapOut (·.getD X.defaultOut))) S =
      simLaw (t := Ac.depth + k) e (expandAdv e E k (Ac.toQueryAlgCoh.mapOut (·.getD
          Ac.defaultOut)))
        S := by
  subst heq
  exact simLaw_expandCoh_of_blockRel e E k hAc hX h _ hE S hS hSτ

/-- **`simLaw_expandCoh_of_blockNone` for an algorithm equal to `A` with other Kraus maps**, both
outputs read with their default outputs. -/
theorem simLaw_expandCoh_eq_of_blockNone {L : Type} [DecidableEq L]
    {Ac X : Alg (Bits m) (BitStr I J) Cc}
    {K' : Fin (Ac.depth + 1) → KrausMap Ac.R (QueryReg Ac.V 1 (Bits m) (BitStr I J))
      (QueryReg Ac.V 1 (Bits m) (BitStr I J))}
    (heq : X = { Ac with step := K' }) (hAc : Ac.TracePreserving) (hX : X.TracePreserving)
    {ℓ : Ac.V → Option L} {G G' : Fin (Ac.depth + 1) → Set Ac.V} {G₀ G₀' : Set Ac.V}
    (h : Ac.BlockNone K' ℓ G G' G₀ G₀') (r : L)
    (S : Set (BaseGame.Tuple (Bits m) Bc Cc k × DB (Bits m) Bc))
    (hS : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k Ac.V) I J m
        (Ac.depth + k),
      (expOut e E k Ac.out y.1.1, slotsDB e y.2) ∈ S ↔ ℓ y.1.1.1 = some r) :
    simLaw (t := X.depth + k) e (expandAdv e E k (X.toQueryAlgCoh.mapOut (·.getD X.defaultOut))) S =
      simLaw (t := Ac.depth + k) e (expandAdv e E k (Ac.toQueryAlgCoh.mapOut (·.getD
          Ac.defaultOut)))
        S := by
  subst heq
  exact simLaw_expandCoh_of_blockNone e E k hAc hX h _ r S hS

end WithStepLaw

end GordieHowe.QROM

namespace GordieHowe.Quantum

open GordieHowe.QROM KrausRel

namespace AdaptiveIAlg

/-! ### Requests fixed by an entrywise permutation of the logs -/

/-- **An element fixed by the permutations relating two lists entrywise** is in one list exactly
when it is in the other. -/
theorem mem_iff_of_forall₂_perm {Req ι : Type*} (e : ι → Equiv.Perm Req) {x : Req}
    (hx : ∀ i, e i x = x) :
    ∀ {l₁ l₂ : List Req}, List.Forall₂ (fun a b => ∃ i, a = e i b) l₁ l₂ → (x ∈ l₁ ↔ x ∈ l₂)
  | _, _, .nil => Iff.rfl
  | _, _, .cons ⟨i, hab⟩ h => by
    rw [List.mem_cons, List.mem_cons, mem_iff_of_forall₂_perm e hx h, hab]
    refine or_congr_left ?_
    conv_lhs => rw [← hx i]
    exact (e i).injective.eq_iff

/-- **A request fixed by every entry's permutation is among the first `n` requests of the
permuted logs exactly when it is among the first `n` requests.** -/
theorem mem_take_requests_logFam {Req : Type} {m : ℕ} (e : Fin m → Equiv.Perm Req)
    (lg : LogReg Req m) {x : Req} (hx : ∀ i, e i x = x) (n : ℕ) :
    x ∈ (requests (logFam e lg)).take n ↔ x ∈ (requests lg).take n :=
  mem_iff_of_forall₂_perm e hx (List.forall₂_take n (requestsBefore_logFam e lg m))

/-! ### The block hypotheses on smaller sets -/

section Mono

variable {X Y Req Resp O L : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)}
  {ℓ : A.W → Option L} {G G' H H' : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ G₀' H₀ H₀' : Set (A.W × Req × Option Resp)}

/-- **The set before a step of smaller sets is smaller.** -/
theorem prevSeq_subset {T : Type*} {G H : ℕ → Set T} {G₀ H₀ : Set T} (h : ∀ n, H n ⊆ G n)
    (h₀ : H₀ ⊆ G₀) (k : ℕ) : prevSeq H H₀ k ⊆ prevSeq G G₀ k := by
  unfold prevSeq
  split_ifs
  exacts [h₀, h _]

/-- **The block hypotheses on smaller sets** through which both families move, which the
permutations map onto each other on the block and on which the initial state is supported. -/
theorem BlockRel.mono {σ : ℕ → Equiv.Perm (A.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (A.W × Req × Option Resp)} {r : L}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r) (hH : ∀ n, H n ⊆ G n) (hH₀ : H₀ ⊆ G₀)
    (hset : ∀ n x, InBlock ℓ r x.1 → (σ n x ∈ H' n ↔ x ∈ H n))
    (hset₀ : ∀ x, InBlock ℓ r x.1 → (σ₀ x ∈ H₀' ↔ x ∈ H₀))
    (hH' : ∀ n, H' n ⊆ G' n) (hH₀' : H₀' ⊆ G₀')
    (hkeep : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq H H₀ k}
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ H k} ((A.step k).op i))
    (hkeep' : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq H' H₀' k}
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ H' k} ((st' k).op i))
    (hinit : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ H₀ ∧ b.1 ∈ H₀)
    (hinit' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ H₀' ∧ b.1 ∈ H₀') :
    A.BlockRel st' ℓ H H' H₀ H₀' σ σ₀ r where
  label_eq := h.label_eq
  label_eq₀ := h.label_eq₀
  kind_eq := h.kind_eq
  set_eq := hset
  set_eq₀ := hset₀
  keepsSet := hkeep
  keepsSet' := hkeep'
  keeps k i r' a b hb := h.keeps k i r' a b (prevSeq_subset hH hH₀ k hb)
  keeps' k i r' a b hb := h.keeps' k i r' a b (prevSeq_subset hH' hH₀' k hb)
  hop k i a b ha hb := h.hop k i a b ⟨ha.1, hH k ha.2⟩ ⟨hb.1, prevSeq_subset hH hH₀ k hb.2⟩
  init_supp := hinit
  init_supp' := hinit'
  init_eq a b ha hb := h.init_eq a b (hH₀ ha) (hH₀ hb)

/-- **The `none`-block hypotheses on smaller sets** through which both families move, with the
same states of label `none`, on which the initial state is supported. -/
theorem BlockNone.mono [DecidableEq L] (h : A.BlockNone st' ℓ G G' G₀ G₀') (hH : ∀ n, H n ⊆ G n)
    (hH₀ : H₀ ⊆ G₀) (hH' : ∀ n, H' n ⊆ G' n) (hH₀' : H₀' ⊆ G₀')
    (hnone : ∀ n x, ℓ x.1 = none → (x ∈ H' n ↔ x ∈ H n))
    (hnone₀ : ∀ x, ℓ x.1 = none → (x ∈ H₀' ↔ x ∈ H₀))
    (hkeep : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq H H₀ k}
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ H k} ((A.step k).op i))
    (hkeep' : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq H' H₀' k}
      {d : DReg A.W A.width X Y Req Resp | d.1 ∈ H' k} ((st' k).op i))
    (hinit : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ H₀ ∧ b.1 ∈ H₀)
    (hinit' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ H₀' ∧ b.1 ∈ H₀') :
    A.BlockNone st' ℓ H H' H₀ H₀' where
  none_eq := hnone
  none_eq₀ := hnone₀
  keepsSet := hkeep
  keepsSet' := hkeep'
  keeps k i r' a b hb := h.keeps k i r' a b (prevSeq_subset hH hH₀ k hb)
  keeps' k i r' a b hb := h.keeps' k i r' a b (prevSeq_subset hH' hH₀' k hb)
  row_none_eq k i a b ha hb := h.row_none_eq k i a b (hH k ha) (prevSeq_subset hH hH₀ k hb)
  gram_eq k r c d hc hd := h.gram_eq k r c d (prevSeq_subset hH hH₀ k hc)
    (prevSeq_subset hH hH₀ k hd)
  init_supp := hinit
  init_supp' := hinit'

end Mono

/-! ### The log of the current slot -/

section SlotLog

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **The log of the index's slot holds `A`'s request**: at the index `some n`, a request in the
log of slot `n` is `A`'s request register, and `A`'s kind is a request. -/
def slotLogSet (idx : Option ℕ) :
    Set (((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁) :=
  {x | ∀ (j : Fin A.slots) q, idx = some (j : ℕ) → x.1.1.logs j = some q →
    q = x.1.1.request ∧ A.kind x.1.1.work = true}

/-- **The well-formed states of the absorbed adversary with the log of the index's slot**
(`tabSet` and `slotLogSet`). -/
def logTabSet (G : ℕ → Set (A.W × Req × Option Resp)) (G₀ : Set (A.W × Req × Option Resp))
    (idx : Option ℕ) :
    Set (((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁) :=
  A.tabSet F G G₀ idx ∩ A.slotLogSet F idx

variable {A F}

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] in
theorem afterIdx_prevIdx_self (k : ℕ) : AfterIdx (prevIdx k) k := by
  unfold prevIdx
  split_ifs
  · trivial
  · change k - 1 < k
    omega

/-- **The absorbed step moves the well-formed states with the slot's log** before step `k` into
those after it. -/
theorem keepsSet_stepTab_logTabSet {st : StepIdx A.slots A.post → KrausMap A.R
      (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)}
    {G : ℕ → Set (A.W × Req × Option Resp)} {G₀ : Set (A.W × Req × Option Resp)}
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    {k : StepIdx A.slots A.post}
    (hA : ∀ i, KeepsSet {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
      {d | d.1 ∈ G k} ((st k).op i)) (i : (A.absorb F.base).R) :
    KeepsSet {d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ |
      d.1 ∈ prevSeq (fun n => A.logTabSet F G G₀ (some n)) (A.logTabSet F G G₀ none) k}
      {d | d.1 ∈ A.logTabSet F G G₀ (some k)} (((A.withStep st).stepTab F k).op i) := by
  intro a b hb hne
  rw [Set.mem_ofPred_eq, prevSeq_eq_idx (A.logTabSet F G G₀)] at hb
  refine ⟨keepsSet_stepTab hG hA i a b hb.1 hne, fun j q hj hq => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hlog⟩ := (A.withStep st).stepTab_rel F hne
  have hkj : (k : ℕ) = j := Option.some_inj.1 hj
  have hbl : b.1.1.1.logs j = none :=
    hb.1.2.1 j (by rw [← hkj]; exact afterIdx_prevIdx_self k)
  rw [hlog j, hbl] at hq
  split_ifs at hq with hk
  · rw [Equiv.swap_apply_left] at hq
    exact ⟨(Option.some_inj.1 hq).symm, hk.2⟩

end SlotLog

/-! ### The block hypotheses on the well-formed states with the slot's log -/

section SwapLog

variable {X Y Req Resp O O' Req₁ Resp₁ Req₂ Resp₂ L : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} {F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)}
  {σW : Equiv.Perm A.W} {sw : Equiv.Perm Req} {J : A.W → Option ℕ} {σ₁ : Equiv.Perm Req₁}
  {ℓ : A.W → Option L} {r : L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ G₀' : Set (A.W × Req × Option Resp)}

/-- **The witness swap keeps the slot's log**, for a swap of the workspace keeping the kind. -/
theorem tTrip_mem_slotLogSet (hk : ∀ x : A.W × Req × Option Resp, A.kind (σW x.1) = A.kind x.1)
    (idx : Option ℕ)
    (x : ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁) :
    A.tTrip F σW sw J σ₁ idx x ∈ A.slotLogSet F idx ↔ x ∈ A.slotLogSet F idx := by
  obtain ⟨⟨⟨w, q, a, lg, s⟩, t⟩, z, y⟩ := x
  refine forall_congr' fun j => ?_
  by_cases hj : idx = some (j : ℕ)
  · subst hj
    show (∀ q', some (j : ℕ) = some (j : ℕ) →
        (lg j).map (swIf (J w = some (j : ℕ)) sw) = some q' →
          q' = swIf (Hit J w (some (j : ℕ))) sw q ∧ A.kind (σW w) = true) ↔
      (∀ q', some (j : ℕ) = some (j : ℕ) → lg j = some q' → q' = q ∧ A.kind w = true)
    rw [swIf_congr sw (hit_some J w j), hk (w, q, a)]
    rcases lg j with _ | q₀
    · simp
    · simp
  · exact ⟨fun _ q' h => absurd h hj, fun _ q' h => absurd h hj⟩

/-- **The block hypotheses through the absorption with a table, on the well-formed states with
the slot's log** (`BlockRel.absorbTab` on `logTabSet`). -/
theorem BlockRel.absorbTabLog [DecidableEq L]
    (h : A.BlockRel st' ℓ G G' G₀ G₀' (fun n => A.jTrip σW sw J (some n))
      (A.jTrip σW sw J none) r)
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hG' : ∀ idx w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx)
    (hF : F.SwapInv sw σ₁) (hJ : A.JSlotStep G G₀ J) (tab : A.OuterTab Req₂ Resp₂) :
    (A.absorbTab F tab).BlockRel (A.absorbTabStep F st') (fun w => ℓ w.1.work)
      (fun n => A.logTabSet F G G₀ (some n)) (fun n => A.logTabSet F G' G₀' (some n))
      (A.logTabSet F G G₀ none) (A.logTabSet F G' G₀' none)
      (fun n => A.tTrip F σW sw J σ₁ (some n)) (A.tTrip F σW sw J σ₁ none) r := by
  have hk : ∀ x : A.W × Req × Option Resp, A.kind (σW x.1) = A.kind x.1 := h.kind_eq 0
  refine (BlockRel.absorbTab st' h hG hG' hF hJ tab).mono (fun _ => Set.inter_subset_left)
    Set.inter_subset_left (fun n x hx => and_congr (tTrip_mem_tabSet hF (some n) (h.set_eq n) x hx)
      (tTrip_mem_slotLogSet hk (some n) x))
    (fun x hx => and_congr (tTrip_mem_tabSet hF none h.set_eq₀ x hx)
      (tTrip_mem_slotLogSet hk none x))
    (fun _ => Set.inter_subset_left) Set.inter_subset_left
    (fun k i => keepsSet_stepTab_logTabSet (st := A.step) hG (h.keepsSet k) i)
    (fun k i => keepsSet_stepTab_logTabSet (st := st') hG' (h.keepsSet' k) i)
    (fun a b hab => ?_) (fun a b hab => ?_)
  · obtain ⟨ha, hb⟩ := init_supp_absorbTab G h.init_supp tab a b hab
    exact ⟨⟨ha, fun _ _ e => absurd e (by simp)⟩, ⟨hb, fun _ _ e => absurd e (by simp)⟩⟩
  · obtain ⟨ha, hb⟩ := init_supp_absorbTab G' h.init_supp' tab a b hab
    exact ⟨⟨ha, fun _ _ e => absurd e (by simp)⟩, ⟨hb, fun _ _ e => absurd e (by simp)⟩⟩

/-- **The `none`-block hypotheses through the absorption with a table, on the well-formed states
with the slot's log.** -/
theorem BlockNone.absorbTabLog [DecidableEq L] (h : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hG' : ∀ idx w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx)
    (tab : A.OuterTab Req₂ Resp₂) :
    (A.absorbTab F tab).BlockNone (A.absorbTabStep F st') (fun w => ℓ w.1.work)
      (fun n => A.logTabSet F G G₀ (some n)) (fun n => A.logTabSet F G' G₀' (some n))
      (A.logTabSet F G G₀ none) (A.logTabSet F G' G₀' none) := by
  have hN := BlockNone.absorbTab (F := F) st' h hG hG' tab
  refine hN.mono (fun _ => Set.inter_subset_left) Set.inter_subset_left
    (fun _ => Set.inter_subset_left) Set.inter_subset_left
    (fun n x hx => and_congr (hN.none_eq n x hx) Iff.rfl)
    (fun x hx => and_congr (hN.none_eq₀ x hx) Iff.rfl)
    (fun k i => keepsSet_stepTab_logTabSet (st := A.step) hG (h.keepsSet k) i)
    (fun k i => keepsSet_stepTab_logTabSet (st := st') hG' (h.keepsSet' k) i)
    (fun a b hab => ?_) (fun a b hab => ?_)
  · obtain ⟨ha, hb⟩ := init_supp_absorbTab G h.init_supp tab a b hab
    exact ⟨⟨ha, fun _ _ e => absurd e (by simp)⟩, ⟨hb, fun _ _ e => absurd e (by simp)⟩⟩
  · obtain ⟨ha, hb⟩ := init_supp_absorbTab G' h.init_supp' tab a b hab
    exact ⟨⟨ha, fun _ _ e => absurd e (by simp)⟩, ⟨hb, fun _ _ e => absurd e (by simp)⟩⟩

end SwapLog

/-! ### The `none`-block hypotheses as block hypotheses at the identity -/

section NoneRel

variable {X Y Req Resp O L : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [DecidableEq L]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)}
  {ℓ : A.W → Option L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ G₀' : Set (A.W × Req × Option Resp)}

/-- **The witness swap with the identities is the identity.** -/
theorem jTrip_refl_apply (J : A.W → Option ℕ) (idx : Option ℕ) (x : A.W × Req × Option Resp) :
    A.jTrip (Equiv.refl _) (Equiv.refl _) J idx x = x := by
  obtain ⟨w, q, a⟩ := x
  show (w, swIf (Hit J w idx) (Equiv.refl Req) q, a) = (w, q, a)
  unfold swIf
  split_ifs <;> rfl

theorem tripPerm_prevSeq_jTrip_refl (J : A.W → Option ℕ) (k : ℕ)
    (d : DReg A.W A.width X Y Req Resp) :
    tripPerm (prevSeq (fun n => A.jTrip (Equiv.refl _) (Equiv.refl _) J (some n))
      (A.jTrip (Equiv.refl _) (Equiv.refl _) J none) k) d = d := by
  obtain ⟨x, p⟩ := d
  unfold prevSeq
  split_ifs <;> exact congrArg (·, p) (jTrip_refl_apply J _ x)

/-- **The overlaps into a block of a label read through `some`** are those of the label. -/
theorem rowGram_map_some {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] (ℓι : ι → Option L)
    (r : L) (K : KrausMap R ι ι) (c d : ι) :
    rowGram (fun p => (ℓι p).map some) (some r) K c d = rowGram ℓι r K c d := by
  unfold rowGram
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr ?_ fun _ _ => rfl
  exact Finset.filter_congr fun a _ => by simp

/-- **No row of a label read through `some` has the label `some none`.** -/
theorem rowGram_map_some_none {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] (ℓι : ι →
    Option L) (K : KrausMap R ι ι) (c d : ι) :
    rowGram (fun p => (ℓι p).map some) none K c d = 0 := by
  unfold rowGram
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a ha => ?_
  simp at ha

/-- **The `none`-block hypotheses with the label read through `some`.** -/
theorem BlockNone.mapSome (h : A.BlockNone st' ℓ G G' G₀ G₀') :
    A.BlockNone st' (fun w => (ℓ w).map some) G G' G₀ G₀' where
  none_eq n x hx := h.none_eq n x (Option.map_eq_none_iff.1 hx)
  none_eq₀ x hx := h.none_eq₀ x (Option.map_eq_none_iff.1 hx)
  keepsSet := h.keepsSet
  keepsSet' := h.keepsSet'
  keeps k i r' a b hb hl hne := by
    obtain ⟨r'', hr, rfl⟩ := Option.map_eq_some_iff.1 hl
    exact congrArg (Option.map some) (h.keeps k i r'' a b hb hr hne)
  keeps' k i r' a b hb hl hne := by
    obtain ⟨r'', hr, rfl⟩ := Option.map_eq_some_iff.1 hl
    exact congrArg (Option.map some) (h.keeps' k i r'' a b hb hr hne)
  row_none_eq k i a b ha hb hal hbl :=
    h.row_none_eq k i a b ha hb (Option.map_eq_none_iff.1 hal) (Option.map_eq_none_iff.1 hbl)
  gram_eq k r' c d hc hd hcl hdl := by
    rcases r' with _ | r''
    · rw [rowGram_map_some_none, rowGram_map_some_none]
    · rw [rowGram_map_some, rowGram_map_some]
      exact h.gram_eq k r'' c d hc hd (Option.map_eq_none_iff.1 hcl) (Option.map_eq_none_iff.1 hdl)
  init_supp := h.init_supp
  init_supp' := h.init_supp'

/-- **The `none`-block hypotheses are block hypotheses at the identity swap**, on the block `none`
of the label read through `some` (whose states are those of label `none`). -/
theorem BlockNone.toBlockRel (h : A.BlockNone st' ℓ G G' G₀ G₀') (J : A.W → Option ℕ) :
    A.BlockRel st' (fun w => (ℓ w).map some) G G' G₀ G₀'
      (fun n => A.jTrip (Equiv.refl _) (Equiv.refl _) J (some n))
      (A.jTrip (Equiv.refl _) (Equiv.refl _) J none) none := by
  have hnone : ∀ x : A.W, InBlock (fun w => (ℓ w).map some) none x → ℓ x = none := fun x hx => by
    rcases hx with hx | hx
    · exact Option.map_eq_none_iff.1 hx
    · obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.1 hx
      exact absurd he (by simp)
  have hm := h.mapSome
  exact
    { label_eq := fun n x => by rw [jTrip_refl_apply]
      label_eq₀ := fun x => by rw [jTrip_refl_apply]
      kind_eq := fun n x => by rw [jTrip_refl_apply]
      set_eq := fun n x hx => by
        rw [jTrip_refl_apply]
        exact h.none_eq n x (hnone _ hx)
      set_eq₀ := fun x hx => by
        rw [jTrip_refl_apply]
        exact h.none_eq₀ x (hnone _ hx)
      keepsSet := h.keepsSet
      keepsSet' := h.keepsSet'
      keeps := hm.keeps
      keeps' := hm.keeps'
      hop := fun k i a b ha hb => by
        have ha' : tripPerm (A.jTrip (Equiv.refl _) (Equiv.refl _) J (some k)) a = a :=
          tripPerm_prevSeq_jTrip_refl J (k + 1) a
        rw [ha', tripPerm_prevSeq_jTrip_refl]
        exact h.row_none_eq k i a b ha.2 hb.2 (hnone _ ha.1) (hnone _ hb.1)
      init_supp := h.init_supp
      init_supp' := h.init_supp'
      init_eq := fun a b _ _ _ _ => by
        have e : ∀ d : DReg A.W A.width X Y Req Resp,
            tripPerm (A.jTrip (Equiv.refl _) (Equiv.refl _) J none) d = d :=
          tripPerm_prevSeq_jTrip_refl J 0
        rw [e a, e b] }

end NoneRel

/-! ### The hypotheses of the composition for the trace-preserving form -/

section TPSwap

variable {X Y Req Resp O O' Req₁ Resp₁ Req₂ Resp₂ L : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [DecidableEq L]
  [Nonempty X] [AddGroup Y]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} {F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)}
  {σW : Equiv.Perm A.W} {sw : Equiv.Perm Req} {J : A.W → Option ℕ} {σ₁ : Equiv.Perm Req₁}
  {ℓ : A.W → Option L} {r : L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ G₀' : Set (A.W × Req × Option Resp)}

variable (A) in
/-- **The requests away from the recorded slot are fixed by the swap**: at a state of `G j` in
the block with a request, the request is fixed by `sw` when the recorded slot is not `j`. -/
def SwapFixAway (sw : Equiv.Perm Req) (J : A.W → Option ℕ) (ℓ : A.W → Option L) (r : L)
    (G : ℕ → Set (A.W × Req × Option Resp)) : Prop :=
  ∀ (j : Fin A.slots), ∀ x ∈ G j, InBlock ℓ r x.1 → A.kind x.1 = true → J x.1 ≠ some (j : ℕ) →
    sw x.2.1 = x.2.1

/-- **The hypotheses of the composition along the witness swap for the trace-preserving form of
the absorbed adversary** (`KindAlg.SwapHyps`), with output `g`: from the block hypotheses of `A`
and `st'` along `jTrip`, for trace-preserving `A` and `A.withStep st'`, a relay that does not see
`sw`, sets closed under changes of the response, a recorded slot changing only at its step and
requests away from it fixed by `sw`; along the well-formed states with the slot's log and the
witness swap `tTrip`, read past the counter. -/
theorem swapHyps_absorbTab
    (h : A.BlockRel st' ℓ G G' G₀ G₀' (fun n => A.jTrip σW sw J (some n))
      (A.jTrip σW sw J none) r)
    (hN : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hG' : ∀ idx w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx)
    (hF : F.SwapInv sw σ₁) (hJ : A.JSlotStep G G₀ J) (hfix : A.SwapFixAway sw J ℓ r G)
    (hA : A.TracePreserving) (hA' : (A.withStep st').TracePreserving)
    (tab : A.OuterTab Req₂ Resp₂) (g : O → O') :
    ((A.absorbTab F tab).mapOut g).toTPKindAlg.SwapHyps σ₁
      (((A.absorbTab F tab).mapOut g).abortStep (A.absorbTabStep F st'))
      (fun w => ℓ w.1.1.work) r (fun w => J w.1.1.work)
      (fun n => ((A.absorbTab F tab).mapOut g).cntOne (A.tTrip F σW sw J σ₁ (some n)))
      (((A.absorbTab F tab).mapOut g).cntOne (A.tTrip F σW sw J σ₁ none))
      (fun n => ((A.absorbTab F tab).mapOut g).cntSet (A.logTabSet F G G₀ (some n)))
      (fun n => ((A.absorbTab F tab).mapOut g).cntSet (A.logTabSet F G' G₀' (some n)))
      (((A.absorbTab F tab).mapOut g).cntSet (A.logTabSet F G G₀ none))
      (((A.absorbTab F tab).mapOut g).cntSet (A.logTabSet F G' G₀' none)) := by
  have hA₂ : ((A.absorbTab F tab).mapOut g).TracePreserving :=
    mapOut_tracePreserving (A.absorbTab_tracePreserving F hA tab) g
  have hA₂' : (((A.absorbTab F tab).mapOut g).withStep (A.absorbTabStep F st')).TracePreserving :=
    mapOut_tracePreserving ((A.withStep st').absorbTab_tracePreserving F hA' tab) g
  have hR := ((BlockRel.absorbTabLog h hG hG' hF hJ tab).mapOut g).toTP hA₂ hA₂'
  have hNR := ((BlockNone.absorbTabLog (F := F) hN hG hG' tab).mapOut g).toTP hA₂ hA₂'
  refine
    { pairNone := fun k => (pairs_of_block_perm hR hNR k).1
      pairOn := fun k => (pairs_of_block_perm hR hNR k).2
      slot := fun k i a b hb hne => ?_
      kind := hR.kind_eq
      req := fun n x => ?_
      resp := fun n w q a a' => rfl
      fix := fun j x hx hl _ hJx => ?_
      closed := fun idx w q a a' hm => by cases idx <;> exact hm
      closed' := fun idx w q a a' hm => by cases idx <;> exact hm
      none_eq := fun idx x hx => by
        cases idx
        · exact hNR.none_eq₀ x hx
        · exact hNR.none_eq _ x hx
      set_eq := fun idx x hx => by
        cases idx
        · exact hR.set_eq₀ x hx
        · exact hR.set_eq _ x hx
      label_eq := fun idx x => by
        cases idx
        · exact hR.label_eq₀ x
        · exact hR.label_eq _ x }
  · rw [AdaptiveIAlg.toTPKindAlg_step_op] at hne
    obtain ⟨r₀, hr₀⟩ := ((A.absorbTab F tab).mapOut g).tpOp_ne_zero hA₂ hne
    obtain ⟨r', a', b', h1, ha1, -, hb1, hb2, -⟩ := A.stepTab_rel F hr₀
    have hb' : b.1 ∈ ((A.absorbTab F tab).mapOut g).cntSet
        (A.logTabSet F G G₀ (prevIdx k)) := by
      have := hb
      erw [prevSeq_cntSet, prevSeq_eq_idx (A.logTabSet F G G₀)] at this
      exact this
    have hb1' : b'.1.1 = b.1.1.1.1.work := hb1
    have hb2' : b'.1.2.1 = b.1.1.1.1.request := hb2
    have ha1' : a'.1.1 = a.1.1.1.1.work := ha1
    have hmem : b'.1 ∈ prevSeq G G₀ k := by
      rw [prevSeq_eq_idxSet]
      have h0 := hG (prevIdx k) _ _ _ b'.1.2.2 hb'.1.1
      rw [← hb1', ← hb2'] at h0
      exact h0
    rcases hJ k r' a' b' hmem h1 with e | ⟨e1, e2⟩
    · left
      change J a'.1.1 = J b'.1.1 at e
      rw [ha1', hb1'] at e
      exact e
    · right
      change J b'.1.1 = none at e1
      change J a'.1.1 = some k at e2
      rw [hb1'] at e1
      rw [ha1'] at e2
      exact ⟨e1, e2⟩
  · change swIf (Hit J x.1.1.1.work (some n)) σ₁ x.2.1 = _
    rw [swIf_congr σ₁ (hit_some J _ n)]
  · obtain ⟨⟨hG1, -, hslot⟩, hlog⟩ := hx
    have hs : SlotCond A F (some (j : ℕ)) x.1.1.1.logs x.2.1 := hslot
    simp only [SlotCond] at hs
    rw [dif_pos (show (j : ℕ) < A.slots from j.isLt)] at hs
    rcases hs with ⟨-, hz⟩ | ⟨q, hq, hz⟩
    · rw [hz]
      exact hF.default
    · obtain ⟨rfl, hk⟩ := hlog j q rfl hq
      rw [hz, ← hF.route, hfix j _ hG1 hl hk hJx]

end TPSwap

/-! ### The expanded run of the composition along the witness swap -/

section SwapLaw

variable {I K Req₁ Resp₁ O' Lb : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
  {m : ℕ} [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [DecidableEq Lb]
  {shA₂ : AlgShape (Bits m) (BitStr I K) Req₁ Resp₁} {A₂ : AdaptiveIAlg shA₂ O'}
  {st₂ : StepIdx A₂.slots A₂.post → KrausMap A₂.R
    (DReg A₂.W A₂.width (Bits m) (BitStr I K) Req₁ Resp₁)
    (DReg A₂.W A₂.width (Bits m) (BitStr I K) Req₁ Resp₁)}
  {C : Challenger (Bits m) (BitStr I K) Req₁ Resp₁} {σ₁ : Equiv.Perm Req₁}
  {ℓB : A₂.toTPKindAlg.W → Option Lb} {r : Lb} {Jc : A₂.toTPKindAlg.W → Option ℕ}
  {σ : ℕ → Equiv.Perm (A₂.toTPKindAlg.W × Req₁ × Option Resp₁)}
  {σ₀ : Equiv.Perm (A₂.toTPKindAlg.W × Req₁ × Option Resp₁)}
  {G G' : ℕ → Set (A₂.toTPKindAlg.W × Req₁ × Option Resp₁)}
  {G₀ G₀' : Set (A₂.toTPKindAlg.W × Req₁ × Option Resp₁)}
  {Bc : Type} (e : BitStr I K ≃ Bc) (E : Expansion (Bits m) Bc (A₂.toTPKindAlg.CW C)) (kq : ℕ)

/-- **The composition with the Kraus maps `abortStep st₂` on the block along the swap**: from
`KindAlg.SwapHyps` of the trace-preserving form, the composition of `A₂.withStep st₂` is that of
`A₂` with other Kraus maps `K'`, the two satisfying `Alg.BlockNone` and `Alg.BlockRel`, the last
permutation `cwPerm` at `σ` after the last step. -/
theorem exists_block_composeBothOut_withStep (hC : C.SwapInv σ₁)
    (h : A₂.toTPKindAlg.SwapHyps σ₁ (A₂.abortStep st₂) ℓB r Jc σ σ₀ G G' G₀ G₀')
    (hinit : ∀ a b, A₂.toTPKindAlg.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hinit' : ∀ a b, A₂.toTPKindAlg.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (hinit_eq : ∀ a b : DReg A₂.toTPKindAlg.W A₂.toTPKindAlg.width (Bits m) (BitStr I K) Req₁ Resp₁,
      a.1 ∈ G₀ → b.1 ∈ G₀ → InBlock ℓB r a.workspace → InBlock ℓB r b.workspace →
      A₂.toTPKindAlg.init.mat (AdaptiveIAlg.tripPerm σ₀ a) (AdaptiveIAlg.tripPerm σ₀ b) =
        A₂.toTPKindAlg.init.mat a b) :
    ∃ (K' : Fin ((A₂.toTPKindAlg.composeBothOut C id).depth + 1) →
        KrausMap (A₂.toTPKindAlg.composeBothOut C id).R
        (QueryReg (A₂.toTPKindAlg.composeBothOut C id).V 1 (Bits m) (BitStr I K))
        (QueryReg (A₂.toTPKindAlg.composeBothOut C id).V 1 (Bits m) (BitStr I K)))
      (ρ : Equiv.Perm (A₂.toTPKindAlg.composeBothOut C id).R) (T T' : ℕ → Set (A₂.toTPKindAlg.CW C))
      (P : ℕ → Equiv.Perm (A₂.toTPKindAlg.CW C)),
      (A₂.withStep st₂).toTPKindAlg.composeBothOut C id =
        { A₂.toTPKindAlg.composeBothOut C id with step := K' } ∧
      P ((A₂.toTPKindAlg.composeBothOut C id).depth + 1) =
        KindAlg.cwPerm _ C σ₁ Jc (σ (A₂.slots + A₂.post)) ∧
      (A₂.toTPKindAlg.composeBothOut C id).BlockNone K' (fun v => ℓB v.1.adv.1.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T' (i + 1)}) {v | v.1 ∈ T 0}
        {v | v.1 ∈ T' 0} ∧
      (A₂.toTPKindAlg.composeBothOut C id).BlockRel K' (fun v => ℓB v.1.adv.1.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T' (i + 1)}) {v | v.1 ∈ T 0}
        {v | v.1 ∈ T' 0} (fun i => WorkRel.wa (P (i + 1))) (WorkRel.wa (P 0)) (fun _ => ρ) r := by
  obtain ⟨K', ρ, T, T', P, hT0, hT0', hP0, hTe, heq, hn, hr⟩ :=
    KindAlg.composeBothOut_block_cw hC h hinit hinit' hinit_eq id
  have hd : (A₂.toTPKindAlg.fullCircBoth C).queries <
      (A₂.toTPKindAlg.composeBothOut C id).depth + 1 := by
    rw [Circuit.toAlg_depth, ReprogrammedCircuit.queries_toCircuit]
    omega
  refine ⟨K', ρ, T, T', P, heq, (hTe _ hd).2.2, ?_, ?_⟩
  · rw [hT0, hT0']
    exact hn
  · rw [hT0, hT0', hP0]
    exact hr

/-- **The expanded runs of the compositions of `A₂.withStep st₂` and `A₂` on one block along the
swap**: from `KindAlg.SwapHyps`, for an expansion whose queries do not see the last permutation
(`hE`), every event whose outcomes have label `some r` (`hS`) and that the last permutation keeps
(`hSτ`) has the same probability; the expansion `E₁` of the first run reads as `E`. -/
theorem simLaw_expand_withStep_eq_of_swapHyps (hC : C.SwapInv σ₁)
    (h : A₂.toTPKindAlg.SwapHyps σ₁ (A₂.abortStep st₂) ℓB r Jc σ σ₀ G G' G₀ G₀')
    (hinit : ∀ a b, A₂.toTPKindAlg.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hinit' : ∀ a b, A₂.toTPKindAlg.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (hinit_eq : ∀ a b : DReg A₂.toTPKindAlg.W A₂.toTPKindAlg.width (Bits m) (BitStr I K) Req₁ Resp₁,
      a.1 ∈ G₀ → b.1 ∈ G₀ → InBlock ℓB r a.workspace → InBlock ℓB r b.workspace →
      A₂.toTPKindAlg.init.mat (AdaptiveIAlg.tripPerm σ₀ a) (AdaptiveIAlg.tripPerm σ₀ b) =
        A₂.toTPKindAlg.init.mat a b)
    (E₁ : Expansion (Bits m) Bc ((A₂.withStep st₂).toTPKindAlg.CW C))
    (hE₁ : ∀ c, E₁.next c = E.next c)
    (hE : ∀ c, E.next (KindAlg.cwPerm _ C σ₁ Jc (σ (A₂.slots + A₂.post)) c) = E.next c)
    (S : Set (BaseGame.Tuple (Bits m) Bc (A₂.toTPKindAlg.CW C) kq × DB (Bits m) Bc))
    (hS : ∀ ω ∈ S, ℓB ω.1.out.adv.1.1 = some r)
    (hSτ : ∀ ω, ((⟨ω.1.queries, ω.1.answers, KindAlg.cwPerm _ C σ₁ Jc (σ (A₂.slots + A₂.post))
      ω.1.out⟩ : BaseGame.Tuple (Bits m) Bc _ kq), ω.2) ∈ S ↔ ω ∈ S) :
    simLaw e (expandAdv e E₁ kq (((A₂.withStep st₂).toTPKindAlg.composeBothOut C
        id).toQueryAlgCoh.mapOut
      (·.getD ((A₂.withStep st₂).toTPKindAlg.composeBothOut C id).defaultOut))) S =
      simLaw e (expandAdv e E kq ((A₂.toTPKindAlg.composeBothOut C id).toQueryAlgCoh.mapOut
        (·.getD (A₂.toTPKindAlg.composeBothOut C id).defaultOut))) S := by
  obtain ⟨K', ρ, T, T', P, heq, hP, hn, hr⟩ :=
    exists_block_composeBothOut_withStep hC h hinit hinit' hinit_eq
  obtain rfl : E = E₁ := by
    cases E₁
    cases E
    exact congrArg Expansion.mk (funext hE₁).symm
  have hAc' := KindAlg.StepsTP.tracePreserving_composeBothOut
    (B := (A₂.withStep st₂).toTPKindAlg) (A₂.withStep st₂).toTPKindAlg_step_tp C id
  have hAc := KindAlg.StepsTP.tracePreserving_composeBothOut
    (B := A₂.toTPKindAlg) A₂.toTPKindAlg_step_tp C id
  have hout : ∀ v, (A₂.toTPKindAlg.composeBothOut C id).out v = v.1 := fun _ => rfl
  refine simLaw_expandCoh_eq_of_blockRel e E kq heq hAc hAc' hr ?_ S (fun y hy => hS _ hy) ?_
  · intro v
    rw [hout, hout]
    simp only [Fin.val_last, hP]
    exact hE v.1
  · intro y
    rw [← hSτ (expOut e E kq (A₂.toTPKindAlg.composeBothOut C id).out y.1.1, slotsDB e y.2)]
    refine Iff.of_eq (congrArg (· ∈ S) (Prod.ext ?_ rfl))
    simp only [Fin.val_last, hP]
    simp only [expOut, expWorkPerm, Equiv.prodCongr_apply, Prod.map]
    congr 1
    funext j
    simp only [ExpandAdv.queryAt, id, Equiv.refl_apply]
    rw [hE]

/-- **The expanded runs give the block of label `some r` the same mass**, under the hypotheses
of `simLaw_expand_withStep_eq_of_swapHyps` without the last permutation. -/
theorem simLaw_expand_withStep_mass_of_swapHyps (hC : C.SwapInv σ₁)
    (h : A₂.toTPKindAlg.SwapHyps σ₁ (A₂.abortStep st₂) ℓB r Jc σ σ₀ G G' G₀ G₀')
    (hinit : ∀ a b, A₂.toTPKindAlg.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hinit' : ∀ a b, A₂.toTPKindAlg.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (hinit_eq : ∀ a b : DReg A₂.toTPKindAlg.W A₂.toTPKindAlg.width (Bits m) (BitStr I K) Req₁ Resp₁,
      a.1 ∈ G₀ → b.1 ∈ G₀ → InBlock ℓB r a.workspace → InBlock ℓB r b.workspace →
      A₂.toTPKindAlg.init.mat (AdaptiveIAlg.tripPerm σ₀ a) (AdaptiveIAlg.tripPerm σ₀ b) =
        A₂.toTPKindAlg.init.mat a b)
    (E₁ : Expansion (Bits m) Bc ((A₂.withStep st₂).toTPKindAlg.CW C))
    (hE₁ : ∀ c, E₁.next c = E.next c)
    (r₁ : Lb)
    (S : Set (BaseGame.Tuple (Bits m) Bc (A₂.toTPKindAlg.CW C) kq × DB (Bits m) Bc))
    (hS : ∀ ω, ω ∈ S ↔ ℓB ω.1.out.adv.1.1 = some r₁) :
    simLaw e (expandAdv e E₁ kq (((A₂.withStep st₂).toTPKindAlg.composeBothOut C
        id).toQueryAlgCoh.mapOut
      (·.getD ((A₂.withStep st₂).toTPKindAlg.composeBothOut C id).defaultOut))) S =
      simLaw e (expandAdv e E kq ((A₂.toTPKindAlg.composeBothOut C id).toQueryAlgCoh.mapOut
        (·.getD (A₂.toTPKindAlg.composeBothOut C id).defaultOut))) S := by
  obtain ⟨K', ρ, T, T', P, heq, -, hn, -⟩ :=
    exists_block_composeBothOut_withStep hC h hinit hinit' hinit_eq
  obtain rfl : E = E₁ := by
    cases E₁
    cases E
    exact congrArg Expansion.mk (funext hE₁).symm
  have hAc' := KindAlg.StepsTP.tracePreserving_composeBothOut
    (B := (A₂.withStep st₂).toTPKindAlg) (A₂.withStep st₂).toTPKindAlg_step_tp C id
  have hAc := KindAlg.StepsTP.tracePreserving_composeBothOut
    (B := A₂.toTPKindAlg) A₂.toTPKindAlg_step_tp C id
  exact simLaw_expandCoh_eq_of_blockNone e E kq heq hAc hAc' hn r₁ S fun y => hS _

end SwapLaw

/-! ### The expanded run of the composition -/

section Expand

variable {I K Req Resp O O' Req₁ Resp₁ Req₂ Resp₂ L : Type} [Fintype I] [Fintype K]
  [DecidableEq I] [DecidableEq K] {m : ℕ}
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [DecidableEq L]
  {shA : AlgShape (Bits m) (BitStr I K) Req Resp} {A : AdaptiveIAlg shA O}
  {F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I K) Req Resp)
    (DReg A.W A.width (Bits m) (BitStr I K) Req Resp)}
  {σW : Equiv.Perm A.W} {sw : Equiv.Perm Req} {J : A.W → Option ℕ} {σ₁ : Equiv.Perm Req₁}
  {ℓ : A.W → Option L} {r : L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ G₀' : Set (A.W × Req × Option Resp)} {tab : A.OuterTab Req₂ Resp₂} {g : O → O'}
  {C : Challenger (Bits m) (BitStr I K) Req₁ Resp₁}

/-- **The adversary with the Kraus maps `st'`, absorbed with a table, with another output**, is
the absorbed adversary with another output and the Kraus maps `absorbTabStep`. -/
theorem absorbTab_mapOut_withStep :
    ((A.withStep st').absorbTab F tab).mapOut g =
      ((A.absorbTab F tab).mapOut g).withStep (A.absorbTabStep F st') :=
  rfl

/-- **The trace-preserving form of an adversary with the Kraus maps `st`** is that of the
adversary with the Kraus maps `abortStep st`. -/
theorem toTPKindAlg_withStep {shB : AlgShape (Bits m) (BitStr I K) Req₁ Resp₁} (B : AdaptiveIAlg shB O')
    (st : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width (Bits m) (BitStr I K) Req₁ Resp₁)
      (DReg B.W B.width (Bits m) (BitStr I K) Req₁ Resp₁)) :
    (B.withStep st).toTPKindAlg =
      ({ B.toTPKindAlg with step := B.abortStep st } : KindAlg _ O')
          :=
  rfl

variable (F σW sw J σ₁ tab g C) in
/-- **The final witness swap of the composed registers** of the trace-preserving form of the
absorbed adversary with the challenger `C`: `tTrip` after the last step, read past the counter,
with the log of the recorded slot swapped by `σ₁`. -/
noncomputable def finalSwap :
    Equiv.Perm (((A.absorbTab F tab).mapOut g).toTPKindAlg.CW C) :=
  KindAlg.cwPerm _ C σ₁ (fun w => J w.1.1.work)
    (((A.absorbTab F tab).mapOut g).cntOne (A.tTrip F σW sw J σ₁ (some (A.slots + A.post))))

end Expand

end AdaptiveIAlg

end GordieHowe.Quantum

namespace GordieHowe

open Quantum Signature QROM

namespace RingSignature.KeyFree

section ExtractBlock

open GordieHowe.SPBCS IOP SPTerm

variable {k kN kS L e N n : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.PK] [DecidableEq T.PK]
  [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  {B : BaseSigner Xb Yb N T RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {Stmt Wit R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R]
  {rel : Stmt → Wit → Prop} [DecidableRel rel]
  {enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit} {dummyS : Stmt}
  [Inhabited M.NIProof] {SC' : Type} [Fintype SC'] [DecidableEq SC']

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n



/-- **The final witness swap of the extraction run's registers** of `seAlgKF`: `finalSwap` at the
relay `seTwoKF`, the table `keyReplyNone keys`, the output `claimOfOutX prf` and the simulation
challenger, with the swap `σR` of the proof queries on the requests. -/
noncomputable def kfFinalSwap (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (σW : Equiv.Perm A.W) (σR : Equiv.Perm R)
    (J : A.W → Option ℕ) :
    Equiv.Perm (SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
        keys Q A)
      Psim Q) :=
  AdaptiveIAlg.finalSwap (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) σW
    (Equiv.sumCongr (Equiv.refl _) σR) J
    ((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR)) (fun _ => keyReplyNone B keys)
    (claimOfOutX prf) (simExtChallenger Psim Q)



/-- **The final witness swap keeps the claim** when `σW` keeps the claim of `A`'s output. -/
theorem advOut_kfFinalSwap {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R} {J : A.W → Option ℕ}
    (hout : ∀ w, claimOfOutX prf (A.out (σW w)) = claimOfOutX prf (A.out w))
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q) :
    SPBCS.advOut (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A).toTPKindAlg
        Psim Q (kfFinalSwap prf keys Q A Psim σW σR J c) =
      SPBCS.advOut (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
          A).toTPKindAlg
        Psim Q c :=
  hout c.adv.1.1.1.1.work

/-- **The final witness swap keeps the simulator's query inputs.** -/
theorem simQueryInputs_kfFinalSwap {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q :
    ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R}
    {J : A.W → Option ℕ}
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q) :
    SPBCS.simQueryInputs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
        keys Q
        A).toTPKindAlg Psim Q (kfFinalSwap prf keys Q A Psim σW σR J c) =
      SPBCS.simQueryInputs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
          keys Q
        A).toTPKindAlg Psim Q c := by
  unfold SPBCS.simQueryInputs
  refine congrArg (List.flatMap · _) (funext fun j => ?_)
  change (if ((logFam _ c.chal.logs) j).isSome ∧ (requestsBefore (logFam _ c.chal.logs) j).length <
      Q
    then _ else _) = _
  rw [length_requestsBefore_logFam, logFam_apply]
  rcases c.chal.logs j <;> rfl

/-- **The final witness swap keeps the final assignments**, for a simulator that does not see the
swap of the tagged statements. -/
theorem finalAss_kfFinalSwap {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R} {J : A.W → Option ℕ}
    (hPsim : ∀ x c, Psim.prog (((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR)) x)
      c = Psim.prog x c)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q) :
    SPBCS.finalAss (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A).toTPKindAlg Psim Q (kfFinalSwap prf keys Q A Psim σW σR J c) =
      SPBCS.finalAss (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A).toTPKindAlg Psim Q c :=
  KindAlg.postAss_chalSw (simExtChallenger_swapInv Psim Q hPsim) (KindAlg.swFam_slotSw _) c.chal

/-- **The extraction queries do not see the final witness swap** (`extractionProg`): the claim,
the final assignments and the simulator's query inputs are kept. -/
theorem simExtractionExpansion_next_kfFinalSwap {prf : Frg → Option M.NIProof} {keys : Fin n →
    B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R}
    {J : A.W → Option ℕ}
    (hout : ∀ w, claimOfOutX prf (A.out (σW w)) = claimOfOutX prf (A.out w))
    (hPsim : ∀ x c, Psim.prog (((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR)) x)
      c = Psim.prog x c)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
      A) Psim Q) :
    (simExtractionExpansion (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt)
        prf keys Q A).toTPKindAlg Psim Q Qs).next (kfFinalSwap prf keys Q A Psim σW σR J c) =
      (simExtractionExpansion (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt)
        prf keys Q A).toTPKindAlg Psim Q Qs).next c := by
  have hP : extractionProg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt)
        prf keys Q A).toTPKindAlg Psim Q Qs (kfFinalSwap prf keys Q A Psim σW σR J c) =
      extractionProg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt)
        prf keys Q A).toTPKindAlg Psim Q Qs c := by
    unfold extractionProg finalAnswer assBytes
    rw [advOut_kfFinalSwap hout, finalAss_kfFinalSwap hPsim, simQueryInputs_kfFinalSwap]
  simp only [simExtractionExpansion, OracleProg.toExpansion]
  rw [hP]

/-- **The outcomes of the extraction run of an adversary `Ag` of the simulation-extraction game**:
the expanded tuple of the measured registers and the database, the registers written out from
`Ag`'s workspace, width and slots (`SPBCS.Reg`), so that the type does not mention `Ag`'s
steps. -/
abbrev KFOutcome {shAg : AlgShape Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b)} (Ag : AdaptiveIAlg shAg (Claim X₀ M.NIProof)) (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b)
        SC')
    (Q kq : ℕ) : Type :=
  BaseGame.Tuple Xq (Out k e)
    (CWork Ag.CntW Ag.width Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b)
      Ag.slots (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) (kq + Q * Psim.q) ×
    DB Xq (Out k e)

omit [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] in
/-- **The extraction laws of equal adversaries, cast to one outcome type**: at `Ag₁ = Ag₂`, the
laws of the extraction runs (`simPMF` of `extAdv`) cast along `KFOutcome Agᵢ = Ω` are equal
(`PMF.map_cast_congr`). With `Ω` the outcomes of a shape term, the two outcome types are compared
with `Ω` alone, never with each other. -/
theorem simPMF_congr_shape
    {shAg : AlgShape Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b)}
    {Ag₁ Ag₂ : AdaptiveIAlg shAg (Claim X₀ M.NIProof)}
    (h : Ag₁ = Ag₂)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    {Ω : Type} (hΩ₁ : KFOutcome Ag₁ Psim Q kq = Ω) (hΩ₂ : KFOutcome Ag₂ Psim Q kq = Ω) :
    (simPMF (outEquiv k e) (extAdv Qs Ag₁ Psim Q kq)).map (cast hΩ₁) =
      (simPMF (outEquiv k e) (extAdv Qs Ag₂ Psim Q kq)).map (cast hΩ₂) :=
  PMF.map_cast_congr (α := fun Ag => KFOutcome Ag Psim Q kq)
    (fun Ag => simPMF (outEquiv k e) (extAdv Qs Ag Psim Q kq)) h hΩ₁ hΩ₂

/-- **The label of an outcome of `seAlgKF`**: `ℓ` at `A`'s workspace in the final registers. -/
noncomputable def kfLabel {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {Lb : Type} (ℓ : A.W → Option Lb) {kq : ℕ}
    (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
      A) Psim Q kq) : Option Lb :=
  ℓ (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
    keys Q A).toTPKindAlg Psim Q ω.1.out).1.1.work

/-- **The final witness swap of an outcome of `seAlgKF`**: `kfFinalSwap` on the final registers,
the queries, the answers and the database kept. -/
noncomputable def kfSwapOut {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    (σW : Equiv.Perm A.W) (σR : Equiv.Perm R) (J : A.W → Option ℕ)
    {kq : ℕ} (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt)
      prf keys Q A) Psim Q kq) :
    KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A)
      Psim Q kq :=
  -- TODO(unbundle-M4): explicit `rel`/`enc`/`dummyS`; `ω.1.out`'s type no longer fixes them
  (⟨ω.1.queries, ω.1.answers, kfFinalSwap (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
    A Psim σW σR J ω.1.out⟩, ω.2)

omit [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] in
/-- **The extraction queries of an adversary with other Kraus maps** are those of the
adversary: the expansion reads the output, the final assignments and the logs, not the steps. -/
theorem simExtractionExpansion_withStep_next
    {shAg : AlgShape Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b)} (Ag : AdaptiveIAlg shAg (Claim X₀ M.NIProof))
    (st : StepIdx Ag.slots Ag.post → KrausMap Ag.R
      (DReg Ag.W Ag.width Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b))
      (DReg Ag.W Ag.width Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b)))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (c : SPBCS.Reg (SC := SC') Ag Psim Q) :
    (simExtractionExpansion (Ag.withStep st).toTPKindAlg Psim Q Qs).next c =
      (simExtractionExpansion Ag.toTPKindAlg Psim Q Qs).next c :=
  rfl

/-- **The hypotheses of the block layers of the key-free adversary**: the block hypotheses of `A`
and `st'` along the witness swap `jTrip σW sw J` (`sw` the swap `σR` of the proof queries), with
sets closed under changes of the response, the recorded slot changing only at its step and the
requests away from it fixed by `sw`; trace-preserving `A` and `A.withStep st'`; `σR` keeping the
statements of the proof queries and whether their witnesses are in the relation, and the blank
tagged statement; a simulator that does not see the swap of the tagged statements; and `σW`
keeping the claim of `A`'s output. -/
structure KFSwapBlock (prf : Frg → Option M.NIProof)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    {Lb : Type} [DecidableEq Lb]
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)))
    (ℓ : A.W → Option Lb) (r : Lb)
    (G G' : ℕ → Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b)))
    (G₀ G₀' : Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b)))
    (σW : Equiv.Perm A.W) (σR : Equiv.Perm R) (J : A.W → Option ℕ) : Prop where
  /-- The block hypotheses along the witness swap. -/
  blockRel : A.BlockRel st' ℓ G G' G₀ G₀'
    (fun n => A.jTrip σW (Equiv.sumCongr (Equiv.refl _) σR) J (some n))
    (A.jTrip σW (Equiv.sumCongr (Equiv.refl _) σR) J none) r
  /-- The `none`-block hypotheses. -/
  blockNone : A.BlockNone st' ℓ G G' G₀ G₀'
  /-- `A`'s sets are closed under changes of the response. -/
  closed : ∀ idx w q a a', (w, q, a) ∈ AdaptiveIAlg.idxSet G G₀ idx →
    (w, q, a') ∈ AdaptiveIAlg.idxSet G G₀ idx
  /-- The other sets are closed under changes of the response. -/
  closed' : ∀ idx w q a a', (w, q, a) ∈ AdaptiveIAlg.idxSet G' G₀' idx →
    (w, q, a') ∈ AdaptiveIAlg.idxSet G' G₀' idx
  /-- The recorded slot changes only at its step. -/
  slot : A.JSlotStep G G₀ J
  /-- The requests away from the recorded slot are fixed by the swap. -/
  fixAway : A.SwapFixAway (Equiv.sumCongr (Equiv.refl _) σR) J ℓ r G
  /-- `A` is trace preserving. -/
  tp : A.TracePreserving
  /-- `A.withStep st'` is trace preserving. -/
  tp' : (A.withStep st').TracePreserving
  /-- `σR` keeps the statements of the proof queries. -/
  stmt_eq : ∀ q, (enc (.inr (σR q))).stmt = (enc (.inr q)).stmt
  /-- `σR` keeps whether the witnesses are in the relation. -/
  rel_iff : ∀ q, rel (enc (.inr (σR q))).stmt (enc (.inr (σR q))).wit ↔
    rel (enc (.inr q)).stmt (enc (.inr q)).wit
  /-- The swap of the tagged statements fixes the blank one. -/
  default_eq : ((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR))
    (default : Stmt × (MUR ⊕ R)) = default
  /-- The simulator does not see the swap of the tagged statements. -/
  sim : ∀ x c, Psim.prog (((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR)) x) c =
    Psim.prog x c
  /-- `σW` keeps the claim of `A`'s output. -/
  out : ∀ w, claimOfOutX prf (A.out (σW w)) = claimOfOutX prf (A.out w)

-- TODO(unbundle-M4): `convert hlaw using 2`; remove once M1b's named register types and
-- shape-indexed AdaptiveIAlg make both sides one instance path
/-- **The extraction law of the key-free adversary with other Kraus maps on one block** (the
h2-form): under `KFSwapBlock`, every event of the extraction run whose outcomes have label
`some r` and that the final witness swap keeps has the same probability for `A.withStep st'` and
for `A`. -/
theorem toOuterMeasure_extLaw_withStep_eq {prf : Frg → Option M.NIProof} {keys : Fin n →
    B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {Lb : Type} [DecidableEq Lb]
    {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b))}
    {ℓ : A.W → Option Lb} {r : Lb}
    {G G' : ℕ → Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {G₀ G₀' : Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R} {J : A.W → Option ℕ}
    (h : KFSwapBlock (rel := rel) (enc := enc) prf A Psim st' ℓ r G G' G₀ G₀' σW σR J) (kq : ℕ)
    (S : Set (KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
      keys Q A) Psim Q kq))
    (hS : ∀ ω ∈ S, kfLabel ℓ ω = some r)
    (hSτ : ∀ ω, kfSwapOut σW σR J ω ∈ S ↔ ω ∈ S) :
    (simPMF (outEquiv k e) (extAdv Qs ((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).withStep (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')) Psim Q
      kq)).toOuterMeasure S =
      (simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
        (Stmt := Stmt) prf keys Q A) Psim Q kq)).toOuterMeasure S := by
  have hA₂ := AdaptiveIAlg.mapOut_tracePreserving
    (A.absorbTab_tracePreserving (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
      h.tp (fun _ => keyReplyNone B keys)) (claimOfOutX prf)
  have hA₂' := AdaptiveIAlg.mapOut_tracePreserving
    ((A.withStep st').absorbTab_tracePreserving
      (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) h.tp'
      (fun _ => keyReplyNone B keys)) (claimOfOutX prf)
  have hF := seTwoKF_swapInv (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q h.stmt_eq
    h.rel_iff h.default_eq
  have hR := ((AdaptiveIAlg.BlockRel.absorbTabLog h.blockRel h.closed h.closed' hF h.slot
    (fun _ => keyReplyNone B keys)).mapOut (claimOfOutX prf)).toTP hA₂ hA₂'
  have hSH := AdaptiveIAlg.swapHyps_absorbTab h.blockRel h.blockNone h.closed h.closed' hF h.slot
    h.fixAway h.tp h.tp' (fun _ => keyReplyNone B keys) (claimOfOutX prf)
  have hlaw := AdaptiveIAlg.simLaw_expand_withStep_eq_of_swapHyps (outEquiv k e)
    (simExtractionExpansion (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    (simExtChallenger_swapInv Psim Q h.sim) hSH
    hR.init_supp hR.init_supp' hR.init_eq (simExtractionExpansion ((seAlgKF (rel := rel) (enc :=
        enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).withStep (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')).toTPKindAlg
      Psim Q Qs) (simExtractionExpansion_withStep_next (seAlgKF (rel := rel) (enc := enc)
        (dummyS := dummyS) (Stmt := Stmt) prf keys Q A) (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st') Psim Q)
    (fun c => simExtractionExpansion_next_kfFinalSwap h.out h.sim c) S hS hSτ
  have e1 := simLaw_eq_toOuterMeasure_simPMF (outEquiv k e) (extAdv Qs ((seAlgKF (rel := rel)
    (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A).withStep
        (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')) Psim Q kq) S
  have e2 := simLaw_eq_toOuterMeasure_simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel)
    (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A) Psim Q kq) S
  rw [← e1, ← e2]
  convert hlaw using 2

-- TODO(unbundle-M4): `convert hlaw using 2`; remove once M1b's named register types and
-- shape-indexed AdaptiveIAlg make both sides one instance path
/-- **The block mass of the extraction law of the key-free adversary with other Kraus maps**
(the h1-form): under `KFSwapBlock`, the event `S` of the outcomes with label `some r` has the
same probability
for `A.withStep st'` and for `A`. -/
theorem toOuterMeasure_extLaw_withStep_label {prf : Frg → Option M.NIProof} {keys : Fin n →
    B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {Lb : Type} [DecidableEq Lb]
    {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b))}
    {ℓ : A.W → Option Lb} {r : Lb}
    {G G' : ℕ → Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {G₀ G₀' : Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R} {J : A.W → Option ℕ}
    (h : KFSwapBlock (rel := rel) (enc := enc) prf A Psim st' ℓ r G G' G₀ G₀' σW σR J) (kq : ℕ)
    (S : Set (KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
      keys Q A) Psim Q kq))
    (r₁ : Lb) (hS : ∀ ω, ω ∈ S ↔ kfLabel ℓ ω = some r₁) :
    (simPMF (outEquiv k e) (extAdv Qs ((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).withStep (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')) Psim Q
      kq)).toOuterMeasure S =
      (simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
        (Stmt := Stmt) prf keys Q A) Psim Q kq)).toOuterMeasure S := by
  have hA₂ := AdaptiveIAlg.mapOut_tracePreserving
    (A.absorbTab_tracePreserving (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
      h.tp (fun _ => keyReplyNone B keys)) (claimOfOutX prf)
  have hA₂' := AdaptiveIAlg.mapOut_tracePreserving
    ((A.withStep st').absorbTab_tracePreserving
      (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) h.tp'
      (fun _ => keyReplyNone B keys)) (claimOfOutX prf)
  have hF := seTwoKF_swapInv (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q h.stmt_eq
    h.rel_iff h.default_eq
  have hR := ((AdaptiveIAlg.BlockRel.absorbTabLog h.blockRel h.closed h.closed' hF h.slot
    (fun _ => keyReplyNone B keys)).mapOut (claimOfOutX prf)).toTP hA₂ hA₂'
  have hSH := AdaptiveIAlg.swapHyps_absorbTab h.blockRel h.blockNone h.closed h.closed' hF h.slot
    h.fixAway h.tp h.tp' (fun _ => keyReplyNone B keys) (claimOfOutX prf)
  have hlaw := AdaptiveIAlg.simLaw_expand_withStep_mass_of_swapHyps (outEquiv k e)
    (simExtractionExpansion (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    (simExtChallenger_swapInv Psim Q h.sim) hSH
    hR.init_supp hR.init_supp' hR.init_eq (simExtractionExpansion ((seAlgKF (rel := rel)
      (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A).withStep
        (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')).toTPKindAlg
      Psim Q Qs) (simExtractionExpansion_withStep_next (seAlgKF (rel := rel) (enc := enc)
        (dummyS := dummyS) (Stmt := Stmt) prf keys Q A) (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st') Psim Q)
    r₁ S hS
  have e1 := simLaw_eq_toOuterMeasure_simPMF (outEquiv k e) (extAdv Qs ((seAlgKF (rel := rel)
    (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A).withStep
        (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')) Psim Q kq)
    S
  have e2 := simLaw_eq_toOuterMeasure_simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel)
    (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A) Psim Q kq)
    S
  rw [← e1, ← e2]
  convert hlaw using 2

/-- **The claim of an outcome of `seAlgKF`**, read from its final registers. -/
noncomputable def kfClaim {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'} {kq : ℕ}
    (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q kq) : Claim X₀ M.NIProof :=
  SPBCS.advOut (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
      A).toTPKindAlg Psim Q ω.1.out

/-- **The main logs of an outcome of `seAlgKF`**: `A`'s logged requests in its final registers. -/
noncomputable def kfMainLogs {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'} {kq : ℕ}
    (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q kq) : LogReg (MUR ⊕ R) A.slots :=
  (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys
      Q A).toTPKindAlg Psim Q ω.1.out).1.1.logs

/-- **An event reading only the claim, the database and the corruptions among the first `Q` main
requests** of an outcome of `seAlgKF`. -/
def ReadsClaimDB {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'} {kq : ℕ}
    (Fr : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q kq → Prop) : Prop :=
  ∀ ω ω', kfClaim ω = kfClaim ω' → ω.2 = ω'.2 →
    (∀ i, (Sum.inl (MURequest.corrupt i) : MUR ⊕ R) ∈ (requests (kfMainLogs ω)).take Q ↔
      (Sum.inl (MURequest.corrupt i) : MUR ⊕ R) ∈ (requests (kfMainLogs ω')).take Q) →
    (Fr ω ↔ Fr ω')

/-- **The final witness swap keeps the label** when `σW` does. -/
theorem kfLabel_kfSwapOut {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'} {kq : ℕ} {Lb :
        Type} {ℓ : A.W → Option Lb}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R} {J : A.W → Option ℕ} (hℓ : ∀ w, ℓ (σW w) = ℓ w)
    (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q kq) : kfLabel ℓ (kfSwapOut σW σR J ω) = kfLabel ℓ ω :=
  hℓ _

/-- **The final witness swap keeps the claim** when `σW` keeps the claim of `A`'s output. -/
theorem kfClaim_kfSwapOut {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'} {kq : ℕ} {σW :
        Equiv.Perm A.W} {σR : Equiv.Perm R}
    {J : A.W → Option ℕ}
    (hout : ∀ w, claimOfOutX prf (A.out (σW w)) = claimOfOutX prf (A.out w))
    (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q
        A) Psim Q kq) : kfClaim (kfSwapOut σW σR J ω) = kfClaim ω :=
  advOut_kfFinalSwap hout ω.1.out

/-- **The final witness swap keeps the multi-user requests among the first `Q` main requests**:
the swap of the proof queries fixes every multi-user request. -/
theorem mem_kfMainLogs_kfSwapOut {prf : Frg → Option M.NIProof} {keys : Fin n → B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'} {kq : ℕ} {σW :
        Equiv.Perm A.W} {σR : Equiv.Perm R}
    {J : A.W → Option ℕ} (ω : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt
        := Stmt) prf keys Q A) Psim Q kq) (x : MUR) :
    (Sum.inl x : MUR ⊕ R) ∈ (requests (kfMainLogs (kfSwapOut σW σR J ω))).take Q ↔
      (Sum.inl x : MUR ⊕ R) ∈ (requests (kfMainLogs ω)).take Q :=
  AdaptiveIAlg.mem_take_requests_logFam
    (fun i : Fin A.slots => swIf (J (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS
        := dummyS) (Stmt := Stmt) prf keys Q A).toTPKindAlg Psim Q ω.1.out).1.1.work = some (i : ℕ))
      (Equiv.sumCongr (Equiv.refl _) σR)) (kfMainLogs ω) (fun i => by unfold swIf; split_ifs <;>
          rfl)
    Q


/-- **The extraction law of the key-free adversary with other Kraus maps on the events of label
`some r` read by the claim and the database**: under `KFSwapBlock`, every event `S` of the outcomes
with label `some r` and a property `Fr` reading only the claim, the database and the corruptions
among the first `Q` main requests (`ReadsClaimDB`) has the same probability for `A.withStep st'`
and for `A`. -/
theorem toOuterMeasure_extLaw_withStep_label_and {prf : Frg → Option M.NIProof} {keys : Fin n →
    B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {Lb : Type} [DecidableEq Lb]
    {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b))}
    {ℓ : A.W → Option Lb} {r : Lb}
    {G G' : ℕ → Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {G₀ G₀' : Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {σW : Equiv.Perm A.W} {σR : Equiv.Perm R} {J : A.W → Option ℕ}
    (h : KFSwapBlock (rel := rel) (enc := enc) prf A Psim st' ℓ r G G' G₀ G₀' σW σR J) (kq : ℕ)
    (Fr : KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
      keys Q A) Psim Q kq → Prop) (hFr : ReadsClaimDB Fr)
    (S : Set (KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
      keys Q A) Psim Q kq))
    (hS : ∀ ω, ω ∈ S ↔ kfLabel ℓ ω = some r ∧ Fr ω) :
    (simPMF (outEquiv k e) (extAdv Qs ((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).withStep (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')) Psim Q
      kq)).toOuterMeasure S =
      (simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
        (Stmt := Stmt) prf keys Q A) Psim Q kq)).toOuterMeasure S := by
  have hℓ : ∀ w, ℓ (σW w) = ℓ w := fun w => h.blockRel.label_eq 0 (w, Sum.inr default, none)
  refine toOuterMeasure_extLaw_withStep_eq h kq S (fun ω hω => ((hS ω).1 hω).1) fun ω => ?_
  rw [hS, hS, kfLabel_kfSwapOut hℓ]
  refine and_congr_right fun _ => hFr _ _ (kfClaim_kfSwapOut h.out ω) rfl fun i => ?_
  exact mem_kfMainLogs_kfSwapOut ω _


/-- **The block mass of the extraction law from the `none`-block hypotheses alone**: for `A` and
`st'` satisfying `BlockNone` along sets closed under changes of the response, with trace-preserving
`A` and `A.withStep st'`, the event `S` of the outcomes with label `some r₁` has the same
probability for `A.withStep st'` and for `A` (`toOuterMeasure_extLaw_withStep_label` at the
identity swap, on the block `none` of the label read through `some`). -/
theorem toOuterMeasure_extLaw_withStep_label_of_blockNone {prf : Frg → Option M.NIProof} {keys :
    Fin n →
    B.KeyCoins} {Q : ℕ}
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A : AdaptiveIAlg shA (Frg × X₀)}
    {Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC'}
    {Lb : Type} [DecidableEq Lb]
    {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg A.W A.width Xq (XOut k e) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b))}
    {ℓ : A.W → Option Lb}
    {G G' : ℕ → Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    {G₀ G₀' : Set (A.W × (MUR ⊕ R) × Option (MUResponse B.core ⊕ M.Response b))}
    (hN : A.BlockNone st' ℓ G G' G₀ G₀')
    (closed : ∀ idx w q a a', (w, q, a) ∈ AdaptiveIAlg.idxSet G G₀ idx →
      (w, q, a') ∈ AdaptiveIAlg.idxSet G G₀ idx)
    (closed' : ∀ idx w q a a', (w, q, a) ∈ AdaptiveIAlg.idxSet G' G₀' idx →
      (w, q, a') ∈ AdaptiveIAlg.idxSet G' G₀' idx)
    (tp : A.TracePreserving) (tp' : (A.withStep st').TracePreserving) (kq : ℕ)
    (S : Set (KFOutcome (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf
      keys Q A) Psim Q kq))
    (r₁ : Lb) (hS : ∀ ω, ω ∈ S ↔ kfLabel ℓ ω = some r₁) :
    (simPMF (outEquiv k e) (extAdv Qs ((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
      (Stmt := Stmt) prf keys Q A).withStep (AdaptiveIAlg.absorbTabStep A
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) st')) Psim Q
      kq)).toOuterMeasure S =
      (simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
        (Stmt := Stmt) prf keys Q A) Psim Q kq)).toOuterMeasure S  := by
  have hσ : ∀ x : Stmt × (MUR ⊕ R),
      ((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) (Equiv.refl R))) x = x := by
    rintro ⟨s, q | q⟩ <;> rfl
  have h : KFSwapBlock (rel := rel) (enc := enc) prf A Psim st' (fun w => (ℓ w).map some) none G
      G' G₀ G₀' (Equiv.refl _) (Equiv.refl R) (fun _ => none) :=
    { blockRel := hN.toBlockRel (fun _ => none)
      blockNone := hN.mapSome
      closed := closed
      closed' := closed'
      slot := fun _ _ _ _ _ _ => Or.inl rfl
      fixAway := fun _ x _ _ _ _ => by rcases x with ⟨w, q | q, a⟩ <;> rfl
      tp := tp
      tp' := tp'
      stmt_eq := fun _ => rfl
      rel_iff := fun _ => Iff.rfl
      default_eq := hσ _
      sim := fun x c => by rw [hσ x]
      out := fun _ => rfl }
  exact toOuterMeasure_extLaw_withStep_label h kq S (some r₁) fun ω => by
    rw [hS]
    show _ ↔ Option.map some _ = some (some r₁)
    simp
    rfl


end ExtractBlock

end RingSignature.KeyFree

end GordieHowe
