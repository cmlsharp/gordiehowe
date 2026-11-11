-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ZeroKnowledge
public import GordieHowe.Model.Quantum.O2H.Budget

@[expose] public section

/-!
# Interactive adversaries that choose at run time between queries and requests

Unruh 2017 (ePrint 2017/398) Definition 6 (p. 14) quantifies over oracle algorithms (p. 10): a
probabilistic Turing machine that, at each oracle call, writes the index of the oracle it calls on a
classical tape. So the adversary of zero knowledge decides at run time, from its earlier measurement
outcomes, whether its next call is a query to the random oracle or a proof request. An interactive
adversary of `GordieHowe/Model/Quantum/Interactive/Basic.lean` (`IAlg`) fixes the kind of every slot in its
schedule. This file defines the adversaries whose slot kinds are chosen at run time (`AdaptiveIAlg`)
and gives them the semantics of the model.

## The model

An adaptive adversary has a kind register in its workspace (`kind : W → Bool`, request when
`true`). At each slot the kind register is measured together with the request register (the
request measurement `KindAlg.measReq`), so the choice is classical, as the Turing machine's
oracle index. A slot of the composed core algorithm (`KindAlg.slotCircBoth`) contains both the
challenger's `q` classical queries and the adversary's `width` queries; on each branch the ones of
the other kind are padded (they read the all-zero assignment list, `paddingAssignments`, and add
`0`): on a request branch the adversary's queries, on a query branch the challenger's. The core
algorithm therefore has a fixed query depth (`KindAlg.composeBoth_depth`), as the core model of
`GordieHowe/Model/Quantum/Core/Model.lean` requires, while each branch queries at the slots it chooses.

The adversary has a **query budget** of `budget` slots: its workspace is extended by a classical
counter of its query slots, and a branch that asks for a query slot after `budget` of them halts
(its weight is removed, as a non-terminating run of a trace-non-increasing Kraus map, HU25
p. 248), so on every branch at most `budget` slots are query slots, `width * budget` queries
(`AdaptiveIAlg.toKindAlg`). This is the run-time counterpart of a Turing machine that makes at
most `t` queries on every run. Requests are not counted by the adversary; the challenger answers
the first `Q` (`Challenger`).

## Results

- `KindAlg.composeBoth_eq_pureGame`: the probability that the composed core algorithm outputs
  `o` is the acceptance probability of the pure game of `GordieHowe/Model/Quantum/Pure/Game.lean` for the
  dilated adversary (deferred measurement).
- `AdaptiveIAlg.budget`: the dilated adversary has a query budget of `budget` slots
  (`Distinguisher.Budget`), so the zero-knowledge games of `GordieHowe/Model/QROM/NIZK.lean` charge it
  `width * budget` queries.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder MatrixOrder

namespace GordieHowe.Quantum

/-! ### Slots of both kinds -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O) (C : Challenger X Y Req Resp)

/-- **Slot `j` with its kind chosen at run time**: the adversary's Kraus map, the request
measurement (of the kind register and the request), the challenger's queries (padded on the
branches without a request), its reply, and the adversary's queries (padded on the branches with
a request). -/
noncomputable def slotCircBoth (j : Fin A.slots) : ReprogrammedCircuit (A.CW C) X Y :=
  .kraus (A.advKraus C (slotStep j)) (.kraus (A.measReq C j)
    (A.chalQueries C j ++ .kraus (KrausMap.ofPerm (A.writeReply C j))
      (A.advQueries C fun v => A.advAss C j v.chal)))

/-- The whole run with every slot's kind chosen at run time: the slots, the post batches, the
adversary's last Kraus map. -/
noncomputable def fullCircBoth : ReprogrammedCircuit (A.CW C) X Y :=
  ReprogrammedCircuit.concat ((List.finRange A.slots).map fun j => A.slotCircBoth C j) ++
    ReprogrammedCircuit.concat ((List.finRange A.post).map (A.postCirc C)) ++
      .kraus (A.advKraus C lastStep) .nil

theorem queries_slotCircBoth (j : Fin A.slots) :
    (A.slotCircBoth C j).queries = C.q + A.width := by
  simp [slotCircBoth, ReprogrammedCircuit.queries, ReprogrammedCircuit.queries_append,
    queries_advQueries, queries_chalQueries]

theorem queries_fullCircBoth :
    (A.fullCircBoth C).queries = A.slots * (C.q + A.width) + A.width * A.post := by
  rw [fullCircBoth, ReprogrammedCircuit.queries_append, ReprogrammedCircuit.queries_append,
    ReprogrammedCircuit.queries_concat, ReprogrammedCircuit.queries_concat, List.map_map,
    List.map_map]
  have h1 : (List.finRange A.slots).map ((fun c => ReprogrammedCircuit.queries c) ∘
      fun j => A.slotCircBoth C j) = (List.finRange A.slots).map fun _ => C.q + A.width :=
    List.map_congr_left fun j _ => A.queries_slotCircBoth C j
  have h2 : (List.finRange A.post).map ((fun c => ReprogrammedCircuit.queries c) ∘ A.postCirc C) =
      (List.finRange A.post).map fun _ => A.width :=
    List.map_congr_left fun b _ => A.queries_postCirc C b
  rw [h1, h2]
  simp [ReprogrammedCircuit.queries, mul_comm]

variable [Nonempty Y]

/-- **A slot with its kind chosen at run time is one slot of the mixed game with the measured
request**, placed in the composed registers: on the request branches the challenger's queries
answer and the adversary's are padded; on the others the reverse. -/
theorem run_slotCircBoth (H : X → Y) (c : C.Coins) (j : Fin A.slots)
    {σ : Matrix A.G A.G ℂ} (hσ : SuppIn (A.blankFrom j) σ) :
    (A.slotCircBoth C j).run H (embed (A.emb C H c j) σ) =
      embed (A.emb C H c (j + 1)) ((Circuit.kraus (A.liftG (slotStep j))
        (A.eventCirc C.toPureEnv (H, c) j true)).run (Equiv.refl _) σ) := by
  have hσ1 := SuppIn.liftG A hσ ⟨j, by omega⟩
  set σ1 := (A.liftG (slotStep j)) σ
  have hσ2 : SuppIn (A.TSet j)
      ((dephase A.reqOutG σ1).submatrix (A.copyG j).symm (A.copyG j).symm) :=
    (hσ1.dephase _).submatrix_perm fun r hr => A.copyG_mem_TSet j hr
  set σ2 := (dephase A.reqOutG σ1).submatrix (A.copyG j).symm (A.copyG j).symm
  have hσ3 : SuppIn (A.TSet j) (σ2.submatrix
      (A.respG C.toPureEnv (H, c) j).symm (A.respG C.toPureEnv (H, c) j).symm) :=
    hσ2.submatrix_perm fun r hr => A.respG_mem_TSet C j (H, c) hr
  have hfront : (ReprogrammedCircuit.kraus (A.advKraus C (slotStep j))
      (ReprogrammedCircuit.kraus (A.measReq C j) ReprogrammedCircuit.nil)).run
      H (embed (A.emb C H c j) σ) = embed (A.emb C H c j) σ2 := by
    simp only [ReprogrammedCircuit.run]
    rw [advKraus_apply_embed, measReq, KrausMap.comp_apply, KrausMap.measureFn_apply,
      dephase_embed, reqOutcome_emb, KrausMap.ofPerm_apply (A.copyReq C j),
      submatrix_embed (π' := A.copyG j) (S := Set.univ) (fun r _ => A.copyReq_emb C H c j r)
        (fun a b h => by simp at h)]
  have hgame : (Circuit.kraus (A.liftG (slotStep j))
      (A.eventCirc C.toPureEnv (H, c) j true)).run (Equiv.refl _) σ =
      (σ2.submatrix (A.respG C.toPureEnv (H, c) j).symm
        (A.respG C.toPureEnv (H, c) j).symm).submatrix
        (C.toPureEnv.oraclePerm A.kind (H, c)).symm (C.toPureEnv.oraclePerm A.kind (H, c)).symm := by
    simp only [eventCirc, Circuit.run, ↓reduceIte, KrausMap.ofPerm_apply, KrausMap.measureFn_apply]
    rw [A.copy_measure j hσ1]
  rw [hgame]
  have hrun : (A.slotCircBoth C j).run H (embed (A.emb C H c j) σ) =
      (ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.writeReply C j))
        (A.advQueries C fun v => A.advAss C j v.chal)).run H
        ((A.chalQueries C j).run H ((ReprogrammedCircuit.kraus (A.advKraus C (slotStep j))
          (ReprogrammedCircuit.kraus (A.measReq C j) ReprogrammedCircuit.nil)).run H
            (embed (A.emb C H c j) σ))) := by
    simp only [slotCircBoth, ReprogrammedCircuit.run, ReprogrammedCircuit.run_append]
  rw [hrun, hfront, run_chalQueries]
  simp only [ReprogrammedCircuit.run]
  rw [KrausMap.ofPerm_apply, submatrix_embed (π' := A.respG C.toPureEnv (H, c) j) (S := A.TSet j)
    (fun r hr => A.writeReply_emb C H c j hr) hσ2,
    A.run_advQueries C H c (j + 1) _
      (fun s => if A.kind s.1 then 0 else C.toPureEnv.oracle (H, c) s.2.2.2)
      (fun r hr _ => A.advAss_eq C H c j hr) hσ3]
  rfl

theorem run_slotsBoth (H : X → Y) (c : C.Coins) (l : List (Fin A.slots)) (j : ℕ)
    (hl : l.map Fin.val = List.range' j l.length) {σ : Matrix A.G A.G ℂ}
    (hσ : SuppIn (A.blankFrom j) σ) :
    (ReprogrammedCircuit.concat (l.map fun k => A.slotCircBoth C k)).run H
        (embed (A.emb C H c j) σ) =
      embed (A.emb C H c (j + l.length))
        ((Circuit.concat (l.map (A.gameSlot C H c))).run (Equiv.refl _) σ) ∧
    SuppIn (A.blankFrom (j + l.length))
        ((Circuit.concat (l.map (A.gameSlot C H c))).run (Equiv.refl _) σ) := by
  induction l generalizing j σ with
  | nil => exact ⟨rfl, hσ⟩
  | cons k l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    have hσ' : SuppIn (A.blankFrom k) σ := by rw [hl.1]; exact hσ
    have h1 := A.run_slotCircBoth C H c k hσ'
    have h2 : SuppIn (A.blankFrom (k + 1)) ((A.gameSlot C H c k).run (Equiv.refl _) σ) :=
      A.suppIn_slot C H c k hσ'
    obtain ⟨ih1, ih2⟩ := ih (↑k + 1) (by rw [hl.2, hl.1]) h2
    rw [ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append, Circuit.run_concat, ← hl.1, h1,
      ih1]
    rw [show (k : ℕ) + 1 + l.length = k + (l.length + 1) by omega] at ih2 ⊢
    exact ⟨rfl, ih2⟩

/-- **The composition with run-time kinds runs the mixed game with measured requests**. -/
theorem fullCircBoth_run (H : X → Y) (c : C.Coins) :
    (A.fullCircBoth C).run H (embed (A.emb C H c 0) A.mgInit) =
      embed (A.emb C H c A.slots) (A.mgRun C.toPureEnv (H, c) true) := by
  obtain ⟨h1, -⟩ := A.run_slotsBoth C H c (List.finRange A.slots) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    A.suppIn_mgInit
  rw [List.length_finRange, Nat.zero_add] at h1
  simp only [fullCircBoth, mgRun, mgCirc, ReprogrammedCircuit.run_append, Circuit.run_append]
  rw [h1, run_posts]
  simp only [ReprogrammedCircuit.run, Circuit.run]
  rw [advKraus_apply_embed]

/-- **The composed core algorithm with run-time kinds**: the compiled circuit `fullCircBoth` on
the composed registers with the clean ancilla, the output read from the adversary's workspace. -/
noncomputable abbrev composeBoth : Alg X Y O :=
  (A.fullCircBoth C).toCircuit.toAlg (MState.withAnc x₀ (A.initSys C))
    fun v => A.out v.1.adv.workspace

/-- **The query count of the composition with run-time kinds**: the challenger's `q` queries and
the adversary's `width` queries at every slot (the ones of the other kind padded), then `width`
queries per post batch. -/
theorem composeBoth_depth :
    (A.composeBoth C).depth = A.slots * (C.q + A.width) + A.width * A.post := by
  rw [composeBoth, Circuit.toAlg_depth, ReprogrammedCircuit.queries_toCircuit]
  exact A.queries_fullCircBoth C

/-- **The final state of the composition with run-time kinds**: the clean ancilla and the
coin-mixture of the placed final states of the mixed game with measured requests. -/
theorem composeBoth_final (H : X → Y) :
    (A.composeBoth C).final H = withAnc x₀ (∑ c, ((C.coins c).toReal : ℂ) •
      embed (A.emb C H c A.slots) (A.mgRun C.toPureEnv (H, c) true)) := by
  rw [Circuit.toAlg_final]
  change (A.fullCircBoth C).toCircuit.run (queryPerm H) (withAnc x₀ (A.initSys C).mat) = _
  rw [ReprogrammedCircuit.run_toCircuit]
  congr 1
  simp only [initSys, MState.mix, A.initSys_coin C H]
  rw [ReprogrammedCircuit.run_sum_smul]
  simp only [A.fullCircBoth_run C]

/-- **The output law of the composition with run-time kinds** is the coin-average of the
acceptance probabilities of the mixed game with measured requests. -/
theorem outLaw_composeBoth_some [DecidableEq O] (H : X → Y) (o : O) :
    (A.composeBoth C).outLaw H (some o) =
      ENNReal.ofReal (∑ c, (C.coins c).toReal * A.mgAccept C.toPureEnv o (H, c) true) := by
  have hpsd := (A.composeBoth C).posSemidef_stage H (A.composeBoth C).depth
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some _ _ _ _ o).trans ?_
  have hdiag : ∀ p, 0 ≤ ((A.composeBoth C).final H p p).re := fun p =>
    (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := p))).1
  have hite : ∀ p, (if some o = some ((A.composeBoth C).out p.1) then
      ENNReal.ofReal ((A.composeBoth C).final H p p).re else 0) =
      ENNReal.ofReal (if o = (A.composeBoth C).out p.1 then
        ((A.composeBoth C).final H p p).re else 0) :=
    fun p => by split_ifs with h1 h2 h2 <;> simp_all
  refine (Finset.sum_congr rfl fun p _ => hite p).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => by split_ifs; exact hdiag p; exact le_rfl]
  congr 1
  rw [composeBoth_final]
  have hanc : ∀ a : X × Y × Bool, (reprogAnc (Y := Y) (x₀ : X) a a).im = 0 := fun a => by
    simp only [reprogAnc, ancWeight]
    split_ifs <;> simp
  have hstep : ∀ σ : Matrix (QueryReg (A.CW C) 1 X Y) (QueryReg (A.CW C) 1 X Y) ℂ,
      (∑ p : ReprogrammedQueryReg (A.CW C) X Y,
        if o = A.out p.1.1.adv.workspace then (withAnc x₀ σ p p).re else 0) =
        ∑ q : QueryReg (A.CW C) 1 X Y,
          if o = A.out q.1.adv.workspace then (σ q q).re else 0 := by
    intro σ
    rw [← (ancSplit (A.CW C) X Y).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ancSplit, Equiv.coe_fn_symm_mk, withAnc, Complex.mul_re, hanc, mul_zero, sub_zero]
    split_ifs
    · rw [← Finset.mul_sum, sum_re_reprogAnc, mul_one]
    · simp
  refine (hstep _).trans ?_
  simp only [re_sum_smul_apply]
  have hg : ∀ q : QueryReg (A.CW C) 1 X Y, ∀ x : ℝ,
      (if o = A.out q.1.adv.workspace then x else 0) =
        (if o = A.out q.1.adv.workspace then 1 else 0) * x :=
    fun q x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun q _ => hg q _]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_left_comm _ (C.coins c).toReal, ← Finset.mul_sum]
  congr 1
  rw [embed_diag_of_injective (A.emb_injective C H c A.slots)]
  simp only [mgAccept]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hw : A.out (A.emb C H c A.slots r).1.adv.workspace = A.out r.1.1 := rfl
  simp only [hw]
  by_cases h : A.out r.1.1 = o
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Deferred measurement for adversaries with run-time kinds** (Nielsen–Chuang section 4.4): the probability that the composed core algorithm outputs `o` is the
acceptance probability of the pure game for the dilated adversary `A.dilate o` against the
challenger as an environment, with the post-phase unitary `A.postOp`. -/
theorem composeBoth_eq_pureGame [DecidableEq O] (o : O) :
    ((A.composeBoth C).realLaw (Equiv.refl Y)).toOuterMeasure {p | p.out = some o} =
      ENNReal.ofReal ((A.dilate o).acceptProb C.toPureEnv A.postOp) := by
  have hacc : ∀ (H : X → Y) (c : C.Coins), A.mgAccept C.toPureEnv o (H, c) true =
      (A.dilate o).acceptProbAt C.toPureEnv A.postOp (H, c) := fun H c => by
    rw [mgAccept_deph, acceptProbAt_dilate]
  have hnn : ∀ ω, 0 ≤ (A.dilate o).acceptProbAt C.toPureEnv A.postOp ω :=
    fun ω => prob_nonneg _ _
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  simp only [PMF.toOuterMeasure_map_apply]
  have hpre : ∀ H : X → Y, (fun o' : Option O => (⟨o', (Equiv.refl Y) ∘ H⟩ : Outcome _ X Y)) ⁻¹'
      {p | p.out = some o} = {some o} := fun H => by ext; simp
  simp only [hpre, PMF.toOuterMeasure_apply_singleton, A.outLaw_composeBoth_some C, hacc]
  rw [Distinguisher.acceptProb, Fintype.sum_prod_type,
    ENNReal.ofReal_sum_of_nonneg fun H _ => Finset.sum_nonneg fun c _ =>
      mul_nonneg ENNReal.toReal_nonneg (hnn _)]
  refine Finset.sum_congr rfl fun H _ => ?_
  simp only [IAlg.toPureEnv_μ_apply, ENNReal.toReal_mul, mul_assoc, ← Finset.mul_sum]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

end KindAlg

/-! ### Supports of the dilated steps -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)

section

/-- The completed Kraus map sends no amplitude to a running state outside `Q` from a halted state
or from a running state in `P`, when the Kraus map itself does not map `P` outside `Q`. -/
theorem complete_op_eq_zero_of {k : StepIdx A.slots A.post} {P Q : A.W → Prop}
    (hop : ∀ r (y x : DReg A.W A.width X Y Req Resp), P x.workspace → ¬ Q y.workspace →
      (A.step k).op r y x = 0)
    (i : A.R ⊕ Bool) {y x : DReg A.W A.width X Y Req Resp} {b : Bool}
    (hy : ¬ Q y.workspace) (hx : b = true ∨ P x.workspace) :
    (A.step k).complete.op i (y, false) (x, b) = 0 := by
  rcases i with r | _ | _ <;> cases b <;>
    simp only [KrausMap.complete, KrausMap.completeOp, kroneckerMap_apply, Matrix.single_apply] <;>
    simp
  rcases hx with hx | hx
  · exact absurd hx Bool.false_ne_true
  · exact hop r y x hx hy

/-- **The dilated step keeps a support of the workspace**: if the Kraus map number `k` does not
map workspaces in `P` to workspaces outside `Q`, its dilation maps the states with clean ancilla
from `k` on whose branch has halted or is in `P` to states with clean ancilla from `k + 1` on whose
branch has halted or is in `Q`. -/
theorem uStepD_supported {k : ℕ} (hk : k < A.slots + A.post + 1) {P Q : A.W → Prop}
    (hop : ∀ r (y x : DReg A.W A.width X Y Req Resp), P x.workspace → ¬ Q y.workspace →
      (A.step ⟨k, hk⟩).op r y x = 0)
    {v : QState (DReg A.DW A.width X Y Req Resp)}
    (hv : Supported {d : DReg A.DW A.width X Y Req Resp | MixedAlg.Clean k d.workspace.2.2 ∧
      (d.workspace.2.1 = true ∨ P d.workspace.1)} v) :
    Supported {d : DReg A.DW A.width X Y Req Resp | MixedAlg.Clean (k + 1) d.workspace.2.2 ∧
      (d.workspace.2.1 = true ∨ Q d.workspace.1)} (A.uStepD k v) := by
  intro r hr
  change ((Quantum.relabel A.relD.symm).trans (A.uStep k)).trans (Quantum.relabel A.relD) v r = 0
  have hψ : ∀ (x : DReg A.W A.width X Y Req Resp) b a,
      ¬ (MixedAlg.Clean k a ∧ (b = true ∨ P x.workspace)) →
        Quantum.relabel A.relD.symm v ((x, b), a) = 0 := by
    intro x b a h
    rw [relabel_apply, Equiv.symm_symm]
    exact hv _ h
  have hfresh : Fresh (MixedAlg.stepSplit (⟨k, hk⟩ : Fin (A.slots + A.post + 1)))
      (Classical.arbitrary (A.R ⊕ Bool)) (Quantum.relabel A.relD.symm v) :=
    fun i a ha => by
      obtain ⟨x, b⟩ := i
      refine hψ x b a fun h => ha ?_
      simpa [MixedAlg.stepSplit] using h.1.1 ⟨k, hk⟩ le_rfl
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, relabel_apply]
  simp only [uStep, hk, ↓reduceDIte]
  rw [stinespring_apply_of_fresh _ hfresh, krausAct_apply]
  obtain ⟨⟨⟨w, b', a'⟩, req, resp⟩, qs⟩ := r
  simp only [DReg.workspace, Set.mem_ofPred_eq, not_and_or, not_or] at hr
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨x, b⟩ := j
  by_cases hj : MixedAlg.Clean k ((MixedAlg.stepSplit (⟨k, hk⟩ : Fin (A.slots + A.post + 1))).symm
      (Classical.arbitrary (A.R ⊕ Bool),
        (MixedAlg.stepSplit (⟨k, hk⟩ : Fin (A.slots + A.post + 1)) a').2)) ∧
      (b = true ∨ P x.workspace)
  · rcases hr with hc | ⟨hb', hQ⟩
    · refine absurd ?_ hc
      have h1 := hj.1
      rw [MixedAlg.stepSplit_symm_reset] at h1
      refine ⟨fun i hi => ?_, h1.2⟩
      have hne : i ≠ ⟨k, hk⟩ := fun hik => by
        rw [hik] at hi
        exact Nat.not_succ_le_self k hi
      have := h1.1 i (by omega)
      simp only at this
      rwa [Function.update_of_ne hne] at this
    · rw [Bool.not_eq_true] at hb'
      subst hb'
      exact mul_eq_zero_of_left (A.complete_op_eq_zero_of hop _ (y := ((w, req, resp), qs)) hQ
        hj.2) _
  · exact mul_eq_zero_of_right _ (hψ x b _ hj)

end

variable [AddGroup Y]

omit [AddGroup Y] in
theorem dilInit_eq_zero_of_diag {g : A.GB} (hg : (A.gameMixed.init ()).mat g g = 0) (a : A.DAnc) :
    A.gameMixed.dilInit () (g, a) = 0 := by
  simp only [MixedAlg.dilInit, appendKet_apply]
  rw [purify_apply_eq_zero _ hg, zero_mul]

/-- **The initial state of the dilated distinguisher** has clean ancilla and is in `P` on the
running branch, if the initial state of the mixed game is supported in `P`. -/
theorem dilate_init_supported [DecidableEq O] (o : O) {P : A.W → Prop}
    (hP : SuppIn {r : A.G | P r.1.1} A.mgInit) :
    Supported {d : DReg A.DW A.width X Y Req Resp | MixedAlg.Clean 0 d.workspace.2.2 ∧
      (d.workspace.2.1 = true ∨ P d.workspace.1)} (A.dilate o).init := by
  rw [A.dilate_init o]
  intro r hr
  obtain ⟨⟨⟨w, b, a⟩, req, resp⟩, qs⟩ := r
  simp only [DReg.workspace, Set.mem_ofPred_eq, not_and_or, not_or] at hr
  change A.gameMixed.dilInit () ((splitLogs.symm (((w, req, resp), qs), fun _ => none), b), a) = 0
  rcases hr with hc | ⟨hb, hw⟩
  · exact A.gameMixed.cleanVec_dilInit () _ _ hc
  · refine A.dilInit_eq_zero_of_diag ?_ a
    rw [Bool.not_eq_true] at hb
    subst hb
    have h0 := hP (splitLogs.symm (((w, req, resp), qs), fun _ => none))
      (splitLogs.symm (((w, req, resp), qs), fun _ => none)) (Or.inl hw)
    change A.mgInit _ _ * Matrix.single false false (1 : ℂ) false false = 0
    rw [h0, zero_mul]

end KindAlg

/-! ### Kraus maps that halt outside a set -/

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **A Kraus map followed by the projection onto a set** `{i | p i}`: the operators
`P * op r` with `P` the diagonal projector. The weight outside the set is removed, which the
model reads as non-termination (HU25 p. 248). -/
def restrict (K : KrausMap R ι ι) (p : ι → Bool) : KrausMap R ι ι where
  op r := Matrix.diagonal (fun i => if p i then 1 else 0) * K.op r
  sum_le := by
    set D : Matrix ι ι ℂ := Matrix.diagonal fun i => if p i then 1 else 0
    have hD : Dᴴ * D = D := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hp : p i <;> simp [hp]
    have hDc : (1 - D).PosSemidef := by
      have : (1 : Matrix ι ι ℂ) - D = Matrix.diagonal fun i => if p i then 0 else 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hp : p i <;> simp [D, hp]
        · simp [D, hij]
      rw [this]
      exact Matrix.PosSemidef.diagonal fun i => by by_cases hp : p i <;> simp [hp]
    have h1 : ∑ r, (D * K.op r)ᴴ * (D * K.op r) ≤ ∑ r, (K.op r)ᴴ * K.op r := by
      rw [Matrix.le_iff]
      have : ∑ r, (K.op r)ᴴ * K.op r - ∑ r, (D * K.op r)ᴴ * (D * K.op r) =
          ∑ r, (K.op r)ᴴ * (1 - D) * K.op r := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ, hD, Matrix.mul_sub,
          Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      rw [this]
      exact Matrix.posSemidef_sum _ fun r _ => hDc.conjTranspose_mul_mul_same (K.op r)
    exact h1.trans K.sum_le

end KrausMap

/-! ### Shapes -/

/-- **The shape of an adversary with run-time kinds** at the interface `X, Y, Req, Resp`: its
workspace, width, slots, post batches, budget and Kraus index. -/
structure AlgShape (X Y Req Resp : Type) where
  /-- The workspace. -/
  W : Type
  [instFintypeW : Fintype W]
  [instDecidableEqW : DecidableEq W]
  /-- The number of parallel query pairs. -/
  width : ℕ
  width_pos : 0 < width
  /-- The number of slots. -/
  slots : ℕ
  /-- The number of query batches after the last slot. -/
  post : ℕ
  /-- The number of slots that may be query slots on a branch. -/
  budget : ℕ
  /-- The index type of the Kraus operators. -/
  R : Type
  [instFintypeR : Fintype R]

attribute [instance] AlgShape.instFintypeW AlgShape.instDecidableEqW AlgShape.instFintypeR

/-- **The workspace with the query counter at a shape** (`AdaptiveIAlg.toKindAlg`): the shape's
workspace and the number of query slots so far. A named type, so that instance search over the
registers built from it stops at its own instances. -/
def AlgShape.CntW {X Y Req Resp : Type} (s : AlgShape X Y Req Resp) : Type := s.W × Fin (s.budget + 2)

instance AlgShape.instFintypeCntW {X Y Req Resp : Type} (s : AlgShape X Y Req Resp) :
    Fintype s.CntW :=
  inferInstanceAs (Fintype (s.W × Fin (s.budget + 2)))

instance AlgShape.instDecidableEqCntW {X Y Req Resp : Type} (s : AlgShape X Y Req Resp) :
    DecidableEq s.CntW :=
  inferInstanceAs (DecidableEq (s.W × Fin (s.budget + 2)))

namespace AlgShape.CntW

variable {X Y Req Resp : Type} {s : AlgShape X Y Req Resp}

/-- The workspace `w` with the counter at `c`. -/
def mk (w : s.W) (c : Fin (s.budget + 2)) : s.CntW := (w, c)

/-- The workspace of a workspace with the counter. -/
def work (x : s.CntW) : s.W := Prod.fst (α := s.W) (β := Fin (s.budget + 2)) x

/-- The counter of a workspace with the counter. -/
def cnt (x : s.CntW) : Fin (s.budget + 2) := Prod.snd (α := s.W) (β := Fin (s.budget + 2)) x

@[simp] theorem work_mk (w : s.W) (c : Fin (s.budget + 2)) : (mk w c).work = w := rfl

@[simp] theorem cnt_mk (w : s.W) (c : Fin (s.budget + 2)) : (mk w c).cnt = c := rfl

@[simp] theorem mk_work_cnt (x : s.CntW) : mk x.work x.cnt = x := rfl

@[ext] theorem ext {x y : s.CntW} (h₁ : x.work = y.work) (h₂ : x.cnt = y.cnt) : x = y :=
  Prod.ext h₁ h₂

theorem exists_eq_mk (x : s.CntW) : ∃ w c, x = mk w c := ⟨x.work, x.cnt, rfl⟩

theorem mk_inj {w w' : s.W} {c c' : Fin (s.budget + 2)} : mk w c = mk w' c' ↔ w = w' ∧ c = c' :=
  Prod.mk.injEq w c w' c' ▸ Iff.rfl

end AlgShape.CntW

/-- **The workspace with the counter as a pair** (`AlgShape.CntW`). -/
def AlgShape.cntWEquiv {X Y Req Resp : Type} (s : AlgShape X Y Req Resp) :
    s.CntW ≃ s.W × Fin (s.budget + 2) where
  toFun x := (x.work, x.cnt)
  invFun p := .mk p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem AlgShape.cntWEquiv_apply {X Y Req Resp : Type} (s : AlgShape X Y Req Resp)
    (x : s.CntW) : s.cntWEquiv x = (x.work, x.cnt) := rfl

@[simp] theorem AlgShape.cntWEquiv_symm_apply {X Y Req Resp : Type} (s : AlgShape X Y Req Resp)
    (p : s.W × Fin (s.budget + 2)) : s.cntWEquiv.symm p = .mk p.1 p.2 := rfl

/-! ### Interactive adversaries with run-time kinds -/

/-- **An interactive mixed adversary with run-time kinds and a query budget** (Unruh 2017, ePrint
2017/398, p. 10, oracle algorithms, whose Turing machine chooses at run time which oracle it calls):
as `IAlg`, except that whether slot `j` is a request or a batch of `width` queries is read from the
kind register of the workspace (`kind`, request when `true`) and measured at the slot, and that on
every branch at most `budget` slots are query slots: a branch that asks for a further query slot
halts (`toKindAlg`). The run is `step 0`, slot `0`, `step 1`, …, slot `slots - 1`, `step slots`,
then `post` batches of `width` queries with `step (slots + 1)`, …, `step (slots + post)` between and
after them. The Kraus maps are trace-non-increasing. The output is read from the computational-basis
measurement of the workspace. -/
structure AdaptiveIAlg {X Y Req Resp : Type} [Fintype X] [Fintype Y] [Fintype Req]
    [Fintype Resp] [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp]
    (sh : AlgShape X Y Req Resp) (O : Type) where
  /-- The kind register: request (`true`) or query (`false`), read from the workspace. -/
  kind : sh.W → Bool
  /-- The initial state. -/
  init : MState (DReg sh.W sh.width X Y Req Resp)
  /-- The Kraus maps. -/
  step : StepIdx sh.slots sh.post →
    KrausMap sh.R (DReg sh.W sh.width X Y Req Resp) (DReg sh.W sh.width X Y Req Resp)
  /-- The output read from the workspace. -/
  out : sh.W → O

-- Two algorithms with the same kind, initial state, steps and output are equal.
attribute [ext] AdaptiveIAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {sh : AlgShape X Y Req Resp}

/-- The workspace: the shape's. -/
abbrev W (_ : AdaptiveIAlg sh O) : Type := sh.W
/-- The number of parallel query pairs: the shape's. -/
abbrev width (_ : AdaptiveIAlg sh O) : ℕ := sh.width
theorem width_pos (A : AdaptiveIAlg sh O) : 0 < A.width := sh.width_pos
/-- The number of slots: the shape's. -/
abbrev slots (_ : AdaptiveIAlg sh O) : ℕ := sh.slots
/-- The number of post batches: the shape's. -/
abbrev post (_ : AdaptiveIAlg sh O) : ℕ := sh.post
/-- The query budget: the shape's. -/
abbrev budget (_ : AdaptiveIAlg sh O) : ℕ := sh.budget
/-- The Kraus index: the shape's. -/
abbrev R (_ : AdaptiveIAlg sh O) : Type := sh.R
/-- **The shape of an adversary**: its type index. -/
abbrev toShape (_ : AdaptiveIAlg sh O) : AlgShape X Y Req Resp := sh

/-- The workspace's `Fintype` instance: the shape's (not an instance: the adversary does not occur
in `sh.W`, so instance search finds the shape's instance directly). -/
abbrev instFintypeW (_ : AdaptiveIAlg sh O) : Fintype sh.W := sh.instFintypeW
/-- The workspace's `DecidableEq` instance: the shape's. -/
abbrev instDecidableEqW (_ : AdaptiveIAlg sh O) : DecidableEq sh.W := sh.instDecidableEqW
/-- The Kraus index's `Fintype` instance: the shape's. -/
abbrev instFintypeR (_ : AdaptiveIAlg sh O) : Fintype sh.R := sh.instFintypeR

end AdaptiveIAlg

/-- **`omega` over the accessors of an adversary**: unfolds the accessors to the fields of the
shape, then runs `omega`. `omega` does not unfold the accessors, so without this step it treats
`A.slots` and `sh.slots` as different atoms. -/
macro "shape_omega" : tactic =>
  `(tactic| ((try simp only [AdaptiveIAlg.slots, AdaptiveIAlg.post, AdaptiveIAlg.budget,
    AdaptiveIAlg.width] at *); omega))

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {sh : AlgShape X Y Req Resp} (A : AdaptiveIAlg sh O)

/-- **The workspace with the query counter** (`toKindAlg`): the shape's (`AlgShape.CntW`). -/
abbrev CntW (_ : AdaptiveIAlg sh O) : Type := sh.CntW

/-- The registers with a query counter at the shape `s`, as the registers without it and the
counter. -/
def _root_.GordieHowe.Quantum.AlgShape.cntSplit (s : AlgShape X Y Req Resp) :
    DReg s.CntW s.width X Y Req Resp ≃ DReg s.W s.width X Y Req Resp × Fin (s.budget + 2) where
  toFun p := (((p.1.1.work, p.1.2.1, p.1.2.2), p.2), p.1.1.cnt)
  invFun q := (((AlgShape.CntW.mk q.1.1.1 q.2, q.1.1.2.1, q.1.1.2.2)), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The adversary's registers with a query counter, as the registers without it and the
counter (`AlgShape.cntSplit`). -/
abbrev cntSplit : DReg A.CntW A.width X Y Req Resp ≃
    DReg A.W A.width X Y Req Resp × Fin (A.budget + 2) :=
  sh.cntSplit

/-- The query counter at the shape `s` advanced on the branches whose kind `kind` is a query. -/
def _root_.GordieHowe.Quantum.AlgShape.cntShift (s : AlgShape X Y Req Resp) (kind : s.W → Bool) :
    Equiv.Perm (DReg s.CntW s.width X Y Req Resp) :=
  Equiv.prodCongr (Equiv.prodCongr (s.cntWEquiv.permCongr.symm (Equiv.prodShear (Equiv.refl s.W)
    fun w => if kind w then Equiv.refl _ else finRotate _)) (Equiv.refl _)) (Equiv.refl _)

/-- The query counter advanced on the branches whose kind is a query (`AlgShape.cntShift` at `A`'s
kind). -/
abbrev cntShift : Equiv.Perm (DReg A.CntW A.width X Y Req Resp) := sh.cntShift A.kind

/-- At the shape `s` and the kind `kind`, a branch is within the budget unless it asks for a query
slot with the counter at `budget`. -/
def _root_.GordieHowe.Quantum.AlgShape.inBudget (s : AlgShape X Y Req Resp) (kind : s.W → Bool)
    (d : DReg s.CntW s.width X Y Req Resp) : Bool :=
  kind d.workspace.work || decide (d.workspace.cnt ≠ Fin.castSucc (Fin.last s.budget))

/-- A branch is within the budget unless it asks for a query slot with the counter at `budget`
(`AlgShape.inBudget` at `A`'s kind). -/
abbrev inBudget (d : DReg A.CntW A.width X Y Req Resp) : Bool := sh.inBudget A.kind d

@[simp] theorem cntSplit_apply (w : A.W) (c : Fin (A.budget + 2)) (rr : Req × Option Resp)
    (p : Fin A.width → X × Y) :
    A.cntSplit (((AlgShape.CntW.mk w c), rr), p) = (((w, rr), p), c) := rfl

@[simp] theorem cntSplit_symm_apply (w : A.W) (c : Fin (A.budget + 2)) (rr : Req × Option Resp)
    (p : Fin A.width → X × Y) :
    A.cntSplit.symm (((w, rr), p), c) = (((AlgShape.CntW.mk w c), rr), p) := rfl

@[simp] theorem cntShift_apply (w : A.W) (c : Fin (A.budget + 2)) (rr : Req × Option Resp)
    (p : Fin A.width → X × Y) :
    A.cntShift (((AlgShape.CntW.mk w c), rr), p) =
      (((AlgShape.CntW.mk w (if A.kind w then c else finRotate _ c)), rr), p) := by
  cases h : A.kind w <;> simp [cntShift, AlgShape.cntShift, h, Equiv.permCongr_apply]

@[simp] theorem cntShift_symm_apply (w : A.W) (c : Fin (A.budget + 2)) (rr : Req × Option Resp)
    (p : Fin A.width → X × Y) :
    A.cntShift.symm (((AlgShape.CntW.mk w c), rr), p) =
      (((AlgShape.CntW.mk w (if A.kind w then c else (finRotate _).symm c)), rr), p) := by
  rw [Equiv.symm_apply_eq]
  cases h : A.kind w <;> simp [h]

@[simp] theorem inBudget_mk (w : A.W) (c : Fin (A.budget + 2)) (rr : Req × Option Resp)
    (p : Fin A.width → X × Y) :
    A.inBudget (((AlgShape.CntW.mk w c), rr), p) =
      (A.kind w || decide (c ≠ Fin.castSucc (Fin.last A.budget))) := rfl

/-- **The Kraus map `k` with the query counter** at the shape `s`, for the kind `kind` and the
steps `step`: before a slot, `step k`, then the projection onto the branches within the budget and
the counter advanced on the query branches; after the slots, `step k` with the identity on the
counter. Sealed, and of the kind and the steps only; it unfolds through `AlgShape.kindStep_eq`. -/
@[irreducible,
    no_expose] def _root_.GordieHowe.Quantum.AlgShape.kindStep (s : AlgShape X Y Req Resp)
    (kind : s.W → Bool)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (k : StepIdx s.slots s.post) :
    KrausMap s.R (DReg s.CntW s.width X Y Req Resp) (DReg s.CntW s.width X Y Req Resp) :=
  if (k : ℕ) < s.slots then
    ((((step k).tensorId (Fin (s.budget + 2))).reindex s.cntSplit.symm).restrict
      (s.inBudget kind)).permConj (Equiv.refl _) (s.cntShift kind)
  else ((step k).tensorId (Fin (s.budget + 2))).reindex s.cntSplit.symm

theorem _root_.GordieHowe.Quantum.AlgShape.kindStep_eq (s : AlgShape X Y Req Resp)
    (kind : s.W → Bool)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (k : StepIdx s.slots s.post) :
    s.kindStep kind step k = if (k : ℕ) < s.slots then
      ((((step k).tensorId (Fin (s.budget + 2))).reindex s.cntSplit.symm).restrict
        (s.inBudget kind)).permConj (Equiv.refl _) (s.cntShift kind)
    else ((step k).tensorId (Fin (s.budget + 2))).reindex s.cntSplit.symm := by
  unfold AlgShape.kindStep; rfl

/-- **The shape of `toKindAlg` at a shape** `s`: the workspace with the query counter. -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.toKindS (s : AlgShape X Y Req Resp) :
    KindShape X Y Req Resp where
  W := s.CntW
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  R := s.R

/-- **The shape of `toKindAlg`**: the shape's (`AlgShape.toKindS`). -/
abbrev kindS (_ : AdaptiveIAlg sh O) : KindShape X Y Req Resp := sh.toKindS

/-- **The adversary with its query counter** (proof-internal and the definition of the model's
semantics): its workspace carries the number of its query slots so far, started at `0`. The Kraus
map before slot `j` is the adversary's, then the projection onto the branches within the budget
(a branch that asks for one more query slot than `budget` halts), then the counter advanced on the
query branches. The counter takes values in `Fin (budget + 2)`; on every branch it stays at most
`budget` (`AdaptiveIAlg.dilBudget`), and the value `budget + 1` is left free for the
trace-preserving form of the adversary (`AdaptiveIAlg.toTPKindAlg`), where it marks a branch that
has ended. -/
def toKindAlg : KindAlg sh.toKindS O where
  kind w := A.kind w.work
  init := MState.reindex A.cntSplit.symm (A.init.tensorKet 0)
  step := sh.kindStep A.kind A.step
  out w := A.out w.1

/-- **The Kraus map `k` with the counter** (`AlgShape.kindStep`): before a slot, `A`'s, then the
projection onto the branches within the budget and the counter advanced on the query branches;
after the slots, `A`'s with the identity on the counter. -/
theorem toKindAlg_step_eq (k : StepIdx A.slots A.post) :
    A.toKindAlg.step k = if (k : ℕ) < A.slots then
      ((((A.step k).tensorId (Fin (A.budget + 2))).reindex A.cntSplit.symm).restrict
        A.inBudget).permConj (Equiv.refl _) A.cntShift
    else ((A.step k).tensorId (Fin (A.budget + 2))).reindex A.cntSplit.symm :=
  sh.kindStep_eq A.kind A.step k

/-- The initial state of the kind algorithm: `A`'s with the counter at `0`. -/
theorem toKindAlg_init : A.toKindAlg.init = MState.reindex A.cntSplit.symm (A.init.tensorKet 0) :=
  rfl

@[simp] theorem toKindAlg_kind_mk (w : A.W) (c : Fin (A.budget + 2)) :
    A.toKindAlg.kind (AlgShape.CntW.mk w c) = A.kind w := rfl

@[simp] theorem toKindAlg_out_mk (w : A.W) (c : Fin (A.budget + 2)) :
    A.toKindAlg.out (AlgShape.CntW.mk w c) = A.out w := rfl

/-- **The Kraus map before slot `k` with the counter**: `A`'s, then the projection onto the
branches within the budget and the counter advanced on the query branches. -/
theorem toKindAlg_step_of_lt {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots) :
    A.toKindAlg.step k = ((((A.step k).tensorId (Fin (A.budget + 2))).reindex
      A.cntSplit.symm).restrict A.inBudget).permConj (Equiv.refl _) A.cntShift :=
  (A.toKindAlg_step_eq k).trans (if_pos hk)

/-- **The Kraus map before a post batch, or the last one, with the counter**: `A`'s with the
identity on the counter. -/
theorem toKindAlg_step_of_not_lt {k : StepIdx A.slots A.post} (hk : ¬ (k : ℕ) < A.slots) :
    A.toKindAlg.step k = ((A.step k).tensorId (Fin (A.budget + 2))).reindex A.cntSplit.symm :=
  (A.toKindAlg_step_eq k).trans (if_neg hk)

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The composed core algorithm** of an adversary with run-time kinds and a challenger: the
composition with every slot's kind chosen at run time (`KindAlg.composeBoth`) of the adversary with
its query counter. -/
noncomputable abbrev compose (C : Challenger X Y Req Resp) : Alg X Y O :=
  A.toKindAlg.composeBoth C

/-- **The query count of the composition**: `q + width` queries at every slot, of which on each
branch those of the other kind are padded, then `width` queries per post batch. -/
theorem compose_depth (C : Challenger X Y Req Resp) :
    (A.compose C).depth = A.slots * (C.q + A.width) + A.width * A.post :=
  A.toKindAlg.composeBoth_depth C

end AdaptiveIAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {sh : AlgShape X Y Req Resp} (A : AdaptiveIAlg sh O)

/-- The query counter of a workspace of `toKindAlg`. -/
def wcnt (w : A.toKindAlg.W) : ℕ := ((AlgShape.CntW.cnt w : Fin (A.budget + 2)) : ℕ)

@[simp] theorem wcnt_mk (w : A.W) (c : Fin (A.budget + 2)) :
    A.wcnt (AlgShape.CntW.mk w c) = c := rfl

/-- **The Kraus map before slot `k` counts the query slot**: from a state with counter
`c ≤ budget`, its operators send only to states with counter `c + 1 ≤ budget` on the branches whose
kind is a query and `c` on the others (a query branch at `c = budget` is projected away). -/
theorem step_op_eq_zero {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots) {c : ℕ}
    (hc : c ≤ A.budget) (r : A.R) (y x : DReg A.toKindAlg.W A.width X Y Req Resp)
    (hx : A.wcnt x.workspace = c)
    (hy : ¬ (A.wcnt y.workspace = c + (if A.kind y.workspace.work then 0 else 1) ∧
      A.wcnt y.workspace ≤ A.budget)) :
    (A.toKindAlg.step k).op r y x = 0 := by
  obtain ⟨⟨wcy, ry, sy⟩, py⟩ := y
  obtain ⟨w, cy, rfl⟩ := AlgShape.CntW.exists_eq_mk wcy
  obtain ⟨⟨wcx, rx, sx⟩, px⟩ := x
  obtain ⟨w', cx, rfl⟩ := AlgShape.CntW.exists_eq_mk wcx
  simp only [DReg.workspace, wcnt_mk, AlgShape.CntW.work_mk] at hx hy
  rw [toKindAlg_step_of_lt A hk]
  simp only [KrausMap.permConj, KrausMap.restrict, KrausMap.reindex,
    KrausMap.tensorId, Matrix.submatrix_apply, Matrix.diagonal_mul, Equiv.symm_symm,
    Equiv.refl_apply, Matrix.kroneckerMap_apply]
  rw [cntShift_symm_apply]
  change (if A.inBudget (((AlgShape.CntW.mk w (if A.kind w then cy else (finRotate _).symm cy)),
      ry, sy), py) = true then 1 else 0) * ((A.step k).op r _ _ *
    (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ)
      (if A.kind w then cy else (finRotate _).symm cy) cx) = 0
  rw [inBudget_mk]
  cases hkw : A.kind w
  · simp only [hkw, Bool.false_eq_true, ↓reduceIte] at hy ⊢
    by_cases hl : (finRotate (A.budget + 2)).symm cy = Fin.castSucc (Fin.last A.budget)
    · simp [hl]
    · by_cases hne : (finRotate (A.budget + 2)).symm cy = cx
      · exfalso
        apply hy
        have hcx : (cx : ℕ) = c := hx
        have hlt : (cx : ℕ) < A.budget := by
          have h1 : cx ≠ Fin.castSucc (Fin.last A.budget) := hne ▸ hl
          have h2 : (cx : ℕ) ≠ A.budget := fun h => h1 (Fin.ext (by simpa using h))
          omega
        have hnl : cx ≠ Fin.last (A.budget + 1) := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        have h1 := coe_finRotate_of_ne_last hnl
        have hcy : cy = finRotate (A.budget + 2) cx := by rw [← hne, Equiv.apply_symm_apply]
        have h2 : (cy : ℕ) = cx + 1 := by rw [hcy, h1]
        constructor <;> omega
      · exact mul_eq_zero_of_right _ (mul_eq_zero_of_right _ (Matrix.one_apply_ne (by
          exact hne)))
  · simp only [hkw, ↓reduceIte, add_zero] at hy ⊢
    by_cases hne : cy = cx
    · exfalso
      apply hy
      have hcx : (cx : ℕ) = c := hx
      rw [hne]
      exact ⟨hcx, hcx ▸ hc⟩
    · exact mul_eq_zero_of_right _ (mul_eq_zero_of_right _ (Matrix.one_apply_ne (by
        exact hne)))

/-- The initial state of the mixed game of `toKindAlg` has counter `0`. -/
theorem suppIn_mgInit_wcnt : SuppIn {r | A.wcnt r.1.1 = 0} A.toKindAlg.mgInit := by
  intro a b hab
  obtain ⟨⟨wca, ra, sa, la⟩, pa⟩ := a
  obtain ⟨w, ca, rfl⟩ := AlgShape.CntW.exists_eq_mk wca
  obtain ⟨⟨wcb, rb, sb, lb⟩, pb⟩ := b
  obtain ⟨w', cb, rfl⟩ := AlgShape.CntW.exists_eq_mk wcb
  simp only [Set.mem_ofPred_eq, wcnt_mk] at hab
  change (_ * Matrix.single (0 : Fin (A.budget + 2)) 0 (1 : ℂ) ca cb) * _ = 0
  rw [Matrix.single_apply, if_neg, mul_zero, zero_mul]
  rintro ⟨h1, h2⟩
  rcases hab with h | h
  · exact h (by rw [← h1]; rfl)
  · exact h (by rw [← h2]; rfl)

variable [Nonempty X] [AddGroup Y] [Nonempty Y] [DecidableEq O]

/-- `KindAlg.composeBoth_eq_pureGame` in `ℝ`. -/
theorem toReal_compose (C : Challenger X Y Req Resp) (o : O) :
    (((A.compose C).realLaw (Equiv.refl Y)).toOuterMeasure {p | p.out = some o}).toReal =
      (A.toKindAlg.dilate o).acceptProb C.toPureEnv A.toKindAlg.postOp := by
  rw [A.toKindAlg.composeBoth_eq_pureGame C o,
    ENNReal.toReal_ofReal (Distinguisher.acceptProb_nonneg _ _ _)]

end AdaptiveIAlg

end GordieHowe.Quantum
