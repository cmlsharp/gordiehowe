-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignAbsorbInv
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript
public import GordieHowe.Model.Quantum.Interactive.MultiRelayPos
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut

@[expose] public section

/-!
# Absorbing an assigning challenger into the adversary

An adversary `A` plays against an outer challenger `C` whose coins are side coins `s ← σ` and the
coins of a main challenger `C'`, and which answers each request through the relay `G s`
(`AssignRelay`): a classical program that reads the oracle in force, makes one request to `C'`,
and returns the reply and an assignment list (Unruh 2017, ePrint 2017/398, section 2, p. 7), which
`C` appends to the assignments in force (`AssignRelay.RelaysChallenger`). The adversary
`A.absorbAssign (G s) C.Q` plays against `C'` itself, which assigns nothing: it runs the relay's
programs itself, holds the table of the assignments in force, and patches its own queries at the
assigned points with the reprogrammed query of `GordieHowe/Model/Quantum/Core/Reprogram.lean`.

## The construction (`AdaptiveIAlg.absorbAssign`)

1. `A.absorb (sideRelay X Y Req Resp Req' Resp'
    Q)` (`GordieHowe/Model/Quantum/Interactive/Absorb.lean`): `A`'s requests,
   numbered, sent to the explicit relay challenger `AssignRelay.chalD C' G Q`, whose replies reveal
   the outer response, the table of the request's assignments, the main request and the main
   reply; the replies stored in the workspace.
2. `patchTag` (`GordieHowe/Model/Quantum/Interactive/AssignPatch.lean`) with the table of the
   stored replies (`assignTab`, in slot order): each query slot is the reprogrammed query for the
   table (exchange with a clean ancilla on the assigned inputs, query, exchange, add the table
   entry), each request is tagged with the table; the requests go to `AssignRelay.chalT C' G Q`,
   which assigns nothing and reads the oracle through the tags.
3. `relayAdv` (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) with `AssignRelay.relayOf
   G Q`: the relay programs run by the adversary, one main request to `C'` and `qG` classical reads
   per request, the main requests padded with `G.idle`.

The output is `A`'s output with the table of the assignments in force at the end.

## Results

- `absorbAssign_tracePreserving`, `absorbAssign_withinBudget`, `absorbAssign_queries`: the absorbed
  adversary is trace preserving, within its budget, and makes
  `width · (budget + post) = A.width · (A.budget + A.post) + Q · qG + Q · qP` queries: one per
  query slot of `A` (the reprogrammed query makes one query), and `qG` reads and `qP` pad sub-slots
  per answered request; `absorbAssign_queries_of_qP`: `Q · qG` alone for a relay without pad
  sub-slots (one without side reads, `AssignRelay.qP_eq_zero`).
- `absorbAssign_toShape`: the shape of the absorbed adversary is `AlgShape.absorbAssignS` at
  `A`'s shape and the relay's numbers `qG`, `qP`, `qS`.
- `mgRun_absorbAssignP`: the mixed game of the second step against `chalT` at the main coins `c'`
  is `A`'s mixed game against `C` at the coins `c`, placed with clean ancillas, when `C` at `c`
  relays `C'` at `c'` through `G` (`AssignRelay.RelaysChallenger`) and `G`'s assignments are safe
  for `C'` (`AssignRelay.SafeAssign`). `readout_absorbAssignP`: at the placed states the second
  step's output is `A`'s with a table, its outer requests are `A`'s answered requests, and the
  oracle read through the table is `A`'s final oracle in force.
- `toOuterMeasure_eq_sum_absorbAssignP_of_placed` (equality): an event of `A`'s composed
  registers against `C` has the `σ`-average probability of any event of the second step's
  composed registers against `chalT` that agrees with it at the placed states (`placedP`).
- `toOuterMeasure_eq_sum_absorbAssignP` (equality): an event `E` of `A`'s output, answered requests
  and final oracle in force (`assignReadout`) against `C` has the `σ`-average probability of `E` of
  the second step's readout (`patchReadout`) against `chalT`.
- `AssignRelay.exists_of_tabAfter`, `AssignRelay.answerAfter_chalT_eq`,
  `AssignRelay.exists_mainOf_mem_mainReqs`, `tab_absorbAssignP`, `TabOrigin`,
  `toOuterMeasure_eq_sum_absorbAssignP_tab`: at the placed states every entry of the table is an
  entry of the table of a reply in the history (`TabOrigin`), which is the run of the request's
  relay program reading through the request's table; the relay sends that run's main request.
- **`toOuterMeasure_le_absorbAssign`** (the law): the same event has at most the `σ`-average of the
  probability that the output `(o, T)` and history of `A.absorbAssign (G s) C.Q` against `C'` lie
  in `E' s`, when `E' s` holds of `(o, T)` with every history whose main requests are `G.idle` or
  ones the relay program of a request of a tagged history can make, whenever `E` holds of `o`, the
  requests and `reprogT T H` (`himp`). The relay step is the event form of
  `toOuterMeasure_le_relayAdv`, an inequality. `toOuterMeasure_le_absorbAssign_tab` (and
  `QueryBoundedAdversary.assignLaw_le_absorbAssign_tab`): `E' s` need hold only when, besides,
  every entry `T x = some y` of the table is assigned by the run of the relay program of a
  request `p` of `hP` reading the oracle through `p`'s table, at some main replies, whose main
  request is a request of the history.
- `QueryBoundedAdversary.absorbAssign` (a `(t + Q · qG + Q · qP)`-query adversary), `assignLaw`,
  `assignLaw_le_absorbAssign`; `RingSignature.GameAdversary.absorbAssign`.
- `toOuterMeasure_le_of_keepsView`: against a challenger keeping a view `f` of the oracle
  (`Challenger.KeepsView`), an event of the final oracle with the view of `H` gives an event of
  the output and the answered requests alone. `toOuterMeasure_le_of_keepsView_and`: the event
  holds together with `f G = f H` at the final oracle `G`.

Hypotheses on the main challenger beyond the relay condition: it reprograms nothing
(`Challenger.NoAssign`), answers at least `C.Q` requests, and its reply programs do not see the
relay's assignments (`AssignRelay.SafeAssign`; any main challenger without queries,
`SafeAssign.ofNoQuery`). On the relay: at most `qG` reads and exactly one main request on every
path (`AssignRelay.reads_le`, `asks_eq_one`).
-/

open Finset Matrix
open GordieHowe.Quantum.AssignRelay (sideRelay)
open scoped BigOperators ENNReal Kronecker ComplexOrder


namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)

variable (Req' Resp') in
/-- `A` with its requests absorbed through the side relay to `chalD`.

Running time: that of `AdaptiveIAlg.absorb` at the side relay (its paragraph). This running
time is argued here, not proved in Lean. -/
abbrev absorbAssignB :=
  A.absorb (sideRelay X Y Req Resp Req' Resp' Q)

/-- **The table of the assignments revealed in the stored replies**, in slot order. -/
abbrev assignTab (w : A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp')) : X → Option Y :=
  A.storeTab (fun x => x.2.1) w

variable (Req' Resp') in
/-- `A` with its requests absorbed and its queries patched by the table of the stored replies;
its output is `A`'s with the table.

Running time: that of `patchTag` (its paragraph) on `absorbAssignB`, with the table `assignTab`
folded from the `A.slots` stored replies (`storeTab`). This running time is argued here, not
proved in Lean. -/
noncomputable abbrev absorbAssignP :=
  (A.absorbAssignB Req' Resp' Q).patchTag (A.assignTab (Req' := Req') (Resp' := Resp'))
    fun w => (A.out w.work, A.assignTab w)

omit [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [AddGroup Ys] in
variable (Ys) in
/-- **The shape of the absorbed adversary** (`absorbAssign`) of an adversary of shape `s`,
through a relay with `qG` oracle reads, `qP` pad sub-slots and `qS` side reads, answering `Q`
requests: the relayed shape (`AlgShape.relayAdvS`, one main request) of the patched
(`AlgShape.patchTagS`) absorbed (`AlgShape.absorbS`) shape. -/
@[reducible] noncomputable def _root_.GordieHowe.Quantum.AlgShape.absorbAssignS (s : AlgShape X Y Req Resp)
    (qG qP qS : ℕ) : AlgShape X Y Req' Resp' :=
  (s.absorbS (Req' := Req × Fin (Q + 1))
    (Resp' := AssignRelay.RespD X Y Resp Req' Resp')).patchTagS.relayAdvS Ys 1 qG qP qS Q

/-- **The adversary with an assigning challenger absorbed** (module docstring): an adversary of the
main challenger's interface. Its output is `A`'s output with the table of the assignments in force
at the end.

Running time: that of `relayAdv` (its paragraph) on `absorbAssignP`: `A`, the patched queries and,
per answered request, the relay program of `G` with its `qG` reads and one main request. This
running time is argued here, not proved in Lean. -/
noncomputable def absorbAssign :
    AdaptiveIAlg (shA.absorbAssignS (Req' := Req') (Resp' := Resp') Ys Q G.qG G.qP G.qS)
      (O × (X → Option Y)) :=
  (A.absorbAssignP Req' Resp' Q).relayAdv (G.relayOf Q) Q ((A.absorbAssignP Req' Resp' Q).relayOut
      (G.relayOf Q))

/-- **The absorbed adversary is trace preserving.** -/
theorem absorbAssign_tracePreserving : (A.absorbAssign G Q).TracePreserving :=
  relayAdv_tracePreserving _ _ _ _

/-- **The absorbed adversary stays within its budget.** -/
theorem absorbAssign_withinBudget : (A.absorbAssign G Q).WithinBudget :=
  relayAdv_withinBudget _ _ _ _

/-- **The query count of the absorbed adversary**: `A`'s query slots and post batches, each query
pair one query, `qG` reads for each of the `Q` answered requests, and the `qP` pad sub-slots of
each (`MultiRelay.qP`). -/
theorem absorbAssign_queries :
    (A.absorbAssign G Q).width * ((A.absorbAssign G Q).budget + (A.absorbAssign G Q).post) =
      A.width * (A.budget + A.post) + Q * G.qG + Q * G.qP :=
  relayAdv_queries _ _ _ _

/-- **The query count of the absorbed adversary, without pad sub-slots**: `A`'s query slots and
post batches and `qG` reads for each of the `Q` answered requests. -/
theorem absorbAssign_queries_of_qP (hP : G.qP = 0) :
    (A.absorbAssign G Q).width * ((A.absorbAssign G Q).budget + (A.absorbAssign G Q).post) =
      A.width * (A.budget + A.post) + Q * G.qG := by
  rw [absorbAssign_queries, hP, Nat.mul_zero, Nat.add_zero]

/-- **The shape of the absorbed adversary** is `AlgShape.absorbAssignS` at the relay's numbers. -/
theorem absorbAssign_toShape :
    (A.absorbAssign G Q).toShape = A.toShape.absorbAssignS Ys Q G.qG G.qP G.qS :=
  rfl

/-! ### The mixed game -/

instance instDecidableEqGB : DecidableEq (A.absorbAssignB Req' Resp' Q).toKindAlg.G :=
  @instDecidableEqGameReg _ _ _ _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    inferInstance

instance : DecidableEq ((A.absorbAssignB Req' Resp' Q).toKindAlg.G × AncReg X Y A.width) :=
  @instDecidableEqProd _ _ (A.instDecidableEqGB (Req' := Req') (Resp' := Resp') Q) inferInstance

noncomputable instance instDecidableEqWP : DecidableEq (A.absorbAssignP Req' Resp'
    Q).toKindAlg.W :=
  @instDecidableEqProd _ _ (@instDecidableEqProd _ _ (A.absorbAssignB Req' Resp' Q).instDecidableEqW
    inferInstance) inferInstance

noncomputable instance : DecidableEq (A.absorbAssignP Req' Resp' Q).toKindAlg.G :=
  @instDecidableEqGameReg _ _ _ _ _ _ _ (A.instDecidableEqWP (Req' := Req') (Resp' := Resp')
      Q) inferInstance inferInstance
    inferInstance inferInstance


section Run

variable {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'} {c : C.Coins}
  {c' : C'.Coins}

/-- **The mixed game of the patched absorbed adversary against `chalT`** is `A`'s mixed game
against the outer challenger, placed (`placeClean` after the last slot, then `patchPlace` with
clean ancillas). -/
theorem mgRun_absorbAssignP (hrel : G.RelaysChallenger C c C' c') (hS : AssignRelay.SafeAssign C' G)
    (H : X → Y) :
    (A.absorbAssignP Req' Resp' C.Q).toKindAlg.mgRun (AssignRelay.chalT C' G C.Q).toPureEnv (H,
        c') true =
      embed ((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
          Resp'))
          (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
        Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
            C.Q).toPureEnv (H, c')
          (A.slots + A.post)) _root_.id)
        (A.toKindAlg.mgRun C.toPureEnv (H, c) true ⊗ₖ ancMat KindAlg.x₀) := by
  have hR := hrel.relays H A.slots
  have hinj : ∀ k, Function.Injective ((sideRelay X Y Req Resp Req' Resp' C.Q).route k) :=
    AssignRelay.sideRelay_route_injective C.Q
  have hT : ∀ (L : LogReg (Req × Fin (C.Q + 1)) A.slots) (k : ℕ), k ≤ A.slots →
      G.tabAfter C.Q H c' (requestsBefore L k) = foldUpTo (fun i =>
        ((AssignRelay.chalD C' G C.Q).toPureEnv.answer (H, c') L i).elim (fun _ => none)
          fun x => x.2.1) k :=
    fun L k hk => AssignRelay.tabAfter_eq_foldUpTo C' G C.Q H c' L k hk
  rw [AdaptiveIAlg.mgRun_patchTag (A.absorbAssignB Req' Resp' C.Q) _ _ (G.tabAfter C.Q H c')
      (AssignRelay.chalT C' G C.Q).toPureEnv (H, c') (AssignRelay.chalD C' G C.Q).toPureEnv (H, c')
      (fun lg k => AssignRelay.answer_chalT_augLogs C.Q hS H c' lg k)
      (fun lg => AssignRelay.oracle_chalD C.Q hS H c' lg)
      (fun k => A.suppIn_patchInv_absorb (sideRelay X Y Req Resp Req' Resp' C.Q) _ (H, c')
          C.toPureEnv (H, c) _ _ hT hR
        hinj k)
      (fun b => A.suppIn_patchInv_absorb_post (sideRelay X Y Req Resp Req' Resp' C.Q) _ (H, c')
          C.toPureEnv (H, c) _ _ hT
        hR hinj b),
    A.mgRun_absorb (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G C.Q).toPureEnv
      ((H, c') : (X → Y) × (AssignRelay.chalD C' G C.Q).Coins) C.toPureEnv (H, c) hR hinj,
    embed_kronecker,
    embed_embed]
  rfl

/-- **The patched absorbed adversary against `chalT` is bounded by the absorbed adversary against
`C'`** (`toOuterMeasure_le_relayAdv_budget` at `absorbAssign`), for events `P` and `P'` with `P'`
holding on the placed states within budget where `P` holds. Stated at a free relay `G`, so that the
shape of `absorbAssign` is compared with that of its `relayAdv` through the coin sums only. -/
theorem toOuterMeasure_chalT_le_absorbAssign_budget (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)
    (Q : ℕ) (hF : (G.relayOf Q).RelaysChallenger (AssignRelay.chalT C' G Q) C' id) (H : X → Y)
    (P : (A.absorbAssignP Req' Resp' Q).toKindAlg.CW (AssignRelay.chalT C' G Q) → Prop)
    (P' : (A.absorbAssign G Q).toKindAlg.CW C' → Prop)
    (himp : ∀ c' y,
      y ∈ ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.dilSet
        {r | P ((A.absorbAssignP Req' Resp' Q).toKindAlg.emb (AssignRelay.chalT C' G Q) H c'
          (A.absorbAssignP Req' Resp' Q).slots r).1} →
      queriesBefore (embR (A.absorbAssignP Req' Resp' Q).post true y).1.2.2.2
        (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.slots +
          (A.absorbAssignP Req' Resp' Q).post) ≤
        (A.absorbAssignP Req' Resp' Q).budget + (A.absorbAssignP Req' Resp' Q).post →
      P' ((A.absorbAssignP Req' Resp' Q).relayPlace (G.relayOf Q)
        (AssignRelay.chalT C' G Q).Q
        ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) C' H c' y)) :
    (((A.absorbAssignP Req' Resp' Q).toKindAlg.composeBothOut (AssignRelay.chalT C' G Q)
        id).outLaw H).toOuterMeasure {x | ∃ v ∈ x, P v} ≤
      (((A.absorbAssign G Q).toKindAlg.composeBothOut C' id).outLaw H).toOuterMeasure
        {x | ∃ v ∈ x, P' v} := by
  classical
  refine le_of_le_of_eq ((A.absorbAssignP Req' Resp' Q).toOuterMeasure_le_relayAdv_budget
    (G.relayOf Q) ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))
    (AssignRelay.chalT C' G Q) C' id hF H P P' himp) ?_
  rw [@KindAlg.toOuterMeasure_outLaw_composeBothOut_id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ((A.absorbAssignP Req' Resp' Q).relayAdv (G.relayOf Q) (AssignRelay.chalT C' G Q).Q
        ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))).toKindAlg C' H P'
      fun _ => Classical.propDecidable _, KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
  refine congrArg ENNReal.ofReal (Finset.sum_congr rfl fun c _ => ?_)
  refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
  rfl

end Run

end AdaptiveIAlg

/-! ### Diagonals of placed product states -/

section Diag

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] {n : ℕ}

open scoped ComplexOrder in
theorem ancMat_diag_im (x₀ : X) (a : AncReg X Y n) : (ancMat (Y := Y) x₀ a a).im = 0 :=
  ((Complex.nonneg_iff.1 ((ancState (Y := Y) (n := n) x₀).posSemidef.diag_nonneg (i := a))).2).symm

theorem sum_ancMat_diag_re (x₀ : X) : ∑ a, (ancMat (Y := Y) (n := n) x₀ a a).re = 1 := by
  have h := congrArg Complex.re (trace_ancMat (Y := Y) (n := n) x₀)
  rw [Matrix.trace, Complex.re_sum] at h
  simpa using h

/-- **The diagonal of a placed product with clean ancillas**, summed against a function that does
not read the ancillas, is the diagonal of the first factor. -/
theorem sum_diag_embed_kronecker_ancMat {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (x₀ : X) (e : κ × AncReg X Y n → ι) (he : Function.Injective e) (σ : Matrix κ κ ℂ)
    (g : ι → ℝ) (f : κ → ℝ) (hg : ∀ k a, g (e (k, a)) = f k) :
    ∑ i, g i * (embed e (σ ⊗ₖ ancMat x₀) i i).re = ∑ k, f k * (σ k k).re := by
  rw [embed_diag_of_injective he, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hg, kroneckerMap_apply, Complex.mul_re, ancMat_diag_im, mul_zero, sub_zero]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_ancMat_diag_re, mul_one]

end Diag

/-! ### The origin of the table -/

namespace AssignRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y]
  [Inhabited Req'] (C' : Challenger X Y Req' Resp') (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)
  (Q : ℕ)

open GordieHowe.OracleProg

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
/-- **The tagged requests of a prefix are a prefix of the tagged requests.** -/
theorem augList_prefix {R T : Type} (T₁ : List R → T) {rs rs' : List R} (h : rs <+: rs') :
    augList T₁ rs <+: augList T₁ rs' := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t r ih =>
    rw [← List.append_assoc, augList_append_singleton]
    exact ih.trans (List.prefix_append _ _)

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
/-- **A tagged request among the first `n`** is a request `r` of `rs` tagged with `T₁` of the
requests `pre` before it, fewer than `n` of them. -/
theorem exists_of_mem_take_augList {R T : Type} (T₁ : List R → T) (n : ℕ) (rs : List R)
    (p : R × T) (hp : p ∈ (augList T₁ rs).take n) :
    ∃ pre r, pre ++ [r] <+: rs ∧ pre.length < n ∧ p = (r, T₁ pre) := by
  induction rs using List.reverseRecOn with
  | nil => simp [augList] at hp
  | append_singleton rs r ih =>
    rw [augList_append_singleton] at hp
    by_cases h : rs.length < n
    · rw [List.take_of_length_le (by simp; omega), List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · obtain ⟨pre, r', h1, h2, h3⟩ :=
          ih (by rw [List.take_of_length_le (by simp; omega)]; exact hp)
        exact ⟨pre, r', h1.trans (List.prefix_append _ _), h2, h3⟩
      · exact ⟨rs, r, List.prefix_refl _, h, rfl⟩
    · rw [List.take_append_of_le_length (by simp; omega)] at hp
      obtain ⟨pre, r', h1, h2, h3⟩ := ih hp
      exact ⟨pre, r', h1.trans (List.prefix_append _ _), h2, h3⟩

/-- **The relay sends the main request of each of the first `Q` requests**: for a request `req`
after the requests `pre`, both within the first `Q` requests of `rs`, the main requests of `rs`
contain the program's main request at some main replies. -/
theorem exists_mainOf_mem_mainReqs (ansM : List Req' → Req' → Option Resp') (H : X → Y)
    {pre rs : List ((Req × Fin (Q + 1)) × (X → Option Y))}
    {req : (Req × Fin (Q + 1)) × (X → Option Y)} (hp : pre ++ [req] <+: rs) (hl : pre.length < Q) :
    ∃ m, G.mainOf req.2 H m req.1.2 req.1.1 ∈ (relayOf G Q).mainReqs Q ansM H rs := by
  refine ⟨ansM ((relayOf G Q).mainReqs Q ansM H pre), ((relayOf G Q).mainReqs_prefix Q ansM H
    hp).subset ?_⟩
  rw [(relayOf G Q).mainReqs_append]
  simp only [hl, ↓reduceIte, filterMap_runEntries_relayOf, G.filterMap_eq_mainOf]
  exact List.mem_append_right _ (List.mem_singleton_self _)

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [AddGroup Y]
  [Inhabited Req'] in
/-- **The reply of `chalT` within its first `Q` requests** is the record of the program reading
through the request's table, at some main replies. -/
theorem answerAfter_chalT_eq (H : X → Y) (c' : C'.Coins)
    (pre : List ((Req × Fin (Q + 1)) × (X → Option Y)))
    (req : (Req × Fin (Q + 1)) × (X → Option Y)) (hl : pre.length < Q) :
    ∃ m, (chalT C' G Q).toPureEnv.answerAfter (H, c') pre req =
      some (recordOf G.idle
        ((recMain req.2 (G.elimProg req.2 req.1.2 req.1.1)).run (combineAns H m))) := by
  obtain ⟨hb, ha, -⟩ := (noAssign_chalT C' G Q).oracleIn H c' pre
  rw [Challenger.answerAfter_toPureEnv_of_lt _ _ _ _ hl, chalT_respond, run_mapOutput, relayProg,
    run_lower, hb, ha]
  exact ⟨_, rfl⟩

variable {C' G} (hS : SafeAssign C' G)

include hS in
/-- **Every entry of the table of `chalD`'s assignments comes from a reply of `chalT`**: an entry
of the table after the requests `rs` is an entry of the table of a reply in `chalT`'s history along
the first `Q` tagged requests. -/
theorem exists_of_tabAfter (H : X → Y) (c' : C'.Coins) (rs : List (Req × Fin (Q + 1))) (x : X)
    (y : Y) (hxy : G.tabAfter Q H c' rs x = some y) :
    ∃ e ∈ histAlong ((chalT C' G Q).toPureEnv.answerAfter (H, c'))
        ((augList (G.tabAfter Q H c') rs).take Q), ∃ d ∈ e.response, d.2.1 x = some y := by
  induction rs using List.reverseRecOn with
  | nil => simp [tabAfter, Env.oracleIn, Challenger.toPureEnv, lastAssign] at hxy
  | append_singleton rs r ih =>
    by_cases hlt : rs.length < Q
    · have hL : (augList (G.tabAfter Q H c') (rs ++ [r])).take Q =
          augList (G.tabAfter Q H c') rs ++ [(r, G.tabAfter Q H c' rs)] := by
        rw [augList_append_singleton, List.take_of_length_le (by simp; omega)]
      have hL' : (augList (G.tabAfter Q H c') rs).take Q = augList (G.tabAfter Q H c') rs :=
        List.take_of_length_le (by simp; omega)
      rw [hL, histAlong_append_singleton]
      rw [hL'] at ih
      have ht : G.tabAfter Q H c' (rs ++ [r]) = overT (G.tabAfter Q H c' rs)
          (lastAssign ((relayProg C' G c' ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist
            (fun _ => none)
            (histTab ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist) r.2 r.1).run
            (((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).base.reprogram
              ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).ass)).1.assignments) := by
        rw [tabAfter, Env.oracleIn_append_singleton,
          Challenger.update_toPureEnv_of_lt _ _ _ _ hlt]
        simp only [chalD_respond, run_mapOutput]
        rw [lastAssign_append]
        rfl
      rw [ht] at hxy
      simp only [overT] at hxy
      rcases h2 : lastAssign ((relayProg C' G c' ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist
            (fun _ => none)
            (histTab ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist) r.2 r.1).run
            (((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).base.reprogram
              ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).ass)).1.assignments x with _ | y'
      · rw [h2, Option.none_or] at hxy
        obtain ⟨e, he, hd⟩ := ih hxy
        exact ⟨e, List.mem_append_left _ he, hd⟩
      · rw [h2, Option.some_or] at hxy
        cases hxy
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        refine ⟨recordOf G.idle ((relayProg C' G c' ((chalD C' G Q).toPureEnv.oracleIn (H, c')
          rs).hist (fun _ => none)
            (histTab ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist) r.2 r.1).run
            (((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).base.reprogram
              ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).ass)), ?_, h2⟩
        change (chalT C' G Q).toPureEnv.answerAfter (H, c') (augList (G.tabAfter Q H c') rs)
          (r, G.tabAfter Q H c' rs) = _
        rw [G.answerAfter_chalT_chalD Q hS, Challenger.answerAfter_toPureEnv_of_lt _ _ _ _ hlt,
          chalD_respond, run_mapOutput]
    · have ht : G.tabAfter Q H c' (rs ++ [r]) = G.tabAfter Q H c' rs := by
        rw [tabAfter, Env.oracleIn_append_singleton,
          Challenger.update_toPureEnv_of_le _ _ _ _ (not_lt.1 hlt)]
        rfl
      have hL : (augList (G.tabAfter Q H c') (rs ++ [r])).take Q =
          (augList (G.tabAfter Q H c') rs).take Q := by
        rw [augList_append_singleton, List.take_append_of_le_length (by simp; omega)]
      rw [hL]
      rw [ht] at hxy
      exact ih hxy

end AssignRelay

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
theorem map_fst_augList {R T : Type} (T₁ : List R → T) (l : List R) :
    (AssignRelay.augList T₁ l).map Prod.fst = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih => simp [AssignRelay.augList_append_singleton, ih]

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
theorem map_fst_relayList_sideRelay (Q : ℕ) (rs : List Req) :
    ((sideRelay X Y Req Resp Req' Resp' Q).relayList rs).map Prod.fst = rs := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [SideRelay.relayList_append_singleton, List.map_append, ih]
    rfl

variable {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'} {c : C.Coins}
  {c' : C'.Coins}

/-- **The readout of the patched absorbed adversary at a placed state is the adversary's**: its
output is the adversary's output with a table, the outer requests of its answered history are the
adversary's answered requests, and the oracle read through the table is the adversary's final
oracle in force. -/
theorem readout_absorbAssignP (hrel : G.RelaysChallenger C c C' c')
    (hS : AssignRelay.SafeAssign C' G)
    (H : X → Y) (r : A.toKindAlg.G) (a : AncReg X Y A.width) :
    (((A.absorbAssignP Req' Resp' C.Q).output (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1).1,
      ((((A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1).map HistoryEntry.request).map
        fun p => p.1.1),
      reprogT ((A.absorbAssignP Req' Resp' C.Q).output (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1).2 H) =
    (A.output C (A.toKindAlg.emb C H c A.slots r).1,
      (A.history C (A.toKindAlg.emb C H c A.slots r).1).map HistoryEntry.request,
      H.reprogram (A.toKindAlg.postAss C (A.toKindAlg.emb C H c A.slots r).1.chal)) := by
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  change LogReg Req A.slots at lg
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only
    rw [map_request_history, map_request_history]
    change ((requests (augLogs (G.tabAfter C.Q H c') ((sideRelay X Y Req Resp Req' Resp' C.Q).logs
        lg))).take C.Q).map
      (fun p => p.1.1) = (requests lg).take C.Q
    rw [requests, AssignRelay.requestsBefore_augLogs_eq, ← requests, SideRelay.requests_logs]
    have hm : (AssignRelay.augList (G.tabAfter C.Q H c') ((sideRelay X Y Req Resp Req' Resp'
        C.Q).relayList
        (requests lg))).map (fun p => p.1.1) = requests lg := by
      rw [show (fun p : (Req × Fin (C.Q + 1)) × (X → Option Y) => p.1.1) =
        Prod.fst ∘ Prod.fst from rfl, ← List.map_map, map_fst_augList, map_fst_relayList_sideRelay]
    rw [List.map_take, hm]
  · simp only
    have hR := hrel.relays H A.slots
    refine Eq.trans ?_ (A.toKindAlg.postAss_eq C H c _).symm
    change reprogT (A.storeTab (fun x => x.2.1)
      ⟨w, rq, rs, lg, A.storeBelow (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
          C.Q).toPureEnv (H, c')
        (A.slots + A.post) lg⟩) H = C.toPureEnv.oracle (H, c) lg
    rw [A.storeTab_storeBelow, hR.oracle_eq lg, AssignRelay.oracle_chalD C.Q hS H c',
      (AssignRelay.noAssign_chalT C' G C.Q).oracle_eq H c', requests,
      AssignRelay.tabAfter_eq_foldUpTo C' G C.Q H c' _ A.slots le_rfl]
    congr 1
    simp only [foldUpTo]
    rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]

/-- **The table of the patched absorbed adversary at a placed state comes from its replies**: every
entry of the table it outputs is an entry of the table of a reply in its history. -/
theorem tab_absorbAssignP (hS : AssignRelay.SafeAssign C' G)
    (H : X → Y) (r : A.toKindAlg.G) (a : AncReg X Y A.width) (x : X) (y : Y)
    (hxy : ((A.absorbAssignP Req' Resp' C.Q).output (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1).2 x = some y) :
    ∃ e ∈ (A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1,
      ∃ d ∈ e.response, d.2.1 x = some y := by
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  change LogReg Req A.slots at lg
  change A.storeTab (fun x => x.2.1)
    ⟨w, rq, rs, lg, A.storeBelow (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
        C.Q).toPureEnv (H, c')
      (A.slots + A.post) lg⟩ x = some y at hxy
  rw [A.storeTab_storeBelow] at hxy
  have hT : foldUpTo (fun i => ((AssignRelay.chalD C' G C.Q).toPureEnv.answer (H, c')
      ((sideRelay X Y Req Resp Req' Resp' C.Q).logs
          lg) i).elim (fun _ => none) fun x => x.2.1) (A.slots + A.post) =
      G.tabAfter C.Q H c' (requests ((sideRelay X Y Req Resp Req' Resp' C.Q).logs lg)) := by
    rw [requests, AssignRelay.tabAfter_eq_foldUpTo C' G C.Q H c' _ A.slots le_rfl]
    simp only [foldUpTo]
    rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  rw [hT] at hxy
  obtain ⟨e, he, hd⟩ := AssignRelay.exists_of_tabAfter C.Q hS H c' _ x y hxy
  refine ⟨e, ?_, hd⟩
  unfold AdaptiveIAlg.history
  erw [KindAlg.history_stateAt_emb]
  change e ∈ histAlong _ ((requests (augLogs (G.tabAfter C.Q H c')
    ((sideRelay X Y Req Resp Req' Resp' C.Q).logs lg))).take C.Q)
  rw [requests, AssignRelay.requestsBefore_augLogs_eq, ← requests]
  exact he

/-- **The tables of the requests of the patched absorbed adversary at a placed state come from
its replies**: every entry of the table of a request in its history is an entry of the table of
a reply in its history. -/
theorem tabReq_absorbAssignP (hS : AssignRelay.SafeAssign C' G)
    (H : X → Y) (r : A.toKindAlg.G) (a : AncReg X Y A.width) :
    ∀ e ∈ (A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1, ∀ x y, e.request.2 x = some y →
      ∃ e' ∈ (A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' G C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
          (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' :=
              Resp'))
            (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
            Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
                C.Q).toPureEnv (H, c')
              (A.slots + A.post)) _root_.id) (r, a))).1,
        ∃ d ∈ e'.response, d.2.1 x = some y := by
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  change LogReg Req A.slots at lg
  unfold AdaptiveIAlg.history
  erw [KindAlg.history_stateAt_emb]
  change ∀ e ∈ histAlong _ ((requests (augLogs (G.tabAfter C.Q H c')
    ((sideRelay X Y Req Resp Req' Resp' C.Q).logs lg))).take C.Q), _
  rw [requests, AssignRelay.requestsBefore_augLogs_eq, ← requests]
  intro e he x y hxy
  obtain ⟨pre', req, hp', rfl⟩ := exists_of_mem_histAlong _ _ _ he
  obtain ⟨pre, r', hpre, -, hreq⟩ := AssignRelay.exists_of_mem_take_augList _ C.Q _ req
    (hp'.subset (List.mem_append_right _ (List.mem_singleton_self _)))
  rw [hreq] at hxy
  obtain ⟨e', he', hd⟩ := AssignRelay.exists_of_tabAfter C.Q hS H c' _ x y hxy
  refine ⟨e', ?_, hd⟩
  have hm := (histAlong_prefix _ (((AssignRelay.augList_prefix _
    ((List.prefix_append _ _).trans hpre)).take C.Q))).subset he'
  change e' ∈ histAlong _ ((requests (augLogs (G.tabAfter C.Q H c')
    ((sideRelay X Y Req Resp Req' Resp' C.Q).logs lg))).take C.Q)
  rw [requests, AssignRelay.requestsBefore_augLogs_eq, ← requests]
  exact hm

/-- **The readout of `A` against the outer challenger**: its output, its answered requests, and the
oracle in force at the end. -/
noncomputable def assignReadout (C : Challenger X Y Req Resp) (H : X → Y) (v : A.toKindAlg.CW C) :
    O × List Req × (X → Y) :=
  (A.output C v, (A.history C v).map HistoryEntry.request,
    H.reprogram (A.toKindAlg.postAss C v.chal))

variable (Q : ℕ) in
/-- **The readout of the patched absorbed adversary against `chalT`**: `A`'s output, the outer
requests of its answered history, and the oracle read through its table. -/
noncomputable def patchReadout (C' : Challenger X Y Req' Resp') (H : X → Y)
    (v : (A.absorbAssignP Req' Resp' Q).toKindAlg.CW (AssignRelay.chalT C' G Q)) : O × List Req × (X
        → Y) :=
  (((A.absorbAssignP Req' Resp' Q).output (AssignRelay.chalT C' G Q) v).1,
    (((A.absorbAssignP Req' Resp' Q).history (AssignRelay.chalT C' G Q) v).map
        HistoryEntry.request).map
      (fun p => p.1.1),
    reprogT ((A.absorbAssignP Req' Resp' Q).output (AssignRelay.chalT C' G Q) v).2 H)

/-- **The placed state of the patched absorbed adversary** at the main coins `c'`, the register
`r` of `A`'s mixed game and the ancilla `a`: the state at which `mgRun_absorbAssignP` places `A`'s
run. -/
noncomputable abbrev placedP (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)
    (C' : Challenger X Y Req' Resp')
    (H : X → Y) (c' : C'.Coins) (r : A.toKindAlg.G) (a : AncReg X Y A.width) :
    (A.absorbAssignP Req' Resp' C.Q).toKindAlg.CW (AssignRelay.chalT C' G C.Q) :=
  ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' G C.Q) H c' A.slots
      (((A.absorbAssignB Req' Resp' C.Q).patchPlace (A.assignTab (Req' := Req') (Resp' := Resp'))
        (fun w => (A.out w.work, A.assignTab w)) (fun _ _ => none) (G.tabAfter C.Q H c') ∘
        Prod.map (A.placeClean (sideRelay X Y Req Resp Req' Resp' C.Q) (AssignRelay.chalD C' G
            C.Q).toPureEnv (H, c')
          (A.slots + A.post)) _root_.id) (r, a))).1

/-- **Absorbing the assigning challenger, up to the relay of the programs, at events agreeing at
the placed states**: an event `P₀` of `A`'s composed registers against the outer challenger has the
`σ`-average probability of an event `P s` of the patched absorbed adversary's composed registers
against `chalT`, when at every placed state (`placedP`) `P s` holds exactly when `P₀` holds at
`A`'s registers (`hP`). Hypotheses: the outer coins are the side coins and the main coins
(`hcoins`); the outer challenger relays the main challenger through `G s` (`hrel`); the relay's
assignments are safe for the main challenger (`hS`). -/
theorem toOuterMeasure_eq_sum_absorbAssignP_of_placed {S : Type} [Fintype S] (σ : PMF S)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (H : X → Y) (P₀ : A.toKindAlg.CW C → Prop)
    (P : ∀ s, (A.absorbAssignP Req' Resp' C.Q).toKindAlg.CW (AssignRelay.chalT C' (G s) C.Q) → Prop)
    (hP : ∀ s c' r a, P s (A.placedP (C := C) (G s) C' H c' r a) ↔
      P₀ (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1) :
    ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {x | ∃ v ∈ x, P₀ v} =
      ∑ s, σ s * (((A.absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
        (AssignRelay.chalT C' (G s) C.Q) id).outLaw H).toOuterMeasure
          {x | ∃ v ∈ x, P s v} := by
  classical
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  have hdiag : ∀ (c : C.Coins) (r : A.toKindAlg.G),
      0 ≤ (A.toKindAlg.mgRun C.toPureEnv (H, c) true r r).re := fun c r =>
    (Complex.nonneg_iff.1 ((Circuit.posSemidef_run _ _ A.toKindAlg.mgInitM.posSemidef).diag_nonneg
      (i := r))).1
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
  have hs : ∀ s, (((A.absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
      (AssignRelay.chalT C' (G s) C.Q) id).outLaw H).toOuterMeasure
        {x | ∃ v ∈ x, P s v} =
      ENNReal.ofReal (∑ c', (C'.coins c').toReal * ∑ r : A.toKindAlg.G,
        if P₀ (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1
        then (A.toKindAlg.mgRun C.toPureEnv (H, e.symm (s, c')) true r r).re else 0) := by
    intro s
    rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
    congr 1
    refine Finset.sum_congr rfl fun c' _ => ?_
    congr 1
    rw [Finset.sum_congr rfl fun r' _ => hite _ _, Finset.sum_congr rfl fun r _ => hite _ _]
    change ∑ r', _ * ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.mgRun
      (AssignRelay.chalT C' (G s) C.Q).toPureEnv (H, c') true r' r').re = _
    rw [A.mgRun_absorbAssignP (G s) (hrel s c') (hS s) H]
    refine sum_diag_embed_kronecker_ancMat _ _ ?_ _ _ _ fun r a => ?_
    · intro p q h
      have h' := ((A.absorbAssignB Req' Resp' C.Q).patchPlace_injective _ _ _ _) h
      simp only [Prod.map, Prod.mk.injEq] at h'
      exact Prod.ext (A.placeClean_injective _ _ _ _ h'.1) h'.2
    · exact if_congr (hP s c' r a) rfl rfl
  simp only [hs]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ => Finset.sum_nonneg fun c' _ => mul_nonneg
    ENNReal.toReal_nonneg
        (Finset.sum_nonneg fun r _ => by split_ifs; exact hdiag _ r; exact le_rfl)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [hcoins, ENNReal.toReal_mul, mul_assoc]
  rw [← Finset.mul_sum, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top σ s)]

/-- **Absorbing the assigning challenger, up to the relay of the programs** (the first two steps of
the construction): an event of `A`'s output, answered requests and final oracle against the outer
challenger has the `σ`-average probability of the same event of the patched absorbed adversary's
readout against `chalT` (the oracle in force read through its table). Hypotheses: the outer coins
are the side coins and the main coins (`hcoins`); the outer challenger relays the main challenger
through `G s` (`hrel`); the relay's assignments are safe for the main challenger (`hS`). -/
theorem toOuterMeasure_eq_sum_absorbAssignP {S : Type} [Fintype S] (σ : PMF S)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (H : X → Y) (E : O × List Req × (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} =
      ∑ s, σ s * (((A.absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
        (AssignRelay.chalT C' (G s) C.Q) (A.patchReadout (G s) C.Q C' H)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E p} := by
  simp only [KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ (A.patchReadout _ C.Q C' H),
    KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ (A.assignReadout C H)]
  exact A.toOuterMeasure_eq_sum_absorbAssignP_of_placed σ G e hcoins hrel hS H _ _
    fun s c' r a => Iff.of_eq (congrArg E (A.readout_absorbAssignP (G s) (hrel s c') (hS s) H r a))

/-- **Every entry of the output table and of the requests' tables comes from a reply in the
history** (the readout `v` of the
patched absorbed adversary against `chalT`). -/
def TabOrigin {Q : ℕ} (v : (A.absorbAssignP Req' Resp' Q).toKindAlg.CW (AssignRelay.chalT C' G Q)) :
    Prop :=
  (∀ x y, ((A.absorbAssignP Req' Resp' Q).output (AssignRelay.chalT C' G Q) v).2 x = some y →
    ∃ e ∈ (A.absorbAssignP Req' Resp' Q).history (AssignRelay.chalT C' G Q) v,
      ∃ d ∈ e.response, d.2.1 x = some y) ∧
  ∀ e ∈ (A.absorbAssignP Req' Resp' Q).history (AssignRelay.chalT C' G
      Q) v, ∀ x y, e.request.2 x = some y →
    ∃ e' ∈ (A.absorbAssignP Req' Resp' Q).history (AssignRelay.chalT C' G Q) v,
      ∃ d ∈ e'.response, d.2.1 x = some y

/-- **`toOuterMeasure_eq_sum_absorbAssignP` with the origin of the table**: the same, with
`TabOrigin` at the patched absorbed adversary's state. -/
theorem toOuterMeasure_eq_sum_absorbAssignP_tab {S : Type} [Fintype S] (σ : PMF S)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (H : X → Y) (E : O × List Req × (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} =
      ∑ s, σ s * (((A.absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
        (AssignRelay.chalT C' (G s) C.Q) id).outLaw H).toOuterMeasure
          {x | ∃ v ∈ x, E (A.patchReadout (G s) C.Q C' H v) ∧ A.TabOrigin (G s) v} :=
  (KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ _ H E).trans
    (A.toOuterMeasure_eq_sum_absorbAssignP_of_placed σ G e hcoins hrel hS H _ _ fun s c' r a =>
      (and_iff_left ⟨A.tab_absorbAssignP (G s) (C := C) (c' := c') (hS s) H r a,
        A.tabReq_absorbAssignP (G s) (C := C) (c' := c') (hS s) H r a⟩).trans
        (Iff.of_eq (congrArg E (A.readout_absorbAssignP (G s) (hrel s c') (hS s) H r a))))

/-- **The relay step of the absorption, with the origin of the table**: for one relay `G`, the
patched absorbed adversary against `chalT` has, on the event `E` of its readout with the table's
origin (`TabOrigin`), at most the probability that the absorbed adversary `A.absorbAssign G Q`
against `C'` outputs `(o, T)` with a history in `E''`, under the hypothesis `himp` of
`toOuterMeasure_le_absorbAssign_tab`. -/
theorem toOuterMeasure_chalT_le_absorbAssign (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
    (hNA : C'.NoAssign) (hQ : Q ≤ C'.Q) (H : X → Y) (E : O × List Req × (X → Y) → Prop)
    (E'' : (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      G.Explains Q H T hP hist' →
      E'' ((o, T), hist')) :
    (((A.absorbAssignP Req' Resp' Q).toKindAlg.composeBothOut (AssignRelay.chalT C' G Q) id).outLaw
        H).toOuterMeasure {x | ∃ v ∈ x, E (A.patchReadout G Q C' H v) ∧ A.TabOrigin G v} ≤
      (((A.absorbAssign G Q).toKindAlg.composeBothOut C' fun v =>
        ((A.absorbAssign G Q).output C' v, (A.absorbAssign G Q).history C' v)).outLaw
          H).toOuterMeasure {x | ∃ p ∈ x, E'' p} := by
  conv_rhs => rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine A.toOuterMeasure_chalT_le_absorbAssign_budget G Q
    (G.relaysChallenger_relayOf C' Q hNA hQ) H _ _ ?_
  intro c' y hy hb
  have ho := (A.absorbAssignP Req' Resp' Q).output_relayPlace (G.relayOf Q)
    (AssignRelay.chalT C' G Q).Q C' H c' y (AssignRelay.chalT C' G Q) (id c')
  have hh := (A.absorbAssignP Req' Resp' Q).history_relayPlace (G.relayOf Q)
    ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) (AssignRelay.chalT C' G Q)
    (id c') C' H c' y
  obtain ⟨k, hk⟩ := (A.absorbAssignP Req' Resp' Q).history_relayPlace_eq (G.relayOf Q)
    ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) (AssignRelay.chalT C' G Q)
    C' H c' y hb
  have hA := (A.absorbAssignP Req' Resp' Q).history_emb_relG (AssignRelay.chalT C' G Q) H c' y
  have origin : ∀ x yv, (∃ en ∈ (A.absorbAssignP Req' Resp' Q).history
      (AssignRelay.chalT C' G Q) ((A.absorbAssignP Req' Resp' Q).toKindAlg.emb
        (AssignRelay.chalT C' G Q) H (id c') (A.absorbAssignP Req' Resp' Q).slots
        (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.relG y).1.1).1,
      ∃ d ∈ en.response, d.2.1 x = some yv) →
      ∃ p ∈ ((A.absorbAssignP Req' Resp' Q).history (AssignRelay.chalT C' G Q)
        ((A.absorbAssignP Req' Resp' Q).toKindAlg.emb (AssignRelay.chalT C' G Q) H (id c')
          (A.absorbAssignP Req' Resp' Q).slots
          (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.relG
              y).1.1).1).map HistoryEntry.request,
        ∃ m, lastAssign ((G.elimProg p.2 p.1.2 p.1.1).run
          (OracleProg.combineAns (reprogT p.2 H) m)).assignments x = some yv ∧
        ∃ e' ∈ ((A.absorbAssignP Req' Resp' Q).relayAdv (G.relayOf Q)
          (AssignRelay.chalT C' G Q).Q
          ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))).history C'
          ((A.absorbAssignP Req' Resp' Q).relayPlace (G.relayOf Q)
            (AssignRelay.chalT C' G Q).Q
            ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) C' H c' y),
          e'.request = G.mainOf p.2 H m p.1.2 p.1.1 := by
    rintro x yv ⟨en, hen, d, hd, hdx⟩
    have hen' := hen
    change en ∈ (A.absorbAssignP Req' Resp' Q).history (AssignRelay.chalT C' G Q) _ at hen'
    erw [hA] at hen'
    obtain ⟨pre, req, hpre, rfl⟩ := exists_of_mem_histAlong _ _ _ hen'
    have hlen : pre.length < Q := by
      by_contra hl
      rw [Challenger.answerAfter_toPureEnv_of_le _ _ _ _ (not_lt.1 hl)] at hd
      cases hd
    obtain ⟨m, hm⟩ := G.answerAfter_chalT_eq C' Q H c' pre req hlen
    rw [hm, Option.mem_def, Option.some.injEq] at hd
    subst hd
    refine ⟨req, List.mem_map_of_mem hen, m, ?_, ?_⟩
    · rw [← OracleProg.run_recMain_fst]
      exact hdx
    · obtain ⟨m₂, hm₂⟩ := G.exists_mainOf_mem_mainReqs Q
        (C'.toPureEnv.answerAfter (H, c')) H hpre hlen
      rw [G.mainOf_congr req.2 H m m₂]
      have hrs : ((requests (splitLogs y).2).take Q).length ≤ Q := List.length_take_le _ _
      have hl := (G.relayOf Q).length_mainReqs Q (C'.toPureEnv.answerAfter (H, c')) H _ hrs
      have hmem : G.mainOf req.2 H m₂ req.1.2 req.1.1 ∈
          ((G.relayOf Q).mainReqs Q (C'.toPureEnv.answerAfter (H, c')) H
            ((requests (splitLogs y).2).take Q) ++
            List.replicate k (G.relayOf Q).idle).take C'.Q := by
        rw [List.take_append, List.take_of_length_le (by
          rw [hl]; change 1 * _ ≤ _; omega)]
        exact List.mem_append_left _ hm₂
      have hmem' : G.mainOf req.2 H m₂ req.1.2 req.1.1 ∈ (((A.absorbAssignP Req' Resp' Q).relayAdv
          (G.relayOf Q) (AssignRelay.chalT C' G Q).Q
          ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))).history C'
          ((A.absorbAssignP Req' Resp' Q).relayPlace (G.relayOf Q)
            (AssignRelay.chalT C' G Q).Q
            ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) C' H c' y)).map
          HistoryEntry.request := by
        rw [hk, map_request_histAlong]
        exact hmem
      obtain ⟨e', he', h'⟩ := List.mem_map.1 hmem'
      exact ⟨e', he', h'⟩
  have htab := hy.2.2
  have h := himp _ _ _ (((A.absorbAssignP Req' Resp' Q).relayAdv (G.relayOf Q)
    (AssignRelay.chalT C' G Q).Q
    ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))).history C'
    ((A.absorbAssignP Req' Resp' Q).relayPlace (G.relayOf Q) (AssignRelay.chalT C' G Q).Q
      ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) C' H c' y)) hy.2.1
    ⟨fun e' he' => by
      rcases hh e' he' with h1 | ⟨e, he, hc⟩
      · exact Or.inl h1
      · exact Or.inr ⟨e.request, List.mem_map_of_mem he, hc⟩,
    fun x yv hxy => origin x yv (htab.1 x yv hxy),
    fun q hq x yv hxy => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
      exact origin x yv (htab.2 e he x yv hxy)⟩
  change E'' (((A.absorbAssignP Req' Resp' Q).relayAdv (G.relayOf Q)
    (AssignRelay.chalT C' G Q).Q
    ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))).output C' _, _)
  rw [ho]
  exact h

/-- **Absorbing an assigning challenger, with the origin of the table**: as
`toOuterMeasure_le_absorbAssign`, where `E' s` need hold only at outputs `(o, T)` whose every
table entry `T x = some y` is assigned by the run of the relay program of a request `p` of `hP`
reading the oracle through the request's table `p.2`, at some main replies `m`, whose main request
is a request of `hist'`, and so is every entry of the table `q.2` of each request `q` of `hP`
(`himp`). -/
theorem toOuterMeasure_le_absorbAssign_tab {S : Type} [Fintype S] (σ : PMF S)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (hNA : C'.NoAssign) (hQ : C.Q ≤ C'.Q) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop)
    (E' : S → (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req C.Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      (G s).Explains C.Q H T hP hist' →
      E' s ((o, T), hist')) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ∑ s, σ s * (((A.absorbAssign (G s) C.Q).toKindAlg.composeBothOut C' fun v =>
        ((A.absorbAssign (G s) C.Q).output C' v, (A.absorbAssign (G s) C.Q).history C' v)).outLaw
          H).toOuterMeasure {x | ∃ p ∈ x, E' s p} := by
  rw [A.toOuterMeasure_eq_sum_absorbAssignP_tab σ G e hcoins hrel hS H E]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (A.toOuterMeasure_chalT_le_absorbAssign (G s) C.Q hNA hQ H E (E' s) (himp s)) zero_le

/-- **Absorbing an assigning challenger into the adversary** (module docstring; the law, event
form). Against the outer challenger `C`, whose coins are side coins `s ← σ` and main coins
(`hcoins`) and which relays the main challenger `C'` through `G s` (`hrel`), the adversary's
output, answered requests and final oracle in force lie in `E` with at most the `σ`-average of the
probability that the output and history of the absorbed adversary `A.absorbAssign (G s) C.Q`
against `C'` lie in `E' s`, when `E' s` holds of the output `(o, T)` with every history `hist'`
whose main requests are the padding request or ones the relay program of a request of a history
`hP` of tagged requests can make, if `E` holds of `o`, the requests of `hP` and the oracle read
through the table `T` (`himp`). Hypotheses on the main challenger: it reprograms nothing (`hNA`),
answers at least `C.Q` requests (`hQ`), and does not see the relay's assignments (`hS`). -/
theorem toOuterMeasure_le_absorbAssign {S : Type} [Fintype S] (σ : PMF S)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (hNA : C'.NoAssign) (hQ : C.Q ≤ C'.Q) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop)
    (E' : S → (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req C.Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      (∀ e' ∈ hist', e'.request = (G s).idle ∨ ∃ p ∈ hP, ((G s).relayOf C.Q).CanAsk p e'.request) →
      E' s ((o, T), hist')) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ∑ s, σ s * (((A.absorbAssign (G s) C.Q).toKindAlg.composeBothOut C' fun v =>
        ((A.absorbAssign (G s) C.Q).output C' v, (A.absorbAssign (G s) C.Q).history C' v)).outLaw
          H).toOuterMeasure {x | ∃ p ∈ x, E' s p} :=
  A.toOuterMeasure_le_absorbAssign_tab σ G e hcoins hrel hS hNA hQ H E E'
    fun s o T hP hist' h1 h2 => himp s o T hP hist' h1 h2.1

section KeepsView

variable {X Y Req Resp O Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (C : Challenger X Y Req Resp)

/-- **The final oracle through a kept view**: against a challenger keeping the view `f`, an event
`E` of the output, the answered requests and the final oracle in force has at most the
probability of an event `E₀` of the output and the answered requests alone, when `E` at an
oracle with the view of `H` gives `E₀` (`hE`). -/
theorem toOuterMeasure_le_of_keepsView {f : (X → Y) → Z} (hC : C.KeepsView f) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop) (E₀ : O × List Req → Prop)
    (hE : ∀ o rs G, f G = f H → E (o, rs, G) → E₀ (o, rs)) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E₀ (p.1, p.2.1)} := by
  classical
  set φ : O × List Req × (X → Y) → O × List Req × Z := fun p => (p.1, p.2.1, f p.2.2)
  set φ₀ : O × List Req × (X → Y) → O × List Req × Z := fun p => (p.1, p.2.1, f H)
  have hφ : (A.toKindAlg.composeBothOut C fun v => φ (A.assignReadout C H v)).outLaw H =
      (A.toKindAlg.composeBothOut C fun v => φ₀ (A.assignReadout C H v)).outLaw H := by
    refine KindAlg.outLaw_composeBothOut_congr_emb _ C H fun c r => ?_
    simp only [φ, φ₀, assignReadout]
    rw [KindAlg.reprogram_postAss_emb, hC.oracle]
  set E₁ : O × List Req × Z → Prop := fun q => ∃ G, f G = q.2.2 ∧ E (q.1, q.2.1, G)
  calc _ ≤ ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E₁ (φ p)} :=
        MeasureTheory.measure_mono fun x hx => by
          obtain ⟨p, hp, h⟩ := hx
          exact ⟨p, hp, p.2.2, rfl, h⟩
    _ = ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E₁ (φ₀ p)} := by
        rw [toOuterMeasure_outLaw_comp A C _ φ H E₁, toOuterMeasure_outLaw_comp A C _ φ₀ H E₁, hφ]
    _ ≤ _ := MeasureTheory.measure_mono fun x hx => by
        obtain ⟨p, hp, G, hG, h⟩ := hx
        exact ⟨p, hp, hE p.1 p.2.1 G hG h⟩

/-- **The final oracle through a kept view, keeping the final oracle**: against a challenger
keeping the view `f`, an event of the output, the answered requests and the final oracle `G` has
at most the probability of the same event with `f G = f H`. -/
theorem toOuterMeasure_le_of_keepsView_and {f : (X → Y) → Z} (hC : C.KeepsView f) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, f p.2.2 = f H ∧ E p} := by
  classical
  set φ : O × List Req × (X → Y) → (O × List Req × (X → Y)) × Z := fun p => (p, f p.2.2)
  set φ₀ : O × List Req × (X → Y) → (O × List Req × (X → Y)) × Z := fun p => (p, f H)
  have hφ : (A.toKindAlg.composeBothOut C fun v => φ (A.assignReadout C H v)).outLaw H =
      (A.toKindAlg.composeBothOut C fun v => φ₀ (A.assignReadout C H v)).outLaw H := by
    refine KindAlg.outLaw_composeBothOut_congr_emb _ C H fun c r => ?_
    refine Prod.ext rfl ?_
    simp only [φ, φ₀, assignReadout]
    rw [KindAlg.reprogram_postAss_emb, hC.oracle]
  set E₁ : (O × List Req × (X → Y)) × Z → Prop := fun q => q.2 = f H ∧ E q.1
  calc _ ≤ ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E₁ (φ₀ p)} :=
        MeasureTheory.measure_mono fun x hx => by
          obtain ⟨p, hp, h⟩ := hx
          exact ⟨p, hp, rfl, h⟩
    _ = ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E₁ (φ p)} := by
        rw [toOuterMeasure_outLaw_comp A C _ φ H E₁, toOuterMeasure_outLaw_comp A C _ φ₀ H E₁, hφ]

end KeepsView

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

/-- **The law of the output, the answered requests and the final oracle in force** of a `t`-query
adversary against the challenger `C` at the oracle `H` (`none`: no termination). -/
noncomputable def assignLaw (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) : PMF (Option (O × List Req × (X → Y))) :=
  𝒜.aux.bind fun a => ((𝒜.alg a).toKindAlg.composeBothOut C ((𝒜.alg a).assignReadout C H)).outLaw H

/-- **The `t`-query adversary with an assigning challenger absorbed**: auxiliary input that of `𝒜`
with side coins drawn from `σ`, and on `(a, s)` the algorithm of `𝒜` at `a` with the challenger
of the relay `G s` absorbed (`AdaptiveIAlg.absorbAssign`). At most `t + Q · qG + Q · qP` queries,
for relays with at most `qG` reads and `qP` pad sub-slots per request. -/
noncomputable def absorbAssign (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {S : Type} (σ : PMF S)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (qG : ℕ) (hG : ∀ s, (G s).qG ≤ qG)
    (qP : ℕ) (hP : ∀ s, (G s).qP ≤ qP) (Q : ℕ) :
    QueryBoundedAdversary X Y Req' Resp' (O × (X → Option Y)) (t + Q * qG + Q * qP) where
  Aux := 𝒜.Aux × S
  aux := 𝒜.aux.bind fun a => σ.map fun s => (a, s)
  sh p := ((𝒜.alg p.1).absorbAssign (G p.2) Q).toShape
  alg p := (𝒜.alg p.1).absorbAssign (G p.2) Q
  tracePreserving p := AdaptiveIAlg.absorbAssign_tracePreserving _ _ _
  withinBudget p := AdaptiveIAlg.absorbAssign_withinBudget _ _ _
  queries_le p := by
    rw [AdaptiveIAlg.absorbAssign_queries]
    exact Nat.add_le_add (Nat.add_le_add (𝒜.queries_le p.1) (Nat.mul_le_mul_left Q (hG p.2)))
      (Nat.mul_le_mul_left Q (hP p.2))

variable {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'}

/-- **Absorbing an assigning challenger, for `t`-query adversaries, with the origin of the table**
(`AdaptiveIAlg.toOuterMeasure_le_absorbAssign_tab` at each auxiliary value): the output, answered
requests and final oracle in force of `𝒜` against `C` lie in `E` with at most the probability that
the transcript of `𝒜.absorbAssign σ G qG hG qP hP C.Q` against `C'` lies in `E'`, under the
hypotheses of
`AdaptiveIAlg.toOuterMeasure_le_absorbAssign_tab`. -/
theorem assignLaw_le_absorbAssign_tab (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {S : Type}
    [Fintype S] (σ : PMF S) (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (qG : ℕ)
    (hG : ∀ s, (G s).qG ≤ qG) (qP : ℕ) (hP : ∀ s, (G s).qP ≤ qP) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (hNA : C'.NoAssign) (hQ : C.Q ≤ C'.Q) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop)
    (E' : (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req C.Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      (G s).Explains C.Q H T hP hist' →
      E' ((o, T), hist')) :
    (𝒜.assignLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbAssign σ G qG hG qP hP C.Q).transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} := by
  rw [assignLaw, transcriptLaw, absorbAssign, PMF.bind_bind, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  have h := (𝒜.alg a).toOuterMeasure_le_absorbAssign_tab σ G e hcoins hrel hS hNA hQ H E
    (fun _ => E') himp
  simp only [Function.comp_apply]
  exact h

/-- **Absorbing an assigning challenger, for `t`-query adversaries**
(`AdaptiveIAlg.toOuterMeasure_le_absorbAssign` at each auxiliary value): the output, answered
requests and final oracle in force of `𝒜` against `C` lie in `E` with at most the probability that
the transcript of `𝒜.absorbAssign σ G qG hG qP hP C.Q` against `C'` lies in `E'`, under the
hypotheses of
`AdaptiveIAlg.toOuterMeasure_le_absorbAssign`. -/
theorem assignLaw_le_absorbAssign (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {S : Type}
    [Fintype S] (σ : PMF S) (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (qG : ℕ)
    (hG : ∀ s, (G s).qG ≤ qG) (qP : ℕ) (hP : ∀ s, (G s).qP ≤ qP) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (hNA : C'.NoAssign) (hQ : C.Q ≤ C'.Q) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop)
    (E' : (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req C.Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      (∀ e' ∈ hist', e'.request = (G s).idle ∨ ∃ p ∈ hP, ((G s).relayOf C.Q).CanAsk p e'.request) →
      E' ((o, T), hist')) :
    (𝒜.assignLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbAssign σ G qG hG qP hP C.Q).transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} :=
  𝒜.assignLaw_le_absorbAssign_tab σ G qG hG qP hP e hcoins hrel hS hNA hQ H E E'
    fun s o T hP hist' h1 h2 => himp s o T hP hist' h1 h2.1

end QueryBoundedAdversary

end GordieHowe.Quantum

namespace GordieHowe.RingSignature.GameAdversary

open GordieHowe.Quantum

variable {X Y Req Resp O Req' Resp' In Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

/-- **The game adversary with an assigning challenger absorbed**: on each start input `inp`, the
`t`-query adversary `A inp` with the challenger of the relays `G inp s`, side coins from `σ inp`,
absorbed (`QueryBoundedAdversary.absorbAssign`). At most `t + Q · qG + Q · qP` queries. -/
noncomputable def absorbAssign (A : GameAdversary X Y Req Resp In O t) {S : Type} (σ : In → PMF S)
    (G : In → S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (qG : ℕ)
    (hG : ∀ inp s, (G inp s).qG ≤ qG) (qP : ℕ) (hP : ∀ inp s, (G inp s).qP ≤ qP) (Q : ℕ) :
    GameAdversary X Y Req' Resp' In (O × (X → Option Y)) (t + Q * qG + Q * qP) := fun inp =>
  (A inp).absorbAssign (σ inp) (G inp) qG (hG inp) qP (hP inp) Q

end GordieHowe.RingSignature.GameAdversary
