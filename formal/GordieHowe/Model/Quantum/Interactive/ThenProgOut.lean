-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ThenProg
public import GordieHowe.Model.Quantum.Interactive.SplitRestrict

@[expose] public section

/-!
# An adversary followed by a classical program on its output

`AdaptiveIAlg.thenProgOut A P q hP`: the adversary with run-time kinds `A`, followed in its post
phase by the classical oracle program `P o` (`GordieHowe/Model/NARG/OracleProg.lean`) on `A`'s
output `o`, read in the computational basis of `A`'s final workspace; `P o` makes at most `q`
queries against every oracle (`hP`). The output is the pair of `A`'s output and the program's
result. It is `AdaptiveIAlg.thenProgWith` (`GordieHowe/Model/Quantum/Interactive/ThenProg.lean`)
with the program `P` on `A`'s output and the output map pairing `A`'s output with the result read
from the table of answers (`AdaptiveIAlg.progRes`). The slots, the budget, the width and the kinds
are `A`'s; `post` is `A.post + q`.

## Results

- `AdaptiveIAlg.toOuterMeasure_outLaw_comp`: an event read through a map `g` of the readout `F`
  is the event under the readout `g ∘ F`.
- `thenProgOut_width`, `thenProgOut_slots`, `thenProgOut_post`, `thenProgOut_budget`.
- `thenProgOut_queries`: `width * (budget + post) = A.width * (A.budget + A.post) + A.width * q`.
- `thenProgOut_tracePreserving`, `withinBudget_thenProgOut`, `requestsAfterAtMost_thenProgOut`.
- `QueryBoundedAdversary.thenProgOut A P q hP s hs`: for a `t`-query adversary `A` with
  `width * q ≤ s` at every auxiliary input (`hs`), a `(t + s)`-query adversary.
- `outLaw_composeBothOut_thenProgWith`: for every readout of the output and the challenger's
  registers, the output law of the composition of `thenProgWith` at `H` is that of `A`'s
  composition read through `g` of `A`'s workspace and the program's table of answers against `H`
  reprogrammed by the final assignments (`KindAlg.postAss`).
- `outLaw_composeBothOut_thenProgOut`: for every readout `F` of the output and the history, the
  output law of the composition of `thenProgOut` at `H` is that of `A`'s composition read as
  `F (o, (P o).run H') h`, `o` the output, `h` the history, `H'` the oracle `H` reprogrammed by the
  final assignments. `outLaw_composeBothOut_thenProgOut_of_noAssign`: against a challenger that
  reprograms nothing (`Challenger.NoAssign`), `H' = H`.
- `KindAlg.outLaw_composeBothOut_map`: a readout followed by a map is the law of the readout,
  mapped. `KindAlg.outLaw_composeBothOut_congr_emb`: readouts that agree on the placed game
  registers (`KindAlg.emb`) have the same output law. `KindAlg.reprogram_postAss_emb_of_noAssign`:
  against a challenger that reprograms nothing, the final oracle in force at the placed game
  registers is `H`.
- `outLaw_compose_thenProgOut`: against every challenger, the output law of the model's
  composition of `thenProgOut` is that of `A`'s composition read as `(o, (P o).run H')`, `H'` the
  final oracle in force.
- `QueryBoundedAdversary.transcriptLawAss`: the transcript law with the final assignments;
  `transcriptLaw_eq_map_transcriptLawAss`: forgetting them gives `transcriptLaw`.
- `QueryBoundedAdversary.transcriptLaw_thenProgOut_assign`: against every challenger, the
  transcript law of `A.thenProgOut` at `H` is `transcriptLawAss` read with the program run at the
  final oracle in force, `H` reprogrammed by the final assignments.
- `QueryBoundedAdversary.transcriptLaw_thenProgOut`: against a challenger that reprograms nothing,
  the transcript law of `A.thenProgOut` at `H` is `A`'s with each output `o` replaced by
  `(o, (P o).run H)`.
- `realLaw_composeBothOut_thenProgOut`, `realLaw_composeBothOut_thenProgOut_of_noAssign`: the
  same with `H` uniform, as an event of the law of `A`'s composed registers (or `A`'s output and
  history) and the oracle.
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Readouts of a composition -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (C : Challenger X Y Req Resp)

/-- **A readout followed by a map**: the output law of the composition read by `φ ∘ f` is the law
read by `f`, mapped by `φ`. -/
theorem outLaw_composeBothOut_map {O' O'' : Type} (f : B.CW C → O') (φ : O' → O'') (H : X → Y) :
    (B.composeBothOut C fun v => φ (f v)).outLaw H =
      ((B.composeBothOut C f).outLaw H).map (Option.map φ) := by
  simp only [Alg.outLaw, PMF.map_comp, Option.map_comp_map]
  rfl

/-- **Readouts that agree on the placed game registers have the same output law**: the
composition is supported on the registers `emb C H c B.slots r` (`outLaw_composeBothOut_some`). -/
theorem outLaw_composeBothOut_congr_emb {O' : Type} {f₁ f₂ : B.CW C → O'} (H : X → Y)
    (h : ∀ c r, f₁ (B.emb C H c B.slots r).1 = f₂ (B.emb C H c B.slots r).1) :
    (B.composeBothOut C f₁).outLaw H = (B.composeBothOut C f₂).outLaw H := by
  classical
  refine PMF.ext_of_apply_some fun o => ?_
  rw [B.outLaw_composeBothOut_some C f₁ H o, B.outLaw_composeBothOut_some C f₂ H o]
  simp only [h]

/-- **Against a challenger that reprograms nothing, the final oracle in force is `H`** at the
placed game registers. -/
theorem reprogram_postAss_emb_of_noAssign {C : Challenger X Y Req Resp} (hC : C.NoAssign)
    (H : X → Y) (c : C.Coins) (r : B.G) :
    H.reprogram (B.postAss C (B.emb C H c B.slots r).1.chal) = H := by
  rw [B.reprogram_postAss_emb C H c r, hC.oracle_eq]

end KindAlg

namespace AdaptiveIAlg

section Comp

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (C : Challenger X Y Req Resp)

/-- **A readout followed by a map, at an event**: the probability of the event `P ∘ g` under the
readout `F` is that of `P` under the readout `g ∘ F`. -/
theorem toOuterMeasure_outLaw_comp {O' O'' : Type} (F : A.toKindAlg.CW C → O') (g : O' → O'')
    (H : X → Y) (P : O'' → Prop) :
    ((A.toKindAlg.composeBothOut C F).outLaw H).toOuterMeasure {x | ∃ p ∈ x, P (g p)} =
      ((A.toKindAlg.composeBothOut C fun v => g (F v)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, P p} := by
  rw [KindAlg.outLaw_composeBothOut_map _ C F g H, PMF.toOuterMeasure_map_apply]
  refine congrArg _ (Set.ext fun x => ?_)
  rcases x with _ | p <;> simp

end Comp

/-! ### The law of `thenProgWith` with a readout -/

section With

variable {X Y Req Resp O Res : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (P : A.W → GordieHowe.OracleProg X Y Res) (q : ℕ)
  (hP : ∀ w, (P w).QueriesLE q) {O' : Type} (g : A.W → (Fin q → Y) → O')
  (C : Challenger X Y Req Resp)

open Quantum.OracleProg (tab)

/-- **The output law of `A` followed by the program, with a readout**: for every readout `F` of the
output and the challenger's registers, the output law of the composition at `H` is the law of
`A`'s composition read by `F` of `g` of `A`'s workspace and the program's table of answers against
`H` reprogrammed by the final assignments, and the challenger's registers. -/
theorem outLaw_composeBothOut_thenProgWith {O'' : Type} (F : O' → A.toKindAlg.CCl C → O'')
    (H : X → Y) :
    ((A.thenProgWith P q hP g).toKindAlg.composeBothOut C fun v =>
        F ((A.thenProgWith P q hP g).toKindAlg.out v.adv.workspace) v.chal).outLaw H =
      (A.toKindAlg.composeBothOut C fun v => F (g v.adv.workspace.1
        (tab (P v.adv.workspace.1) q KindAlg.x₀ (H.reprogram (A.toKindAlg.postAss C v.chal)) q))
          v.chal).outLaw H := by
  classical
  refine PMF.ext_of_apply_some fun o => ?_
  rw [Alg.outLaw_some_eq_sum, Alg.outLaw_some_eq_sum]
  have hL := sum_indicator_composeBothOut C (K := (A.thenProgWith P q hP g).toKindAlg)
    (fun v => F ((A.thenProgWith P q hP g).toKindAlg.out v.adv.workspace) v.chal) H
    {v | F ((A.thenProgWith P q hP g).toKindAlg.out v.adv.workspace) v.chal = o}
  have hR := sum_indicator_composeBothOut C (K := A.toKindAlg)
    (fun v => F (g v.adv.workspace.1 (tab (P v.adv.workspace.1) q KindAlg.x₀
      (H.reprogram (A.toKindAlg.postAss C v.chal)) q)) v.chal) H
    {v | F (g v.adv.workspace.1 (tab (P v.adv.workspace.1) q KindAlg.x₀
      (H.reprogram (A.toKindAlg.postAss C v.chal)) q)) v.chal = o}
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hD := A.sum_diag_thenProgWith P q hP g C H fun c u => if F c u = o then 1 else 0
  simpa only [Set.mem_ofPred_eq] using hD

end With

/-! ### The adversary followed by a program on its output -/

section Out

variable {X Y Req Resp O R : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (P : O → GordieHowe.OracleProg X Y R) (q : ℕ)

/-- The program on `A`'s output, as a program on `A`'s workspace. -/
def progOn (w : A.W) : GordieHowe.OracleProg X Y R :=
  P (A.out w)

/-- **The adversary followed by a classical program on its output** (module docstring): `A`'s
run, then `P` on `A`'s output with basis-state queries in `q` extra post batches; the output is
`A`'s output with the program's result (its run on the all-zero oracle if it wants more answers
than the table holds, which `hP` excludes).

Running time: that of `A`, then `q` queries and `q + 1` basis permutations, each computing one
query of `P o` (`OracleProg.next` on at most `q` answers) and moving one answer; polynomial when
`A` and `P` are. This running time is argued here, not proved in Lean. -/
noncomputable def thenProgOut (hP : ∀ o, (P o).QueriesLE q) : AdaptiveIAlg (shA.thenProgS q) (O × R) :=
  A.thenProgWith (A.progOn P) q (fun w => hP (A.out w)) fun w T =>
    (A.out w, A.progRes (A.progOn P) q (fun w => (A.progOn P w).run 0) w T)

variable (hP : ∀ o, (P o).QueriesLE q)

/-- The width of `A` followed by the program is `A`'s. -/
@[simp] theorem thenProgOut_width : (A.thenProgOut P q hP).width = A.width := rfl

/-- The slots of `A` followed by the program are `A`'s. -/
@[simp] theorem thenProgOut_slots : (A.thenProgOut P q hP).slots = A.slots := rfl

/-- `A` followed by the program has `q` more post batches than `A`. -/
@[simp] theorem thenProgOut_post : (A.thenProgOut P q hP).post = A.post + q := rfl

/-- The query budget of `A` followed by the program is `A`'s. -/
@[simp] theorem thenProgOut_budget : (A.thenProgOut P q hP).budget = A.budget := rfl

/-- **The queries of `A` followed by the program** on every branch: `A`'s and the program's `q`
batches of `width` queries. -/
theorem thenProgOut_queries :
    (A.thenProgOut P q hP).width * ((A.thenProgOut P q hP).budget + (A.thenProgOut P q hP).post) =
      A.width * (A.budget + A.post) + A.width * q :=
  A.thenProgWith_queries (A.progOn P) q _ _

/-- **`A` followed by the program is trace preserving** when `A` is. -/
theorem thenProgOut_tracePreserving (hA : A.TracePreserving) :
    (A.thenProgOut P q hP).TracePreserving :=
  A.thenProgWith_tracePreserving (A.progOn P) q _ _ hA

/-- **Every proof query of `A` followed by the program comes after at most `budget` query slots.** -/
theorem requestsAfterAtMost_thenProgOut :
    (A.thenProgOut P q hP).RequestsAfterAtMost A.budget :=
  A.requestsAfterAtMost_thenProgWith (A.progOn P) q _ _

variable [Nonempty Y]

/-- **`A` followed by the program stays within its budget** when `A` does. -/
theorem withinBudget_thenProgOut (hA : A.WithinBudget) : (A.thenProgOut P q hP).WithinBudget :=
  A.withinBudget_thenProgWith (A.progOn P) q _ _ hA

variable (C : Challenger X Y Req Resp)

/-- **The output law of `A` followed by the program on its output** (main result): against every
challenger `C`, oracle `H` and readout `F` of the output and the history, the output law of the
composition at `H` is the law of `A`'s composition read as `F (o, (P o).run H') h`, where `o` is
`A`'s output, `h` the history, and `H'` the oracle `H` reprogrammed by the final assignments. -/
theorem outLaw_composeBothOut_thenProgOut {O' : Type}
    (F : O × R → List (HistoryEntry Req Resp) → O') (H : X → Y) :
    ((A.thenProgOut P q hP).toKindAlg.composeBothOut C fun v =>
        F ((A.thenProgOut P q hP).output C v) ((A.thenProgOut P q hP).history C v)).outLaw H =
      (A.toKindAlg.composeBothOut C fun v =>
        F (A.output C v, (P (A.output C v)).run (H.reprogram (A.toKindAlg.postAss C v.chal)))
          (A.history C v)).outLaw H := by
  refine (A.outLaw_composeBothOut_thenProgWith (A.progOn P) q (fun w => hP (A.out w)) _ C
    (fun oo u => F oo (A.toKindAlg.stateAt C u A.toKindAlg.slots).history) H).trans
    (congrArg (fun f => (A.toKindAlg.composeBothOut C f).outLaw H) (funext fun v => ?_))
  show F (A.out _, A.progRes (A.progOn P) q _ _ (Quantum.OracleProg.tab _ q _ _ q)) _ = _
  rw [A.progRes_tab (A.progOn P) q (fun w => hP (A.out w))]
  rfl

/-- **The output law of the model's composition of `A` followed by the program**: against every
challenger `C` (which may reprogram) and oracle `H`, the law of `A`'s composition read as
`(o, (P o).run H')`, where `o` is `A`'s output and `H'` is the final oracle in force, `H`
reprogrammed by the final assignments (`KindAlg.postAss`). -/
theorem outLaw_compose_thenProgOut (H : X → Y) :
    ((A.thenProgOut P q hP).compose C).outLaw H =
      (A.toKindAlg.composeBothOut C fun v => (A.output C v,
        (P (A.output C v)).run (H.reprogram (A.toKindAlg.postAss C v.chal)))).outLaw H :=
  A.outLaw_composeBothOut_thenProgOut P q hP C (fun o _ => o) H

/-- **The output law against a challenger that reprograms nothing**: the law of `A`'s composition
read as `F (o, (P o).run H) h`. -/
theorem outLaw_composeBothOut_thenProgOut_of_noAssign (hC : C.NoAssign) {O' : Type}
    (F : O × R → List (HistoryEntry Req Resp) → O') (H : X → Y) :
    ((A.thenProgOut P q hP).toKindAlg.composeBothOut C fun v =>
        F ((A.thenProgOut P q hP).output C v) ((A.thenProgOut P q hP).history C v)).outLaw H =
      (A.toKindAlg.composeBothOut C fun v =>
        F (A.output C v, (P (A.output C v)).run H) (A.history C v)).outLaw H := by
  rw [A.outLaw_composeBothOut_thenProgOut P q hP C F H]
  refine A.toKindAlg.outLaw_composeBothOut_congr_emb C H fun c r => ?_
  simp only [A.toKindAlg.reprogram_postAss_emb_of_noAssign hC H c r]

/-- **The law of `A` followed by the program on its output, with `H` uniform**: an event `E` of
the readout `F` of the output and the history, and of the oracle read through `e`, has the
probability, in the law of `A`'s composed registers `v` and the oracle, of `E` at
`F (o, (P o).run H') h`, where `o` is `A`'s output, `h` the history, and `H'` the oracle
reprogrammed by the final assignments. -/
theorem realLaw_composeBothOut_thenProgOut {O' : Type}
    (F : O × R → List (HistoryEntry Req Resp) → O') {Bt : Type} (e : Y ≃ Bt)
    (E : Option O' → (X → Bt) → Prop) :
    (((A.thenProgOut P q hP).toKindAlg.composeBothOut C fun v =>
        F ((A.thenProgOut P q hP).output C v) ((A.thenProgOut P q hP).history C v)).realLaw
        e).toOuterMeasure {p | E p.out p.oracle} =
      ((A.toKindAlg.composeBothOut C id).realLaw e).toOuterMeasure
        {p | E (p.out.map fun v => F (A.output C v, (P (A.output C v)).run
          ((e.symm ∘ p.oracle).reprogram (A.toKindAlg.postAss C v.chal))) (A.history C v))
          p.oracle} := by
  rw [Alg.realLaw, Alg.realLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  have hH : e.symm ∘ (e ∘ H) = H := by
    funext x
    simp
  have hm : (A.toKindAlg.composeBothOut C fun v => F (A.output C v, (P (A.output C v)).run
      (H.reprogram (A.toKindAlg.postAss C v.chal))) (A.history C v)).outLaw H =
      ((A.toKindAlg.composeBothOut C id).outLaw H).map (Option.map fun v => F (A.output C v,
        (P (A.output C v)).run (H.reprogram (A.toKindAlg.postAss C v.chal))) (A.history C v)) :=
    A.toKindAlg.outLaw_composeBothOut_map C id (fun v => F (A.output C v,
      (P (A.output C v)).run (H.reprogram (A.toKindAlg.postAss C v.chal))) (A.history C v)) H
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    A.outLaw_composeBothOut_thenProgOut P q hP C F H, hm, PMF.toOuterMeasure_map_apply]
  congr 1
  ext o
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hH]

/-- **The law with `H` uniform, against a challenger that reprograms nothing**: an event `E` of
the readout `F` of the output and the history, and of the oracle read through `e`, has the
probability, in the law of `A`'s output `o` with the history `h` and the oracle, of `E` at
`F (o, (P o).run H) h`. -/
theorem realLaw_composeBothOut_thenProgOut_of_noAssign (hC : C.NoAssign) {O' : Type}
    (F : O × R → List (HistoryEntry Req Resp) → O') {Bt : Type} (e : Y ≃ Bt)
    (E : Option O' → (X → Bt) → Prop) :
    (((A.thenProgOut P q hP).toKindAlg.composeBothOut C fun v =>
        F ((A.thenProgOut P q hP).output C v) ((A.thenProgOut P q hP).history C v)).realLaw
        e).toOuterMeasure {p | E p.out p.oracle} =
      ((A.toKindAlg.composeBothOut C fun v => (A.output C v, A.history C v)).realLaw
        e).toOuterMeasure
        {p | E (p.out.map fun oh => F (oh.1, (P oh.1).run (e.symm ∘ p.oracle)) oh.2) p.oracle} := by
  rw [Alg.realLaw, Alg.realLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  have hH : e.symm ∘ (e ∘ H) = H := by
    funext x
    simp
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    A.outLaw_composeBothOut_thenProgOut_of_noAssign P q hP C hC F H,
    A.toKindAlg.outLaw_composeBothOut_map C (fun v => (A.output C v, A.history C v))
      (fun oh => F (oh.1, (P oh.1).run H) oh.2) H,
    PMF.toOuterMeasure_map_apply]
  congr 1
  ext o
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hH]

end Out

end AdaptiveIAlg

/-! ### Query-bounded adversaries -/

namespace QueryBoundedAdversary

variable {X Y Req Resp O R : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ} (A : QueryBoundedAdversary X Y Req Resp O t)
  (P : O → GordieHowe.OracleProg X Y R) (q : ℕ) (hP : ∀ o, (P o).QueriesLE q)

/-- **A `t`-query adversary followed by a program on its output**: the same auxiliary input, and on
each value `a` the adversary followed by `P` on its output (`AdaptiveIAlg.thenProgOut`), a
`(t + s)`-query adversary when `width * q ≤ s` at every value (`hs`); the program's `q` batches add
`width * q` queries (`AdaptiveIAlg.thenProgOut_queries`).

Running time: that of `A.alg a` followed by the program (`AdaptiveIAlg.thenProgOut`); polynomial
when `A` and `P` are. This running time is argued here, not proved in Lean. -/
noncomputable def thenProgOut (s : ℕ) (hs : ∀ a, (A.alg a).width * q ≤ s) :
    QueryBoundedAdversary X Y Req Resp (O × R) (t + s) where
  Aux := A.Aux
  aux := A.aux
  sh a := (A.sh a).thenProgS q
  alg a := (A.alg a).thenProgOut P q hP
  tracePreserving a := (A.alg a).thenProgOut_tracePreserving P q hP (A.tracePreserving a)
  withinBudget a := (A.alg a).withinBudget_thenProgOut P q hP (A.withinBudget a)
  queries_le a := by
    rw [AdaptiveIAlg.thenProgOut_queries]
    exact Nat.add_le_add (A.queries_le a) (hs a)

/-- **The transcript law with the final assignments** at the oracle `H` against the challenger
`C`: the auxiliary input drawn, then the composed algorithm run, read as the adversary's output
and the history (`transcriptLaw`) together with the final assignments (`KindAlg.postAss`), which
reprogram `H` into the final oracle in force; `none` when the run does not terminate. -/
noncomputable def transcriptLawAss {O : Type} {t : ℕ}
    (A : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) :
    PMF (Option ((O × List (HistoryEntry Req Resp)) × List (Assignment X Y))) :=
  A.aux.bind fun a =>
    ((A.alg a).toKindAlg.composeBothOut C fun v =>
      (((A.alg a).output C v, (A.alg a).history C v),
        (A.alg a).toKindAlg.postAss C v.chal)).outLaw H

/-- **The transcript law forgets the final assignments** of `transcriptLawAss`. -/
theorem transcriptLaw_eq_map_transcriptLawAss (C : Challenger X Y Req Resp) (H : X → Y) :
    A.transcriptLaw C H = (A.transcriptLawAss C H).map (Option.map Prod.fst) := by
  simp only [transcriptLaw, transcriptLawAss, PMF.map_bind]
  refine congrArg A.aux.bind (funext fun a => ?_)
  exact (A.alg a).toKindAlg.outLaw_composeBothOut_map C (fun v =>
    (((A.alg a).output C v, (A.alg a).history C v), (A.alg a).toKindAlg.postAss C v.chal))
    Prod.fst H

/-- **The transcript law of the adversary followed by a program on its output, against every
challenger**: at the oracle `H`, the law `transcriptLawAss` of `A`'s output `o`, the history `h`
and the final assignments `as`, read as `((o, (P o).run H'), h)`, where the program reads
`H' = H.reprogram as`, the final oracle in force. -/
theorem transcriptLaw_thenProgOut_assign (s : ℕ) (hs : ∀ a, (A.alg a).width * q ≤ s)
    (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.thenProgOut P q hP s hs).transcriptLaw C H =
      (A.transcriptLawAss C H).map
        (Option.map fun p => ((p.1.1, (P p.1.1).run (H.reprogram p.2)), p.1.2)) := by
  simp only [transcriptLaw, transcriptLawAss, PMF.map_bind]
  refine congrArg A.aux.bind (funext fun a => ?_)
  exact ((A.alg a).outLaw_composeBothOut_thenProgOut P q hP C Prod.mk H).trans
    ((A.alg a).toKindAlg.outLaw_composeBothOut_map C (fun v =>
      (((A.alg a).output C v, (A.alg a).history C v), (A.alg a).toKindAlg.postAss C v.chal))
      (fun p => ((p.1.1, (P p.1.1).run (H.reprogram p.2)), p.1.2)) H)

/-- **The transcript law of the adversary followed by a program on its output**: against a
challenger that reprograms nothing, at the oracle `H`, `A`'s transcript law with each output `o`
replaced by `(o, (P o).run H)`. -/
theorem transcriptLaw_thenProgOut (s : ℕ) (hs : ∀ a, (A.alg a).width * q ≤ s)
    (C : Challenger X Y Req Resp) (hC : C.NoAssign) (H : X → Y) :
    (A.thenProgOut P q hP s hs).transcriptLaw C H =
      (A.transcriptLaw C H).map (Option.map fun oh => ((oh.1, (P oh.1).run H), oh.2)) := by
  simp only [transcriptLaw, PMF.map_bind]
  refine congrArg A.aux.bind (funext fun a => ?_)
  exact ((A.alg a).outLaw_composeBothOut_thenProgOut_of_noAssign P q hP C hC Prod.mk H).trans
    ((A.alg a).toKindAlg.outLaw_composeBothOut_map C
      (fun v => ((A.alg a).output C v, (A.alg a).history C v))
      (fun oh => ((oh.1, (P oh.1).run H), oh.2)) H)

end QueryBoundedAdversary

end GordieHowe.Quantum
