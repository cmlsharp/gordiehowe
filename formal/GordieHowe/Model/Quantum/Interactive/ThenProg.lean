-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.QueryFreeTest
public import GordieHowe.Model.Quantum.Interactive.ProgAlg
public import GordieHowe.Model.Quantum.Interactive.TPRun
public import GordieHowe.Model.Quantum.Interactive.Embed
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedLastProofQuery

@[expose] public section

/-!
# An adversary followed by a classical oracle program

`AdaptiveIAlg.thenProgWith A P q hP g`: the adversary with run-time kinds `A`, followed in its post
phase by the classical oracle program `P w` (`GordieHowe/Model/NARG/OracleProg.lean`) on `A`'s
final workspace `w`, read in the computational basis; `P w` makes at most `q` queries against every
oracle (`hP`). The output is `g w T` of `A`'s workspace and the program's table `T` of answers.
`AdaptiveIAlg.thenProg A P q hP` outputs the program's result, a bit (`g` reads the result off the
table, `progRes`). This turns an adversary that outputs a claim into a distinguisher that runs a
verifier on the claim.

The workspace is `A`'s with the registers of the compiled program of
`GordieHowe/Model/Quantum/Interactive/ProgAlg.lean` (`OracleProg.ProgW`): a table of `q` answers and
a kept pair, initially blank (the table `0`, the kept pair `(x₀, 0)`). The run is `A`'s run, with
`A`'s Kraus maps acting on `A`'s registers. After `A`'s last Kraus map, the kept pair is exchanged
with query pair `0` and its input becomes the first query of the program (`startPerm`); then come
`q` extra post batches, each followed by the move of the answer of pair `0` into the table and the
next query of the program (`progPerm`). The other query pairs are queried too; nothing reads them
afterwards. The slots, the budget, the width and the kinds are `A`'s; `post` is `A.post + q`.

## Results

- `thenProgWith_tracePreserving`, `withinBudget_thenProgWith`, `requestsAfterAtMost_thenProgWith`,
  `thenProgWith_queries`; for `thenProg`: `thenProg_tracePreserving`, `withinBudget_thenProg`,
  `requestsAfterAtMost_thenProg`, `thenProg_queries`.
- `out_tailPerm`, `chal_tailPerm`: after `A`'s run, the output is `g` of `A`'s workspace and the
  table of the program's answers against `H` reprogrammed by the final assignments
  (`KindAlg.postAss`); the challenger's registers are left alone. `progRes_tab`: the result read
  from that table is the program's run.
- `sum_diag_thenProgWith`: the diagonal of the final state of the composition with a challenger,
  summed against a function of the output and the challenger's registers, is that of `A`'s
  composition summed against the same function of `g` of `A`'s workspace and the table.
- `outLaw_thenProg`: the probability that the composition of `thenProg` with a challenger outputs
  `b` on the oracle `H` is the probability that the composition of `A` ends with composed
  registers `v` such that `P` on `A`'s workspace, run against `H` reprogrammed by the final
  assignments, returns `b`.
- `realLaw_thenProg`: the same with `H` uniform, as an event of the law of `A`'s composed registers
  and the oracle.
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Circuits whose run is a basis permutation -/

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y]

/-- **The run of `c` with oracle `H` is the basis permutation `π`**: every input state is moved by
`π`. -/
def RunsPerm (H : X → Y) (c : ReprogrammedCircuit V X Y) (π : Equiv.Perm (QueryReg V 1 X Y)) :
    Prop :=
  ∀ ρ, c.run H ρ = ρ.submatrix π.symm π.symm

/-- The empty circuit runs the identity. -/
theorem runsPerm_nil (H : X → Y) : (nil : ReprogrammedCircuit V X Y).RunsPerm H (Equiv.refl _) :=
  fun ρ => by simp [run]

/-- A basis permutation as a circuit runs that permutation. -/
theorem runsPerm_ofPerm (H : X → Y) (π : Equiv.Perm (QueryReg V 1 X Y)) :
    (kraus (KrausMap.ofPerm π) nil).RunsPerm H π :=
  fun ρ => by simp only [run, KrausMap.ofPerm_apply]

/-- **Concatenated permutation circuits run the composite permutation**, the first one first. -/
theorem RunsPerm.append {H : X → Y} {c d : ReprogrammedCircuit V X Y}
    {π σ : Equiv.Perm (QueryReg V 1 X Y)} (hc : c.RunsPerm H π) (hd : d.RunsPerm H σ) :
    (c ++ d).RunsPerm H (π.trans σ) := fun ρ => by
  rw [run_append, hc, hd, submatrix_submatrix]
  rfl

/-- **A concatenation of permutation circuits runs the composite permutation**, the first one
first. -/
theorem runsPerm_concat {H : X → Y} {α : Type*} {f : α → ReprogrammedCircuit V X Y}
    {g : α → Equiv.Perm (QueryReg V 1 X Y)} (h : ∀ a, (f a).RunsPerm H (g a)) :
    ∀ l : List α, (concat (l.map f)).RunsPerm H ((l.map g).foldr (fun π acc => π.trans acc)
      (Equiv.refl _))
  | [] => runsPerm_nil H
  | a :: l => (h a).append (runsPerm_concat h l)

end ReprogrammedCircuit

/-! ### The adversary's queries of a batch, one basis state at a time -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {ksK : KindShape X Y Req Resp} (K : KindAlg ksK O) (C : Challenger X Y Req Resp)

/-- **The adversary's query `k` on a basis state**, when the reprogramming reads only the
challenger's registers: pair `k` is queried to `H` reprogrammed by `f` of them. -/
theorem advStepPerm_chal (H : X → Y) (f : K.CCl C → List (Assignment X Y)) (k : Fin K.width)
    (y : QueryReg (K.CW C) 1 X Y) :
    K.advStepPerm C H (fun v => f v.chal) k y =
      (⟨(y.1.adv.1, Function.update y.1.adv.2 k ((y.1.adv.2 k).1,
        (y.1.adv.2 k).2 + H.reprogram (f y.1.chal) (y.1.adv.2 k).1)), y.1.chal⟩, y.2) := by
  obtain ⟨⟨⟨d, prs⟩, u⟩, qr⟩ := y
  simp only [advStepPerm, Equiv.trans_apply, advSwap, pairSwap, Function.Involutive.toPerm,
    Equiv.coe_fn_mk, queryPermOf_apply, Function.update_self, Function.update_idem]
  refine Prod.ext (CWork.ext (Prod.ext rfl (funext fun i => ?_)) rfl) (funext fun j => ?_)
  · by_cases hi : i = k
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  · simp [Fin.fin_one_eq_zero j]

/-- **The adversary's queries of a batch on a basis state**, along a list of distinct pairs: the
pairs of the list are queried, the others and the rest of the registers are left alone. -/
theorem foldr_advStepPerm_chal (H : X → Y) (f : K.CCl C → List (Assignment X Y)) :
    ∀ (l : List (Fin K.width)), l.Nodup → ∀ y : QueryReg (K.CW C) 1 X Y,
      (l.map (K.advStepPerm C H fun v => f v.chal)).foldr (fun π acc => π.trans acc)
        (Equiv.refl _) y =
      (⟨(y.1.adv.1, fun i => if i ∈ l then ((y.1.adv.2 i).1,
        (y.1.adv.2 i).2 + H.reprogram (f y.1.chal) (y.1.adv.2 i).1) else y.1.adv.2 i), y.1.chal⟩,
        y.2)
  | [], _, y => by
    obtain ⟨⟨⟨d, prs⟩, u⟩, qr⟩ := y
    rfl
  | k :: l, hl, y => by
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.foldr_cons, Equiv.trans_apply]
    rw [foldr_advStepPerm_chal H f l hl.2, advStepPerm_chal]
    obtain ⟨⟨⟨d, prs⟩, u⟩, qr⟩ := y
    refine Prod.ext (CWork.ext (Prod.ext rfl (funext fun i => ?_)) rfl) rfl
    by_cases hi : i = k
    · subst hi
      simp [hl.1]
    · simp [hi]

/-- **The adversary's queries of a batch on a basis state**: all pairs queried. -/
theorem advQueriesPerm_chal (H : X → Y) (f : K.CCl C → List (Assignment X Y))
    (y : QueryReg (K.CW C) 1 X Y) :
    ((List.finRange K.width).map (K.advStepPerm C H fun v => f v.chal)).foldr
        (fun π acc => π.trans acc) (Equiv.refl _) y =
      (⟨(y.1.adv.1, fun i => ((y.1.adv.2 i).1,
        (y.1.adv.2 i).2 + H.reprogram (f y.1.chal) (y.1.adv.2 i).1)), y.1.chal⟩, y.2) := by
  rw [foldr_advStepPerm_chal K C H f _ (List.nodup_finRange _)]
  simp

end KindAlg

/-! ### Output laws as diagonal sums -/

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [AddGroup Y]
  (G : Alg X Y O)

/-- **The probability of an event of the output**: the diagonal mass of the final state on the
outcomes whose output satisfies the event. -/
theorem toOuterMeasure_outLaw_some (H : X → Y) (E : O → Prop) :
    (G.outLaw H).toOuterMeasure {o | ∃ v, o = some v ∧ E v} =
      ∑ i, Set.indicator {i | E (G.out i.1)} (fun i => ENNReal.ofReal (G.final H i i).re) i := by
  rw [Alg.outLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, tsum_fintype,
    Fintype.sum_option]
  rw [Set.indicator_of_notMem (by simp), zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : E (G.out i.1)
  · rw [Set.indicator_of_mem (by exact ⟨_, rfl, h⟩), Set.indicator_of_mem (show i ∈ {i | E (G.out i.1)} from h)]
    rfl
  · rw [Set.indicator_of_notMem (by
        rintro ⟨v, hv, hE⟩
        rw [Option.map_some, Option.some.injEq] at hv
        exact h (hv ▸ hE)),
      Set.indicator_of_notMem (show i ∉ {i | E (G.out i.1)} from h)]

/-- **The probability of an output value**: the diagonal mass of the final state on the outcomes
with that output. -/
theorem outLaw_some_eq_sum (H : X → Y) (o : O) :
    G.outLaw H (some o) =
      ∑ i, Set.indicator {i | G.out i.1 = o} (fun i => ENNReal.ofReal (G.final H i i).re) i := by
  rw [← G.toOuterMeasure_outLaw_some H (· = o), ← PMF.toOuterMeasure_apply_singleton]
  congr 1
  ext v
  simp

end Alg

namespace AdaptiveIAlg

section With

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) {Res : Type} (P : A.W → GordieHowe.OracleProg X Y Res) (q : ℕ)

open Quantum.OracleProg (ProgW answers nextQ)

/-! ### The adversary followed by the program -/

/-- The registers of `A` with the program's registers, as `A`'s registers and the program's. -/
def progSplit : DReg (A.W × ProgW X Y q) A.width X Y Req Resp ≃
    DReg A.W A.width X Y Req Resp × ProgW X Y q where
  toFun p := (((p.1.1.1, p.1.2.1, p.1.2.2), p.2), p.1.1.2)
  invFun r := ((((r.1.1.1, r.2), r.1.1.2.1, r.1.1.2.2)), r.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A Kraus map on `A`'s registers as a map on the registers with the program's, the identity on
the program's registers. -/
def liftProg {R : Type} [Fintype R] (K : KrausMap R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)) :
    KrausMap R (DReg (A.W × ProgW X Y q) A.width X Y Req Resp)
      (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  (K.tensorId (ProgW X Y q)).reindex (A.progSplit q).symm

/-- The query pair that carries the program's queries. -/
def pair0 : Fin A.width := ⟨0, A.width_pos⟩

/-- **Exchange the kept pair with query pair `0`.** -/
def keepIn : Equiv.Perm (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  Function.Involutive.toPerm
    (fun p => (((p.1.1.1, (p.1.1.2.1, p.2 A.pair0)), p.1.2), Function.update p.2 A.pair0 p.1.1.2.2))
    fun p => by
      obtain ⟨⟨⟨w, T, kp⟩, rr⟩, prs⟩ := p
      simp

variable [Nonempty X] [AddGroup Y]

/-- The query of `P w` after the first `j` answers of the table `T` (padded with `x₀`). -/
noncomputable def progQ (w : A.W) (T : Fin q → Y)
    (j : ℕ) : X :=
  nextQ (P w) q KindAlg.x₀ T j

/-- **Advance the input of pair `0` from `x` to `x'`**, two functions of the workspace that the
exchange leaves alone (an involution). -/
noncomputable def swapInput (x x' : A.W → (Fin q → Y) → X) :
    Equiv.Perm (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  Function.Involutive.toPerm
    (fun p => (p.1, Function.update p.2 A.pair0
      (Equiv.swap (x p.1.1.1 p.1.1.2.1) (x' p.1.1.1 p.1.1.2.1) (p.2 A.pair0).1, (p.2 A.pair0).2)))
    fun p => by
      obtain ⟨⟨⟨w, T, kp⟩, rr⟩, prs⟩ := p
      simp

/-- **The start of the program**: the kept pair `(x₀, 0)` moved into pair `0`, and its input set
to the first query of `P w`. -/
noncomputable def startPerm :
    Equiv.Perm (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  (A.keepIn q).trans (A.swapInput q (fun _ _ => KindAlg.x₀) fun w T => A.progQ P q w T 0)

/-- **Move the answer of pair `0` into entry `i` of the table** (an exchange). -/
def recordAns (i : Fin q) : Equiv.Perm (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  Function.Involutive.toPerm
    (fun p => (((p.1.1.1, (Function.update p.1.1.2.1 i (p.2 A.pair0).2, p.1.1.2.2)), p.1.2),
      Function.update p.2 A.pair0 ((p.2 A.pair0).1, p.1.1.2.1 i)))
    fun p => by
      obtain ⟨⟨⟨w, T, kp⟩, rr⟩, prs⟩ := p
      refine Prod.ext (Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) rfl) ?_
      · funext l
        by_cases hl : l = i
        · subst hl
          simp
        · simp [Function.update_of_ne hl]
      · simp

/-- **The program's step after its query `i`**: the answer moved into entry `i` of the table, the
input of pair `0` advanced to the next query of `P w`. -/
noncomputable def progPerm (i : Fin q) :
    Equiv.Perm (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  (A.recordAns q i).trans
    (A.swapInput q (fun w T => A.progQ P q w T i) fun w T => A.progQ P q w T ((i : ℕ) + 1))

/-- A Kraus map index of `A` as one of `A` followed by the program. -/
def castStep (k : StepIdx A.slots A.post) : StepIdx A.slots (A.post + q) :=
  ⟨k, by have := k.2; omega⟩

/-- The index embedding of `A`'s Kraus operators. -/
def someEmb : A.R ↪ Option A.R :=
  ⟨some, Option.some_injective _⟩

/-- The index embedding of the operator of a basis permutation. -/
def noneEmb : Unit ↪ Option A.R :=
  ⟨fun _ => none, fun _ _ _ => rfl⟩

/-- **The Kraus maps of `A` followed by the program**: `A`'s maps before its last; `A`'s last map
followed by the start of the program; the program's steps. -/
noncomputable def thenStep
    (k : StepIdx A.slots (A.post + q)) :
    KrausMap (Option A.R) (DReg (A.W × ProgW X Y q) A.width X Y Req Resp)
      (DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :=
  if h : (k : ℕ) < A.slots + A.post then
    (A.liftProg q (A.step ⟨k, by shape_omega⟩)).embedIdx A.someEmb
  else if h' : (k : ℕ) = A.slots + A.post then
    ((A.liftProg q (A.step lastStep)).permConj (Equiv.refl _) (A.startPerm P q)).embedIdx A.someEmb
  else
    (KrausMap.ofPerm (A.progPerm P q ⟨k - (A.slots + A.post) - 1, by have := k.2; omega⟩)).embedIdx A.noneEmb

/-- **The program's result read from a table** `T`: `P w` fed the table, `d w` if it wants more
answers than the table holds. -/
noncomputable def progRes (d : A.W → Res) (w : A.W) (T : Fin q → Y) : Res :=
  (OracleProgAns.result (P w) (answers q T q)).getD (d w)

/-- **The shape of the adversary followed by a classical oracle program** (`thenProgWith`): the
workspace with the program's register, `q` more post batches, the optional Kraus index. -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.thenProgS (s : AlgShape X Y Req Resp) (q : ℕ) :
    AlgShape X Y Req Resp where
  W := s.W × ProgW X Y q
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post + q
  budget := s.budget
  R := Option s.R

/-- **The adversary followed by a classical oracle program, with an output map** (module
docstring): `A`'s run, then `P` on `A`'s final workspace with basis-state queries in `q` extra
post batches; the output is `g` of `A`'s final workspace and the program's table of answers.

Running time: that of `A`, then `q` queries and `q + 1` basis permutations, each computing one
query of `P w` (`OracleProg.next` on at most `q` answers) and moving one answer, then `g`;
polynomial when `A`, `P` and `g` are. This running time is argued here, not proved in Lean. -/
noncomputable def thenProgWith {O' : Type} (_hP : ∀ w, (P w).QueriesLE q)
    (g : A.W → (Fin q → Y) → O') : AdaptiveIAlg (shA.thenProgS q) O' where
  kind w := A.kind w.1
  init := MState.reindex (A.progSplit q).symm (A.init.tensorKet (0, (KindAlg.x₀, 0)))
  step := A.thenStep P q
  out w := g w.1 w.2.1

variable (hP : ∀ w, (P w).QueriesLE q) {O' : Type} (g : A.W → (Fin q → Y) → O')

/-- The width of `A` followed by the program is `A`'s. -/
@[simp] theorem thenProgWith_width : (A.thenProgWith P q hP g).width = A.width := rfl

/-- The slots of `A` followed by the program are `A`'s. -/
@[simp] theorem thenProgWith_slots : (A.thenProgWith P q hP g).slots = A.slots := rfl

/-- `A` followed by the program has `q` more post batches than `A`. -/
@[simp] theorem thenProgWith_post : (A.thenProgWith P q hP g).post = A.post + q := rfl

/-- The query budget of `A` followed by the program is `A`'s. -/
@[simp] theorem thenProgWith_budget : (A.thenProgWith P q hP g).budget = A.budget := rfl

/-- **The queries of `A` followed by the program** on every branch: `A`'s and the program's `q`
batches of `width` queries. -/
theorem thenProgWith_queries :
    (A.thenProgWith P q hP g).width * ((A.thenProgWith P q hP g).budget + (A.thenProgWith P q hP g).post) =
      A.width * (A.budget + A.post) + A.width * q := by
  simp only [thenProgWith_width, thenProgWith_budget, thenProgWith_post]
  ring

/-- **`A` followed by the program is trace preserving** when `A` is: its other maps are basis
permutations. -/
theorem thenProgWith_tracePreserving (hA : A.TracePreserving) :
    (A.thenProgWith P q hP g).TracePreserving := by
  intro k
  change ∑ r, ((A.thenStep P q k).op r)ᴴ * (A.thenStep P q k).op r = 1
  unfold thenStep
  split_ifs
  · exact KrausMap.embedIdx_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (hA _) _)) _
  · exact KrausMap.embedIdx_tp
      (KrausMap.permConj_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (hA _) _)) _ _) _
  · exact KrausMap.embedIdx_tp (KrausMap.tp_ofPerm _) _

/-- **Every proof query of `A` followed by the program comes after at most `budget` query slots.** -/
theorem requestsAfterAtMost_thenProgWith :
    (A.thenProgWith P q hP g).RequestsAfterAtMost A.budget :=
  (A.thenProgWith P q hP g).requestsAfterAtMost_budget

/-! ### Kraus maps on the composed registers -/

section Composed

omit [Nonempty X] [AddGroup Y]

variable (C : Challenger X Y Req Resp) {shA₀ : AlgShape X Y Req Resp} (A₀ : AdaptiveIAlg shA₀ O)

/-- **A basis permutation of the adversary's registers on the composed registers**: the identity on
the query counter, the challenger's registers and the query register. -/
def composedPerm (π : Equiv.Perm (DReg A₀.W A₀.width X Y Req Resp)) :
    Equiv.Perm (QueryReg (A₀.toKindAlg.CW C) 1 X Y) :=
  (composedSplit C A₀).trans ((Equiv.prodCongr π (Equiv.refl _)).trans (composedSplit C A₀).symm)

/-- `composedPerm` acts on the adversary's registers alone. -/
theorem composedSplit_composedPerm (π : Equiv.Perm (DReg A₀.W A₀.width X Y Req Resp))
    (x : QueryReg (A₀.toKindAlg.CW C) 1 X Y) :
    composedSplit C A₀ (composedPerm C A₀ π x) = (π (composedSplit C A₀ x).1, (composedSplit C A₀ x).2) := by
  simp [composedPerm, Prod.map]

/-- Indexing the operators through an injection does not change the map on the composed registers. -/
theorem composedLift_embedIdx_apply {R R' : Type} [Fintype R] [Fintype R']
    (K : KrausMap R (DReg A₀.W A₀.width X Y Req Resp) (DReg A₀.W A₀.width X Y Req Resp))
    (f : R ↪ R') (ρ : Matrix (QueryReg (A₀.toKindAlg.CW C) 1 X Y)
      (QueryReg (A₀.toKindAlg.CW C) 1 X Y) ℂ) :
    composedLift C A₀ (K.embedIdx f) ρ = composedLift C A₀ K ρ :=
  ((lifts_composedLift C A₀ (K.embedIdx f)).congr_right fun σ => KrausMap.embedIdx_apply K f σ).apply_eq
    (lifts_composedLift C A₀ K) ρ

/-- **A Kraus map followed by a basis permutation, on the composed registers.** -/
theorem composedLift_permConj_apply {R : Type} [Fintype R]
    (K : KrausMap R (DReg A₀.W A₀.width X Y Req Resp) (DReg A₀.W A₀.width X Y Req Resp))
    (π : Equiv.Perm (DReg A₀.W A₀.width X Y Req Resp)) (ρ : Matrix (QueryReg (A₀.toKindAlg.CW C) 1 X Y)
      (QueryReg (A₀.toKindAlg.CW C) 1 X Y) ℂ) :
    composedLift C A₀ (K.permConj (Equiv.refl _) π) ρ =
      (composedLift C A₀ K ρ).submatrix (composedPerm C A₀ π).symm (composedPerm C A₀ π).symm := by
  have h : ((composedLift C A₀ K).permConj (Equiv.refl _) (composedPerm C A₀ π)).Lifts
      (composedSplit C A₀) (K.permConj (Equiv.refl _) π) :=
    (lifts_composedLift C A₀ K).permConj (fun _ => rfl)
      (perm_symm_lift _ (composedSplit_composedPerm C A₀ π))
  rw [(lifts_composedLift C A₀ _).apply_eq h ρ, KrausMap.permConj_apply]
  simp

/-- **A basis permutation on the composed registers.** -/
theorem composedLift_ofPerm_apply (π : Equiv.Perm (DReg A₀.W A₀.width X Y Req Resp))
    (ρ : Matrix (QueryReg (A₀.toKindAlg.CW C) 1 X Y) (QueryReg (A₀.toKindAlg.CW C) 1 X Y) ℂ) :
    composedLift C A₀ (KrausMap.ofPerm π) ρ =
      ρ.submatrix (composedPerm C A₀ π).symm (composedPerm C A₀ π).symm := by
  rw [(lifts_composedLift C A₀ _).apply_eq
    (KrausMap.lifts_ofPerm _ (perm_symm_lift _ (composedSplit_composedPerm C A₀ π))) ρ,
    KrausMap.ofPerm_apply]

end Composed

/-! ### Before the program, the composition lifts `A`'s -/

section Lift

variable (C : Challenger X Y Req Resp)

/-- The adversary's registers of `(thenProgWith A P q hP g).toKindAlg` as those of `A.toKindAlg`
and the program's registers. -/
def cntProg : DReg (A.thenProgWith P q hP g).toKindAlg.W A.width X Y Req Resp ≃
    DReg A.toKindAlg.W A.width X Y Req Resp × ProgW X Y q where
  toFun p := (((((p.1.1.1.1, p.1.1.2), p.1.2.1, p.1.2.2)), p.2), p.1.1.1.2)
  invFun r := (((((r.1.1.1.1, r.2), r.1.1.1.2), r.1.1.2.1, r.1.1.2.2)), r.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The composed registers of `(thenProgWith A P q hP g).toKindAlg` as those of `A.toKindAlg`
and the program's registers. -/
def cwProg : (A.thenProgWith P q hP g).toKindAlg.CW C ≃ A.toKindAlg.CW C × ProgW X Y q where
  toFun v := (⟨(A.cntProg P q hP g v.adv).1, v.chal⟩, (A.cntProg P q hP g v.adv).2)
  invFun u := ⟨(A.cntProg P q hP g).symm (u.1.adv, u.2), u.1.chal⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Nonempty X] [AddGroup Y] in
/-- `liftProg K` lifts `K` along the program's registers. -/
theorem lifts_liftProg {R : Type} [Fintype R]
    (K : KrausMap R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)) :
    (A.liftProg q K).Lifts (A.progSplit q) K :=
  KrausMap.lifts_reindex_tensorId _ _

/-- **A Kraus map of `A`, with the program's registers alongside, on the composed registers.** -/
theorem lifts_composedLift_liftProg {R : Type} [Fintype R]
    (K : KrausMap R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)) :
    (composedLift C (A.thenProgWith P q hP g) (A.liftProg q K)).Lifts
      (ReprogrammedCircuit.liftEquiv (A.cwProg P q hP g C)) (composedLift C A K) :=
  ((((A.lifts_liftProg q K).tensorId (Fin (A.budget + 2))
    (E₂ := liftProd (A.progSplit q) _) fun _ _ => rfl).reindex fun _ => rfl).tensorId _
    (E₂ := liftProd (A.cntProg P q hP g) _) fun _ _ => rfl).reindex fun _ => rfl

/-- **The Kraus maps before `A`'s last** are `A`'s, with the program's registers alongside. -/
theorem thenProgWith_step_of_lt {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots + A.post) :
    (A.thenProgWith P q hP g).step (A.castStep q k) = (A.liftProg q (A.step k)).embedIdx A.someEmb := by
  show A.thenStep P q _ = _
  unfold thenStep
  exact dif_pos hk

/-- **The adversary's Kraus maps before its last lift `A`'s** along the program's registers. -/
theorem lifts_step_thenProgWith {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots + A.post) :
    ((A.thenProgWith P q hP g).toKindAlg.step (A.castStep q k)).Lifts (A.cntProg P q hP g)
      (A.toKindAlg.step k) := by
  have hcopy : ((A.thenProgWith P q hP g).step (A.castStep q k)).Lifts (A.progSplit q) (A.step k) := by
    rw [A.thenProgWith_step_of_lt P q hP g hk]
    exact (A.lifts_liftProg q (A.step k)).embedIdx _
  have hcnt : ((A.thenProgWith P q hP g).cntKraus (A.castStep q k)).Lifts (A.cntProg P q hP g)
      (A.cntKraus k) :=
    (hcopy.tensorId (Fin (A.budget + 2)) (E₂ := liftProd (A.progSplit q) _) fun _ _ => rfl).reindex
      fun _ => rfl
  rw [toKindAlg_step, toKindAlg_step]
  refine KrausMap.Lifts.ite (fun _ => ?_) fun _ => hcnt
  have hσ : ∀ x, A.cntProg P q hP g ((Equiv.refl (A.thenProgWith P q hP g).CReg).symm x) =
      ((Equiv.refl A.CReg).symm (A.cntProg P q hP g x).1, (A.cntProg P q hP g x).2) := fun _ => rfl
  have hτ : ∀ x, A.cntProg P q hP g ((A.thenProgWith P q hP g).cntShift x) =
      (A.cntShift (A.cntProg P q hP g x).1, (A.cntProg P q hP g x).2) := fun x => by
    obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
    simp only [cntShift, AlgShape.cntShift, cntProg, Equiv.prodCongr_apply, Prod.map,
      Equiv.prodShear_apply, Equiv.refl_apply]
    rfl
  refine (hcnt.restrict fun x => ?_).permConj hσ (perm_symm_lift _ hτ)
  obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
  rfl

open ReprogrammedCircuit (liftEquiv Lifted)

/-- **The adversary's Kraus maps before `A`'s last, on the composed registers, lift `A`'s.** -/
theorem lifts_advKraus_thenProgWith {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots + A.post) :
    ((A.thenProgWith P q hP g).toKindAlg.advKraus C (A.castStep q k)).Lifts (liftEquiv (A.cwProg P q hP g C))
      (A.toKindAlg.advKraus C k) :=
  ((A.lifts_step_thenProgWith P q hP g hk).tensorId _ (E₂ := liftProd (A.cntProg P q hP g) _)
    fun _ _ => rfl).reindex fun _ => rfl

/-- **The request measurement lifts `A`'s** along the program's registers. -/
theorem lifts_measReq_thenProgWith (j : Fin A.slots) :
    ((A.thenProgWith P q hP g).toKindAlg.measReq C j).Lifts (liftEquiv (A.cwProg P q hP g C))
      (A.toKindAlg.measReq C j) := by
  refine KrausMap.Lifts.comp (KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_))
    (KrausMap.lifts_measureFn _ fun x => ?_)
  · obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    show liftEquiv (A.cwProg P q hP g C) (if A.kind w then _ else _) =
      ((if A.kind w then _ else _), _)
    by_cases hk : A.kind w = true
    · rw [if_pos hk, if_pos hk]
      rfl
    · rw [if_neg hk, if_neg hk]
  · obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

/-- **The writing of the reply lifts `A`'s** along the program's registers. -/
theorem lifts_writeReply_thenProgWith (j : Fin A.slots) :
    (KrausMap.ofPerm ((A.thenProgWith P q hP g).toKindAlg.writeReply C j)).Lifts
      (liftEquiv (A.cwProg P q hP g C)) (KrausMap.ofPerm (A.toKindAlg.writeReply C j)) := by
  refine KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_)
  obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
  show liftEquiv (A.cwProg P q hP g C) (if (u.logs j).isSome then _ else _) =
    ((if (u.logs j).isSome then _ else _), _)
  by_cases hl : (u.logs j).isSome = true
  · rw [if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl]

/-- **The adversary's queries lift `A`'s** along the program's registers. -/
theorem lifted_advQueries_thenProgWith 
    (ass : A.toKindAlg.CW C → List (Assignment X Y)) :
    Lifted (A.cwProg P q hP g C) ((A.thenProgWith P q hP g).toKindAlg.advQueries C
      fun v => ass (A.cwProg P q hP g C v).1) (A.toKindAlg.advQueries C ass) := by
  refine Lifted.concat_map (fun k => ReprogrammedCircuit.lifted_kraus ?_
    (ReprogrammedCircuit.lifted_rquery (fun v => rfl)
    (ReprogrammedCircuit.lifted_kraus ?_ (by exact ReprogrammedCircuit.lifted_nil)))) _
  all_goals
    refine KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_)
    obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

/-- **The challenger's queries lift those of `A`'s composition** along the program's registers. -/
theorem lifted_chalQueries_thenProgWith (j : Fin A.slots) :
    Lifted (A.cwProg P q hP g C) ((A.thenProgWith P q hP g).toKindAlg.chalQueries C j)
      (A.toKindAlg.chalQueries C j) := by
  unfold KindAlg.chalQueries
  refine Lifted.concat_map (fun i => ?_) _
  have hp : ∀ (π' : Equiv.Perm (QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y))
      (π : Equiv.Perm (QueryReg (A.toKindAlg.CW C) 1 X Y)),
      (∀ x, liftEquiv (A.cwProg P q hP g C) (π' x) = (π (liftEquiv (A.cwProg P q hP g C) x).1,
        (liftEquiv (A.cwProg P q hP g C) x).2)) →
      (KrausMap.ofPerm π').Lifts (liftEquiv (A.cwProg P q hP g C)) (KrausMap.ofPerm π) :=
    fun _ _ h => KrausMap.lifts_ofPerm _ (perm_symm_lift _ h)
  refine ReprogrammedCircuit.lifted_kraus (hp _ _ fun x => ?_)
    (ReprogrammedCircuit.lifted_rquery (fun v => rfl)
      (ReprogrammedCircuit.lifted_kraus (hp _ _ fun x => ?_)
        (by exact ReprogrammedCircuit.lifted_nil)))
  all_goals
    obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

/-- **Every slot lifts `A`'s slot** along the program's registers. -/
theorem lifted_slotCircBoth_thenProgWith (j : Fin A.slots) :
    Lifted (A.cwProg P q hP g C) ((A.thenProgWith P q hP g).toKindAlg.slotCircBoth C j)
      (A.toKindAlg.slotCircBoth C j) :=
  ReprogrammedCircuit.lifted_kraus (A.lifts_advKraus_thenProgWith P q hP g C (k := slotStep j)
    (by simp; omega))
    (ReprogrammedCircuit.lifted_kraus (A.lifts_measReq_thenProgWith P q hP g C j)
      ((A.lifted_chalQueries_thenProgWith P q hP g C j).append
        (ReprogrammedCircuit.lifted_kraus (A.lifts_writeReply_thenProgWith P q hP g C j)
        (A.lifted_advQueries_thenProgWith P q hP g C fun u => A.toKindAlg.advAss C j u.chal))))

/-- **`A`'s post batches lift `A`'s** along the program's registers. -/
theorem lifted_postCirc_thenProgWith (b : Fin A.post) :
    Lifted (A.cwProg P q hP g C) ((A.thenProgWith P q hP g).toKindAlg.postCirc C (Fin.castAdd q b))
      (A.toKindAlg.postCirc C b) :=
  ReprogrammedCircuit.lifted_kraus (A.lifts_advKraus_thenProgWith P q hP g C (k := postStep b) (by simp))
    (A.lifted_advQueries_thenProgWith P q hP g C fun u => A.toKindAlg.postAss C u.chal)

end Lift

/-! ### The run of the composition -/

section Run

variable (C : Challenger X Y Req Resp)

open ReprogrammedCircuit (liftEquiv Lifted)

/-- The blank program registers: the table `0` and the kept pair `(x₀, 0)`. -/
noncomputable def progBlank : ProgW X Y q := (0, (KindAlg.x₀, 0))

/-- **The initial state of `(thenProgWith A P q hP g).toKindAlg`** is that of `A.toKindAlg` with
the blank program registers. -/
theorem init_thenProgWith_apply (w w' : A.W) (z z' : ProgW X Y q) (n n' : Fin (A.budget + 2))
    (rq rq' : Req) (rs rs' : Option Resp) (pr pr' : Fin A.width → X × Y) :
    (A.thenProgWith P q hP g).toKindAlg.init.mat ((((w, z), n), rq, rs), pr)
        ((((w', z'), n'), rq', rs'), pr') =
      A.toKindAlg.init.mat ((((w, n), rq, rs), pr)) ((((w', n'), rq', rs'), pr')) *
        Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) (1 : ℂ) z z' := by
  show A.init.mat ((w, rq, rs), pr) ((w', rq', rs'), pr') *
      Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) (1 : ℂ) z z' * Matrix.single 0 0 (1 : ℂ) n n' =
    A.init.mat ((w, rq, rs), pr) ((w', rq', rs'), pr') * Matrix.single 0 0 (1 : ℂ) n n' *
      Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) (1 : ℂ) z z'
  ring

variable [Nonempty Y]

omit [Nonempty Y] in
/-- **The initial state of the composition of `thenProgWith A P q hP g`** is that of `A` with the
blank program registers. -/
theorem initSys_thenProgWith :
    ((A.thenProgWith P q hP g).toKindAlg.initSys C).mat =
      liftMat (liftEquiv (A.cwProg P q hP g C)) (A.toKindAlg.initSys C).mat
        (Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) 1) := by
  ext x y
  obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
  obtain ⟨⟨⟨⟨⟨⟨w', c'⟩, n'⟩, rq', rs'⟩, pr'⟩, u'⟩, qr'⟩ := y
  rw [liftMat_apply]
  simp only [KindAlg.initSys, MState.mix]
  rw [Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  set z : CRest X Y Req A.slots C.q C.Coins := (⟨fun _ => none, fun _ _ => (KindAlg.x₀, 0), ω⟩,
    fun _ => (KindAlg.x₀, 0))
  show (A.thenProgWith P q hP g).toKindAlg.init.mat ((((w, c), n), rq, rs), pr)
      ((((w', c'), n'), rq', rs'), pr') * Matrix.single z z (1 : ℂ) (u, qr) (u', qr') =
    A.toKindAlg.init.mat ((((w, n), rq, rs), pr)) ((((w', n'), rq', rs'), pr')) *
      Matrix.single z z (1 : ℂ) (u, qr) (u', qr') *
        Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) 1 c c'
  exact (congrArg (· * Matrix.single z z (1 : ℂ) (u, qr) (u', qr'))
    (A.init_thenProgWith_apply P q hP g w w' c c' n n' rq rq' rs rs' pr pr')).trans (by ring)

omit [Nonempty X] [Nonempty Y] in
/-- The run of a concatenation of two lists of circuits is the run of the second after the first. -/
theorem run_concat_append (H : X → Y) {V : Type} [Fintype V] [DecidableEq V]
    (l₁ l₂ : List (ReprogrammedCircuit V X Y)) (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    (ReprogrammedCircuit.concat (l₁ ++ l₂)).run H ρ =
      (ReprogrammedCircuit.concat l₂).run H ((ReprogrammedCircuit.concat l₁).run H ρ) := by
  induction l₁ generalizing ρ with
  | nil => rfl
  | cons c l ih =>
    rw [List.cons_append, ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append, ih,
      ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append]

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- A map over `Fin (m + n)` as the map over the first `m` indices, then over the last `n`. -/
theorem map_finRange_add {α : Type*} (m n : ℕ) (g : Fin (m + n) → α) :
    (List.finRange (m + n)).map g =
      (List.finRange m).map (fun i => g (Fin.castAdd n i)) ++
        (List.finRange n).map (fun j => g (Fin.natAdd m j)) := by
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  rfl

omit [Nonempty X] [Nonempty Y] in
/-- **Program steps after batches**: the circuit of `q` batches, each a Kraus map then a circuit
`Q`, then a last Kraus map, runs as the first Kraus map then `q` times `Q` followed by the next Kraus
map. -/
theorem run_batches_shift (H : X → Y) {V : Type} [Fintype V] [DecidableEq V] {R : Type} [Fintype R]
    (Q : ReprogrammedCircuit V X Y) :
    ∀ (n : ℕ) (s : Fin (n + 1) → KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y))
      (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ),
      (ReprogrammedCircuit.concat ((List.finRange n).map fun i =>
          ReprogrammedCircuit.kraus (s i.castSucc) Q) ++ .kraus (s (Fin.last n)) .nil).run H ρ =
        (ReprogrammedCircuit.concat ((List.finRange n).map fun i =>
          Q ++ .kraus (s i.succ) .nil)).run H (s 0 ρ)
  | 0, s, ρ => rfl
  | n + 1, s, ρ => by
    have ih := run_batches_shift H Q n (fun j => s j.succ) (Q.run H (s 0 ρ))
    simp only [List.finRange_succ, List.map_cons, List.map_map, ReprogrammedCircuit.concat,
      ReprogrammedCircuit.run_append, ReprogrammedCircuit.kraus_append,
      ReprogrammedCircuit.run, Function.comp_def, Fin.succ_castSucc, Fin.succ_last,
      Fin.castSucc_zero] at ih ⊢
    exact ih

end Run

/-! ### The steps after `A`'s -/

section Tail

variable (C : Challenger X Y Req Resp)

open ReprogrammedCircuit (liftEquiv Lifted RunsPerm)

/-- The Kraus map index `slots + post + j` of `A` followed by the program: `j = 0` is `A`'s last
map with the start of the program, `j = i + 1` the program's step after its query `i`. -/
def progIdx (j : Fin (q + 1)) : StepIdx A.slots (A.post + q) :=
  ⟨A.slots + A.post + j, by have := j.2; omega⟩

omit [Nonempty X] [AddGroup Y] in
/-- The Kraus map before the program's batch `i` is `progIdx i`. -/
theorem postStep_natAdd (i : Fin q) :
    (postStep (Fin.natAdd A.post i) : StepIdx A.slots (A.post + q)) = A.progIdx q i.castSucc :=
  Fin.ext (by simp [progIdx]; omega)

omit [Nonempty X] [AddGroup Y] in
/-- The last Kraus map is the program's step after its last query. -/
theorem lastStep_eq_progIdx :
    (lastStep : StepIdx A.slots (A.post + q)) = A.progIdx q (Fin.last q) :=
  Fin.ext (by simp [progIdx]; omega)

/-- **The Kraus map before the program's first batch**: `A`'s last map, then the start of the program. -/
theorem thenProgWith_step_start :
    (A.thenProgWith P q hP g).step (A.progIdx q 0) =
      ((A.liftProg q (A.step lastStep)).permConj (Equiv.refl _) (A.startPerm P q)).embedIdx
        A.someEmb := by
  show A.thenStep P q _ = _
  unfold thenStep
  rw [dif_neg (by simp [progIdx]), dif_pos (by simp [progIdx])]

/-- **The Kraus map after the program's batch `i`** is the program's step after its query `i`. -/
theorem thenProgWith_step_succ (i : Fin q) :
    (A.thenProgWith P q hP g).step (A.progIdx q i.succ) =
      (KrausMap.ofPerm (A.progPerm P q i)).embedIdx A.noneEmb := by
  show A.thenStep P q _ = _
  unfold thenStep
  rw [dif_neg (by simp [progIdx]), dif_neg (by simp [progIdx])]
  congr 3
  exact Fin.ext (by simp [progIdx])

/-- The program's steps come after the slots. -/
theorem not_progIdx_lt (j : Fin (q + 1)) :
    ¬ ((A.progIdx q j : StepIdx (A.thenProgWith P q hP g).slots (A.thenProgWith P q hP g).post) : ℕ) <
      (A.thenProgWith P q hP g).slots := by
  simp [progIdx]
  omega

/-- **The program's steps on the composed registers** are its Kraus maps with the identity on the
query counter, the challenger's registers and the query register. -/
theorem advKraus_progIdx (j : Fin (q + 1)) :
    (A.thenProgWith P q hP g).toKindAlg.advKraus C (A.progIdx q j) =
      composedLift C (A.thenProgWith P q hP g) ((A.thenProgWith P q hP g).step (A.progIdx q j)) :=
  advKraus_eq_composedLift C _ (A.not_progIdx_lt P q hP g j)

/-- **`A`'s last Kraus map with the start of the program, on the composed registers**: on a state
with the program's registers alongside, `A`'s last map, then the start of the program. -/
theorem advKraus_start_apply (ρ : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y)
      (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ) (τ : Matrix (ProgW X Y q) (ProgW X Y q) ℂ) :
    (A.thenProgWith P q hP g).toKindAlg.advKraus C (A.progIdx q 0)
        (liftMat (liftEquiv (A.cwProg P q hP g C)) ρ τ) =
      (liftMat (liftEquiv (A.cwProg P q hP g C)) (composedLift C A (A.step lastStep) ρ) τ).submatrix
        (composedPerm C (A.thenProgWith P q hP g) (A.startPerm P q)).symm
        (composedPerm C (A.thenProgWith P q hP g) (A.startPerm P q)).symm := by
  rw [A.advKraus_progIdx P q hP g C 0, A.thenProgWith_step_start P q hP g]
  refine (composedLift_embedIdx_apply C (A.thenProgWith P q hP g) (R := A.R) _ A.someEmb _).trans ?_
  refine (composedLift_permConj_apply C (A.thenProgWith P q hP g) (R := A.R) _ _ _).trans ?_
  rw [A.lifts_composedLift_liftProg P q hP g C]

/-- **The program's step after its query `i`, on the composed registers**, is a basis
permutation. -/
theorem runsPerm_progStep (H : X → Y) (i : Fin q) :
    (ReprogrammedCircuit.kraus ((A.thenProgWith P q hP g).toKindAlg.advKraus C (A.progIdx q i.succ))
      .nil).RunsPerm H (composedPerm C (A.thenProgWith P q hP g) (A.progPerm P q i)) := fun ρ => by
  rw [ReprogrammedCircuit.run, ReprogrammedCircuit.run,
    A.advKraus_progIdx P q hP g C i.succ, A.thenProgWith_step_succ P q hP g]
  exact (composedLift_embedIdx_apply C (A.thenProgWith P q hP g) (R := Unit) _ A.noneEmb _).trans
    (composedLift_ofPerm_apply C (A.thenProgWith P q hP g) _ _)

/-- The post-phase queries of `A` followed by the program. -/
noncomputable def postQueries : ReprogrammedCircuit ((A.thenProgWith P q hP g).toKindAlg.CW C) X Y :=
  (A.thenProgWith P q hP g).toKindAlg.advQueries C fun v => (A.thenProgWith P q hP g).toKindAlg.postAss C v.chal

/-- The post-phase queries as one basis permutation. -/
noncomputable def postQueriesPerm (H : X → Y) :
    Equiv.Perm (QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y) :=
  ((List.finRange A.width).map ((A.thenProgWith P q hP g).toKindAlg.advStepPerm C H
    fun v => (A.thenProgWith P q hP g).toKindAlg.postAss C v.chal)).foldr (fun π acc => π.trans acc)
    (Equiv.refl _)

/-- **The post-phase queries run the basis permutation `postQueriesPerm`.** -/
theorem runsPerm_postQueries (H : X → Y) :
    (A.postQueries P q hP g C).RunsPerm H (A.postQueriesPerm P q hP g C H) :=
  ReprogrammedCircuit.runsPerm_concat (fun k => fun ρ =>
    (A.thenProgWith P q hP g).toKindAlg.run_advSub C H _ k ρ) _

/-- **The basis permutation after `A`'s last Kraus map**: the start of the program, then `q` times
the post-phase queries followed by the program's step. -/
noncomputable def tailPerm (H : X → Y) :
    Equiv.Perm (QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y) :=
  (composedPerm C (A.thenProgWith P q hP g) (A.startPerm P q)).trans
    (((List.finRange q).map fun i => (A.postQueriesPerm P q hP g C H).trans
      (composedPerm C (A.thenProgWith P q hP g) (A.progPerm P q i))).foldr (fun π acc => π.trans acc)
      (Equiv.refl _))

/-- **The run of the composition of `A` followed by the program**: the final state of `A`'s
composition with the blank program registers, moved by the basis permutation `tailPerm`. -/
theorem run_fullCircBoth_thenProgWith (H : X → Y) :
    ((A.thenProgWith P q hP g).toKindAlg.fullCircBoth C).run H
        ((A.thenProgWith P q hP g).toKindAlg.initSys C).mat =
      (liftMat (liftEquiv (A.cwProg P q hP g C))
        ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat)
        (Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) 1)).submatrix
        (A.tailPerm P q hP g C H).symm (A.tailPerm P q hP g C H).symm := by
  set s : Fin (q + 1) → KrausMap (A.thenProgWith P q hP g).R (QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y)
      (QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y) := fun j => (A.thenProgWith P q hP g).toKindAlg.advKraus C (A.progIdx q j)
  have hposts : (List.finRange (A.thenProgWith P q hP g).toKindAlg.post).map ((A.thenProgWith P q hP g).toKindAlg.postCirc C) =
      (List.finRange A.post).map (fun i => (A.thenProgWith P q hP g).toKindAlg.postCirc C (Fin.castAdd q i)) ++
        (List.finRange q).map (fun i => ReprogrammedCircuit.kraus (s i.castSucc)
          (A.postQueries P q hP g C)) := by
    refine (map_finRange_add A.post q ((A.thenProgWith P q hP g).toKindAlg.postCirc C)).trans ?_
    congr 1
    refine List.map_congr_left fun i _ => ?_
    exact congrArg (fun k : StepIdx A.slots (A.post + q) =>
      ReprogrammedCircuit.kraus ((A.thenProgWith P q hP g).toKindAlg.advKraus C k) (A.postQueries P q hP g C))
      (A.postStep_natAdd q i)
  have hlast : ((A.thenProgWith P q hP g).toKindAlg.advKraus C lastStep) = s (Fin.last q) := by
    show (A.thenProgWith P q hP g).toKindAlg.advKraus C (lastStep : StepIdx A.slots (A.post + q)) = _
    rw [A.lastStep_eq_progIdx q]
  have hpre : (ReprogrammedCircuit.concat ((List.finRange A.post).map fun i =>
      (A.thenProgWith P q hP g).toKindAlg.postCirc C (Fin.castAdd q i))).run H
        ((ReprogrammedCircuit.concat ((List.finRange (A.thenProgWith P q hP g).toKindAlg.slots).map fun j =>
          (A.thenProgWith P q hP g).toKindAlg.slotCircBoth C j)).run H ((A.thenProgWith P q hP g).toKindAlg.initSys C).mat) =
      liftMat (liftEquiv (A.cwProg P q hP g C)) ((preCirc C A.toKindAlg).run H
        (A.toKindAlg.initSys C).mat)
        (Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) 1) := by
    rw [A.initSys_thenProgWith P q hP g C]
    erw [(Lifted.concat_map (fun j => A.lifted_slotCircBoth_thenProgWith P q hP g C j) _).run H,
      (Lifted.concat_map (fun b => A.lifted_postCirc_thenProgWith P q hP g C b) _).run H]
    rw [preCirc, ReprogrammedCircuit.run_append]
  have hA : (A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat =
      composedLift C A (A.step lastStep) ((preCirc C A.toKindAlg).run H
        (A.toKindAlg.initSys C).mat) := by
    rw [fullCircBoth_eq, ReprogrammedCircuit.run_append]
    simp only [ReprogrammedCircuit.run]
    exact congrArg (fun K => KrausMap.apply K ((preCirc C A.toKindAlg).run H
      (A.toKindAlg.initSys C).mat)) (advKraus_eq_composedLift C A (k := lastStep) (by simp))
  have htail : (ReprogrammedCircuit.concat ((List.finRange q).map fun i =>
      A.postQueries P q hP g C ++ .kraus (s i.succ) .nil)).RunsPerm H
      (((List.finRange q).map fun i => (A.postQueriesPerm P q hP g C H).trans
        (composedPerm C (A.thenProgWith P q hP g) (A.progPerm P q i))).foldr (fun π acc => π.trans acc) (Equiv.refl _)) :=
    ReprogrammedCircuit.runsPerm_concat (fun i =>
      (A.runsPerm_postQueries P q hP g C H).append (A.runsPerm_progStep P q hP g C H i)) _
  rw [fullCircBoth_eq, preCirc, ReprogrammedCircuit.run_append, ReprogrammedCircuit.run_append,
    hposts, run_concat_append, hpre, hlast, ← ReprogrammedCircuit.run_append]
  refine (run_batches_shift H (A.postQueries P q hP g C) q s _).trans ?_
  rw [htail]
  simp only [s]
  erw [A.advKraus_start_apply P q hP g C]
  rw [← hA, submatrix_submatrix]
  rfl

end Tail

/-! ### The program's run on a basis state -/

section Forward

open Quantum.OracleProg (tab xs)

omit [Nonempty X] [AddGroup Y] in
/-- `keepIn` on a basis state. -/
theorem keepIn_apply (w : A.W) (z : ProgW X Y q) (rr : Req × Option Resp)
    (prs : Fin A.width → X × Y) :
    A.keepIn q (((w, z), rr), prs) =
      (((w, (z.1, prs A.pair0)), rr), Function.update prs A.pair0 z.2) :=
  rfl

omit [Nonempty X] [AddGroup Y] in
/-- `swapInput` on a basis state. -/
theorem swapInput_apply (x x' : A.W → (Fin q → Y) → X) (w : A.W) (z : ProgW X Y q)
    (rr : Req × Option Resp) (prs : Fin A.width → X × Y) :
    A.swapInput q x x' (((w, z), rr), prs) =
      (((w, z), rr), Function.update prs A.pair0
        (Equiv.swap (x w z.1) (x' w z.1) (prs A.pair0).1, (prs A.pair0).2)) :=
  rfl

/-- **The start of the program on the blank program registers**: pair `0` holds the first query
of `P w` with answer `0`. -/
theorem startPerm_apply_blank (w : A.W) (rr : Req × Option Resp) (prs : Fin A.width → X × Y) :
    A.startPerm P q (((w, progBlank q), rr), prs) =
      (((w, (0, prs A.pair0)), rr), Function.update prs A.pair0 (A.progQ P q w 0 0, 0)) := by
  simp only [startPerm, Equiv.trans_apply, keepIn_apply, swapInput_apply, progBlank,
    Function.update_self, Function.update_idem, Equiv.swap_apply_left]

omit [Nonempty X] [AddGroup Y] in
/-- `recordAns` on a basis state. -/
theorem recordAns_apply (i : Fin q) (w : A.W) (T : Fin q → Y) (kp : X × Y) (rr : Req × Option Resp)
    (prs : Fin A.width → X × Y) :
    A.recordAns q i (((w, (T, kp)), rr), prs) =
      (((w, (Function.update T i (prs A.pair0).2, kp)), rr),
        Function.update prs A.pair0 ((prs A.pair0).1, T i)) :=
  rfl

/-- **The program's step after query `i` on a basis state of its run**: with the table holding the
answers to the first `i` queries of `P w` against `G` and pair `0` the answer to query `i`, the
table holds the first `i + 1` answers and pair `0` the next query with answer `0`. -/
theorem progPerm_apply_tab (G : X → Y) (i : Fin q) (w : A.W) (kp : X × Y) (rr : Req × Option Resp)
    (prs : Fin A.width → X × Y)
    (hp : prs A.pair0 = (xs (P w) KindAlg.x₀ G i, G (xs (P w) KindAlg.x₀ G i))) :
    A.progPerm P q i (((w, (tab (P w) q KindAlg.x₀ G i, kp)), rr), prs) =
      (((w, (tab (P w) q KindAlg.x₀ G (i + 1), kp)), rr), Function.update prs A.pair0
        (xs (P w) KindAlg.x₀ G (i + 1), 0)) := by
  have hu : Function.update (tab (P w) q KindAlg.x₀ G i) i (prs A.pair0).2 =
      tab (P w) q KindAlg.x₀ G (i + 1) := by
    rw [hp]
    exact Quantum.OracleProg.update_tab (P w) q KindAlg.x₀ G i.2
  simp only [progPerm, Equiv.trans_apply, recordAns_apply, swapInput_apply, hu,
    Function.update_self, Function.update_idem]
  have h1 : A.progQ P q w (tab (P w) q KindAlg.x₀ G (i + 1)) i = (prs A.pair0).1 := by
    rw [hp]
    exact Quantum.OracleProg.nextQ_tab (P w) q KindAlg.x₀ G (by omega) (by omega)
  have h2 : A.progQ P q w (tab (P w) q KindAlg.x₀ G (i + 1)) ((i : ℕ) + 1) =
      xs (P w) KindAlg.x₀ G (i + 1) :=
    Quantum.OracleProg.nextQ_tab (P w) q KindAlg.x₀ G le_rfl (by omega)
  rw [h1, Equiv.swap_apply_left, h2, Quantum.OracleProg.tab_self (P w) q KindAlg.x₀ G i.2]

variable (C : Challenger X Y Req Resp)

/-- **The registers in the run of the program after `i` queries**: `A`'s workspace `w`, the table of
the first `i` answers of `P w` against `G`, pair `0` at query `i` with answer `0`, and the
challenger's registers `u`. -/
def ProgAt (w : A.W) (u : A.toKindAlg.CCl C) (G : X → Y) (i : ℕ)
    (y : QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y) : Prop :=
  y.1.adv.workspace.1.1 = w ∧ y.1.adv.workspace.1.2.1 = tab (P w) q KindAlg.x₀ G i ∧
    y.1.adv.2 A.pair0 = (xs (P w) KindAlg.x₀ G i, 0) ∧ y.1.chal = u

/-- **One batch of the program**: the post-phase queries, then the program's step after query `i`, take the registers after `i` queries to those after `i + 1`. -/
theorem progAt_succ (H : X → Y) (w : A.W) (u : A.toKindAlg.CCl C) (i : Fin q)
    {y : QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y}
    (hy : A.ProgAt P q hP g C w u (H.reprogram (A.toKindAlg.postAss C u)) i y) :
    A.ProgAt P q hP g C w u (H.reprogram (A.toKindAlg.postAss C u)) (i + 1)
      (((A.postQueriesPerm P q hP g C H).trans
        (composedPerm C (A.thenProgWith P q hP g) (A.progPerm P q i))) y) := by
  obtain ⟨⟨⟨⟨⟨⟨w', T, kp⟩, n⟩, rr⟩, prs⟩, u'⟩, qr⟩ := y
  obtain ⟨h1, h2, h3, h4⟩ := hy
  simp only at h1 h2 h3 h4
  subst h1 h2 h4
  rw [Equiv.trans_apply, postQueriesPerm]
  erw [KindAlg.advQueriesPerm_chal (A.thenProgWith P q hP g).toKindAlg C H
    ((A.thenProgWith P q hP g).toKindAlg.postAss C)]
  have hp := A.progPerm_apply_tab P q (H.reprogram (A.toKindAlg.postAss C u')) i w' kp rr
    (fun j => ((prs j).1, (prs j).2 + H.reprogram (A.toKindAlg.postAss C u') (prs j).1))
    (by simp only [h3, zero_add])
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show ((A.progPerm P q i _).1.1.2.1) = _
    erw [hp]
  · show ((A.progPerm P q i _).2 A.pair0) = _
    erw [hp]
    simp

/-- **The start of the program**: on `A`'s composed registers with the blank program registers, the start of the program gives the registers after `0` queries. -/
theorem progAt_start (H : X → Y) (a : QueryReg (A.toKindAlg.CW C) 1 X Y) :
    A.ProgAt P q hP g C a.1.adv.workspace.1 a.1.chal (H.reprogram (A.toKindAlg.postAss C a.1.chal)) 0
      (composedPerm C (A.thenProgWith P q hP g) (A.startPerm P q)
        ((ReprogrammedCircuit.liftEquiv (A.cwProg P q hP g C)).symm (a, progBlank q))) := by
  obtain ⟨⟨⟨⟨⟨w, n⟩, rr⟩, prs⟩, u⟩, qr⟩ := a
  have hs := A.startPerm_apply_blank P q w rr prs
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show ((A.startPerm P q _).1.1.2.1) = _
    erw [hs]
    exact (Quantum.OracleProg.tab_zero (P w) q KindAlg.x₀ _).symm
  · show ((A.startPerm P q _).2 A.pair0) = _
    erw [hs]
    rw [Quantum.OracleProg.xs_zero]
    rfl

/-- **Batches `m`, …, `m + l.length - 1` of the program** take the registers after `m` queries to those after `m + l.length`. -/
theorem progAt_foldr (H : X → Y) (w : A.W) (u : A.toKindAlg.CCl C) :
    ∀ (l : List (Fin q)) (m : ℕ), l.map Fin.val = List.range' m l.length →
      ∀ y, A.ProgAt P q hP g C w u (H.reprogram (A.toKindAlg.postAss C u)) m y →
      A.ProgAt P q hP g C w u (H.reprogram (A.toKindAlg.postAss C u)) (m + l.length)
        ((l.map fun i => (A.postQueriesPerm P q hP g C H).trans
          (composedPerm C (A.thenProgWith P q hP g) (A.progPerm P q i))).foldr
          (fun π acc => π.trans acc) (Equiv.refl _) y)
  | [], m, _, y, hy => hy
  | i :: l, m, hl, y, hy => by
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl
    simp only [List.map_cons, List.foldr_cons, Equiv.trans_apply, List.length_cons]
    have h1 := A.progAt_succ P q hP g C H w u i (hl.1 ▸ hy)
    have h2 := progAt_foldr H w u l (m + 1) hl.2 _ (by rw [← hl.1]; exact h1)
    rw [show m + (l.length + 1) = m + 1 + l.length by omega]
    exact h2

/-- **The program's table after `A`'s run**: on the basis state with `A`'s composed registers `a`
and the blank program registers, the permutation after `A`'s last Kraus map ends with output `g`
of `A`'s workspace and the table of the `q` answers of `P` on it against `H` reprogrammed by the
final assignments. -/
theorem out_tailPerm (H : X → Y) (a : QueryReg (A.toKindAlg.CW C) 1 X Y) :
    (A.thenProgWith P q hP g).toKindAlg.out (A.tailPerm P q hP g C H
        ((ReprogrammedCircuit.liftEquiv (A.cwProg P q hP g C)).symm (a, progBlank q))).1.adv.workspace =
      g a.1.adv.workspace.1 (tab (P a.1.adv.workspace.1) q KindAlg.x₀
        (H.reprogram (A.toKindAlg.postAss C a.1.chal)) q) := by
  have h := A.progAt_foldr P q hP g C H a.1.adv.workspace.1 a.1.chal (List.finRange q) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange]) _
    (A.progAt_start P q hP g C H a)
  rw [List.length_finRange, Nat.zero_add] at h
  obtain ⟨h1, h2, -, -⟩ := h
  change g _ _ = _
  simp only [tailPerm, Equiv.trans_apply]
  rw [h1, h2]

/-- **The challenger's registers after `A`'s run are left alone** by the permutation after `A`'s
last Kraus map. -/
theorem chal_tailPerm (H : X → Y) (a : QueryReg (A.toKindAlg.CW C) 1 X Y) :
    (A.tailPerm P q hP g C H
        ((ReprogrammedCircuit.liftEquiv (A.cwProg P q hP g C)).symm (a, progBlank q))).1.chal =
      a.1.chal := by
  have h := A.progAt_foldr P q hP g C H a.1.adv.workspace.1 a.1.chal (List.finRange q) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange]) _
    (A.progAt_start P q hP g C H a)
  obtain ⟨-, -, -, h4⟩ := h
  exact h4

omit [Nonempty X] in
include hP in
/-- **The program's result read from its table of answers** against an oracle is its run on the
oracle, when it makes at most `q` queries. -/
theorem progRes_tab (d : A.W → Res) (w : A.W) (G : X → Y) (x₀ : X) :
    A.progRes P q d w (tab (P w) q x₀ G q) = (P w).run G := by
  unfold progRes
  rw [Quantum.OracleProg.result_answers_tab (P w) q x₀ G (hP w G)]
  rfl

end Forward

/-! ### The output law -/

section Law

variable (C : Challenger X Y Req Resp) [Nonempty Y]

open ReprogrammedCircuit (liftEquiv)
open Quantum.OracleProg (tab)

omit [Nonempty Y] in
/-- **The diagonal of the final state of the composition of `A` followed by the program**, summed
against a function `G` of the output and the challenger's registers, is the diagonal of the final
state of `A`'s composition summed against `G` of `g` of `A`'s workspace and the program's table
of answers against `H` reprogrammed by the final assignments, and the challenger's registers. -/
theorem sum_diag_thenProgWith (H : X → Y) (G : O' → A.toKindAlg.CCl C → ℝ≥0∞) :
    ∑ x : QueryReg ((A.thenProgWith P q hP g).toKindAlg.CW C) 1 X Y,
        G ((A.thenProgWith P q hP g).toKindAlg.out x.1.adv.workspace) x.1.chal *
          ENNReal.ofReal (((A.thenProgWith P q hP g).toKindAlg.fullCircBoth C).run H
            ((A.thenProgWith P q hP g).toKindAlg.initSys C).mat x x).re =
      ∑ a : QueryReg (A.toKindAlg.CW C) 1 X Y,
        G (g a.1.adv.workspace.1 (tab (P a.1.adv.workspace.1) q KindAlg.x₀
            (H.reprogram (A.toKindAlg.postAss C a.1.chal)) q)) a.1.chal *
          ENNReal.ofReal ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat a a).re := by
  rw [A.run_fullCircBoth_thenProgWith P q hP g C H]
  simp only [Matrix.submatrix_apply]
  rw [← Equiv.sum_comp (A.tailPerm P q hP g C H)]
  simp only [Equiv.symm_apply_apply]
  rw [← (liftEquiv (A.cwProg P q hP g C)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (progBlank (X := X) (Y := Y) q)]
  · rw [liftMat_apply, Equiv.apply_symm_apply, Matrix.single_apply_same, mul_one,
      A.out_tailPerm P q hP g C H a, A.chal_tailPerm P q hP g C H a]
  · intro z _ hz
    rw [liftMat_apply, Equiv.apply_symm_apply]
    simp [Ne.symm hz]
  · simp

/-- **The composition with the ancilla, summed against a function of the composed registers**, is
the sum over the composed registers without the ancilla. -/
theorem sum_indicator_composeBothOut {ksK : KindShape X Y Req Resp} {K : KindAlg ksK O} {O' : Type} (f : K.CW C → O')
    (H : X → Y) (S : Set (K.CW C)) [DecidablePred (· ∈ S)] :
    ∑ i, Set.indicator {i | i.1.1 ∈ S}
        (fun i => ENNReal.ofReal ((K.composeBothOut C f).final H i i).re) i =
      ∑ x : QueryReg (K.CW C) 1 X Y, (if x.1 ∈ S then 1 else 0) *
        ENNReal.ofReal ((K.fullCircBoth C).run H (K.initSys C).mat x x).re := by
  have hB := sum_liftMat_diag (ancSplit (K.CW C) X Y)
    (ReprogrammedCircuit.posSemidef_run H (K.fullCircBoth C) (K.initSys C).posSemidef)
    (posSemidef_reprogAnc KindAlg.x₀) (trace_reprogAnc KindAlg.x₀)
    (fun x => if x.1 ∈ S then 1 else 0)
  rw [← hB]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [final_composeBothOut]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  split_ifs <;> simp_all [ancSplit]

end Law

/-! ### Termination -/

section Budget

variable [Nonempty Y]

/-- **The final state of the composition of `A` followed by the program has `A`'s trace**: the
program's steps are basis permutations. -/
theorem trace_final_thenProgWith (C : Challenger X Y Req Resp) (H : X → Y) :
    (((A.thenProgWith P q hP g).compose C).final H).trace = ((A.compose C).final H).trace := by
  have hB : ((A.thenProgWith P q hP g).compose C).final H = withAnc KindAlg.x₀
      (((A.thenProgWith P q hP g).toKindAlg.fullCircBoth C).run H
        ((A.thenProgWith P q hP g).toKindAlg.initSys C).mat) :=
    KindAlg.final_composeBothOut C (A.thenProgWith P q hP g).toKindAlg id H
  have hA : (A.compose C).final H = withAnc KindAlg.x₀
      ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat) :=
    KindAlg.final_composeBothOut C A.toKindAlg id H
  rw [hB, hA, KindAlg.trace_withAnc, KindAlg.trace_withAnc,
    A.run_fullCircBoth_thenProgWith P q hP g C H]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp (A.tailPerm P q hP g C H).symm
    fun x => liftMat (ReprogrammedCircuit.liftEquiv (A.cwProg P q hP g C))
      ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat)
      (Matrix.single (progBlank (X := X) (Y := Y) q) (progBlank (X := X) (Y := Y) q) 1) x x]
  rw [← (ReprogrammedCircuit.liftEquiv (A.cwProg P q hP g C)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (progBlank (X := X) (Y := Y) q)]
  · rw [liftMat_apply, Equiv.apply_symm_apply, Matrix.single_apply_same, mul_one]
  · intro z _ hz
    rw [liftMat_apply, Equiv.apply_symm_apply]
    simp [Ne.symm hz]
  · simp

/-- **`A` followed by the program stays within its budget** when `A` does: its run never fails to
terminate where `A`'s does not (`withinBudget_iff`). -/
theorem withinBudget_thenProgWith (hA : A.WithinBudget) :
    (A.thenProgWith P q hP g).WithinBudget := by
  classical
  rw [withinBudget_iff] at hA ⊢
  intro C H
  rw [Alg.outLaw_none, A.trace_final_thenProgWith P q hP g C H, ← Alg.outLaw_none]
  exact hA C H

end Budget

end With

/-! ### A program with a bit as its result -/

section Bit

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (P : A.W → GordieHowe.OracleProg X Y Bool) (q : ℕ)

open Quantum.OracleProg (ProgW)

/-- **The adversary followed by a classical oracle program** (module docstring): `A`'s run, then
`P` on `A`'s final workspace with basis-state queries in `q` extra post batches; the output is the
program's result (`false` if it wants more answers than the table holds, which `hP` excludes).

Running time: that of `A`, then `q` queries and `q + 1` basis permutations, each computing one
query of `P w` (`OracleProg.next` on at most `q` answers) and moving one answer; polynomial when
`A` and `P` are. This running time is argued here, not proved in Lean. -/
noncomputable def thenProg (hP : ∀ w, (P w).QueriesLE q) :=
  A.thenProgWith P q hP (A.progRes P q fun _ => false)

variable (hP : ∀ w, (P w).QueriesLE q)

/-- The width of `A` followed by the program is `A`'s. -/
@[simp] theorem thenProg_width : (A.thenProg P q hP).width = A.width := rfl

/-- The slots of `A` followed by the program are `A`'s. -/
@[simp] theorem thenProg_slots : (A.thenProg P q hP).slots = A.slots := rfl

/-- `A` followed by the program has `q` more post batches than `A`. -/
@[simp] theorem thenProg_post : (A.thenProg P q hP).post = A.post + q := rfl

/-- The query budget of `A` followed by the program is `A`'s. -/
@[simp] theorem thenProg_budget : (A.thenProg P q hP).budget = A.budget := rfl

/-- **The queries of `A` followed by the program** on every branch: `A`'s and the program's `q`
batches of `width` queries. -/
theorem thenProg_queries :
    (A.thenProg P q hP).width * ((A.thenProg P q hP).budget + (A.thenProg P q hP).post) =
      A.width * (A.budget + A.post) + A.width * q :=
  A.thenProgWith_queries P q hP _

/-- **`A` followed by the program is trace preserving** when `A` is: its other maps are basis
permutations. -/
theorem thenProg_tracePreserving (hA : A.TracePreserving) :
    (A.thenProg P q hP).TracePreserving :=
  A.thenProgWith_tracePreserving P q hP _ hA

/-- **Every proof query of `A` followed by the program comes after at most `budget` query slots.** -/
theorem requestsAfterAtMost_thenProg :
    (A.thenProg P q hP).RequestsAfterAtMost A.budget :=
  (A.thenProg P q hP).requestsAfterAtMost_budget

variable (C : Challenger X Y Req Resp)

/-- **The diagonal of the final state of the composition of `A` followed by the program**, summed
against a function of the output, is the diagonal of the final state of `A`'s composition summed
against the same function of the program's result on `A`'s workspace, run against `H`
reprogrammed by the final assignments. -/
theorem sum_diag_thenProg (H : X → Y) (g : Bool → ℝ≥0∞) :
    ∑ x : QueryReg ((A.thenProg P q hP).toKindAlg.CW C) 1 X Y,
        g ((A.thenProg P q hP).toKindAlg.out x.1.adv.workspace) *
          ENNReal.ofReal (((A.thenProg P q hP).toKindAlg.fullCircBoth C).run H
            ((A.thenProg P q hP).toKindAlg.initSys C).mat x x).re =
      ∑ a : QueryReg (A.toKindAlg.CW C) 1 X Y,
        g ((P a.1.adv.workspace.1).run (H.reprogram (A.toKindAlg.postAss C a.1.chal))) *
          ENNReal.ofReal ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat a a).re := by
  refine (A.sum_diag_thenProgWith P q hP _ C H fun b _ => g b).trans
    (Finset.sum_congr rfl fun a _ => ?_)
  rw [A.progRes_tab P q hP]

variable [Nonempty Y]

/-- **The output law of `A` followed by the program** (main result): against every challenger and
oracle `H`, the probability that the composition outputs `b` is the probability that the
composition of `A` ends with composed registers `v` on which `P` of `A`'s workspace, run against `H`
reprogrammed by the final assignments, returns `b`. -/
theorem outLaw_thenProg (H : X → Y) (b : Bool) :
    ((A.thenProg P q hP).compose C).outLaw H (some b) =
      ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v, o = some v ∧
          (P v.adv.workspace.1).run (H.reprogram (A.toKindAlg.postAss C v.chal)) = b} := by
  classical
  rw [Alg.outLaw_some_eq_sum, Alg.toOuterMeasure_outLaw_some]
  have hL := sum_indicator_composeBothOut C (K := (A.thenProg P q hP).toKindAlg)
    (fun v => (A.thenProg P q hP).toKindAlg.out v.adv.workspace) H
    {v | (A.thenProg P q hP).toKindAlg.out v.adv.workspace = b}
  have hR := sum_indicator_composeBothOut C (K := A.toKindAlg) id H
    {v | (P v.adv.workspace.1).run (H.reprogram (A.toKindAlg.postAss C v.chal)) = b}
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hD := A.sum_diag_thenProg P q hP C H fun c => if c = b then 1 else 0
  simpa only [Set.mem_ofPred_eq] using hD

/-- **The law of the bit output by `A` followed by the program**, with `H` uniform: the
probability that the composition outputs `b` is the probability, in the law of `A`'s composed
registers and the oracle, that `P` on `A`'s workspace, run against the oracle reprogrammed by the
final assignments, returns `b`. -/
theorem realLaw_thenProg {Bt : Type} (e : Y ≃ Bt) (b : Bool) :
    (((A.thenProg P q hP).compose C).realLaw e).toOuterMeasure {p | p.out = some b} =
      ((A.toKindAlg.composeBothOut C id).realLaw e).toOuterMeasure
        {p | ∃ v, p.out = some v ∧ (P v.adv.workspace.1).run
          ((e.symm ∘ p.oracle).reprogram (A.toKindAlg.postAss C v.chal)) = b} := by
  have hset : {p : Outcome (Option Bool) X Bt | p.out = some b} =
      {p | ∃ v, p.out = some v ∧ (fun (v : Bool) (_ : X → Bt) => v = b) v p.oracle} := by
    ext p
    simp
  rw [hset]
  refine (Alg.toOuterMeasure_realLaw_out ((A.thenProg P q hP).compose C) e
    (fun (v : Bool) (_ : X → Bt) => v = b)).trans (Eq.trans ?_
    (Alg.toOuterMeasure_realLaw_out (A.toKindAlg.composeBothOut C id) e (fun (v : A.toKindAlg.CW C) (h : X → Bt) =>
      (P v.adv.workspace.1).run ((e.symm ∘ h).reprogram (A.toKindAlg.postAss C v.chal)) = b)).symm)
  refine tsum_congr fun H => ?_
  congr 1
  have hH : e.symm ∘ (e ∘ H) = H := by
    funext x
    simp
  simp only [hH]
  have h := A.outLaw_thenProg P q hP C H b
  rw [Alg.outLaw_some_eq_sum, Alg.toOuterMeasure_outLaw_some] at h
  exact h

/-- **The final state of the composition of `A` followed by the program has `A`'s trace**: the
program's steps are basis permutations. -/
theorem trace_final_thenProg (H : X → Y) :
    (((A.thenProg P q hP).compose C).final H).trace = ((A.compose C).final H).trace :=
  A.trace_final_thenProgWith P q hP _ C H

/-- **`A` followed by the program stays within its budget** when `A` does: its run never fails to
terminate where `A`'s does not (`withinBudget_iff`). -/
theorem withinBudget_thenProg (hA : A.WithinBudget) : (A.thenProg P q hP).WithinBudget :=
  A.withinBudget_thenProgWith P q hP _ hA

end Bit

end AdaptiveIAlg

end GordieHowe.Quantum
