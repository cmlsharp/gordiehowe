-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkJoinHonest
public import GordieHowe.Model.IOP.CausalHVZK

@[expose] public section

/-!
# Honest-verifier zero knowledge of a multi-circuit IOP with forked domains

The composite verifier's view (`GordieHowe.IOP.SPIOP.views` of `GordieHowe.RealizedProgram.ProofSystem.IOP.toCausalIOP`) of the honest run
(`GordieHowe.RealizedProgram.ProofSystem.IOP.honest`) is simulated by `simulator`: uniform challenges, the application phase's
simulator on them, every domain's simulator on the public input the simulated application
transcript fixes, and the view of the composite transcript assembled from these parts
(`assemble`), whose commitment holds the simulated leaves at the queried positions and default
leaves elsewhere (`fakeCom`). The view depends on the commitment only at the queried positions
(`view_assemble_congr`), and the honest run is the assembled transcript of its parts
(`run_eq_assemble`), so outside the application phase's completeness events the two laws are equal
(the application phase's simulator, then the domains' perfect simulators on the public inputs,
`IdentDistrib.dependent`, `view_identDistrib`); the error is the probability of the events
together (`hvzk_of_errorBound`). For honest inputs read with uniform coins (`coinHonest`), the
events may read the coins, and the error is their probability over the coins and the challenges
(`hvzk_coins`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS
open scoped NNReal ENNReal

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel)

/-! ### Composite transcripts from their parts -/

/-- **The prefix's transcript** from the domains' oracle messages `O`, their commit rounds `r` and
the application phase's transcript. -/
def prefixTr (O : C.Com) (r : ∀ d, (C.circuit d).Rounds) (trApp : C.app.spec.Transcript (Fin.last C.app.n)) :
    (C.P .pre).Transcript (Fin.last (C.rounds .pre)) :=
  Transcript.join (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) (fun _ => O)
    (Transcript.join (joinN C.m r) trApp)

/-- **The composite transcript** from the prefix's parts, every branch's transcript and every
join part's transcript. -/
def assemble (O : C.Com) (r : ∀ d, (C.circuit d).Rounds)
    (trApp : C.app.spec.Transcript (Fin.last C.app.n)) (trs : ∀ d, (C.circuit d).BranchTrs)
    (trj : ∀ d, (C.circuit d).join.Transcript (Fin.last (C.circuit d).jn)) : FullTr C.P C.term :=
  FullTr.join (k := .seq) (FullTr.ofLeaf (P := C.P) (j := .pre) (C.prefixTr O r trApp))
    (FullTr.joinN .par C.m fun d => FullTr.join (k := .seq)
      (FullTr.joinN .par (C.circuit d).nb fun b =>
        FullTr.ofLeaf (P := C.P) (j := .br d b) (trs d b))
      (FullTr.ofLeaf (P := C.P) (j := .jn d) (trj d)))

/-- **The prefix's messages after the first** do not read the commitment. -/
theorem prefixTr_apply_ne (O O' : C.Com) (r : ∀ d, (C.circuit d).Rounds)
    (trApp : C.app.spec.Transcript (Fin.last C.app.n)) (i : Fin (C.rounds .pre)) (hi : (i : ℕ) ≠ 0) :
    C.prefixTr O r trApp i = C.prefixTr O' r trApp i := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin (C.nc + C.app.n), i = Fin.natAdd 1 j :=
    ⟨⟨i.1 - 1, by have := i.2; change i.1 < 1 + (C.nc + C.app.n) at this; omega⟩,
      Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩
  exact (Transcript.join_right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec)
    (fun _ => O : (commitSpec C.Com).Transcript (Fin.last 1)) (Transcript.join (joinN C.m r) trApp)
      j).trans (Transcript.join_right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec)
    (fun _ => O' : (commitSpec C.Com).Transcript (Fin.last 1)) (Transcript.join (joinN C.m r) trApp)
      j).symm

/-- **The prefix's first message** is the commitment. -/
theorem prefixTr_zero (O : C.Com) (r : ∀ d, (C.circuit d).Rounds)
    (trApp : C.app.spec.Transcript (Fin.last C.app.n)) :
    cast C.type_zero (C.prefixTr O r trApp ⟨0, C.pos_rounds_pre⟩) = O := by
  have h := Transcript.join_left (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec)
    (fun _ => O : (commitSpec C.Com).Transcript (Fin.last 1)) (Transcript.join (joinN C.m r) trApp)
      ⟨0, Nat.one_pos⟩
  exact (congrArg (cast C.type_zero) h).trans (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))

/-- **The join part's challenges of an assembled transcript** are its join transcript's. -/
theorem joinCh_assemble (O : C.Com) (r : ∀ d, (C.circuit d).Rounds)
    (trApp : C.app.spec.Transcript (Fin.last C.app.n)) (trs : ∀ d, (C.circuit d).BranchTrs)
    (trj : ∀ d, (C.circuit d).join.Transcript (Fin.last (C.circuit d).jn)) (d : Fin C.m) :
    C.joinCh d (C.assemble O r trApp trs trj).challenges =
      fun i : (C.circuit d).join.ChallengeIdx => trj d i.1 := by
  funext i
  have h := FullTr.challenges_partN .par C.m (c := C.domainTerm)
    (C.assemble O r trApp trs trj).right d
  change ((Chs.partN .par C.m ((C.assemble O r trApp trs trj).right.challenges) d).right.at
    (.here (IOP.Shape.Idx.jn (S := C.shape) d))) i = _
  rw [← h]
  change (((FullTr.joinN (P := C.P) .par C.m (c := C.domainTerm) _).partN .par C.m d).challenges.right.at
    (.here (IOP.Shape.Idx.jn (S := C.shape) d))) i = _
  rw [FullTr.partN_joinN]
  rfl

/-- **The view of an assembled transcript reads the commitment only at the queried positions**:
two commitments agreeing at the leaves each domain's verdict reads at its join's challenges give
the same view. -/
theorem view_assemble_congr (O O' : C.Com) (r : ∀ d, (C.circuit d).Rounds)
    (trApp : C.app.spec.Transcript (Fin.last C.app.n)) (trs : ∀ d, (C.circuit d).BranchTrs)
    (trj : ∀ d, (C.circuit d).join.Transcript (Fin.last (C.circuit d).jn))
    (h : ∀ d, ∀ j ∈ (C.oracle d).queries (fun i => trj d i.1),
      (C.oracle d).leaf (O d) j = (C.oracle d).leaf (O' d) j) :
    C.toCausalIOP.views.view (C.assemble O r trApp trs trj) =
      C.toCausalIOP.views.view (C.assemble O' r trApp trs trj) := by
  have hq : ∀ q : C.term.Leaf, q ≠ C.preLeafT →
      C.assemble O r trApp trs trj q = C.assemble O' r trApp trs trj q := fun q hq => by
    rcases q with p | p
    · cases p
      exact absurd rfl hq
    · rfl
  have hpre : ∀ i : Fin (C.rounds .pre), (i : ℕ) ≠ 0 →
      C.assemble O r trApp trs trj C.preLeafT i = C.assemble O' r trApp trs trj C.preLeafT i :=
    fun i hi => C.prefixTr_apply_ne O O' r trApp i hi
  refine IOP.SPIOP.view_eq (fun cc => ?_) (fun p i => ?_) (fun q hq' => ?_)
  · by_cases hp : cc.leaf = C.preLeafT
    · obtain ⟨p, idx⟩ := cc
      subst hp
      exact hpre idx.1 fun h0 => by
        have hd := idx.2
        rw [show idx.1 = ⟨0, C.pos_rounds_pre⟩ from Fin.ext h0] at hd
        exact absurd (C.oracleIdx.2.symm.trans hd) (by decide)
    · exact congrFun (hq cc.leaf hp) cc.idx.1
  · by_cases hp : p = C.preLeafT
    · subst hp
      by_cases hi : (i.1 : ℕ) = 0
      · obtain rfl : i = C.oracleIdx := Subtype.ext (Fin.ext hi)
        rfl
      · exact congrArg _ (congrArg _ (hpre i.1 hi))
    · exact congrArg _ (congrArg _ (congrFun (hq p hp) i.1))
  · change q ∈ C.queryList _ at hq'
    obtain ⟨d, -, hd⟩ := List.mem_flatMap.1 hq'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hd
    rw [Finset.mem_sort, joinCh_assemble] at hj
    change (C.oracle d).leaf (cast C.type_zero (C.prefixTr O r trApp ⟨0, C.pos_rounds_pre⟩) d) j =
      (C.oracle d).leaf (cast C.type_zero (C.prefixTr O' r trApp ⟨0, C.pos_rounds_pre⟩) d) j
    rw [prefixTr_zero, prefixTr_zero]
    exact h d j hj

/-! ### The honest run assembled -/

variable {C} {S : C.SimData} {I : Type} {relI : Set (Stmt × I)} (Hc : C.Honest S I relI)
  (y : I) (c : Hc.Coins) (x : Stmt) (ch : Chs C.P C.term)

/-- Domain `d`'s honest commit rounds at the composite challenges. -/
abbrev Honest.roundsAt (d : Fin C.m) : (C.circuit d).Rounds :=
  (Hc.circuit d).rounds (Hc.wit y c.pads d) (c.circuits d) (chN C.m (C.commitCh ch) d)

/-- Domain `d`'s honest branches' transcripts at the composite challenges. -/
abbrev Honest.trsAt (d : Fin C.m) : (C.circuit d).BranchTrs :=
  (Hc.circuit d).trs (C.app.pub d x (Hc.appTr y c x ch)) (Hc.wit y c.pads d) (c.circuits d)
    (Hc.roundsAt y c ch d) (fun b => C.branchCh d b ch)

/-- Domain `d`'s honest join transcript at the composite challenges. -/
abbrev Honest.joinAt (d : Fin C.m) : (C.circuit d).join.Transcript (Fin.last (C.circuit d).jn) :=
  ((Hc.circuit d).join (C.app.pub d x (Hc.appTr y c x ch)) (Hc.wit y c.pads d) (c.circuits d)
    (Hc.roundsAt y c ch d) (Hc.trsAt y c x ch d)).transcript (C.joinCh d ch)

/-- The domains' honest oracle messages. -/
abbrev Honest.comAt : C.Com := fun d => (Hc.circuit d).commit (Hc.wit y c.pads d) (c.circuits d)

/-- **The honest run is the transcript assembled from its parts.** -/
theorem run_eq_assemble :
    (honest Hc y c).run x ch = C.assemble (Hc.comAt y c) (Hc.roundsAt y c ch) (Hc.appTr y c x ch)
      (Hc.trsAt y c x ch) (Hc.joinAt y c x ch) := by
  have htrs : ∀ d, C.branchTrs d (((honest Hc y c).run x ch).right.partN .par C.m d).left =
      Hc.trsAt y c x ch d := fun d => by
    funext b
    change ((((honest Hc y c).run x ch).right.partN .par C.m d).left.partN .par _ b) _ = _
    rw [run_honest_branch, domainStmt_honest]
  refine FullTr.ext_node (FullTr.ext_leaf ?_) (FullTr.ext_partN .par C.m fun d => ?_)
  · change ((honest Hc y c).run x ch).left C.preHere = _
    rw [run_honest_pre]
    change Transcript.join _ (Transcript.join ((CausalTranscript.appendN C.m fun d =>
      (Hc.circuit d).commitRounds (Hc.wit y c.pads d) (c.circuits d)).transcript _) _) =
        C.prefixTr _ _ _
    rw [CausalTranscript.appendN_transcript]
    rfl
  · change _ = (FullTr.joinN .par C.m (c := C.domainTerm) _).partN .par C.m d
    rw [FullTr.partN_joinN]
    refine FullTr.ext_node (FullTr.ext_partN .par _ fun b => ?_) (FullTr.ext_leaf ?_)
    · change _ = (FullTr.joinN .par (C.circuit d).nb
        (c := fun b => leaf (IOP.Shape.Idx.br (S := C.shape) d b))
        fun b => FullTr.ofLeaf (P := C.P) (j := .br d b) (Hc.trsAt y c x ch d b)).partN .par _ b
      rw [FullTr.partN_joinN]
      refine FullTr.ext_leaf ?_
      change ((((honest Hc y c).run x ch).right.partN .par C.m d).left.partN .par _ b) _ = _
      rw [run_honest_branch, domainStmt_honest]
      rfl
    · change (((honest Hc y c).run x ch).right.partN .par C.m d).right _ = _
      rw [run_honest_join, domainStmt_honest, htrs]
      rfl

/-! ### The simulator -/

variable (C) in
/-- **A commitment holding the seen leaves**: each domain's oracle message with the leaves of its
view at the queried positions and the default leaf elsewhere. -/
def fakeCom (v : ∀ d, (C.oracle d).View) : C.Com :=
  fun d => (C.oracle d).ofLeaves fun j => ((v d).com j).getD (C.oracle d).leafDefault

variable (C) in
/-- **The composite transcript of the domains' views** and the application phase's transcript
(`assemble` at `fakeCom`). -/
def assembleView (trApp : C.app.spec.Transcript (Fin.last C.app.n)) (v : ∀ d, (C.oracle d).View) :
    FullTr C.P C.term :=
  C.assemble (C.fakeCom v) (fun d => (v d).rounds) trApp (fun d => (v d).trs) (fun d => (v d).join)

/-- Domain `d`'s honest view at the composite challenges. -/
abbrev Honest.viewAt (d : Fin C.m) : (C.oracle d).View :=
  (C.oracle d).view (C.joinCh d ch) (Hc.comAt y c d) (Hc.roundsAt y c ch d) (Hc.trsAt y c x ch d)
    (Hc.joinAt y c x ch d)

/-- **The view of the honest run** is the view of the transcript assembled from the application
phase's honest transcript and the domains' honest views. -/
theorem view_run :
    C.toCausalIOP.views.view ((honest Hc y c).run x ch) =
      C.toCausalIOP.views.view (C.assembleView (Hc.appTr y c x ch) (Hc.viewAt y c x ch)) := by
  rw [run_eq_assemble]
  refine C.view_assemble_congr _ _ _ _ _ _ fun d j hj => ?_
  have hch : (fun i : (C.circuit d).join.ChallengeIdx => Hc.joinAt y c x ch d i.1) = C.joinCh d ch :=
    funext fun i => CausalTranscript.challenge _ _ i
  rw [hch] at hj
  change _ = (C.oracle d).leaf ((C.oracle d).ofLeaves fun j =>
    (((C.oracle d).comView.see (C.joinCh d ch) (Hc.comAt y c d)) j).getD (C.oracle d).leafDefault) j
  rw [(C.oracle d).leaf_ofLeaves, MessageView.see_of_mem _ hj]
  rfl

variable (S) in
/-- **The simulated view** at the challenges `ch` and the coins `s`: the application phase's
simulator, every domain's simulator on the public input the simulated application transcript
fixes, and the view of the assembled transcript. -/
def simAt (x : Stmt) (ch : Chs C.P C.term) (s : S.app.SimCoins × ∀ d, (S.sim d).Coins) :
    CausalView C.toCausalIOP.views :=
  C.toCausalIOP.views.view (C.assembleView (S.app.sim x (C.appCh ch) s.1) fun d =>
    (S.sim d).sim (C.app.pub d x (S.app.sim x (C.appCh ch) s.1)) (chN C.m (C.commitCh ch) d)
      (fun b => C.branchCh d b ch) (C.joinCh d ch) (s.2 d))

variable (S) in
/-- **The simulator of a multi-circuit IOP with forked domains** (module docstring) at the simulator
data `S`.

Running time: one uniform draw of the challenges, one run of the application phase's simulator
and of every domain's simulator (their own Running time paragraphs), the verifier's computation of
the public inputs (`PhaseStep.pub`), and the assembly of the view, which copies transcript entries;
polynomial. This running time is argued here, not proved in Lean. -/
def simulator : CausalJointSimulator C.toCausalIOP.views Stmt :=
  CausalJointSimulator.ofChallenges (S.app.SimCoins × ∀ d, (S.sim d).Coins) (simAt S)

/-- **Outside the completeness events the honest view has the simulator's law**: on the relation,
at challenges `ch` avoiding the application phase's completeness events, the view of the honest run
over uniform coins has the law of `simAt x ch` (the application phase's simulator, then every
domain's perfect simulator on the public input it fixes, `IdentDistrib.dependent`). -/
theorem view_identDistrib {x : Stmt} {y : I} (hy : (x, y) ∈ relI) {ch : Chs C.P C.term}
    (hgood : Hc.app.Avoids x y (C.appCh ch)) :
    (fun c => C.toCausalIOP.views.view ((honest Hc y c).run x ch)) =ᵈ simAt S x ch := by
  have key := (IdentDistrib.dependent
    (f₁ := fun π => (Hc.app.prover x y π).transcript (C.appCh ch))
    (g₁ := S.app.sim x (C.appCh ch))
    (f₂ := fun π (ρ : ∀ d, (Hc.circuit d).Coins) d => (C.oracle d).view (C.joinCh d ch)
      ((Hc.circuit d).commit (Hc.wit y π d) (ρ d))
      ((Hc.circuit d).rounds (Hc.wit y π d) (ρ d) (chN C.m (C.commitCh ch) d))
      ((Hc.circuit d).trs (C.app.pub d x ((Hc.app.prover x y π).transcript (C.appCh ch)))
        (Hc.wit y π d) (ρ d) ((Hc.circuit d).rounds (Hc.wit y π d) (ρ d) (chN C.m (C.commitCh ch) d))
        (fun b => C.branchCh d b ch))
      (((Hc.circuit d).join (C.app.pub d x ((Hc.app.prover x y π).transcript (C.appCh ch)))
        (Hc.wit y π d) (ρ d) ((Hc.circuit d).rounds (Hc.wit y π d) (ρ d) (chN C.m (C.commitCh ch) d))
        ((Hc.circuit d).trs (C.app.pub d x ((Hc.app.prover x y π).transcript (C.appCh ch)))
          (Hc.wit y π d) (ρ d)
          ((Hc.circuit d).rounds (Hc.wit y π d) (ρ d) (chN C.m (C.commitCh ch) d))
          (fun b => C.branchCh d b ch))).transcript (C.joinCh d ch)))
    (g₂ := fun trApp (s₂ : ∀ d, (S.sim d).Coins) d =>
      (S.sim d).sim (C.app.pub d x trApp) (chN C.m (C.commitCh ch) d)
        (fun b => C.branchCh d b ch) (C.joinCh d ch) (s₂ d))
    (Hc.app.identDistrib x y hy _) fun π =>
      IdentDistrib.pi fun d => Hc.perfect d _ _ (Hc.app.dom_honest x y hy π _ hgood d) _ _ _).comp
    fun v => C.toCausalIOP.views.view (C.assembleView v.1 v.2)
  refine IdentDistrib.trans (IdentDistrib.of_equiv Hc.coinsEquiv fun c => ?_)
    (key.trans (IdentDistrib.of_equiv (Equiv.refl _) fun _ => rfl))
  rw [view_run]
  rfl

/-- **Honest-verifier zero knowledge of a multi-circuit IOP with forked domains at the
completeness error `e`** (CY24 Definition 23.1.8 for composites, `CausalHVZK`) at `simulator`,
with error the application phase's completeness error `e` (`hE`: the completeness events together
have probability at most `e`). -/
theorem hvzk_of_errorBound {e : Stmt → ℝ≥0} (hE : Hc.app.ErrorBound e) :
    CausalHVZKStmt C.toCausalIOP.views relI (honest Hc) id (simulator S) e :=
  CausalHVZK.of_offExceptions (fun x y ch => ¬ Hc.app.Avoids x y (C.appCh ch))
    (fun x y hy => prob_not_avoids_of_errorBound Hc hE x y hy) fun _ _ hy _ hch =>
      view_identDistrib Hc hy (not_not.mp hch)

section Coins

variable {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (Stmt × J)}

/-- **The honest prover with coins** for honest inputs `J` read with the coins `ω` as the honest
inputs `inp y ω`: at the coins `(ω, c)`, the honest prover (`honest`) at `inp y ω` and the honest
prover's coins `c`. -/
noncomputable def coinHonest (inp : J → Ω → I) (y : J) (ρ : Ω × Hc.Coins) :
    CausalProver C.P C.term Stmt :=
  honest Hc (inp y ρ.1) ρ.2

/-- **Honest-verifier zero knowledge of a multi-circuit IOP with forked domains over the prover's
coins** (CY24 Definition 23.1.8 for composites, `CausalHVZK`): for honest inputs `J` read with
uniform coins `ω` as the honest inputs `inp y ω`, the honest prover with coins (`coinHonest`) is
zero knowledge at `simulator` with error the application phase's completeness error over the
coins `e` (`hE`). The exception event reads the coins `ω` (`CausalHVZK.of_offExceptions_coins`). -/
theorem hvzk_coins {inp : J → Ω → I} {e : Stmt → ℝ≥0} (hE : Hc.app.CoinErrorBound relJ inp e) :
    CausalHVZKStmt C.toCausalIOP.views relJ (coinHonest Hc inp) id (simulator S) e :=
  CausalHVZK.of_offExceptions_coins (honest := fun y ω c => honest Hc (inp y ω) c)
    (fun x y ω ch => (x, inp y ω) ∉ relI ∨ ¬ Hc.app.Avoids x (inp y ω) (C.appCh ch))
    (fun x y hy => prob_not_avoids_coins Hc hE x y hy) fun _ _ _ _ _ hn =>
      view_identDistrib Hc (not_not.mp (not_or.mp hn).1) (not_not.mp (not_or.mp hn).2)

/-- **Completeness of the honest prover with coins over all its coins**: on `relJ`, the composite
verifier rejects the run of `coinHonest Hc inp y` with probability at most the application phase's
completeness error over the coins `e` (`hE`), over uniform coins `ω`, honest coins and challenges
(`completeness_coins` at every value of the honest coins). -/
theorem completeness_coinHonest {inp : J → Ω → I} {e : Stmt → ℝ≥0}
    (hE : Hc.app.CoinErrorBound relJ inp e) (x : Stmt) (y : J) (hy : (x, y) ∈ relJ) :
    Pr[q ← (Ω × Hc.Coins) × Chs C.P C.term :
        C.verifier x ((coinHonest Hc inp y q.1).run x q.2) ≠ true] ≤ e x := by
  rw [← QROM.probUniform_equiv (A := (Ω × Chs C.P C.term) × Hc.Coins)
    ⟨fun a => ((a.1.1, a.2), a.1.2), fun q => ((q.1.1, q.2), q.1.2), fun _ => rfl, fun _ => rfl⟩]
  exact QROM.probUniform_prod_le _ fun c => completeness_coins Hc hE c x y hy

end Coins

end RealizedProgram.ProofSystem.IOP

end GordieHowe
