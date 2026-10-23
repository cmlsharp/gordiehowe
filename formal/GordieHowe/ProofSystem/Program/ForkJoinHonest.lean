-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkJoinBCS
public import GordieHowe.Model.IOP.CausalPartN
public import GordieHowe.ProofSystem.Program.Phased

@[expose] public section

/-!
# The honest prover of a multi-circuit IOP with forked domains

The honest prover of a multi-circuit IOP with forked domains (`GordieHowe.RealizedProgram.ProofSystem.IOP`) as a causal prover of
the series–parallel term (`honest`), and its completeness (`completeness_of_errorBound`,
`completeness_coins`).

* `GordieHowe.RealizedProgram.ProofSystem.IOP.Honest`: the application phase's honest prover (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest`), every domain's
  honest forked prover (`GordieHowe.FieldProof.BranchShape.Honest`), accepted on its domain (`GordieHowe.FieldProof.BranchShape.Honest.Accepts`),
  with a perfect simulator of its view (`GordieHowe.FieldProof.BranchShape.Simulator.Perfect`).
* `honest y c`: at the prefix, the commitment to the domains' honest inputs, the domains' commit
  rounds and the application phase's honest prover; at branch `b` of domain `d`, the domain's
  honest branch on the public input and the commit rounds the prefix fixes; at the join part of
  domain `d`, the domain's honest join on them and the branches' transcripts.
* `run_honest_pre`, `run_honest_branch`, `run_honest_join`: its run, leaf by leaf.
* `completeness_of_errorBound`: on the honest inputs, the composite verifier rejects the honest run
  with probability at most the application phase's completeness error `e`
  (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.ErrorBound`: its completeness events have together probability at most `e`);
  `completeness_coins`: for honest inputs read with uniform coins, at most the completeness error
  over the coins (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.CoinErrorBound`), over the coins and the challenges.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec IOP.SPTerm
open scoped NNReal ENNReal

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel)

/-- **The simulator data of a multi-circuit IOP with forked domains**: the application phase's
simulator and every domain's simulator (`simulator` assembles them). Data apart from the honest
prover (`Honest`). -/
structure SimData where
  /-- The application phase's simulator. -/
  app : C.app.Sim
  /-- Each domain's simulator. -/
  sim : ∀ d, (C.circuit d).Simulator (C.oracle d)

/-- **The honest prover of a multi-circuit IOP with forked domains** (module docstring), simulated by
`S`, on honest inputs `I` related to statements by `relI`. -/
structure Honest (S : C.SimData) (I : Type) (relI : Set (Stmt × I)) where
  /-- Each domain's honest inputs. -/
  In : Fin C.m → Type
  /-- Each domain's honest domain. -/
  dom : ∀ d, C.Pub d → In d → Prop
  /-- The application phase's honest prover. -/
  app : C.app.Honest I relI In dom S.app
  /-- Each domain's honest forked prover. -/
  circuit : ∀ d, (C.circuit d).Honest (In d)
  /-- Each domain's honest prover is accepted on its domain. -/
  accepts : ∀ d, (circuit d).Accepts (dom d)
  /-- Each domain's simulator is perfect on its domain. -/
  perfect : ∀ d, (S.sim d).Perfect (circuit d) (dom d)

variable {C} {S : C.SimData} {I : Type} {relI : Set (Stmt × I)} (Hc : C.Honest S I relI)

/-- **The honest prover's coins**: the application phase's pads and every domain's coins. -/
structure Honest.Coins where
  /-- The application phase's pads. -/
  pads : Hc.app.Pads
  /-- Every domain's coins. -/
  circuits : ∀ d, (Hc.circuit d).Coins

/-- The coins as a pair. -/
def Honest.coinsEquiv : Hc.Coins ≃ Hc.app.Pads × ∀ d, (Hc.circuit d).Coins where
  toFun c := (c.pads, c.circuits)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Hc.Coins := Fintype.ofEquiv _ Hc.coinsEquiv.symm
instance : Nonempty Hc.Coins := Hc.coinsEquiv.nonempty

/-- Domain `d`'s honest input at the honest input `y` and the pads `π`. -/
abbrev Honest.wit (y : I) (π : Hc.app.Pads) (d : Fin C.m) : Hc.In d := Hc.app.wit d y π

/-- **The honest prefix**: the commitment to the domains' honest inputs, the domains' honest
commit rounds in order, then the application phase's honest prover. -/
def Honest.prefixFamily (y : I) (c : Hc.Coins) (x : Stmt) : CausalTranscript (C.P .pre) :=
  (CausalTranscript.oneMessage (fun d => (Hc.circuit d).commit (Hc.wit y c.pads d) (c.circuits d) :
      C.Com)).append fun _ =>
    (CausalTranscript.appendN C.m fun d =>
      (Hc.circuit d).commitRounds (Hc.wit y c.pads d) (c.circuits d)).append fun _ =>
        Hc.app.prover x y c.pads

/-- The honest prefix prover. -/
noncomputable def Honest.prefixProver (y : I) (c : Hc.Coins) : Prover (C.P .pre) Stmt :=
  CausalTranscript.realize (Hc.prefixFamily y c)

/-- **The honest branch `b` of domain `d`** on the domain's statement after the prefix. -/
noncomputable def Honest.branchProver (d : Fin C.m) (b : Fin (C.circuit d).nb) (y : I)
    (c : Hc.Coins) : Prover (C.P (.br d b)) C.PostStmt :=
  CausalTranscript.realize (P := (C.circuit d).branch b) fun z =>
    (Hc.circuit d).branch b (C.domainStmt d z).pub (Hc.wit y c.pads d) (c.circuits d)
      (C.domainStmt d z).rounds

/-- **The honest join part of domain `d`** on the domain's statement and its branches'
transcripts. -/
noncomputable def Honest.joinProver (d : Fin C.m) (y : I) (c : Hc.Coins) :
    Prover (C.P (.jn d)) (SeqStmt C.PostStmt C.P (C.branchTerm d)) :=
  CausalTranscript.realize (P := (C.circuit d).join) fun z =>
    (Hc.circuit d).join (C.domainStmt d z.1).pub (Hc.wit y c.pads d) (c.circuits d)
      (C.domainStmt d z.1).rounds (C.branchTrs d z.2)

/-- **The honest causal prover** (module docstring). -/
noncomputable def honest (y : I) (c : Hc.Coins) : CausalProver C.P C.term Stmt :=
  (CausalProver.ofLeaf (P := C.P) (j := .pre) (Hc.prefixProver y c)).seq
    (CausalProver.nodeN .par C.m fun d =>
      (CausalProver.nodeN .par (C.circuit d).nb fun b =>
        CausalProver.ofLeaf (P := C.P) (j := .br d b) (Hc.branchProver d b y c)).seq
      (CausalProver.ofLeaf (P := C.P) (j := .jn d) (Hc.joinProver d y c)))

/-! ### The run -/

variable (C) in
/-- The prefix's part of the composite challenges. -/
def preCh (ch : Chs C.P C.term) : (C.P .pre).Challenges := Chs.equivLeaf ch.left

variable (C) in
/-- **Branch `b` of domain `d`'s challenges** among the composite challenges. -/
def branchCh (d : Fin C.m) (b : Fin (C.circuit d).nb) (ch : Chs C.P C.term) :
    ((C.circuit d).branch b).Challenges :=
  ((((Chs.right ch).partN .par C.m d).left).partN .par (C.circuit d).nb b).at
    (.here (IOP.Shape.Idx.br (S := C.shape) d b))

variable (y : I) (c : Hc.Coins) (x : Stmt) (ch : Chs C.P C.term)

/-- **The honest run at the prefix** is the honest prefix family at the prefix's challenges. -/
theorem run_honest_pre :
    ((honest Hc y c).run x ch).left C.preHere = (Hc.prefixFamily y c x).transcript (C.preCh ch) :=
  (CausalProver.run_ofLeaf _ x ch.left).trans (CausalTranscript.run_realize _ _ x)

/-- The honest run's domain part, at the statement extended by the honest prefix. -/
theorem run_honest_domain (d : Fin C.m) :
    ((honest Hc y c).run x ch).right.partN .par C.m d =
      ((CausalProver.nodeN .par (C.circuit d).nb fun b =>
        CausalProver.ofLeaf (P := C.P) (j := .br d b) (Hc.branchProver d b y c)).seq
        (CausalProver.ofLeaf (P := C.P) (j := .jn d) (Hc.joinProver d y c))).run
          (x, ((honest Hc y c).run x ch).left) ((Chs.right ch).partN .par C.m d) :=
  CausalProver.run_nodeN_partN .par C.m _ _ _ d

/-- **The honest run at branch `b` of domain `d`** is the domain's honest branch at its
challenges. -/
theorem run_honest_branch (d : Fin C.m) (b : Fin (C.circuit d).nb) :
    ((((honest Hc y c).run x ch).right.partN .par C.m d).left.partN .par (C.circuit d).nb b)
        (.here (IOP.Shape.Idx.br (S := C.shape) d b)) =
      ((Hc.circuit d).branch b (C.domainStmt d (x, ((honest Hc y c).run x ch).left)).pub
        (Hc.wit y c.pads d) (c.circuits d)
        (C.domainStmt d (x, ((honest Hc y c).run x ch).left)).rounds).transcript
          (C.branchCh d b ch) := by
  rw [run_honest_domain]
  change ((CausalProver.nodeN .par (C.circuit d).nb fun b =>
      CausalProver.ofLeaf (P := C.P) (j := .br d b) (Hc.branchProver d b y c)).run _
        (((Chs.right ch).partN .par C.m d).left)).partN .par (C.circuit d).nb b _ = _
  rw [CausalProver.run_nodeN_partN]
  exact (CausalProver.run_ofLeaf _ _ _).trans (CausalTranscript.run_realize
    (P := (C.circuit d).branch b) (fun z => (Hc.circuit d).branch b (C.domainStmt d z).pub
      (Hc.wit y c.pads d) (c.circuits d) (C.domainStmt d z).rounds) _ _)

/-- **The honest run at the join part of domain `d`** is the domain's honest join at its
challenges, on the honest branches' transcripts. -/
theorem run_honest_join (d : Fin C.m) :
    (((honest Hc y c).run x ch).right.partN .par C.m d).right
        (.here (IOP.Shape.Idx.jn (S := C.shape) d)) =
      ((Hc.circuit d).join (C.domainStmt d (x, ((honest Hc y c).run x ch).left)).pub
        (Hc.wit y c.pads d) (c.circuits d)
        (C.domainStmt d (x, ((honest Hc y c).run x ch).left)).rounds
        (C.branchTrs d (((honest Hc y c).run x ch).right.partN .par C.m d).left)).transcript
          (C.joinCh d ch) := by
  rw [run_honest_domain]
  change (CausalProver.ofLeaf (P := C.P) (j := .jn d) (Hc.joinProver d y c)).run _
    (((Chs.right ch).partN .par C.m d).right) (.here _) = _
  exact (CausalProver.run_ofLeaf _ _ _).trans (CausalTranscript.run_realize
    (P := (C.circuit d).join) (fun z : SeqStmt C.PostStmt C.P (C.branchTerm d) =>
      (Hc.circuit d).join (C.domainStmt d z.1).pub
      (Hc.wit y c.pads d) (c.circuits d) (C.domainStmt d z.1).rounds (C.branchTrs d z.2)) _ _)

variable (C) in
/-- The commit rounds' part of the composite challenges. -/
def commitCh (ch : Chs C.P C.term) : C.commitRounds.Challenges := (C.preCh ch).right.left

variable (C) in
/-- The application phase's part of the composite challenges. -/
def appCh (ch : Chs C.P C.term) : C.app.spec.Challenges := (C.preCh ch).right.right

/-- The application phase's honest transcript at the composite challenges. -/
abbrev Honest.appTr : C.app.spec.Transcript (Fin.last C.app.n) :=
  (Hc.app.prover x y c.pads).transcript (C.appCh ch)

/-- **Domain `d`'s statement on the honest run**: the public input the honest application
transcript fixes, the domain's honest oracle message and its honest commit rounds. -/
theorem domainStmt_honest (d : Fin C.m) :
    C.domainStmt d (x, ((honest Hc y c).run x ch).left) =
      ⟨C.app.pub d x (Hc.appTr y c x ch), (Hc.circuit d).commit (Hc.wit y c.pads d) (c.circuits d),
        (Hc.circuit d).rounds (Hc.wit y c.pads d) (c.circuits d) (chN C.m (C.commitCh ch) d)⟩ := by
  unfold domainStmt context
  dsimp only
  rw [run_honest_pre]
  simp only [PhaseStep.CommittedContext.app, PhaseStep.CommittedContext.com,
    PhaseStep.CommittedContext.rounds, Honest.prefixFamily]
  erw [CausalTranscript.append_right, CausalTranscript.append_right, CausalTranscript.append_left,
    CausalTranscript.append_left, CausalTranscript.appendN_transcript, part_joinN]
  rfl

/-- **The composite verifier accepts the honest run** wherever the application phase's
challenges avoid its completeness events. -/
theorem verifier_honest (hy : (x, y) ∈ relI) (hgood : Hc.app.Avoids x y (C.appCh ch)) :
    C.verifier x ((honest Hc y c).run x ch) = true := by
  have hok := Hc.app.ok_honest x y hy c.pads _ hgood
  have hdom := fun d => Hc.app.dom_honest x y hy c.pads _ hgood d
  change (verifierN .par C.m C.domainV (x, ((honest Hc y c).run x ch).left)
      ((honest Hc y c).run x ch).right && C.app.ok x _) = true
  rw [Bool.and_eq_true]
  refine ⟨verifierN_of_forall .par C.m (c := C.domainTerm) _ fun d => ?_, ?_⟩
  · have hacc := Hc.accepts d _ _ (hdom d) (c.circuits d) (chN C.m (C.commitCh ch) d)
      (fun b => C.branchCh d b ch) (C.joinCh d ch)
    unfold domainV
    rw [run_honest_join, domainStmt_honest]
    have htrs : C.branchTrs d (((honest Hc y c).run x ch).right.partN .par C.m d).left =
        (Hc.circuit d).trs (C.app.pub d x (Hc.appTr y c x ch)) (Hc.wit y c.pads d) (c.circuits d)
          ((Hc.circuit d).rounds (Hc.wit y c.pads d) (c.circuits d) (chN C.m (C.commitCh ch) d))
          (fun b => C.branchCh d b ch) := by
      funext b
      change ((((honest Hc y c).run x ch).right.partN .par C.m d).left.partN .par _ b) _ = _
      rw [run_honest_branch, domainStmt_honest]
    rw [htrs]
    exact hacc
  · have he : (C.context (x, ((honest Hc y c).run x ch).left)).app = Hc.appTr y c x ch := by
      unfold context
      dsimp only
      rw [run_honest_pre]
      simp only [PhaseStep.CommittedContext.app, Honest.prefixFamily]
      erw [CausalTranscript.append_right, CausalTranscript.append_right]
      rfl
    rw [he]
    exact hok

/-- The application phase's challenge `j` is the composite challenge of the prefix at round
`j` of the application phase, read through its type. -/
theorem appCh_apply (ch : Chs C.P C.term) (j : C.app.spec.ChallengeIdx) :
    C.appCh ch j = cast (append_Challenge_inr (P₁ := C.commitRounds) (P₂ := C.app.spec) j)
      (cast (append_Challenge_inr (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec)
        (ChallengeIdx.inr j)) (ch ⟨C.preLeafT, ChallengeIdx.inr (ChallengeIdx.inr j)⟩)) :=
  rfl

/-- **The composite challenge of round `j` of the application phase** has the phase's type. -/
def appChEquiv (j : C.app.spec.ChallengeIdx) :
    (⟨C.preLeafT, ChallengeIdx.inr (ChallengeIdx.inr j)⟩ : ChIdx C.P C.term).Challenge ≃
      C.app.spec.Challenge j :=
  (Equiv.cast (append_Challenge_inr (P₁ := commitSpec C.Com)
    (P₂ := C.commitRounds ++ C.app.spec) (ChallengeIdx.inr j))).trans
    (Equiv.cast (append_Challenge_inr (P₁ := C.commitRounds) (P₂ := C.app.spec) j))

/-- **Updating the composite challenge of round `j` of the application phase** updates the
application phase's challenges at `j`. -/
theorem appCh_update (ch : Chs C.P C.term) (j : C.app.spec.ChallengeIdx)
    (v : (⟨C.preLeafT, ChallengeIdx.inr (ChallengeIdx.inr j)⟩ : ChIdx C.P C.term).Challenge) :
    C.appCh (Function.update ch ⟨C.preLeafT, ChallengeIdx.inr (ChallengeIdx.inr j)⟩ v) =
      Function.update (C.appCh ch) j (C.appChEquiv j v) := by
  funext j'
  by_cases h : j' = j
  · subst h
    rw [appCh_apply, Function.update_self, Function.update_self]
    rfl
  · rw [appCh_apply, Function.update_of_ne h, appCh_apply, Function.update_of_ne]
    intro e
    obtain ⟨-, hi⟩ := ChIdx.mk.inj e
    exact h (ChallengeIdx.inr_injective (ChallengeIdx.inr_injective (eq_of_heq hi)))

variable (C) in
/-- **The application phase's challenges among uniform composite challenges are uniform**: an
event on them has the probability it has over the application phase's challenges
(`QROM.probUniform_restrict`). -/
theorem prob_appCh (E : C.app.spec.Challenges → Prop) :
    Pr[ch ← Chs C.P C.term : E (C.appCh ch)] = Pr[a ← C.app.spec.Challenges : E a] := by
  classical
  refine QROM.probUniform_restrict
    (fun j : C.app.spec.ChallengeIdx =>
      (⟨C.preLeafT, ChallengeIdx.inr (ChallengeIdx.inr j)⟩ : ChIdx C.P C.term))
    (fun j j' e => ?_) (fun j => C.appChEquiv j) E
  obtain ⟨-, hi⟩ := ChIdx.mk.inj e
  exact ChallengeIdx.inr_injective (ChallengeIdx.inr_injective (eq_of_heq hi))

/-- **The completeness events, read on the composite challenges,** have probability at most the
application phase's completeness error `e` (`hE`). -/
theorem prob_not_avoids_of_errorBound {e : Stmt → ℝ≥0} (hE : Hc.app.ErrorBound e) (x : Stmt)
    (y : I) (hy : (x, y) ∈ relI) :
    Pr[ch ← Chs C.P C.term : ¬ Hc.app.Avoids x y (C.appCh ch)] ≤ e x :=
  (prob_appCh C _).trans_le (hE x y hy)

/-- **Completeness of a multi-circuit IOP with forked domains at the completeness error `e`**: at
every value `c` of the honest coins, on the honest inputs, the composite verifier rejects the
honest run with probability at most the application phase's completeness error `e` (`hE`: the
completeness events together have probability at most `e`). -/
theorem completeness_of_errorBound {e : Stmt → ℝ≥0} (hE : Hc.app.ErrorBound e) (c : Hc.Coins)
    (x : Stmt) (y : I) (hy : (x, y) ∈ relI) :
    Pr[ch ← Chs C.P C.term : C.verifier x ((honest Hc y c).run x ch) ≠ true] ≤ e x :=
  (probUniform_mono fun ch hch hgood => hch (verifier_honest Hc y c x ch hy hgood)).trans
    (prob_not_avoids_of_errorBound Hc hE x y hy)

section Coins

variable {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (Stmt × J)} {inp : J → Ω → I}

/-- **The completeness events over the prover's coins, read on the composite challenges,** have
probability at most the application phase's completeness error over the coins `e` (`hE`). -/
theorem prob_not_avoids_coins {e : Stmt → ℝ≥0} (hE : Hc.app.CoinErrorBound relJ inp e) (x : Stmt)
    (y : J) (hy : (x, y) ∈ relJ) :
    Pr[u ← (Ω × Chs C.P C.term) :
      (x, inp y u.1) ∉ relI ∨ ¬ Hc.app.Avoids x (inp y u.1) (C.appCh u.2)] ≤ e x :=
  (probUniform_prod_congr_snd fun ω => prob_appCh C fun a =>
    (x, inp y ω) ∉ relI ∨ ¬ Hc.app.Avoids x (inp y ω) a).trans_le (hE x y hy)

/-- **Completeness of a multi-circuit IOP with forked domains over the prover's coins**
(`causalCompletenessCoins`): for honest inputs `J` read with uniform coins `ω` as the honest inputs
`inp y ω`, at every value `c` of the honest prover's coins, on `relJ`, the composite verifier rejects
the honest run with probability at most the application phase's completeness error over the coins
`e` (`hE`), over uniform coins `ω` and challenges. -/
theorem completeness_coins {e : Stmt → ℝ≥0} (hE : Hc.app.CoinErrorBound relJ inp e) (c : Hc.Coins) :
    causalCompletenessCoins relJ C.verifier (fun y ω => honest Hc (inp y ω) c) e :=
  fun x y hy => (probUniform_mono fun u hu => by
      by_contra hn
      exact hu (verifier_honest Hc (inp y u.1) c x u.2 (not_not.mp (not_or.mp hn).1)
        (not_not.mp (not_or.mp hn).2))).trans
    (prob_not_avoids_coins Hc hE x y hy)

end Coins

end RealizedProgram.ProofSystem.IOP

namespace RealizedProgram.ProofSystem.PhaseStep

variable {Stmt W : Type} {rel : Set (Stmt × W)} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop} {A : PhaseStep Stmt W rel Pub Wit holds} {I : Type}
  {relI : Set (Stmt × I)} {In : Fin m → Type} {dom : ∀ i, Pub i → In i → Prop}

open Classical in
/-- **Per-round probabilities give the summed completeness error** (union bound): events of
probability at most `δ j` over round `j`'s challenge, whatever the others, have together
probability at most `∑ j, δ j`. -/
theorem Honest.BadBound.errorBound {SA : A.Sim} {Ah : A.Honest I relI In dom SA} {δ : A.spec.ChallengeIdx → ℝ≥0}
    (h : Ah.BadBound δ) : Ah.ErrorBound fun _ => ∑ j, δ j := by
  intro x y hy
  refine (probUniform_mono fun ch (hc : ¬ Ah.Avoids x y ch) => ?_).trans
    ((QROM.probUniform_exists_le fun j ch => Ah.bad j x y ch).trans
      ((Finset.sum_le_sum fun j _ => ?_).trans_eq (ENNReal.ofNNReal_finsetSum _ _).symm))
  · unfold Honest.Avoids AvoidsEvents at hc
    push Not at hc
    exact hc
  · exact probUniform_pi_le_of_update j _ fun f => h j x y hy f

end RealizedProgram.ProofSystem.PhaseStep

namespace RealizedProgram.ProofSystem.Phased

variable {Stmt W : Type} {rel : Set (Stmt × W)} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop} {K : ℕ} {L : PhaseLayout K}
  {P : Phased Stmt W rel Pub Wit holds L} {I : Type} {relI : Set (Stmt × I)} {In : Fin m → Type}
  {dom : ∀ i, Pub i → In i → Prop}

open Classical in
/-- **Per-phase probabilities give the summed completeness error** (union bound): events of
probability at most `δ k` over phase `k`'s challenge, whatever the others, have together
probability at most `∑ k, δ k`. -/
theorem Honest.BadBound.errorBound {Ph : P.Honest I relI In dom} {δ : Fin K → ℝ≥0}
    (h : Ph.BadBound δ) : Ph.ErrorBound fun _ => ∑ k, δ k := fun x y hy =>
  (QROM.probUniform_exists_le fun k c => Ph.bad k x y c).trans
    ((Finset.sum_le_sum fun k _ => probUniform_pi_le_of_update k _ fun f => h k x y hy f).trans_eq
      (ENNReal.ofNNReal_finsetSum _ _).symm)

end RealizedProgram.ProofSystem.Phased

end GordieHowe
