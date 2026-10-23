-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldHonest
public import GordieHowe.ProofSystem.Program.FieldFork

@[expose] public section

/-!
# GordieHowe: the honest prover of any domain's circuit proof, forked

The honest data of the forked domain `d` (`GordieHowe.RealizedProgram.fieldForkSound`, `TreeFork.Sound.HonestData`)
under the compiler's completeness (`CircuitsAccept`):

* **the branches** (`GordieHowe.RealizedProgram.forkBranchHonest`): each branch's honest masked reduction
  (`GordieHowe.RealizedProgram.branchHonest`) at the join's logical assignment;
* **the join** (`GordieHowe.RealizedProgram.forkJoinHonestData`): the domain's masked reduction at the honest branches'
  transcripts (`MaskedReduction.Honest.fixAt`, complete by the branches' completeness and the rows,
  `GordieHowe.RealizedProgram.forkJoin_complete`), the kits' honest masks, and the honest committed cells
  (`GordieHowe.RealizedProgram.fieldHonestCells`) at the branches' pads, which commit every branch, the rows, the
  words and the masks;
* **the forked honest data** (`GordieHowe.RealizedProgram.fieldForkHonest`).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge IOP

section

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)
  (TA : ir.CircuitsAccept I src)

/-- **Each branch's simulator** (`branchSim`).

Running time: that of `branchSim`. This running time is argued here, not proved in Lean. -/
def forkBranchSim (b : Fin (ir.nBranch d R.Pk)) : ((ir.fieldFork src R).branch b).Sim :=
  ir.branchSim src R.rs (ir.branchEquiv d R.Pk b)

/-- **Each branch's honest masked reduction** at the join's logical assignment (`branchHonest`,
`fieldFork_view`), simulated by `forkBranchSim`. -/
noncomputable def forkBranchHonest (b : Fin (ir.nBranch d R.Pk)) :
    ((ir.fieldFork src R).branch b).Honest (ir.fieldFork src R).view
      (ir.Cell d → (I (ir.domainField d)).K) (ir.HonestDom d) (forkBranchSim src R b) :=
  (ir.branchHonest src R.rs R.claimOk TA (ir.branchEquiv d R.Pk b)).congrView
    (fieldFork_view src R).symm

/-- **The join's commitment**: the committed cells commit every branch at its pads, and the rows. -/
def ForkCommit (p' : (ir.fieldFork src R).JoinPub)
    (x : (ir.fieldFork src R).JoinIn (forkBranchHonest src R TA))
    (w : ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K) : Prop :=
  (∀ b, (ir.branchHonest src R.rs R.claimOk TA (ir.branchEquiv d R.Pk b)).Commits p'.1 x.1 (x.2 b) w) ∧
    ir.RowsCommit src R.rs p'.1 x.1 w

/-- **The join's masked reduction is complete at the honest branches' transcripts**: every branch's output
by its completeness, the rows by `rows_of_honest` (`outHolds_fieldForkTranscript_iff`). -/
theorem forkJoin_complete : ∀ p' x, (ir.fieldFork src R).JoinDom (forkBranchHonest src R TA) p' x →
    ∀ w, ForkCommit src R TA p' x w →
      (ir.fieldMaskedReduction src R.rs).OutHolds (ir.fieldFork src R).join.path.level.view p'.1
        (ir.fieldForkTranscript src R p'.2) w := by
  intro p' x hx w hw
  obtain ⟨hdom, chs, htrs⟩ := hx
  refine (ir.outHolds_fieldForkTranscript_iff src R _ p'.1 p'.2 w).2 ⟨fun b => ?_, ?_⟩
  · rw [htrs b]
    exact (forkBranchHonest src R TA b).complete p'.1 x.1 hdom (x.2 b) w (hw.1 b) (chs b)
  · have h := rows_of_honest R.claimOk p'.1 x.1 hdom w hw.2
    unfold FixedAt
    rw [show (ir.fieldFork src R).join.path.level.view =
      (ir.treeLevel d R.rs (ir.ClaimPads d src R.Pk)).view from fieldFork_view src R]
    exact h

/-- **The join's masked-reduction simulator**: the empty simulator at the fixed transcripts
(`MaskedReduction.Sim.fixAt`).

Running time: constant. This running time is argued here, not proved in Lean. -/
def forkJoinClaimSim : (ir.fieldFork src R).join.maskedReduction.Sim :=
  FieldProof.MaskedReduction.Sim.fixAt (ir.fieldMaskedReduction src R.rs) Prod.fst
    (fun p' => ir.fieldForkTranscript src R p'.2)

/-- **The join's honest masked reduction**: the domain's masked reduction at the honest branches' transcripts
(`MaskedReduction.Honest.fixAt`), its committed cells' words the honest logical assignment's;
simulated by `forkJoinClaimSim`. -/
def forkJoinClaimHonest :
    (ir.fieldFork src R).join.maskedReduction.Honest (ir.fieldFork src R).join.path.level.view
      ((ir.fieldFork src R).JoinIn (forkBranchHonest src R TA))
      ((ir.fieldFork src R).JoinDom (forkBranchHonest src R TA)) (forkJoinClaimSim src R) :=
  (FieldProof.MaskedReduction.Honest.fixAt (ir.fieldMaskedReduction src R.rs) Prod.fst (fun p' => ir.fieldForkTranscript src R p'.2)
    (ForkCommit src R TA) (forkJoin_complete src R TA)).withCommits fun _ x _ w =>
      ∀ z, (ir.fieldFork src R).join.path.IsWord z →
        (ir.treeLevel d R.rs (ir.ClaimPads d src R.Pk)).view w z = ir.fieldHonestLog src R.rs x.1 z

theorem forkJoinClaimHonest_val_word : ∀ p' x π w, (forkJoinClaimHonest src R TA).Commits p' x π w →
    ∀ z, (ir.fieldFork src R).join.path.IsWord z →
      (ir.fieldFork src R).join.path.level.view w z = ir.fieldHonestLog src R.rs x.1 z :=
  fun _p _x _π _w hw z hz => by
    rw [show (ir.fieldFork src R).join.path.level.view =
      (ir.treeLevel d R.rs (ir.ClaimPads d src R.Pk)).view from fieldFork_view src R]
    exact hw.2 z hz

/-- **The join's simulator data** (`RingSwitching.TreeFieldProof.SimData`): the join's masked-reduction
simulator (`forkJoinClaimSim`) and the tree layout's Ligero hiding data. -/
def forkJoinSimData : (ir.fieldFork src R).join.SimData where
  maskedReduction := forkJoinClaimSim src R
  ligero := (ir.fieldTreeOf src R).layoutHiding R.numbers (ir.fieldJoinMaskedReduction src R)
    (routes_path _ 0 _ _ _ _ ((readsOnly_fieldMaskedReduction src R.rs).fixAt _ _))

/-- **The join's honest data** (`RingSwitching.TreeFieldProof.HonestData`): the join's honest masked reduction
(`forkJoinClaimHonest`), the kits' honest masks, the honest logical assignment as the words'
values, the tree layout's Ligero honest prover, and the honest committed cells at the branches' pads
(`fieldHonestCells`), which commit every branch (`branch_commits`), the rows, the words and the
masks, their prefix cells in `S0`. -/
def forkJoinHonestData :
    (ir.fieldFork src R).join.HonestData (ir.fieldForkSound src R).joinRel (forkJoinSimData src R)
      ((ir.fieldFork src R).JoinIn (forkBranchHonest src R TA))
      ((ir.fieldFork src R).JoinDom (forkBranchHonest src R TA)) where
  maskedReduction := forkJoinClaimHonest src R TA
  masks := maskHonest (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
  val _ x _ := ir.fieldHonestLog src R.rs x.1
  val_word := forkJoinClaimHonest_val_word src R TA
  cells x π :=
    ir.fieldHonestCells x.1 x.2
      (splitPads (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
        (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
        (routes_path _ 0 _ _ _ _ ((readsOnly_fieldMaskedReduction src R.rs).fixAt _ _)) (forkJoinClaimHonest src R TA) (fun _ x _ => ir.fieldHonestLog src R.rs x.1)
        (forkJoinClaimHonest_val_word src R TA) π).2
  commits p' x π hx := by
    have hok := R.claimOk
    have hbase := hx.1.1.base
    set sp := splitPads (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
      (routes_path _ 0 _ _ _ _ ((readsOnly_fieldMaskedReduction src R.rs).fixAt _ _)) (forkJoinClaimHonest src R TA) (fun _ x _ => ir.fieldHonestLog src R.rs x.1)
      (forkJoinClaimHonest_val_word src R TA) π with hsp
    refine (commits_honestRun_iff _ 0 _ _ _ _ _ _ _ p' x π _).2 ⟨⟨⟨fun b => ?_, ?_⟩, ?_⟩, ?_⟩
    · let bp : ir.BranchPads src R.rs R.claimOk TA := x.2
      have hc := branch_commits R.claimOk TA p'.1 hbase bp sp.2 (ir.branchEquiv d R.Pk b)
      rw [padsOfIdx_branch bp b] at hc
      exact hc
    · exact ⟨(fieldHonestCells_place hbase _ _).1.trans (treeCells_fieldHonestLog hok hbase),
        (fieldHonestCells_place hbase _ _).2⟩
    · intro z hz
      exact honestView_word (Pads := ir.ClaimPads d src R.Pk) hok.tree hok.place hbase _ 0 _ 0 _ 0 _ _ z hz
    · exact maskCommits_of_maskVal _ _ (maskCellsDistinct_fieldEdges R.rs) _
        (fieldHonestCells_maskVal src R TA _ _)
  admissible p' x π hx := by
    refine TreeSpec.admissible_layoutDomain _ _ _ _ fun j => ?_
    change ir.fieldHonestCells x.1 _ _ (.inl j) ∈ R.Pk.S0
    simp only [fieldHonestCells, treeHonestCells, cellVal, treeRootAt, treeBase]
    cases hv : maskVal (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) _ (.inl j) with
    | none => exact R.Pk.S0.zero_mem
    | some v =>
      obtain ⟨e, he, πe, c, hc, rfl⟩ := exists_of_maskVal (h := hv) ..
      rcases c with j0 | o
      · exact e.kit.masks.preVal_mem πe j0
      · obtain ⟨o', ho'⟩ := fieldEdges_maskOwn he o
        exact absurd (hc.symm.trans ho') (by simp)

/-- **The simulator data of the forked domain `d`** (`TreeFork.SimData`): every branch's simulator
(`forkBranchSim`) and the join's simulator data (`forkJoinSimData`). -/
def forkSimData : (ir.fieldFork src R).SimData where
  branch := forkBranchSim src R
  join := forkJoinSimData src R

/-- **The simulator of the forked domain `d`** (`TreeFork.simulatorOf` at the fixed claims and
`forkSimData`), of its forked circuit proof (`fieldForkShape`, `fieldForkOracle`).

Running time: that of `TreeFork.simulatorOf` (its paragraph). This running time is argued here, not
proved in Lean. -/
def fieldForkSim : (ir.fieldForkShape src R).Simulator (ir.fieldForkOracle src R) :=
  (ir.fieldFork src R).simulatorOf (FixedAt (R := R) (ir.fieldFork src R).view) (fun x => x)
    (forkSimData src R)

/-- **The honest data of the forked domain `d`** (`TreeFork.Sound.HonestData`) on the honest domain
(`HonestDom`), simulated by `forkSimData`: the branches' honest masked reductions (`forkBranchHonest`)
and the join's honest data (`forkJoinHonestData`). `TA`: the compiler's completeness (trust base). -/
noncomputable def fieldForkHonest :
    (ir.fieldForkSound src R).HonestData (forkSimData src R) (ir.Cell d → (I (ir.domainField d)).K)
      (ir.HonestDom d) where
  branch := forkBranchHonest src R TA
  join := forkJoinHonestData src R TA

end

end GordieHowe.RealizedProgram
