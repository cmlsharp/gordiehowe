-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Program.FieldForkCodecs
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.Transcript.TranscriptData

@[expose] public section

/-!
# GordieHowe: the series–parallel transcript of a program on the generic per-field domain proofs

The C++ series–parallel transcript (`GordieHowe.SPBCS.ProofSystemTranscript`) of the multi-circuit IOP with forked
domains on the generic per-field domain proofs (`GordieHowe.RealizedProgram.ProofSystem.fieldBranches`), from the program's own
parts (label, statement codec, branch names, the phases' codecs and readers) and every domain's
field codec (`GordieHowe.RealizedProgram.FieldCodec`) and size bounds (`GordieHowe.RealizedProgram.ForkFits`):

* **the transcript** (`GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscript`): every domain's commit rounds, branches, join
  and leaves by `FieldForkCodecs`, and a declared largest grant;
* **the largest grant** (`GordieHowe.RealizedProgram.ProofSystem.sup_fieldForkTranscript_maxGrant`): when the fields' readers
  grant nothing, the commit rounds and the branches grant nothing, so the largest grant of a round is
  the application phase's and the joins' (`GordieHowe.RealizedProgram.ProofSystem.fieldForkGrant`), read off the plan;
* **the loads** (`GordieHowe.RealizedProgram.ProofSystem.fieldForkLoads`): every round's load within its domain's `forkLoad`, the
  phases' given;
* **the round errors** (`GordieHowe.RealizedProgram.ProofSystem.fieldForkError_le`): every domain's commit rounds within its
  certified commit bound, a batch branch's rounds within the batch's summed errors and GKR's
  rounds within `max 3 (2 · gkrWidth)/|K|` each (`branchError_le`), the join's combinations, test and column query each within its own term
  (`GordieHowe.RingSwitching.TreeFieldProof.error_le_of`), as `FieldRoundsLe` lists them;
* **the queries and the leaves** (`GordieHowe.RealizedProgram.ProofSystem.fieldIop_queries`, `GordieHowe.RealizedProgram.ProofSystem.fieldIop_nLeaves`);
* **the rounds of the branches** (`GordieHowe.RealizedProgram.colsIP_n`, `GordieHowe.RealizedProgram.mergedIP_n`,
  `GordieHowe.RealizedProgram.gkrBranch_n`).
-/

namespace GordieHowe.RealizedProgram.ProofSystem.IOP

open GordieHowe.IOP IOP.ProtocolSpec IOP.SPTerm SPBCS

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel)

/-- **Every component's readers at their grants** satisfy `good` when the domains' commit rounds',
the application phase's, the branches' and the join parts' do (as `readersOf_allLoads`). -/
theorem readersOf_allGranted {rr : ∀ d, SpecReaders (C.circuit d).commitRounds}
    {rApp : SpecReaders C.app.spec} {rbr : ∀ d b, SpecReaders ((C.circuit d).branch b)}
    {rjn : ∀ d, SpecReaders (C.circuit d).join} {good : ℕ → SPBCS.Load → Prop}
    (hr : ∀ d, (rr d).AllGranted good) (happ : rApp.AllGranted good)
    (hbr : ∀ d b, (rbr d b).AllGranted good) (hjn : ∀ d, (rjn d).AllGranted good) :
    ∀ j, (C.readersOf rr rApp rbr rjn j).AllGranted good
  | .pre => SpecReaders.AllGranted.append (r₁ := fun c => (commitSpec.not_challengeIdx c).elim)
      (fun c => (commitSpec.not_challengeIdx c).elim)
      (SpecReaders.AllGranted.append (SpecReaders.AllGranted.appendN C.m hr) happ)
  | .br d b => hbr d b
  | .jn d => hjn d

/-- **The largest grant of a round of any component** is the application phase's and the join
parts' when the domains' commit rounds and the branches grant nothing. -/
theorem sup_readersOf_maxGrant {rr : ∀ d, SpecReaders (C.circuit d).commitRounds}
    {rApp : SpecReaders C.app.spec} {rbr : ∀ d b, SpecReaders ((C.circuit d).branch b)}
    {rjn : ∀ d, SpecReaders (C.circuit d).join} (hr : ∀ d, (rr d).Ungranted)
    (hbr : ∀ d b, (rbr d b).Ungranted) :
    Finset.univ.sup (fun q : C.term.Leaf => (C.readersOf rr rApp rbr rjn q.label).maxGrant) =
      max rApp.maxGrant (Finset.univ.sup fun d => (rjn d).maxGrant) := by
  have h0 : ∀ x : SpecReaders (commitSpec C.Com), x.maxGrant = 0 := fun x =>
    SpecReaders.Ungranted.maxGrant_eq fun c => (commitSpec.not_challengeIdx c).elim
  have hpre : (C.readersOf rr rApp rbr rjn .pre).maxGrant = rApp.maxGrant := by
    change (((fun c => (commitSpec.not_challengeIdx c).elim : SpecReaders (commitSpec C.Com))) ++
      (SpecReaders.appendN C.m rr ++ rApp)).maxGrant = _
    rw [SpecReaders.maxGrant_append, SpecReaders.maxGrant_append, h0,
      SpecReaders.Ungranted.maxGrant_eq (SpecReaders.AllGranted.appendN C.m hr)]
    simp
  have hleaf : ∀ j, (C.readersOf rr rApp rbr rjn j).maxGrant ≤
      Finset.univ.sup (fun q : C.term.Leaf => (C.readersOf rr rApp rbr rjn q.label).maxGrant) := by
    intro j
    have h := Finset.le_sup (f := fun q : C.term.Leaf => (C.readersOf rr rApp rbr rjn q.label).maxGrant)
      (Finset.mem_univ (Shape.leafOf (S := C.shape) j))
    rwa [Shape.label_leafOf] at h
  refine le_antisymm (Finset.sup_le fun q _ => ?_) (max_le ?_ (Finset.sup_le fun d _ => ?_))
  · generalize q.label = j
    match j with
    | .pre => exact hpre.le.trans (le_max_left _ _)
    | .br d b => exact ((hbr d b).maxGrant_eq).le.trans (Nat.zero_le _)
    | .jn d =>
      exact le_trans (Finset.le_sup (f := fun d => (rjn d).maxGrant) (Finset.mem_univ d))
        (le_max_right _ _)
  · exact hpre.symm.le.trans (hleaf .pre)
  · exact hleaf (.jn d)

end GordieHowe.RealizedProgram.ProofSystem.IOP

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations
open scoped NNReal

section

/-- **The codecs of a field**: its byte codec and its challenge reader. -/
structure FieldCodec (F : FieldInterp) where
  /-- The bytes of a field element. -/
  fb : ℕ
  /-- The byte codec. -/
  FB : SPBCS.Codec.FieldBytes F.K fb
  /-- The challenge reader. -/
  rd : CReader F.K

/-- **The size bounds of domain `d`'s forked proof at `2^20` bytes**: the arrays at most `Mx`
elements (`ForkSizesLe`), a GKR message and the tableau's writes within `2^20` bytes, the
challenge reads at most `Lmax` elements (`ForkLoadSizesLe`). -/
structure ForkFits {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
    (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)
    (cod : FieldCodec (I (ir.domainField d))) where
  /-- The largest array. -/
  Mx : ℕ
  /-- An array of `Mx` elements fits. -/
  mx : 9 + Mx * cod.fb ≤ 2 ^ 20
  /-- The arrays have at most `Mx` elements. -/
  sizes : ForkSizesLe R Mx
  /-- A GKR message fits. -/
  gkr : 2 * (1 + cod.fb) ≤ 2 ^ 20
  /-- The tableau's writes fit. -/
  ligero : LigeroFits cod.fb (ir.fieldFork src R).join.N (ir.fieldFork src R).join.code.k
    (ir.fieldFork src R).join.cp.nrep (2 ^ 20)
  /-- The largest challenge read. -/
  Lmax : ℕ
  /-- The challenge reads have at most `Lmax` elements. -/
  loads : ForkLoadSizesLe src R Lmax
  /-- The stream grants of the join's challenges (none by default). -/
  grants : ForkGrants := {}

/-! ## The rounds of the branches -/

section Rounds

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
  {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge (I (ir.domainField d)) Pk))

/-- A covered batch on columns has its batch phase's `2 n + 5` rounds. -/
theorem colsIP_n (i : Fin (ir.cbatches d Pk).length) :
    (ir.colsIP src rs i).n =
      2 * (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).n + 5 := by
  change 1 + (1 + (1 + (GKR.Schedule.roundLength _ + (1 + (1 + 0))))) = _
  rw [GKR.Schedule.roundLength_eq]
  omega

/-- A covered merged batch on columns has its batch phase's `2 n + 5` rounds: the merging challenge
is drawn in the zerocheck point's move. -/
theorem mergedIP_n (i : Fin (ir.mbatches d Pk).length) :
    (ir.mergedIP src rs i).n =
      2 * (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).n + 5 := by
  change 1 + (1 + (1 + (GKR.Schedule.roundLength _ + (1 + (1 + 0))))) = _
  rw [GKR.Schedule.roundLength_eq]
  omega

/-- A covered batch on bits has its batch phase's `2 n + 5` rounds and the `8` moves
of the `4` bit rounds. -/
theorem sumIP_n (i : Fin (ir.sumBatches d Pk).length) :
    (ir.sumIP src rs i).n =
      2 * (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).n + 13 := by
  change 1 + (1 + (1 + (GKR.Schedule.roundLength _ + (1 + (1 + 0))))) +
    GKR.Schedule.roundLength 4 = _
  rw [GKR.Schedule.roundLength_eq, GKR.Schedule.roundLength_eq]
  omega

/-- A covered merged batch on bits has its batch phase's `2 n + 5` rounds (the merging challenge
drawn in the zerocheck point's move) and the `8` moves of the `4` bit rounds. -/
theorem sumMergedIP_n (i : Fin (ir.sumMBatches d Pk).length) :
    (ir.sumMergedIP src rs i).n =
      2 * (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).n + 13 := by
  change 1 + (1 + (1 + (GKR.Schedule.roundLength _ + (1 + (1 + 0))))) +
    GKR.Schedule.roundLength 4 = _
  rw [GKR.Schedule.roundLength_eq, GKR.Schedule.roundLength_eq]
  omega

/-- GKR's branch has every circuit's `1 + circuitLength` rounds. -/
theorem gkrBranch_n :
    (ir.branchIP src rs (.inr ())).n = ((List.finRange (ir.circs d).length).map fun i =>
      1 + GKR.Schedule.circuitLength _ (ir.circSource d src i).circuit).sum := by
  change (FieldProof.MaskedReduction.ofList (ncOf := fun _ => 1) (ir.gkrIP src rs) (List.finRange _)).n = _
  rw [ofList_n]
  exact congrArg List.sum (List.map_congr_left fun i _ =>
    GordieHowe.GKR.LayeredCircuit.interaction_n _ _)

end Rounds

section ForkRounds

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)

/-- **The rounds of domain `d`'s branches and join besides the circuits' lengths**, at `Unit` pads:
every covered batch's `2 n + 5`, merged or not (`8` more on bits for the bit sumcheck), one
per circuit, the join's at most `2 · #edges + 3`. -/
noncomputable def forkRoundsConst : ℕ :=
  ∑ i : Fin (ir.cbatches d R.Pk).length,
      (2 * (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).n + 5) +
    ∑ i : Fin (ir.sumBatches d R.Pk).length,
      (2 * (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).n + 13) +
    ∑ i : Fin (ir.mbatches d R.Pk).length,
      (2 * (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).n + 5) +
    ∑ i : Fin (ir.sumMBatches d R.Pk).length,
      (2 * (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).n + 13) +
    (ir.circs d).length + (2 * R.rs.length + 3)

/-- **The rounds of domain `d`'s branches and join**: at most `forkRoundsConst` and every
circuit's `circuitLength`. -/
theorem fieldFork_rounds :
    ∑ b, (ir.fieldForkShape src R).bn b + (ir.fieldForkShape src R).jn ≤
      forkRoundsConst R + ∑ i, GKR.Schedule.circuitLength _ (ir.circSource d src i).circuit := by
  have hb : ∑ b, (ir.fieldForkShape src R).bn b =
      ((List.finRange (ir.nBranch d R.Pk)).map fun b =>
        (ir.branchIP src R.rs (ir.branchEquiv d R.Pk b)).n).sum := by
    rw [Fin.sum_univ_def]
  have hj := forkJoin_n_le src R
  rw [length_fieldEdges] at hj
  rw [hb, sum_branch (f := fun j => (ir.branchIP src R.rs j).n)]
  have hc : ∑ i : Fin (ir.cbatches d R.Pk).length,
      (ir.branchIP src R.rs (.inl (.inl (.inl i)))).n =
      ∑ i : Fin (ir.cbatches d R.Pk).length,
        (2 * (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).n + 5) :=
    Finset.sum_congr rfl fun i _ => colsIP_n src R.rs i
  have hsb : ∑ i : Fin (ir.sumBatches d R.Pk).length,
      (ir.branchIP src R.rs (.inl (.inl (.inr i)))).n =
      ∑ i : Fin (ir.sumBatches d R.Pk).length,
        (2 * (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).n + 13) :=
    Finset.sum_congr rfl fun i _ => sumIP_n src R.rs i
  have hm : ∑ i : Fin (ir.mbatches d R.Pk).length,
      (ir.branchIP src R.rs (.inl (.inr (.inl i)))).n =
      ∑ i : Fin (ir.mbatches d R.Pk).length,
        (2 * (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).n + 5) :=
    Finset.sum_congr rfl fun i _ => mergedIP_n src R.rs i
  have hsm : ∑ i : Fin (ir.sumMBatches d R.Pk).length,
      (ir.branchIP src R.rs (.inl (.inr (.inr i)))).n =
      ∑ i : Fin (ir.sumMBatches d R.Pk).length,
        (2 * (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).n + 13) :=
    Finset.sum_congr rfl fun i _ => sumMergedIP_n src R.rs i
  have hg : (ir.branchIP src R.rs (.inr ())).n =
      (ir.circs d).length + ∑ i, GKR.Schedule.circuitLength _ (ir.circSource d src i).circuit := by
    rw [gkrBranch_n, ← Fin.sum_univ_def, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [hc, hsb, hm, hsm, hg, forkRoundsConst]
  omega

/-- **A bound on domain `d`'s `forkLoad`**: the reader's `Lmax` draws, the `t` column indices of
`byteLen N` bytes. -/
theorem forkLoad_le (rd : CReader (I (ir.domainField d)).K) {Lmax : ℕ} {L : Load}
    (h : rd.load.nsmul Lmax ≤ L) (ht : (ir.fieldFork src R).join.cp.t ≤ L.draws)
    (hN : Rejection.byteLen (ir.fieldFork src R).join.N ≤ L.bytes) :
    forkLoad src R rd Lmax ≤ L := by
  rw [Load.le_iff] at h ⊢
  exact ⟨max_le h.1 ht, max_le h.2 hN⟩

variable {src R} in
/-- **The tableau's data rows are at most `Lmax`** when the challenge reads are and there is a
low-degree repetition. -/
theorem ForkLoadSizesLe.R_le {Lmax : ℕ} (h : ForkLoadSizesLe src R Lmax)
    (hn : 0 < (ir.fieldFork src R).join.cp.nrep) : (ir.fieldFork src R).join.R ≤ Lmax := by
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  have := Nat.le_mul_of_pos_left (ir.fieldFork src R).join.R hn
  omega

end ForkRounds

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)
  (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P) {W Stmt : Type}
  {rel : Set (ir.Valuation I × W)}
  (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
    (GordieHowe.Domain.lowered (B.withFieldProofs R).domains))
  (f : Stmt → ir.Valuation I) (cod : ∀ d : Fin ir.domains.length, FieldCodec (I (ir.domainField d)))
  (fits : ∀ d : Fin ir.domains.length, ForkFits B.src (R d) (cod d))

/-- **The multi-circuit IOP with forked domains on the generic per-field domain proofs** at the
lowering `Lw`, the statement read through `f`. -/
abbrev fieldIop := ((B.fieldBranches R).iopOf Lw).comap f

/-- **The C++ series–parallel transcript on the generic per-field domain proofs** (module docstring). -/
def fieldForkTranscript (label : List Byte) (k : ℕ) (stmt : Codec Stmt)
    (name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte)
    (appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20))
    (appReaders : SpecReaders (B.fieldIop R Lw f).app.spec) (maxGrant : ℕ) :
    ProofSystemTranscript (B.fieldIop R Lw f) where
  label := label
  k := k
  stmt := stmt
  name := name
  commitWrites d := forkCommitWrites B.src (R d) (cod d).FB (fits d).ligero.commit_le
  appWrites := appWrites
  branchWrites d b := forkBranchWrites B.src (R d) (cod d).FB (fits d).mx (fits d).sizes (fits d).gkr b
  joinWrites d := forkJoinWrites B.src (R d) (cod d).FB (fits d).mx (fits d).sizes (fits d).ligero
  leaf d := forkLeafCodec B.src (R d) (cod d).FB
  commitReaders d := forkCommitReaders B.src (R d) (cod d).rd
  appReaders := appReaders
  branchReaders d b := forkBranchReaders B.src (R d) (cod d).rd b
  joinReaders d := forkJoinReaders B.src (R d) (cod d).rd (fits d).grants
  maxGrant := maxGrant

/-- **The largest grant of the transcript on the generic per-field domain proofs** at the joins'
grants `g`: the application phase's readers' and every domain's join's (`forkJoinGrant`). -/
def fieldForkGrant (g : Fin ir.domains.length → ForkGrants) {n : ℕ} {Q : ProtocolSpec n}
    (appReaders : SpecReaders Q) : ℕ :=
  max appReaders.maxGrant (Finset.univ.sup fun d => forkJoinGrant (R d) (g d))

/-- **The largest grant of a round of the transcript** is `fieldForkGrant` when the fields'
readers grant nothing: the commit rounds and the branches grant nothing
(`IOP.sup_readersOf_maxGrant`). -/
theorem sup_fieldForkTranscript_maxGrant (hrd : ∀ d, (cod d).rd.grant = 0) {label : List Byte}
    {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIop R Lw f).app.spec} {mg : ℕ} :
    Finset.univ.sup (fun q : (B.fieldIop R Lw f).term.Leaf => ((B.fieldForkTranscript R Lw f cod fits
      label k stmt name appWrites appReaders mg).readers q.label).maxGrant) =
      fieldForkGrant R (fun d => (fits d).grants) appReaders :=
  ((B.fieldIop R Lw f).sup_readersOf_maxGrant (fun d => forkCommitReaders_ungranted (hrd d))
    (fun d b => forkBranchReaders_ungranted (hrd d) b)).trans
    (congrArg (max _) (Finset.sup_congr rfl fun d _ => maxGrant_forkJoinReaders (hrd d) _))

/-- **Every round's load satisfies `good`** when every load within its domain's `forkLoad` does and
the phases' readers' loads do. -/
theorem fieldForkLoads {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIop R Lw f).app.spec} {mg : ℕ} {good : Load → Prop}
    (hgood : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (fits d).Lmax → good L)
    (happ : appReaders.AllLoads good) :
    ∀ j, ((B.fieldForkTranscript R Lw f cod fits label k stmt name appWrites appReaders
      mg).readers j).AllLoads
      good :=
  (B.fieldIop R Lw f).readersOf_allLoads
    (fun d => (forkCommitReaders_allLoads (cod d).rd (fits d).loads.rest).mono fun _ h => hgood d _ h)
    happ
    (fun d _ => (branchReaders_allLoads (cod d).rd (fits d).loads.rest _).mono fun _ h => hgood d _ h)
    (fun d => (forkJoinReaders_allLoads (cod d).rd _ (fits d).loads).mono fun _ h => hgood d _ h)

/-- **Every round's load at its grant satisfies `good`**, a predicate larger grants keep, when
every load within its domain's `forkLoad` at the rest sizes `Lr d` passes at grant `0`, every
domain's first combination passes at its grant for every number of touching claims up to the
claim count, and the phases' readers do. -/
theorem fieldForkLoadsGranted {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIop R Lw f).app.spec} {mg : ℕ} {good : ℕ → Load → Prop}
    (hg : ∀ g L, good 0 L → good g L) {Lr : Fin ir.domains.length → ℕ}
    (hLr : ∀ d, ForkRestSizesLe B.src (R d) (Lr d))
    (hrest : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (Lr d) → good 0 L)
    (hstage : ∀ d : Fin ir.domains.length, ∀ n ≤ ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk),
      good ((CReader.pi n (cod d).rd).extend ((fits d).grants.stage 0)).grant
        ((cod d).rd.load.nsmul n))
    (happ : appReaders.AllGranted good) :
    ∀ j, ((B.fieldForkTranscript R Lw f cod fits label k stmt name appWrites appReaders
      mg).readers j).AllGranted
      good :=
  (B.fieldIop R Lw f).readersOf_allGranted
    (fun d => SpecReaders.AllGranted.of_allLoads hg
      ((forkCommitReaders_allLoads (cod d).rd (hLr d)).mono (hrest d)))
    happ
    (fun d _ => SpecReaders.AllGranted.of_allLoads hg
      ((branchReaders_allLoads (cod d).rd (hLr d) _).mono (hrest d)))
    (fun d => forkJoinReaders_allGranted (cod d).rd _ (hLr d) hg (hrest d) (hstage d))

/-! ### Statements read through a map and checked (`comapWith`) -/

/-- **The multi-circuit IOP with forked domains on the generic per-field domain proofs** at the
lowering `Lw`, the statement read through `f` and checked by `chk`. -/
abbrev fieldIopWith (chk : Stmt → Bool) :=
  ((B.fieldBranches R).iopOf Lw).comapWith f chk

/-- **The C++ series–parallel transcript of `fieldIopWith`** (as `fieldForkTranscript`). -/
def fieldForkTranscriptWith (chk : Stmt → Bool) (label : List Byte) (k : ℕ)
    (stmt : Codec Stmt)
    (name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m, Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) →
      List Byte)
    (appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20))
    (appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec) (maxGrant : ℕ) :
    ProofSystemTranscript (B.fieldIopWith R Lw f chk) where
  label := label
  k := k
  stmt := stmt
  name := name
  commitWrites d := forkCommitWrites B.src (R d) (cod d).FB (fits d).ligero.commit_le
  appWrites := appWrites
  branchWrites d b := forkBranchWrites B.src (R d) (cod d).FB (fits d).mx (fits d).sizes (fits d).gkr b
  joinWrites d := forkJoinWrites B.src (R d) (cod d).FB (fits d).mx (fits d).sizes (fits d).ligero
  leaf d := forkLeafCodec B.src (R d) (cod d).FB
  commitReaders d := forkCommitReaders B.src (R d) (cod d).rd
  appReaders := appReaders
  branchReaders d b := forkBranchReaders B.src (R d) (cod d).rd b
  joinReaders d := forkJoinReaders B.src (R d) (cod d).rd (fits d).grants
  maxGrant := maxGrant

/-- **The largest grant of a round of `fieldForkTranscriptWith`** (as
`sup_fieldForkTranscript_maxGrant`). -/
theorem sup_fieldForkTranscriptWith_maxGrant (hrd : ∀ d, (cod d).rd.grant = 0)
    {chk : Stmt → Bool} {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m, Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) →
      List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec} {mg : ℕ} :
    Finset.univ.sup (fun q : (B.fieldIopWith R Lw f chk).term.Leaf =>
      ((B.fieldForkTranscriptWith R Lw f cod fits chk label k stmt name appWrites appReaders
        mg).readers q.label).maxGrant) =
      fieldForkGrant R (fun d => (fits d).grants) appReaders :=
  ((B.fieldIopWith R Lw f chk).sup_readersOf_maxGrant (fun d => forkCommitReaders_ungranted (hrd d))
    (fun d b => forkBranchReaders_ungranted (hrd d) b)).trans
    (congrArg (max _) (Finset.sup_congr rfl fun d _ => maxGrant_forkJoinReaders (hrd d) _))

/-- **Every round's load of `fieldForkTranscriptWith` satisfies `good`** (as `fieldForkLoads`). -/
theorem fieldForkLoadsWith {chk : Stmt → Bool} {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m, Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) →
      List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec} {mg : ℕ} {good : Load → Prop}
    (hgood : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (fits d).Lmax → good L)
    (happ : appReaders.AllLoads good) :
    ∀ j, ((B.fieldForkTranscriptWith R Lw f cod fits chk label k stmt name appWrites
      appReaders mg).readers j).AllLoads good :=
  (B.fieldIopWith R Lw f chk).readersOf_allLoads
    (fun d => (forkCommitReaders_allLoads (cod d).rd (fits d).loads.rest).mono fun _ h => hgood d _ h)
    happ
    (fun d _ => (branchReaders_allLoads (cod d).rd (fits d).loads.rest _).mono fun _ h => hgood d _ h)
    (fun d => (forkJoinReaders_allLoads (cod d).rd _ (fits d).loads).mono fun _ h => hgood d _ h)

/-- **Every round's load of `fieldForkTranscriptWith` at its grant satisfies `good`** (as
`fieldForkLoadsGranted`). -/
theorem fieldForkLoadsGrantedWith {chk : Stmt → Bool} {label : List Byte} {k : ℕ}
    {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m, Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) →
      List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec} {mg : ℕ} {good : ℕ → Load → Prop}
    (hg : ∀ g L, good 0 L → good g L) {Lr : Fin ir.domains.length → ℕ}
    (hLr : ∀ d, ForkRestSizesLe B.src (R d) (Lr d))
    (hrest : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (Lr d) → good 0 L)
    (hstage : ∀ d : Fin ir.domains.length, ∀ n ≤ ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk),
      good ((CReader.pi n (cod d).rd).extend ((fits d).grants.stage 0)).grant
        ((cod d).rd.load.nsmul n))
    (happ : appReaders.AllGranted good) :
    ∀ j, ((B.fieldForkTranscriptWith R Lw f cod fits chk label k stmt name appWrites
      appReaders mg).readers j).AllGranted good :=
  (B.fieldIopWith R Lw f chk).readersOf_allGranted
    (fun d => SpecReaders.AllGranted.of_allLoads hg
      ((forkCommitReaders_allLoads (cod d).rd (hLr d)).mono (hrest d)))
    happ
    (fun d _ => SpecReaders.AllGranted.of_allLoads hg
      ((branchReaders_allLoads (cod d).rd (hLr d) _).mono (hrest d)))
    (fun d => forkJoinReaders_allGranted (cod d).rd _ (hLr d) hg (hrest d) (hstage d))

/-- Domain `d` has a branch per covered batch and GKR's (`nBranch`). -/
theorem fieldForkNb (d : Fin (B.fieldIop R Lw f).m) :
    ((B.fieldIop R Lw f).circuit d).nb = ir.nBranch d (R d).Pk :=
  rfl

/-- **Every round of the series–parallel composite on the generic per-field domain proofs, on its own,
is at most `δ`** (`IOP.Sound.error_le`): every domain's round charges within `δ`
(`FieldRoundsLe`): its commit rounds within its certified commit bound
(`RingSwitching.TreeFieldProof.sum_commitError`), a batch branch's rounds within the batch's summed errors and GKR's
rounds within `max 3 (2 · gkrWidth)/|K|` each (`branchError_le`), the join's combinations, test and column query within their own terms
(`RingSwitching.TreeFieldProof.error_le_of`); and the phases' given. -/
theorem fieldForkError_le [Inhabited W] {proj : ir.Valuation I → ir.Assignment I → W}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) {δ : ℝ≥0}
    (hk : ∀ d : Fin ir.domains.length, ir.FieldRoundsLe (R d) δ)
    (happ : ∀ j, ((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).εapp j ≤ δ) :
    ∀ c, (((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).comap f).error c ≤ δ := by
  have single : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ≥0) (j : ι), g j ≤ ∑ i, g i := fun g j =>
    Finset.single_le_sum (f := g) (fun _ _ => zero_le) (Finset.mem_univ j)
  refine IOP.Sound.error_le _ (fun d j => ?_) happ (fun d b j => ?_) (fun d j => ?_)
  · have hsum := ((ir.fieldFork B.src (R d)).join.sum_commitError
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound).trans
      (congrArg Ligero.AgreementThreshold.Bounds.commit
        (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..))
    exact (single _ j).trans (hsum.trans_le (hk d).commit)
  · exact ir.branchError_le B.src (R d).rs B.enforce (hk d).batches (hk d).gkr _ j
  · refine (ir.fieldFork B.src (R d)).join.error_le_of
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound
      ?_ ((congrArg Ligero.AgreementThreshold.Bounds.test
        (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..)).trans_le (hk d).test) (by
        rw [show (ir.fieldFork B.src (R d)).join.cp.t = (R d).numbers.Sh.nreq from
            Ligero.MaskRow.TreeLayout.Numbers.t_setup ..,
          show (ir.fieldFork B.src (R d)).join.cp.bounds = (R d).numbers.bounds from
            Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..]
        exact (hk d).column) j
    rw [Finset.sum_eq_zero fun i _ => Fin.elim0 i.1, zero_add]
    refine le_trans ?_ (hk d).combinations
    gcongr
    exact_mod_cast ir.combinations_fieldTreeOf_le B.src (R d)

/-- **The round errors of the series–parallel composite on the generic per-field domain proofs sum
to at most** the domains' `fieldSumBound` and the application phase's errors
(`IOP.Sound.sum_error`): each domain's commit rounds to its certified commit bound
(`RingSwitching.TreeFieldProof.sum_commitError`), its branches to the covered batches' phase errors
and GKR's shape budgets (`sum_branchError_le`), its join to the combinations', test and column
terms (`RingSwitching.TreeFieldProof.sum_ipError`, `sum_cpError`). -/
theorem fieldForkError_sum_le [Inhabited W] {proj : ir.Valuation I → ir.Assignment I → W}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    ∑ c, (((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).comap f).error c ≤
      ∑ d : Fin ir.domains.length, ir.fieldSumBound I (R d) +
        ∑ j, ((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).εapp j := by
  refine IOP.Sound.sum_error_le _ fun d => ?_
  have hsum := ((ir.fieldFork B.src (R d)).join.sum_commitError
    (Rel := (ir.fieldForkSound B.src (R d)).joinRel)
    (ir.fieldForkSound B.src (R d)).joinSound).trans
    (congrArg Ligero.AgreementThreshold.Bounds.commit
      (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..))
  have hjoin := (ir.fieldFork B.src (R d)).join.sum_error
    (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound
  have h0 : ∑ i, (ir.fieldForkSound B.src (R d)).εj i = 0 := Finset.sum_eq_zero fun i _ => i.1.elim0
  rw [h0, zero_add, RingSwitching.TreeFieldProof.cpError,
    show (ir.fieldFork B.src (R d)).join.cp.t = (R d).numbers.Sh.nreq from
      Ligero.MaskRow.TreeLayout.Numbers.t_setup ..,
    show (ir.fieldFork B.src (R d)).join.cp.bounds = (R d).numbers.bounds from
      Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..] at hjoin
  have hj2 : ∑ j, ((ir.fieldFork B.src (R d)).join.sound
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel)
      (ir.fieldForkSound B.src (R d)).joinSound).error j =
      ((ir.fieldFork B.src (R d)).join.path.combinations : ℝ≥0) /
        Fintype.card (I (ir.domainField d)).K +
      ((R d).numbers.bounds.test + (R d).numbers.bounds.column +
        (if npOf (R d).Pk (R d).rs = 0 then 0 else
          Ligero.SubfieldTest.jointSubfieldError (R d).numbers.Sh.block (R d).numbers.Sh.N
            (R d).numbers.Sh.nreq)) := hjoin
  have hc : ((ir.fieldFork B.src (R d)).join.path.combinations : ℝ≥0) ≤ (R d).rs.length := by
    exact_mod_cast ir.combinations_fieldTreeOf_le B.src (R d)
  refine (add_le_add (le_of_eq hsum) (add_le_add (ir.sum_branchError_le B.src (R d).rs B.enforce)
    (le_of_eq hj2))).trans ?_
  rw [fieldSumBound]
  have hq : ((ir.fieldFork B.src (R d)).join.path.combinations : ℝ≥0) /
      Fintype.card (I (ir.domainField d)).K ≤
      ((R d).rs.length : ℝ≥0) / Fintype.card (I (ir.domainField d)).K := by gcongr
  calc _ ≤ (R d).numbers.bounds.commit + (ir.batchesError d (R d).Pk + ir.gkrSumError I d +
        (((R d).rs.length : ℝ≥0) / Fintype.card (I (ir.domainField d)).K +
          ((R d).numbers.bounds.test + (R d).numbers.bounds.column +
          (if npOf (R d).Pk (R d).rs = 0 then 0 else
            Ligero.SubfieldTest.jointSubfieldError (R d).numbers.Sh.block (R d).numbers.Sh.N
              (R d).numbers.Sh.nreq)))) := by gcongr
    _ = _ := by ring

/-- **Every round of the composite read through `f` and checked** (as `fieldForkError_le`). -/
theorem fieldForkErrorWith_le [Inhabited W] {chk : Stmt → Bool} {proj : ir.Valuation I → ir.Assignment I → W}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) {δ : ℝ≥0}
    (hk : ∀ d : Fin ir.domains.length, ir.FieldRoundsLe (R d) δ)
    (happ : ∀ j, ((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).εapp j ≤ δ) :
    ∀ c, (((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).comapWith f chk).error c ≤ δ := by
  have single : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ≥0) (j : ι), g j ≤ ∑ i, g i := fun g j =>
    Finset.single_le_sum (f := g) (fun _ _ => zero_le) (Finset.mem_univ j)
  refine IOP.Sound.error_le _ (fun d j => ?_) happ (fun d b j => ?_) (fun d j => ?_)
  · have hsum := ((ir.fieldFork B.src (R d)).join.sum_commitError
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound).trans
      (congrArg Ligero.AgreementThreshold.Bounds.commit
        (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..))
    exact (single _ j).trans (hsum.trans_le (hk d).commit)
  · exact ir.branchError_le B.src (R d).rs B.enforce (hk d).batches (hk d).gkr _ j
  · refine (ir.fieldFork B.src (R d)).join.error_le_of
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound
      ?_ ((congrArg Ligero.AgreementThreshold.Bounds.test
        (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..)).trans_le (hk d).test) (by
        rw [show (ir.fieldFork B.src (R d)).join.cp.t = (R d).numbers.Sh.nreq from
            Ligero.MaskRow.TreeLayout.Numbers.t_setup ..,
          show (ir.fieldFork B.src (R d)).join.cp.bounds = (R d).numbers.bounds from
            Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..]
        exact (hk d).column) j
    rw [Finset.sum_eq_zero fun i _ => Fin.elim0 i.1, zero_add]
    refine le_trans ?_ (hk d).combinations
    gcongr
    exact_mod_cast ir.combinations_fieldTreeOf_le B.src (R d)


/-- **The round errors of the composite read through `f` and checked sum to at most** the
domains' `fieldSumBound` and the application phase's errors
(`IOP.Sound.sum_error`): each domain's commit rounds to its certified commit bound
(`RingSwitching.TreeFieldProof.sum_commitError`), its branches to the covered batches' phase errors
and GKR's shape budgets (`sum_branchError_le`), its join to the combinations', test and column
terms (`RingSwitching.TreeFieldProof.sum_ipError`, `sum_cpError`). -/
theorem fieldForkErrorWith_sum_le [Inhabited W] {chk : Stmt → Bool}
    {proj : ir.Valuation I → ir.Assignment I → W}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (h : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    ∑ c, (((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).comapWith f chk).error
      c ≤
      ∑ d : Fin ir.domains.length, ir.fieldSumBound I (R d) +
        ∑ j, ((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) h hend).εapp j := by
  refine IOP.Sound.sum_error_le _ fun d => ?_
  have hsum := ((ir.fieldFork B.src (R d)).join.sum_commitError
    (Rel := (ir.fieldForkSound B.src (R d)).joinRel)
    (ir.fieldForkSound B.src (R d)).joinSound).trans
    (congrArg Ligero.AgreementThreshold.Bounds.commit
      (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..))
  have hjoin := (ir.fieldFork B.src (R d)).join.sum_error
    (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound
  have h0 : ∑ i, (ir.fieldForkSound B.src (R d)).εj i = 0 := Finset.sum_eq_zero fun i _ => i.1.elim0
  rw [h0, zero_add, RingSwitching.TreeFieldProof.cpError,
    show (ir.fieldFork B.src (R d)).join.cp.t = (R d).numbers.Sh.nreq from
      Ligero.MaskRow.TreeLayout.Numbers.t_setup ..,
    show (ir.fieldFork B.src (R d)).join.cp.bounds = (R d).numbers.bounds from
      Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..] at hjoin
  have hj2 : ∑ j, ((ir.fieldFork B.src (R d)).join.sound
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel)
      (ir.fieldForkSound B.src (R d)).joinSound).error j =
      ((ir.fieldFork B.src (R d)).join.path.combinations : ℝ≥0) /
        Fintype.card (I (ir.domainField d)).K +
      ((R d).numbers.bounds.test + (R d).numbers.bounds.column +
        (if npOf (R d).Pk (R d).rs = 0 then 0 else
          Ligero.SubfieldTest.jointSubfieldError (R d).numbers.Sh.block (R d).numbers.Sh.N
            (R d).numbers.Sh.nreq)) := hjoin
  have hc : ((ir.fieldFork B.src (R d)).join.path.combinations : ℝ≥0) ≤ (R d).rs.length := by
    exact_mod_cast ir.combinations_fieldTreeOf_le B.src (R d)
  refine (add_le_add (le_of_eq hsum) (add_le_add (ir.sum_branchError_le B.src (R d).rs B.enforce)
    (le_of_eq hj2))).trans ?_
  rw [fieldSumBound]
  have hq : ((ir.fieldFork B.src (R d)).join.path.combinations : ℝ≥0) /
      Fintype.card (I (ir.domainField d)).K ≤
      ((R d).rs.length : ℝ≥0) / Fintype.card (I (ir.domainField d)).K := by gcongr
  calc _ ≤ (R d).numbers.bounds.commit + (ir.batchesError d (R d).Pk + ir.gkrSumError I d +
        (((R d).rs.length : ℝ≥0) / Fintype.card (I (ir.domainField d)).K +
          ((R d).numbers.bounds.test + (R d).numbers.bounds.column +
          (if npOf (R d).Pk (R d).rs = 0 then 0 else
            Ligero.SubfieldTest.jointSubfieldError (R d).numbers.Sh.block (R d).numbers.Sh.N
              (R d).numbers.Sh.nreq)))) := by gcongr
    _ = _ := by ring

end ProofSystem

end

end GordieHowe.RealizedProgram
