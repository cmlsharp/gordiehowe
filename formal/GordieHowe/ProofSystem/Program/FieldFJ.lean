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
  and leaves by `FieldForkCodecs`;
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

/-- A covered merged batch on columns has its merging challenge and its batch phase's `2 n + 5` rounds. -/
theorem mergedIP_n (i : Fin (ir.mbatches d Pk).length) :
    (ir.mergedIP src rs i).n =
      2 * (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).n + 6 := by
  change 1 + (1 + (1 + (1 + (GKR.Schedule.roundLength _ + (1 + (1 + 0)))))) = _
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

/-- A covered merged batch on bits has its merging challenge, its batch phase's
`2 n + 5` rounds and the `8` moves of the `4` bit rounds. -/
theorem sumMergedIP_n (i : Fin (ir.sumMBatches d Pk).length) :
    (ir.sumMergedIP src rs i).n =
      2 * (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).n + 14 := by
  change 1 + (1 + (1 + (1 + (GKR.Schedule.roundLength _ + (1 + (1 + 0)))))) +
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
every covered batch's `2 n + 5` (`2 n + 6` merged, `8` more on bits for the bit sumcheck), one
per circuit, the join's at most `2 · #edges + 3`. -/
noncomputable def forkRoundsConst : ℕ :=
  ∑ i : Fin (ir.cbatches d R.Pk).length,
      (2 * (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).n + 5) +
    ∑ i : Fin (ir.sumBatches d R.Pk).length,
      (2 * (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).n + 13) +
    ∑ i : Fin (ir.mbatches d R.Pk).length,
      (2 * (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).n + 6) +
    ∑ i : Fin (ir.sumMBatches d R.Pk).length,
      (2 * (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).n + 14) +
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
        (2 * (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).n + 6) :=
    Finset.sum_congr rfl fun i _ => mergedIP_n src R.rs i
  have hsm : ∑ i : Fin (ir.sumMBatches d R.Pk).length,
      (ir.branchIP src R.rs (.inl (.inr (.inr i)))).n =
      ∑ i : Fin (ir.sumMBatches d R.Pk).length,
        (2 * (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).n + 14) :=
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
    (GordieHowe.Domain.lowered (B.withFieldProofs R).guardedDomain))
  (f : Stmt → ir.Valuation I) (cod : ∀ d : Fin ir.domains.length, FieldCodec (I (ir.domainField d)))
  (fits : ∀ d : Fin ir.domains.length, ForkFits B.src (R d) (cod d))

/-- **The multi-circuit IOP with forked domains on the generic per-field domain proofs** at the
lowering `Lw`, the statement read through `f`. -/
abbrev fieldIop := ((B.fieldBranches R).iopOf Lw).comap f

/-- **The C++ series–parallel transcript on the generic per-field domain proofs** (module docstring). -/
def fieldForkTranscript (label : List Byte) (k : ℕ) (stmt : Codec Stmt)
    (name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte)
    (appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20))
    (appReaders : SpecReaders (B.fieldIop R Lw f).app.spec) :
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

/-- **Every round's load satisfies `good`** when every load within its domain's `forkLoad` does and
the phases' readers' loads do. -/
theorem fieldForkLoads {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIop R Lw f).app.spec} {good : Load → Prop}
    (hgood : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (fits d).Lmax → good L)
    (happ : appReaders.AllLoads good) :
    ∀ j, ((B.fieldForkTranscript R Lw f cod fits label k stmt name appWrites appReaders).readers j).AllLoads
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
    {appReaders : SpecReaders (B.fieldIop R Lw f).app.spec} {good : ℕ → Load → Prop}
    (hg : ∀ g L, good 0 L → good g L) {Lr : Fin ir.domains.length → ℕ}
    (hLr : ∀ d, ForkRestSizesLe B.src (R d) (Lr d))
    (hrest : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (Lr d) → good 0 L)
    (hstage : ∀ d : Fin ir.domains.length, ∀ n ≤ ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk),
      good ((CReader.pi n (cod d).rd).extend ((fits d).grants.stage 0)).grant
        ((cod d).rd.load.nsmul n))
    (happ : appReaders.AllGranted good) :
    ∀ j, ((B.fieldForkTranscript R Lw f cod fits label k stmt name appWrites appReaders).readers j).AllGranted
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
    (appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec) :
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

/-- **Every round's load of `fieldForkTranscriptWith` satisfies `good`** (as `fieldForkLoads`). -/
theorem fieldForkLoadsWith {chk : Stmt → Bool} {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m, Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) →
      List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec} {good : Load → Prop}
    (hgood : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (fits d).Lmax → good L)
    (happ : appReaders.AllLoads good) :
    ∀ j, ((B.fieldForkTranscriptWith R Lw f cod fits chk label k stmt name appWrites
      appReaders).readers j).AllLoads good :=
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
    {appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec} {good : ℕ → Load → Prop}
    (hg : ∀ g L, good 0 L → good g L) {Lr : Fin ir.domains.length → ℕ}
    (hLr : ∀ d, ForkRestSizesLe B.src (R d) (Lr d))
    (hrest : ∀ d L, L ≤ forkLoad B.src (R d) (cod d).rd (Lr d) → good 0 L)
    (hstage : ∀ d : Fin ir.domains.length, ∀ n ≤ ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk),
      good ((CReader.pi n (cod d).rd).extend ((fits d).grants.stage 0)).grant
        ((cod d).rd.load.nsmul n))
    (happ : appReaders.AllGranted good) :
    ∀ j, ((B.fieldForkTranscriptWith R Lw f cod fits chk label k stmt name appWrites
      appReaders).readers j).AllGranted good :=
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
    (T : (B.withFieldProofs R).CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) {δ : ℝ≥0}
    (hk : ∀ d : Fin ir.domains.length, ir.FieldRoundsLe (R d) δ)
    (happ : ∀ j, ((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) T h hend).εapp j ≤ δ) :
    ∀ c, (((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) T h hend).comap f).error c ≤ δ := by
  have single : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ≥0) (j : ι), g j ≤ ∑ i, g i := fun g j =>
    Finset.single_le_sum (f := g) (fun _ _ => zero_le) (Finset.mem_univ j)
  refine IOP.Sound.error_le _ (fun d j => ?_) happ (fun d b j => ?_) (fun d j => ?_)
  · have hsum := ((ir.fieldFork B.src (R d)).join.sum_commitError
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound).trans
      (congrArg Ligero.AgreementThreshold.Bounds.commit
        (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..))
    exact (single _ j).trans (hsum.trans_le (hk d).commit)
  · exact ir.branchError_le B.src (R d).rs T (hk d).batches (hk d).gkr _ j
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

/-- **Every round of the composite read through `f` and checked** (as `fieldForkError_le`). -/
theorem fieldForkErrorWith_le [Inhabited W] {chk : Stmt → Bool} {proj : ir.Valuation I → ir.Assignment I → W}
    {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}
    (T : (B.withFieldProofs R).CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) {δ : ℝ≥0}
    (hk : ∀ d : Fin ir.domains.length, ir.FieldRoundsLe (R d) δ)
    (happ : ∀ j, ((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) T h hend).εapp j ≤ δ) :
    ∀ c, (((B.fieldBranches R).soundIOPSound (B.fieldBranchesSound R) T h hend).comapWith f chk).error c ≤ δ := by
  have single : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ≥0) (j : ι), g j ≤ ∑ i, g i := fun g j =>
    Finset.single_le_sum (f := g) (fun _ _ => zero_le) (Finset.mem_univ j)
  refine IOP.Sound.error_le _ (fun d j => ?_) happ (fun d b j => ?_) (fun d j => ?_)
  · have hsum := ((ir.fieldFork B.src (R d)).join.sum_commitError
      (Rel := (ir.fieldForkSound B.src (R d)).joinRel) (ir.fieldForkSound B.src (R d)).joinSound).trans
      (congrArg Ligero.AgreementThreshold.Bounds.commit
        (Ligero.MaskRow.TreeLayout.Numbers.bounds_setup ..))
    exact (single _ j).trans (hsum.trans_le (hk d).commit)
  · exact ir.branchError_le B.src (R d).rs T (hk d).batches (hk d).gkr _ j
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

end ProofSystem

end

end GordieHowe.RealizedProgram
