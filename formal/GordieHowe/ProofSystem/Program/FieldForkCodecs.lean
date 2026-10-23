-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFork
public import GordieHowe.ProofSystem.RingSwitching.PlanTreeCodecs
public import GordieHowe.ProofSystem.Zerocheck.BatchedCodecs
public import GordieHowe.ProofSystem.Program.Transcript.PrefixCodecs
public import GordieHowe.ProofSystem.Program.Transcript.Readers

@[expose] public section

/-!
# GordieHowe: the codecs and challenge readers of any domain, forked

The write codecs and challenge readers of the forked domain `d` (`GordieHowe.RealizedProgram.fieldFork`), at a field's
byte codec `FB` and challenge reader `rd`:

* **the branches** (`GordieHowe.RealizedProgram.forkBranchWrites`, `GordieHowe.RealizedProgram.forkBranchReaders`): a covered batch's
  batch phase (`GordieHowe.BatchedZerocheck.writes`), a merged batch's merging challenge and batch phase, GKR's every
  circuit in sequence (`SpecWrites.sourceInteraction`, `ofListWrites`);
* **the join** (`GordieHowe.RealizedProgram.forkJoinWrites`, `GordieHowe.RealizedProgram.forkJoinReaders`): the join's masked row reduction (the
  fixed masked reduction, no rounds; every stage's combination challenge and measurements,
  `PEdge.runWrites`), then Ligero with the prefix-row test; its commit rounds and leaves
  (`GordieHowe.RealizedProgram.forkCommitWrites`, `GordieHowe.RealizedProgram.forkCommitReaders`, `GordieHowe.RealizedProgram.forkLeafCodec`);
* **the readers' loads** (`GordieHowe.RealizedProgram.forkLoad`, `GordieHowe.RealizedProgram.branchReaders_allLoads`,
  `GordieHowe.RealizedProgram.forkJoinReaders_allLoads`, `GordieHowe.RealizedProgram.forkCommitReaders_allLoads`) under the decidable
  size bound `GordieHowe.RealizedProgram.ForkLoadSizesLe`;
* **the sizes**: the join's commit phase's `2` rounds, its tree's `N` leaves, its `t` queries, its
  `2` rounds per stage and Ligero's `3` (`GordieHowe.RealizedProgram.forkJoin_n`).

The array sizes enter through one decidable bound (`GordieHowe.RealizedProgram.ForkSizesLe`).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations

section

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)

/-! ## The sizes -/

/-- **The arrays of domain `d`'s forked proof have at most `Mx` field elements**: every covered
batch's skip message, round message and terminal claims (read at any pads, here `Unit`), and every
stage's measurements. -/
def ForkSizesLe (Mx : ℕ) : Prop :=
  (∀ i : Fin (ir.cbatches d R.Pk).length,
      (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).e ≤ Mx ∧
      (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).D ≤ Mx ∧
      (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).k ≤ Mx) ∧
  (∀ i : Fin (ir.sumBatches d R.Pk).length,
      (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).e ≤ Mx ∧
      (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).D ≤ Mx ∧
      (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).k ≤ Mx ∧ 2 ≤ Mx) ∧
  ((∀ i : Fin (ir.mbatches d R.Pk).length,
      (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).e ≤ Mx ∧
      (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).D ≤ Mx ∧
      (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).k ≤ Mx) ∧
    ∀ i : Fin (ir.sumMBatches d R.Pk).length,
      (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).e ≤ Mx ∧
      (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).D ≤ Mx ∧
      (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).k ≤ Mx ∧ 2 ≤ Mx) ∧
  ∀ r ∈ R.rs, r.plan.degree ≤ Mx

instance (Mx : ℕ) : Decidable (ForkSizesLe R Mx) := by
  unfold ForkSizesLe
  infer_instance

variable {src R}

/-- An array of at most `Mx` elements fits. -/
theorem fits_of_le {fb B Mx m : ℕ} (hMx : 9 + Mx * fb ≤ B) (h : m ≤ Mx) : 9 + m * fb ≤ B :=
  (Nat.add_le_add_left (Nat.mul_le_mul_right fb h) 9).trans hMx

/-- **Every stage's measurements fit.** -/
theorem stages_fit {fb B Mx : ℕ} (hMx : 9 + Mx * fb ≤ B) (hs : ForkSizesLe R Mx) :
    ∀ e ∈ ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk), 9 + e.d * fb ≤ B := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_mapIdx.1 he
  exact fits_of_le hMx (hs.2.2.2 _ (List.getElem_mem ha))

variable (src R)

/-! ## The branches -/

/-- **The codecs of branch `j`**: a covered batch's batch phase (`BatchedZerocheck.writes`), a merged
batch's merging challenge (no codec) and batch phase, every circuit's GKR in sequence
(`SpecWrites.sourceInteraction`). -/
def branchWrites {fb B Mx : ℕ} (FB : SPBCS.Codec.FieldBytes (I (ir.domainField d)).K fb)
    (hMx : 9 + Mx * fb ≤ B) (hs : ForkSizesLe R Mx) (hgkr : 2 * (1 + fb) ≤ B) :
    (j : ir.BranchIdx d R.Pk) → SpecWrites (ir.branchIP src R.rs j).spec B
  | .inl (.inl (.inl i)) =>
    BatchedZerocheck.writes FB _ _ _ _ (fits_of_le hMx (hs.1 i).1) (fits_of_le hMx (hs.1 i).2.1)
      (fits_of_le hMx (hs.1 i).2.2)
  | .inl (.inl (.inr i)) =>
    BatchedZerocheck.writes FB _ _ _ _ (fits_of_le hMx (hs.2.1 i).1)
        (fits_of_le hMx (hs.2.1 i).2.1) (fits_of_le hMx (hs.2.1 i).2.2.1) ++
      BatchedZerocheck.roundWrites FB 2 (fits_of_le hMx (hs.2.1 i).2.2.2) 4
  | .inl (.inr (.inl i)) =>
    SpecWrites.oneV (M := (I (ir.domainField d)).K) (B := B) ++
      BatchedZerocheck.writes FB _ _ _ _ (fits_of_le hMx (hs.2.2.1.1 i).1)
        (fits_of_le hMx (hs.2.2.1.1 i).2.1) (fits_of_le hMx (hs.2.2.1.1 i).2.2)
  | .inl (.inr (.inr i)) =>
    (SpecWrites.oneV (M := (I (ir.domainField d)).K) (B := B) ++
      BatchedZerocheck.writes FB _ _ _ _ (fits_of_le hMx (hs.2.2.1.2 i).1)
        (fits_of_le hMx (hs.2.2.1.2 i).2.1) (fits_of_le hMx (hs.2.2.1.2 i).2.2.1)) ++
      BatchedZerocheck.roundWrites FB 2 (fits_of_le hMx (hs.2.2.1.2 i).2.2.2) 4
  | .inr _ =>
    ofListWrites (M := ir.gkrIP src R.rs)
      (fun i => SpecWrites.sourceInteraction FB hgkr (ir.circSource d src i) (ir.circNodes d src i))
      (List.finRange _)

/-- **The challenge readers of branch `j`**: a covered batch's (`BatchedZerocheck.readers`), a merged
batch's merging challenge and batch phase, every circuit's GKR (`SpecReaders.sourceInteraction`). -/
def branchReaders (rd : CReader (I (ir.domainField d)).K) :
    (j : ir.BranchIdx d R.Pk) → SpecReaders (ir.branchIP src R.rs j).spec
  | .inl (.inl (.inl _)) => BatchedZerocheck.readers rd _ _ _ _
  | .inl (.inl (.inr _)) =>
    BatchedZerocheck.readers rd _ _ _ _ ++ BatchedZerocheck.roundReaders rd 2 4
  | .inl (.inr (.inl _)) =>
    SpecReaders.one (I (ir.domainField d)).K rd ++ BatchedZerocheck.readers rd _ _ _ _
  | .inl (.inr (.inr _)) =>
    (SpecReaders.one (I (ir.domainField d)).K rd ++ BatchedZerocheck.readers rd _ _ _ _) ++
      BatchedZerocheck.roundReaders rd 2 4
  | .inr _ =>
    ofListReaders (M := ir.gkrIP src R.rs)
      (fun i => SpecReaders.sourceInteraction rd (ir.circSource d src i) (ir.circNodes d src i))
      (List.finRange _)

/-- **The codecs of the forked domain's branches** (`branchWrites` at `branchEquiv`). -/
def forkBranchWrites {fb B Mx : ℕ} (FB : SPBCS.Codec.FieldBytes (I (ir.domainField d)).K fb)
    (hMx : 9 + Mx * fb ≤ B) (hs : ForkSizesLe R Mx) (hgkr : 2 * (1 + fb) ≤ B)
    (b : Fin (ir.fieldFork src R).nb) : SpecWrites ((ir.fieldFork src R).branch b).spec B :=
  branchWrites src R FB hMx hs hgkr (ir.branchEquiv d R.Pk b)

/-- **The challenge readers of the forked domain's branches.** -/
def forkBranchReaders (rd : CReader (I (ir.domainField d)).K)
    (b : Fin (ir.fieldFork src R).nb) : SpecReaders ((ir.fieldFork src R).branch b).spec :=
  branchReaders src R rd (ir.branchEquiv d R.Pk b)

/-! ## The join -/

/-- **The stream grants of a forked domain's join**: the extra stream bytes of every stage's
combination challenge, by the stage's position, and of Ligero's constraint challenge. -/
structure ForkGrants where
  /-- The grant of the stage at each position. -/
  stage : ℕ → ℕ := fun _ => 0
  /-- The grant of Ligero's constraint challenge. -/
  linear : ℕ := 0

/-- **The join's masked row reduction**: the join's tree closed on the fixed masked reduction. -/
abbrev forkJoinIp := (ir.fieldFork src R).join.path.close (ir.fieldFork src R).join.maskedReduction

/-- **The codecs of the join**: the join's masked row reduction (the fixed masked reduction, no rounds; every stage's
combination challenge and measurements, `PEdge.runWrites`), then the proof phase of Ligero with
the prefix-row test (`Ligero.MaskRow.Setup.writes`). -/
def forkJoinWrites {fb B Mx : ℕ} (FB : SPBCS.Codec.FieldBytes (I (ir.domainField d)).K fb)
    (hMx : 9 + Mx * fb ≤ B) (hs : ForkSizesLe R Mx)
    (hlig : LigeroFits fb (ir.fieldFork src R).join.N (ir.fieldFork src R).join.code.k
      (ir.fieldFork src R).join.cp.nrep B) :
    SpecWrites (ir.fieldForkShape src R).join B :=
  runWrites FB (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
      (claimReads R.rs) (ir.fieldJoinMaskedReduction src R) (SpecWrites.ofNone (P := FieldProof.MaskedRowReduction.noRounds) fun i => i.elim0)
      (stages_fit hMx hs) ++
    (ir.fieldFork src R).join.cp.writes (forkJoinIp src R).rowsAt FB hlig.aux
      (by have := hlig.response; omega)

/-- **The challenge readers of the join**: every stage's combination challenge
(`PEdge.runReaders`), the stage at position `i` granted `g.stage i` stream bytes, then the proof
phase of Ligero (`Ligero.MaskRow.Setup.readers`), the constraint challenge granted `g.linear`. -/
def forkJoinReaders (rd : CReader (I (ir.domainField d)).K) (g : ForkGrants) :
    SpecReaders (ir.fieldForkShape src R).join :=
  runReaders rd g.stage (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
      (claimReads R.rs) (ir.fieldJoinMaskedReduction src R) (fun i => i.1.elim0) ++
    (ir.fieldFork src R).join.cp.readers (forkJoinIp src R).rowsAt rd g.linear

/-- **The codecs of the join's commit rounds**: the low-degree responses
(`Ligero.MaskRow.Setup.commitWrites`). -/
def forkCommitWrites {fb B : ℕ} (FB : SPBCS.Codec.FieldBytes (I (ir.domainField d)).K fb)
    (hc : 9 + (ir.fieldFork src R).join.cp.nrep * (ir.fieldFork src R).join.code.k * fb ≤ B) :
    SpecWrites (ir.fieldForkShape src R).commitRounds B :=
  (ir.fieldFork src R).join.cp.commitWrites (forkJoinIp src R).rowsAt FB hc

/-- **The challenge readers of the join's commit rounds** (`Ligero.MaskRow.Setup.commitReaders`). -/
def forkCommitReaders (rd : CReader (I (ir.domainField d)).K) :
    SpecReaders (ir.fieldForkShape src R).commitRounds :=
  (ir.fieldFork src R).join.cp.commitReaders (forkJoinIp src R).rowsAt rd

/-- **The leaf codec of the join's tree**: a column of the tableau
(`Ligero.MaskRow.Setup.leafCodec`). -/
def forkLeafCodec {fb : ℕ} (FB : SPBCS.Codec.FieldBytes (I (ir.domainField d)).K fb) :
    Codec (ir.fieldForkOracle src R).Leaf :=
  (ir.fieldFork src R).join.cp.leafCodec (forkJoinIp src R).rowsAt FB

/-- A serialized column has at most the bytes of a column with two mask entries. -/
theorem length_ser_forkLeafCodec_le {fb : ℕ} (FB : SPBCS.Codec.FieldBytes (I (ir.domainField d)).K fb)
    (c : (ir.fieldForkOracle src R).Leaf) :
    ((forkLeafCodec src R FB).ser c).length ≤
      (9 + ((ir.fieldFork src R).join.cp.nrep + (ir.fieldFork src R).join.R) * fb) +
        ((1 + fb) + (1 + fb)) :=
  (ir.fieldFork src R).join.cp.length_ser_leafCodec_le (forkJoinIp src R).rowsAt FB c

/-! ## The sizes of the join -/

/-- The join's commit phase has two rounds. -/
theorem forkJoin_nc : (ir.fieldForkShape src R).nc = 2 :=
  (ir.fieldFork src R).join.cp.nc_commitProve (forkJoinIp src R).rowsAt

/-- The join's tree has the tableau's `N` leaves. -/
theorem forkJoin_nLeaves : (ir.fieldForkOracle src R).nLeaves = (ir.fieldFork src R).join.N :=
  (ir.fieldFork src R).join.cp.nLeaves_commitProve (forkJoinIp src R).rowsAt

/-- The join's opening queries the tableau's `t` columns. -/
theorem forkJoin_card_queries (ch : (ir.fieldForkSound src R).joinProof.cp.spec.Challenges) :
    ((ir.fieldForkSound src R).joinProof.cp.queries ch).card = (ir.fieldFork src R).join.cp.t :=
  (ir.fieldFork src R).join.cp.card_queries (forkJoinIp src R).rowsAt ch

/-- **The join has at most two rounds per stage and Ligero's `3`.** -/
theorem forkJoin_n_le :
    (ir.fieldForkShape src R).jn ≤ 2 * (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)).length + 3 := by
  have h := (ir.fieldFork src R).join.cp.n_commitProve (forkJoinIp src R).rowsAt
  change (forkJoinIp src R).n + ((ir.fieldFork src R).join.cp.commitProve (forkJoinIp src R).rowsAt).n ≤ _
  rw [h]
  have hr := run_n_le (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
    (claimReads R.rs) (ir.fieldJoinMaskedReduction src R)
  change ((PEdge.path (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
      (claimReads R.rs)).run (ir.fieldJoinMaskedReduction src R)).n + 3 ≤ _
  change _ ≤ 0 + _ at hr
  omega

/-! ## The loads -/

/-- **The largest load of domain `d`'s forked proof**: `Lmax` elements, and the `t` draws of
`choose`. -/
def forkLoad (rd : CReader (I (ir.domainField d)).K) (Lmax : ℕ) : Load :=
  (rd.load.nsmul Lmax).max ⟨(ir.fieldFork src R).join.cp.t, Rejection.byteLen (ir.fieldFork src R).join.N⟩

/-- **The challenge reads of domain `d`'s forked proof have at most `Lmax` elements**: every
batch's `max (max n k) 3`, every circuit's GKR `max outDim 2`, the first combination's `nc`, every
later stage's at most `laterBound`, the Ligero test's `nrep · R + nL + nQ`. -/
def ForkLoadSizesLe (Lmax : ℕ) : Prop :=
  (∀ i : Fin (ir.cbatches d R.Pk).length, max (max (ir.colsBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.cbatches d R.Pk)[i]).n
      (ir.colsBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.cbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.sumBatches d R.Pk).length,
      max (max (ir.bitsBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumBatches d R.Pk)[i]).cb).n
        (ir.bitsBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumBatches d R.Pk)[i]).cb).k) 3 ≤ Lmax) ∧
  ((∀ i : Fin (ir.mbatches d R.Pk).length, max (max (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.mbatches d R.Pk)[i]).n
      (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.mbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
    ∀ i : Fin (ir.sumMBatches d R.Pk).length,
      max (max (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumMBatches d R.Pk)[i]).mb).n
        (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumMBatches d R.Pk)[i]).mb).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.circs d).length, max (ir.circSource d src i).outDim 2 ≤ Lmax) ∧ ir.claimCount (d := d) (Pk := R.Pk) ≤ Lmax ∧ laterBound R.rs ≤ Lmax ∧
  (ir.fieldFork src R).join.cp.nrep * (ir.fieldFork src R).join.R +
    ((ir.fieldFork src R).join.nLr + (ir.fieldFork src R).join.nQ) ≤ Lmax

/-- **The challenge reads of domain `d`'s forked proof other than the first combination have at
most `Lmax` elements** (`ForkLoadSizesLe` without the first combination's `nc`). -/
def ForkRestSizesLe (Lmax : ℕ) : Prop :=
  (∀ i : Fin (ir.cbatches d R.Pk).length, max (max (ir.colsBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.cbatches d R.Pk)[i]).n
      (ir.colsBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.cbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.sumBatches d R.Pk).length,
      max (max (ir.bitsBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumBatches d R.Pk)[i]).cb).n
        (ir.bitsBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumBatches d R.Pk)[i]).cb).k) 3 ≤ Lmax) ∧
  ((∀ i : Fin (ir.mbatches d R.Pk).length, max (max (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.mbatches d R.Pk)[i]).n
      (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) (ir.mbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
    ∀ i : Fin (ir.sumMBatches d R.Pk).length,
      max (max (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumMBatches d R.Pk)[i]).mb).n
        (ir.mergedBatchAt R.rs (ir.ClaimPads d src R.Pk) ((ir.sumMBatches d R.Pk)[i]).mb).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.circs d).length, max (ir.circSource d src i).outDim 2 ≤ Lmax) ∧ laterBound R.rs ≤ Lmax ∧
  (ir.fieldFork src R).join.cp.nrep * (ir.fieldFork src R).join.R +
    ((ir.fieldFork src R).join.nLr + (ir.fieldFork src R).join.nQ) ≤ Lmax

variable {src R}

/-- The reads other than the first combination's are within the load sizes' `Lmax`. -/
theorem ForkLoadSizesLe.rest {Lmax : ℕ} (h : ForkLoadSizesLe src R Lmax) : ForkRestSizesLe src R Lmax :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem nsmul_le_forkLoad (rd : CReader (I (ir.domainField d)).K) {Lmax m : ℕ} (h : m ≤ Lmax) :
    rd.load.nsmul m ≤ forkLoad src R rd Lmax :=
  (Load.nsmul_le_nsmul _ h).trans (Load.le_max_left _ _)

/-- **The loads of the branches' readers** are at most `forkLoad`. -/
theorem branchReaders_allLoads (rd : CReader (I (ir.domainField d)).K) {Lmax : ℕ}
    (hL : ForkRestSizesLe src R Lmax) :
    ∀ j, (branchReaders src R rd j).AllLoads (· ≤ forkLoad src R rd Lmax)
  | .inl (.inl (.inl i)) => (BatchedZerocheck.readers_allLoads rd).mono fun _ h =>
      h.trans (nsmul_le_forkLoad rd (hL.1 i))
  | .inl (.inl (.inr i)) => SpecReaders.append_allLoads
      ((BatchedZerocheck.readers_allLoads rd).mono fun _ h =>
        h.trans (nsmul_le_forkLoad rd (hL.2.1 i)))
      (BatchedZerocheck.roundReaders_allLoads rd 2 _ ((show rd.load ≤ rd.load.nsmul 1 from
        ⟨by simp [Load.nsmul], by simp [Load.nsmul]⟩).trans
        (nsmul_le_forkLoad rd (le_trans (by omega) (hL.2.1 i)))) 4)
  | .inl (.inr (.inl i)) => SpecReaders.append_allLoads
      (SpecReaders.one_allLoads _ ((show rd.load ≤ rd.load.nsmul 1 from
        ⟨by simp [Load.nsmul], by simp [Load.nsmul]⟩).trans
        (nsmul_le_forkLoad rd (le_trans (by omega) (hL.2.2.1.1 i)))))
      ((BatchedZerocheck.readers_allLoads rd).mono fun _ h =>
        h.trans (nsmul_le_forkLoad rd (hL.2.2.1.1 i)))
  | .inl (.inr (.inr i)) => SpecReaders.append_allLoads (SpecReaders.append_allLoads
      (SpecReaders.one_allLoads _ ((show rd.load ≤ rd.load.nsmul 1 from
        ⟨by simp [Load.nsmul], by simp [Load.nsmul]⟩).trans
        (nsmul_le_forkLoad rd (le_trans (by omega) (hL.2.2.1.2 i)))))
      ((BatchedZerocheck.readers_allLoads rd).mono fun _ h =>
        h.trans (nsmul_le_forkLoad rd (hL.2.2.1.2 i))))
      (BatchedZerocheck.roundReaders_allLoads rd 2 _ ((show rd.load ≤ rd.load.nsmul 1 from
        ⟨by simp [Load.nsmul], by simp [Load.nsmul]⟩).trans
        (nsmul_le_forkLoad rd (le_trans (by omega) (hL.2.2.1.2 i)))) 4)
  | .inr _ => ofListReaders_allLoads (fun i =>
      (SpecReaders.sourceInteraction_allLoads rd _ _).mono fun _ h =>
        h.trans (nsmul_le_forkLoad rd (hL.2.2.2.1 i))) _

/-- **The loads of Ligero's proof-phase readers** are at most `forkLoad`. -/
theorem forkLigeroReaders_allLoads (rd : CReader (I (ir.domainField d)).K) (gl : ℕ) {Lmax : ℕ}
    (hL : ForkRestSizesLe src R Lmax) :
    ((ir.fieldFork src R).join.cp.readers (forkJoinIp src R).rowsAt rd gl).AllLoads
      (· ≤ forkLoad src R rd Lmax) := by
  refine (ir.fieldFork src R).join.cp.readers_allLoads _ rd _ ?_ ?_
  · refine le_trans ?_ (nsmul_le_forkLoad rd hL.2.2.2.2.2)
    simp only [CReader.prod_load, CReader.pi_load, Load.add, Load.nsmul, Load.le_iff]
    constructor
    · nlinarith [Nat.zero_le ((ir.fieldFork src R).join.cp.nrep * (ir.fieldFork src R).join.R)]
    · simp
  · exact le_trans (b := ⟨(ir.fieldFork src R).join.cp.t, Rejection.byteLen (ir.fieldFork src R).join.N⟩)
      (Load.Le.mk (by simp only [CReader.choose_load, mul_one]; exact le_rfl) le_rfl)
      (Load.le_max_right _ _)

/-- **Every stage's touching claims' reads are within `forkLoad`**: the first's at most
`claimCount`, every later one's at most `laterBound`. -/
theorem stages_le_forkLoad (rd : CReader (I (ir.domainField d)).K) {Lmax : ℕ}
    (hc : ir.claimCount (d := d) (Pk := R.Pk) ≤ Lmax) (hL : ForkRestSizesLe src R Lmax) :
    StagesOk (fun _ n => rd.load.nsmul n ≤ forkLoad src R rd Lmax)
      (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
      (claimReads R.rs) :=
  stagesOk_of_bound _ 0 _ _ _ (fun n hn => nsmul_le_forkLoad rd (hn.trans hc)) fun _ n hn => by
    refine nsmul_le_forkLoad rd (le_trans ?_ hL.2.2.2.2.1)
    rw [routeAt_np, map_d_fieldEdges] at hn
    exact hn.trans (card_passing_le R.rs)

/-- **The loads of the join's readers** are at most `forkLoad`. -/
theorem forkJoinReaders_allLoads (rd : CReader (I (ir.domainField d)).K) (g : ForkGrants)
    {Lmax : ℕ} (hL : ForkLoadSizesLe src R Lmax) :
    (forkJoinReaders src R rd g).AllLoads (· ≤ forkLoad src R rd Lmax) :=
  SpecReaders.append_allLoads (runReaders_allLoads rd _ _ 0 _ _ _ _ _ (fun i => i.1.elim0)
    (stages_le_forkLoad rd hL.2.2.2.2.1 hL.rest))
    (forkLigeroReaders_allLoads rd _ hL.rest)

/-- **The join's readers at their grants**: a predicate `good` that larger grants keep holds at
every round when it holds at grant `0` within `forkLoad` at the rest sizes, and at the first
combination's grant for at most `claimCount` elements. -/
theorem forkJoinReaders_allGranted (rd : CReader (I (ir.domainField d)).K) (g : ForkGrants)
    {Lmax : ℕ} (hL : ForkRestSizesLe src R Lmax) {good : ℕ → Load → Prop}
    (hg : ∀ g L, good 0 L → good g L) (hrest : ∀ L, L ≤ forkLoad src R rd Lmax → good 0 L)
    (hstage : ∀ n ≤ ir.claimCount (d := d) (Pk := R.Pk),
      good ((CReader.pi n rd).extend (g.stage 0)).grant (rd.load.nsmul n)) :
    (forkJoinReaders src R rd g).AllGranted good :=
  SpecReaders.AllGranted.append
    (runReaders_allGranted rd _ _ hg 0 _ _ _ _ _ (fun i => i.1.elim0)
      (stagesOk_of_bound _ 0 _ _ _ hstage fun _ n hn => hg _ _ (hrest _
        (nsmul_le_forkLoad rd (le_trans (by rw [routeAt_np, map_d_fieldEdges] at hn; exact hn.trans (card_passing_le R.rs))
          hL.2.2.2.2.1)))))
    (SpecReaders.AllGranted.of_allLoads hg ((forkLigeroReaders_allLoads rd _ hL).mono hrest))

/-- **The loads of the join's commit-round readers** (`nrep · R` elements) are at most
`forkLoad`. -/
theorem forkCommitReaders_allLoads (rd : CReader (I (ir.domainField d)).K) {Lmax : ℕ}
    (hL : ForkRestSizesLe src R Lmax) :
    (forkCommitReaders src R rd).AllLoads (· ≤ forkLoad src R rd Lmax) :=
  ((ir.fieldFork src R).join.cp.commitReaders_allLoads _ rd).mono fun _ h =>
    h.trans (nsmul_le_forkLoad rd (le_trans (Nat.le_add_right _ _) hL.2.2.2.2.2))

end

end GordieHowe.RealizedProgram
