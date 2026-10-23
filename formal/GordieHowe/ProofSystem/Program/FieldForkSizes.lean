-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldForkCodecs

@[expose] public section

/-!
# GordieHowe: the sizes of any domain's forked proof

The sizes that bound the loads of domain `d`'s forked proof (`GordieHowe.RealizedProgram.ForkLoadSizesLe`):

* **the masked reduction** (`GordieHowe.RealizedProgram.card_fieldMaskedReduction_Lin`, `GordieHowe.RealizedProgram.card_fieldMaskedReduction_Q`): one linear row
  per covered batch and `depth + 1` per circuit; every batch's pad products, `depth + 1` per
  circuit and the quadratic triples;
* **the join's masked row reduction** (`GordieHowe.RealizedProgram.card_forkJoinIp_Lin`, `GordieHowe.RealizedProgram.card_forkJoinIp_Q_le`): the
  masked reduction's rows and the tree's output claims; the masked reduction's products and at most the masks' own
  cells;
* **the tableau** (`GordieHowe.RealizedProgram.forkJoin_R`, `GordieHowe.RealizedProgram.forkJoin_nQ`, `GordieHowe.RealizedProgram.forkJoin_nLr`): its data
  rows, product groups and prepared rows from the layout (`TreeLayout.tableau`), the root own
  cells (`GordieHowe.RealizedProgram.card_rootOwn`, `GordieHowe.RealizedProgram.card_maskOwn`, `GordieHowe.RealizedProgram.card_claimPads`);
* **the load numbers** (`GordieHowe.RealizedProgram.ForkLoadNumbers`, decidable): the sizes from the program, the
  certificate and bounds `gp` on the circuits' pads and `gt` on their tails' depths; they give
  `ForkLoadSizesLe` (`GordieHowe.RealizedProgram.forkLoadSizesLe_of`).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations

section

section Claim

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
  {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge (I (ir.domainField d)) Pk))

/-- **A sum over the branches** is the sum over the covered batches on columns, on bits, the merged
batches on columns, on bits, and GKR. -/
theorem sum_branch (f : ir.BranchIdx d Pk → ℕ) :
    ((List.finRange (ir.nBranch d Pk)).map fun b => f (ir.branchEquiv d Pk b)).sum =
      ∑ i, f (.inl (.inl (.inl i))) + ∑ i, f (.inl (.inl (.inr i))) +
        ∑ i, f (.inl (.inr (.inl i))) + ∑ i, f (.inl (.inr (.inr i))) + f (.inr ()) := by
  rw [← Fin.sum_univ_def, Fintype.sum_equiv (ir.branchEquiv d Pk) _ f fun _ => rfl]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  ring

/-- **The linear rows of the masked reduction**: one per covered batch, `depth + 1` per circuit. -/
theorem card_fieldMaskedReduction_Lin :
    Fintype.card (ir.fieldMaskedReduction src rs).Lin =
      (ir.cbatches d Pk).length + (ir.sumBatches d Pk).length + (ir.mbatches d Pk).length +
        (ir.sumMBatches d Pk).length +
        ∑ i, ((ir.circSource d src i).tail.depth + 1) := by
  change Fintype.card ((FieldProof.MaskedReduction.ofList (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
    (fun b => ir.branchIP src rs (ir.branchEquiv d Pk b)) (List.finRange _)).Lin ⊕ Empty) = _
  rw [Fintype.card_sum, ofList_card_Lin,
    sum_branch (f := fun j => Fintype.card (ir.branchIP src rs j).Lin)]
  have hg : Fintype.card (ir.branchIP src rs (.inr ())).Lin =
      ∑ i, ((ir.circSource d src i).tail.depth + 1) := by
    change Fintype.card (FieldProof.MaskedReduction.ofList (ncOf := fun _ => 1) (ir.gkrIP src rs) (List.finRange _)).Lin = _
    rw [ofList_card_Lin, ← Fin.sum_univ_def]
    exact Finset.sum_congr rfl fun i _ => Fintype.card_fin _
  rw [hg]
  simp only [Fintype.card_empty, add_zero]
  change ∑ _i, Fintype.card Unit + ∑ _i, Fintype.card Unit + ∑ _i, Fintype.card Unit +
    ∑ _i, Fintype.card Unit + _ = _
  simp only [Fintype.card_unit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

/-- **The product triples of the masked reduction**: every batch's pad products, `depth + 1` per circuit,
the quadratic triples. -/
theorem card_fieldMaskedReduction_Q :
    Fintype.card (ir.fieldMaskedReduction src rs).Q =
      ∑ i : Fin (ir.cbatches d Pk).length, (ir.colsBatchAt rs Unit (ir.cbatches d Pk)[i]).m +
        ∑ i : Fin (ir.sumBatches d Pk).length,
          (ir.bitsBatchAt rs Unit ((ir.sumBatches d Pk)[i]).cb).m +
        ∑ i : Fin (ir.mbatches d Pk).length, (ir.mergedBatchAt rs Unit (ir.mbatches d Pk)[i]).m +
        ∑ i : Fin (ir.sumMBatches d Pk).length,
          (ir.mergedBatchAt rs Unit ((ir.sumMBatches d Pk)[i]).mb).m +
        ∑ i, ((ir.circSource d src i).tail.depth + 1) + Fintype.card (ir.QuadIdx d) := by
  change Fintype.card ((FieldProof.MaskedReduction.ofList (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
    (fun b => ir.branchIP src rs (ir.branchEquiv d Pk b)) (List.finRange _)).Q ⊕ ir.QuadIdx d) = _
  rw [Fintype.card_sum, ofList_card_Q,
    sum_branch (f := fun j => Fintype.card (ir.branchIP src rs j).Q)]
  have hg : Fintype.card (ir.branchIP src rs (.inr ())).Q =
      ∑ i, ((ir.circSource d src i).tail.depth + 1) := by
    change Fintype.card (FieldProof.MaskedReduction.ofList (ncOf := fun _ => 1) (ir.gkrIP src rs) (List.finRange _)).Q = _
    rw [ofList_card_Q, ← Fin.sum_univ_def]
    exact Finset.sum_congr rfl fun i _ => Fintype.card_fin _
  have hc : ∑ i : Fin (ir.cbatches d Pk).length,
      Fintype.card (ir.branchIP src rs (.inl (.inl (.inl i)))).Q =
      ∑ i : Fin (ir.cbatches d Pk).length,
        (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).m :=
    Finset.sum_congr rfl fun i _ => BatchedZerocheck.AffineBatch.card_cell
      (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i])
  have hsb : ∑ i : Fin (ir.sumBatches d Pk).length,
      Fintype.card (ir.branchIP src rs (.inl (.inl (.inr i)))).Q =
      ∑ i : Fin (ir.sumBatches d Pk).length,
        (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).m :=
    Finset.sum_congr rfl fun i _ => BatchedZerocheck.AffineBatch.card_cell
      (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb)
  have hm : ∑ i : Fin (ir.mbatches d Pk).length,
      Fintype.card (ir.branchIP src rs (.inl (.inr (.inl i)))).Q =
      ∑ i : Fin (ir.mbatches d Pk).length,
        (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).m :=
    Finset.sum_congr rfl fun i _ => BatchedZerocheck.MergedAffineBatch.card_cell
      (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i])
  have hsm : ∑ i : Fin (ir.sumMBatches d Pk).length,
      Fintype.card (ir.branchIP src rs (.inl (.inr (.inr i)))).Q =
      ∑ i : Fin (ir.sumMBatches d Pk).length,
        (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).m :=
    Finset.sum_congr rfl fun i _ => BatchedZerocheck.MergedAffineBatch.card_cell
      (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb)
  rw [hg, hc, hsb, hm, hsm]
  rfl

end Claim

section Join

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)

/-- **The linear rows of the join's masked row reduction**: the masked reduction's and the tree's output claims. -/
theorem card_forkJoinIp_Lin :
    Fintype.card (forkJoinIp src R).Lin = Fintype.card (ir.fieldMaskedReduction src R.rs).Lin +
      (PEdge.path (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
        (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk))
        (ir.claimCount (d := d) (Pk := R.Pk)) (claimReads R.rs)).outClaims := by
  change Fintype.card (((PEdge.path (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk))
      (ir.claimCount (d := d) (Pk := R.Pk)) (claimReads R.rs)).run
        (ir.fieldJoinMaskedReduction src R)).Lin ⊕ Fin _) = _
  rw [Fintype.card_sum, run_card_Lin, Fintype.card_fin]
  rfl

/-- **The masks' own cells of the tree's edges** are the realized edges' kits'. -/
theorem sum_nOwn_fieldEdges {Pads : Type} [Fintype Pads] :
    ((ir.fieldEdges d R.Pk R.rs Pads).map fun e => e.kit.masks.nOwn).sum =
      (R.rs.map fun r => r.kit.masks.nOwn).sum := by
  congr 1
  refine List.ext_getElem (by simp [length_fieldEdges]) fun a h1 h2 => ?_
  simp only [List.getElem_map]
  rw [getElem_fieldEdges]
  rfl

/-- **The product triples of the join's masked row reduction**: the masked reduction's and at most the masks' own
cells. -/
theorem card_forkJoinIp_Q_le :
    Fintype.card (forkJoinIp src R).Q ≤ Fintype.card (ir.fieldMaskedReduction src R.rs).Q +
      (R.rs.map fun r => r.kit.masks.nOwn).sum := by
  have h := run_card_Q_le (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
    (claimReads R.rs) (ir.fieldJoinMaskedReduction src R)
  rw [sum_nOwn_fieldEdges] at h
  exact h

/-- **The tree's output claims** are at most `laterBound`: the claims that do not read the first
edge's child and `d + 1` per edge (all the claims with no edge). -/
theorem outClaims_le_laterBound :
    (PEdge.path (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
        (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk))
        (ir.claimCount (d := d) (Pk := R.Pk)) (claimReads R.rs)).outClaims ≤ laterBound R.rs := by
  refine le_trans ?_ (card_passing_le R.rs)
  rw [← map_d_fieldEdges R.rs (ir.ClaimPads d src R.Pk)]
  cases h : ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk) with
  | nil =>
    have hr : R.rs = [] := by
      have hl := congrArg List.length h
      rw [length_fieldEdges] at hl
      exact List.length_eq_zero_iff.1 hl
    have hf : (Finset.univ.filter fun c : Fin (ir.claimCount (d := d) (Pk := R.Pk)) =>
        0 ∉ claimReads R.rs c) = Finset.univ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro h0
      have := lt_of_mem_claimReads R.rs h0
      rw [hr] at this
      exact Nat.not_lt_zero _ this
    rw [hf, Finset.card_univ, Fintype.card_fin]
    simp only [List.map_nil, List.sum_nil, add_zero]
    exact le_rfl
  | cons e es =>
    have := outClaims_cons_le (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0 e es
      (ir.claimCount (d := d) (Pk := R.Pk)) (claimReads R.rs)
    rwa [routeAt_np] at this

/-- **The data rows of the join's tableau** (`TreeLayout.tableau`): the witness rows of the
positions (the prefix rows, the words, the root own cells), the three product blocks and the extra
rows of the masking (`Masking.extra`: none for untested masks, the six piece rows of the mask
test). -/
theorem forkJoin_R :
    (ir.fieldFork src R).join.R =
      (Ligero.MaskRow.TreeLayout.prefixRows R.numbers.Sh (npOf R.Pk R.rs) * R.numbers.Sh.w +
        ir.nwOf d (R.rs.map REdge.plan) + Fintype.card (ir.RootOwn d R.Pk R.rs (ir.ClaimPads d src R.Pk)) +
          R.numbers.Sh.w - 1) / R.numbers.Sh.w +
        3 * ((Fintype.card (forkJoinIp src R).Q + R.numbers.Sh.w - 1) / R.numbers.Sh.w) +
          R.numbers.masking.extra :=
  rfl

/-- **The product groups of the join's tableau**: the products in rows of width `w`. -/
theorem forkJoin_nQ :
    (ir.fieldFork src R).join.nQ =
      (Fintype.card (forkJoinIp src R).Q + R.numbers.Sh.w - 1) / R.numbers.Sh.w :=
  rfl

/-- **The prepared linear rows of the join's tableau**: the masked row reduction's rows and three rows per
product (`Ligero.Routing.PreparedRow`). -/
theorem forkJoin_nLr :
    (ir.fieldFork src R).join.nLr =
      Fintype.card (forkJoinIp src R).Lin + Fintype.card (forkJoinIp src R).Q * 3 := by
  change Fintype.card (Ligero.Routing.PreparedRow _ _) = _
  rw [Fintype.card_congr Ligero.Routing.PreparedRow.equivSum, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  rfl

/-- **The root own cells**: the spare cell, the cells at the root, the masks' own cells, the pads. -/
theorem card_rootOwn (Pads : Type) [Fintype Pads] :
    Fintype.card (ir.RootOwn d R.Pk R.rs Pads) =
      1 + Fintype.card (ir.RootCell d (R.rs.map REdge.plan)) + Fintype.card (MaskOwn R.Pk R.rs) +
        Fintype.card Pads := by
  change @Fintype.card _ (Fintype.ofEquiv _ _) = _
  rw [Fintype.ofEquiv_card]
  simp only [Fintype.card_sum, Fintype.card_unit]
  omega

/-- **The masks' own cells**: every realized edge's kit's. -/
theorem card_maskOwn : Fintype.card (MaskOwn R.Pk R.rs) = (R.rs.map fun r => r.kit.masks.nOwn).sum := by
  change Fintype.card (Σ a : Fin R.rs.length, Fin R.rs[a].kit.masks.nOwn) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Fin.sum_univ_getElem (R.rs.map fun r => r.kit.masks.nOwn)]
  exact Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ fun i => by simp

/-- **The masked reduction's pads**: every batch's and every circuit's. -/
theorem card_claimPads :
    Fintype.card (ir.ClaimPads d src R.Pk) =
      ∑ i : Fin (ir.cbatches d R.Pk).length, Fintype.card ((ir.cbatches d R.Pk)[i]).Pad +
        ∑ i : Fin (ir.sumBatches d R.Pk).length,
          (Fintype.card ((ir.sumBatches d R.Pk)[i]).cb.Pad + 8) +
        ∑ i : Fin (ir.mbatches d R.Pk).length, Fintype.card ((ir.mbatches d R.Pk)[i]).Pad +
        ∑ i : Fin (ir.sumMBatches d R.Pk).length,
          (Fintype.card ((ir.sumMBatches d R.Pk)[i]).mb.Pad + 8) +
        ∑ i, Fintype.card (ir.circSource d src i).PadIdx := by
  unfold ClaimPads
  simp only [Fintype.card_sum, Fintype.card_sigma, SCBatch.Pad, SMBatch.Pad, BitPad,
    Fintype.card_prod, Fintype.card_fin]
  ring

/-- **The cells at the root** are at most the cell keys at no node. -/
theorem card_rootCell_le (es : List PackingEdge) :
    Fintype.card (ir.RootCell d es) ≤
      ((ir.cellKeys d).filter fun k => (ir.cellNode es k).isNone).length := by
  have h := Fintype.card_le_of_injective
    (fun k : ir.RootCell d es =>
      (⟨((ir.cellKeys d).filter fun k => (ir.cellNode es k).isNone).idxOf k.1.1,
        List.idxOf_lt_length_of_mem (List.mem_filter.2 ⟨k.1.2, by simp [k.2]⟩)⟩ :
        Fin ((ir.cellKeys d).filter fun k => (ir.cellNode es k).isNone).length))
    (fun a b hab => by
      have ha : a.1.1 ∈ (ir.cellKeys d).filter fun k => (ir.cellNode es k).isNone :=
        List.mem_filter.2 ⟨a.1.2, by simp [a.2]⟩
      have hb : b.1.1 ∈ (ir.cellKeys d).filter fun k => (ir.cellNode es k).isNone :=
        List.mem_filter.2 ⟨b.1.2, by simp [b.2]⟩
      have := congrArg Fin.val hab
      simp only at this
      exact Subtype.ext (Subtype.ext ((List.idxOf_inj ha).1 this)))
  simpa using h

/-! ## The load numbers -/

/-- **The product triples' bound** of the join's masked row reduction at the circuits' tail bounds `gt`. -/
def forkQBound (gt : Fin (ir.circs d).length → ℕ) : ℕ :=
  ∑ i : Fin (ir.cbatches d R.Pk).length, (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).m +
    ∑ i : Fin (ir.sumBatches d R.Pk).length,
      (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).m +
    ∑ i : Fin (ir.mbatches d R.Pk).length, (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).m +
    ∑ i : Fin (ir.sumMBatches d R.Pk).length,
      (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).m +
    ∑ i, gt i + Fintype.card (ir.QuadIdx d) + (R.rs.map fun r => r.kit.masks.nOwn).sum

/-- **The linear rows' bound** of the join's masked row reduction at the circuits' tail bounds `gt`. -/
def forkLinBound (gt : Fin (ir.circs d).length → ℕ) : ℕ :=
  (ir.cbatches d R.Pk).length + (ir.sumBatches d R.Pk).length + (ir.mbatches d R.Pk).length +
    (ir.sumMBatches d R.Pk).length +
    ∑ i, gt i +
    laterBound R.rs

/-- **The data rows' bound** of the join's tableau at the circuits' pad bounds `gp` and tail
bounds `gt`. -/
def forkRBound (gp gt : Fin (ir.circs d).length → ℕ) : ℕ :=
  (Ligero.MaskRow.TreeLayout.prefixRows R.numbers.Sh (npOf R.Pk R.rs) * R.numbers.Sh.w +
      ir.nwOf d (R.rs.map REdge.plan) +
      (1 + ((ir.cellKeys d).filter fun k => (ir.cellNode (R.rs.map REdge.plan) k).isNone).length +
        (R.rs.map fun r => r.kit.masks.nOwn).sum +
        (∑ i : Fin (ir.cbatches d R.Pk).length, Fintype.card ((ir.cbatches d R.Pk)[i]).Pad +
          ∑ i : Fin (ir.sumBatches d R.Pk).length,
            (Fintype.card ((ir.sumBatches d R.Pk)[i]).cb.Pad + 8) +
          ∑ i : Fin (ir.mbatches d R.Pk).length, Fintype.card ((ir.mbatches d R.Pk)[i]).Pad +
          ∑ i : Fin (ir.sumMBatches d R.Pk).length,
            (Fintype.card ((ir.sumMBatches d R.Pk)[i]).mb.Pad + 8) + ∑ i, gp i)) +
      R.numbers.Sh.w - 1) / R.numbers.Sh.w +
    3 * ((forkQBound R gt + R.numbers.Sh.w - 1) / R.numbers.Sh.w) + 6

/-- **The load numbers of domain `d`'s forked proof** at the circuits' pad bounds `gp` and tail
bounds `gt` (decidable): the batches', every circuit's GKR reads at its width (`circuitWidth`),
the combinations' and the Ligero test's reads at most `Lmax` elements. -/
def ForkLoadNumbers (gp gt : Fin (ir.circs d).length → ℕ) (Lmax : ℕ) : Prop :=
  (∀ i : Fin (ir.cbatches d R.Pk).length,
      max (max (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).n
        (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.sumBatches d R.Pk).length,
      max (max (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).n
        (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).k) 3 ≤ Lmax) ∧
  ((∀ i : Fin (ir.mbatches d R.Pk).length,
      max (max (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).n
        (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
    ∀ i : Fin (ir.sumMBatches d R.Pk).length,
      max (max (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).n
        (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.circs d).length, max (ir.circuitWidth (ir.circAt d i)) 2 ≤ Lmax) ∧ ir.claimCount (d := d) (Pk := R.Pk) ≤ Lmax ∧ laterBound R.rs ≤ Lmax ∧
  R.numbers.Sh.nrep * forkRBound R gp gt +
    ((forkLinBound R gt + forkQBound R gt * 3) +
      (forkQBound R gt + R.numbers.Sh.w - 1) / R.numbers.Sh.w) ≤ Lmax

instance (gp gt : Fin (ir.circs d).length → ℕ) (Lmax : ℕ) :
    Decidable (ForkLoadNumbers R gp gt Lmax) := by
  unfold ForkLoadNumbers
  infer_instance

/-- **The load numbers of domain `d`'s forked proof other than the first combination's**
(`ForkLoadNumbers` without the first combination's `nc`; decidable). -/
def ForkRestNumbers (gp gt : Fin (ir.circs d).length → ℕ) (Lmax : ℕ) : Prop :=
  (∀ i : Fin (ir.cbatches d R.Pk).length,
      max (max (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).n
        (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.sumBatches d R.Pk).length,
      max (max (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).n
        (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).k) 3 ≤ Lmax) ∧
  ((∀ i : Fin (ir.mbatches d R.Pk).length,
      max (max (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).n
        (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).k) 3 ≤ Lmax) ∧
    ∀ i : Fin (ir.sumMBatches d R.Pk).length,
      max (max (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).n
        (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).k) 3 ≤ Lmax) ∧
  (∀ i : Fin (ir.circs d).length, max (ir.circuitWidth (ir.circAt d i)) 2 ≤ Lmax) ∧ laterBound R.rs ≤ Lmax ∧
  R.numbers.Sh.nrep * forkRBound R gp gt +
    ((forkLinBound R gt + forkQBound R gt * 3) +
      (forkQBound R gt + R.numbers.Sh.w - 1) / R.numbers.Sh.w) ≤ Lmax

instance (gp gt : Fin (ir.circs d).length → ℕ) (Lmax : ℕ) :
    Decidable (ForkRestNumbers R gp gt Lmax) := by
  unfold ForkRestNumbers
  infer_instance

/-- **The Ligero test's reads from the load numbers' bound**, at bounds `gp` on the circuits' pads
and `gt` on their tails' depths (`card_forkJoinIp_Q_le`, `card_forkJoinIp_Lin`, `card_rootOwn`). -/
theorem forkLigero_le {gp gt : Fin (ir.circs d).length → ℕ} {Lmax : ℕ}
    (hp : ∀ i, Fintype.card (ir.circSource d src i).PadIdx ≤ gp i)
    (ht : ∀ i, (ir.circSource d src i).tail.depth + 1 ≤ gt i)
    (h7 : R.numbers.Sh.nrep * forkRBound R gp gt +
      ((forkLinBound R gt + forkQBound R gt * 3) +
        (forkQBound R gt + R.numbers.Sh.w - 1) / R.numbers.Sh.w) ≤ Lmax) :
    (ir.fieldFork src R).join.cp.nrep * (ir.fieldFork src R).join.R +
      ((ir.fieldFork src R).join.nLr + (ir.fieldFork src R).join.nQ) ≤ Lmax := by
  have hgt : ∑ i, ((ir.circSource d src i).tail.depth + 1) ≤ ∑ i, gt i :=
    Finset.sum_le_sum fun i _ => ht i
  have hgp : ∑ i, Fintype.card (ir.circSource d src i).PadIdx ≤ ∑ i, gp i :=
    Finset.sum_le_sum fun i _ => hp i
  have hQ : Fintype.card (forkJoinIp src R).Q ≤ forkQBound R gt := by
    refine (card_forkJoinIp_Q_le src R).trans ?_
    rw [card_fieldMaskedReduction_Q]
    unfold forkQBound
    omega
  have hL : Fintype.card (forkJoinIp src R).Lin ≤ forkLinBound R gt := by
    rw [card_forkJoinIp_Lin, card_fieldMaskedReduction_Lin]
    have := outClaims_le_laterBound src R
    unfold forkLinBound
    omega
  have hO : Fintype.card (ir.RootOwn d R.Pk R.rs (ir.ClaimPads d src R.Pk)) ≤
      1 + ((ir.cellKeys d).filter fun k => (ir.cellNode (R.rs.map REdge.plan) k).isNone).length +
        (R.rs.map fun r => r.kit.masks.nOwn).sum +
        (∑ i : Fin (ir.cbatches d R.Pk).length, Fintype.card ((ir.cbatches d R.Pk)[i]).Pad +
          ∑ i : Fin (ir.sumBatches d R.Pk).length,
            (Fintype.card ((ir.sumBatches d R.Pk)[i]).cb.Pad + 8) +
          ∑ i : Fin (ir.mbatches d R.Pk).length, Fintype.card ((ir.mbatches d R.Pk)[i]).Pad +
          ∑ i : Fin (ir.sumMBatches d R.Pk).length,
            (Fintype.card ((ir.sumMBatches d R.Pk)[i]).mb.Pad + 8) + ∑ i, gp i) := by
    rw [card_rootOwn, card_maskOwn, card_claimPads]
    have := card_rootCell_le (ir := ir) (d := d) (R.rs.map REdge.plan)
    omega
  have hR : (ir.fieldFork src R).join.R ≤ forkRBound R gp gt := by
    rw [forkJoin_R]
    unfold forkRBound
    refine Nat.add_le_add (Nat.add_le_add (Nat.div_le_div_right ?_) ?_)
      (Ligero.MaskRow.TreeLayout.Masking.extra_le_six _)
    · omega
    · exact Nat.mul_le_mul_left 3 (Nat.div_le_div_right (by omega))
  have hnQ : (ir.fieldFork src R).join.nQ ≤ (forkQBound R gt + R.numbers.Sh.w - 1) / R.numbers.Sh.w := by
    rw [forkJoin_nQ]
    exact Nat.div_le_div_right (by omega)
  have hnLr : (ir.fieldFork src R).join.nLr ≤ forkLinBound R gt + forkQBound R gt * 3 := by
    rw [forkJoin_nLr]
    nlinarith
  have hrep : (ir.fieldFork src R).join.cp.nrep = R.numbers.Sh.nrep :=
    Ligero.MaskRow.TreeLayout.Numbers.nrep_setup ..
  rw [hrep]
  have := Nat.mul_le_mul_left R.numbers.Sh.nrep hR
  omega

/-- **The load numbers give the load sizes**, at bounds `gp` on the circuits' pads and `gt` on
their tails' depths (`forkLigero_le`). -/
theorem forkLoadSizesLe_of {gp gt : Fin (ir.circs d).length → ℕ} {Lmax : ℕ}
    (hp : ∀ i, Fintype.card (ir.circSource d src i).PadIdx ≤ gp i)
    (ht : ∀ i, (ir.circSource d src i).tail.depth + 1 ≤ gt i)
    (ho : ∀ i, (ir.circSource d src i).outDim ≤ ir.circuitWidth (ir.circAt d i))
    (h : ForkLoadNumbers R gp gt Lmax) : ForkLoadSizesLe src R Lmax := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, fun i => (max_le_max (ho i) le_rfl).trans (h4 i), h5, h6,
    forkLigero_le src R hp ht h7⟩

/-- **The rest numbers give the rest sizes** (`forkLigero_le`). -/
theorem forkRestSizesLe_of {gp gt : Fin (ir.circs d).length → ℕ} {Lmax : ℕ}
    (hp : ∀ i, Fintype.card (ir.circSource d src i).PadIdx ≤ gp i)
    (ht : ∀ i, (ir.circSource d src i).tail.depth + 1 ≤ gt i)
    (ho : ∀ i, (ir.circSource d src i).outDim ≤ ir.circuitWidth (ir.circAt d i))
    (h : ForkRestNumbers R gp gt Lmax) : ForkRestSizesLe src R Lmax := by
  obtain ⟨h1, h2, h3, h4, h6, h7⟩ := h
  exact ⟨h1, h2, h3, fun i => (max_le_max (ho i) le_rfl).trans (h4 i), h6,
    forkLigero_le src R hp ht h7⟩

end Join

end

end GordieHowe.RealizedProgram
