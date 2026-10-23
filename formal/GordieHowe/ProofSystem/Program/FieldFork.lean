-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldDomain
public import GordieHowe.ProofSystem.RingSwitching.TreeFork
public import GordieHowe.ProofSystem.FieldProof.ClaimFix

@[expose] public section

/-!
# GordieHowe: the circuit proof of any domain, forked

The series–parallel form (`TreeFork`, `lib/gordiehowe/transcript_fork.h`) of the circuit proof of
domain `d` of a valid realized program (`GordieHowe.RealizedProgram.fieldProof`):

* **the branches** (`GordieHowe.RealizedProgram.fieldFork`): the domain's masked reduction's branches in order
  (`GordieHowe.RealizedProgram.branchIP` at `GordieHowe.RealizedProgram.branchEquiv`): each covered batch on columns, on bits, each
  covered merged batch on columns, on bits, then GKR (the circuits in sequence), each on the domain's public input;
* **the join** (`GordieHowe.RealizedProgram.fieldFork`): the domain's tree domain on its Ligero numbers
  (`TreeSpec.layoutDomain`) at the domain's masked reduction read at the branches' transcripts
  (`MaskedReduction.fixAt`, `GordieHowe.RealizedProgram.fieldForkTranscript`), so its stages and its Ligero setup are the
  domain's;
* **soundness** (`GordieHowe.RealizedProgram.fieldForkSound`): each branch's (`GordieHowe.RealizedProgram.branchSound`), the rows and the
  quadratic triples as the fixed claims (`GordieHowe.RealizedProgram.FixedAt`), the join's masked reduction sound at the fixed
  transcript (`MaskedReduction.Sound.fixAt`, `GordieHowe.RealizedProgram.outHolds_fieldForkTranscript_iff`), the readout the
  committed cells and the domain's predicate under the compiler trust (`GordieHowe.RealizedProgram.holds_of_fieldSat`).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge BatchedZerocheck IOP IOP.ProtocolSpec Ligero.MaskRow
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)

/-- **The full transcripts of the branches.** -/
abbrev ForkTrs : Type :=
  (b : Fin (ir.nBranch d R.Pk)) → (ir.branchIP src R.rs (ir.branchEquiv d R.Pk b)).spec.Transcript
    (Fin.last (ir.branchIP src R.rs (ir.branchEquiv d R.Pk b)).n)

/-- **The masked reduction's transcript from the branches'**: the branches' in order; the rows have no
rounds. -/
def fieldForkTranscript (trs : ir.ForkTrs src R) :
    (ir.fieldMaskedReduction src R.rs).spec.Transcript (Fin.last (ir.fieldMaskedReduction src R.rs).n) :=
  Transcript.join (FieldProof.MaskedReduction.ofListTranscript trs (List.finRange _)) fun i => i.elim0

/-- **The join's masked reduction**: the domain's masked reduction at the branches' transcripts. -/
def fieldJoinMaskedReduction :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src R.Pk R.rs) (ir.DomainPub I × ir.ForkTrs src R)
      (ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K) id (ir.FLog src R.Pk R.rs)
      (ir.claimCount (d := d) (Pk := R.Pk)) :=
  (ir.fieldMaskedReduction src R.rs).fixAt Prod.fst fun p' => ir.fieldForkTranscript src R p'.2

/-- **The forked domain `d`** (see the module docstring); the join's claims read the nodes of the
masked reduction's (`readsOnly_fieldMaskedReduction`), which gives the routing obligation. -/
abbrev fieldFork :
    TreeFork (I (ir.domainField d)).K R.Pk.p (ir.FCell src R.Pk R.rs) (ir.FLog src R.Pk R.rs)
      (ir.DomainPub I) (ir.claimCount (d := d) (Pk := R.Pk)) where
  nb := ir.nBranch d R.Pk
  nb_pos := Nat.succ_pos _
  ncb b := ir.branchNc d R.Pk (ir.branchEquiv d R.Pk b)
  branch b := ir.branchIP src R.rs (ir.branchEquiv d R.Pk b)
  join := (ir.fieldTreeOf src R).layoutDomain R.numbers (ir.fieldJoinMaskedReduction src R)
    (routes_path _ 0 _ _ _ _ ((readsOnly_fieldMaskedReduction src R.rs).fixAt _ _))

/-- **The join's logical assignment is the tree's** (`path_level_eq`). -/
theorem fieldFork_view :
    (ir.fieldFork src R).view = (ir.treeLevel d R.rs (ir.ClaimPads d src R.Pk)).view :=
  congrArg Level.view (path_level_eq _ 0 _ _ 0 _ Fin.elim0)

variable {src R} in
/-- **The fixed claims** at the logical assignment `view`: the rows and the quadratic triples. -/
def FixedAt (view : (ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K) →
      ir.FLog src R.Pk R.rs → (I (ir.domainField d)).K) (p : ir.DomainPub I)
    (x : ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K) : Prop :=
  (∀ q, (ir.rowClaims src R.rs p q).eval (view x) = 0) ∧
    Ligero.Routing.SourceProducts (ir.quadProducts src R.rs) x

/-- **The masked reduction's output at the branches' transcripts** is every branch's output and the fixed
claims. -/
theorem outHolds_fieldForkTranscript_iff
    (view : (ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K) →
      ir.FLog src R.Pk R.rs → (I (ir.domainField d)).K)
    (p : ir.DomainPub I) (trs : ir.ForkTrs src R)
    (x : ir.FCell src R.Pk R.rs → (I (ir.domainField d)).K) :
    (ir.fieldMaskedReduction src R.rs).OutHolds view p (ir.fieldForkTranscript src R trs) x ↔
      (∀ b, (ir.branchIP src R.rs (ir.branchEquiv d R.Pk b)).OutHolds view p (trs b) x) ∧
        FixedAt (R := R) view p x := by
  refine (FieldProof.MaskedReduction.outHolds_append_iff _ _ view p _ x).trans ?_
  erw [Transcript.left_join, Transcript.right_join]
  rw [FieldProof.MaskedReduction.outHolds_ofList_iff]
  refine and_congr (by simp only [List.mem_finRange, true_implies]) ?_
  exact FieldProof.MaskedReduction.outHolds_staticProducts_iff _ _ view p _ x

/-- **The forked soundness of domain `d`** (see the module docstring). -/
noncomputable def fieldForkSound : (ir.fieldFork src R).Sound (ir.FieldHolds I src R.rs) where
  sat b := ir.branchSat src R.rs (ir.branchEquiv d R.Pk b)
  εb b := ir.branchError src R.rs (ir.branchEquiv d R.Pk b)
  branchSound b := (ir.fieldFork_view src R).symm ▸ ir.branchSound src R.rs (ir.branchEquiv d R.Pk b)
  fixed := FixedAt (R := R) (ir.fieldFork src R).view
  εj i := i.1.elim0
  joinSound := FieldProof.MaskedReduction.Sound.fixAt _ _ _ fun p' x =>
    (ir.outHolds_fieldForkTranscript_iff src R _ p'.1 p'.2 x).symm
  readout x := x
  readout_sound p x _ hb hf T := by
    obtain ⟨⟨hc, hsb, hm, hsm⟩, hg⟩ := (ir.forall_branchSat_iff src R.rs p x).1 hb
    rw [FixedAt, fieldFork_view] at hf
    exact ir.holds_of_fieldSat src R.rs R.claimOk T p x ⟨hc, hsb, hm, hsm, hg, hf.1, hf.2⟩

/-- **The forked circuit proof of domain `d`** (`TreeFork.shapeOf` at the fixed claims; the
forked soundness's `toShape`). -/
abbrev fieldForkShape :=
  (ir.fieldFork src R).shapeOf (FixedAt (R := R) (ir.fieldFork src R).view) fun x => x

/-- **The forked soundness of domain `d`'s forked circuit proof.** -/
noncomputable abbrev fieldForkFull := (ir.fieldForkSound src R).toFork

/-- **How domain `d`'s forked verdict reads its oracle message** (`TreeFork.oracleOf`; the forked
soundness's `oracle`). -/
abbrev fieldForkOracle :=
  (ir.fieldFork src R).oracleOf (FixedAt (R := R) (ir.fieldFork src R).view) fun x => x

end

end GordieHowe.RealizedProgram
