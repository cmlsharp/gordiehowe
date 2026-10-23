-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Errors
public import GordieHowe.Language.Honest.Basic
public import GordieHowe.ProofSystem.Program.PiFormat
public import GordieHowe.ProofSystem.Program.Comap
public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.ProofSystem.Program.Basic

@[expose] public section

/-!
# GordieHowe: the codecs and readers of a program's phases

The pieces of a transcript for the application phase of a program's proof system (`GordieHowe.RealizedProgram.layout`:
phase `k + 1` draws its challenges, then sends its late values masked):

* **the phases' messages** (`GordieHowe.RealizedProgram.msgCodec`, `GordieHowe.RealizedProgram.appWrites`): the late values of the phase
  in identifier order (`GordieHowe.RealizedProgram.lateList`), each an array of elements of its pad space written as
  elements of its field (`Codec.FieldBytes.ofSubgroup` at the field's bytes `GordieHowe.RealizedProgram.FieldBytesOf`),
  after an empty byte string; the bound `GordieHowe.RealizedProgram.msgB`;
* **the phases' challenges** (`GordieHowe.RealizedProgram.phaseReader`, `GordieHowe.RealizedProgram.appReaders`): the challenges of the
  phase in identifier order (`GordieHowe.RealizedProgram.chalList`), each a vector of its size drawn by a reader of its
  sampler's values, with the loads (`GordieHowe.RealizedProgram.appReaders_allLoads`);
* **the phased honest prover at any lowering** (`GordieHowe.RealizedProgram.ProofSystem.phasedHonestAt`): the protocol's honest prover
  (`GordieHowe.RealizedProgram.ProofSystem.honest`) does not read the lowering;
* general facts: shape bounds of GKR sources weaken (`CircuitBudget.WidthsAtMost.mono`,
  `GordieHowe.GKR.LayeredCircuit.ShapeAtMost.mono`).

The codecs are injective, self-delimiting and bounded; byte identity with the C++ is not a goal (a
subfield message is written as elements of its field).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## The phases' messages -/

variable (ir I) in
/-- **The late values of phase `k + 1`**, in identifier order. -/
def lateList (k : Fin ir.phases) :
    List {l : (ir.layout I).Late // (ir.layout I).phase l = k} :=
  (List.finRange ir.values.length).filterMap fun v : Fin ir.values.length =>
    if h : ir.IsLate v ∧ (ir.value v).phase - 1 = k then some ⟨⟨v, h.1⟩, Fin.ext h.2⟩ else none

theorem lateList_nodup (k : Fin ir.phases) : (ir.lateList I k).Nodup := by
  refine List.Nodup.filterMap (fun a a' b ha ha' => ?_) (List.nodup_finRange _)
  simp only [Option.mem_def] at ha ha'
  split_ifs at ha ha' with h h'
  obtain rfl := Option.some_inj.1 ha
  exact (congrArg (fun l => l.1.1) (Option.some_inj.1 ha')).symm

theorem mem_lateList (k : Fin ir.phases) (l : {l : (ir.layout I).Late // (ir.layout I).phase l = k}) :
    l ∈ ir.lateList I k := by
  refine List.mem_filterMap.2 ⟨l.1.1, List.mem_finRange _, ?_⟩
  have h : ir.IsLate l.1.1 ∧ (ir.value l.1.1).phase - 1 = k := ⟨l.1.2, congrArg Fin.val l.2⟩
  simp only [h, and_self, dite_true]
  rfl

variable (I) in
/-- **The bytes of the fields' elements**: `fb f` bytes for an element of field `f`. -/
structure FieldBytesOf where
  /-- The bytes of an element of field `f`. -/
  fb : ℕ → ℕ
  /-- The encoding of field `f`. -/
  bytes : ∀ f, Codec.FieldBytes (I f).K (fb f)

variable (FB : FieldBytesOf I)

variable (ir) in
/-- **The codec of late value `v`'s message**: an array of `size` elements of its pad space, each
written as an element of its field. -/
def maskCodec (v : ℕ) : WriteCodec (ir.Mask I v) :=
  WriteCodec.fieldArray ((FB.bytes (ir.valueField v)).ofSubgroup
    ((I (ir.valueField v)).space (ir.value v).padSpace)) (ir.value v).size

variable (ir) in
/-- **The codec of phase `k + 1`'s message**: the phase's late values in identifier order
(`lateList`), each by `maskCodec`. -/
def msgCodec (k : Fin ir.phases) : WriteCodec ((ir.layout I).PhaseMsg k) :=
  WriteCodec.piList (ir.lateList I k) (lateList_nodup k) (mem_lateList k)
    fun l => ir.maskCodec FB l.1.1

variable (ir) in
/-- **The bound of phase `k + 1`'s message**: `9` bytes, and per late value `9` bytes and its
elements' bytes. -/
def msgB (k : Fin ir.phases) : ℕ :=
  9 + ((ir.lateList I k).map fun l =>
    9 + (ir.value l.1.1).size * FB.fb (ir.valueField l.1.1)).sum

theorem msgCodec_B (k : Fin ir.phases) : (ir.msgCodec FB k).B = ir.msgB FB k :=
  WriteCodec.piList_B _ _ _ _

variable (ir) in
/-- **The codecs of the phases** (`PhaseLayout.writes` at `msgCodec`), each message at most `B`
bytes (`hB`). -/
def appWrites {B : ℕ} (hB : ∀ k, ir.msgB FB k ≤ B) : SpecWrites (ir.layout I).spec B :=
  (ir.layout I).writes (ir.msgCodec FB) fun k => (msgCodec_B FB k).trans_le (hB k)

/-! ## The phases' challenges -/

variable (ir) in
/-- **The challenges of phase `k + 1`**, in identifier order. -/
def chalList (k : Fin ir.phases) : List (ir.ChalAt k) :=
  (List.finRange ir.challenges.length).filterMap fun j : Fin ir.challenges.length =>
    if h : (ir.challenge j).phase = k + 1 then some ⟨j, h⟩ else none

theorem chalList_nodup (k : Fin ir.phases) : (ir.chalList k).Nodup := by
  refine List.Nodup.filterMap (fun a a' b ha ha' => ?_) (List.nodup_finRange _)
  simp only [Option.mem_def] at ha ha'
  split_ifs at ha ha' with h h'
  obtain rfl := Option.some_inj.1 ha
  exact (congrArg Subtype.val (Option.some_inj.1 ha')).symm

/-- A phase has at most the program's challenges. -/
theorem length_chalList_le (k : Fin ir.phases) : (ir.chalList k).length ≤ ir.challenges.length :=
  (List.length_filterMap_le _ _).trans (List.length_finRange).le

theorem mem_chalList (k : Fin ir.phases) (j : ir.ChalAt k) : j ∈ ir.chalList k := by
  refine List.mem_filterMap.2 ⟨j.1, List.mem_finRange _, ?_⟩
  simp only [j.2, dite_true]
  rfl

variable (I) in
/-- **The readers of the challenges' sampled values**: challenge `j`'s sampler's values by
`reader j`. -/
abbrev SamplerReaders (ir : RealizedProgram) : Type :=
  ∀ j : Fin ir.challenges.length,
    CReader ((I (ir.chalField j)).SamplerTy (ir.challenge j).sampler)

variable (rd : SamplerReaders I ir)

variable (ir) in
/-- **The load of challenge `j`'s draws**: `size` draws of its sampler's reader. -/
def chalLoad (j : Fin ir.challenges.length) : Load :=
  (rd j).load.nsmul (ir.challenge j).size

variable (ir) in
/-- **The reader of phase `k + 1`'s challenge**: the phase's challenges in identifier order
(`chalList`), each a vector of its size drawn by `rd`, each challenge's load at most `L k`. -/
def phaseReader (L : Fin ir.phases → Load) (hL : ∀ k (j : ir.ChalAt k), ir.chalLoad rd j.1 ≤ L k)
    (k : Fin ir.phases) : CReader ((ir.layout I).Ch k) :=
  CReader.piList (ir.chalList k) (chalList_nodup k) (mem_chalList k)
    (fun j => CReader.pi (ir.challenge j.1).size (rd j.1)) (L k) (hL k)

variable (ir) in
/-- **The challenge readers of the phases** (`PhaseLayout.readers` at `phaseReader`). -/
def appReaders (L : Fin ir.phases → Load) (hL : ∀ k (j : ir.ChalAt k), ir.chalLoad rd j.1 ≤ L k) :
    SpecReaders (ir.layout I).spec :=
  (ir.layout I).readers (ir.phaseReader rd L hL)

/-- **The loads of the phases' readers** satisfy `good` when phase `k + 1`'s `L k` repeated once
per challenge of the phase does. -/
theorem appReaders_allLoads (L : Fin ir.phases → Load)
    (hL : ∀ k (j : ir.ChalAt k), ir.chalLoad rd j.1 ≤ L k) {good : Load → Prop}
    (h : ∀ k, good ((L k).nsmul (ir.chalList k).length)) :
    (ir.appReaders rd L hL).AllLoads good :=
  (ir.layout I).readers_allLoads fun k => h k

/-! ## The honest prover at any lowering -/

namespace ProofSystem

variable {P : Export.Plan} (B : ir.ProofSystem P I) {W : Type} {rel : Set (ir.Valuation I × W)}
  (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
    (GordieHowe.Domain.lowered B.guardedDomain))

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The phased honest prover at the lowering `Lw`** (`ProofSystem.phasedHonest`, which is this at the
protocol's lowering): the honest prover does not read the lowering. -/
def phasedHonestAt (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    (H : ir.HonestCore I relH) :
    ((Lw.check (ir.stmtOk I)).toPhased B.enforcement).Honest Inp relH
      (fun d => (HD A d).In) fun d => (HD A d).dom where
  wit d y π := (HD A d).encode (ir.honestCells I d (H.val y) π)
  late := H.late
  challengeCausal y π := challengeCausal_of_respectsReads B.valid.program.order (H.respects y) π
  padOrder y := padOrder_of_respectsReads B.valid.program.pads (H.respects y)
  bad := H.bad
  ok_honest x _ hy _ _ _ := stmtOk_iff.2 ⟨H.checks x _ hy, H.bounded x _ hy⟩
  dom_honest x _ hy _ _ hc d := (HD A d).dom_of x _ _ (B.holds_honest H hy hc d)

end ProofSystem

end

end GordieHowe.RealizedProgram

namespace GordieHowe.GKR

namespace CircuitBudget

variable {F : Type} [Field F]

/-- Every layer's width bound weakens to a larger bound. -/
theorem WidthsAtMost.mono {d : ℕ} {C : Circuit F d} {w w' : ℕ} (h : WidthsAtMost C w)
    (hw : w ≤ w') : WidthsAtMost C w' := by
  induction C with
  | input => trivial
  | layer Q tail ih => exact ⟨h.1.trans hw, ih h.2⟩

end CircuitBudget

namespace LayeredCircuit

variable {F : Type} [Field F] {d : ℕ}

/-- **A shape bound weakens** to larger widths and depths. -/
theorem ShapeAtMost.mono {S : LayeredCircuit F d} {w l w' l' : ℕ} (h : S.ShapeAtMost w l)
    (hw : w ≤ w') (hl : l ≤ l') : S.ShapeAtMost w' l' :=
  ⟨h.outDim_le.trans hw, h.widths.mono hw, h.depth_le.trans hl⟩

end LayeredCircuit

end GordieHowe.GKR
