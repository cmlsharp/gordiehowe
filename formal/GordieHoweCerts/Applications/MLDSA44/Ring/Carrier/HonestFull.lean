-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestCross
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestFull

@[expose] public section

/-!
# GordieHowe: the honest execution of the ML-DSA-44 ring carriers

The execution of the source program of an ML-DSA-44 ring carrier
(`GordieHowe.RealizedProgram.SourceExecution`), generic in the program through its decided facts
(`MldsaCarrierHonest`, `MldsaCarrierSelect`, `MldsaCarrierQuot`, `MldsaCarrierExec`), from which
`GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` builds the honest strategy:

* **The honest relation** (`relH`): the program statement of an honest input
  (`GordieHowe.MLDSA44.Ring.RingIn`: a ring statement and a witness of the ring relation) is the
  frontend's statement of its ring statement (`stmtOf`), which holds the ring's carrier rows
  (`RowsOf`, `rowsOf_stmtOf`).
* **The honest values in their nodes** (`CarrierANode`: the node `GF(p^1)` of domain `A`'s field
  is a subfield; `specE_mem`, `aValE_mem`, `honest_cell_mem`), from which the honest roles put the
  node-typed values in their types (`GordieHowe.RealizedProgram.HonestRoles.sourceSatAt`).
* **Every source predicate holds** (`source_holds`): domain `H`'s core and domain `A`'s gadgets
  through the renamings (`core_holds`, `aSource_holds`), the member's checks (`select_honest`,
  `idxBool_honest`, `muBool_honest`), the signature relation and its quotient's range
  (`sig_row`, the four rows at `r`, and `qRange_holds`) and the crossing (`cross_holds`), whose
  operands read bits
  (`crossBits_honest`).
* **The execution** (`sourceExecution`): the honest values read off by `execOf`, no late value,
  no completeness event (`δ = 0`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

set_option hygiene false in
local notation "σH" => CarrierHEmbed.σ program

set_option hygiene false in
local notation "hV" => CarrierHEmbed.V program

set_option hygiene false in
local notation "σA" => CarrierAEmbed.σ program

set_option hygiene false in
local notation "aV" => CarrierAEmbed.V program

set_option hygiene false in
local notation "predMapA" => CarrierAEmbed.pred program

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open MLDSA44.NativeAlgebraCircuit (outputBits flat)
open MLDSA44.NativeAlgebraCircuit.Honest (hintBool)
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt muBitNat muBitNat_le natGF16B hValCore_mem_gf16
  hValCore_mem_bit cA w1A advice)
open MLDSA44.Emulated (MldsaELayout aValues MldsaEAlgebra MldsaEmulatedHonest DigitLayout fm fmz)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-! ## The program facts -/

/-- **The realization's predicates of an ML-DSA-44 ring carrier**: `mac.A`, the norm range's top
row, the MAC blind's Booleanity, the MAC's low, high and no-wrap rows and its tail `mac`. -/
def carrierRealizationPreds : List ℕ := [8, 9, 16, 23, 24, 25, 249]

/-- **The program facts of an ML-DSA-44 ring carrier's execution** (decided per carrier): `251`
predicates, the source predicates (the realization's `8`, `9`, `16`, `23 … 25`, `249` are none),
no statement check, the keys' declared bound `q`, the operands of every cross-field `equal`, the
crossing's `A` operand's length and the committed source cells' classes. -/
class MldsaCarrierExec (program : RealizedProgram) [CarrierHEmbed program] [CarrierAEmbed program]
    [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
    [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
    [MldsaCarrierFront program] [MldsaCarrierQuot program] : Prop where
  /-- The program is well formed. -/
  wf : program.WellFormed
  /-- The realization's predicates are no source predicates. -/
  nonSource : ∀ q ∈ carrierRealizationPreds, program.inSource (program.predicate q) = false
  /-- **Every predicate is a held one, one of the carrier's own or a realization's**: the carrier
  predicate of a held native predicate of domain `H`'s core (`corePredLo … hPredHi`) or of a held
  emulated gadget of `aSource`; the table's selection, the signature relation's four rows, the
  `μ` bits' Booleanity, the index bits' check, the quotient's range or the crossing; or one of
  `carrierRealizationPreds`. -/
  coverage : ∀ q < program.predicates.length,
    (∃ p ∈ CarrierHEmbed.held program, p.2 = q ∧ corePredLo ≤ p.1 ∧ p.1 ≤ hPredHi) ∨
      (∃ p ∈ CarrierAEmbed.held program, p.2 = q ∧ p.1 ∈ aSource) ∨
      q ∈ [(TableSelect.shape program).pred, MldsaRandomPoint.rel0 program,
        MldsaRandomPoint.rel0 program + 1, MldsaRandomPoint.rel0 program + 2,
        MldsaRandomPoint.rel0 program + 3, MldsaCarrierFront.muBoolPred program,
        (TableSelect.shape program).idxPred, MldsaCarrierQuot.qPred program,
        MldsaCarrierFront.crossPred program] ∨
      q ∈ carrierRealizationPreds
  /-- The statement has no member checks. -/
  checks : program.statement.checks = []
  /-- The keys are declared below `q`. -/
  ranges : program.declaredRanges = [(MldsaRingStmt.keys program, 8380417)]
  /-- The keys have `64 · 5120` coordinates. -/
  keysSize : (program.value (MldsaRingStmt.keys program)).size = 327680
  /-- Every cross-field `equal` crosses `ref 558` of domain `H` and `ref 95` of domain `A`. -/
  crossOperands : program.crossOperandsB 1 (.ref 558) 0 (.ref 95) = true
  /-- The crossing's `A` operand has `7168` coordinates. -/
  len95 : program.exprLen (.ref 95) = 7168
  /-- The committed source cells' classes. -/
  cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (([56, 57, 58, 59, 66] ++ (MldsaCarrierHonest.qD program).ids).contains v &&
        program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)") ||
      (match hOf program v with
        | some u => (natGF16B u && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "GF(2^16)") ||
          ([556, 561].contains u && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "bit")
        | none => match aOf program v with
          | some u => (aValues (MldsaEAlgebra.layout (CarrierAEmbed.emu program))).contains u &&
            program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)"
          | none => false)) = true

/-- **The node `GF(p^1)` of domain `A`'s field is a subfield** (the prime subfield of a Goldilocks
extension). A fact about the field interpretation, instantiated for Goldilocks² and Goldilocks⁴. -/
class CarrierANode (F0 : FieldInterp) : Prop where
  /-- The node `GF(p^1)` is a subfield. -/
  subfield : ∃ S : Subfield F0.K, ∀ x, x ∈ F0.node "GF(p^1)" ↔ x ∈ S

/-- **Goldilocks² has characteristic `pGold`** (`ExpChar`), at the field interpretation. -/
instance instExpCharGold2 : ExpChar RealizedProgram.gold2.K pGold :=
  inferInstanceAs (ExpChar GoldilocksExt2 pGold)

/-- **Goldilocks²'s node `GF(p^1)` is the prime subfield `F_p`.** -/
instance : CarrierANode RealizedProgram.gold2 :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ RealizedProgram.gold2Node "GF(p^1)" ↔ _
    rw [RealizedProgram.gold2Node, if_pos rfl]
    rfl⟩⟩

/-- **Goldilocks⁴ has characteristic `pGold`** (`ExpChar`), at the field interpretation. -/
instance instExpCharGold4 : ExpChar RealizedProgram.gold4.K pGold :=
  inferInstanceAs (ExpChar GoldilocksExt4 pGold)

/-- **Goldilocks⁴'s node `GF(p^1)` is the prime subfield `F_p`.** -/
instance : CarrierANode RealizedProgram.gold4 :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ RealizedProgram.gold4Node "GF(p^1)" ↔ _
    rw [RealizedProgram.gold4Node, if_pos rfl]
    rfl⟩⟩

/-! ## The renamings' inverses -/

theorem hOf_spec {program : RealizedProgram} [CarrierHEmbed program] {v u : ℕ}
    (h : hOf program v = some u) : u ∈ hV ∧ (σH).val u = v := by
  unfold hOf at h
  exact Renaming.invOn_spec h

theorem aOf_spec {program : RealizedProgram} [CarrierAEmbed program] {v u : ℕ}
    (h : aOf program v = some u) : u ∈ aV ∧ (σA).val u = v := by
  unfold aOf at h
  exact Renaming.invOn_spec h

/-! ## The honest values in their nodes -/

section Nodes

variable {F0 FH : FieldInterp} [CarrierANode F0] (y : RingIn msgLen)

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

theorem natCast_memA (n : ℕ) : (n : (interp 0).K) ∈ (interp 0).node "GF(p^1)" := by
  obtain ⟨S, hS⟩ := CarrierANode.subfield (F0 := F0)
  exact (hS _).2 (natCast_mem S n)

theorem bit_memA {z : (interp 0).K} (h : z = 0 ∨ z = 1) : z ∈ (interp 0).node "GF(p^1)" := by
  rcases h with rfl | rfl
  · exact_mod_cast natCast_memA (F0 := F0) (FH := FH) 0
  · exact_mod_cast natCast_memA (F0 := F0) (FH := FH) 1

/-- **The honest spectra lie in `GF(p^1)`**: sums of products of naturals and powers of `ψ`. -/
theorem specE_mem (j : ℕ) : specE y (interp 0).K j ∈ (interp 0).node "GF(p^1)" := by
  obtain ⟨S, hS⟩ := CarrierANode.subfield (F0 := F0)
  change specE y F0.K j ∈ F0.node "GF(p^1)"
  rw [hS]
  unfold specE
  split_ifs with hj
  · rw [Ops.nttScheme_apply (k := 8) (by norm_num) _ _ (Nat.mod_lt _ (by norm_num))]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (natCast_mem _ _)
      (Subfield.pow_mem _ (natCast_mem _ _) _)
  · exact zero_mem _

/-- **The nodes of an ML-DSA-44 ring carrier contain `1`**: `GF(p^1)` of field `0`, `GF(2^16)`
(the selection subfield's node, `MldsaHNodes.node_of_sel`) and `bit` of field `1`. -/
theorem oneNodes [HField FH] [MldsaHNodes FH] :
    OneNodes interp [(0, "GF(p^1)"), (1, "GF(2^16)"), (1, "bit")] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simpa using natCast_memA (F0 := F0) (FH := FH) 1
  · exact MldsaHNodes.node_of_sel (FH := FH) 1 (one_mem _)
  · exact (MldsaHNodes.bit_iff (FH := FH) 1).2 (Or.inr rfl)

theorem dite_mem_zero' {K : Type*} [Field K] {S : AddSubgroup K} {p : Prop} [Decidable p]
    {f : p → K} (h : ¬ p) : (if hp : p then f hp else 0) ∈ S := by
  rw [dif_neg h]
  exact zero_mem _

/-- **The honest high halves lie in `GF(p^1)`**: sums of products of integers' casts. -/
theorem qHonC_memA (i : Fin 4) (t : ℕ) : qHonC y (interp 0).K i t ∈ (interp 0).node "GF(p^1)" := by
  obtain ⟨S, hS⟩ := CarrierANode.subfield (F0 := F0)
  change qHonC y F0.K i t ∈ F0.node "GF(p^1)"
  rw [hS]
  exact qHonC_mem y S i t

/-- **Domain `A`'s honest values lie in `GF(p^1)`.** -/
theorem aValE_mem {L : MldsaELayout} (hnd : (aValues L).Nodup) {u : ℕ} (hu : u ∈ aValues L)
    (j : ℕ) : aValE y (interp 0).K L u j ∈ (interp 0).node "GF(p^1)" := by
  have natm := natCast_memA (F0 := F0) (FH := FH)
  have bitA := fun {z : (interp 0).K} (h : z = 0 ∨ z = 1) => bit_memA (F0 := F0) (FH := FH) h
  rcases List.mem_append.1 hu with hf | hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · by_cases hj : j < 1024
      · rw [aValE_59 y _ _ hj]; exact natm _
      · unfold aValE; rw [if_neg (by decide), if_neg (by decide)]; exact dite_mem_zero' hj
    · by_cases hj : j < 512
      · rw [aValE_60 y _ _ hj]
        unfold cA
        rcases Nat.mod_two_eq_zero_or_one j with h | h
        · simp only [h, Fin.zero_eta, Matrix.cons_val_zero]
          exact bitA (MLDSA44.Native.ternaryBits_bool _).1
        · simp only [h, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
          exact bitA (MLDSA44.Native.ternaryBits_bool _).2
      · unfold aValE; rw [if_pos rfl]; exact dite_mem_zero' hj
    · by_cases hj : j < 6144
      · rw [aValE_63 y _ _ hj]
        unfold outputBits w1A
        exact bitA (Falcon512.HashCircuit.wiresOfByteVec_allBool _ _)
      · unfold aValE; rw [if_neg (by decide), if_pos rfl]; exact dite_mem_zero' hj
    · by_cases hj : j < 1024
      · rw [aValE_64 y _ _ hj]
        change ((MLDSA44.useHintSign _ _).toNat : (interp 0).K) ∈ _
        exact natm _
      · unfold aValE; rw [if_neg (by decide), if_neg (by decide)]; exact dite_mem_zero' hj
  · by_cases hj : j < 1024
    · obtain ⟨k, hk⟩ := aValE_digit_natCast y (interp 0).K hnd hd hj
      rw [hk]
      exact natm k
    · obtain ⟨h1, h2, -, -⟩ := MLDSA44.Emulated.aVal_digit_ne hnd hd
      unfold aValE
      rw [if_neg h1, if_neg h2]
      exact dite_mem_zero' hj

end Nodes

/-! ## The source program at the honest values -/

section Exec

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] [MldsaCarrierSelect program] [MldsaCarrierQuot program]
  [MldsaCarrierExec program]
  {F0 FH : FieldInterp} [RealizedProgram.PrimeCastField F0 pGold] [CarrierANode F0] [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout (CarrierAEmbed.emu program)

set_option hygiene false in
local notation "qD" => MldsaCarrierHonest.qD program

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MldsaHNodes FH]
  [hE : MldsaEmulatedHonest emu F0 FH]

theorem mem_castElt_of_eqA {a b : ℕ} (h : a = b) {S : String} {z : (interp a).K}
    (hz : z ∈ (interp a).node S) : (castElt z : (interp b).K) ∈ (interp b).node S := by
  subst h
  rwa [castElt_self]

/-- **An honest committed source value lies in its value's node.** -/
theorem honest_cell_mem (y : RingIn msgLen) {v : ℕ} (hv : v < program.values.length)
    (hp : program.privCellB v = true) (hsrc : program.IsSourceValue v)
    (j : ℕ) {S : String} (hS : (program.value v).node.map (·.name) = some S) :
    honestVal program F0 FH y v j ∈ (interp (program.valueField v)).node S := by
  have hcl := List.all_eq_true.1 (MldsaCarrierExec.cell_classes (program := program)) v
    (List.mem_range.2 hv)
  simp only [hp, hsrc, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, hS, Option.some.injEq, List.contains_iff_mem] at hcl
  rcases hcl with ⟨⟨hm, hf⟩, rfl⟩ | hcl
  · have hmem := honestVal_member (program := program) (F0 := F0) (FH := FH) y j
    have key : castElt (b := 0) (honestVal program F0 FH y v j) ∈ (interp 0).node "GF(p^1)" := by
      simp only [List.cons_append, List.mem_cons] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | hq
      · rw [hmem.1]
        split_ifs
        · exact specE_mem y j
        · exact zero_mem _
      · rw [hmem.2.1]
        split_ifs
        · exact specE_mem y _
        · exact zero_mem _
      · rw [hmem.2.2.1]; exact natCast_memA _
      · rw [hmem.2.2.2.1]; exact natCast_memA _
      · rw [hmem.2.2.2.2.1]
        split_ifs
        · exact qHonC_memA y _ _
        · exact zero_mem _
      · rw [hmem.2.2.2.2.2 v hq]; exact natCast_memA _
    have := mem_castElt_of_eqA (F0 := F0) (FH := FH) hf.symm key
    rwa [castElt_castElt_of_eq hf] at this
  · revert hcl
    rcases hh : hOf program v with _ | u
    · rcases ha : aOf program v with _ | u
      · simp
      · simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq, List.contains_iff_mem]
        rintro ⟨⟨hu, hf⟩, rfl⟩
        obtain ⟨huV, rfl⟩ := aOf_spec ha
        rw [honestVal_heldA y hu j]
        exact mem_castElt_of_eqA hf.symm (aValE_mem y MldsaEmulatedHonest.a_nodup hu j)
    · obtain ⟨huV, rfl⟩ := hOf_spec hh
      obtain ⟨-, -, hfu, -⟩ := (CarrierHEmbed.embedding (program := program)).vals u huV
      rw [honestVal_heldH y huV j]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Option.some.injEq,
        List.contains_iff_mem]
      rintro (⟨⟨hG, hf⟩, rfl⟩ | ⟨⟨hB, hf⟩, rfl⟩)
      · exact mem_castElt_of_eqA hfu.symm (hValCore_mem_gf16 y (hfu.symm.trans hf) hG j)
      · exact mem_castElt_of_eqA hfu.symm (hValCore_mem_bit y (hfu.symm.trans hf) hB j)

/-- **Every source predicate holds** at the source environment of the honest values, at a
statement holding the ring's carrier rows: the member's checks, the signature relation and its
quotient's range, domain `A`'s gadgets and domain `H`'s core through the renamings, and the
crossing (the realization's predicates are no source predicates, `MldsaCarrierExec.nonSource`). -/
theorem source_holds (y : RingIn msgLen) (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (π : (program.layout interp).Pads)
    (hx : RowsOf y.x x) {q : ℕ} (hq : q < program.predicates.length)
    (hs : program.inSource (program.predicate q) = true) :
    program.HoldsAt (program.srcEnv interp x (honestVal program F0 FH y) c π)
      (program.predicate q).body := by
  rcases MldsaCarrierExec.coverage (program := program) q hq with
    ⟨p, hp, rfl, hk⟩ | ⟨p, hp, rfl, hk⟩ | ho | hr
  · rw [← CarrierHEmbed.pred_held p hp]
    exact core_holds y x c π hk.1 hk.2
  · rw [← CarrierAEmbed.pred_held p hp]
    exact aSource_holds y x c π hk
  rotate_left
  · rw [MldsaCarrierExec.nonSource q hr] at hs
    cases hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h | h | h | h | h | h | h | h | h <;> subst h
  · exact select_honest y x c π hx
  · exact sig_row y x c π 0
  · exact sig_row y x c π 1
  · exact sig_row y x c π 2
  · exact sig_row y x c π 3
  · exact muBool_honest y x c π
  · exact idxBool_honest y x c π
  · exact qRange_holds y x c π
  · exact cross_holds y x c π

/-- **The source cross-field `equal`s read bits** at the source environment of the honest
values: every one crosses `ref 558` and `ref 95` (`MldsaCarrierExec.crossOperands`), which read bits
(`crossBits_honest`). -/
theorem source_crossBits (y : RingIn msgLen) (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (π : (program.layout interp).Pads) :
    program.CrossBitsAt interp (program.srcEnv interp x (honestVal program F0 FH y) c π) := by
  obtain ⟨hxb, hyb⟩ := crossBits_honest y x c π
  refine crossBitsAt_of_operands (MldsaCarrierExec.crossOperands (program := program))
    (fun i hi => ?_) (fun i hi => ?_)
  · rw [MldsaCarrierFront.lens.1] at hi
    unfold evalWith
    rw [MldsaCarrierFront.domains.2]
    exact hxb i hi
  · rw [MldsaCarrierExec.len95] at hi
    unfold evalWith
    rw [MldsaCarrierFront.domains.1]
    exact hyb i hi

variable (program F0 FH) in
/-- **The honest relation**: the program statement of an honest input is the frontend's statement
of its ring statement (`stmtOf`). -/
def relH : Set (program.Valuation interp × RingIn msgLen) :=
  {p | p.1 = stmtOf (program := program) (I := interp) p.2.x}

/-- **The frontend's statement lies within the declared bounds**: the keys' carrier rows lie below
`q` (`keyEntry_lt`). -/
theorem stmtBounded_stmtOf (x : RStmt msgLen) :
    program.StmtBounded interp (stmtOf (program := program) (I := interp) x) := by
  intro vN hvN i _
  rw [MldsaCarrierExec.ranges (program := program), List.mem_singleton] at hvN
  subst hvN
  refine ⟨_, keyEntry_lt (x.keyAt (i / 5120)) (i % 5120), ?_⟩
  rw [RealizedProgram.stmtRead_of_isStmtLeaf _
    (by rw [MldsaRingStmt.keysKind (program := program)]; rfl)]
  unfold stmtOf
  rw [if_pos rfl]
  exact castElt_natCast MldsaRingStmt.fields.1.symm _

variable (program F0 FH) in
/-- **The execution of an ML-DSA-44 ring carrier's source program**
(`RealizedProgram.SourceExecution`): at the frontend's statement of the ring statement, the honest
values `honestVal` read off by `execOf` (a value bound to its digits as their number), no late
value, no completeness event. The source program accepts (`source_holds`, the honest cells' nodes
`honest_cell_mem` at the honest roles `hR`, `source_crossBits`); no `mod_q` has the field form. -/
noncomputable def sourceExecution {PN : ℕ → List String} (hI : (interp).Registered program)
    (hL : (interp).Lawful program PN) {Gn : RealizedProgram.Gens}
    (R : program.CommittedFacts interp Gn) (hbc : program.BoundNoCopy)
    {nodes : List (ℕ × String)} {S : RealizedProgram.Structure} (hR : program.HonestRoles nodes S)
    (hO : OneNodes interp nodes) (hbit : (interp).BitNodes program)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false) :
    program.SourceExecution interp (relH (msgLen := msgLen) program F0 FH) where
  packFree _ _ _ _ _ := RealizedProgram.packFreeAt_of_noGamma hR.noGamma _
  stmtOf y := stmtOf (program := program) (I := interp) y.x
  stmt _ _ h := h
  val y := program.execOf interp (honestVal program F0 FH y)
  late _ _ := 0
  respects _ _ _ _ _ _ _ := rfl
  bad _ _ _ _ := False
  δ _ := 0
  badBound _ _ _ _ _ := by simp [IOP.probUniform]
  checks x y _ := by
    intro m hm
    rw [MldsaCarrierExec.checks (program := program)] at hm
    cases hm
  bounded x y h := by
    rw [show x = stmtOf (program := program) (I := interp) y.x from h]
    exact stmtBounded_stmtOf y.x
  accepting x y hx c _ := by
    rw [show x = stmtOf (program := program) (I := interp) y.x from hx]
    refine sourceAcceptingAtC_of_srcEnv (l := 0) (π := 0) MldsaCarrierExec.wf hI hL R hbc
      hR.kprivTyped (hR.boundOneMem hO) ?_ ?_ <;> rw [RealizedProgram.srcEnvL_zero]
    · exact hR.sourceSatAt hbit (fun _ hv hp hs j _ hS => honest_cell_mem y hv hp hs j hS)
        fun p hp hs => by
          obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
          exact source_holds y _ c 0 (rowsOf_stmtOf y.x) hq hs
    · exact source_crossBits y _ c 0
  fieldEqs _ _ _ _ _ := RealizedProgram.fieldEqsAt_of_none hff _

/-- **The execution of an ML-DSA-44 ring carrier's source program has no completeness error.** -/
theorem sourceExecution_δ {PN : ℕ → List String} (hI : (interp).Registered program)
    (hL : (interp).Lawful program PN) {Gn : RealizedProgram.Gens}
    (R : program.CommittedFacts interp Gn) (hbc : program.BoundNoCopy)
    {nodes : List (ℕ × String)} {S : RealizedProgram.Structure} (hR : program.HonestRoles nodes S)
    (hO : OneNodes interp nodes) (hbit : (interp).BitNodes program)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false) :
    (sourceExecution (msgLen := msgLen) program F0 FH hI hL R hbc hR hO hbit hff).δ = 0 := rfl

end Exec

end GordieHowe.MLDSA44.Ring.Carrier
