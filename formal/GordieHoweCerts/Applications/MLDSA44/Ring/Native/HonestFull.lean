-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestCross
public import GordieHoweCerts.Applications.MLDSA44.Native.HonestFull

@[expose] public section

/-!
# GordieHowe: the honest execution of the native ML-DSA-44 ring programs

The execution of the source program of a native ML-DSA-44 ring program
(`GordieHowe.RealizedProgram.SourceExecution`), generic in the program through its decided facts
(`MldsaRingHonest`, `MldsaRingExec`), from which `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` builds the
honest strategy:

* **The honest relation** (`relH`): the program statement of an honest input
  (`GordieHowe.MLDSA44.Ring.RingIn`: a ring statement and a witness of the ring relation) is the
  frontend's statement of its ring statement (`stmtOf`), which holds the ring's rows (`RowsOf`,
  `rowsOf_stmtOf`).
* **The honest values in their nodes** (`hValCore_mem_gf16`, `hValCore_mem_bit`, `aValR_mem`,
  `honest_cell_mem`), from which the honest roles put the node-typed values in their types
  (`GordieHowe.RealizedProgram.HonestRoles.sourceSatAt`).
* **Every source predicate holds** (`source_holds`): domain `H`'s core and domain `A`'s gadgets
  through the renaming (`core_holds`, `aSource_holds`), the signature relation (`sig_holds`), the
  member's checks (`select_honest`, `idxBool_honest`, `muBool_honest`) and the crossing
  (`cross_holds`), whose operands read bits (`crossBits_honest`).
* **The execution** (`sourceExecution`): the honest values read off by `execOf`, no late value,
  no completeness event (`δ = 0`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open MLDSA44.NativeAlgebraCircuit (outputBits)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

set_option hygiene false in
local notation "ringV" => MldsaRingEmbed.V program

set_option hygiene false in
local notation "ringR" => MldsaRingEmbed.R program

set_option hygiene false in
local notation "predMap" => MldsaRingEmbed.pred program

set_option hygiene false in
local notation "vA" => MldsaRandomPoint.aHat program

set_option hygiene false in
local notation "vT" => MldsaRandomPoint.t1 program

set_option hygiene false in
local notation "vI" => (TableSelect.shape program).idx

set_option hygiene false in
local notation "vMu" => MldsaRingFront.muA program

set_option hygiene false in
local notation "vQ" => MldsaRandomPoint.q program

/-- **Value `u` of the native program is a word of domain `H`'s core** (`GF(2^16)`): a core round's
words, `w1`'s or `μ`'s words, the threshold words or a memory cell. -/
def natGF16B (u : ℕ) : Bool := coreHashB u || [557, 560, 562, 563, 564, 565].contains u

/-- **The realization's predicates of a native ring program**: `mac.A`, the norm range's top row,
the MAC blind's Booleanity, the MAC's low, high and no-wrap rows and its tail `mac`. -/
def realizationPreds : List ℕ := [8, 9, 16, 21, 22, 23, 247]

/-- **The program facts of a native ML-DSA-44 ring program's execution** (decided per program):
`249` predicates, the source predicates (the realization's `8`, `9`, `16`, `21 … 23`, `247` are
none), the table's predicates `0` and `11`, no statement check or bound, the committed source
values' classes and the node-typed values'. -/
class MldsaRingExec (program : RealizedProgram) [MldsaRingEmbed program] [MldsaRingRelation program]
    [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program]
    [MldsaRingHonest program] : Prop where
  /-- The program is well formed. -/
  wf : program.WellFormed
  /-- The realization's predicates are no source predicates. -/
  nonSource : ∀ q ∈ realizationPreds, program.inSource (program.predicate q) = false
  /-- **Every predicate is a held one, one of the ring program's own or a realization's**: the
  ring predicate of a held native predicate of domain `H`'s core (`corePredLo … hPredHi`) or of
  `aSource`; the
  table's selection, the signature relation's four rows, `member.mu`'s Booleanity, the index
  bits' check or the crossing; or one of `realizationPreds`. -/
  coverage : ∀ q < program.predicates.length,
    (∃ p ∈ MldsaRingEmbed.held program, p.2 = q ∧ ((corePredLo ≤ p.1 ∧ p.1 ≤ hPredHi) ∨ p.1 ∈ aSource)) ∨
      q ∈ [(TableSelect.shape program).pred, MldsaRandomPoint.rel0 program,
        MldsaRandomPoint.rel0 program + 1, MldsaRandomPoint.rel0 program + 2,
        MldsaRandomPoint.rel0 program + 3, MldsaRingFront.muBoolPred program,
        (TableSelect.shape program).idxPred, MldsaRingFront.crossPred program] ∨
      q ∈ realizationPreds
  /-- The statement has no member checks. -/
  checks : program.statement.checks = []
  /-- The program declares no statement bound. -/
  noBounds : program.declaredRanges = []
  /-- The committed source cells' classes. -/
  cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      ([vA, vT, vMu, vI, vQ].contains v && program.valueField v == 0 &&
        (program.value v).node.map (·.name) == some "GF(p^1)") ||
      (decide (MldsaRingHonest.inv program v ∈ ringV) &&
        (σ).val (MldsaRingHonest.inv program v) == v &&
        ((Native.AValues.contains (MldsaRingHonest.inv program v) && program.valueField v == 0 &&
            (program.value v).node.map (·.name) == some "GF(p^1)") ||
          (natGF16B (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "GF(2^16)") ||
          ([556, 561].contains (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "bit")))) = true

/-! ## The honest values in their nodes -/

section Nodes

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [HField FH] [MldsaHConsts program FH]
  [MldsaHNativeData FH] [MldsaHNodes FH] (y : RingIn msgLen)

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option maxRecDepth 8192 in
/-- **SampleInBall's honest memory cells lie in `GF(2^16)`.** -/
theorem memFR_mem {v : ℕ} (n : ℕ) (hv : v ∈ [560, 562, 563, 564, 565]) :
    memFR program F0 FH y v n ∈ (interp 1).node "GF(2^16)" := by
  have hθ := (samM program F0 FH).θ_mem
  have zero : (0 : (interp 1).K) ∈ (interp 1).node "GF(2^16)" := zero_mem _
  have sel : ∀ z ∈ (samM program F0 FH).field.E, z ∈ (interp 1).node "GF(2^16)" := by
    rw [samM_field]
    exact MldsaHNodes.node_of_sel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold memFR honestMemWR
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · rw [if_pos rfl]
    split_ifs
    · exact sel _ (MemoryShuffle.honestWit_read_value_mem _ _ _ _ hθ _)
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    split_ifs
    · exact sel _ (MemoryShuffle.honestWit_cEnc_mem _ _ _ _ hθ _)
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    split_ifs
    · exact sel _ (MemoryShuffle.honestWit_finalOrigin_mem _ _ _ _ _)
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    split_ifs
    · refine sel _ ?_
      unfold MemoryShuffle.unit
      refine Subfield.add_mem _ (Subfield.one_mem _) (Subfield.mul_mem _
        (Subfield.add_mem _ hθ (Subfield.one_mem _)) ?_)
      change (if sgBR program F0 FH y _ then 1 else 0) ∈ _
      split_ifs
      · exact Subfield.one_mem _
      · exact Subfield.zero_mem _
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
    split_ifs
    · refine sel _ ?_
      unfold SampleInBall.originOf SelectionField.embedBits
      refine Subfield.sum_mem _ fun k _ => Subfield.mul_mem _ ?_ (SelectionField.e_mem _ _)
      exact bit_mem_subfield (honestWit_origin_bool _ _ _ _ _ _)
    · exact zero

set_option maxRecDepth 8192 in
/-- **The core's honest words lie in `GF(2^16)`**: the core rounds' words, `w1`'s and `μ`'s
words, the threshold words and the memory cells. -/
theorem hValCore_mem_gf16 {u : ℕ} (hf : program.valueField u = 1) (hu : natGF16B u = true)
    (j : ℕ) : hValCore program F0 FH y u j ∈ (interp (program.valueField u)).node "GF(2^16)" := by
  obtain ⟨n7, n8, nm⟩ := h_classes
  have pack := MldsaHNodes.pack_mem (FH := FH)
  unfold natGF16B at hu
  simp only [Bool.or_eq_true, List.contains_iff_mem] at hu
  rcases hu with hc | hm
  · have hH : MLDSA44.IsHashValue u := by
      rcases coreHashB_cases hc with rfl | rfl | ⟨p, -, t, rfl⟩
      · unfold MLDSA44.IsHashValue; simp
      · unfold MLDSA44.IsHashValue; simp
      · unfold MLDSA44.IsHashValue; simp [wordsOwner_checks.1 p t]
    unfold hValCore hashValCore
    rw [if_pos hH]
    split_ifs
    · exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · split
      · exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
      · exact zero_mem _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | hm
    · unfold hValCore
      rw [if_neg n8, if_neg (by decide), if_pos rfl]
      exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · have hm' : u ∈ [560, 561, 562, 563, 564, 565] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        omega
      unfold hValCore
      rw [if_neg (nm u hm'), if_neg (by rintro rfl; simp at hm),
        if_neg (by rintro rfl; simp at hm), if_pos hm']
      exact mem_castElt_of_eqH (a := 1) hf.symm (memFR_mem y j (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        omega))

set_option maxRecDepth 8192 in
/-- **The core's honest bits lie in the node `bit`**: the selected bytes' bits and the read
origins' bits. -/
theorem hValCore_mem_bit {u : ℕ} (hf : program.valueField u = 1) (hu : u ∈ [556, 561]) (j : ℕ) :
    hValCore program F0 FH y u j ∈ (interp (program.valueField u)).node "bit" := by
  obtain ⟨n7, -, nm⟩ := h_classes
  have bit : ∀ z : (interp 1).K, z = 0 ∨ z = 1 → z ∈ (interp 1).node "bit" :=
    fun z h => (MldsaHNodes.bit_iff (FH := FH) z).2 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · unfold hValCore
    rw [if_neg n7, if_pos rfl]
    refine mem_castElt_of_eqH (a := 1) hf.symm (bit _ ?_)
    unfold jFR
    split_ifs
    · exact constBit_bool _ _
    · exact Or.inl rfl
  · unfold hValCore
    rw [if_neg (nm 561 (by simp)), if_neg (by decide), if_neg (by decide), if_pos (by simp)]
    refine mem_castElt_of_eqH (a := 1) hf.symm (bit _ ?_)
    unfold memFR
    rw [if_neg (by decide), if_pos rfl]
    split_ifs
    · unfold honestMemWR
      exact honestWit_origin_bool _ _ _ _ _ _
    · exact Or.inl rfl

end Nodes

section ANodes

variable {F0 FH : FieldInterp} [QField F0] (y : RingIn msgLen)

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **Domain `A`'s honest values lie in `F_q`.** -/
theorem aValR_mem {u : ℕ} (hu : u ∈ Native.AValues) (j : ℕ) :
    aValR y F0.K u j ∈ (interp 0).node "GF(p^1)" := by
  have natm := Native.natCast_mem_prime (F0 := F0) (FH := FH)
  have bitA := fun {z : (interp 0).K} (h : z = 0 ∨ z = 1) => Native.bitA_mem (F0 := F0) (FH := FH) h
  by_cases h59 : u = 59
  · subst h59
    by_cases hj : j < 512
    · rw [aValR_59 y _ hj]
      unfold cA
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · simp only [h, Fin.zero_eta, Matrix.cons_val_zero]
        exact bitA (MLDSA44.Native.ternaryBits_bool _).1
      · simp only [h, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        exact bitA (MLDSA44.Native.ternaryBits_bool _).2
    · unfold aValR; rw [if_pos rfl]; exact Native.dite_mem_zero hj
  by_cases h62 : u = 62
  · subst h62
    by_cases hj : j < 6144
    · rw [aValR_62 y _ hj]
      unfold outputBits w1A
      exact bitA (Falcon512.HashCircuit.wiresOfByteVec_allBool _ _)
    · unfold aValR; rw [if_neg (by decide), if_pos rfl]; exact Native.dite_mem_zero hj
  by_cases hj : j < 1024
  · simp only [Native.AValues, List.mem_cons, List.not_mem_nil, or_false] at hu
    have d := aValR_digits y F0.K hj
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [aValR_58 y _ hj]; exact natm _
    · exact absurd rfl h59
    · rw [aValR_60 y _ hj]; exact natm _
    · exact absurd rfl h62
    · rw [aValR_63 y _ hj]
      change ((MLDSA44.useHintSign _ _).toNat : F0.K) ∈ _
      exact natm _
    · rw [d.1]; exact natm _
    · rw [d.2.1]; exact natm _
    · rw [d.2.2.1]; exact natm _
    · rw [d.2.2.2.1]; exact natm _
    · rw [d.2.2.2.2.1]; exact natm _
    · rw [d.2.2.2.2.2]; exact natm _
  · unfold aValR
    rw [if_neg h59, if_neg h62]
    exact Native.dite_mem_zero hj

end ANodes

/-! ## The source program at the honest values -/

section Exec

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]
  [MldsaRingExec program]
  {F0 FH : FieldInterp} [QField F0] [HField FH] [Native.MldsaAAlgebra nat] [hN : Native.MldsaNativeHonest nat F0 FH]
  [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MldsaHNativeData FH] [MldsaHNodes FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The honest quotients lie in `F_q`.** -/
theorem qHon_mem_prime (y : RingIn msgLen) (i t : ℕ) :
    qHon y ((interp 0).decode 1753) i t ∈ (interp 0).node "GF(p^1)" :=
  (QField.node_prime (F0 := F0) _).2 (qHon_mem y _ (by
    rw [decode_psi (F0 := F0) (FH := FH)]
    exact natCast_mem _ _) _ _)

/-- **An honest committed source value lies in its value's node.** -/
theorem honest_cell_mem (y : RingIn msgLen) {v : ℕ} (hv : v < program.values.length)
    (hp : program.privCellB v = true) (hsrc : program.IsSourceValue v)
    (j : ℕ) {S : String} (hS : (program.value v).node.map (·.name) = some S) :
    honestVal program F0 FH y v j ∈ (interp (program.valueField v)).node S := by
  have hcl := List.all_eq_true.1 (MldsaRingExec.cell_classes (program := program)) v
    (List.mem_range.2 hv)
  simp only [hp, hsrc, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, hS, Option.some.injEq, List.contains_iff_mem,
    decide_eq_true_eq] at hcl
  rcases hcl with ⟨⟨hm, hf⟩, rfl⟩ | ⟨⟨hinv, heq⟩, hcls⟩
  · unfold honestVal
    split_ifs <;> first
      | exact Native.mem_castElt_of_eq hf.symm (Native.natCast_mem_prime (F0 := F0) (FH := FH) _)
      | exact Native.mem_castElt_of_eq hf.symm
          (Nat.cast_zero (R := (interp 0).K) ▸ Native.natCast_mem_prime (F0 := F0) (FH := FH) 0)
      | exact Native.mem_castElt_of_eq hf.symm (qHon_mem_prime y _ _)
      | (exfalso; simp_all)
  · obtain ⟨u, hu, rfl⟩ : ∃ u ∈ ringV, (σ).val u = v := ⟨_, hinv, heq⟩
    rw [MldsaRingHonest.inv_val u hu] at hcls
    obtain ⟨-, -, hfu, -⟩ := (MldsaRingEmbed.embedding (program := program)).vals u hu
    rw [honestVal_held y hu j]
    rcases hcls with (⟨⟨hA, hf⟩, rfl⟩ | ⟨⟨hG, hf⟩, rfl⟩) | ⟨⟨hB, hf⟩, rfl⟩
    · refine Native.mem_castElt_of_eq hfu.symm ?_
      unfold natVal
      rw [if_pos hA]
      exact Native.mem_castElt_of_eq (hf.symm.trans hfu) (aValR_mem y hA j)
    · have hnA : u ∉ Native.AValues := fun h => by
        have := (Native.MldsaNativeHonest.a_cells (program := nat) u h).2
        omega
      refine Native.mem_castElt_of_eq hfu.symm ?_
      unfold natVal
      rw [if_neg hnA]
      exact hValCore_mem_gf16 y (hfu.symm.trans hf) hG j
    · have hnA : u ∉ Native.AValues := fun h => by
        have := (Native.MldsaNativeHonest.a_cells (program := nat) u h).2
        omega
      refine Native.mem_castElt_of_eq hfu.symm ?_
      unfold natVal
      rw [if_neg hnA]
      exact hValCore_mem_bit y (hfu.symm.trans hf) hB j

/-- **Every source predicate holds** at the source environment of the honest values, at a
statement holding the ring's rows: domain `A`'s gadgets and domain `H`'s core through the
renaming, the member's checks, the signature relation and the crossing; the realization's
predicates are no source predicates (`MldsaRingExec.coverage`, `MldsaRingExec.nonSource`). -/
theorem source_holds (y : RingIn msgLen) (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (π : (program.layout interp).Pads)
    (hx : RowsOf y.x x) {q : ℕ} (hq : q < program.predicates.length)
    (hs : program.inSource (program.predicate q) = true) :
    program.HoldsAt (program.srcEnv interp x (honestVal program F0 FH y) c π)
      (program.predicate q).body := by
  rcases MldsaRingExec.coverage (program := program) q hq with ⟨p, hp, rfl, hk | hk⟩ | ho | hr
  · rw [← MldsaRingEmbed.pred_held p hp]
    exact core_holds y x c π hk.1 hk.2
  · rw [← MldsaRingEmbed.pred_held p hp]
    exact aSource_holds y x c π hk
  rotate_left
  · rw [MldsaRingExec.nonSource q hr] at hs
    cases hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h | h | h | h | h | h | h | h <;> subst h
  · exact select_honest y x c π hx
  · exact sig_holds y x c π (by simp)
  · exact sig_holds y x c π (by simp)
  · exact sig_holds y x c π (by simp)
  · exact sig_holds y x c π (by simp)
  · exact muBool_honest y x c π
  · exact idxBool_honest y x c π
  · exact cross_holds y x c π

/-- **The source cross-field `equal`s read bits** at the source environment of the honest
values: every one crosses `ref 513` and `ref 50` (`MldsaRingHonest.crossOperands`), which read bits
(`crossBits_honest`). -/
theorem source_crossBits (y : RingIn msgLen) (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (π : (program.layout interp).Pads) :
    program.CrossBitsAt interp (program.srcEnv interp x (honestVal program F0 FH y) c π) := by
  obtain ⟨hxb, hyb⟩ := crossBits_honest y x c π
  refine crossBitsAt_of_operands (MldsaRingHonest.crossOperands (program := program))
    (fun i hi => ?_) (fun i hi => ?_)
  · rw [MldsaRingFront.lens.1] at hi
    unfold evalWith
    rw [MldsaRingFront.domains.2]
    exact hxb i hi
  · rw [MldsaRingHonest.len50] at hi
    unfold evalWith
    rw [MldsaRingFront.domains.1]
    exact hyb i hi

variable (program F0 FH) in
/-- **The honest relation**: the program statement of an honest input is the frontend's statement
of its ring statement (`stmtOf`). -/
def relH : Set (program.Valuation interp × RingIn msgLen) :=
  {p | p.1 = stmtOf (program := program) (I := interp) p.2.x}

variable (program F0 FH) in
/-- **The execution of a native ML-DSA-44 ring program's source program**
(`RealizedProgram.SourceExecution`): at the frontend's statement of the ring statement, the honest
values `honestVal` read off by `execOf` (a value bound to its digits as their number), no late
value, no completeness event. The source program accepts (`source_holds`, the honest cells' nodes
`honest_cell_mem` at the honest roles `hR`, `source_crossBits`); no `mod_q` has the field form. -/
noncomputable def sourceExecution {PN : ℕ → List String} (hI : (interp).Registered program)
    (hL : (interp).Lawful program PN) {Gn : RealizedProgram.Gens}
    (R : program.CommittedFacts interp Gn) (hbc : program.BoundNoCopy)
    {L : List (ℕ × String)} {S : RealizedProgram.Structure} (hR : program.HonestRoles L S)
    (hO : OneNodes interp L) (hbit : (interp).BitNodes program)
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
    rw [MldsaRingExec.checks (program := program)] at hm
    cases hm
  bounded x _ _ := RealizedProgram.stmtBounded_of_nil MldsaRingExec.noBounds x
  accepting x y hx c _ := by
    rw [show x = stmtOf (program := program) (I := interp) y.x from hx]
    refine sourceAcceptingAtC_of_srcEnv (l := 0) (π := 0) MldsaRingExec.wf hI hL R hbc
      hR.kprivTyped (hR.boundOneMem hO) ?_ ?_ <;> rw [RealizedProgram.srcEnvL_zero]
    · exact hR.sourceSatAt hbit (fun _ hv hp hs j _ hS => honest_cell_mem y hv hp hs j hS)
        fun p hp hs => by
          obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
          exact source_holds y _ c 0 (rowsOf_stmtOf y.x) hq hs
    · exact source_crossBits y _ c 0
  fieldEqs _ _ _ _ _ := RealizedProgram.fieldEqsAt_of_none hff _

/-- **The execution of a native ML-DSA-44 ring program's source program has no completeness
error.** -/
theorem sourceExecution_δ {PN : ℕ → List String} (hI : (interp).Registered program)
    (hL : (interp).Lawful program PN) {Gn : RealizedProgram.Gens}
    (R : program.CommittedFacts interp Gn) (hbc : program.BoundNoCopy)
    {L : List (ℕ × String)} {S : RealizedProgram.Structure} (hR : program.HonestRoles L S)
    (hO : OneNodes interp L) (hbit : (interp).BitNodes program)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false) :
    (sourceExecution (msgLen := msgLen) program F0 FH hI hL R hbc hR hO hbit hff).δ = 0 := rfl

end Exec

end GordieHowe.MLDSA44.Ring.Native
