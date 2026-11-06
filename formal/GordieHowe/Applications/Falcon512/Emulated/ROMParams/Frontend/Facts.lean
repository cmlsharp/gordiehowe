-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Basic
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Structure
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Plan
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Certified
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.ShapeFacts
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.HashShapeFacts
public import GordieHowe.Language.Library.Select

@[expose] public section

/-!
# GordieHowe frontend: the program facts of `Falcon512.Emulated.ROMParams`

The program facts the Falcon frontend reads
(`FalconHBase`, `FalconACore`, decided on the tables of
`GordieHowe.Generated.Falcon512.Emulated.ROMParams.Program.program`, export `5d9fe0d5`) and the
selection's labels in `GF(2^128)` (`FalconHConsts program gf128`, `FalconSelField program gf128
gold2`: entry `j` of the constant `39` is `g^j`, checked in the spread representation
`gf2_128Exec`, `gpow_chain`, `gN_chain`). Domain `H` of the emulated program has the native
program's numbering, so these are the native program's facts at the emulated program; domain `A`
holds `c_A` and `s2` at `595` and `596`, one id later than the native program, after
`key.coefficients` (`594`).
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open Generated.Falcon512.Emulated.ROMParams.Program (program)
open Generated.Falcon512.Emulated.ROMParams.ShapeFacts
open RealizedProgram
open HashShapeFacts
open GF2_128Exec

/-- The values the extractor reads read nothing from the run (`RealizedProgram.nodeReads`). -/
theorem srcReads_nil : ∀ v ∈ [45, 46, 47, 589, 595, 596],
    program.nodeReads program.fuel v = [] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact nodeReads_of_priv value_nonce_kind _
  · exact nodeReads_of_priv value_message_kind _
  · exact nodeReads_of_priv value_message_2ein_5fmessage_kind _
  · exact nodeReads_of_bits_priv value_h2p_2eselect_2eraw_kind value_h2p_2eselect_2eraw_2ewords_kind _
  · exact nodeReads_of_priv value_crossing_2ec_5fA_kind _
  · exact nodeReads_of_priv value_s2_kind _

/-- `statement.hhat` is a value of field `1`. -/
theorem hhatField : program.valueField 593 = 1 := valueShape_field value_statement_2ehhat_header.2

/-- The selection's predicates are `h2p.select.start`, `.step`, `.done` and `.route`, source predicates. -/
theorem selectPreds : ∀ p ∈ [270, 271, 272, 273],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true := by
  intro p hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨predicate_h2p_2eselect_2estart_role.1, program.inSource_of_source predicate_h2p_2eselect_2estart_role.2⟩
  · exact ⟨predicate_h2p_2eselect_2estep_role.1, program.inSource_of_source predicate_h2p_2eselect_2estep_role.2⟩
  · exact ⟨predicate_h2p_2eselect_2edone_role.1, program.inSource_of_source predicate_h2p_2eselect_2edone_role.2⟩
  · exact ⟨predicate_h2p_2eselect_2eroute_role.1, program.inSource_of_source predicate_h2p_2eselect_2eroute_role.2⟩

/-- The selection has the first-`n` shape at `(S, n, w) = (717, 512, 16)`. -/
theorem selectShape_eq :
    program.selectShape? 717 512 16 270 271 272 273 = some selShape := by
  have hstream : program.expr 537 = _ := expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e0_eq
  have hs : ∃ sup, program.bitSupport? 27 (program.expr 537) = some sup ∧ 717 * 16 ≤ sup.length := by
    rw [hstream]
    simp only [RealizedProgram.bitSupport?, RealizedProgram.bitCat?,
      isBitView_of_kind value_h2p_2eshake_2estate_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep1_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep2_kind,
      isBitView_of_kind value_h2p_2eshake_2eout_2ep3_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep4_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep5_kind,
      isBitView_of_kind value_h2p_2eshake_2eout_2ep6_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep7_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep8_kind,
      isBitView_of_kind value_h2p_2eshake_2eout_2ep9_kind, isBitView_of_kind value_h2p_2eshake_2eout_2ep10_kind, ite_true, Option.map_some,
      valueShape_size value_h2p_2eshake_2estate_header.2, valueShape_size value_h2p_2eshake_2eout_2ep1_header.2, valueShape_size value_h2p_2eshake_2eout_2ep2_header.2, valueShape_size value_h2p_2eshake_2eout_2ep3_header.2, valueShape_size value_h2p_2eshake_2eout_2ep4_header.2, valueShape_size value_h2p_2eshake_2eout_2ep5_header.2,
      valueShape_size value_h2p_2eshake_2eout_2ep6_header.2, valueShape_size value_h2p_2eshake_2eout_2ep7_header.2, valueShape_size value_h2p_2eshake_2eout_2ep8_header.2, valueShape_size value_h2p_2eshake_2eout_2ep9_header.2, valueShape_size value_h2p_2eshake_2eout_2ep10_header.2]
    exact ⟨_, rfl, by decide +kernel⟩
  have e29 : Generated.Falcon512.Emulated.ROMParams.Program.idx29 = List.replicate 717 (0, 1, 16) := by decide +kernel
  have e38 : Generated.Falcon512.Emulated.ROMParams.Program.idx38 = List.replicate 512 (0, 1, 16) := by decide +kernel
  exact selectShape?_of_selectMatches
    { start := predicate_h2p_2eselect_2estart_body
      step := predicate_h2p_2eselect_2estep_body
      done := predicate_h2p_2eselect_2edone_body
      route := by
        obtain ⟨t, h⟩ := predicate_h2p_2eselect_2eroute_body
        rw [e29, e38] at h
        exact ⟨t, h⟩
      acc := expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_eq
      lt := by
        have h := expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq
        rw [e29] at h
        exact h
      stream := hs
      acc_lt := expr_lt_of_ne_default (by rw [expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_eq]; intro hc; cases hc)
      lt_lt := expr_lt_of_ne_default (by rw [expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq]; intro hc; cases hc)
      stream_lt := expr_lt_of_ne_default (by rw [expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e0_eq]; intro hc; cases hc)
      raw := isBitView_of_kind value_h2p_2eselect_2eraw_kind
      zeroConst := by
        simp only [isZeroConst, isConstant_of_kind value_h2p_2eshake_2epadding_2emax_2econstant_2eright_kind, constEntries_of_kind value_h2p_2eshake_2epadding_2emax_2econstant_2eright_kind]
        decide
      full := by
        simp only [isNodeBit, value_h2p_2eselect_2efull_header.1, value_h2p_2eselect_2efull_type.2, valueShape_typeSource value_h2p_2eselect_2efull_header.2,
          valueShape_size value_h2p_2eselect_2efull_header.2]
        have hsrc : program.IsSourceValue 591 := valueShape_role value_h2p_2eselect_2efull_header.2
        simp [hsrc]
      consts := by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact isConstant_of_kind value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_kind
        · exact isConstant_of_kind value_h2p_2eshake_2epadding_2emax_2econstant_2eright_kind
        · exact isConstant_of_kind value_h2p_2eselect_2estep_2econstant_2eleft_2esecond_2esecond_2esecond_2efirst_kind
        · exact isConstant_of_kind value_h2p_2eselect_2estep_2econstant_2eright_kind
        · exact isConstant_of_kind value_h2p_2eselect_2edone_2econstant_2eleft_2esecond_2esecond_2efirst_kind
        · exact isConstant_of_kind value_h2p_2eselect_2edone_2econstant_2eright_kind
        · exact isConstant_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2esecond_2efirst_2efirst_2esecond_2efirst_kind
        · exact isConstant_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind
        · exact isConstant_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2esecond_2esecond_2efirst_kind
        · exact isConstant_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e1_2efirst_kind
    }

/-- Domain `H` has field `0`. -/
theorem domainField0 : program.domainField 0 = 0 :=
  Generated.Falcon512.Emulated.ROMParams.conditions.fieldTable.domainField_eq 0 (by decide)

/-- Domain `A` has field `1`. -/
theorem domainField1 : program.domainField 1 = 1 :=
  Generated.Falcon512.Emulated.ROMParams.conditions.fieldTable.domainField_eq 1 (by decide)

/-- The selection's constants are values of domain `H`. -/
theorem selConstField :
    ∀ v ∈ [25, 27, 35, 37, 33, 34, 36, 38, 39, 32], program.valueField v = 0 := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valueShape_field value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_header.2
  · exact valueShape_field value_h2p_2eshake_2epadding_2emax_2econstant_2eright_header.2
  · exact valueShape_field value_h2p_2eselect_2estep_2econstant_2eright_header.2
  · exact valueShape_field value_h2p_2eselect_2edone_2econstant_2eright_header.2
  · exact valueShape_field value_h2p_2eselect_2eroute_2econstant_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2esecond_2esecond_2efirst_header.2
  · exact valueShape_field value_h2p_2eselect_2estep_2econstant_2eleft_2esecond_2esecond_2esecond_2efirst_header.2
  · exact valueShape_field value_h2p_2eselect_2edone_2econstant_2eleft_2esecond_2esecond_2efirst_header.2
  · exact valueShape_field value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2esecond_2efirst_2efirst_2esecond_2efirst_header.2
  · exact valueShape_field value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_header.2
  · exact valueShape_field value_h2p_2eselect_2eroute_2econstant_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e1_2efirst_header.2

/-- The entries of the selection's constants other than the labels. -/
theorem const_entries :
    (program.constEntries 39).getD 0 0 = 1 ∧ (program.constEntries 25).getD 0 0 = 1 ∧
    (program.constEntries 27).getD 0 0 = 0 ∧
    (∀ i < 716, (program.constEntries 35).getD i 0 = 0) ∧
    (∀ t < 205, (program.constEntries 37).getD t 0 = 0) ∧
    (∀ t < 205, (program.constEntries 33).getD t 0 = 1) ∧
    (program.constEntries 34).getD 0 0 = (program.constEntries 39).getD 1 0 ∧
    (∀ u < 16, (program.constEntries 38).getD u 0 = (program.constEntries 39).getD u 0) ∧
    (∀ u < 16, (program.constEntries 32).getD u 0 = 61445 / 2 ^ u % 2) := by
  rw [constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind, constEntries_of_kind value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_kind, constEntries_of_kind value_h2p_2eshake_2epadding_2emax_2econstant_2eright_kind, constEntries_of_kind value_h2p_2eselect_2estep_2econstant_2eright_kind, constEntries_of_kind value_h2p_2eselect_2edone_2econstant_2eright_kind, constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2esecond_2esecond_2efirst_kind, constEntries_of_kind value_h2p_2eselect_2estep_2econstant_2eleft_2esecond_2esecond_2esecond_2efirst_kind, constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2esecond_2efirst_2efirst_2esecond_2efirst_kind, constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e1_2efirst_kind]
  decide +kernel

/-- `δ`'s field is its challenge's. -/
theorem deltaField : program.chalField 0 = program.valueField 592 :=
  challenge_h2p_2eselect_2edelta_full.2.2.1.trans (valueShape_field value_h2p_2eselect_2edelta_header.2).symm

/-- The selection's committed values read nothing from the run. -/
theorem selReads_nil :
    ∀ v ∈ 590 :: 591 :: 589 :: program.exprNodes (.ref 537),
    program.nodeReads program.fuel v = [] := by
  intro v hv
  rw [exprNodes_ref_of_refs_nil (expr_lt_of_ne_default (by rw [expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e0_eq]; intro hc; cases hc))
    expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e0_eq rfl] at hv
  change v ∈ [590, 591, 589, 97, 146, 195, 244, 293, 342, 391, 440, 489, 538, 587] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nodeReads_of_priv value_h2p_2eselect_2ecount_kind _
  · exact nodeReads_of_priv value_h2p_2eselect_2efull_kind _
  · exact nodeReads_of_bits_priv value_h2p_2eselect_2eraw_kind value_h2p_2eselect_2eraw_2ewords_kind _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2estate_kind value_h2p_2eshake_2estate_2ewords_kind _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep1_kind (word_facts 1 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep2_kind (word_facts 2 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep3_kind (word_facts 3 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep4_kind (word_facts 4 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep5_kind (word_facts 5 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep6_kind (word_facts 6 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep7_kind (word_facts 7 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep8_kind (word_facts 8 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep9_kind (word_facts 9 23).2.1 _
  · exact nodeReads_of_bits_priv value_h2p_2eshake_2eout_2ep10_kind (word_facts 10 23).2.1 _

/-- Challenge `0` is full, of one coordinate, in field `0`. -/
theorem chal0 :
    (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧
    program.chalField 0 = 0 :=
  ⟨challenge_h2p_2eselect_2edelta_full.2.2.2, challenge_h2p_2eselect_2edelta_full.2.1,
    challenge_h2p_2eselect_2edelta_full.2.2.1⟩

/-- `select.raw` is a bit view; it and `c_A` have `8192` coordinates. -/
theorem raw_facts :
    program.isBitView 589 = true ∧ (program.value 589).size = 8192 ∧
    (program.value 595).size = 8192 :=
  ⟨isBitView_of_kind value_h2p_2eselect_2eraw_kind, valueShape_size value_h2p_2eselect_2eraw_header.2, valueShape_size value_crossing_2ec_5fA_header.2⟩

/-- The member check `falcon_key_canonical [12289]` of `hhat`. -/
theorem hhatCheck :
    RealizedProgram.MemberCheck.mk "hhat" 0 1024 "falcon_key_canonical" [12289] ∈
    program.statement.checks := by
  rw [statement_checks]
  exact List.mem_singleton.2 rfl

/-- `hhat` is value `593`. -/
theorem hhatValue : program.memberValue? "hhat" = some 593 := by
  refine RealizedProgram.memberValue?_of_memberValuesB (m := ⟨"hhat", 0, 1024, "falcon_key_canonical", [12289]⟩)
    (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Emulated.ROMParams.programOk) (k := 0) ?_ ?_
  · rw [statement_checks]; rfl
  · rw [RealizedProgram.Structure.memberValueTab_eq, Generated.Falcon512.Emulated.ROMParams.Structure.memberValues_eq]; rfl

/-- `hhat` has `512` coordinates. -/
theorem hhatSize : (program.value 593).size = 512 := valueShape_size value_statement_2ehhat_header.2

/-- The program's shared expressions read only earlier entries. -/
theorem refsOrdered : program.RefsOrdered := Generated.Falcon512.Emulated.ROMParams.conditions.wellFormed.refsOrdered

/-- The program of `Falcon512.Emulated.ROMParams` has the Falcon frontend's program facts. -/
instance : FalconHBase program where
  selectPreds := selectPreds
  selectShape_eq := selectShape_eq
  refsOrdered := refsOrdered
  domainField0 := domainField0
  selConstField := selConstField
  const_entries := const_entries
  deltaKind := value_h2p_2eselect_2edelta_kind
  deltaField := deltaField
  selReads_nil := selReads_nil
  chal0 := chal0
  isSourceChal_iff j := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.Falcon512.Emulated.ROMParams.conditions.wellFormed,
      source_challenges, List.mem_singleton]

/-- The emulated program has the Falcon frontend's program facts about domain `A`, at
`c_A = 595`, `s2 = 596`. -/
instance : FalconACore program where
  cA := 595
  s2 := 596
  domainField1 := domainField1
  macEqual := by
    obtain ⟨_, h⟩ := predicate_mac_2eequal_body
    exact ⟨299, predicate_mac_2eequal_role.1, by rw [h]; rfl, program.inSource_of_source predicate_mac_2eequal_role.2⟩
  cABoolean := by
    obtain ⟨_, h⟩ := predicate_crossing_2ec_5fA_2eboolean_body
    exact ⟨284, predicate_crossing_2ec_5fA_2eboolean_role.1, by rw [h]; rfl,
      program.inSource_of_type predicate_crossing_2ec_5fA_2eboolean_role.2 (valueShape_role value_crossing_2ec_5fA_header.2)⟩
  raw_facts := raw_facts
  hhatCheck := hhatCheck
  hhatValue := hhatValue
  hhatSize := hhatSize
  hhatField := hhatField
  srcReads_nil := srcReads_nil

/-- **The labels `g^j` as spread products**: entry `j + 1` of the constant `39` is entry `j` times
`g`, checked in the spread representation (`gf2_128Exec`). -/
theorem gpow_chain : ∀ j < 511, gf2_128Exec.mul
    (gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 39).getD j 0)).toNat)
    (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) =
    gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 39).getD (j + 1) 0)).toNat := by
  rw [constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind]
  decide +kernel

/-- **`g^512` as a spread product**: the constant `36` is entry `511` of `39` times `g`. -/
theorem gN_chain : gf2_128Exec.mul
    (gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 39).getD 511 0)).toNat)
    (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) =
    gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 36).getD 0 0)).toNat := by
  rw [constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind, constEntries_of_kind value_h2p_2eselect_2edone_2econstant_2eleft_2esecond_2esecond_2efirst_kind]
  decide +kernel

/-- **Entry `j` of the constant `39` is `g^j`** (`gpow_chain`, from entry `0 = 1`). -/
theorem gf2_128OfNat_gpow : ∀ j < 512,
    gf2_128OfNat ((program.constEntries 39).getD j 0) = gf2_128SubfieldGen ^ j
  | 0, _ => by rw [(FalconHBase.const_entries (program := program)).1, gf2_128OfNat_one, pow_zero]
  | j + 1, hj => by
    have hmul := gfMul_eq_of_spread (gpow_chain j (by omega))
    have := congrArg gf2_128OfBitVec hmul
    rw [gf2_128OfBitVec_gfMul, gf2_128OfBitVec_subfieldGenBV] at this
    change gf2_128OfNat _ * _ = gf2_128OfNat _ at this
    rw [← this, gf2_128OfNat_gpow j (by omega), pow_succ]

/-- The selection labels of the program of `Falcon512.Emulated.ROMParams` in `GF(2^128)`. -/
instance : FalconHConsts program RealizedProgram.gf128 where
  gpow := gf2_128OfNat_gpow
  gN := by
    have hmul := congrArg gf2_128OfBitVec (gfMul_eq_of_spread gN_chain)
    rw [gf2_128OfBitVec_gfMul, gf2_128OfBitVec_subfieldGenBV] at hmul
    change gf2_128OfNat _ * _ = gf2_128OfNat _ at hmul
    change gf2_128OfNat _ = gf2_128SubfieldGen ^ 512
    rw [← hmul, gf2_128OfNat_gpow 511 (by omega), ← pow_succ]
    rfl

/-- The selection field of the program of `Falcon512.Emulated.ROMParams` is `GF(2^128)`, with its
labels; domain `A`'s field is Goldilocks². -/
instance : FalconSelField program RealizedProgram.gf128 RealizedProgram.gold2 :=
  FalconSelField.ofHash

end GordieHowe.Falcon512.Emulated.ROMParams
