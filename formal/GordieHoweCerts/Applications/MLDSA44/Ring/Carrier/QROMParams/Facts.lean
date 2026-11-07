-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.RoleSemantics
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.SourceRoleFacts
public import GordieHoweCerts.Generated.MLDSA44.Emulated.QROMParams.ShapeFacts
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.Front
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Facts
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.Facts
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified

@[expose] public section

/-!
# GordieHowe: the honest facts of `MLDSA44.Ring.Carrier.QROMParams`

The program facts the honest execution of the ML-DSA-44 ring carrier at the ROM parameters reads
(`GordieHowe.MLDSA44.Ring.Carrier.MldsaCarrierHonest`), from the named shape facts and checked source roles of
`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program` and of the native and emulated
programs it holds, and the proofs of possession's honest classes at the held programs.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program RealizedProgram
open Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts

/-- The native program the carrier holds has the honest hash's facts. -/
instance : MLDSA44.MldsaHHonest (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHonest nat)

/-- The native program the carrier holds has the memory check's facts. -/
instance : MLDSA44.MldsaHShuffle (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHShuffle nat)

/-- The native program the carrier holds has SampleInBall's honest cells. -/
instance : MLDSA44.MldsaHSelHonest (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest nat)

/-- The emulated program's native program has the honest hash's facts. -/
instance : MLDSA44.MldsaHHonest
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHHonest (Emulated.MldsaEmbed.nat emu))

/-- The emulated program's native program has SampleInBall's honest cells. -/
instance : MLDSA44.MldsaHSelHonest
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest (Emulated.MldsaEmbed.nat emu))

/-- The emulated program the carrier holds has the honest strategy's facts. -/
noncomputable instance : Emulated.MldsaEmulatedHonest (CarrierAEmbed.emu program)
    RealizedProgram.gold4 RealizedProgram.gf256 :=
  inferInstanceAs (Emulated.MldsaEmulatedHonest emu RealizedProgram.gold4 RealizedProgram.gf256)

/-- **The carrier's honest values' facts.** -/
instance : MldsaCarrierHonest program where
  qD := ⟨4096, [542, 543, 544]⟩
  kind64 := value_signature_2erelation_2eq_kind
  qFits := ⟨by decide, by decide, by decide⟩
  member_nodup := by decide
  member_none := by decide +kernel
  member_noneA := by decide +kernel
  member_cells := by
    intro v hv
    have hw := Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hw.privCellB_of_kind_priv value_member_2ea_5fhat_header.1 value_member_2ea_5fhat_kind,
        valueShape_field value_member_2ea_5fhat_header.2⟩
    · exact ⟨hw.privCellB_of_kind_priv value_member_2et1_header.1 value_member_2et1_kind,
        valueShape_field value_member_2et1_header.2⟩
    · exact ⟨hw.privCellB_of_kind_priv value_member_2emu_header.1 value_member_2emu_kind,
        valueShape_field value_member_2emu_header.2⟩
    · exact ⟨hw.privCellB_of_kind_priv value_member_2eselect_2eindex_header.1
          value_member_2eselect_2eindex_kind, valueShape_field value_member_2eselect_2eindex_header.2⟩
    · exact ⟨hw.privCellB_of_kind_priv value_signature_2erelation_2eq_2edigit_2elow_header.1
          value_signature_2erelation_2eq_2edigit_2elow_kind,
        valueShape_field value_signature_2erelation_2eq_2edigit_2elow_header.2⟩
    · exact ⟨hw.privCellB_of_kind_priv value_signature_2erelation_2eq_2edigit_2emiddle_header.1
          value_signature_2erelation_2eq_2edigit_2emiddle_kind,
        valueShape_field value_signature_2erelation_2eq_2edigit_2emiddle_header.2⟩
    · exact ⟨hw.privCellB_of_kind_priv value_signature_2erelation_2eq_2edigit_2ehigh_header.1
          value_signature_2erelation_2eq_2edigit_2ehigh_kind,
        valueShape_field value_signature_2erelation_2eq_2edigit_2ehigh_header.2⟩
  qSizes := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact valueShape_size value_signature_2erelation_2eq_2edigit_2elow_header.2
    · exact valueShape_size value_signature_2erelation_2eq_2edigit_2emiddle_header.2
    · exact valueShape_size value_signature_2erelation_2eq_2edigit_2ehigh_header.2
  privCellH := fun u hu h => by
    have hv := embeddingH.vals u hu
    have hc := hv.2.2.2.2.2.2.1
    have hp : nat.privCellB u = true := h
    rw [kind_of_privCellB hp] at hc
    exact Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv hv.2.1 (Renaming.kindCorr_priv _ hc)
  privCellA := fun u hu h => by
    have hv := embeddingA.vals u hu
    have hc := hv.2.2.2.2.2.2.1
    have hp : emu.privCellB u = true := h
    rw [kind_of_privCellB hp] at hc
    exact Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv hv.2.1 (Renaming.kindCorr_priv _ hc)
  coreV := ⟨⟨mem_hV_of_hVB rfl, mem_hV_of_hVB rfl⟩, fun p hp t => mem_hV_of_hVB
    ((by decide +kernel : ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, hVB (wordsVal p t) = true)
      p hp t)⟩
  selV := fun _ hu => mem_hV_of_hVB
    ((by decide : ∀ u ∈ [556, 557, 560, 561, 562, 563, 564, 565], hVB u = true) _ hu)
  aVals := by decide +kernel
  boundExprs := by
    change ∀ u ∈ [58, 61, 65, 66], (match (emu.value u).kind with
      | .bound E => E.opsFree && E.directNodes.all (· ∈ aV) && E.refs.isEmpty
      | _ => false) = true
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rw [Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_z_kind]; decide +kernel
    · rw [Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_signature_2ew_kind]; decide +kernel
    · rw [Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2eoffset_kind]; decide +kernel
    · rw [Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2eslack_kind]; decide +kernel
  bound := Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.derivable.elim fun _ hD => hD.bound

/-- **The carrier's table selection's identifiers.** -/
instance : MldsaCarrierSelect program where
  idx58 := rfl
  pred0 := rfl
  idxPred8 := rfl

/-- **The carrier's quotient's facts.** -/
instance : MldsaCarrierQuot program where
  sigReal := predicate_signature_2erelation_body
  qRange := by
    obtain ⟨r, h⟩ := predicate_signature_2erelation_2eq_body
    exact ⟨r, _, h, by decide⟩
  field64 := valueShape_field value_signature_2erelation_2eq_header.2
  size64 := valueShape_size value_signature_2erelation_2eq_header.2
  lt64 := value_signature_2erelation_2eq_header.1

/-- **The carrier's execution facts.** -/
instance : MldsaCarrierExec program where
  wf := Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed
  predicates_length := predicates_length
  nonSource := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact program.inSource_of_realization predicate_mac_2eA_role.2
    · exact program.inSource_of_realization predicate_range_2enorm_2ez_2etop_role.2
    · exact program.inSource_of_type_realization predicate_mac_2eblind_2eboolean_role.2
        (valueShape_role value_mac_2eblind_header.2)
    · exact program.inSource_of_realization predicate_mac_2elow_role.2
    · exact program.inSource_of_realization predicate_mac_2ehigh_role.2
    · exact program.inSource_of_realization predicate_mac_2enowrap_role.2
    · exact program.inSource_of_realization predicate_mac_role.2
  checks := statement_checks
  ranges := statement_ranges
  keysSize := valueShape_size value_ring_2ekeys_header.2
  crossOperands := by
    apply crossOperandsB_of_operands
    intro p hp dx x dy y k real hb
    obtain ⟨q, hq, hqp⟩ := exists_index_of_mem hp
    have hc : (program.predicate q).body.isCross = true := by rw [hqp, hb]; rfl
    have hm := mem_crossPredicateIds_iff.mpr ⟨hq, hc⟩
    rw [cross_predicates] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst q
    obtain ⟨r, hr⟩ := predicate_mac_2eequal_body
    rw [hqp, hb] at hr
    cases hr
    exact ⟨rfl, rfl, rfl, rfl⟩
  len42 := by
    have hk : program.expr 42 ≠ default := by
      rw [expr_mac_2eequal_2eshape_2eright_eq]
      decide
    rw [exprLen_ref Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered
        (expr_lt_of_ne_default hk), expr_mac_2eequal_2eshape_2eright_eq, exprLen_reindex, idx104_eq]
    decide
  cell_classes := cell_classes_of_rows (program := program)
    Generated.MLDSA44.Ring.Carrier.QROMParams.SourceRoleFacts.rolesOk (skip := [52, 53, 54, 60, 63, 64, 68, 69, 528, 529])
    (by
      rw [Generated.MLDSA44.Ring.Carrier.QROMParams.SourceRoles.roles_eq]
      decide +kernel)
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [value_ring_2etr_kind]; simp
      · rw [value_ring_2ekeys_kind]; simp
      · rw [value_ring_2emu_kind]; simp
      · rw [value_z_kind]; simp
      · rw [value_signature_2ew_kind]; simp
      · rw [value_signature_2erelation_2eq_kind]; simp
      · rw [value_hint_2eoffset_kind]; simp
      · rw [value_hint_2eslack_kind]; simp
      · obtain ⟨_, h⟩ := value_member_2etable_2epowers_kind; rw [h]; simp
      · obtain ⟨_, h⟩ := value_member_2etable_2edigests_kind; rw [h]; simp)

/-- **Every executed source coordinate reads its honest value**, by the program's classifier. -/
theorem role_coordinates {msgLen : ℕ} (y : RingIn msgLen) {v j : ℕ}
    (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    roleVal program RealizedProgram.gold4 RealizedProgram.gf256 y
        Generated.MLDSA44.Ring.Carrier.QROMParams.SourceRoles.classifier v j =
      program.execOf (mldsaInterpOf RealizedProgram.gold4 RealizedProgram.gf256)
        (honestVal program RealizedProgram.gold4 RealizedProgram.gf256 y) v j := by
  refine role_source_coordinates y Generated.MLDSA44.Ring.Carrier.QROMParams.SourceRoleFacts.rolesOk
    (skip := [52, 53, 54, 528, 529]) ?_ ?_ hs hc hpad
  · rw [Generated.MLDSA44.Ring.Carrier.QROMParams.SourceRoles.roles_eq]
    decide +kernel
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [value_ring_2etr_kind]; simp [Kind.isBound]
    · rw [value_ring_2ekeys_kind]; simp [Kind.isBound]
    · rw [value_ring_2emu_kind]; simp [Kind.isBound]
    · obtain ⟨_, h⟩ := value_member_2etable_2epowers_kind; rw [h]; simp [Kind.isBound]
    · obtain ⟨_, h⟩ := value_member_2etable_2edigests_kind; rw [h]; simp [Kind.isBound]

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
