-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.RoleSemantics
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.SourceRoleFacts
public import GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.ShapeFacts
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.ROMParams.Frontend.Front
public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.Facts
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Certified

@[expose] public section

/-!
# GordieHowe: the honest facts of `MLDSA44.Ring.Native.ROMParams`

The program facts the honest execution of the native ML-DSA-44 ring program at the ROM parameters
reads (`GordieHowe.MLDSA44.Ring.Native.MldsaRingHonest`), from the named shape facts of
`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program` and of the native program it holds
(`GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program`), its checked source roles and its
embedding, and the native program's honest classes at the held program.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program RealizedProgram
open Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts


/-- The native program the ring holds has the honest hash's facts. -/
instance : MLDSA44.MldsaHHonest (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHonest nat)

/-- The native program the ring holds has the memory check's facts. -/
instance : MLDSA44.MldsaHShuffle (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHShuffle nat)

/-- The native program the ring holds has SampleInBall's honest cells. -/
instance : MLDSA44.MldsaHSelHonest (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest nat)

/-- The native program the ring holds has the honest strategy's facts. -/
noncomputable instance : MLDSA44.Native.MldsaNativeHonest (MldsaRingEmbed.nat program)
    RealizedProgram.fq6 RealizedProgram.gf128 :=
  inferInstanceAs (MLDSA44.Native.MldsaNativeHonest nat RealizedProgram.fq6
    RealizedProgram.gf128)

/-- A renamed committed value of the held program is committed. -/
theorem privCell_held {u : ℕ} (hu : u ∈ embedData.V) (h : nat.privCellB u = true) :
    program.privCellB (σ.val u) = true := by
  have hv := embedding.vals u hu
  have hk : (program.value (σ.val u)).kind = .priv := by
    have hc := hv.2.2.2.2.2.2.1
    rw [kind_of_privCellB h] at hc
    exact Renaming.kindCorr_priv _ hc
  exact Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.privCellB_of_kind_priv hv.2.1 hk

/-- **The ring program's honest values' facts.** -/
instance : MldsaRingHonest program where
  inv := heldInv σ embedData.V
  inv_val := by
    change ∀ u ∈ embedData.V, heldInv σ embedData.V (σ.val u) = u
    decide +kernel
  member_ne := by
    change ∀ u ∈ embedData.V, ∀ v ∈ [54, 55, 56, 57, 63], σ.val u ≠ v
    decide +kernel
  member_nodup := by
    change ([54, 55, 56, 57, 63] : List ℕ).Nodup
    decide
  memberCells := by
    intro v hv
    change v ∈ [54, 55, 56, 57, 63] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    have hc := Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hc.privCellB_of_kind_priv value_member_2ea_5fhat_header.1 value_member_2ea_5fhat_kind,
        valueShape_field value_member_2ea_5fhat_header.2⟩
    · exact ⟨hc.privCellB_of_kind_priv value_member_2et1_header.1 value_member_2et1_kind,
        valueShape_field value_member_2et1_header.2⟩
    · exact ⟨hc.privCellB_of_kind_priv value_member_2emu_header.1 value_member_2emu_kind,
        valueShape_field value_member_2emu_header.2⟩
    · exact ⟨hc.privCellB_of_kind_priv value_member_2eselect_2eindex_header.1
          value_member_2eselect_2eindex_kind,
        valueShape_field value_member_2eselect_2eindex_header.2⟩
    · exact ⟨hc.privCellB_of_kind_priv value_signature_2eQ_header.1 value_signature_2eQ_kind,
        valueShape_field value_signature_2eQ_header.2⟩
  privCell := fun _ hu h => privCell_held hu h
  coreV := by
    change (69 ∈ embedData.V ∧ 119 ∈ embedData.V) ∧ ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24,
      wordsVal p t ∈ embedData.V
    decide +kernel
  selV := by
    change ∀ u ∈ [556, 557, 560, 561, 562, 563, 564, 565], u ∈ embedData.V
    decide +kernel
  aV := by
    change ∀ u ∈ MLDSA44.Native.AValues ++ [57, 64, 65], u ∈ embedData.V
    decide +kernel
  boundExprs := by
    change ([57, 64, 65] : List ℕ).all (fun u => match (nat.value u).kind with
      | .bound E => E.opsFree && E.directNodes.all (· ∈ embedData.V) && E.refs.isEmpty
      | _ => true) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true,
      Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_z_kind,
      Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2eoffset_kind,
      Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2eslack_kind]
    decide +kernel
  len50 := by
    change program.exprLen (.ref 90) = 7168
    have hk : program.expr 90 ≠ default := by
      rw [expr_mac_2eequal_2eshape_2eright_eq]
      decide
    rw [exprLen_ref Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered
        (expr_lt_of_ne_default hk),
      expr_mac_2eequal_2eshape_2eright_eq, exprLen_reindex, idx107_eq]
    decide
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
  bound := Generated.MLDSA44.Ring.Native.ROMParams.conditions.derivable.elim fun _ hD => hD.bound

/-- The realization's predicates are no source predicates. -/
theorem nonSource : ∀ q ∈ realizationPreds,
    program.inSource (program.predicate q) = false := by
  intro q hq
  simp only [realizationPreds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact program.inSource_of_realization predicate_mac_2eA_role.2
  · exact program.inSource_of_realization predicate_range_2enorm_2ez_2etop_role.2
  · exact program.inSource_of_type_realization predicate_mac_2eblind_2eboolean_role.2
      (valueShape_role value_mac_2eblind_header.2)
  · exact program.inSource_of_realization predicate_mac_2elow_role.2
  · exact program.inSource_of_realization predicate_mac_2ehigh_role.2
  · exact program.inSource_of_realization predicate_mac_2enowrap_role.2
  · exact program.inSource_of_realization predicate_mac_role.2

/-- The committed source values' classes, from the checked source roles at the renaming's inverse
table. -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      ([MldsaRandomPoint.aHat program, MldsaRandomPoint.t1 program, MldsaRingFront.muA program,
          (TableSelect.shape program).idx, MldsaRandomPoint.q program].contains v && program.valueField v == 0 &&
        (program.value v).node.map (·.name) == some "GF(p^1)") ||
      (decide (MldsaRingHonest.inv program v ∈ MldsaRingEmbed.V program) &&
        (MldsaRingEmbed.σ program).val (MldsaRingHonest.inv program v) == v &&
        ((MLDSA44.Native.AValues.contains (MldsaRingHonest.inv program v) && program.valueField v == 0 &&
            (program.value v).node.map (·.name) == some "GF(p^1)") ||
          (natGF16B (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "GF(2^16)") ||
          ([556, 561].contains (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "bit")))) = true := by
  refine cell_classes_of_rows
    Generated.MLDSA44.Ring.Native.ROMParams.SourceRoleFacts.rolesOk
    (skip := [51, 52, 53, 59, 68, 69, 528, 529]) (val := σ.val) (inv := heldInv σ embedData.V)
    (held := heldB σ embedData.V) ?_ rfl (fun _ h => mem_of_heldB h) ?_
  · change Generated.MLDSA44.Ring.Native.ROMParams.SourceRoles.roles.all
      (rowB [51, 52, 53, 59, 68, 69, 528, 529] [54, 55, 56, 57, 63] σ.val
        (heldInv σ embedData.V) (heldB σ embedData.V)) = true
    rw [Generated.MLDSA44.Ring.Native.ROMParams.SourceRoles.roles_eq]
    decide +kernel
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [value_ring_2etr_kind]; simp
    · rw [value_ring_2ekeys_kind]; simp
    · rw [value_ring_2emu_kind]; simp
    · rw [value_z_kind]; simp
    · rw [value_hint_2eoffset_kind]; simp
    · rw [value_hint_2eslack_kind]; simp
    · obtain ⟨_, h⟩ := value_member_2etable_2epowers_kind; rw [h]; simp
    · obtain ⟨_, h⟩ := value_member_2etable_2edigests_kind; rw [h]; simp

/-- **The ring program's execution facts.** -/
instance : MldsaRingExec program where
  wf := Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed
  nonSource := nonSource
  coverage := by
    rw [predicates_length]
    decide +kernel
  checks := statement_checks
  noBounds := statement_ranges
  cell_classes := cell_classes

/-- **Every executed source coordinate reads its honest value**, by the program's classifier. -/
theorem role_coordinates {msgLen : ℕ} (y : RingIn msgLen) {v j : ℕ}
    (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    roleVal program RealizedProgram.fq6 RealizedProgram.gf128 y
        Generated.MLDSA44.Ring.Native.ROMParams.SourceRoles.classifier v j =
      program.execOf (mldsaInterpOf RealizedProgram.fq6 RealizedProgram.gf128)
        (honestVal program RealizedProgram.fq6 RealizedProgram.gf128 y) v j := by
  refine role_source_coordinates y Generated.MLDSA44.Ring.Native.ROMParams.SourceRoleFacts.rolesOk
    (skip := [51, 52, 53, 528, 529]) (val := σ.val) (inv := heldInv σ embedData.V)
    (held := heldB σ embedData.V) ?_ rfl (fun _ h => mem_of_heldB h) ?_ hs hc hpad
  · change Generated.MLDSA44.Ring.Native.ROMParams.SourceRoles.roles.all
      (roleRowB [51, 52, 53, 528, 529] 54 55 56 57 63 σ.val (heldInv σ embedData.V)
        (heldB σ embedData.V)) = true
    rw [Generated.MLDSA44.Ring.Native.ROMParams.SourceRoles.roles_eq]
    decide +kernel
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [value_ring_2etr_kind]; simp [Kind.isBound]
    · rw [value_ring_2ekeys_kind]; simp [Kind.isBound]
    · rw [value_ring_2emu_kind]; simp [Kind.isBound]
    · obtain ⟨_, h⟩ := value_member_2etable_2epowers_kind; rw [h]; simp [Kind.isBound]
    · obtain ⟨_, h⟩ := value_member_2etable_2edigests_kind; rw [h]; simp [Kind.isBound]

end GordieHowe.MLDSA44.Ring.Native.ROMParams
