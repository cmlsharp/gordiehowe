-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.ShapeFacts

public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.Certified
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.Frontend.Basic
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.Embed
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.RelationFacts
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.Table
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Frontend.Basic
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Frontend.Shape
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.QROMParams.Certified

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Native.QROMParams`, the frontend's facts and its soundness

The program facts of the native ML-DSA-44 ring program's frontend at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program.program`), decided here:
`MldsaRingStmt` (`ring.keys` value `52`, `ring.mu` value `53`; the frontend does not read `ring.tr`,
value `51`), `MldsaRingFront` (`member.mu` `56`, `h` `60`, `hint.w1` `64`, domain `H`'s `mu` `69`
and `w1` `71`, the crossing `mac.equal` of the shared expressions `513` and `50`), and the native
program's `MldsaAAlgebra`, `MldsaHSample`, `MldsaHHashCore`, `MldsaHConsts` and `MldsaHConstsSelect`
at the native program the ring holds. With the native frontend's hash view
(`MLDSA44.hashViewCore`) and SampleInBall's view (`MLDSA44.sampleView`, at the
native program at the QROM parameters), `source_rbr_knowledge_soundness` is the frontend's
round-by-round knowledge soundness of `Π_P₀` (`Ring.Native.rbr_of_views`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open Generated.MLDSA44.Ring.Native.QROMParams.Program RealizedProgram IOP
open Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts


/-- The native ML-DSA ring program at the ROM parameters has the statement values' facts. -/
instance : MldsaRingStmt program where
  keys := 52
  mu := 53
  keysKind := Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.value_ring_2ekeys_kind
  muKind := Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.value_ring_2emu_kind
  fields := ⟨RealizedProgram.valueShape_field Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.value_ring_2ekeys_header.2,
    RealizedProgram.valueShape_field Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.value_ring_2emu_header.2⟩
  keys_ne := by decide

/-- The native program the ring holds has domain `A`'s facts. -/
instance : MLDSA44.Native.MldsaAAlgebra (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.Native.MldsaAAlgebra nat)

/-- The native program the ring holds has SampleInBall's facts. -/
instance : MLDSA44.MldsaHSample (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSample nat)

/-- The native program the ring holds has the hash core's facts. -/
instance : MLDSA44.MldsaHHashCore (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHashCore nat)

/-- The native program the ring holds has the memory check's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConsts (MldsaRingEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConsts nat RealizedProgram.gf256)

/-- The native program the ring holds has the selection's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConstsSelect (MldsaRingEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConstsSelect nat RealizedProgram.gf256)

/-! The crossing's index maps: `x` reads `μ ‖ w1` below `6656`, then the support and the sign of
each coefficient alternately; `y` reads its parts in order. -/

theorem idx164_lo' : ∀ a < 104, ∀ b < 64, idx164.entry (64 * a + b) = 64 * a + b := by
  decide +kernel
theorem idx164_lo : ∀ t < 6656, idx164.entry t = t := fun t ht => by
  have h := idx164_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx164_even : ∀ k < 256, idx164.entry (6656 + 2 * k) = 6656 + k := by decide +kernel
theorem idx164_odd : ∀ k < 256, idx164.entry (6656 + (2 * k + 1)) = 6912 + k := by decide +kernel
theorem idx107_eq : idx107 = [(0, 1, 7168)] := by decide +kernel

/-- A checked node-typed source header. -/
private theorem typedCell {v : ℕ} {h : ValueShape}
    (hh : v < program.values.length ∧ program.valueShape v = h)
    (hr : h.role = .source := by rfl) (ht : h.typeSource = .node := by rfl) :
    v < program.values.length ∧ program.IsSourceValue v ∧
      (program.value v).typeSource = .node :=
  ⟨hh.1, (valueShape_role hh.2).trans hr, (valueShape_typeSource hh.2).trans ht⟩

set_option maxRecDepth 8192 in
/-- The native ML-DSA ring program at the QROM parameters has the frontend's facts. -/
instance : MldsaRingFront program where
  muA := 56
  hA := 60
  w1A := 66
  muH := 71
  w1H := 73
  muBoolPred := 10
  crossPred := 248
  crossH := 553
  crossA := 90
  shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  domains := ⟨Generated.MLDSA44.Ring.Native.QROMParams.conditions.fieldTable.domainField_eq 0 (by decide),
    Generated.MLDSA44.Ring.Native.QROMParams.conditions.fieldTable.domainField_eq 1 (by decide)⟩
  ltCross := ⟨by decide, expr_lt_of_ne_default (by
    rw [expr_mac_2eequal_2eshape_2eleft_eq]
    decide)⟩
  expr0 := Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.expr_member_2eselect_2eshape_2eleft_2efirst_2esecond_2esecond_2efirst_2efirst_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_eq
  expr1 := Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.expr_member_2eselect_2eshape_2eleft_2efirst_2esecond_2esecond_2efirst_2efirst_2efirst_eq
  muSize := RealizedProgram.valueShape_size Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.value_member_2emu_header.2
  muBool := by
    obtain ⟨t, ht⟩ := predicate_member_2emu_2eboolean_body
    refine ⟨?_, predicate_member_2emu_2eboolean_role.1,
      program.inSource_of_type predicate_member_2emu_2eboolean_role.2
        (valueShape_role value_member_2emu_header.2)⟩
    rw [ht]
    rfl
  cross := ⟨Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.predicate_mac_2eequal_role.1,
    program.inSource_of_source Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.predicate_mac_2eequal_role.2,
    Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.predicate_mac_2eequal_body⟩
  exprH := ⟨idx164, Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_eq, idx164_lo, idx164_even, idx164_odd⟩
  exprA := ⟨idx107, Generated.MLDSA44.Ring.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eright_eq, fun t ht => by rw [idx107_eq, IndexMap.entry_step_one ht, Nat.zero_add]⟩
  lens := by
    have hk : program.expr 553 ≠ default := by
      rw [expr_mac_2eequal_2eshape_2eleft_eq]
      decide
    refine ⟨?_, valueShape_size value_mu_header.2, valueShape_size value_w1_header.2, ?_, ?_,
      valueShape_size value_hint_2ew1_header.2⟩
    · rw [exprLen_ref Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed.refsOrdered
          (expr_lt_of_ne_default hk), expr_mac_2eequal_2eshape_2eleft_eq, exprLen_reindex, idx164_eq]
      decide
    · have hk' : program.expr 551 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2efirst_eq]
        decide
      change program.exprLen (.ref 551) = 256
      rw [exprLen_ref Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed.refsOrdered
          (expr_lt_of_ne_default hk'), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2efirst_eq,
        exprLen_add, exprLen_leaf]
      exact valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2
    · have hk' : program.expr 550 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_2eshared_eq]
        decide
      have hk'' : program.expr 552 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq]
        decide
      change program.exprLen (.ref 552) = 256
      rw [exprLen_ref Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk''), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq,
        exprLen_ref Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk'), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_2eshared_eq]
      rw [exprLen_add, exprLen_mul, exprLen_leaf]
      exact valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2
  bitViews := ⟨by simp only [isBitView, value_mu_kind], by simp only [isBitView, value_w1_kind]⟩
  vals := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  typedCore := by
    intro v hv
    simp only [MLDSA44.hTypedCore, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact typedCell value_h2c_2esample_2eselect_2ej_header
    · exact typedCell value_h2c_2esample_2emem_2eread_5fvalue_header
    · exact typedCell value_h2c_2esample_2emem_2eread_5forigin_header
    · exact typedCell value_h2c_2esample_2emem_2ec_5fenc_header
    · exact typedCell value_h2c_2esample_2emem_2efinal_5forigin_header
    · exact typedCell value_h2c_2esample_2emem_2eunit_header
    · exact typedCell value_h2c_2esample_2emem_2eorigin_header
  sibOff := 2
  chalSucc := chal2
  chal0 := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed,
      source_challenges]
    decide +kernel
  chalR := ⟨by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed,
      source_challenges]
    decide +kernel, by decide, by decide⟩
  relReads := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact program.nodeReads_of_priv value_signature_2ew_kind _
    · exact program.nodeReads_of_priv value_signature_2eQ_kind _
    · exact program.nodeReads_of_priv value_member_2et1_kind _
    · exact program.nodeReads_of_priv value_member_2ea_5fhat_kind _
    · exact program.nodeReads_of_bound value_z_kind _
    · exact program.nodeReads_of_priv value_challenge_2ec_kind _
  chalCases j hj := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed,
      source_challenges] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    change j = 0 ∨ j = 1 ∨ ∃ j', j = j' + 2
    rcases hj with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨0, rfl⟩)
    · exact .inr (.inr ⟨1, rfl⟩)
  chalIff j := by
    change program.IsSourceChal (j + 2) ↔ nat.IsSourceChal j
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Native.QROMParams.conditions.wellFormed,
      nat.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Native.QROMParams.conditions.wellFormed,
      source_challenges, Generated.MLDSA44.Native.QROMParams.ShapeFacts.source_challenges]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  chalShape j hj := by
    change nat.IsSourceChal j at hj
    rw [nat.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Native.QROMParams.conditions.wellFormed,
      Generated.MLDSA44.Native.QROMParams.ShapeFacts.source_challenges] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨challenge_h2c_2esample_2eselect_2edelta_full.2.2.2,
        challenge_h2c_2esample_2eselect_2edelta_full.2.1,
        Generated.MLDSA44.Native.QROMParams.ShapeFacts.challenge_h2c_2esample_2eselect_2edelta_full.2.2.2,
        Generated.MLDSA44.Native.QROMParams.ShapeFacts.challenge_h2c_2esample_2eselect_2edelta_full.2.1,
        challenge_h2c_2esample_2eselect_2edelta_full.2.2.1.trans
          Generated.MLDSA44.Native.QROMParams.ShapeFacts.challenge_h2c_2esample_2eselect_2edelta_full.2.2.1.symm⟩
    · exact ⟨challenge_h2c_2esample_2emem_2edelta_full.2.2.2,
        challenge_h2c_2esample_2emem_2edelta_full.2.1,
        Generated.MLDSA44.Native.QROMParams.ShapeFacts.challenge_h2c_2esample_2emem_2edelta_full.2.2.2,
        Generated.MLDSA44.Native.QROMParams.ShapeFacts.challenge_h2c_2esample_2emem_2edelta_full.2.1,
        challenge_h2c_2esample_2emem_2edelta_full.2.2.1.trans
          Generated.MLDSA44.Native.QROMParams.ShapeFacts.challenge_h2c_2esample_2emem_2edelta_full.2.2.1.symm⟩
  projReads := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact program.nodeReads_of_bits_priv value_h2c_2ec_5ftilde_2eout_kind value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_kind _
    · exact program.nodeReads_of_bound value_z_kind _
    · exact program.nodeReads_of_priv value_h_kind _

open Generated.MLDSA44.Native.QROMParams (interp)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Ring.Native.QROMParams`**
(`Ring.Native.rbr_of_views` at the native frontend's `sampleView` and `hashViewCore`): the
relation `Ring.Native.rel`, the extractor `Ring.Native.extractor` and the errors
`Ring.Native.ringEps` (`5143/|F_q^11|` at `member.table.gamma`, SampleInBall's `264/2^256` and
`295/2^256` at the ring's challenges `1`, `2`). -/
theorem source_rbr_knowledge_soundness :
    RBRKnowledgeSound (rel (program := program) (F0 := RealizedProgram.fq11)
        (FH := RealizedProgram.gf256)) (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent MLDSA44.sampleView)
        (ringEvent_use MLDSA44.sampleView)
        (sound_of_views MLDSA44.sampleView
          MLDSA44.hashViewCore))
      (program.roundError interp (ringEps (program := program) (F0 := RealizedProgram.fq11)
        (FH := RealizedProgram.gf256) MLDSA44.sampleView)) :=
  rbr_of_views MLDSA44.sampleView MLDSA44.hashViewCore

end GordieHowe.MLDSA44.Ring.Native.QROMParams
