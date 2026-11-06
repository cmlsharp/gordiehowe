-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Native.ROMParams.ShapeFacts

public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.Frontend.RelationFacts
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.Frontend.Table
public import GordieHowe.Applications.MLDSA44.Frontend.Sample
public import GordieHowe.Applications.MLDSA44.Frontend.Hash

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Native.ROMParams`, the frontend's facts and its soundness

The program facts of the native ML-DSA-44 ring program's frontend at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`), decided here:
`MldsaRingStmt` (`ring.keys` value `53`, `ring.mu` value `54`; the frontend does not read `ring.tr`,
value `52`), `MldsaRingFront` (`member.mu` `57`, `h` `61`, `hint.w1` `65`, domain `H`'s `mu` `70`
and `w1` `72`, the crossing `mac.equal` of the shared expressions `513` and `50`), and the native
program's `MldsaAAlgebra`, `MldsaHSample`, `MldsaHHashCore`, `MldsaHConsts` and `MldsaHConstsSelect`
at the native program the ring holds. With the native frontend's hash view
(`MLDSA44.hashViewCore`) and SampleInBall's view (`MLDSA44.sampleView`),
`source_rbr_knowledge_soundness` is the frontend's round-by-round knowledge soundness of `Π_P₀`
(`Ring.Native.rbr_of_views`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program RealizedProgram IOP
open Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts


/-- The native ML-DSA ring program at the ROM parameters has the statement values' facts. -/
instance : MldsaRingStmt program where
  keys := 53
  mu := 54
  keysKind := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.value_ring_2ekeys_kind
  muKind := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.value_ring_2emu_kind
  fields := ⟨RealizedProgram.valueShape_field Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.value_ring_2ekeys_header.2,
    RealizedProgram.valueShape_field Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.value_ring_2emu_header.2⟩
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

/-- The native program the ring holds has the memory check's constants in `GF(2^128)`. -/
instance : MLDSA44.MldsaHConsts (MldsaRingEmbed.nat program)
    RealizedProgram.gf128 :=
  inferInstanceAs (MLDSA44.MldsaHConsts nat RealizedProgram.gf128)

/-- The native program the ring holds has the selection's constants in `GF(2^128)`. -/
instance : MLDSA44.MldsaHConstsSelect (MldsaRingEmbed.nat program)
    RealizedProgram.gf128 :=
  inferInstanceAs (MLDSA44.MldsaHConstsSelect nat RealizedProgram.gf128)

/-! The crossing's index maps: `x` reads `μ ‖ w1` below `6656`, then the support and the sign of
each coefficient alternately; `y` reads its parts in order. -/

theorem idx163_lo' : ∀ a < 104, ∀ b < 64, idx163.entry (64 * a + b) = 64 * a + b := by
  decide +kernel
theorem idx163_lo : ∀ t < 6656, idx163.entry t = t := fun t ht => by
  have h := idx163_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx163_even : ∀ k < 256, idx163.entry (6656 + 2 * k) = 6656 + k := by decide +kernel
theorem idx163_odd : ∀ k < 256, idx163.entry (6656 + (2 * k + 1)) = 6912 + k := by decide +kernel
theorem idx106_eq : idx106 = [(0, 1, 7168)] := by decide +kernel

/-- A checked node-typed source header. -/
private theorem typedCell {v : ℕ} {h : ValueShape}
    (hh : v < program.values.length ∧ program.valueShape v = h)
    (hr : h.role = .source := by rfl) (ht : h.typeSource = .node := by rfl) :
    v < program.values.length ∧ program.IsSourceValue v ∧
      (program.value v).typeSource = .node :=
  ⟨hh.1, (valueShape_role hh.2).trans hr, (valueShape_typeSource hh.2).trans ht⟩

set_option maxRecDepth 8192 in
/-- The native ML-DSA ring program at the ROM parameters has the frontend's facts. -/
instance : MldsaRingFront program where
  muA := 57
  hA := 61
  w1A := 65
  muH := 70
  w1H := 72
  shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  domains := ⟨Generated.MLDSA44.Ring.Native.ROMParams.conditions.fieldTable.domainField_eq 0 (by decide),
    Generated.MLDSA44.Ring.Native.ROMParams.conditions.fieldTable.domainField_eq 1 (by decide)⟩
  lt513 := expr_lt_of_ne_default (by
    rw [expr_mac_2eequal_2eshape_2eleft_eq]
    decide)
  expr0 := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_member_2eselect_2eshape_2eleft_2efirst_2esecond_2esecond_2efirst_2efirst_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_eq
  expr1 := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_member_2eselect_2eshape_2eleft_2efirst_2esecond_2esecond_2efirst_2efirst_2efirst_eq
  muSize := RealizedProgram.valueShape_size Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.value_member_2emu_header.2
  muBool := by
    obtain ⟨t, ht⟩ := predicate_member_2emu_2eboolean_body
    refine ⟨?_, predicate_member_2emu_2eboolean_role.1,
      program.inSource_of_type predicate_member_2emu_2eboolean_role.2
        (valueShape_role value_member_2emu_header.2)⟩
    rw [ht]
    rfl
  cross := ⟨Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_mac_2eequal_role.1,
    program.inSource_of_source Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_mac_2eequal_role.2,
    Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_mac_2eequal_body⟩
  exprH := ⟨idx163, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_eq, idx163_lo, idx163_even, idx163_odd⟩
  exprA := ⟨idx106, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eright_eq, fun t ht => by rw [idx106_eq, IndexMap.entry_step_one ht, Nat.zero_add]⟩
  lens := by
    have hk : program.expr 513 ≠ default := by
      rw [expr_mac_2eequal_2eshape_2eleft_eq]
      decide
    refine ⟨?_, valueShape_size value_mu_header.2, valueShape_size value_w1_header.2, ?_, ?_,
      valueShape_size value_hint_2ew1_header.2⟩
    · rw [exprLen_ref Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered
          (expr_lt_of_ne_default hk), expr_mac_2eequal_2eshape_2eleft_eq, exprLen_reindex, idx163_eq]
      decide
    · have hk' : program.expr 511 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2efirst_eq]
        decide
      change program.exprLen (.ref 511) = 256
      rw [exprLen_ref Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered
          (expr_lt_of_ne_default hk'), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2efirst_eq,
        exprLen_add, exprLen_leaf]
      exact valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2
    · have hk' : program.expr 510 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_2eshared_eq]
        decide
      have hk'' : program.expr 512 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq]
        decide
      change program.exprLen (.ref 512) = 256
      rw [exprLen_ref Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk''), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq,
        exprLen_ref Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk'), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_2eshared_eq]
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
  chalSucc _ := rfl
  chal0 := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed,
      source_challenges]
    decide +kernel
  chalIff j := by
    change program.IsSourceChal (j + 1) ↔ nat.IsSourceChal j
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed,
      nat.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Native.ROMParams.conditions.wellFormed,
      source_challenges, Generated.MLDSA44.Native.ROMParams.ShapeFacts.source_challenges]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  chalShape j hj := by
    change nat.IsSourceChal j at hj
    rw [nat.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Native.ROMParams.conditions.wellFormed,
      Generated.MLDSA44.Native.ROMParams.ShapeFacts.source_challenges] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨challenge_h2c_2esample_2eselect_2edelta_full.2.2.2,
        challenge_h2c_2esample_2eselect_2edelta_full.2.1,
        Generated.MLDSA44.Native.ROMParams.ShapeFacts.challenge_h2c_2esample_2eselect_2edelta_full.2.2.2,
        Generated.MLDSA44.Native.ROMParams.ShapeFacts.challenge_h2c_2esample_2eselect_2edelta_full.2.1,
        challenge_h2c_2esample_2eselect_2edelta_full.2.2.1.trans
          Generated.MLDSA44.Native.ROMParams.ShapeFacts.challenge_h2c_2esample_2eselect_2edelta_full.2.2.1.symm⟩
    · exact ⟨challenge_h2c_2esample_2emem_2edelta_full.2.2.2,
        challenge_h2c_2esample_2emem_2edelta_full.2.1,
        Generated.MLDSA44.Native.ROMParams.ShapeFacts.challenge_h2c_2esample_2emem_2edelta_full.2.2.2,
        Generated.MLDSA44.Native.ROMParams.ShapeFacts.challenge_h2c_2esample_2emem_2edelta_full.2.1,
        challenge_h2c_2esample_2emem_2edelta_full.2.2.1.trans
          Generated.MLDSA44.Native.ROMParams.ShapeFacts.challenge_h2c_2esample_2emem_2edelta_full.2.2.1.symm⟩
  projReads := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact program.nodeReads_of_bits_priv value_h2c_2ec_5ftilde_2eout_kind value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_kind _
    · exact program.nodeReads_of_bound value_z_kind _
    · exact program.nodeReads_of_priv value_h_kind _

open Generated.MLDSA44.Native.ROMParams (interp)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Ring.Native.ROMParams`**
(`Ring.Native.rbr_of_views` at the native frontend's `sampleView` and `hashViewCore`): the
relation `Ring.Native.rel`, the extractor `Ring.Native.extractor` and the errors
`Ring.Native.ringEps` (`5143/|F_q^6|` at `member.table.gamma`, SampleInBall's `264/2^128` and
`295/2^128` at the ring's challenges `1`, `2`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness (rel (program := program) (F0 := RealizedProgram.fq6)
        (FH := RealizedProgram.gf128)) (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent MLDSA44.sampleView)
        (ringEvent_use MLDSA44.sampleView)
        (sound_of_views MLDSA44.sampleView
          MLDSA44.hashViewCore))
      (program.roundError interp (ringEps (program := program) (F0 := RealizedProgram.fq6)
        (FH := RealizedProgram.gf128) MLDSA44.sampleView)) :=
  rbr_of_views MLDSA44.sampleView MLDSA44.hashViewCore

end GordieHowe.MLDSA44.Ring.Native.ROMParams
