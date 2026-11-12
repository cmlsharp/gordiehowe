-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.ShapeFacts

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.Frontend.Basic
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.Embed
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.RelationFacts
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.Table
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Frontend.Basic
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Frontend.Shape
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.Frontend.Basic
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Carrier.QROMParams`, the frontend's facts and its soundness

The program facts of the ML-DSA-44 ring carrier's frontend at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program`, fields Goldilocks⁴ and
`GF(2^256)`), decided here: `Native.MldsaRingStmt` (`ring.keys` value `54`, `ring.mu` value `55`;
the frontend does not read `ring.tr`, value `53`), `MldsaCarrierFront` (the record,
`member.mu` `58`, the crossing `mac.equal` of the shared expressions `558` and `95`), the native
program's `MldsaHSample`,
`MldsaHHashCore`, `MldsaHConsts` and `MldsaHConstsSelect` at the native program
whose domain `H` core the carrier holds, and the emulated program's `MldsaEAlgebra` (with its
native program's `MldsaHHash`, `MldsaHSample`, `MldsaHConsts`) at the emulated program whose
domain `A` gadgets the carrier holds. With the native frontend's hash view
(`MLDSA44.hashViewCore`) and SampleInBall's view (`MLDSA44.sampleView`, at the
native program at the QROM parameters), `source_rbr_knowledge_soundness` is the frontend's
round-by-round knowledge soundness of `Π_P₀` (`Ring.Carrier.rbr_of_views`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program RealizedProgram IOP
open Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts

/-- The carrier at the QROM parameters has the statement values' facts. -/
instance : Native.MldsaRingStmt program where
  keys := 54
  mu := 55
  keysKind := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.value_ring_2ekeys_kind
  muKind := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.value_ring_2emu_kind
  fields := ⟨RealizedProgram.valueShape_field Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.value_ring_2ekeys_header.2,
    RealizedProgram.valueShape_field Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.value_ring_2emu_header.2⟩
  keys_ne := by decide

/-- The native program the carrier holds has SampleInBall's facts. -/
instance : MLDSA44.MldsaHSample (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSample nat)

/-- The native program the carrier holds has the hash core's facts. -/
instance : MLDSA44.MldsaHHashCore (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHashCore nat)

/-- The native program the carrier holds has the memory check's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConsts (CarrierHEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConsts nat RealizedProgram.gf256)

/-- The native program the carrier holds has the selection's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConstsSelect (CarrierHEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConstsSelect nat RealizedProgram.gf256)

/-- The emulated program the carrier holds has domain `A`'s facts. -/
instance : Emulated.MldsaEAlgebra (CarrierAEmbed.emu program) :=
  inferInstanceAs (Emulated.MldsaEAlgebra emu)

/-- The emulated program's native program has the hash's facts. -/
instance : MLDSA44.MldsaHHash
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHHash (Emulated.MldsaEmbed.nat emu))

/-- The emulated program's native program has SampleInBall's facts. -/
instance : MLDSA44.MldsaHSample
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHSample (Emulated.MldsaEmbed.nat emu))

/-- The emulated program's native program has the memory check's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConsts
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) RealizedProgram.gf256 :=
  inferInstanceAs
    (MLDSA44.MldsaHConsts (Emulated.MldsaEmbed.nat emu) RealizedProgram.gf256)

/-! The crossing's index maps: `x` reads `μ ‖ w1` below `6656`, then the support and the sign of
each coefficient alternately; `y` reads its parts in order. -/

theorem idx165_lo' : ∀ a < 104, ∀ b < 64, idx165.entry (64 * a + b) = 64 * a + b := by
  decide +kernel
theorem idx165_lo : ∀ t < 6656, idx165.entry t = t := fun t ht => by
  have h := idx165_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx165_even : ∀ k < 256, idx165.entry (6656 + 2 * k) = 6656 + k := by decide +kernel
theorem idx165_odd : ∀ k < 256, idx165.entry (6656 + (2 * k + 1)) = 6912 + k := by decide +kernel
theorem idx108_eq : idx108 = [(0, 1, 7168)] := by decide +kernel

/-- Where the renamings put the values and shared expressions the frontend reads, at this
carrier. -/
theorem σH_ids : (CarrierHEmbed.σ program).val 120 = 74 ∧ (CarrierHEmbed.σ program).val 70 = 76 ∧
    (CarrierHEmbed.σ program).val 457 = 413 ∧ (CarrierHEmbed.σ program).ref 523 = 556 ∧
    (CarrierHEmbed.σ program).ref 522 = 555 := by decide +kernel

theorem σA_ids : (CarrierAEmbed.σ program).val 58 = 61 ∧ (CarrierAEmbed.σ program).val 59 = 62 ∧
    (CarrierAEmbed.σ program).val 60 = 63 ∧ (CarrierAEmbed.σ program).val 61 = 64 ∧
    (CarrierAEmbed.σ program).val 63 = 69 := by decide +kernel

-- The `decide +kernel` checks of this instance decide closed goals about literals: the named
-- generated facts (`…_kind`, `expr_…_eq`, `idx…_eq`) are rewritten into them first.
/-- The carrier at the QROM parameters has the frontend's facts. -/
instance : MldsaCarrierFront program where
  hA := 62
  w1A := 69
  muBoolPred := 10
  crossPred := 250
  valsA := ⟨σA_ids.1.trans z_eq.symm, σA_ids.2.1, σA_ids.2.2.1.trans c_eq.symm,
    σA_ids.2.2.2.1.trans w_eq.symm, σA_ids.2.2.2.2⟩
  shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  domains := ⟨Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.fieldTable.domainField_eq 0 (by decide),
    Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.fieldTable.domainField_eq 1 (by decide)⟩
  lt558 := expr_lt_of_ne_default (by
    rw [expr_mac_2eequal_2eshape_2eleft_eq]
    decide)
  expr0 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_member_2eselect_2eshape_2eleft_2efirst_2esecond_2esecond_2efirst_2efirst_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_eq
  expr1 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_member_2eselect_2eshape_2eleft_2efirst_2esecond_2esecond_2efirst_2efirst_2efirst_eq
  muSize := RealizedProgram.valueShape_size Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.value_member_2emu_header.2
  muBool := by
    obtain ⟨t, ht⟩ := predicate_member_2emu_2eboolean_body
    refine ⟨?_, predicate_member_2emu_2eboolean_role.1,
      program.inSource_of_type predicate_member_2emu_2eboolean_role.2
        (valueShape_role value_member_2emu_header.2)⟩
    rw [ht]
    rfl
  cross := ⟨Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.predicate_mac_2eequal_role.1,
    program.inSource_of_source Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.predicate_mac_2eequal_role.2,
    Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.predicate_mac_2eequal_body⟩
  exprH := by
    rw [σH_ids.1, σH_ids.2.1, σH_ids.2.2.2.1]
    exact ⟨idx165, Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_eq, idx165_lo, idx165_even, idx165_odd⟩
  expr557 := by
    rw [σH_ids.2.2.2.2]
    exact Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq
  exprA := ⟨idx108, Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eright_eq, fun t ht => by rw [idx108_eq, IndexMap.entry_step_one ht, Nat.zero_add]⟩
  lens := by
    rw [σH_ids.1, σH_ids.2.1, σH_ids.2.2.2.1]
    have hk : program.expr 558 ≠ default := by
      rw [expr_mac_2eequal_2eshape_2eleft_eq, idx165_eq]
      decide +kernel
    refine ⟨?_, valueShape_size value_mu_header.2, valueShape_size value_w1_header.2, ?_, ?_,
      valueShape_size value_hint_2ew1_header.2⟩
    · rw [exprLen_ref Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered
          (expr_lt_of_ne_default hk), expr_mac_2eequal_2eshape_2eleft_eq, exprLen_reindex, idx165_eq]
      decide +kernel
    · have hk' : program.expr 556 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2efirst_eq]
        decide +kernel
      rw [exprLen_ref Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered
          (expr_lt_of_ne_default hk'), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2efirst_eq,
        exprLen_add, exprLen_leaf]
      exact valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2
    · have hk' : program.expr 555 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_2eshared_eq]
        decide +kernel
      have hk'' : program.expr 557 ≠ default := by
        rw [expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq]
        decide +kernel
      change program.exprLen (.ref 557) = 256
      rw [exprLen_ref Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk''), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_eq,
        exprLen_ref Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk'), expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2esecond_2eshared_eq]
      rw [exprLen_add, exprLen_mul, exprLen_leaf]
      exact valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2
  bitViews := by
    rw [σH_ids.1, σH_ids.2.1]
    exact ⟨by simp only [isBitView, value_mu_kind], by simp only [isBitView, value_w1_kind]⟩
  chal0 := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed,
      source_challenges]
    decide +kernel
  chal1 := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed,
      source_challenges]
    decide +kernel
  chalIff j := by
    change program.IsSourceChal (j + 2) ↔ nat.IsSourceChal j
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed,
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
    rw [σH_ids.2.2.1, z_eq]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact program.nodeReads_of_bits_priv value_h2c_2ec_5ftilde_2eout_kind value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_kind _
    · exact program.nodeReads_of_bound value_z_kind _
    · exact program.nodeReads_of_priv value_h_kind _
  relReads := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact program.nodeReads_of_bound value_signature_2ew_kind _
    · exact program.nodeReads_of_bound value_signature_2erelation_2eq_kind _
    · exact program.nodeReads_of_priv value_signature_2eQ_kind _
    · exact program.nodeReads_of_priv value_member_2et1_kind _
    · exact program.nodeReads_of_priv value_member_2ea_5fhat_kind _
    · exact program.nodeReads_of_bound value_z_kind _
    · exact program.nodeReads_of_priv value_challenge_2ec_kind _

open Generated.MLDSA44.Emulated.QROMParams (interp)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Ring.Carrier.QROMParams`**
(`Ring.Carrier.rbr_of_views` at the native frontend's `sampleView` and `hashViewCore`): the
relation `Ring.Carrier.rel`, the extractor `Ring.Carrier.extractor` and the errors
`Ring.Carrier.ringEps` (`5143/|Goldilocks⁴|` at `member.table.gamma`, `2040/|Goldilocks⁴|` at `signature.r`,
SampleInBall's `264/2^256` and `295/2^256` at the carrier's challenges `2`, `3`). -/
theorem source_rbr_knowledge_soundness :
    RBRKnowledgeSound (rel (program := program) (F0 := RealizedProgram.gold4)
        (FH := RealizedProgram.gf256)) (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent MLDSA44.sampleView)
        (ringEvent_use MLDSA44.sampleView)
        (sound_of_views MLDSA44.sampleView
          MLDSA44.hashViewCore))
      (program.roundError interp (ringEps (program := program) (F0 := RealizedProgram.gold4)
        (FH := RealizedProgram.gf256) MLDSA44.sampleView)) :=
  rbr_of_views MLDSA44.sampleView MLDSA44.hashViewCore

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
