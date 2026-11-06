-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.HonestValues
public import GordieHowe.Applications.Falcon512.Native.QROMParams.GadgetFacts
public import GordieHowe.Language.Honest.SourceRoles

public section

/-!
# Native Falcon witness meanings for checked source roles

Checked role placement and coverage select source coordinates. The lemmas below identify each
role's witness component with the existing honest value.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram
open Generated.Falcon512.Native.QROMParams.Program (program)
open Generated.Falcon512.Native.QROMParams.SourceRoleFacts
open Generated.Falcon512.Native.QROMParams.ShapeFacts
open HashShapeFacts

local notation "classifier" => Generated.Falcon512.Native.QROMParams.SourceRoles.classifier

/-- **Every round's words have their declared hash role.** Closed data. -/
theorem role_words_lookup : ∀ (p : Fin 11) (t : Fin 24),
    Generated.Falcon512.Native.QROMParams.SourceRoles.classifier.lookup (wordsVal p t) =
      some (SourceRole.hashWord, 1 + 24 * (p : ℕ) + (t : ℕ)) := by
  rw [Generated.Falcon512.Native.QROMParams.SourceRoles.classifier_eq]
  decide +kernel

/-- **The checked source roles read the honest values at every source coordinate.** -/
theorem role_source_coordinates {FH FA : FieldInterp} [HField FH] [AField FA]
    [FalconHConsts program FH] [FalconSelField program FH FA] {i : HonestIn}
    {s : SourceValues (falconInterpOf FH FA 0).K
      (falconInterpOf FH FA (SelectShape.field program selShape)).K}
    (hsv : HonestSourceValues program FH FA i s)
    {v j : ℕ} (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    s.valuation (program := program) (I := falconInterpOf FH FA) classifier v j =
      program.execOf (falconInterpOf FH FA) (honestVal program FH FA i) v j := by
  have hk := hc.source_kind hs hpad
  obtain ⟨r, hr⟩ := rolesOk.exec_covered hc hs hpad
  obtain ⟨hm, hv⟩ := sourceRoleTable_mem hr
  subst v
  rcases role_value_cases r hm with ho | hl
  · obtain ⟨⟨p, t⟩, hw⟩ := Option.isSome_iff_exists.1 ho
    have he := wordsOwner?_eq hw
    simp only at he
    rw [← he]
    rw [SourceValues.valuation_of_lookup _ (role_words_lookup p t),
      execOf_of_priv _ (word_facts p t).2.1]
    exact hsv.meaning_round j p t
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_nonce_lookup, execOf_of_priv _ value_nonce_kind]
      exact hsv.meaning_nonce j
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_message_lookup, execOf_of_priv _ value_message_kind]
      exact hsv.meaning_message j
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_message_2ein_5fmessage_lookup, execOf_of_priv _ value_message_2ein_5fmessage_kind]
      exact hsv.meaning_flags j
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_h2p_2eshake_2estate_2ewords_lookup, execOf_of_priv _ value_h2p_2eshake_2estate_2ewords_kind]
      exact hsv.meaning_state j
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_h2p_2eselect_2eraw_2ewords_lookup, execOf_of_priv _ value_h2p_2eselect_2eraw_2ewords_kind]
      exact hsv.meaning_raw j
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_h2p_2eselect_2ecount_lookup, execOf_of_priv _ value_h2p_2eselect_2ecount_kind]
      exact hsv.meaning_count j
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_h2p_2eselect_2efull_lookup, execOf_of_priv _ value_h2p_2eselect_2efull_kind]
      exact hsv.meaning_full j
    · rw [hl, value_statement_2ehhat_kind] at hk
      simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
      exact False.elim hk.2.2
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_crossing_2ec_5fA_lookup, execOf_of_priv _ value_crossing_2ec_5fA_kind]
      exact hsv.meaning_algebra j (slot := 0) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_s2_lookup, execOf_of_priv _ value_s2_kind]
      exact hsv.meaning_algebra j (slot := 1) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_signature_2es1_lookup, execOf_of_priv _ value_signature_2es1_kind]
      exact hsv.meaning_algebra j (slot := 2) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2ea_lookup, execOf_of_priv _ value_norm_2ea_kind]
      exact hsv.meaning_algebra j (slot := 3) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2esq_lookup, execOf_of_priv _ value_norm_2esq_kind]
      exact hsv.meaning_algebra j (slot := 4) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2ecc_lookup, execOf_of_priv _ value_norm_2ecc_kind]
      exact hsv.meaning_algebra j (slot := 5) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2end_lookup, execOf_of_priv _ value_norm_2end_kind]
      exact hsv.meaning_algebra j (slot := 6) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2enc_lookup, execOf_of_priv _ value_norm_2enc_kind]
      exact hsv.meaning_algebra j (slot := 7) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2eD_lookup, execOf_of_priv _ value_norm_2eD_kind]
      exact hsv.meaning_algebra j (slot := 8) (by decide) (by simp [NormValues])
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_norm_2eDc_lookup, execOf_of_priv _ value_norm_2eDc_kind]
      exact hsv.meaning_algebra j (slot := 9) (by decide) (by simp [NormValues])

end GordieHowe.Falcon512.Native.QROMParams
