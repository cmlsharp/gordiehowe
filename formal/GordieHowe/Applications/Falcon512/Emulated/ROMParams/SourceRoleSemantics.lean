-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.HonestValues
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.GadgetFacts
public import GordieHowe.Language.Honest.SourceRoles

public section

/-!
# Emulated Falcon witness meanings for checked source roles

Checked role placement and coverage select source coordinates. The lemmas below identify each
role's witness component with the existing honest value.
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open RealizedProgram
open Generated.Falcon512.Emulated.ROMParams.Program (program)
open Generated.Falcon512.Emulated.ROMParams.SourceRoleFacts
open Generated.Falcon512.Emulated.ROMParams.ShapeFacts
open HashShapeFacts
open Native (HonestIn)

local notation "classifier" => Generated.Falcon512.Emulated.ROMParams.SourceRoles.classifier

/-- **Every round's words have their declared hash role.** Closed data. -/
theorem role_words_lookup : ∀ (p : Fin 11) (t : Fin 24),
    Generated.Falcon512.Emulated.ROMParams.SourceRoles.classifier.lookup (wordsVal p t) =
      some (SourceRole.hashWord, 1 + 24 * (p : ℕ) + (t : ℕ)) := by
  rw [Generated.Falcon512.Emulated.ROMParams.SourceRoles.classifier_eq]
  decide +kernel

/-- **The checked source roles read the honest values at every source coordinate.** -/
theorem role_source_coordinates {FH FA : FieldInterp} [HField FH] [EField FA]
    [FalconHConsts program FH] [FalconSelField program FH FA] {i : HonestIn}
    {s : SourceValues (falconInterpOf FH FA 0).K
      (falconInterpOf FH FA (SelectShape.field program selShape)).K}
    (hsv : HonestSourceValues program FH FA i s) (x : program.Valuation (falconInterpOf FH FA))
    (c : ∀ k, (program.layout (falconInterpOf FH FA)).Ch k)
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
    rcases hl with hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl
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
    · rw [hl, value_key_2ecoefficients_kind] at hk
      simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
      exact False.elim hk.2.2
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_crossing_2ec_5fA_lookup, execOf_of_priv _ value_crossing_2ec_5fA_kind]
      exact hsv.meaning_algebra j (by simp [aValues]) (hsv.cA j)
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_s2_lookup, execOf_of_priv _ value_s2_kind]
      exact hsv.meaning_algebra j (by simp [aValues]) (hsv.s2 j)
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_signature_2es1_lookup, execOf_of_priv _ value_signature_2es1_kind]
      exact hsv.meaning_algebra j (by simp [aValues]) (hsv.s1 j)
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_magnitudes_2emag1_lookup]
      exact hsv.meaning_mag1 j x c (by
        have hsz := hk.2.1
        rwa [valueShape_size value_magnitudes_2emag1_header.2] at hsz)
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_magnitudes_2emag2_lookup, execOf_of_priv _ value_magnitudes_2emag2_kind]
      exact hsv.meaning_algebra j (by simp [aValues]) (hsv.mag2 j)
    · rw [hl] at hk ⊢
      rw [SourceValues.valuation_of_lookup _ role_encoding_2elow2_lookup, execOf_of_priv _ value_encoding_2elow2_kind]
      exact hsv.meaning_algebra j (by simp [aValues]) (hsv.low2 j)
    · rw [hl] at hk ⊢
      have hj0 : j = 0 := by
        have hsz := hk.2.1
        rw [valueShape_size value_norm_2esquares_header.2] at hsz
        exact Nat.lt_one_iff.1 hsz
      subst j
      rw [SourceValues.valuation_of_lookup _ role_norm_2esquares_lookup]
      exact hsv.meaning_squares x c

end GordieHowe.Falcon512.Emulated.ROMParams
