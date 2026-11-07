-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Honest.Hash
public import GordieHoweCerts.Generated.Falcon512.Native.ROMParams.ShapeFacts
public import GordieHoweCerts.Generated.Falcon512.Native.ROMParams.Core
public import GordieHoweCerts.Generated.Falcon512.Native.ROMParams.SourceRoles

public section

/-!
# The Keccak rounds of `Falcon512.Native.ROMParams`

The checked round families (`Shapes.family_rounds_0_rows`, the two rounds reading a shared
expression, and `Shapes.family_rounds_1_rows`, the others) read at `roundRow`: each round's shapes
and honest word facts, with no reading of the program.
-/

namespace GordieHowe.Falcon512.Native.ROMParams.HashShapeFacts
open RealizedProgram
open _root_.GordieHowe.Generated.Falcon512.Native.ROMParams
open Program (program idx0 idx6 idx7 idx8 idx9 idx10 idx11 idx12 idx13)
open ShapeFacts

/-- **Every round is a row of its family.** Closed data: no reading of the program. -/
theorem roundRow_mem : ∀ (p : Fin 11) (t : Fin 24),
    (roundSrcIsRef p t = true → roundRow p t ∈ Shapes.family_rounds_0_rows) ∧
      (roundSrcIsRef p t = false → roundRow p t ∈ Shapes.family_rounds_1_rows) := by
  decide +kernel

/-- **The shapes of the `264` rounds.** -/
theorem roundShapes (p : Fin 11) (t : Fin 24) :
    (program.predicate (roundPred p t)).body.roundShape? =
      some ⟨0, outVal p t, linRef p t, rcLeaf t, 1, 3, idx12, idx13⟩ ∧
    (program.expr (linRef p t)).linShape? =
      some ⟨roundSrc p t.castSucc, linRef p t - 1, idx7, idx8, idx9, idx10, idx11⟩ ∧
    (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx6) := by
  cases h : roundSrcIsRef p t
  · have hr := (roundRow_mem p t).2 h
    obtain ⟨_, hb⟩ := family_rounds_1_predicate0_body hr
    rw [roundSrc_of_not_isRef h]
    exact ⟨PredBody.roundShape?_of_eq hb, Expr.linShape?_of_eq (family_rounds_1_expr0_eq hr),
      Expr.colShape?_of_eq (family_rounds_1_expr1_eq hr)⟩
  · have hr := (roundRow_mem p t).1 h
    obtain ⟨_, hb⟩ := family_rounds_0_predicate0_body hr
    rw [roundSrc_of_isRef h]
    exact ⟨PredBody.roundShape?_of_eq hb, Expr.linShape?_of_eq (family_rounds_0_expr0_eq hr),
      Expr.colShape?_of_eq (family_rounds_0_expr1_eq hr)⟩

/-- A shared expression that is not the default has a valid index. -/
private theorem expr_lt {k : ℕ} {e : Expr} (h : program.expr k = e) (he : e ≠ default) :
    k < program.exprs.length :=
  expr_lt_of_ne_default (h ▸ he)

/-- The rounds are source predicates below the table's length, their shared expressions below the
expressions' length, their outputs of `1600` coordinates. -/
theorem round_facts (p : Fin 11) (t : Fin 24) :
    roundPred p t < program.predicates.length ∧
      program.inSource (program.predicate (roundPred p t)) = true ∧
      linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧
      1600 ≤ (program.value (outVal p t)).size := by
  cases h : roundSrcIsRef p t
  · have hr := (roundRow_mem p t).2 h
    have hrole := family_rounds_1_predicate0_role hr
    exact ⟨hrole.1, program.inSource_of_source hrole.2,
      expr_lt (family_rounds_1_expr0_eq hr) (by intro hc; cases hc),
      expr_lt (family_rounds_1_expr1_eq hr) (by intro hc; cases hc),
      Nat.le_of_eq (valueShape_size (family_rounds_1_value0_header hr).2).symm⟩
  · have hr := (roundRow_mem p t).1 h
    have hrole := family_rounds_0_predicate0_role hr
    exact ⟨hrole.1, program.inSource_of_source hrole.2,
      expr_lt (family_rounds_0_expr0_eq hr) (by intro hc; cases hc),
      expr_lt (family_rounds_0_expr1_eq hr) (by intro hc; cases hc),
      Nat.le_of_eq (valueShape_size (family_rounds_0_value0_header hr).2).symm⟩

/-- **The rounds' words and outputs**: every output is the bit view `idx0` of its committed words. -/
theorem word_facts (p : Fin 11) (t : Fin 24) :
    (program.value (outVal p t)).kind = .bits (wordsVal p t) idx0 ∧
      (program.value (wordsVal p t)).kind = .priv ∧
      wordsVal p t < program.values.length ∧ program.IsSourceValue (wordsVal p t) ∧
      program.valueField (outVal p t) = 0 ∧ program.valueField (wordsVal p t) = 0 ∧
      (program.value (outVal p t)).size = 1600 ∧ (program.value (wordsVal p t)).size = 100 ∧
      (program.value (wordsVal p t)).type = .sub "GF(2^16)" ∧
      (program.value (wordsVal p t)).node.map (·.name) = some "GF(2^16)" := by
  cases h : roundSrcIsRef p t
  · have hr := (roundRow_mem p t).2 h
    have ho := family_rounds_1_value0_header hr
    have hw := family_rounds_1_value1_header hr
    exact ⟨family_rounds_1_value0_kind hr, family_rounds_1_value1_kind hr, hw.1,
      valueShape_role hw.2, valueShape_field ho.2, valueShape_field hw.2, valueShape_size ho.2,
      valueShape_size hw.2, (family_rounds_1_value1_type hr).2,
      congrArg (Option.map (·.name)) (valueShape_node hw.2)⟩
  · have hr := (roundRow_mem p t).1 h
    have ho := family_rounds_0_value0_header hr
    have hw := family_rounds_0_value1_header hr
    exact ⟨family_rounds_0_value0_kind hr, family_rounds_0_value1_kind hr, hw.1,
      valueShape_role hw.2, valueShape_field ho.2, valueShape_field hw.2, valueShape_size ho.2,
      valueShape_size hw.2, (family_rounds_0_value1_type hr).2,
      congrArg (Option.map (·.name)) (valueShape_node hw.2)⟩

/-- **The honest word checks of a round.** -/
theorem words_checks (p : Fin 11) (t : Fin 24) :
    program.isBitsB (outVal p t) (wordsVal p t) idx0 = true ∧
      program.privCellB (wordsVal p t) = true ∧ program.valueField (outVal p t) = 0 ∧
      program.valueField (wordsVal p t) = 0 ∧ (program.value (outVal p t)).size = 1600 ∧
      (program.value (wordsVal p t)).size = 100 ∧
      (program.value (wordsVal p t)).type.nodeName = some "GF(2^16)" := by
  obtain ⟨hk, hw, hlt, _, hf, hfw, hs, hsw, ht, _⟩ := word_facts p t
  exact ⟨isBitsB_of_kind hk, checked.wellFormed.privCellB_of_kind_priv hlt hw, hf, hfw, hs, hsw,
    valueType_nodeName ht⟩

/-- **Every source role reads a round's words or a named value.** Closed data. -/
theorem role_value_cases : ∀ r ∈ SourceRoles.roles,
    (wordsOwner? r.value).isSome = true ∨ r.value ∈ [45, 46, 47, 96, 588, 590, 591, 593, 594, 595,
      596, 597, 598, 599, 600, 601, 602, 603] := by
  decide +kernel

end GordieHowe.Falcon512.Native.ROMParams.HashShapeFacts
