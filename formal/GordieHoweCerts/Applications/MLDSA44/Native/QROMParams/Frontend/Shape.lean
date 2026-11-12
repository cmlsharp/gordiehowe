-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Frontend.Reads
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Hash
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Sample
public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.ShapeFacts

@[expose] public section

/-!
# GordieHowe frontend: domain `H`'s facts of `MLDSA44.Native.QROMParams`

The realized program of the native ML-DSA-44 proof of possession at the QROM parameters (`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`,
export `c825eb05`) has the domain `H` of `MLDSA44.Native.ROMParams` up to its `GF(2^256)` constants: the
program facts of the generic ML-DSA domain-`H` frontend (`MldsaHBase` … `MldsaHSample`, decided on
the program's tables) and, over `GF(2^256)` (`gf256`), the program-and-field facts (`MldsaHConsts`:
constant `37` the embedding basis, the constant of `h2c.sample.mem.unit` and of expression `523`
`θ + 1`), decided in `GF(2^256)`.
-/

namespace GordieHowe.MLDSA44.Native.QROMParams

open Generated.MLDSA44.Native.QROMParams.Program (program)
open ROMParams

/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHBase program where
  hPreds := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2eblocks_2er0_source_range
  hTyped := by shape_decide
  trKind := Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_tr_kind

/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHCross program where
  refsOrdered := Generated.MLDSA44.Native.QROMParams.conditions.wellFormed.refsOrdered
  lt525 := by shape_decide
  lt524 := by shape_decide
  expr525 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_eq
  expr524 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_eq
  len71 := by shape_decide
  len523 := by shape_decide
  len524 := by shape_decide
  bitView71 := by shape_decide
  domainField1 := by shape_decide

/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHSelect program where
  bitView555 := by shape_decide
  bitView556 := by shape_decide
  bitView559 := by shape_decide
  pred264 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2eselect_2estart_body
  pred265 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2eselect_2estep_body
  pred266 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2eselect_2eroute_body
  expr508 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estart_2eshape_2eleft_2efirst_2efirst_eq
  expr509 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2efirst_eq
  expr510 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument0_eq
  expr511 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq
  expr512 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_eq
  expr513 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2efirst_eq
  expr514 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2esecond_2esecond_2eshared_2esecond_2eshared_2esecond_eq
  expr515 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2esecond_2esecond_2eshared_2esecond_eq
  expr516 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2esecond_2esecond_2eshared_2efirst_2esecond_eq
  expr517 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2esecond_2esecond_eq
  expr518 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2esecond_2efirst_2esecond_2eshared_2esecond_eq
  expr519 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2eselect_2estep_2eshape_2eleft_2esecond_2esecond_2efirst_2esecond_2efirst_2esecond_2efirst_2esecond_eq
  refsSel := by shape_decide
  selConstsA := by
    shape_decide
  jFacts := by
    shape_decide
  selLens := by shape_decide
  stepConsts := by
    shape_decide
  routeConsts := by
    shape_decide
  routeLens := by shape_decide

section Rounds

open Generated.MLDSA44.Native.QROMParams.Program (idx17 idx18 idx19 idx20 idx21 idx22 idx23 idx24)

/-- A row of the checked round family has its round's shapes, with the given state source. -/
private theorem round_of_row {r : List ℕ} {src : RealizedProgram.StateSrc}
    (hb : ∃ t, (program.predicate (r.getD 0 0)).body = .equal 1 (.add (.leaf (r.getD 1 0))
      (.add (.add (.ref (r.getD 2 0)) (.mul (.sub (.leaf (r.getD 3 0)) (.reindex idx23
      (.ref (r.getD 2 0)))) (.reindex idx24 (.ref (r.getD 2 0))))) (.leaf (r.getD 4 0))))
      (.leaf (r.getD 5 0)) t)
    (hl : program.expr (r.getD 2 0) = .reindex idx22 (.add (.add src.expr (.reindex idx19
      (.reindex idx18 (.ref (r.getD 7 0))))) (.reindex idx19 (.reindex idx21 (.reindex idx20
      (.ref (r.getD 7 0)))))))
    (hc : program.expr (r.getD 7 0) = .apply (.sum 5) (.reindex idx17 src.expr)) :
    (program.predicate (r.getD 0 0)).body.roundShape? =
        some ⟨1, r.getD 1 0, r.getD 2 0, r.getD 4 0, r.getD 3 0, r.getD 5 0, idx23, idx24⟩ ∧
      (program.expr (r.getD 2 0)).linShape? =
        some ⟨src, r.getD 7 0, idx18, idx19, idx20, idx21, idx22⟩ ∧
      (program.expr (r.getD 7 0)).colShape? = some (src, idx17) := by
  obtain ⟨t, ht⟩ := hb
  exact ⟨RealizedProgram.PredBody.roundShape?_of_eq ht, RealizedProgram.Expr.linShape?_of_eq hl,
    RealizedProgram.Expr.colShape?_of_eq hc⟩

/-- Each round has a row of the checked round family: the first permutation round reads the
permutation's input expression, every later round the previous round's output. -/
private theorem round_rows : ∀ p : Fin 10, ∀ t : Fin 24,
    ((t : ℕ) = 0 → ∃ r ∈ Generated.MLDSA44.Native.QROMParams.Shapes.family_keccak_rounds_0_rows, r.getD 0 0 = roundPred p t ∧
      r.getD 1 0 = outVal p t ∧ r.getD 2 0 = linRef p t ∧ r.getD 3 0 = 10 ∧
      r.getD 4 0 = rcLeaf t ∧ r.getD 5 0 = 12 ∧ r.getD 6 0 = linRef p 0 - 2 ∧
      r.getD 7 0 = linRef p t - 1) ∧
    ((t : ℕ) ≠ 0 → ∃ r ∈ Generated.MLDSA44.Native.QROMParams.Shapes.family_keccak_rounds_1_rows, r.getD 0 0 = roundPred p t ∧
      r.getD 1 0 = outVal p t ∧ r.getD 2 0 = linRef p t ∧ r.getD 3 0 = 10 ∧
      r.getD 4 0 = rcLeaf t ∧ r.getD 5 0 = 12 ∧ r.getD 6 0 = outVal p (t - 1) ∧
      r.getD 7 0 = linRef p t - 1) := by
  decide +kernel

/-- The rounds' checked shapes and table facts. -/
private theorem rounds_checked (p : Fin 10) (t : Fin 24) :
    ((program.predicate (roundPred p t)).body.roundShape? =
        some ⟨1, outVal p t, linRef p t, rcLeaf t, 10, 12, idx23, idx24⟩ ∧
      (program.expr (linRef p t)).linShape? =
        some ⟨roundSrc p t.castSucc, linRef p t - 1, idx18, idx19, idx20, idx21, idx22⟩ ∧
      (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx17)) ∧
    (roundPred p t < program.predicates.length ∧
      program.inSource (program.predicate (roundPred p t)) = true ∧
      linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧
      1600 ≤ (program.value (outVal p t)).size) := by
  by_cases h0 : (t : ℕ) = 0
  · obtain ⟨r, hr, e0, e1, e2, e3, e4, e5, e6, e7⟩ := (round_rows p t).1 h0
    have hsrc : roundSrc p t.castSucc = .ref (r.getD 6 0) := by
      rw [e6]; simp only [roundSrc, Fin.coe_castSucc, h0, ↓reduceIte]
    have hrow := round_of_row (src := .ref (r.getD 6 0)) (Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_predicate0_body hr)
      (Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_expr0_eq hr) (Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_expr1_eq hr)
    have hrole := Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_predicate0_role hr
    have hhead := Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_value0_header hr
    rw [e0, e1, e2, e3, e4, e5, e7] at hrow
    rw [e0] at hrole
    rw [e1] at hhead
    rw [hsrc]
    refine ⟨hrow, hrole.1, program.inSource_of_source hrole.2, ?_, ?_, ?_⟩
    · rw [← e2]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_expr0_eq hr]; intro h; cases h)
    · rw [← e7]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_0_expr1_eq hr]; intro h; cases h)
    · exact (RealizedProgram.valueShape_size hhead.2).ge
  · obtain ⟨r, hr, e0, e1, e2, e3, e4, e5, e6, e7⟩ := (round_rows p t).2 h0
    have hsrc : roundSrc p t.castSucc = .leaf (r.getD 6 0) := by
      rw [e6]; simp only [roundSrc, Fin.coe_castSucc, h0, if_false]
    have hrow := round_of_row (src := .leaf (r.getD 6 0)) (Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_predicate0_body hr)
      (Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_expr0_eq hr) (Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_expr1_eq hr)
    have hrole := Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_predicate0_role hr
    have hhead := Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_value0_header hr
    rw [e0, e1, e2, e3, e4, e5, e7] at hrow
    rw [e0] at hrole
    rw [e1] at hhead
    rw [hsrc]
    refine ⟨hrow, hrole.1, program.inSource_of_source hrole.2, ?_, ?_, ?_⟩
    · rw [← e2]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_expr0_eq hr]; intro h; cases h)
    · rw [← e7]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.QROMParams.ShapeFacts.family_keccak_rounds_1_expr1_eq hr]; intro h; cases h)
    · exact (RealizedProgram.valueShape_size hhead.2).ge

end Rounds

/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHHashData program where
  roundShapes := fun p t => (rounds_checked p t).1
  round_facts := fun p t => (rounds_checked p t).2
  const_states := by
    shape_decide
  const_rc := by
    intro t
    fin_cases t
    · show program.constEntries 11 = _ ∧ program.isConstant 11 = true ∧ program.valueField 11 = 1
      shape_decide
    · show program.constEntries 13 = _ ∧ program.isConstant 13 = true ∧ program.valueField 13 = 1
      shape_decide
    · show program.constEntries 14 = _ ∧ program.isConstant 14 = true ∧ program.valueField 14 = 1
      shape_decide
    · show program.constEntries 15 = _ ∧ program.isConstant 15 = true ∧ program.valueField 15 = 1
      shape_decide
    · show program.constEntries 16 = _ ∧ program.isConstant 16 = true ∧ program.valueField 16 = 1
      shape_decide
    · show program.constEntries 17 = _ ∧ program.isConstant 17 = true ∧ program.valueField 17 = 1
      shape_decide
    · show program.constEntries 18 = _ ∧ program.isConstant 18 = true ∧ program.valueField 18 = 1
      shape_decide
    · show program.constEntries 19 = _ ∧ program.isConstant 19 = true ∧ program.valueField 19 = 1
      shape_decide
    · show program.constEntries 20 = _ ∧ program.isConstant 20 = true ∧ program.valueField 20 = 1
      shape_decide
    · show program.constEntries 21 = _ ∧ program.isConstant 21 = true ∧ program.valueField 21 = 1
      shape_decide
    · show program.constEntries 22 = _ ∧ program.isConstant 22 = true ∧ program.valueField 22 = 1
      shape_decide
    · show program.constEntries 23 = _ ∧ program.isConstant 23 = true ∧ program.valueField 23 = 1
      shape_decide
    · show program.constEntries 24 = _ ∧ program.isConstant 24 = true ∧ program.valueField 24 = 1
      shape_decide
    · show program.constEntries 25 = _ ∧ program.isConstant 25 = true ∧ program.valueField 25 = 1
      shape_decide
    · show program.constEntries 26 = _ ∧ program.isConstant 26 = true ∧ program.valueField 26 = 1
      shape_decide
    · show program.constEntries 27 = _ ∧ program.isConstant 27 = true ∧ program.valueField 27 = 1
      shape_decide
    · show program.constEntries 28 = _ ∧ program.isConstant 28 = true ∧ program.valueField 28 = 1
      shape_decide
    · show program.constEntries 29 = _ ∧ program.isConstant 29 = true ∧ program.valueField 29 = 1
      shape_decide
    · show program.constEntries 30 = _ ∧ program.isConstant 30 = true ∧ program.valueField 30 = 1
      shape_decide
    · show program.constEntries 31 = _ ∧ program.isConstant 31 = true ∧ program.valueField 31 = 1
      shape_decide
    · show program.constEntries 18 = _ ∧ program.isConstant 18 = true ∧ program.valueField 18 = 1
      shape_decide
    · show program.constEntries 32 = _ ∧ program.isConstant 32 = true ∧ program.valueField 32 = 1
      shape_decide
    · show program.constEntries 17 = _ ∧ program.isConstant 17 = true ∧ program.valueField 17 = 1
      shape_decide
    · show program.constEntries 33 = _ ∧ program.isConstant 33 = true ∧ program.valueField 33 = 1
      shape_decide

/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHHash program where
  view_kinds := ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2ec_5ftilde_2eout_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2ec_5ftilde_2er167_2evalue_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esib_2eout_2ep0_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esib_2er23_2evalue_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esib_2er23_2evalue_2ewords_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esib_2eout_2ep1_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esib_2er47_2evalue_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esib_2er47_2evalue_2ewords_kind⟩
  view_facts := by
    shape_decide
  hash_exprs := ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2epadding_2esuffix_2eshape_2eleft_2esecond_2efirst_2eshared_2efirst_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2eblocks_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esib_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esib_2er24_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq⟩
  expr_blk := fun
    | ⟨0, _⟩, h, _ => absurd h (by simp)
    | ⟨1, _⟩, h, _ => absurd h (by simp)
    | ⟨2, _⟩, _, _ => ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er24_2eshape_2eabsorbed_eq, by simp only [Fin.val_mk]; decide +kernel⟩
    | ⟨3, _⟩, _, _ => ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er48_2eshape_2eabsorbed_eq, by simp only [Fin.val_mk]; decide +kernel⟩
    | ⟨4, _⟩, _, _ => ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er72_2eshape_2eabsorbed_eq, by simp only [Fin.val_mk]; decide +kernel⟩
    | ⟨5, _⟩, _, _ => ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er96_2eshape_2eabsorbed_eq, by simp only [Fin.val_mk]; decide +kernel⟩
    | ⟨6, _⟩, _, _ => ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er120_2eshape_2eabsorbed_eq, by simp only [Fin.val_mk]; decide +kernel⟩
    | ⟨7, _⟩, _, _ => ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2ec_5ftilde_2er144_2eshape_2eabsorbed_eq, by simp only [Fin.val_mk]; decide +kernel⟩
    | ⟨8, _⟩, _, h => absurd h (by simp)
    | ⟨9, _⟩, _, h => absurd h (by simp)
  hash_sizes := by
    shape_decide
  pad_exprs := ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2epadding_2emonotone_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2epadding_2emax_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2epadding_2emin_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2epadding_2esuffix_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2epadding_2ezeros_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2emu_2epadding_2eoutput_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2epadding_2esuffix_2eshape_2eleft_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2epadding_2esuffix_2eshape_2eleft_2esecond_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2epadding_2eoutput_2eshape_2eleft_2efirst_2efirst_2eshared_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2epadding_2eoutput_2eshape_2eleft_2efirst_2efirst_eq, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2emu_2epadding_2eoutput_2eshape_2eleft_2esecond_2esecond_2efirst_eq⟩
  pad_facts := by
    shape_decide
  bit_kinds := ⟨Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2emu_2eout_kind, Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_w1_kind⟩
  kind458 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2ec_5ftilde_2eout_kind

-- Depth 1024 needed (fails at 512): `shape_decide` in the field `recConsts`.
set_option maxRecDepth 1024 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHShuffle program where
  phases_pos := by shape_decide
  pred268 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2emem_2eorigin_body
  pred270 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2emem_2efresh_body
  expr520 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2emem_2eunit_2eshape_2eleft_2esecond_2efirst_2efirst_eq
  expr521 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_h2c_2esample_2emem_2eshape_2eleft_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_2efirst_eq
  expr522 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2esecond_2eshared_eq
  refsMem := by shape_decide
  cellFacts := by
    shape_decide
  memConsts := by
    shape_decide
  freshLen := by shape_decide
  pred269_body := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2emem_body
  recConsts := by
    shape_decide
  recLens := by
    simp only [memR]
    shape_decide

/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHSample program where
  kind560 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esample_2eselect_2edelta_kind
  field560 := by shape_decide
  kind567 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_h2c_2esample_2emem_2edelta_kind
  field567 := by shape_decide
  sampleReads_nil := by
    shape_decide
  isSourceChal_iff := fun {j} => by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds
      Generated.MLDSA44.Native.QROMParams.conditions.wellFormed,
      Generated.MLDSA44.Native.QROMParams.ShapeFacts.source_challenges]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  chalFacts := by
    shape_decide
/-- **Entry `j < 8` of the constant `37` is `g^j`** in `GF(2^256)`, computed. -/
theorem c37_pow : ∀ j < 8,
    gf2_256OfNat ((program.constEntries 36).getD j 0) = gf2_256SubfieldGen ^ j := by
  shape_decide

/-- The native program at the QROM parameters, over `GF(2^256)`: entry `j < 8` of the constant `37` is `g^j = e_j`. -/
instance : MldsaHConstsSelect program RealizedProgram.gf256 where
  c37 j hj := c37_pow j hj

/-- The native program at the QROM parameters, over `GF(2^256)`: the constant of `h2c.sample.mem.unit` is `θ + 1`. -/
instance : MldsaHConsts program RealizedProgram.gf256 where
  theta := ⟨340282366920938463481821351509772796213, Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_h2c_2esample_2emem_2eunit_body, Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eleft_2eshared_2efirst_2esecond_2efirst_eq,
    by decide +kernel⟩

end GordieHowe.MLDSA44.Native.QROMParams
