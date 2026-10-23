-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Hash
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.Facts

@[expose] public section

/-!
# GordieHowe frontend: the Keccak trace's facts of `Falcon512.Native.QROMParams`

The program facts of `h2p.shake` (`FalconHHashData`, `FalconHHash`) for
`GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program` (export `c825eb05`), by `decide` over its
tables (a few minutes) and `rfl` for the generated bodies.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open Generated.Falcon512.Native.QROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace ROMParams

set_option maxRecDepth 8192 in
/-- **The shapes of the `240` rounds** (generated data: reading predicate `245` of the table unfolds `List.getD` that deep). -/
theorem roundShapes :
    ∀ p : Fin 10, ∀ t : Fin 24,
    (program.predicate (roundPred p t)).body.roundShape? =
    some ⟨0, outVal p t, linRef p t, rcLeaf t, 2, 4, idx14, idx15⟩ ∧
    (program.expr (linRef p t)).linShape? =
    some ⟨roundSrc p t.castSucc, linRef p t - 1, idx9, idx10, idx11, idx12, idx13⟩ ∧
    (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx8) := by
  decide +kernel

/-- The rounds are source predicates below the table's length, their shared expressions below the expressions' length, their outputs of `1600` coordinates. -/
theorem round_facts :
    ∀ p : Fin 10, ∀ t : Fin 24,
    roundPred p t < program.predicates.length ∧
    program.inSource (program.predicate (roundPred p t)) = true ∧
    linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧
    1600 ≤ (program.value (outVal p t)).size := by
  decide +kernel

/-- The constant states: all ones (`const2`), all zeros (`const4`). -/
theorem const_states :
    program.constEntries 2 = List.replicate 1600 1 ∧
    program.constEntries 4 = List.replicate 1600 0 ∧ program.isConstant 2 = true ∧
    program.isConstant 4 = true ∧ program.valueField 2 = 0 ∧ program.valueField 4 = 0 := by
  decide +kernel

/-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
theorem const_rc :
    ∀ t : Fin 24, program.constEntries (rcLeaf t) =
    List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧
    program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The `h2p.shake` facts of the program of `Falcon512.Native.QROMParams`, decided over the tables. -/
instance : FalconHHashData program where
  roundShapes := roundShapes
  round_facts := round_facts
  const_states := const_states
  const_rc := const_rc

/-- The predicates of `h2p.shake` are source predicates, decided. -/
theorem shake_source :
    ∀ q < 246, q < program.predicates.length ∧
    program.inSource (program.predicate q) = true := by
  decide +kernel

/-- Facts of the absorbed block's selector and the squeezes' inputs, decided. -/
theorem squeezeIn_facts :
    idx24.entry 0 = 0 ∧ idx24.entry 1 = 1 ∧ idx25.entry 0 = 0 ∧
    idx26.entry 0 = 1 ∧ (∀ j < 1600, idx27.entry j = 0) ∧ (∀ j < 1600, idx7.entry j = j) ∧
    idx27.size = 1600 ∧ (program.value 26).size = 1 ∧ program.isConstant 26 = true ∧
    program.isConstant 0 = true ∧ program.valueField 26 = 0 ∧ program.valueField 0 = 0 ∧
    (program.constEntries 26).getD 0 0 = 1 ∧ (program.constEntries 0).getD 0 0 = 0 ∧
    29 < program.predicates.length ∧ program.inSource (program.predicate 29) = true ∧
    56 < program.exprs.length := by
  decide +kernel

/-- Facts of the flags and the padding predicates, decided. -/
theorem flag_facts :
    (47 < program.values.length ∧ program.IsSourceValue 47 ∧
    (program.value 47).typeSource = .node ∧ (program.value 47).type = .bit) ∧
    (program.value 47).size = 136 ∧
    (∀ i < 135, idx16.entry i = i + 1) ∧ (∀ i < 135, idx17.entry i = i) ∧
    (∀ i < 135, idx18.entry i = 0) ∧ idx19.entry 0 = 72 ∧ idx20.entry 0 = 39 ∧
    idx16.size = 135 ∧ idx19.size = 1 ∧ idx20.size = 1 ∧
    program.isConstant 27 = true ∧ program.valueField 27 = 0 ∧
    (∀ i < 135, (program.constEntries 27).getD i 0 = 0) ∧
    (∀ p ∈ [24, 25, 26, 27, 28], p < program.predicates.length ∧
    program.inSource (program.predicate p) = true) := by
  decide +kernel

/-- Facts of the absorbed block and the padding's constants, decided. -/
theorem absorb_facts :
    (∀ j < 1088, idx4.entry j = if j < 320 then j else 320) ∧
    (∀ j < 1088, idx5.entry j = if j < 320 then 768 else j - 320) ∧
    (∀ j < 1088, idx6.entry j = j) ∧ idx6.size = 1088 ∧
    (∀ i < 136, idx21.entry i = i) ∧ (∀ i < 136, ∀ t < 8, idx22.entry (i * 8 + t) = t) ∧
    (∀ i < 136, idx23.entry i = 0) ∧ idx21.size = 136 ∧ idx17.size = 135 ∧
    (program.value 45).size = 320 ∧ (program.value 46).size = 768 ∧ (program.value 0).size = 1 ∧
    program.constEntries 1 = List.replicate 512 0 ∧
    (∀ t < 8, (program.constEntries 28).getD t 0 = (program.constEntries 39).getD t 0) ∧
    (∀ i < 135, (program.constEntries 29).getD i 0 =
    (program.constEntries 39).getD 0 0 ^^^ (program.constEntries 39).getD 1 0 ^^^
    (program.constEntries 39).getD 2 0 ^^^ (program.constEntries 39).getD 3 0 ^^^
    (program.constEntries 39).getD 4 0) ∧
    (∀ i < 136, (program.constEntries 30).getD i 0 = 0) ∧
    (∀ i < 135, (program.constEntries 31).getD i 0 = 0) ∧
    (program.constEntries 31).getD 135 0 = (program.constEntries 39).getD 7 0 ∧
    (∀ v ∈ [1, 28, 29, 30, 31], program.isConstant v = true ∧ program.valueField v = 0) := by
  decide +kernel

/-- The views' sizes, decided. -/
theorem view_sizes :
    (program.value 97).size = 1600 ∧ (program.value 146).size = 1088 ∧
    (program.value 195).size = 1088 ∧ (program.value 244).size = 1088 ∧
    (program.value 293).size = 1088 ∧ (program.value 342).size = 1088 ∧
    (program.value 391).size = 1088 ∧ (program.value 440).size = 1088 ∧
    (program.value 489).size = 1088 ∧ (program.value 538).size = 432 ∧
    489 < program.exprs.length := by
  decide +kernel

/-- Facts of the views' selections, decided. -/
theorem view_sel :
    idx0.size = 100 ∧ idx1.size = 68 ∧ idx2.size = 27 ∧
    (∀ j < 100, idx0.entry j = j) ∧ (∀ j < 68, idx1.entry j = j) ∧ (∀ j < 27, idx2.entry j = j) ∧
    ∀ k : Fin 9, program.valueField (viewVal (k + 1)) = 0 ∧
    program.valueField (outVal (k + 1) 23) = 0 ∧ (program.value (outVal (k + 1) 23)).size = 1600 ∧
    (program.value (viewVal (k + 1))).size = zslot (k + 1) := by
  decide +kernel

/-- Facts of the nonce and the message part, decided: bit-typed source values. -/
theorem buf_facts :
    (45 < program.values.length ∧ program.IsSourceValue 45 ∧
    (program.value 45).typeSource = .node ∧ (program.value 45).type = .bit) ∧
    (46 < program.values.length ∧ program.IsSourceValue 46 ∧
    (program.value 46).typeSource = .node ∧ (program.value 46).type = .bit) := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- expr_squeezeIn. -/
theorem expr_squeezeIn :
    program.expr 53 = .reindex idx24 (.concat (.leaf 26) (.leaf 0)) ∧
    program.expr 54 = .add (.reindex idx25 (.ref 53)) (.reindex idx26 (.ref 53)) ∧
    program.expr 55 = .reindex idx7 (.leaf 95) ∧ program.expr 56 = .reindex idx7 (.leaf 97) ∧
    program.predicate 29 = «p.h2p.shake.padding.output» :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- pred_padding. -/
theorem pred_padding :
    program.predicate 24 = «p.h2p.shake.padding.monotone» ∧
    program.predicate 25 = «p.h2p.shake.padding.max» ∧
    program.predicate 26 = «p.h2p.shake.padding.min» ∧
    program.predicate 27 = «p.h2p.shake.padding.suffix» ∧
    program.predicate 28 = «p.h2p.shake.padding.zeros» :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- expr_absorb. -/
theorem expr_absorb :
    program.expr 0 =
    .add (.reindex idx4 (.concat (.leaf 45) (.leaf 0)))
    (.reindex idx5 (.concat (.leaf 46) (.leaf 0))) ∧
    program.expr 1 = .reindex idx6 (.ref 0) ∧
    program.expr 2 =
    .reindex idx7 (.reindex idx7 (.concat (.reindex idx6 (.reindex idx6 (.ref 1))) (.leaf 1))) ∧
    program.expr 51 = .reindex idx21 (.concat (.leaf 26) (.reindex idx17 (.leaf 47))) ∧
    program.expr 52 = .apply (.sum 8) (.mul (.reindex idx6 (.reindex idx6 (.ref 1)))
    (.reindex idx22 (.leaf 28))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- expr489. -/
theorem expr489 :
    program.expr 489 =
    .add (.add (.add (.add (.add (.add (.add (.add (.add
    (.reindex idx30 (.concat (.leaf 97) (.leaf 0)))
    (.reindex idx31 (.concat (.leaf 146) (.leaf 0))))
    (.reindex idx32 (.concat (.leaf 195) (.leaf 0))))
    (.reindex idx33 (.concat (.leaf 244) (.leaf 0))))
    (.reindex idx34 (.concat (.leaf 293) (.leaf 0))))
    (.reindex idx35 (.concat (.leaf 342) (.leaf 0))))
    (.reindex idx36 (.concat (.leaf 391) (.leaf 0))))
    (.reindex idx37 (.concat (.leaf 440) (.leaf 0))))
    (.reindex idx38 (.concat (.leaf 489) (.leaf 0))))
    (.reindex idx39 (.concat (.leaf 538) (.leaf 0))) :=
  rfl

set_option maxRecDepth 4096 in
/-- The view kinds of the output views. -/
theorem view_kinds : ∀ k : Fin 9,
    (program.value (viewVal (k + 1))).kind =
        .bits (outVal (k + 1) 23 - 1) (if (k : ℕ) + 1 = 9 then idx2 else idx1) ∧
      (program.value (outVal (k + 1) 23)).kind = .bits (outVal (k + 1) 23 - 1) idx0 ∧
      (program.value (outVal (k + 1) 23 - 1)).kind = .priv := by
  intro k
  fin_cases k <;> exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The `h2p.shake` facts of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHHash program where
  shake_source := shake_source
  expr_squeezeIn := expr_squeezeIn
  squeezeIn_facts := squeezeIn_facts
  pred_padding := pred_padding
  flag_facts := flag_facts
  absorb_facts := absorb_facts
  expr_absorb := expr_absorb
  expr489 := expr489
  view_sizes := view_sizes
  view_kinds := view_kinds
  view_sel := view_sel
  buf_facts := buf_facts

end GordieHowe.Falcon512.Native.QROMParams
