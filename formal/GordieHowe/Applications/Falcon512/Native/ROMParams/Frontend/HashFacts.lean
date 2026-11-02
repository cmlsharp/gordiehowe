-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Hash
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Facts

@[expose] public section

/-!
# GordieHowe frontend: the Keccak trace's facts of `Falcon512.Native.ROMParams`

The program facts of `h2p.shake` (`FalconHHashData`, `FalconHHash`) for
`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program` (export `3ed06086`), by `decide` over its
tables (a few minutes) and `rfl` for the generated bodies.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

set_option maxRecDepth 8192 in
/-- **The shapes of the `264` rounds** (generated data: reading predicate `269` of the table unfolds `List.getD` that deep). -/
theorem roundShapes :
    ∀ p : Fin 11, ∀ t : Fin 24,
    (program.predicate (roundPred p t)).body.roundShape? =
    some ⟨0, outVal p t, linRef p t, rcLeaf t, 1, 3, idx12, idx13⟩ ∧
    (program.expr (linRef p t)).linShape? =
    some ⟨roundSrc p t.castSucc, linRef p t - 1, idx7, idx8, idx9, idx10, idx11⟩ ∧
    (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx6) := by
  decide +kernel

/-- The rounds are source predicates below the table's length, their shared expressions below the expressions' length, their outputs of `1600` coordinates. -/
theorem round_facts :
    ∀ p : Fin 11, ∀ t : Fin 24,
    roundPred p t < program.predicates.length ∧
    program.inSource (program.predicate (roundPred p t)) = true ∧
    linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧
    1600 ≤ (program.value (outVal p t)).size := by
  decide +kernel

/-- The constant states: all ones (`const2`), all zeros (`const4`). -/
theorem const_states :
    program.constEntries 1 = List.replicate 1600 1 ∧
    program.constEntries 3 = List.replicate 1600 0 ∧ program.isConstant 1 = true ∧
    program.isConstant 3 = true ∧ program.valueField 1 = 0 ∧ program.valueField 3 = 0 := by
  decide +kernel

/-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
theorem const_rc :
    ∀ t : Fin 24, program.constEntries (rcLeaf t) =
    List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧
    program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The `h2p.shake` facts of the program of `Falcon512.Native.ROMParams`, decided over the tables. -/
instance : FalconHHashData program where
  roundShapes := roundShapes
  round_facts := round_facts
  const_states := const_states
  const_rc := const_rc

/-- The predicates of `h2p.shake` are source predicates, decided. -/
theorem shake_source :
    ∀ q < 270, q < program.predicates.length ∧
    program.inSource (program.predicate q) = true := by
  decide +kernel

/-- Facts of the absorbed block's selector and the squeezes' inputs, decided. -/
theorem squeezeIn_facts :
    idx22.entry 0 = 0 ∧ idx22.entry 1 = 1 ∧ idx23.entry 0 = 0 ∧
    idx24.entry 0 = 1 ∧ (∀ j < 1600, idx25.entry j = 0) ∧ (∀ j < 1600, idx5.entry j = j) ∧
    idx25.size = 1600 ∧ (program.value 25).size = 1 ∧ program.isConstant 25 = true ∧
    program.isConstant 27 = true ∧ program.valueField 25 = 0 ∧ program.valueField 27 = 0 ∧
    (program.constEntries 25).getD 0 0 = 1 ∧ (program.constEntries 27).getD 0 0 = 0 ∧
    29 < program.predicates.length ∧ program.inSource (program.predicate 29) = true ∧
    56 < program.exprs.length := by
  decide +kernel

/-- Facts of the flags and the padding predicates, decided. -/
theorem flag_facts :
    (47 < program.values.length ∧ program.IsSourceValue 47 ∧
    (program.value 47).typeSource = .node ∧ (program.value 47).type = .bit) ∧
    (program.value 47).size = 136 ∧
    (∀ i < 135, idx14.entry i = i + 1) ∧ (∀ i < 135, idx15.entry i = i) ∧
    (∀ i < 135, idx16.entry i = 0) ∧ idx17.entry 0 = 72 ∧ idx18.entry 0 = 39 ∧
    idx14.size = 135 ∧ idx17.size = 1 ∧ idx18.size = 1 ∧
    program.isConstant 26 = true ∧ program.valueField 26 = 0 ∧
    (∀ i < 135, (program.constEntries 26).getD i 0 = 0) ∧
    (∀ p ∈ [24, 25, 26, 27, 28], p < program.predicates.length ∧
    program.inSource (program.predicate p) = true) := by
  decide +kernel

/-- Facts of the absorbed block and the padding's constants, decided. -/
theorem absorb_facts :
    (∀ j < 1088, idx4.entry j = j) ∧ idx4.size = 1088 ∧
    (∀ i < 136, idx19.entry i = i) ∧ (∀ i < 136, ∀ t < 8, idx20.entry (i * 8 + t) = t) ∧
    (∀ i < 136, idx21.entry i = 0) ∧ idx19.size = 136 ∧ idx15.size = 135 ∧
    (program.value 45).size = 320 ∧ (program.value 46).size = 768 ∧ (program.value 27).size = 1 ∧
    program.constEntries 0 = List.replicate 512 0 ∧
    (∀ t < 8, (program.constEntries 28).getD t 0 = (program.constEntries 39).getD t 0) ∧
    (∀ i < 135, (program.constEntries 29).getD i 0 =
    (program.constEntries 39).getD 0 0 ^^^ (program.constEntries 39).getD 1 0 ^^^
    (program.constEntries 39).getD 2 0 ^^^ (program.constEntries 39).getD 3 0 ^^^
    (program.constEntries 39).getD 4 0) ∧
    (∀ i < 136, (program.constEntries 30).getD i 0 = 0) ∧
    (∀ i < 135, (program.constEntries 31).getD i 0 = 0) ∧
    (program.constEntries 31).getD 135 0 = (program.constEntries 39).getD 7 0 ∧
    (∀ v ∈ [0, 28, 29, 30, 31], program.isConstant v = true ∧ program.valueField v = 0) := by
  decide +kernel

/-- The views' sizes, decided. -/
theorem view_sizes :
    (program.value 97).size = 1600 ∧ (program.value 146).size = 1088 ∧
    (program.value 195).size = 1088 ∧ (program.value 244).size = 1088 ∧
    (program.value 293).size = 1088 ∧ (program.value 342).size = 1088 ∧
    (program.value 391).size = 1088 ∧ (program.value 440).size = 1088 ∧
    (program.value 489).size = 1088 ∧ (program.value 538).size = 1088 ∧
    (program.value 587).size = 592 ∧ 537 < program.exprs.length := by
  decide +kernel

/-- Facts of the views' selections, decided. -/
theorem view_sel :
    idx0.size = 100 ∧ idx1.size = 68 ∧ idx2.size = 37 ∧
    (∀ j < 100, idx0.entry j = j) ∧ (∀ j < 68, idx1.entry j = j) ∧ (∀ j < 37, idx2.entry j = j) ∧
    ∀ k : Fin 10, program.valueField (viewVal (k + 1)) = 0 ∧
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
    program.expr 53 = .reindex idx22 (.concat (.leaf 25) (.leaf 27)) ∧
    program.expr 54 = .add (.reindex idx23 (.ref 53)) (.reindex idx24 (.ref 53)) ∧
    program.expr 55 = .reindex idx5 (.leaf 95) ∧ program.expr 56 = .reindex idx5 (.leaf 97) ∧
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
    .reindex idx4 (.concat (.leaf 45) (.leaf 46)) ∧
    program.expr 1 = .reindex idx4 (.ref 0) ∧
    program.expr 2 =
    .reindex idx5 (.reindex idx5 (.concat (.reindex idx4 (.reindex idx4 (.ref 1))) (.leaf 0))) ∧
    program.expr 51 = .reindex idx19 (.concat (.leaf 25) (.reindex idx15 (.leaf 47))) ∧
    program.expr 52 = .apply (.sum 8) (.mul (.reindex idx4 (.reindex idx4 (.ref 1)))
    (.reindex idx20 (.leaf 28))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The stream's expression. -/
theorem expr537 :
    program.expr 537 =
    .reindex idx28 (RealizedProgram.concatR (.leaf 97)
      [.leaf 146, .leaf 195, .leaf 244, .leaf 293, .leaf 342, .leaf 391, .leaf 440, .leaf 489,
        .leaf 538, .leaf 587]) :=
  rfl

/-- The stream's index map, decided. -/
theorem idx28_entry : ∀ i < 717, ∀ b < 16, idx28.entry (16 * i + b) =
    (if i < 68 then 0 else 1600 + 1088 * (i / 68 - 1)) +
      (16 * (i % 68) + if b < 8 then b + 8 else b - 8) :=
  idx_stream_entry rfl

set_option maxRecDepth 4096 in
/-- The view kinds of the output views. -/
theorem view_kinds : ∀ k : Fin 10,
    (program.value (viewVal (k + 1))).kind =
        .bits (outVal (k + 1) 23 - 1) (if (k : ℕ) + 1 = 10 then idx2 else idx1) ∧
      (program.value (outVal (k + 1) 23)).kind = .bits (outVal (k + 1) 23 - 1) idx0 ∧
      (program.value (outVal (k + 1) 23 - 1)).kind = .priv := by
  intro k
  fin_cases k <;> exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The `h2p.shake` facts of the program of `Falcon512.Native.ROMParams`. -/
instance : FalconHHash program where
  shake_source := shake_source
  expr_squeezeIn := expr_squeezeIn
  squeezeIn_facts := squeezeIn_facts
  pred_padding := pred_padding
  flag_facts := flag_facts
  absorb_facts := absorb_facts
  expr_absorb := expr_absorb
  expr537 := expr537
  idx28_entry := idx28_entry
  view_sizes := view_sizes
  view_kinds := view_kinds
  view_sel := view_sel
  buf_facts := buf_facts

end GordieHowe.Falcon512.Native.ROMParams
