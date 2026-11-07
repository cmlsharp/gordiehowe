-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.SelectionSourceRoles
public import GordieHoweCerts.Applications.MLDSA44.Honest.SampleInBall

public section

namespace GordieHowe.MLDSA44

open RealizedProgram

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [HField FH] [MldsaHConsts program FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "selectionInputs" => ({
  selected := jF FH i
  threshold := packWord (FH := FH) (lowF FH i)
  readValue := fun n => if h : n < 39 then ((honestMemW program F0 FH i).read ⟨n, h⟩).value else 0
  readOrigin := fun n => if h : n < 234 then
    ((honestMemW program F0 FH i).read ⟨n / 6, by change n / 6 < 39; omega⟩).origin ⟨n % 6, by omega⟩ else 0
  encoded := fun n => if h : n < 256 then (honestMemW program F0 FH i).cEnc ⟨n, h⟩ else 0
  finalOrigin := fun n => if h : n < 256 then (honestMemW program F0 FH i).finalOrigin ⟨n, h⟩ else 0
  unit := fun n => if h : n < 39 then
    MemoryShuffle.unit (samM program F0 FH).Θ ((honestMemW program F0 FH i).signs ⟨n, h⟩) else 0
  origin := fun n => if h : n < 39 then
    (samM program F0 FH).originOf ((honestMemW program F0 FH i).read ⟨n, h⟩).origin else 0
} : SelectionSourceValues FH.K)

variable (i : MLDSA44.HonestInput)

/-- **The checked `selected` role reads the existing honest selection value.** -/
theorem selection_role_selected {classifier : SourceRoleClassifier}
    (h : classifier.lookup 556 = some (.selection, 0)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 556 j =
      hVal program F0 FH i 556 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hf := (MldsaHSelHonest.sel_cells (program := program)).2.2.2.2.2.2.2.2.2.2.1
  have he := hVal_557 (program := program) (F0 := F0) (FH := FH) i 556 rfl j
  have hc := congrArg (castElt (b := program.valueField 556)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `threshold` role reads the existing honest selection value.** -/
theorem selection_role_threshold {classifier : SourceRoleClassifier}
    (h : classifier.lookup 557 = some (.selection, 1)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 557 j =
      hVal program F0 FH i 557 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hf := (MldsaHSelHonest.sel_cells (program := program)).2.2.2.1
  have he := hVal_558 (program := program) (F0 := F0) (FH := FH) i 557 rfl j
  have hc := congrArg (castElt (b := program.valueField 557)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `read_value` role reads the existing honest selection value.** -/
theorem selection_role_read_value {classifier : SourceRoleClassifier}
    (h : classifier.lookup 560 = some (.selection, 2)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 560 j =
      hVal program F0 FH i 560 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hv : 560 ∈ [560, 561, 562, 563, 564, 565] := by decide
  have hf := ((MldsaHSelHonest.mem_cells (program := program)).1 560 hv).2
  have he := hVal_mem (program := program) (F0 := F0) (FH := FH) i 560 hv j
  rw [memF_read_value i j] at he
  have hc := congrArg (castElt (b := program.valueField 560)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `read_origin` role reads the existing honest selection value.** -/
theorem selection_role_read_origin {classifier : SourceRoleClassifier}
    (h : classifier.lookup 561 = some (.selection, 3)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 561 j =
      hVal program F0 FH i 561 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hv : 561 ∈ [560, 561, 562, 563, 564, 565] := by decide
  have hf := ((MldsaHSelHonest.mem_cells (program := program)).1 561 hv).2
  have he := hVal_mem (program := program) (F0 := F0) (FH := FH) i 561 hv j
  rw [memF_read_origin i j] at he
  have hc := congrArg (castElt (b := program.valueField 561)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `encoded` role reads the existing honest selection value.** -/
theorem selection_role_encoded {classifier : SourceRoleClassifier}
    (h : classifier.lookup 562 = some (.selection, 4)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 562 j =
      hVal program F0 FH i 562 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hv : 562 ∈ [560, 561, 562, 563, 564, 565] := by decide
  have hf := ((MldsaHSelHonest.mem_cells (program := program)).1 562 hv).2
  have he := hVal_mem (program := program) (F0 := F0) (FH := FH) i 562 hv j
  rw [memF_encoded i j] at he
  have hc := congrArg (castElt (b := program.valueField 562)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `final_origin` role reads the existing honest selection value.** -/
theorem selection_role_final_origin {classifier : SourceRoleClassifier}
    (h : classifier.lookup 563 = some (.selection, 5)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 563 j =
      hVal program F0 FH i 563 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hv : 563 ∈ [560, 561, 562, 563, 564, 565] := by decide
  have hf := ((MldsaHSelHonest.mem_cells (program := program)).1 563 hv).2
  have he := hVal_mem (program := program) (F0 := F0) (FH := FH) i 563 hv j
  rw [memF_final_origin i j] at he
  have hc := congrArg (castElt (b := program.valueField 563)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `unit` role reads the existing honest selection value.** -/
theorem selection_role_unit {classifier : SourceRoleClassifier}
    (h : classifier.lookup 564 = some (.selection, 6)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 564 j =
      hVal program F0 FH i 564 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hv : 564 ∈ [560, 561, 562, 563, 564, 565] := by decide
  have hf := ((MldsaHSelHonest.mem_cells (program := program)).1 564 hv).2
  have he := hVal_mem (program := program) (F0 := F0) (FH := FH) i 564 hv j
  rw [memF_unit i j] at he
  have hc := congrArg (castElt (b := program.valueField 564)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `origin` role reads the existing honest selection value.** -/
theorem selection_role_origin {classifier : SourceRoleClassifier}
    (h : classifier.lookup 565 = some (.selection, 7)) (j : Nat) :
    (selectionInputs).valuation (program := program) (I := interp) classifier 565 j =
      hVal program F0 FH i 565 j := by
  rw [SelectionSourceValues.valuation_of_lookup _ h]
  have hv : 565 ∈ [560, 561, 562, 563, 564, 565] := by decide
  have hf := ((MldsaHSelHonest.mem_cells (program := program)).1 565 hv).2
  have he := hVal_mem (program := program) (F0 := F0) (FH := FH) i 565 hv j
  rw [memF_origin i j] at he
  have hc := congrArg (castElt (b := program.valueField 565)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

end GordieHowe.MLDSA44
