-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Native.HonestValues
public import GordieHowe.Language.Honest.SourceRoles
public import GordieHowe.Applications.MLDSA44.Honest.AlgebraSourceRoles

public section

namespace GordieHowe.MLDSA44.Native
open RealizedProgram
variable {program : RealizedProgram} [MldsaAAlgebra program] [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [QField F0] [HField FH]
  [MldsaHConsts program FH] [MldsaHNativeData FH] [MldsaHNodes FH]
  [MldsaNativeHonest program F0 FH]
set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

omit [MldsaAAlgebra program] [QField F0] [MldsaHNodes FH]
  [MldsaNativeHonest program F0 FH] in
/-- **A bound source reads its committed digits through the existing source reader.** -/
theorem native_execOf_bound (i : MLDSA44.HonestInput) (x : program.Valuation interp) {v : Nat} {e : Expr}
    (hk : (program.value v).kind = .bound e) (j : Nat) :
    castElt (b := 0) (program.execOf interp (honestVal program F0 FH i) v j) =
      rdA (program.srcEnv interp x (honestVal program F0 FH i) (program.chal0 interp) 0) v j := by
  rw [execOf_bound_eq_reader (honestVal program F0 FH i)
    (program.srcEnv interp x (honestVal program F0 FH i) (program.chal0 interp) 0) rfl hk]
  exact (RealizedProgram.evalE_leaf _ _ _ _).symm


/-- **The source `z` equals the honest centered coefficient.** -/
theorem native_execOf_z (i : MLDSA44.HonestInput) (x : program.Valuation interp)
    {j : Nat} (hj : j < 1024) :
    castElt (b := 0) (program.execOf interp (honestVal program F0 FH i) 57 j) =
      ((MLDSA44.NativeAlgebraCircuit.flat
        (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz j hj) : Int) :
          (interp 0).K) := by
  rw [native_execOf_bound i x (MldsaNativeHonest.a_kinds (program := program)).1]
  exact rdA_58 i hj

/-- **The source offset equals the honest UseHint offset.** -/
theorem native_execOf_offset (i : MLDSA44.HonestInput) (x : program.Valuation interp)
    {j : Nat} (hj : j < 1024) :
    castElt (b := 0) (program.execOf interp (honestVal program F0 FH i) 64 j) =
      ((offN i (fm j hj) : Nat) : (interp 0).K) := by
  rw [native_execOf_bound i x (MldsaNativeHonest.a_kinds (program := program)).2.1]
  exact rdA_65 hj

/-- **The source slack equals the honest UseHint slack.** -/
theorem native_execOf_slack (i : MLDSA44.HonestInput) (x : program.Valuation interp)
    {j : Nat} (hj : j < 1024) :
    castElt (b := 0) (program.execOf interp (honestVal program F0 FH i) 65 j) =
      ((slN i (fm j hj) : Nat) : (interp 0).K) := by
  rw [native_execOf_bound i x (MldsaNativeHonest.a_kinds (program := program)).2.2]
  exact rdA_66 hj


/-- **A private algebra source retains its existing honest value.** -/
theorem native_execOf_private (i : MLDSA44.HonestInput) {v : Nat}
    (hv : v ∈ AValues) (j : Nat) :
    castElt (b := 0) (program.execOf interp (honestVal program F0 FH i) v j) =
      aVal F0 i v j := by
  rw [execOf_of_priv _ (kind_of_privCellB ((MldsaNativeHonest.a_cells (program := program)) v hv).1)]
  exact honestVal_a i v hv j


set_option hygiene false in
local notation "algebraInputs" => ({
  z := fun j => if h : j < 1024 then
    ((MLDSA44.NativeAlgebraCircuit.flat
      (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz j h) : Int) : F0.K) else 0
  hint := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).h (fm j h) else 0
  challenge := fun j => if h : j < 512 then
    (nativeA F0 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ else 0
  w := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).w (fm j h) else 0
  w1 := fun j => if h : j < 6144 then MLDSA44.NativeAlgebraCircuit.outputBits (nativeA F0 i).w1A
    ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ else 0
  nonpositive := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).np (fm j h) else 0
  offset := fun j => if h : j < 1024 then ((offN i (fm j h) : Nat) : F0.K) else 0
  slack := fun j => if h : j < 1024 then ((slN i (fm j h) : Nat) : F0.K) else 0
} : AlgebraSourceValues F0.K)

variable (i : MLDSA44.HonestInput)

/-- **The checked `z` role gives the existing source execution value.** -/
theorem native_role_z {classifier : SourceRoleClassifier}
    (h : classifier.lookup 57 = some (.aWitness, 0)) {j : Nat} (hj : j < 1024) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 57 j =
      program.execOf interp (honestVal program F0 FH i) 57 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_z, dite_eq_left hj]
  have hf : program.valueField 57 = 0 := (MldsaNativeHonest.a_bound (program := program)).1
  have he := native_execOf_z (program := program) (F0 := F0) (FH := FH) i (fun _ _ => 0) hj
  have hc := congrArg (castElt (b := program.valueField 57)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `hint` role gives the existing source execution value.** -/
theorem native_role_hint {classifier : SourceRoleClassifier}
    (h : classifier.lookup 58 = some (.aWitness, 1)) {j : Nat} (hj : j < 1024) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 58 j =
      program.execOf interp (honestVal program F0 FH i) 58 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_hint, dite_eq_left hj]
  have hv : 58 ∈ AValues := by decide
  have hf : program.valueField 58 = 0 := ((MldsaNativeHonest.a_cells (program := program)) 58 hv).2
  have he := native_execOf_private (program := program) (F0 := F0) (FH := FH) i hv j
  rw [aVal_59 i hj] at he
  have hc := congrArg (castElt (b := program.valueField 58)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `challenge` role gives the existing source execution value.** -/
theorem native_role_challenge {classifier : SourceRoleClassifier}
    (h : classifier.lookup 59 = some (.aWitness, 2)) {j : Nat} (hj : j < 512) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 59 j =
      program.execOf interp (honestVal program F0 FH i) 59 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_challenge, dite_eq_left hj]
  have hv : 59 ∈ AValues := by decide
  have hf : program.valueField 59 = 0 := ((MldsaNativeHonest.a_cells (program := program)) 59 hv).2
  have he := native_execOf_private (program := program) (F0 := F0) (FH := FH) i hv j
  rw [aVal_60 i hj] at he
  have hc := congrArg (castElt (b := program.valueField 59)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `w` role gives the existing source execution value.** -/
theorem native_role_w {classifier : SourceRoleClassifier}
    (h : classifier.lookup 60 = some (.aWitness, 3)) {j : Nat} (hj : j < 1024) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 60 j =
      program.execOf interp (honestVal program F0 FH i) 60 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_w, dite_eq_left hj]
  have hv : 60 ∈ AValues := by decide
  have hf : program.valueField 60 = 0 := ((MldsaNativeHonest.a_cells (program := program)) 60 hv).2
  have he := native_execOf_private (program := program) (F0 := F0) (FH := FH) i hv j
  rw [aVal_61 i hj] at he
  have hc := congrArg (castElt (b := program.valueField 60)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `w1` role gives the existing source execution value.** -/
theorem native_role_w1 {classifier : SourceRoleClassifier}
    (h : classifier.lookup 62 = some (.aWitness, 4)) {j : Nat} (hj : j < 6144) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 62 j =
      program.execOf interp (honestVal program F0 FH i) 62 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_w1, dite_eq_left hj]
  have hv : 62 ∈ AValues := by decide
  have hf : program.valueField 62 = 0 := ((MldsaNativeHonest.a_cells (program := program)) 62 hv).2
  have he := native_execOf_private (program := program) (F0 := F0) (FH := FH) i hv j
  rw [aVal_63 i hj] at he
  have hc := congrArg (castElt (b := program.valueField 62)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `nonpositive` role gives the existing source execution value.** -/
theorem native_role_nonpositive {classifier : SourceRoleClassifier}
    (h : classifier.lookup 63 = some (.aWitness, 5)) {j : Nat} (hj : j < 1024) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 63 j =
      program.execOf interp (honestVal program F0 FH i) 63 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_nonpositive, dite_eq_left hj]
  have hv : 63 ∈ AValues := by decide
  have hf : program.valueField 63 = 0 := ((MldsaNativeHonest.a_cells (program := program)) 63 hv).2
  have he := native_execOf_private (program := program) (F0 := F0) (FH := FH) i hv j
  rw [aVal_64 i hj] at he
  have hc := congrArg (castElt (b := program.valueField 63)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `offset` role gives the existing source execution value.** -/
theorem native_role_offset {classifier : SourceRoleClassifier}
    (h : classifier.lookup 64 = some (.aWitness, 6)) {j : Nat} (hj : j < 1024) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 64 j =
      program.execOf interp (honestVal program F0 FH i) 64 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_offset, dite_eq_left hj]
  have hf : program.valueField 64 = 0 := (MldsaNativeHonest.a_bound (program := program)).2.1
  have he := native_execOf_offset (program := program) (F0 := F0) (FH := FH) i (fun _ _ => 0) hj
  have hc := congrArg (castElt (b := program.valueField 64)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

/-- **The checked `slack` role gives the existing source execution value.** -/
theorem native_role_slack {classifier : SourceRoleClassifier}
    (h : classifier.lookup 65 = some (.aWitness, 7)) {j : Nat} (hj : j < 1024) :
    (algebraInputs).valuation (program := program) (I := interp) classifier 65 j =
      program.execOf interp (honestVal program F0 FH i) 65 j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ h]
  simp only [AlgebraSourceValues.meaning_slack, dite_eq_left hj]
  have hf : program.valueField 65 = 0 := (MldsaNativeHonest.a_bound (program := program)).2.2.1
  have he := native_execOf_slack (program := program) (F0 := F0) (FH := FH) i (fun _ _ => 0) hj
  have hc := congrArg (castElt (b := program.valueField 65)) he
  rw [castElt_castElt_of_eq hf] at hc
  exact hc.symm

end GordieHowe.MLDSA44.Native
