-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.SourceRoles

public section
namespace GordieHoweTest.SourceRoles
open GordieHowe GordieHowe.RealizedProgram

@[expose] def program : RealizedProgram where
  phases := 0
  fields := []
  domains := []
  values := [
    { name := "witness", shape := [1], kind := .priv, type := .field,
      node := some ⟨"A", 0⟩ },
    { name := "input", shape := [1], kind := .pub .input, type := .field },
    { name := "generated", shape := [1], kind := .priv, type := .field,
      role := .realization 0 }]
  predicates := []

@[expose] def witness : SourceRoleEntry := ⟨0, .aWitness, 3, 0, some ⟨"A", 0⟩⟩
@[expose] def input : SourceRoleEntry := ⟨1, .input, 0, 0, none⟩

example : program.sourceRolesB [witness] = true := by decide +kernel
example : program.sourceRolesB [witness, input] = true := by decide +kernel
example : program.sourceRolesB [] = false := by decide +kernel
example : program.sourceRolesB [input] = false := by decide +kernel
example : program.sourceRolesB [witness, witness] = false := by decide +kernel
example : program.sourceRolesB [input, witness] = false := by decide +kernel
example : program.sourceRolesB [{ witness with field := 1 }] = false := by decide +kernel
example : program.sourceRolesB [{ witness with node := some ⟨"B", 0⟩ }] = false := by decide +kernel
example : program.sourceRolesB [{ witness with node := some ⟨"A", 1⟩ }] = false := by decide +kernel
example : program.sourceRolesB [witness, { input with value := 2 }] = false := by decide +kernel
example : program.sourceRolesB [witness, { input with value := 3 }] = false := by decide +kernel
example : SourceRolesOk program [witness] := sourceRoles_sound (by decide +kernel)
example : (sourceRoleClassifier [witness]).lookup 0 = some (.aWitness, 3) :=
  (sourceRoles_sound (ir := program) (rs := [witness]) (by decide +kernel)).lookup_at (k := 0) rfl

example : (sourceRoleClassifier [witness]).lookup 0 = some (.aWitness, 3) := by decide +kernel
example : (sourceRoleClassifier [witness]).lookup 0 ≠ some (.aWitness, 0) := by decide +kernel
example : (sourceRoleClassifier [witness]).lookup 0 ≠ some (.hashWord, 3) := by decide +kernel
example : (sourceRoleClassifier [witness]).lookup 1 = none := by decide +kernel
example : (sourceRoleClassifier [input]).lookup 1 = some (.input, 0) := by decide +kernel

/-- Source execution assigns bound values before completion generates their digits. -/
@[expose] def boundProgram : RealizedProgram :=
  { program with values := program.values ++
      [{ name := "bound", shape := [1], kind := .bound (.leaf 0), type := .field }] }
@[expose] def boundWitness : SourceRoleEntry := ⟨3, .carry, 0, 0, none⟩
example : boundProgram.sourceRolesB [witness] = false := by decide +kernel
example : boundProgram.sourceRolesB [witness, boundWitness] = true := by decide +kernel

example : sourceRolesPartB program none = true := by decide +kernel
example : sourceRolesPartB program (some []) = false := by decide +kernel
example : sourceRolesPartB program (some [witness]) = true := by decide +kernel
example : SourceRolesPartOk program (some [witness]) :=
  sourceRolesPart_sound (by decide +kernel)

-- The optional contract is eliminated through its public API, without unfolding it.
example : SourceRolesOk program [witness] :=
  (sourceRolesPart_sound (ir := program) (rs := some [witness]) (by decide +kernel)).present rfl

end GordieHoweTest.SourceRoles
