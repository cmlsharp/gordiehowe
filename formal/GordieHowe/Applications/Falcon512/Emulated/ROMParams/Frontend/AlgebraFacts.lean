-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.Frontend.Facts
public import GordieHowe.Language.RealizedProgram.Kinds

@[expose] public section

/-!
# GordieHowe frontend: the domain `A` facts of `Falcon512.Emulated.ROMParams`

The program facts of domain `A` that the emulated Falcon frontend reads (`FalconEAlg`) for
`GordieHowe.Generated.Falcon512.Emulated.ROMParams.Program.program` (export `5d9fe0d5`): the
predicate bodies by `rfl`, the tables by `decide`, and the values' kinds by the kernel through
`RealizedProgram.Kind.isPriv` and `RealizedProgram.Kind.opaque?`.
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open Generated.Falcon512.Emulated.ROMParams.Program (program)

/-- `crossing.c_A`, `s2`, `signature.s1`, `magnitudes.mag2` and `encoding.low2` are committed. -/
theorem privKinds : (program.value 595).kind = .priv ∧ (program.value 596).kind = .priv ∧
    (program.value 597).kind = .priv ∧ (program.value 599).kind = .priv ∧
    (program.value 600).kind = .priv := by
  -- The kinds read through `Kind.isPriv`, decided by the kernel.
  have h : ∀ v ∈ [595, 596, 597, 599, 600], (program.value v).kind.isPriv = true := by
    decide +kernel
  exact ⟨RealizedProgram.Kind.eq_priv_of_isPriv (h 595 (by simp)),
    RealizedProgram.Kind.eq_priv_of_isPriv (h 596 (by simp)),
    RealizedProgram.Kind.eq_priv_of_isPriv (h 597 (by simp)),
    RealizedProgram.Kind.eq_priv_of_isPriv (h 599 (by simp)),
    RealizedProgram.Kind.eq_priv_of_isPriv (h 600 (by simp))⟩

/-- `key.coefficients` is computed from `statement.hhat`. -/
theorem keyKind : (program.value 594).kind = .pub (.opaque "key.coefficients" [593]) :=
  RealizedProgram.Kind.eq_opaque_of_opaque? (by decide +kernel)

/-- `statement.hhat` is an opaque statement value of no argument. -/
theorem hhatKind : (program.value 593).kind = .pub (.opaque "statement.hhat" []) :=
  RealizedProgram.Kind.eq_opaque_of_opaque? (by decide +kernel)

/-- The program of `Falcon512.Emulated.ROMParams` has the emulated Falcon frontend's program facts
about domain `A`. -/
instance : FalconEAlg program where
  cA_eq := rfl
  s2_eq := rfl
  sig := ⟨_, rfl⟩
  magS1 := ⟨_, rfl⟩
  magS2 := ⟨_, rfl⟩
  normSum := ⟨_, rfl⟩
  rMag1 := ⟨_, rfl⟩
  rMag2 := ⟨_, rfl⟩
  rLow2 := ⟨_, rfl⟩
  rBudget := ⟨_, rfl⟩
  rNorm := ⟨_, rfl⟩
  high2 := ⟨_, rfl⟩
  inSource := by decide +kernel
  consts := by decide +kernel
  fields := by decide +kernel
  sizes := by decide +kernel
  privKinds := privKinds
  keyKind := keyKind
  hhatKind := hhatKind
  keyDeclared := by decide +kernel

/-- **Domain `A`'s obligation at `Falcon512.Emulated.ROMParams`** (`algebraSound`), at
`GF(2^128)` and Goldilocks². -/
theorem algebraSound :
    AlgebraSound (program := program) (FH := RealizedProgram.gf128) (FA := RealizedProgram.gold2) :=
  Emulated.algebraSound

end GordieHowe.Falcon512.Emulated.ROMParams
