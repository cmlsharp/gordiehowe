-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.Honest
public import GordieHowe.Language.Honest.SourceRoles

public section

namespace GordieHowe.Falcon512.Ring.Carrier

open RealizedProgram

/-- **The witness components read by the carrier's source-role interpreter.**
The field is a parameter; the record contains only computational values and functions. -/
structure SourceValues (K : Type) where
  spectrum : ℕ → K
  signer : ℕ
  s2 : ℕ → ℕ
  s1 : ℕ → ℕ
  quotient : ℕ → ℕ
  mag1 : ℕ → ℕ
  mag2 : ℕ → ℕ
  squares : ℕ

/-- **Interpret a declared carrier role and slot.** Statement values are supplied separately
by the execution's statement. Unused tags and slots contribute zero. -/
@[expose] def SourceValues.meaning {K : Type} [Semiring K] (s : SourceValues K) :
    SourceRole → ℕ → ℕ → K
  | .ringSigma, 0, j => if j < 512 then s.spectrum j else 0
  | .selection, 0, j => (s.signer / 2 ^ j % 2 : ℕ)
  | .aWitness, 0, j => (s.s2 j : ℕ)
  | .aWitness, 1, j => (s.s1 j : ℕ)
  | .aWitness, 2, j => (s.mag1 j : ℕ)
  | .aWitness, 3, j => (s.mag2 j : ℕ)
  | .aWitness, 4, j => (s.mag2 j % 128 : ℕ)
  | .carry, 0, j => (s.quotient j : ℕ)
  | .carry, 1, j => if j = 0 then (s.squares : ℕ) else 0
  | _, _, _ => 0

/-- **Assign source values through the shared, already constructed classifier.**
The interpreter does not inspect the program's syntax or reconstruct the role table. -/
@[expose] def SourceValues.valuation {program : RealizedProgram} {I : Interp}
    (s : SourceValues (I 0).K) (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => castElt (s.meaning role slot j)
    | none => 0

/-- **A named lookup fixes the witness component read by the valuation.** -/
theorem SourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    (s : SourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : ℕ}
    {role : SourceRole} {slot : ℕ} (h : classifier.lookup v = some (role, slot)) (j : ℕ) :
    s.valuation (program := program) classifier v j = castElt (s.meaning role slot j) := by
  simp only [valuation, h]

/-- **An absent source-role entry contributes zero.** -/
theorem SourceValues.valuation_of_none {program : RealizedProgram} {I : Interp}
    (s : SourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : ℕ}
    (h : classifier.lookup v = none) (j : ℕ) :
    s.valuation (program := program) classifier v j = 0 := by
  simp only [valuation, h]

end GordieHowe.Falcon512.Ring.Carrier

namespace GordieHowe.Falcon512.Ring
open RealizedProgram
variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] [FalconCarrierHonest program]
  [FalconRingRoleFacts program] {I : Interp} [EField (I 0)]
  {msgLen : Nat} {G : Native.Signer msgLen}
attribute [local instance] ringField_carrier

omit [FalconCarrierBase program] [FalconCarrierHonest program]
  [FalconRingRoleFacts program] [EField (I 0)] in
/-- **A carrier bound value reads its committed digits in the source environment.** -/
theorem carrier_execOf_bound (y : RingIn G) {v : Nat} {x : Expr}
    (hk : (program.value v).kind = .bound x) (j : Nat) :
    castElt (program.execOf I (honestVal program I y) v j) =
      rdC (program.srcEnv I (stmtOf y.x) (honestVal program I y) (program.chal0 I) 0) v j := by
  rw [execOf_bound_eq_reader (honestVal program I y)
    (program.srcEnv I (stmtOf y.x) (honestVal program I y) (program.chal0 I) 0) rfl hk]
  exact (RealizedProgram.evalE_leaf _ _ _ _).symm

/-- **The bound quotient equals the direct witness quotient.** -/
theorem carrier_execOf_quot (y : RingIn G) {j : Nat} (hj : j < 512) :
    castElt (program.execOf I (honestVal program I y) 11 j) =
      ((Carrier.quot y.normIn j : Nat) : (I 0).K) := by
  rw [carrier_execOf_bound y FalconCarrierHonest.quotKind]
  exact rd_quot y hj

/-- **The bound magnitude equals the direct witness magnitude.** -/
theorem carrier_execOf_mag1 (y : RingIn G) {j : Nat} (hj : j < 512) :
    castElt (program.execOf I (honestVal program I y) 12 j) =
      ((Carrier.mag1 y.normIn j : Nat) : (I 0).K) := by
  rw [carrier_execOf_bound y FalconCarrierHonest.mag1Kind]
  exact rd_mag1 y hj

/-- **The bound squared norm equals the direct witness squared norm.** -/
theorem carrier_execOf_squares (y : RingIn G) :
    castElt (program.execOf I (honestVal program I y) 16 0) =
      ((Carrier.squares y.normIn : Nat) : (I 0).K) := by
  rw [carrier_execOf_bound y FalconCarrierHonest.sqKind]
  exact rd_sq y
end GordieHowe.Falcon512.Ring
