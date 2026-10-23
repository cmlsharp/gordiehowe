-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.Model.IOP.UniformTranscript

@[expose] public section

/-!
# Finite message types of the GKR schedule's protocols

The one-move protocols (`one`), the empty protocol, the sumcheck phase (`rounds`), the circuit phase
(`circuit`) and the GKR protocol (`spec`) have finite and nonempty message types over a finite
field. The uniform-simulator statements (`GordieHowe/Model/IOP/UniformTranscript.lean`) need them to speak
of a uniform full transcript.
-/

namespace GordieHowe.GKR.Schedule

open IOP IOP.ProtocolSpec

variable {F : Type} [Field F]

/-- The message type of a one-move protocol is finite when its message set is. -/
instance one_typeFintype {dir : Direction} {Msg : Type} [Fintype Msg] :
    ∀ i, Fintype ((one dir Msg).Type i) := fun _ => inferInstanceAs (Fintype Msg)

/-- The message type of a one-move protocol is nonempty when its message set is. -/
instance one_typeNonempty {dir : Direction} {Msg : Type} [Nonempty Msg] :
    ∀ i, Nonempty ((one dir Msg).Type i) := fun _ => inferInstanceAs (Nonempty Msg)

/-- The empty protocol has no message types. -/
instance empty_typeFintype : ∀ i, Fintype (empty.Type i) := fun i => i.elim0

/-- The empty protocol has no message types. -/
instance empty_typeNonempty : ∀ i, Nonempty (empty.Type i) := fun i => i.elim0

/-- The message types of the sumcheck phase are finite. -/
instance rounds_typeFintype [Fintype F] :
    (k : ℕ) → ∀ i, Fintype ((rounds F k).Type i)
  | 0 => fun i => i.elim0
  | k + 1 =>
    letI := rounds_typeFintype k
    inferInstanceAs (∀ i, Fintype ((one .P_to_V (F × F) ++ (one .V_to_P F ++ rounds F k)).Type i))

/-- The message types of the sumcheck phase are nonempty. -/
instance rounds_typeNonempty : (k : ℕ) → ∀ i, Nonempty ((rounds F k).Type i)
  | 0 => fun i => i.elim0
  | k + 1 =>
    haveI := rounds_typeNonempty k
    haveI : Nonempty F := ⟨0⟩
    inferInstanceAs (∀ i, Nonempty ((one .P_to_V (F × F) ++ (one .V_to_P F ++ rounds F k)).Type i))

/-- The message types of the circuit phase are finite. -/
instance circuit_typeFintype [Fintype F] {d : ℕ} :
    (C : Circuit F d) → ∀ i, Fintype ((circuit F C).Type i)
  | .input _ => inferInstanceAs (∀ i, Fintype ((one .V_to_P F).Type i))
  | .layer (inDim := b) _ tail =>
    letI := circuit_typeFintype tail
    inferInstanceAs (∀ i, Fintype ((one .V_to_P (F × F) ++
      (rounds F (2 * b) ++ (one .P_to_V (F × F) ++ circuit F tail))).Type i))

/-- The message types of the circuit phase are nonempty. -/
instance circuit_typeNonempty {d : ℕ} :
    (C : Circuit F d) → ∀ i, Nonempty ((circuit F C).Type i)
  | .input _ =>
    haveI : Nonempty F := ⟨0⟩
    inferInstanceAs (∀ i, Nonempty ((one .V_to_P F).Type i))
  | .layer (inDim := b) _ tail =>
    haveI := circuit_typeNonempty tail
    haveI : Nonempty F := ⟨0⟩
    inferInstanceAs (∀ i, Nonempty ((one .V_to_P (F × F) ++
      (rounds F (2 * b) ++ (one .P_to_V (F × F) ++ circuit F tail))).Type i))

/-- The message types of the GKR protocol are finite. -/
instance spec_typeFintype [Fintype F] {d : ℕ} (C : Circuit F d) :
    ∀ i, Fintype ((spec F C).Type i) :=
  inferInstanceAs (∀ i, Fintype ((one .V_to_P (Fin d → F) ++ circuit F C).Type i))

/-- The message types of the GKR protocol are nonempty. -/
instance spec_typeNonempty {d : ℕ} (C : Circuit F d) :
    ∀ i, Nonempty ((spec F C).Type i) :=
  haveI : Nonempty F := ⟨0⟩
  inferInstanceAs (∀ i, Nonempty ((one .V_to_P (Fin d → F) ++ circuit F C).Type i))

end GordieHowe.GKR.Schedule
