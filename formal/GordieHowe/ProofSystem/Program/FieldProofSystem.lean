-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldForkHonest
public import GordieHowe.ProofSystem.Program.ForkProofSystem

@[expose] public section

/-!
# GordieHowe: a proof system on the generic per-field domain proofs

A proof system of a valid realized program (`GordieHowe.RealizedProgram.ProofSystem`) with every domain's circuit proof the
generic per-field one (`GordieHowe.RealizedProgram.fieldProof`) at the domain's ready data (`GordieHowe.RealizedProgram.FieldReady`):

* **the proof system** (`GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs`): a program's checks, the model of its interpretation
  and its GKR sources, every domain's circuit proof `fieldProof` at its ready data and its soundness
  `fieldSound`; a proof system's validity facts and GKR sources with those proofs
  (`GordieHowe.RealizedProgram.ProofSystem.withFieldProofs`);
* **the domains' honest provers** (`GordieHowe.RealizedProgram.ProofSystem.fieldHonestDomains`): every domain's `fieldHonest`;
* **the forked domains** (`GordieHowe.RealizedProgram.ProofSystem.fieldBranches`): every domain's forked circuit proof, its
  soundness and the reading of its oracle message (`fieldForkSound`), and their honest provers
  (`GordieHowe.RealizedProgram.ProofSystem.fieldForkHonestDomains`, `fieldForkHonest`).
-/

namespace GordieHowe.RealizedProgram

open Export

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp}

/-- **The proof system of a program on the generic per-field domain proofs**: the program's checks
`checks` at the opaque ranges `orng`, the model `model` of the interpretation, the GKR sources
`src`, and every domain's circuit proof `fieldProof` at its ready data `R d` (its soundness:
`ofFieldProofsSound`). -/
def ofFieldProofs {orng : List (ℕ × ℕ)} (checks : ir.Checks P orng)
    (model : I.Model P ir orng) (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
    (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P) : ir.ProofSystem P I where
  opaqueRanges := orng
  checks := checks
  model := model
  src := src
  proof d := ir.fieldProof src (R d)

/-- **The soundness of the domain proofs of `ofFieldProofs`**: every domain's `fieldSound`. -/
noncomputable def ofFieldProofsSound {orng : List (ℕ × ℕ)} (checks : ir.Checks P orng)
    (model : I.Model P ir orng) (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
    (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P) :
    (ofFieldProofs checks model src R).Sound := fun d =>
  ir.fieldSound src (R d)

end ProofSystem

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp}

variable (B : ir.ProofSystem P I) (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)

/-- **A proof system on the generic per-field domain proofs**: `B`'s validity facts and GKR sources,
every domain's circuit proof `fieldProof` at its ready data `R d` (`ofFieldProofs`; its soundness
`withFieldProofsSound`). A proof system built by `ofFieldProofs` at `R` is its own
`withFieldProofs R`. -/
def withFieldProofs : ir.ProofSystem P I :=
  ofFieldProofs B.checks B.model B.src R

/-- **The soundness of `withFieldProofs`**: every domain's `fieldSound` (`ofFieldProofsSound`). -/
noncomputable def withFieldProofsSound : (B.withFieldProofs R).Sound :=
  ofFieldProofsSound B.checks B.model B.src R

/-- **The domains' simulator data of the proof system** (`fieldSim`). -/
def fieldSims : (B.withFieldProofs R).DomainSims := fun d => ir.fieldSim B.src (R d)

/-- **The domains' honest provers of the proof system** (`fieldHonest`), from the compiler's
completeness, simulated by `fieldSims`. -/
noncomputable def fieldHonestDomains : (B.withFieldProofs R).HonestDomains (B.fieldSims R) := fun TA d =>
  ir.fieldHonest B.src (R d) TA fun _ _ _ h => h

/-- **The forked domain proofs of the proof system**: every domain's forked circuit proof and the
reading of its oracle message (their soundness: `fieldBranchesSound`). -/
def fieldBranches : (B.withFieldProofs R).FieldBranches where
  fork d := ir.fieldForkShape B.src (R d)
  oracle d := ir.fieldForkOracle B.src (R d)

/-- **The soundness of the forked domain proofs of the proof system** (`fieldForkFull`). -/
noncomputable def fieldBranchesSound : (B.fieldBranches R).Sound := fun d =>
  ir.fieldForkFull B.src (R d)

/-- **The simulators of the forked domains** (`fieldForkSim`).

Running time: that of `fieldForkSim` at each domain. This running time is argued here, not proved
in Lean. -/
def fieldForkSims : (B.fieldBranches R).ForkSims := fun d => ir.fieldForkSim B.src (R d)

/-- **The honest provers of the forked domains** (`fieldForkHonest`) on the domains' honest inputs of
`fieldHonestDomains`, simulated by `fieldForkSims`. `TA`: the compiler's completeness (trust base). -/
noncomputable def fieldForkHonestDomains (TA : (B.withFieldProofs R).CircuitsAccept) :
    ∀ d, (B.fieldBranches R).ForkDomainHonest d (B.fieldHonestDomains R TA d).In
      (B.fieldHonestDomains R TA d).dom (B.fieldForkSims R d) := fun d =>
  { circuit := (ir.fieldForkHonest B.src (R d) TA).toShape
    accepts := (ir.fieldForkHonest B.src (R d) TA).accepts
    perfect := (ir.fieldForkHonest B.src (R d) TA).perfect }

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The honest prover of the protocol with forked domains on the generic per-field domain proofs**
at the honest prover `H` (`FieldBranches.honest` at `fieldHonestDomains` and `fieldForkHonestDomains`).
`TA`: the compiler's completeness (trust base). -/
noncomputable abbrev fieldForkHonest (TA : (B.withFieldProofs R).CircuitsAccept)
    (H : ir.HonestCore I relH) :
    (B.fieldBranches R).protocol.Honest ((B.fieldBranches R).simData (B.fieldForkSims R)) Inp relH :=
  (B.fieldBranches R).honest TA (B.fieldHonestDomains R) (B.fieldForkHonestDomains R TA) H

end ProofSystem

end GordieHowe.RealizedProgram
