-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.Interp
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the proof system of `Falcon512.Ring.Native.ROMParams`

The security theorem of the proof system at the realized program of the native Falcon ring at the ROM parameters
(`GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Program.program`, export `b65a4929`: one domain `A` with
the batches `norm.center`, `norm.column0`, `norm.column1` and `norm.column2`, one
phase with the challenges `member.ring.gamma` and `alpha:A`, the lookup tables `A.64` of three
groups and `A.189` of two, no late value), at the GKR sources `src` of its circuit:

* **the ready data** (`ready`): domain `A`'s packing facts (`fq9Packing`), the tableau
  `GordieHowe.RealizedProgram.falconRingNativeROMACert` and the checks `fieldOkA` (`GordieHowe.RealizedProgram.fieldOkB`, by
  `decide +kernel`);
* **the proof system** (`proofSystem`): the validity facts (the program's checks:
  `GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Valid.valid`, `GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Realize.derivable`,
  `sourceValid`, `cellsValid` and `locality` by `decide +kernel`; the model of the interpretation
  `interpModel`, from the field's model) and domain `A`'s circuit proof under the compiler trust,
  the generic per-field domain proof at `ready` (`GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs`), defined without the
  trust bundle;
* **the headlines** (`iop_completeness`, `iop_hvzk`, in the series–parallel order through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk`; soundness through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness`): the proof system's, the domain's
  honest prover being the generic per-field one (`GordieHowe.RealizedProgram.ProofSystem.fieldHonestDomains`), from the compiler's
  completeness alone;
* **the round errors** (`GordieHowe.RealizedProgram.phaseError`, `phaseError_le`): at the phase's challenge round, the
  source protocol `Π_P₀`'s round error at its one challenge `member.ring.gamma` (`alpha:A` is a
  realization challenge) and LogUp's `15610 / (12289^9 − 189)` (`GordieHowe.RealizedProgram.realError_eq`: the groups'
  `N_g + T − 1`, `(4096 + 63) + (4096 + 63) + (1733 + 63)` for `A.64` and
  `(4096 + 188) + (1024 + 188)` for `A.189`); at domain `A`'s rounds, the round charges of the
  generic per-field domain proof (`GordieHowe.RealizedProgram.FieldRoundsLe`, `GordieHowe/Applications/Falcon512/Ring/Native/ROMParams/Transcript.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
open Generated.Falcon512.Ring.Native.ROMParams.Program (program)
open scoped NNReal

/-! ## The validity facts -/

/-- **The model of the interpretation** (`Interp.Model.of_models`): every field identifier is
`F_q^9` with its model at `GF(p^1)`; the name and characteristic, the plan's prime-subfield node and
the absence of node-typed `Bit` values by `decide`; the opaque functions are `0`; no MAC tail, no
field-form `mod_q`. -/
theorem interpModel :
    interpROM.Model Generated.Falcon512.Ring.Native.ROMParams.Plan.plan program [] :=
  .of_models (RealizedProgram.Interp.models_const RealizedProgram.fq9_model)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (RealizedProgram.Interp.opaqueBit_of_lt_two fun _ _ _ => Nat.zero_lt_two)
    (RealizedProgram.Interp.macModel_of_noTail (by decide +kernel))
    (RealizedProgram.Interp.fieldFormModel_of_none (by decide +kernel))

/-- **The cells checks** (`RealizedProgram.CellsValid`): a domain, every field `equal` lowered into `A`,
the five groups' LogUp identities in `c.A`, every node-typed value a committed value of `A`. -/
theorem cellsValid : program.CellsValid := by decide +kernel

/-- **The domain is local** (`RealizedProgram.Local`): every predicate of `A` reads only `A`, by the
checker (`RealizedProgram.Local.of_localB`). -/
theorem locality :
    program.Local (RealizedProgram.treeNodesOf Generated.Falcon512.Ring.Native.ROMParams.Plan.plan program) :=
  RealizedProgram.Local.of_localB Generated.Falcon512.Ring.Native.ROMParams.Valid.wellFormed
    (by decide +kernel)

/-- **The source part is well formed** (`RealizedProgram.SourceValid`): the source predicates read only
source values, the source values are computed only from source values and read from the run only
the source challenge `member.ring.gamma`. -/
theorem sourceValid : program.SourceValid := by decide +kernel

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interpROM c)

/-! ## The proof system -/

/-- The program has one domain. -/
theorem domains_length : program.domains.length = 1 := by decide

/-- Domain `A`'s packing facts. -/
abbrev fieldPkA : (interpROM.field (program.domainField 0)).Packing := RealizedProgram.fq9Packing

/-- **Domain `A`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkA : program.fieldOkB (I := interpROM) 0
    Generated.Falcon512.Ring.Native.ROMParams.Plan.plan fieldPkA RealizedProgram.falconRingNativeROMACert = true := by
  decide +kernel

/-- **The ready data of the domain.** -/
def ready :
    ∀ d : Fin program.domains.length,
      program.FieldReady interpROM d Generated.Falcon512.Ring.Native.ROMParams.Plan.plan
  | ⟨0, _⟩ => ⟨fieldPkA, RealizedProgram.falconRingNativeROMACert, fieldOkA,
      Generated.Falcon512.Ring.Native.ROMParams.Valid.wellFormed⟩
  | ⟨_ + 1, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The proof system of `Falcon512.Ring.Native.ROMParams`** at the GKR sources `src`: the validity facts and
every domain's circuit proof under the compiler trust, the generic per-field domain proof at
`ready` (`RealizedProgram.ProofSystem.ofFieldProofs`). -/
def proofSystem :
    program.ProofSystem Generated.Falcon512.Ring.Native.ROMParams.Plan.plan interpROM :=
  RealizedProgram.ProofSystem.ofFieldProofs
    ⟨Generated.Falcon512.Ring.Native.ROMParams.Valid.valid,
      Generated.Falcon512.Ring.Native.ROMParams.Realize.derivable,
      sourceValid, cellsValid, locality⟩
    interpModel src ready

/-- **The domains' honest provers of the proof system** (`RealizedProgram.ProofSystem.fieldHonestDomains`), from the
compiler's completeness. -/
noncomputable def honestProofSystem :
    (proofSystem src).HonestDomains ((proofSystem src).fieldSims ready) :=
  (proofSystem src).fieldHonestDomains ready

/-! ## The round errors -/

/-- Domain `A`, as an index of the program's domains. -/
abbrev domainA : Fin program.domains.length := ⟨0, by decide⟩

/-! ## The headlines -/

variable {Inp : Type} {relH : Set (program.Valuation interpROM × Inp)}

/-- **Completeness of `Falcon512.Ring.Native.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
the forked domains `RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`, the domains' honest provers `honestProofSystem`): in the
series–parallel order of `prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement)
(`hc`), then at every value of the coins, on every honest input, the honest prover is rejected with
probability at most `errc`. `TA`: the program's GKR circuits accept honest inputs (trust base). -/
@[headline]
theorem iop_completeness (TA : (proofSystem src).CircuitsAccept) (H : program.HonestCore interpROM relH)
    {errc : program.Valuation interpROM → ℝ≥0} (hc : H.Complete errc) (c : ((proofSystem src).fieldForkHonest ready TA H).Coins) :
    CausalCompleteStmt relH ((proofSystem src).fieldBranches ready).protocol.verifier
      (fun y => RealizedProgram.ProofSystem.IOP.honest ((proofSystem src).fieldForkHonest ready TA H) y c) errc :=
  ((proofSystem src).fieldBranches ready).completeness TA (honestProofSystem src) _ H hc c

/-- **Honest-verifier zero knowledge of `Falcon512.Ring.Native.ROMParams` at the realized program**
(`RealizedProgram.ProofSystem.FieldBranches.hvzk` at the forked domains of `proofSystem`): in the series–parallel order of
`prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement) (`hc`), the simulator of the
series–parallel composite is honest-verifier zero knowledge for the honest prover with error `errc`.
`TA`: as for `iop_completeness` (trust base). -/
@[headline]
theorem iop_hvzk (TA : (proofSystem src).CircuitsAccept) (H : program.HonestCore interpROM relH) {errc : program.Valuation interpROM → ℝ≥0}
    (hc : H.Complete errc) :
    CausalHVZKStmt ((proofSystem src).fieldBranches ready).protocol.toCausalIOP.views relH
      (RealizedProgram.ProofSystem.IOP.honest ((proofSystem src).fieldForkHonest ready TA H)) id
      (RealizedProgram.ProofSystem.IOP.simulator
        (((proofSystem src).fieldBranches ready).simData ((proofSystem src).fieldForkSims ready))) errc :=
  ((proofSystem src).fieldBranches ready).hvzk TA (honestProofSystem src) _ H hc

end GordieHowe.Falcon512.Ring.Native.ROMParams
