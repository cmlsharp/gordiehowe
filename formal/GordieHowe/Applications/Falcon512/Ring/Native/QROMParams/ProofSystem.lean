-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Interp
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the proof system of `Falcon512.Ring.Native.QROMParams`

The security theorem of the proof system at the realized program of the native Falcon ring at the QROM parameters
(`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Program.program`, export `b65a4929`: one domain `A`, one
phase with the challenges `member.ring.gamma` and `alpha:A`, the lookup tables `A.64` (three
groups) and `A.189` (two groups), the batches `norm.center` and `norm.column1`, no late value), at the GKR sources `src`
of its circuit:

* **the ready data** (`ready`): domain `A`'s packing facts (`fq20Packing`), the tableau
  `fq20K271Cert` and the checks `fieldOkA` (`GordieHowe.RealizedProgram.fieldOkB`, by `decide +kernel`);
* **the proof system** (`proofSystem`): the validity facts (the program's checks:
  `GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Valid.valid`, `GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Realize.derivable`, `sourceValid`,
  `cellsValid` and `locality` by `decide +kernel`; the model of the interpretation `interpModel`,
  from the field's model) and domain `A`'s circuit proof under the compiler trust, the generic
  per-field domain proof at `ready` (`GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs`), defined without the trust bundle;
* **the headlines** (`iop_completeness`, `iop_hvzk`, in the series–parallel order through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk`; soundness through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness`): the proof system's, the domain's
  honest prover being the generic per-field one (`GordieHowe.RealizedProgram.ProofSystem.fieldHonestDomains`), from the compiler's
  completeness alone;
* **the round errors** (`GordieHowe.RealizedProgram.phaseError`, `phaseError_le`): at the
  phase's challenge round, `Π_P₀`'s round error at `member.ring.gamma` and LogUp's
  `15610 / (12289^20 − 189)` (`GordieHowe.RealizedProgram.realError_eq`: the five groups' `N_g + T − 1`,
  `4159 + 4159 + 1796 + 4284 + 1212`); at domain `A`'s rounds, the domain proof's round charges
  (`GordieHowe.RealizedProgram.FieldRoundsLe`: the batches' `82/|F|`, GKR, the combinations, the test and the column
  with the joint subfield term; `GordieHowe/Applications/Falcon512/Ring/Native/QROMParams/Transcript.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open scoped NNReal

/-! ## The validity facts -/

/-- **The model of the interpretation** (`Interp.Model.of_models`): every field identifier is
`F_q^20` with its model at `GF(p^1)`; the name and characteristic, the plan's prime-subfield node
and the absence of node-typed `Bit` values by `decide`; the opaque functions are `0`; no MAC tail,
no field-form `mod_q`. -/
theorem interpModel :
    interpQROM.Model Generated.Falcon512.Ring.Native.QROMParams.Plan.plan program [] :=
  .of_models (RealizedProgram.Interp.models_const RealizedProgram.fq20_model)
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
    program.Local (RealizedProgram.treeNodesOf Generated.Falcon512.Ring.Native.QROMParams.Plan.plan program) :=
  RealizedProgram.Local.of_localB Generated.Falcon512.Ring.Native.QROMParams.Valid.wellFormed
    (by decide +kernel)

/-- **The source part is well formed** (`RealizedProgram.SourceValid`). -/
theorem sourceValid : program.SourceValid := by decide +kernel

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interpQROM c)

/-! ## The proof system -/

/-- The program has one domain. -/
theorem domains_length : program.domains.length = 1 := by decide

/-- Domain `A`'s packing facts. -/
abbrev fieldPkA : (interpQROM.field (program.domainField 0)).Packing := RealizedProgram.fq20Packing

/-- **Domain `A`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkA : program.fieldOkB (I := interpQROM) 0
    Generated.Falcon512.Ring.Native.QROMParams.Plan.plan fieldPkA RealizedProgram.fq20K271Cert = true := by
  decide +kernel

/-- **The ready data of the domain.** -/
def ready :
    ∀ d : Fin program.domains.length,
      program.FieldReady interpQROM d Generated.Falcon512.Ring.Native.QROMParams.Plan.plan
  | ⟨0, _⟩ => ⟨fieldPkA, RealizedProgram.fq20K271Cert, fieldOkA,
      Generated.Falcon512.Ring.Native.QROMParams.Valid.wellFormed⟩
  | ⟨_ + 1, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The proof system of `Falcon512.Ring.Native.QROMParams`** at the GKR sources `src`: the validity facts and
every domain's circuit proof under the compiler trust, the generic per-field domain proof at
`ready` (`RealizedProgram.ProofSystem.ofFieldProofs`). -/
def proofSystem :
    program.ProofSystem Generated.Falcon512.Ring.Native.QROMParams.Plan.plan interpQROM :=
  RealizedProgram.ProofSystem.ofFieldProofs
    ⟨Generated.Falcon512.Ring.Native.QROMParams.Valid.valid,
      Generated.Falcon512.Ring.Native.QROMParams.Realize.derivable,
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

variable {Inp : Type} {relH : Set (program.Valuation interpQROM × Inp)}

/-- **Completeness of `Falcon512.Ring.Native.QROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
the forked domains `RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`, the domains' honest provers `honestProofSystem`): in the
series–parallel order of `prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement)
(`hc`), then at every value of the coins, on every honest input, the honest prover is rejected with
probability at most `errc`. `TA`: the program's GKR circuits accept honest inputs (trust base). -/
@[headline]
theorem iop_completeness (TA : (proofSystem src).CircuitsAccept) (H : program.HonestCore interpQROM relH)
    {errc : program.Valuation interpQROM → ℝ≥0} (hc : H.Complete errc) (c : ((proofSystem src).fieldForkHonest ready TA H).Coins) :
    CausalCompleteStmt relH ((proofSystem src).fieldBranches ready).protocol.verifier
      (fun y => RealizedProgram.ProofSystem.IOP.honest ((proofSystem src).fieldForkHonest ready TA H) y c) errc :=
  ((proofSystem src).fieldBranches ready).completeness TA (honestProofSystem src) _ H hc c

/-- **Honest-verifier zero knowledge of `Falcon512.Ring.Native.QROMParams` at the realized program**
(`RealizedProgram.ProofSystem.FieldBranches.hvzk` at the forked domains of `proofSystem`): in the series–parallel order of
`prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement) (`hc`), the simulator of the
series–parallel composite is honest-verifier zero knowledge for the honest prover with error `errc`.
`TA`: as for `iop_completeness` (trust base). -/
@[headline]
theorem iop_hvzk (TA : (proofSystem src).CircuitsAccept) (H : program.HonestCore interpQROM relH) {errc : program.Valuation interpQROM → ℝ≥0}
    (hc : H.Complete errc) :
    CausalHVZKStmt ((proofSystem src).fieldBranches ready).protocol.toCausalIOP.views relH
      (RealizedProgram.ProofSystem.IOP.honest ((proofSystem src).fieldForkHonest ready TA H)) id
      (RealizedProgram.ProofSystem.IOP.simulator
        (((proofSystem src).fieldBranches ready).simData ((proofSystem src).fieldForkSims ready))) errc :=
  ((proofSystem src).fieldBranches ready).hvzk TA (honestProofSystem src) _ H hc

end GordieHowe.Falcon512.Ring.Native.QROMParams
