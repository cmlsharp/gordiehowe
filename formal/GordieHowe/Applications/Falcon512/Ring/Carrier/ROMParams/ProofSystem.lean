-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the proof system of `Falcon512.Ring.Carrier.ROMParams`

The security theorem of the proof system at the realized program of the Falcon ring carrier at the ROM parameters
(`GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Program.program`, export `b65a4929`: one domain `A` over
Goldilocks², one phase with the challenges `member.ring.gamma` and `alpha:A`, the lookup
tables `A.128` and `A.2048` of one group each, one batch `magnitudes.s2`, no late value), at the GKR
sources `src` of its circuit:

* **the ready data** (`ready`): domain `A`'s packing facts (`gold2Packing`), the tableau
  `gold2K512R2Cert` and the checks `fieldOkA` (`GordieHowe.RealizedProgram.fieldOkB`, by `decide +kernel`);
* **the proof system** (`proofSystem`): the validity facts (the program's checks:
  `GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Valid.valid`, `GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Realize.derivable`,
  `sourceValid`, `cellsValid` and `locality` by `decide +kernel`; the model of the interpretation
  `interpModel`, from the field's model) and domain `A`'s circuit proof under the compiler trust,
  the generic per-field domain proof at `ready` (`GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs`), defined without the
  trust bundle;
* **the headlines** (`iop_completeness`, `iop_hvzk`, in the series–parallel order through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk`; soundness through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness`): the proof system's, the domain's
  honest prover being the generic per-field one (`GordieHowe.RealizedProgram.ProofSystem.fieldHonestDomains`), from the compiler's
  completeness alone;
* **the round errors**, in full (the carrier has no hand-built model): at the phase's challenge
  round, the source protocol `Π_P₀`'s round error at its one challenge `member.ring.gamma`
  (`alpha:A` is a realization challenge) and LogUp's `7304 / (p^2 − 2048)`
  (`GordieHowe.RealizedProgram.realError_eq`: the groups' `N_g + T − 1`, `(3072 + 127) + (2058 + 2047)`, about
  `2^-115.17`); at domain `A`'s proof rounds each its own charge (`GordieHowe.RealizedProgram.FieldRoundsLe`): the
  batches' `35/|F|`, GKR's `max 3 (2 · gkrWidth)/|F|` per round, the root's combination `1/|F|`, the tree layout's test
  round `1/|F|` and its column round `((1147 − 1)_97 + (2 · 512 − 1)_97)/(2560)_97` with the joint
  subfield term `(512 − 1)_97/(2560)_97`; at its commit rounds
  `(101777974921/(|F| − 1))^2` (`Tableau.gold2K512R2Bounds.commit`, about `2^-182.87`); `F = Goldilocks²`,
  `|F| = p^2`, `p = 2^64 − 2^32 + 1`. Each is bounded by a dyadic (`GordieHowe.RealizedProgram.FieldRoundsLe.of_num`,
  `Tableau.gold2K512R2Column_le`, `Tableau.gold2K512R2Commit_le`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open scoped NNReal

/-! ## The validity facts -/

/-- **The model of the interpretation** (`Interp.Model.of_models`): every field identifier is
Goldilocks² with its model at `GF(p^1)`; the name and characteristic, the plan's prime-subfield node
and the absence of node-typed `Bit` values by `decide`; the opaque functions are `0`; no MAC tail,
no field-form `mod_q`. -/
theorem interpModel :
    interpROM.Model Generated.Falcon512.Ring.Carrier.ROMParams.Plan.plan program [] :=
  .of_models (RealizedProgram.Interp.models_const RealizedProgram.gold2_model)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (RealizedProgram.Interp.opaqueBit_of_lt_two fun _ _ _ => Nat.zero_lt_two)
    (RealizedProgram.Interp.macModel_of_noTail (by decide +kernel))
    (RealizedProgram.Interp.fieldFormModel_of_none (by decide +kernel))

/-- **The cells checks** (`RealizedProgram.CellsValid`): a domain, every field `equal` lowered into `A`
(the top rows of the two-sided lookups on bound values as affine rows), the two groups' LogUp
identities in `c.A`, every node-typed value a committed value of `A`. -/
theorem cellsValid : program.CellsValid := by decide +kernel

/-- **The domain is local** (`RealizedProgram.Local`): every predicate of `A` reads only `A`, by the
checker (`RealizedProgram.Local.of_localB`). -/
theorem locality :
    program.Local (RealizedProgram.treeNodesOf Generated.Falcon512.Ring.Carrier.ROMParams.Plan.plan program) :=
  RealizedProgram.Local.of_localB Generated.Falcon512.Ring.Carrier.ROMParams.Valid.wellFormed
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
abbrev fieldPkA : (interpROM.field (program.domainField 0)).Packing := RealizedProgram.gold2Packing

/-- **Domain `A`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkA : program.fieldOkB (I := interpROM) 0
    Generated.Falcon512.Ring.Carrier.ROMParams.Plan.plan fieldPkA RealizedProgram.gold2K512R2Cert = true := by
  decide +kernel

/-- **The ready data of the domain** (`RealizedProgram.FieldReady`): `gold2Packing`, the tableau
`gold2K512R2Cert`, the checks `fieldOkA`. -/
def ready :
    ∀ d : Fin program.domains.length,
      program.FieldReady interpROM d Generated.Falcon512.Ring.Carrier.ROMParams.Plan.plan
  | ⟨0, _⟩ => ⟨fieldPkA, RealizedProgram.gold2K512R2Cert, fieldOkA,
      Generated.Falcon512.Ring.Carrier.ROMParams.Valid.wellFormed⟩
  | ⟨_ + 1, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The proof system of `Falcon512.Ring.Carrier.ROMParams`** at the GKR sources `src`: the validity facts
and domain `A`'s circuit proof under the compiler trust, the generic per-field domain proof at
`ready` (`RealizedProgram.ProofSystem.ofFieldProofs`). -/
def proofSystem :
    program.ProofSystem Generated.Falcon512.Ring.Carrier.ROMParams.Plan.plan interpROM :=
  RealizedProgram.ProofSystem.ofFieldProofs
    ⟨Generated.Falcon512.Ring.Carrier.ROMParams.Valid.valid,
      Generated.Falcon512.Ring.Carrier.ROMParams.Realize.derivable,
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

/-- **Completeness of `Falcon512.Ring.Carrier.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
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

/-- **Honest-verifier zero knowledge of `Falcon512.Ring.Carrier.ROMParams` at the realized program**
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

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
