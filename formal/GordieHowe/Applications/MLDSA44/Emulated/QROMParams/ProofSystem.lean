-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.HashField
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Locality
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Foundations.Fields.GF2_256Conv
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the proof system of `MLDSA44.Emulated.QROMParams`

The security theorem of the proof system at the realized program of the emulated ML-DSA-44 proof of possession at the QROM
parameters
(`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program.program`, export `c825eb05`: domain `A` over
Goldilocks⁴ with the GKR circuit `c.A` and the batch `A.boolean`, domain `H` over `GF(2^256)` with
the GKR circuit `c.H` and the batch `h2c.mu.blocks.r0`; two phases: the source challenges
`h2c.sample.select.delta` and `h2c.sample.mem.delta` with the MAC key `mac.beta`, then the lookup
challenge `alpha:A`; the cross-field `equal` `mac.equal` realized by the MAC), at the
interpretation `GordieHowe.MLDSA44.Emulated.QROMParams.HashField.interp` and the GKR sources `src` of its circuits:

* **the validity facts**: the program's checks (the validity `GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Valid.valid`, the
  realization validity `GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Realize.derivable`, the source part `sourceValid`,
  the cells checks `cellsValid`, the locality `GordieHowe.MLDSA44.Emulated.QROMParams.Locality.locality`) and the model of
  the interpretation (`interpModel`: Goldilocks⁴ and `GF(2^256)` with their field models, the MAC
  field `GF(2^256)` of width `256` with the taps `{0, 2, 5, 10}`, no field-form `mod_q`), by
  `decide +kernel` and the field models;
* **the ready data** (`ready`): domain `A`'s (`gold4Packing`, the tableau `gold4K512R2Cert`, the
  checks `fieldOkA` by `decide +kernel`) and domain `H`'s (`GordieHowe.MLDSA44.Emulated.QROMParams.HashField.readyH`);
* **the proof system** (`proofSystem`): every domain's circuit proof the generic per-field domain proof
  at `ready` (`GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs`), under the compiler trust; its verifier rejects a statement
  outside the declared bounds (`GordieHowe.RealizedProgram.stmtOk`);
* **the headlines** (`iop_completeness`, `iop_hvzk`, in the series–parallel order through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk`; soundness through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness`);
* **the round errors**: at the first phase's challenge round, `Π_P₀`'s round errors at its two
  challenges and the MAC's `26/2^256` at `mac.beta` (`GordieHowe.RealizedProgram.realError_eq`); at the second, LogUp's
  `17920/(p^4 − 4096)` at `alpha:A` (`GordieHowe.RealizedProgram.realError_eq`, about `2^-241.87`); at domain `A`'s
  branches the Boolean batch's `55/|F|` and GKR's `max 3 (2 · gkrWidth)/|F|` per round, at its join the root's
  combination `1/|F|` and the tree layout's test and column (with the joint subfield term) rounds,
  at its commit rounds `(118174498727/(|F| − 1))^2` (`Tableau.gold4K512R2Bounds.commit`),
  `F = Goldilocks⁴`; at domain `H`'s the same charges of its tableau (`GordieHowe.RealizedProgram.FieldRoundsLe`,
  `GordieHowe/Applications/MLDSA44/Emulated/QROMParams/Transcript.lean`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
open Generated.MLDSA44.Emulated.QROMParams.Program (program)
open HashField (interp)
open scoped NNReal

/-! ## The validity facts -/

/-- **The model of the interpretation** (`Interp.Model.of_models`): field `0` is Goldilocks⁴ with
its model at `GF(p^1)`, field `1` `GF(2^256)` with its model at `bit`; the names and
characteristics, the plan's prime-subfield nodes and the nodes of the node-typed `Bit` values are
the fields', by `decide`; `mac.target_bits` returns bits; the one MAC tail has its powers in
`GF(2^256)`, a binary MAC field of width `256` with the taps `{0, 2, 5, 10}` (`gf256_macFieldOk`),
and its target's bits computed by `mac.target_bits` (`RealizedProgram.macTailsAt`, by `decide`); no
field-form `mod_q`. -/
theorem interpModel : interp.Model Generated.MLDSA44.Emulated.QROMParams.Plan.plan program [] :=
  .of_models (RealizedProgram.mldsaInterpOf_models RealizedProgram.gold4_model RealizedProgram.gf256_model)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (RealizedProgram.Interp.opaqueBit_of_lt_two RealizedProgram.targetBitsFn_lt_two)
    (RealizedProgram.Interp.macModel_of_tails (f := 1) (nm := "mac.target_bits") (by decide +kernel)
      RealizedProgram.gf256_macFieldOk RealizedProgram.targetBitsFn_target)
    (RealizedProgram.Interp.fieldFormModel_of_none (by decide +kernel))

/-- **The cells checks** (`RealizedProgram.CellsValid`): the committing domains `A` and `H`, every field
`equal` lowered into its domain, the LogUp identity of `A.512` and the MAC's H half in their
circuits, every node-typed value a committed value of its domain. -/
theorem cellsValid : program.CellsValid := by decide +kernel

/-- **The source part is well formed** (`RealizedProgram.SourceValid`). -/
theorem sourceValid : program.SourceValid := by decide +kernel

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interp c)

/-! ## The proof system -/

/-- The program has two domains. -/
theorem domains_length : program.domains.length = 2 := by decide

/-- Domain `A`'s packing facts. -/
abbrev fieldPkA : (interp.field (program.domainField 0)).Packing := RealizedProgram.gold4Packing

/-- **Domain `A`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkA : program.fieldOkB (I := interp) 0 Generated.MLDSA44.Emulated.QROMParams.Plan.plan fieldPkA
    RealizedProgram.gold4K512R2Cert = true := by
  decide +kernel

/-- **The ready data of both domains.** -/
def ready :
    ∀ d : Fin program.domains.length,
      program.FieldReady interp d Generated.MLDSA44.Emulated.QROMParams.Plan.plan
  | ⟨0, _⟩ => ⟨fieldPkA, RealizedProgram.gold4K512R2Cert, fieldOkA,
      Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed⟩
  | ⟨1, _⟩ => HashField.readyH
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The proof system of `MLDSA44.Emulated.QROMParams`** at the GKR sources `src`: the validity facts and
every domain's circuit proof under the compiler trust, the generic per-field domain proof at
`ready` (`RealizedProgram.ProofSystem.ofFieldProofs`). -/
def proofSystem :
    program.ProofSystem Generated.MLDSA44.Emulated.QROMParams.Plan.plan interp :=
  RealizedProgram.ProofSystem.ofFieldProofs
    ⟨Generated.MLDSA44.Emulated.QROMParams.Valid.valid,
      Generated.MLDSA44.Emulated.QROMParams.Realize.derivable, sourceValid, cellsValid,
      Locality.locality⟩
    interpModel src ready

/-- **The domains' honest provers of the proof system** (`RealizedProgram.ProofSystem.fieldHonestDomains`), from the
compiler's completeness. -/
noncomputable def honestProofSystem :
    (proofSystem src).HonestDomains ((proofSystem src).fieldSims ready) :=
  (proofSystem src).fieldHonestDomains ready

/-! ## The round errors -/

/-- Domain `A`, as an index of the program's domains. -/
abbrev domainA : Fin program.domains.length := ⟨0, by decide⟩

/-- Domain `H`, as an index of the program's domains. -/
abbrev domainH : Fin program.domains.length := ⟨1, by decide⟩

/-! ## The headlines -/

variable {Inp : Type} {relH : Set (program.Valuation interp × Inp)}

/-- **Completeness of `MLDSA44.Emulated.QROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
the forked domains `RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`, the domains' honest provers `honestProofSystem`): in the
series–parallel order of `prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement)
(`hc`), then at every value of the coins, on every honest input, the honest prover is rejected with
probability at most `errc`. `TA`: the program's GKR circuits accept honest inputs (trust base). -/
@[headline]
theorem iop_completeness (TA : (proofSystem src).CircuitsAccept) (H : program.HonestCore interp relH)
    {errc : program.Valuation interp → ℝ≥0} (hc : H.Complete errc) (c : ((proofSystem src).fieldForkHonest ready TA H).Coins) :
    CausalCompleteStmt relH ((proofSystem src).fieldBranches ready).protocol.verifier
      (fun y => RealizedProgram.ProofSystem.IOP.honest ((proofSystem src).fieldForkHonest ready TA H) y c) errc :=
  ((proofSystem src).fieldBranches ready).completeness TA (honestProofSystem src) _ H hc c

/-- **Honest-verifier zero knowledge of `MLDSA44.Emulated.QROMParams` at the realized program**
(`RealizedProgram.ProofSystem.FieldBranches.hvzk` at the forked domains of `proofSystem`): in the series–parallel order of
`prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement) (`hc`), the simulator of the
series–parallel composite is honest-verifier zero knowledge for the honest prover with error `errc`.
`TA`: as for `iop_completeness` (trust base). -/
@[headline]
theorem iop_hvzk (TA : (proofSystem src).CircuitsAccept) (H : program.HonestCore interp relH) {errc : program.Valuation interp → ℝ≥0}
    (hc : H.Complete errc) :
    CausalHVZKStmt ((proofSystem src).fieldBranches ready).protocol.toCausalIOP.views relH
      (RealizedProgram.ProofSystem.IOP.honest ((proofSystem src).fieldForkHonest ready TA H)) id
      (RealizedProgram.ProofSystem.IOP.simulator
        (((proofSystem src).fieldBranches ready).simData ((proofSystem src).fieldForkSims ready))) errc :=
  ((proofSystem src).fieldBranches ready).hvzk TA (honestProofSystem src) _ H hc

end GordieHowe.MLDSA44.Emulated.QROMParams
