-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Interp
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Locality
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Foundations.Fields.GF2_128Conv
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the proof system of `Falcon512.Native.ROMParams`

The security theorem of the proof system at the realized program of the native Falcon proof of possession at the ROM parameters
(`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program`, export `c825eb05`: domain `H` over
`GF(2^128)` with the GKR circuit `c.H` and its batch on bits, domain `A` over `F_q^9` with the GKR
circuit `c.A` and the batches `norm.center`, `norm.column0`, `norm.column1`, `norm.column2` and
`A.boolean`; two phases: the source challenge `h2p.select.delta` with
the MAC key `mac.beta`, then the lookup challenge `alpha:A`; the cross-field `equal`
`mac.equal` realized by the MAC), at the interpretation `GordieHowe.Falcon512.Native.ROMParams.interp` and the GKR
sources `src` of its circuits:

* **the validity facts**: the program's checks (the validity `GordieHowe.Generated.Falcon512.Native.ROMParams.Valid.valid`, item
  13 `GordieHowe.Generated.Falcon512.Native.ROMParams.Realize.derivable`, the source part, the cells checks and the
  locality `GordieHowe.Falcon512.Native.ROMParams.Locality`) and the model of the interpretation
  (`GordieHowe.Falcon512.Native.ROMParams.interpModel`);
* **the ready data** (`ready`): domain `H`'s (`readyH`: `gf128Packing`, the tableau
  `gf128K282R2Cert`, the checks `fieldOkH`) and domain `A`'s (`fq9Packing`, the tableau
  `GordieHowe.RealizedProgram.falconNativeROMACert`, the checks `fieldOkA`), the checks `GordieHowe.RealizedProgram.fieldOkB` by
  `decide +kernel`;
* **the proof system** (`proofSystem`): every domain's circuit proof the generic per-field domain
  proof at `ready` (`GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs`), under the compiler trust;
* **the headlines** (`iop_completeness`, `iop_hvzk`, in the series–parallel order through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness` and `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk`; soundness through `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness`): the proof system's, the domains'
  honest provers being the generic per-field ones (`honestProofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldHonestDomains`);
* **the round errors**: at the first phase's challenge round, `Π_P₀`'s round error at
  `h2p.select.delta` and the MAC's `64/2^128` at `mac.beta` (`GordieHowe.RealizedProgram.realError_eq`); at the second,
  LogUp's `16448/(q^9 − 189)` at `alpha:A` (`GordieHowe.RealizedProgram.realError_eq`); at the domains' rounds, the
  round charges of the generic per-field domain proofs (`GordieHowe.RealizedProgram.FieldRoundsLe`,
  `GordieHowe/Applications/Falcon512/Native/ROMParams/Transcript.lean`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
open Generated.Falcon512.Native.ROMParams.Program (program)
open scoped NNReal

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interp c)

/-! ## The proof system -/

/-- The program has two domains. -/
theorem domains_length : program.domains.length = 2 := by decide

/-- Domain `H`'s packing facts. -/
abbrev fieldPkH : (interp.field (program.domainField 0)).Packing := RealizedProgram.gf128Packing

/-- **Domain `H`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkH : program.fieldOkB (I := interp) 0 Generated.Falcon512.Native.ROMParams.Plan.plan
    fieldPkH RealizedProgram.gf128K282R2Cert = true := by
  decide +kernel

/-- **Domain `H`'s ready data** (`RealizedProgram.FieldReady`): `gf128Packing`, the tableau
`gf128K282R2Cert`, the checks `fieldOkH`. -/
def readyH : program.FieldReady interp 0 Generated.Falcon512.Native.ROMParams.Plan.plan :=
  ⟨fieldPkH, RealizedProgram.gf128K282R2Cert, fieldOkH, Generated.Falcon512.Native.ROMParams.Valid.wellFormed⟩

/-- Domain `A`'s packing facts. -/
abbrev fieldPkA : (interp.field (program.domainField 1)).Packing := RealizedProgram.fq9Packing

/-- **Domain `A`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkA : program.fieldOkB (I := interp) 1 Generated.Falcon512.Native.ROMParams.Plan.plan
    fieldPkA RealizedProgram.falconNativeROMACert = true := by
  decide +kernel

/-- **The ready data of both domains.** -/
def ready :
    ∀ d : Fin program.domains.length,
      program.FieldReady interp d Generated.Falcon512.Native.ROMParams.Plan.plan
  | ⟨0, _⟩ => readyH
  | ⟨1, _⟩ => ⟨fieldPkA, RealizedProgram.falconNativeROMACert, fieldOkA,
      Generated.Falcon512.Native.ROMParams.Valid.wellFormed⟩
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The proof system of `Falcon512.Native.ROMParams`** at the GKR sources `src`: the validity facts and
every domain's circuit proof under the compiler trust, the generic per-field domain proof at
`ready` (`RealizedProgram.ProofSystem.ofFieldProofs`). -/
def proofSystem :
    program.ProofSystem Generated.Falcon512.Native.ROMParams.Plan.plan interp :=
  RealizedProgram.ProofSystem.ofFieldProofs
    ⟨Generated.Falcon512.Native.ROMParams.Valid.valid,
      Generated.Falcon512.Native.ROMParams.Realize.derivable,
      Locality.sourceValid, Locality.cellsValid,
      Locality.locality⟩
    interpModel src ready

/-- **The domains' honest provers of the proof system** (`RealizedProgram.ProofSystem.fieldHonestDomains`), from the
compiler's completeness. -/
noncomputable def honestProofSystem :
    (proofSystem src).HonestDomains ((proofSystem src).fieldSims ready) :=
  (proofSystem src).fieldHonestDomains ready

/-! ## The round errors -/

/-- Domain `H`, as an index of the program's domains. -/
abbrev domainH : Fin program.domains.length := ⟨0, by decide⟩

/-- Domain `A`, as an index of the program's domains. -/
abbrev domainA : Fin program.domains.length := ⟨1, by decide⟩

/-! ## The headlines at a source protocol -/

variable {Inp : Type} {relH : Set (program.Valuation interp × Inp)}

/-- **Completeness of `Falcon512.Native.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
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

/-- **Honest-verifier zero knowledge of `Falcon512.Native.ROMParams` at the realized program**
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

end GordieHowe.Falcon512.Native.ROMParams
