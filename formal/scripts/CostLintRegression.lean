-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-!
# Cost lint regression fixtures

Run `python3 scripts/test_cost_lint.py`. The runner places these fixtures after the actual lint
implementation and before its environment-wide commands. Every bad definition returns the same
kind of data as a good definition, through `Classical.choice`; the compiler has no code for it.
The result types include an abbreviation and implicit dependent parameters, as generated and
program-level wrappers do. No fixture is imported by the library or added to the exception list.
-/

namespace GordieHowe.CostLintRegression

variable (P : RealizedProgram.Export.Plan) (ir : RealizedProgram) (I : RealizedProgram.Interp)

abbrev Systems := ir.ProofSystem P I

def goodSystem (x : Systems P ir I) := x
noncomputable def badSystem (x : Systems P ir I) := Classical.choice ⟨x⟩

def goodReady (i : Fin ir.domains.length) (x : ir.FieldReady I i P) := x
noncomputable def badReady (i : Fin ir.domains.length) (x : ir.FieldReady I i P) :=
  Classical.choice ⟨x⟩

def goodCertified (x : RealizedProgram.CertifiedProgram P ir I) := x
noncomputable def badCertified (x : RealizedProgram.CertifiedProgram P ir I) :=
  Classical.choice ⟨x⟩

def goodRuntimeInputs (x : RuntimeInputs) := x
noncomputable def badRuntimeInputs (x : RuntimeInputs) := Classical.choice ⟨x⟩

def goodCompletionInputs (x : CompletionInputs) := x
noncomputable def badCompletionInputs (x : CompletionInputs) := Classical.choice ⟨x⟩

variable {Stmt W : Type} {rel : Set (Stmt × W)}

def goodIop (x : RealizedProgram.ProofSystem.IOP Stmt W rel) := x
noncomputable def badIop (x : RealizedProgram.ProofSystem.IOP Stmt W rel) := Classical.choice ⟨x⟩

def goodTranscript {C : RealizedProgram.ProofSystem.IOP Stmt W rel}
    (x : SPBCS.ProofSystemTranscript C) := x
noncomputable def badTranscript {C : RealizedProgram.ProofSystem.IOP Stmt W rel}
    (x : SPBCS.ProofSystemTranscript C) := Classical.choice ⟨x⟩

def goodSimulator {C : RealizedProgram.ProofSystem.IOP Stmt W rel} (x : C.SimData) := x
noncomputable def badSimulator {C : RealizedProgram.ProofSystem.IOP Stmt W rel}
    (x : C.SimData) := Classical.choice ⟨x⟩

variable {OracleIn OracleOut Proof Coins : Type}

abbrev RingSystems (types : RingSignature.PSTypes) :=
  RingSignature.ProofSystem OracleIn OracleOut Stmt W types

def goodRingProofSystem {types : RingSignature.PSTypes}
    (x : RingSystems (OracleIn := OracleIn) (OracleOut := OracleOut) (Stmt := Stmt) (W := W) types) := x
noncomputable def badRingProofSystem {types : RingSignature.PSTypes}
    (x : RingSystems (OracleIn := OracleIn) (OracleOut := OracleOut) (Stmt := Stmt) (W := W) types) :=
  Classical.choice ⟨x⟩

def goodPSTypes (x : RingSignature.PSTypes) := x
noncomputable def badPSTypes (x : RingSignature.PSTypes) := Classical.choice ⟨x⟩

def goodRingScheme {n : ℕ} {types : RingSignature.RingTypes}
    (x : RingSignature.RingScheme OracleIn OracleOut n types) := x
noncomputable def badRingScheme {n : ℕ} {types : RingSignature.RingTypes}
    (x : RingSignature.RingScheme OracleIn OracleOut n types) := Classical.choice ⟨x⟩

def goodRingTypes (x : RingSignature.RingTypes) := x
noncomputable def badRingTypes (x : RingSignature.RingTypes) := Classical.choice ⟨x⟩

def goodBaseSigner {n : ℕ} {types : RingSignature.BaseTypes}
    (x : RingSignature.BaseSigner OracleIn OracleOut n types) := x
noncomputable def badBaseSigner {n : ℕ} {types : RingSignature.BaseTypes}
    (x : RingSignature.BaseSigner OracleIn OracleOut n types) := Classical.choice ⟨x⟩

def goodBaseTypes (x : RingSignature.BaseTypes) := x
noncomputable def badBaseTypes (x : RingSignature.BaseTypes) := Classical.choice ⟨x⟩

def goodProverFn (x : NARG.ProverFn OracleIn OracleOut Stmt W Proof Coins) := x
noncomputable def badProverFn (x : NARG.ProverFn OracleIn OracleOut Stmt W Proof Coins) := Classical.choice ⟨x⟩

def goodProver (x : NARG.Prover OracleIn OracleOut Stmt W Proof Coins) := x
noncomputable def badProver (x : NARG.Prover OracleIn OracleOut Stmt W Proof Coins) := Classical.choice ⟨x⟩

def goodVerifier (x : NARG.Verifier OracleIn OracleOut Proof Stmt) := x
noncomputable def badVerifier (x : NARG.Verifier OracleIn OracleOut Proof Stmt) := Classical.choice ⟨x⟩

def goodExtractor {n : ℕ} {spec : IOP.ProtocolSpec n} (x : IOP.Extractor spec Stmt W) := x
noncomputable def badExtractor {n : ℕ} {spec : IOP.ProtocolSpec n}
    (x : IOP.Extractor spec Stmt W) := Classical.choice ⟨x⟩

def goodPlainIop {n : ℕ} {spec : IOP.ProtocolSpec n} (x : IOP.IOP spec Stmt) := x
noncomputable def badPlainIop {n : ℕ} {spec : IOP.ProtocolSpec n}
    (x : IOP.IOP spec Stmt) := Classical.choice ⟨x⟩

def goodMultiIop (x : MultiCircuitIOP Stmt W rel) := x
noncomputable def badMultiIop (x : MultiCircuitIOP Stmt W rel) := Classical.choice ⟨x⟩

-- These aliases must be recognized before their own function arguments are peeled off.
def goodIopProver {n : ℕ} {spec : IOP.ProtocolSpec n} (x : IOP.Prover spec Stmt) :
    IOP.Prover spec Stmt := x
noncomputable def badIopProver {n : ℕ} {spec : IOP.ProtocolSpec n}
    (x : IOP.Prover spec Stmt) : IOP.Prover spec Stmt := Classical.choice ⟨x⟩

def goodIopVerifier {n : ℕ} {spec : IOP.ProtocolSpec n} (x : IOP.Verifier spec Stmt) :
    IOP.Verifier spec Stmt := x
noncomputable def badIopVerifier {n : ℕ} {spec : IOP.ProtocolSpec n}
    (x : IOP.Verifier spec Stmt) : IOP.Verifier spec Stmt := Classical.choice ⟨x⟩

end GordieHowe.CostLintRegression

run_cmd liftTermElabM do
  let (bad, _) ← computabilityFailures #[]
  let cases := ["System", "Ready", "Certified", "RuntimeInputs", "CompletionInputs", "Iop", "Transcript", "Simulator",
    "ProverFn", "Prover", "Verifier", "Extractor", "PlainIop", "MultiIop", "IopProver", "IopVerifier",
    "RingProofSystem", "PSTypes", "RingScheme", "RingTypes", "BaseSigner", "BaseTypes"]
  for suffix in cases do
    let good := Name.str `GordieHowe.CostLintRegression ("good" ++ suffix)
    let rejected := Name.str `GordieHowe.CostLintRegression ("bad" ++ suffix)
    unless (IR.findEnvDecl (← getEnv) good).isSome do
      throwError "cost lint regression: positive fixture {good} did not compile"
    if bad.any (·.1 == good) then
      throwError "cost lint regression: rejected compiled fixture {good}"
    unless bad.any (·.1 == rejected) do
      throwError "cost lint regression: missed noncomputable fixture {rejected}"
  logInfo m!"cost lint regression: {cases.length} compiled fixtures accepted and \
    {cases.length} noncomputable fixtures rejected"

run_cmd liftTermElabM do
  let (strict, runtime, _) ← computabilityFailureClasses #[]
  for n in [`GordieHowe.CostLintRegression.badSimulator,
      `GordieHowe.CostLintRegression.badExtractor] do
    unless strict.any (·.1 == n) && !runtime.any (·.1 == n) do
      throwError "cost lint regression: extractor/simulator escaped strict checking: {n}"
  let some a := runtime.find? (·.1 == `GordieHowe.CostLintRegression.badSystem) |
    throwError "cost lint regression: missing runtime system failure"
  let some b := runtime.find? (·.1 == `GordieHowe.CostLintRegression.badReady) |
    throwError "cost lint regression: missing runtime ready failure"
  enforceRuntimeCeiling 1 #[a]
  let overflowRejected ← try
    enforceRuntimeCeiling 1 #[a, b]
    pure false
  catch _ => pure true
  unless overflowRejected do
    throwError "cost lint regression: runtime ceiling accepted an additional failure"
  logInfo m!"cost lint regression: simulator/extractor strict; ceiling boundary accepted and overflow rejected"
