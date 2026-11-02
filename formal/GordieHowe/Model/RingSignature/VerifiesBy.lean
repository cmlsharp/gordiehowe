-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Base

@[expose] public section

/-!
# Proof systems whose verifier is a query-bounded program

`ProofSystem.VerifiesBy PS Vp qv`: the verifier of `PS` at every oracle `H` is the result of the
classical oracle program `Vp x π` against `H`, and every such program makes at most `qv` queries.
An event that verifies a proof at the final oracle in force then reads that oracle only through a
program with `qv` queries.

- `VerifiesBy.mono`: a larger query bound.
-/

namespace GordieHowe.RingSignature

variable {X Y Stmt Wit : Type}

/-- **The verifier of `PS` is the query-bounded program `Vp`**: `PS.verify H x π` is the result of
`Vp x π` against `H` (`verify_eq`), and `Vp x π` makes at most `qv` queries (`queries`). -/
structure ProofSystem.VerifiesBy {TPS : PSTypes} (PS : ProofSystem X Y Stmt Wit TPS)
    (Vp : Stmt → PS.Proof → OracleProg X Y Bool) (qv : ℕ) : Prop where
  /-- The verifier is the program's result. -/
  verify_eq : ∀ H x π, PS.verify H x π = (Vp x π).run H
  /-- The program makes at most `qv` queries. -/
  queries : ∀ x π, (Vp x π).QueriesLE qv

/-- A larger query bound. -/
theorem ProofSystem.VerifiesBy.mono {TPS : PSTypes} {PS : ProofSystem X Y Stmt Wit TPS}
    {Vp : Stmt → PS.Proof → OracleProg X Y Bool} {qv qv' : ℕ} (h : PS.VerifiesBy Vp qv)
    (hq : qv ≤ qv') : PS.VerifiesBy Vp qv' :=
  ⟨h.verify_eq, fun x π => (h.queries x π).mono hq⟩

end GordieHowe.RingSignature
