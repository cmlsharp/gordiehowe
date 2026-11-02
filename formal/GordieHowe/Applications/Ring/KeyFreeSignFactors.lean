-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Split

@[expose] public section

/-!
# Key-free signers that factor through the base component and a public part

A key-free signer `ksign` (the signer of the key-free relay,
`GordieHowe/Applications/Ring/KeyFreeRelay.lean`) whose run at an oracle `H` is read from the base
component `base sp H` and one value of the second component: the public part and the signature
`out` at the base component and the side coins, then the published value `pub`, and the assignment
`asg` from the public part and the second component of `H` at the kept point `xk`.

- `KFSignFactors`: the factorization, with its program over the base component.
- `KFStmt`, `KFStmt.ofProg`: a statement program over the base component.
-/

open scoped ENNReal

namespace GordieHowe.RingSignature.KeyFree

open GordieHowe.Quantum RingSignature.OracleSplit

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  {N : ℕ} {PK Msg Pub BSig SC : Type}

/-- **A key-free signer factoring through the base component and a public part**: for the
public key `pk`, the ring `R`, the request number `c`, the message `m` and the side coins `s`, its
run at every oracle `H` is `out` at the base component of `H` (the public part `q` and the
signature, `none` for a refusal), read as the published value `pub q`, the signature, and the
assignment list `asg q` from the second component of `H` at the kept point `xk q`; the public
part, the signature and the kept data are the run at the base component of a program `outB` over
the base component, with at most `qOut` queries. -/
structure KFSignFactors (Pb : Type)
    (ksign : PK → KeyRing PK N → ℕ → Msg → SC → OracleProg X Y (Option (Pub × BSig ×
      List (Assignment X Y)))) where
  /-- The public part and the signature at a base component; `none` is a refusal. -/
  out : (X → Y₁) → PK → KeyRing PK N → ℕ → Msg → SC → Option (Pb × BSig)
  /-- The kept point of a public part. -/
  xk : (X → Y₁) → PK → KeyRing PK N → Msg → Pb → X
  /-- The published value of a public part. -/
  pub : (X → Y₁) → PK → KeyRing PK N → Msg → Pb → Pub
  /-- The assignments of a public part, from the second component at the kept point. -/
  asg : (X → Y₁) → PK → KeyRing PK N → Msg → Pb → Y₂ → List (Assignment X Y)
  /-- The run is read from the base component and the second component at the kept point. -/
  run_eq : ∀ pk R c m s (H : X → Y), (ksign pk R c m s).run H =
    (out (base sp H) pk R c m s).map fun q => (pub (base sp H) pk R m q.1, q.2,
      asg (base sp H) pk R m q.1 (prf sp H (xk (base sp H) pk R m q.1)))
  /-- The public part and the signature, with the kept point, the published value and the
  assignments, as a program over the base component. -/
  outB : PK → KeyRing PK N → ℕ → Msg → SC →
    OracleProg X Y₁ (Option ((Pb × BSig) × (X × Pub × (Y₂ → List (Assignment X Y)))))
  /-- The query bound of `outB`. -/
  qOut : ℕ
  /-- `outB` runs as `out`, with the kept point, the published value and the assignments. -/
  run_outB : ∀ pk R c m s (ω : X → Y₁), (outB pk R c m s).run ω =
    (out ω pk R c m s).map fun q => (q, xk ω pk R m q.1, pub ω pk R m q.1, asg ω pk R m q.1)
  /-- `outB` makes at most `qOut` queries. -/
  outB_queries : ∀ pk R c m s, (outB pk R c m s).QueriesLE qOut

/-- **A statement program over the base component**: a program `stmtPB` whose run at `ω` is
`stmtPω ω`, with at most `qSt` queries. -/
structure KFStmt {St X₀ : Type} (stmtPω : (X → Y₁) → St → X₀) where
  /-- The statement program over the base component. -/
  stmtPB : St → OracleProg X Y₁ X₀
  /-- Its query bound. -/
  qSt : ℕ
  /-- It runs as `stmtPω`. -/
  run_stmtPB : ∀ x (ω : X → Y₁), (stmtPB x).run ω = stmtPω ω x
  /-- It makes at most `qSt` queries. -/
  stmtPB_queries : ∀ x, (stmtPB x).QueriesLE qSt

/-- **A statement program over the base component, from its program**: `stmtPω` its run. -/
def KFStmt.ofProg {St X₀ : Type} (P : St → OracleProg X Y₁ X₀) (q : ℕ)
    (hP : ∀ x, (P x).QueriesLE q) : KFStmt (fun ω x => (P x).run ω) where
  stmtPB := P
  qSt := q
  run_stmtPB _ _ := rfl
  stmtPB_queries := hP

end GordieHowe.RingSignature.KeyFree
