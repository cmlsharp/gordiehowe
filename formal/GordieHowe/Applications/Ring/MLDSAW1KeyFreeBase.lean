-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeFactors
public import GordieHowe.Applications.Ring.KeyFreeRelayB
public import GordieHowe.Applications.Ring.MLDSAW1CaseSplitSide

@[expose] public section

/-!
# The key-free signer of the ML-DSA ring publishing `w₁` over the base component

The statement program over the base component of the key-free relay in side-read mode (`KFStmt`,
`GordieHowe/Applications/Ring/KeyFreeSignFactors.lean`) for the ML-DSA ring publishing `w₁`; the
signer's program over the base component is part of `w1KFFactors`
(`GordieHowe/Applications/Ring/KeyFreeFactors.lean`).

- `w1KFStmt`: the statement program `w1StmtProg` for `w1StmtPω`, with at most `2N` queries.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum RingSignature.KeyFree

section Sign

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁]
  [AddGroup Y₂] (O : W1Oracles X Y p prims Msg N reps) (sp : Y ≃+ Y₁ × Y₂) (βmin : ℚ≥0)
  (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) {RMsg : Type}
  (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) [Fintype Msg] [DecidableEq Msg]
  [Fintype RMsg] [DecidableEq RMsg]

end Sign

section Stmt

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (Mo : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

/-- **The statement program over the base component** for `w1StmtPω`: `w1StmtProg`, with at
most `2N` queries. -/
noncomputable def w1KFStmt (sp : Y ≃+ Y₁ × Y₂) :
    KFStmt (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) :=
  KFStmt.ofProg (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg)

end Stmt

end GordieHowe.Ring.MLDSAW1
