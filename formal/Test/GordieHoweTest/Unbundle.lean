-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Applications.Ring.KeyFreeSideSteps

/-!
# Register types from shapes

An algorithm's register types are read from its type index, a shape term, never from the
algorithm itself. So two algorithms that differ only in their steps, coins or output, compared at
their register types, compare two equal shape terms, and the comparison never unfolds an
algorithm. Each check below closes by `rfl` under a small heartbeat cap.

The checks in the block comment at the end are not expected to pass yet: they need the
shape-indexed `AdaptiveIAlg` (`PENDING M1b`) or the type-indexed schemes (`PENDING M2`).
-/

namespace GordieHoweTest.Unbundle

open GordieHowe GordieHowe.Quantum GordieHowe.QROM

section KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ks : KindShape X Y Req Resp} (K : KindAlg ks O)

set_option maxHeartbeats 20000 in
/-- Replacing the steps keeps the Kraus index and the workspace. -/
example (st : StepIdx K.slots K.post → KrausMap K.R (DReg K.W K.width X Y Req Resp)
    (DReg K.W K.width X Y Req Resp)) : (K.withStep st).R = K.R ∧ (K.withStep st).W = K.W :=
  ⟨rfl, rfl⟩

set_option maxHeartbeats 20000 in
/-- Forgetting the output keeps the workspace and the dilation's workspace. -/
example : K.unitOut.W = K.W ∧ K.unitOut.DW = K.DW :=
  ⟨rfl, rfl⟩

set_option maxHeartbeats 20000 in
/-- The trace-preserving form has one shape whatever `freeze`. -/
example {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) :
    (A.toTPKindAlg true).R = (A.toTPKindAlg false).R ∧
      (A.toTPKindAlg true).unitOut.DW = (A.toTPKindAlg false).DW :=
  ⟨rfl, rfl⟩

end KindAlg

section Relay

open RingSignature

variable {m : ℕ} {Y Y₁ Req Resp O Req' Resp' : Type} [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited Req'] [Inhabited Req] {shA₀ : AlgShape (Bits m) Y Req Resp} (A₀ : AdaptiveIAlg shA₀ O)
  (G : (Bits m → Y₁) → AssignRelay (Bits m) Y Req Resp Req' Resp' (Bits m) Y₁) (Q : ℕ)

set_option maxHeartbeats 20000 in
/-- The trace-preserving form of the compound relayed adversary, at both freezes and with its
output forgotten, over free `A₀` and `G`: one workspace and one Kraus index. -/
example :
    ((AdaptiveIAlg.assignSideBase A₀ G Q).toTPKindAlg true).unitOut.W =
        ((AdaptiveIAlg.assignSideBase A₀ G Q).toTPKindAlg false).W ∧
      ((AdaptiveIAlg.assignSideBase A₀ G Q).toTPKindAlg true).unitOut.R =
        ((AdaptiveIAlg.assignSideBase A₀ G Q).toTPKindAlg false).R :=
  ⟨rfl, rfl⟩

end Relay

/-
PENDING M1b (shape-indexed `AdaptiveIAlg`):

* `((AdaptiveIAlg.assignSideBase A₀ G Q).mapOut f).R = (AdaptiveIAlg.assignSideBase A₀ G Q).R`
  and the same for `.W`, over free `A₀` and `G`, by `rfl` under the cap.
* `(A.relayAdv F Q out').mapOut g = A.relayAdv F Q (g ∘ out')`, by `rfl`.
* `(A.relayAdv (F.withSide ω₁) Q o).W = (A.relayAdv (F.withSide ω₂) Q o).W`, by `rfl`.
* `withStep_restrictAt_eq` and kfExt's `leftPerm_tp_steps` at concrete terms.

PENDING M2 (type-indexed schemes):

* `(freshScheme …).PK = PubKey p prims`, `RingStmt Bh = RingStmt Bf`, `PSf.Proof = Sc.Response b`,
  and `@List.idxOf (freshBase …).PK _ = @List.idxOf (PubKey p prims) _`, by `rfl`.
-/

end GordieHoweTest.Unbundle
