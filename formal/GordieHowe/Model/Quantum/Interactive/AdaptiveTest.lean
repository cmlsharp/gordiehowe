-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Test
public import GordieHowe.Model.Quantum.Interactive.Adaptive

@[expose] public section

/-!
# Residual-state tests for adversaries with run-time kinds

The tests of `GordieHowe/Model/Quantum/Interactive/Test.lean` (Unruh 2017, ePrint 2017/398, Definition 14,
p. 21, `Π^{H_final}_{x‖π}`) for adversaries with run-time kinds (`AdaptiveIAlg`):
`AdaptiveIAlg.QTest A` and the adversary followed by the test, `AdaptiveIAlg.withTest A T`, with
the same construction (the output copied after `A`'s last Kraus map, the test's channels and
batches as post batches). The kind of a slot is read from `A`'s part of the workspace, and the
budget of query slots is `A`'s.
-/

open Finset Matrix
open scoped BigOperators MatrixOrder

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **A residual-state test that queries the oracle** (Unruh 2017, Definition 14, p. 21, the test
`Π^{H_final}_{x‖π}` applied to the residual state `S_A`; the projective measurement circuits of
p. 12, generalized to trace-preserving maps): Kraus channels on the adversary's registers, `step 0`
before the first of `batches` batches of `width` queries and `step (b + 1)` after batch `b`, and
the outcome, a predicate `ok` of the workspace measured in the computational basis at the end. The
module docstring explains why the channels need not depend on `x‖π`. -/
structure QTest (A : AdaptiveIAlg X Y Req Resp O) where
  /-- The number of query batches. -/
  batches : ℕ
  /-- The index type of the Kraus operators. -/
  R : Type
  [instFintypeR : Fintype R]
  /-- The channels: `step 0` before the first batch, `step (b + 1)` after batch `b`. -/
  step : Fin (batches + 1) →
    KrausChannel R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)
  /-- The outcome: the test accepts on the measured workspaces satisfying `ok`. -/
  ok : A.W → Prop

attribute [instance] QTest.instFintypeR

variable (A : AdaptiveIAlg X Y Req Resp O)

instance : DecidableEq (DReg A.W A.width X Y Req Resp × A.W) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

/-- The number of queries of a test: `width` per batch. -/
def QTest.queries {A : AdaptiveIAlg X Y Req Resp O} (T : A.QTest) : ℕ := A.width * T.batches

open Classical in
/-- **The canonical representative of the output of a workspace**: a workspace with the same
output, chosen from the output value alone (`outRep_eq_of_out_eq`). -/
noncomputable def outRep (w : A.W) : A.W :=
  Classical.choose (⟨w, rfl⟩ : ∃ w', A.out w' = A.out w)

theorem out_outRep (w : A.W) : A.out (A.outRep w) = A.out w :=
  Classical.choose_spec (⟨w, rfl⟩ : ∃ w', A.out w' = A.out w)

/-- **The representative depends only on the output.** -/
theorem outRep_eq_of_out_eq {w w' : A.W} (h : A.out w = A.out w') : A.outRep w = A.outRep w' := by
  have key : ∀ o o' : O, o = o' → ∀ (p : ∃ v, A.out v = o) (p' : ∃ v, A.out v = o'),
      Classical.choose p = Classical.choose p' := by
    rintro o _ rfl p p'
    rfl
  exact key _ _ h _ _

/-- The registers of `A^Π` as `A`'s registers and the copy register. -/
def copySplit : DReg (A.W × A.W) A.width X Y Req Resp ≃
    DReg A.W A.width X Y Req Resp × A.W where
  toFun p := (((p.1.1.1, p.1.2.1, p.1.2.2), p.2), p.1.1.2)
  invFun q := ((((q.1.1.1, q.2), q.1.1.2.1, q.1.1.2.2)), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The blank content of the copy register**: a fixed workspace value (the workspace is nonempty,
since the initial state is a density matrix on `A`'s registers). -/
noncomputable def copyBlank : A.W :=
  A.init.nonempty.some.1.1

/-- **Copy the output into the copy register**: the basis permutation that exchanges the blank
copy `copyBlank` with `outRep w`, an involution. On a blank copy it writes the representative of
the output of the workspace `w`. -/
noncomputable def copyOut : Equiv.Perm (DReg (A.W × A.W) A.width X Y Req Resp) :=
  Function.Involutive.toPerm
    (fun p => (((p.1.1.1, Equiv.swap A.copyBlank (A.outRep p.1.1.1) p.1.1.2), p.1.2), p.2))
    fun p => by simp

/-- A Kraus map on `A`'s registers as a map on the registers of `A^Π`, the identity on the copy
register. -/
def liftCopy {R : Type} [Fintype R] (K : KrausMap R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)) :
    KrausMap R (DReg (A.W × A.W) A.width X Y Req Resp)
      (DReg (A.W × A.W) A.width X Y Req Resp) :=
  (K.tensorId (A.W)).reindex A.copySplit.symm

/-- The index embedding of `A`'s Kraus operators into those of `A^Π`. -/
def embA (R' : Type) : A.R ↪ Option A.R × Option R' :=
  ⟨fun r => (some r, none), fun _ _ h => Option.some_inj.1 (congrArg Prod.fst h)⟩

/-- The index embedding of the test's Kraus operators into those of `A^Π`. -/
def embT (R' : Type) : R' ↪ Option A.R × Option R' :=
  ⟨fun r => (none, some r), fun _ _ h => Option.some_inj.1 (congrArg Prod.snd h)⟩

/-- The index embedding of the operators of the Kraus map at the junction. -/
def embAT (R' : Type) : A.R × R' ↪ Option A.R × Option R' :=
  ⟨fun p => (some p.1, some p.2), fun _ _ h => Prod.ext (Option.some_inj.1 (congrArg Prod.fst h))
    (Option.some_inj.1 (congrArg Prod.snd h))⟩

variable {A} (T : A.QTest)

/-- **The Kraus map at the junction**: `A`'s last Kraus map, the copy of the output, the test's
first channel. -/
noncomputable def junction : KrausMap (A.R × T.R) (DReg (A.W × A.W) A.width X Y Req Resp)
    (DReg (A.W × A.W) A.width X Y Req Resp) :=
  (A.liftCopy (T.step 0).toKrausMap).comp
    ((A.liftCopy (A.step lastStep)).permConj (Equiv.refl _) A.copyOut)

/-- **The Kraus maps of `A^Π`**: `A`'s maps before its last, then the junction, then the test's
channels after its batches. -/
noncomputable def withTestStep (k : StepIdx A.slots (A.post + T.batches)) :
    KrausMap (Option A.R × Option T.R) (DReg (A.W × A.W) A.width X Y Req Resp)
      (DReg (A.W × A.W) A.width X Y Req Resp) :=
  if h : (k : ℕ) < A.slots + A.post then
    (A.liftCopy (A.step ⟨k, by omega⟩)).embedIdx (A.embA T.R)
  else if (k : ℕ) = A.slots + A.post then
    (junction T).embedIdx (A.embAT T.R)
  else
    (A.liftCopy (T.step ⟨k - (A.slots + A.post), by omega⟩).toKrausMap).embedIdx (A.embT T.R)

variable (A) in
/-- **The adversary followed by a test** (`A^Π`; Unruh 2017, Definition 14, p. 21, Prove with the
test `Π^{H_final}_{x‖π}(S_A)`): the workspace of `A` with a copy register; `A`'s run; after `A`'s
last Kraus map the output is copied (`copyOut`); then the test's channels and its batches, as post
batches (queries to `H_final`). The output is `A`'s output read from the copy register alone, so the
test's maps, which leave the copy register alone, never change it.

Running time: that of `A`, one copy of its output register, and the test's channels and its
`T.queries` queries; polynomial when `A` and the test are. This running time is argued here, not
proved in Lean. -/
noncomputable def withTest : AdaptiveIAlg X Y Req Resp O where
  W := A.W × A.W
  width := A.width
  width_pos := A.width_pos
  slots := A.slots
  post := A.post + T.batches
  budget := A.budget
  kind w := A.kind w.1
  R := Option A.R × Option T.R
  init := MState.reindex A.copySplit.symm (A.init.tensorKet A.copyBlank)
  step := withTestStep T
  out p := A.out p.2

/-- **The output of `A^Π` is `A`'s output at the copy register**, which holds the copied
representative after the junction. -/
theorem withTest_out (w : A.W) (c : A.W) : (A.withTest T).out (w, c) = A.out c :=
  rfl

theorem withTest_width : (A.withTest T).width = A.width :=
  rfl

theorem withTest_post : (A.withTest T).post = A.post + T.batches :=
  rfl

theorem withTest_budget : (A.withTest T).budget = A.budget :=
  rfl

/-- **The queries of `A^Π`** on every branch: `A`'s queries of its query slots and post phase, and
the test's `width * batches`. -/
theorem withTest_queries :
    (A.withTest T).width * ((A.withTest T).budget + (A.withTest T).post) =
      A.width * (A.budget + A.post) + T.queries := by
  rw [withTest_width, withTest_budget, withTest_post, QTest.queries]
  ring

end AdaptiveIAlg

end GordieHowe.Quantum
