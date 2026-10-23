-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Basic

@[expose] public section

/-!
# Residual-state tests that query the oracle

Unruh 2017 ("Post-quantum security of Fiat-Shamir", ePrint 2017/398), Definition 14, p. 21, tests
the adversary's residual state after its output `x‖π` has been measured: in Prove,
`ok_A ← Π^{H_final}_{x‖π}(S_A)`, where `Π` is a projective measurement circuit (p. 12: the
description of a unitary `U_{M,x}`, after which the outcome qubits are measured) with oracle
access to the final oracle `H_final`.

- `IAlg.QTest A`: a test of the residual state of an interactive adversary `A`: Kraus channels on
  `A`'s registers (`DReg`), one before the first of `batches` batches of `width` queries and one
  after each batch, and the outcome, a predicate `ok` of the workspace measured at the end.
- `IAlg.withTest A T`: the adversary `A` followed by the test (`A^Π`). After `A`'s last Kraus map,
  the output `A.out w` is copied into an extra classical register (`copyOut`, which copies the
  canonical representative `outRep w` of the fibre of `A.out` through `w`, so only the output value
  is measured); then the test's channels and batches act on `A`'s registers and leave the copy
  alone. The test's queries are post-phase queries, so they query the oracle reprogrammed by all the
  challenger's assignments (`KindAlg.postAss`), `H_final`. The output is read from the copy
  (`withTest_out`), so it is `A`'s output measured before the test.

**Modelling choices.** The test's maps are trace preserving (`KrausChannel`), as a projective
measurement circuit is; general channels with a computational-basis outcome are more tests than
Unruh's projective ones. The channels do not depend on `x‖π`: an adversary that keeps a copy of
its output in its residual state (a basis copy, which the measurement of the output makes
classical) lets an unparametrized test read `x‖π`, so the quantifier over adversaries covers
Unruh's family `Π_{x‖π}`. The test makes `width * batches` queries (`QTest.queries`), the
queries of its batches.
-/

open Finset Matrix
open scoped BigOperators MatrixOrder

namespace GordieHowe.Quantum

/-! ### Kraus maps with a larger index set -/

namespace KrausMap

variable {R R' ι : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι]

open Classical in
/-- **`K` with its operators indexed through an injection** `f : R ↪ R'`: the operator of `K` at
`f r`, the zero operator at the indices outside the range of `f`. -/
noncomputable def embedIdx (K : KrausMap R ι ι) (f : R ↪ R') : KrausMap R' ι ι where
  op r' := if h : ∃ r, f r = r' then K.op h.choose else 0
  sum_le := by
    have hg : ∀ r, (if h : ∃ r₀, f r₀ = f r then K.op h.choose else 0) = K.op r := fun r => by
      rw [dif_pos ⟨r, rfl⟩]
      congr 1
      exact f.injective (Exists.choose_spec (⟨r, rfl⟩ : ∃ r₀, f r₀ = f r))
    have hsum : ∑ r', (if h : ∃ r, f r = r' then K.op h.choose else 0)ᴴ *
        (if h : ∃ r, f r = r' then K.op h.choose else 0) = ∑ r, (K.op r)ᴴ * K.op r := by
      rw [← Finset.sum_subset (Finset.subset_univ (univ.map f)) fun r' _ hr' => by
        rw [dif_neg fun ⟨r, hr⟩ => hr' (Finset.mem_map.2 ⟨r, Finset.mem_univ _, hr⟩)]
        simp, Finset.sum_map]
      exact Finset.sum_congr rfl fun r _ => by rw [hg r]
    exact hsum.trans_le K.sum_le

theorem embedIdx_apply (K : KrausMap R ι ι) (f : R ↪ R') (ρ : Matrix ι ι ℂ) :
    (K.embedIdx f) ρ = K ρ := by
  classical
  have hop : ∀ r, (K.embedIdx f).op (f r) = K.op r := fun r => by
    change (if h : ∃ r₀, f r₀ = f r then K.op h.choose else 0) = K.op r
    rw [dif_pos ⟨r, rfl⟩]
    congr 1
    exact f.injective (Exists.choose_spec (⟨r, rfl⟩ : ∃ r₀, f r₀ = f r))
  have hzero : ∀ r', r' ∉ univ.map f → (K.embedIdx f).op r' = 0 := fun r' hr' => by
    change (if h : ∃ r, f r = r' then K.op h.choose else 0) = 0
    rw [dif_neg fun ⟨r, hr⟩ => hr' (Finset.mem_map.2 ⟨r, Finset.mem_univ _, hr⟩)]
  simp only [apply]
  rw [← Finset.sum_subset (Finset.subset_univ (univ.map f)) fun r' _ hr' => by
    rw [hzero r' hr']
    simp, Finset.sum_map]
  exact Finset.sum_congr rfl fun r _ => by rw [hop r]

/-- **Indexing through an injection keeps trace preservation**: the added operators are zero. -/
theorem embedIdx_tp {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) (f : R ↪ R') :
    ∑ r', ((K.embedIdx f).op r')ᴴ * (K.embedIdx f).op r' = 1 := by
  classical
  have hop : ∀ r, (K.embedIdx f).op (f r) = K.op r := fun r => by
    change (if h : ∃ r₀, f r₀ = f r then K.op h.choose else 0) = K.op r
    rw [dif_pos ⟨r, rfl⟩]
    congr 1
    exact f.injective (Exists.choose_spec (⟨r, rfl⟩ : ∃ r₀, f r₀ = f r))
  have hzero : ∀ r', r' ∉ univ.map f → (K.embedIdx f).op r' = 0 := fun r' hr' => by
    change (if h : ∃ r, f r = r' then K.op h.choose else 0) = 0
    rw [dif_neg fun ⟨r, hr⟩ => hr' (Finset.mem_map.2 ⟨r, Finset.mem_univ _, hr⟩)]
  rw [← Finset.sum_subset (Finset.subset_univ (univ.map f)) fun r' _ hr' => by
    rw [hzero r' hr']
    simp, Finset.sum_map]
  rw [← h]
  exact Finset.sum_congr rfl fun r _ => by rw [hop r]

end KrausMap

/-! ### The test -/

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **A residual-state test that queries the oracle** (Unruh 2017, Definition 14, p. 21, the test
`Π^{H_final}_{x‖π}` applied to the residual state `S_A`; the projective measurement circuits of
p. 12, generalized to trace-preserving maps): Kraus channels on the adversary's registers, `step 0`
before the first of `batches` batches of `width` queries and `step (b + 1)` after batch `b`, and
the outcome, a predicate `ok` of the workspace measured in the computational basis at the end. The
module docstring explains why the channels need not depend on `x‖π`. -/
structure QTest (A : IAlg X Y Req Resp O) where
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

variable (A : IAlg X Y Req Resp O)

instance : DecidableEq (DReg A.W A.width X Y Req Resp × A.W) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

/-- The number of queries of a test: `width` per batch. -/
def QTest.queries {A : IAlg X Y Req Resp O} (T : A.QTest) : ℕ := A.width * T.batches

variable {A} (T : A.QTest)

end IAlg

end GordieHowe.Quantum
