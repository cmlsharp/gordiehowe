-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ProgAlg
public import GordieHowe.Model.Quantum.Interactive.PureTest

@[expose] public section

/-!
# The test of the kept registers of a compiled program

A residual-state test (`IAlg.QTest`) of the compiled program `OracleProg.toIAlg p q pad φ hφ`
(`GordieHowe/Model/Quantum/Interactive/ProgAlg.lean`), whose kept pair holds `φ` queried once to the oracle: one
query that uncomputes the answer of the kept pair, then a unitary that maps `φ` to the basis state
`i₀`, then the measurement of the workspace, accepting when the kept pair is `i₀`. On the run of
the compiled program against `H` with the test's query answered by `H`, the kept pair returns to
`φ` (`OracleProg.keptTest_run`), and the test accepts with probability `1`
(`OracleProg.pureRun_withTest_keptTest_toAdaptive`, `GordieHowe/Model/Quantum/Interactive/KeptTestAdaptive.lean`,
for the embedding into the adversaries with run-time kinds).

- `OracleProg.keptTest p q pad φ hφ i₀`: the test. Its channels are `keptSwapNeg` (the exchange of
  the kept pair with the query pair, the answers moved negated) before its one query, then
  `keptSwapNeg` again and the unitary `rotateTo φ hφ i₀` on the kept pair (`keptMat`).
- `OracleProg.regVec T qp χ`: the vector with the table `T`, the kept pair holding `χ` and the
  query pair at `qp`; `OracleProg.progVec` is `regVec` at `φ` queried once (`progVec_eq_regVec`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace OracleProg

open GordieHowe.OracleProg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddCommGroup Y]
  [Nonempty Req] (p : OracleProg X Y O) (q : ℕ) (pad : X)

/-- **Exchange the kept pair with the query pair**, negating the answers moved (an involution). -/
def keptSwapNeg : Equiv.Perm (ProgReg X Y Req Resp q) :=
  Function.Involutive.toPerm (fun r => (((r.1.1.1, ((r.2 0).1, -(r.2 0).2)), r.1.2),
      fun _ => (r.1.1.2.1, -r.1.1.2.2))) fun r => by
    obtain ⟨⟨⟨T, k⟩, rq⟩, qp⟩ := r
    refine Prod.ext (Prod.ext (Prod.ext rfl (Prod.ext rfl (neg_neg _))) rfl) (funext fun j => ?_)
    simp [Fin.fin_one_eq_zero j]

/-- The registers as the kept pair and the rest. -/
def keptSplit : ProgReg X Y Req Resp q ≃
    (X × Y) × ((Fin q → Y) × (Req × Option Resp) × (X × Y)) where
  toFun r := (r.1.1.2, (r.1.1.1, r.1.2, r.2 0))
  invFun s := (((s.2.1, s.1), s.2.2.1), fun _ => s.2.2.2)
  left_inv r := Prod.ext rfl (funext fun j => by rw [Fin.fin_one_eq_zero j])
  right_inv _ := rfl

/-- An operator on the kept pair, acting on the registers. -/
noncomputable def keptMat (V : Matrix (X × Y) (X × Y) ℂ) :
    Matrix (ProgReg X Y Req Resp q) (ProgReg X Y Req Resp q) ℂ :=
  (V ⊗ₖ (1 : Matrix ((Fin q → Y) × (Req × Option Resp) × (X × Y))
    ((Fin q → Y) × (Req × Option Resp) × (X × Y)) ℂ)).submatrix (keptSplit q) (keptSplit q)

omit [AddCommGroup Y] [Nonempty Req] in
theorem keptMat_conjTranspose_mul {V : Matrix (X × Y) (X × Y) ℂ} (hV : Vᴴ * V = 1) :
    (keptMat (Req := Req) (Resp := Resp) q V)ᴴ * keptMat q V = 1 := by
  rw [keptMat, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
    ← mul_kronecker_mul, hV, conjTranspose_one, one_mul, one_kronecker_one, submatrix_one_equiv]

/-- **The vector with the table `T`, the kept pair holding `χ` and the query pair at `qp`**,
the request and response registers blank. -/
noncomputable def regVec (T : Fin q → Y) (qp : X × Y) (χ : QState (X × Y)) :
    QState (ProgReg X Y Req Resp q) :=
  WithLp.toLp 2 fun r => if r.1.1.1 = T ∧ r.1.2 = (req₀, none) ∧ r.2 0 = qp then χ r.1.1.2 else 0

/-- The vector with the table `T`, the kept pair at `kp` and the query pair holding `χ`. -/
noncomputable def swapVec (T : Fin q → Y) (kp : X × Y) (χ : QState (X × Y)) :
    QState (ProgReg X Y Req Resp q) :=
  WithLp.toLp 2 fun r => if r.1.1.1 = T ∧ r.1.2 = (req₀, none) ∧ r.1.1.2 = kp then χ (r.2 0)
    else 0

/-- `χ` with its answer register negated. -/
def negAns (χ : QState (X × Y)) : QState (X × Y) := WithLp.toLp 2 fun a => χ (a.1, -a.2)

/-- `χ` queried once to `H`: `|x, y⟩ ↦ |x, y + H x⟩`. -/
def queried (H : X → Y) (χ : QState (X × Y)) : QState (X × Y) :=
  WithLp.toLp 2 fun a => χ (a.1, a.2 - H a.1)

theorem progVec_eq_regVec (H : X → Y) (φ : QState (X × Y)) (T : Fin q → Y) (qp : X × Y) :
    progVec (Req := Req) (Resp := Resp) q H φ T qp = regVec q T qp (queried H φ) :=
  rfl

theorem permOp_keptSwapNeg_regVec (T : Fin q → Y) (x : X) (y : Y) (χ : QState (X × Y)) :
    permOp (keptSwapNeg (Req := Req) (Resp := Resp) q) (regVec q T (x, y) χ) =
      swapVec q T (x, -y) (negAns χ) := by
  ext r
  obtain ⟨⟨⟨T', kx, ky⟩, rq⟩, qs⟩ := r
  have hs : (keptSwapNeg (Req := Req) (Resp := Resp) q).symm (((T', kx, ky), rq), qs) =
      (((T', ((qs 0).1, -(qs 0).2)), rq), fun _ => (kx, -ky)) := rfl
  rw [permOp_apply, hs]
  simp only [regVec, swapVec, negAns, PiLp.toLp_apply, Prod.ext_iff, neg_eq_iff_eq_neg]

theorem permOp_keptSwapNeg_swapVec (T : Fin q → Y) (x : X) (y : Y) (χ : QState (X × Y)) :
    permOp (keptSwapNeg (Req := Req) (Resp := Resp) q) (swapVec q T (x, y) χ) =
      regVec q T (x, -y) (negAns χ) := by
  ext r
  obtain ⟨⟨⟨T', kx, ky⟩, rq⟩, qs⟩ := r
  have hs : (keptSwapNeg (Req := Req) (Resp := Resp) q).symm (((T', kx, ky), rq), qs) =
      (((T', ((qs 0).1, -(qs 0).2)), rq), fun _ => (kx, -ky)) := rfl
  rw [permOp_apply, hs]
  simp only [regVec, swapVec, negAns, PiLp.toLp_apply, Prod.ext_iff, neg_eq_iff_eq_neg]

theorem permOp_queryPerm_swapVec (H : X → Y) (T : Fin q → Y) (kp : X × Y)
    (χ : QState (X × Y)) :
    permOp (queryPerm H) (swapVec (Req := Req) (Resp := Resp) q T kp χ) =
      swapVec q T kp (queried H χ) := by
  ext r
  have h : ((queryPerm H).symm r).2 0 = ((r.2 0).1, (r.2 0).2 - H (r.2 0).1) := by
    simp [queryPerm, sub_eq_add_neg]
  have h1 : ((queryPerm H).symm r).1 = r.1 := rfl
  rw [permOp_apply, swapVec, swapVec, PiLp.toLp_apply, PiLp.toLp_apply, h, h1]
  rfl

omit [AddCommGroup Y] in
theorem matApply_keptMat_regVec (V : Matrix (X × Y) (X × Y) ℂ) (T : Fin q → Y) (qp : X × Y)
    (χ : QState (X × Y)) :
    matApply (keptMat (Req := Req) (Resp := Resp) q V) (regVec q T qp χ) =
      regVec q T qp (matApply V χ) := by
  ext r
  rw [matApply_apply]
  refine (Fintype.sum_equiv (keptSplit q) _ (fun s => keptMat q V r ((keptSplit q).symm s) *
    regVec q T qp χ ((keptSplit q).symm s)) fun i => by simp).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [keptMat, submatrix_apply, Equiv.apply_symm_apply, kroneckerMap_apply, regVec,
    PiLp.toLp_apply, matApply_apply]
  obtain ⟨⟨⟨T', kp⟩, rq⟩, qs⟩ := r
  simp only [keptSplit, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  by_cases hc : T' = T ∧ rq = (req₀, none) ∧ qs 0 = qp
  · simp only [hc, and_self, ↓reduceIte]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single (T, (req₀, none), qp)]
    · simp [one_apply, hc, keptSplit]
    · intro b _ hb
      have hne : ¬ (b.1 = T ∧ b.2.1 = (req₀, none) ∧ b.2.2 = qp) := fun h =>
        hb (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
      simp only [hne, ↓reduceIte, mul_zero]
    · simp
  · simp only [hc, ↓reduceIte]
    refine sum_eq_zero fun k _ => sum_eq_zero fun b _ => ?_
    by_cases hb : b.1 = T ∧ b.2.1 = (req₀, none) ∧ b.2.2 = qp
    · have hne : (T', rq, qs 0) ≠ b := fun h => hc (by
        rw [← h] at hb
        exact hb)
      simp [one_apply, hne, keptSplit]
    · simp [hb]

/-- The unitary on the kept pair that maps `φ` to the basis state `i₀`, as a matrix. -/
noncomputable def keptRotate (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) :
    Matrix (X × Y) (X × Y) ℂ :=
  unitaryMat (rotateTo φ hφ i₀)

/-- The operator after the test's query: `keptSwapNeg`, then `keptRotate` on the kept pair. -/
noncomputable def keptTestMat1 (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) :
    Matrix (ProgReg X Y Req Resp q) (ProgReg X Y Req Resp q) ℂ :=
  keptMat q (keptRotate φ hφ i₀) * (1 : Matrix _ _ ℂ).submatrix (keptSwapNeg q).symm
    (Equiv.refl _)

omit [Nonempty Req] in
theorem keptTestMat1_conjTranspose_mul (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) :
    (keptTestMat1 (Req := Req) (Resp := Resp) q φ hφ i₀)ᴴ * keptTestMat1 q φ hφ i₀ = 1 := by
  rw [keptTestMat1, conjTranspose_mul, mul_assoc, ← mul_assoc (keptMat q _)ᴴ, keptRotate,
    keptMat_conjTranspose_mul q (unitaryMat_conjTranspose_mul _), one_mul,
    permMat_conjTranspose_mul]

/-- The operators of the test's channels. -/
noncomputable def keptTestMat (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) (b : Fin 2) :
    Matrix (ProgReg X Y Req Resp q) (ProgReg X Y Req Resp q) ℂ :=
  if (b : ℕ) = 0 then (1 : Matrix _ _ ℂ).submatrix (keptSwapNeg q).symm (Equiv.refl _)
  else keptTestMat1 q φ hφ i₀

/-- **The test of the kept pair** (the test of the oracle-test gap lemma): exchange the kept pair
into the query pair (answers negated), one query, exchange back (answers negated again), so the
kept pair holds the answer uncomputed (`uncompute`, `GordieHowe/Model/Quantum/OracleTestBoundary.lean`); then
the unitary `rotateTo φ hφ i₀` on the kept pair and the measurement of the workspace, accepting
when the kept pair is `i₀`: the projective measurement onto `φ` after the uncomputing query.

`rotateTo φ hφ i₀` is some unitary extension of `v ↦ ⟪φ, v⟫ e_{i₀}` (`extendUnitary`, an
existence argument), not an explicit circuit. The acceptance law depends on it only through `φ`:
for every state `Ψ`, `‖(⟨i₀| U ⊗ I) Ψ‖² = ‖(⟨φ| ⊗ I) Ψ‖²` whenever `U^† e_{i₀} = φ`, so the
acceptance probability is that of any circuit mapping `φ` to `i₀`. Only the post-measurement
state differs, and no statement uses it.

Running time: two basis permutations, one query, and one unitary on the kept pair, whose acceptance
law is that of any circuit mapping `φ` to `i₀`; for the Merkle-node superposition of the oracle test
(`SPBCS.Base.oracleTestQBTest`), an `X` gate on the tag bit and `16k` Hadamard gates on the two
digests, run backwards. This running time is argued here, not proved in Lean. -/
noncomputable def keptTest (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) :
    (toIAlg (Req := Req) (Resp := Resp) p q pad φ hφ).QTest where
  batches := 1
  R := Unit
  step b := KrausChannel.ofUnitary (keptTestMat q φ hφ i₀ b) (by
    unfold keptTestMat
    split_ifs
    · exact permMat_conjTranspose_mul _
    · exact keptTestMat1_conjTranspose_mul q φ hφ i₀)
  ok w := w.2 = i₀

/-- The channels of the test have one operator each. -/
theorem keptTest_step_pureAt (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) (b : Fin 2) :
    ((keptTest (Req := Req) (Resp := Resp) p q pad φ hφ i₀).step b).toKrausMap.PureAt ()
      (keptTestMat q φ hφ i₀ b) :=
  KrausChannel.pureAt_toKrausMap rfl fun r hr => absurd (Subsingleton.elim (α := Unit) r ()) hr

/-- The queries of the test: one. -/
theorem keptTest_queries (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y) :
    (keptTest (Req := Req) (Resp := Resp) p q pad φ hφ i₀).queries = 1 :=
  rfl

/-- **The test returns the kept pair to `φ`**: on the run vector, the test's channels and its
query to `H` leave the table and the query pair and turn the kept pair from `φ` queried once to
the basis state `i₀`. -/
theorem keptTest_run (H : X → Y) (φ : QState (X × Y)) (hφ : ‖φ‖ = 1) (i₀ : X × Y)
    (T : Fin q → Y) (x : X) :
    matApply (keptTestMat (Req := Req) (Resp := Resp) q φ hφ i₀ 1) (permOp (queryPerm H)
      (matApply (keptTestMat q φ hφ i₀ 0) (progVec q H φ T (x, 0)))) =
      regVec q T (x, 0) (EuclideanSpace.single i₀ 1) := by
  have h0 : keptTestMat (Req := Req) (Resp := Resp) q φ hφ i₀ 0 =
      (1 : Matrix _ _ ℂ).submatrix (keptSwapNeg q).symm (Equiv.refl _) := rfl
  have h1 : keptTestMat (Req := Req) (Resp := Resp) q φ hφ i₀ 1 = keptTestMat1 q φ hφ i₀ := rfl
  rw [h0, h1, keptTestMat1, matApply_permMat, progVec_eq_regVec, permOp_keptSwapNeg_regVec,
    permOp_queryPerm_swapVec, matApply_mul, matApply_permMat, permOp_keptSwapNeg_swapVec,
    neg_neg, matApply_keptMat_regVec, keptRotate, matApply_unitaryMat]
  have hφ' : negAns (queried H (negAns (queried H φ))) = φ := by
    ext a
    simp only [negAns, queried, PiLp.toLp_apply, neg_sub, sub_neg_eq_add, add_sub_cancel_left]
  rw [hφ', rotateTo_apply_self]

end OracleProg

end GordieHowe.Quantum
