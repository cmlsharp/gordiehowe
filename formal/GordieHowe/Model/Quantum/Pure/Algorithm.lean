-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.PermHybrid
public import GordieHowe.Model.Quantum.Core.Measure
public import GordieHowe.Model.Quantum.Core.Oracle
public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Quantum oracle algorithms in the pure-state model

This file defines unitary quantum oracle algorithms of query depth `d`, transcribing the model
of Ambainis, Hamburg and Unruh, "Quantum security proofs using semi-classical oracles"
(CRYPTO 2019, ePrint 2018/904; cited as AHU19), section 2, pp. 8–9. Each sentence of the model
is quoted below with the Lean that transcribes it.

- "Given a function f : X → Y, we model a quantum-accessible oracle O for f as a unitary
  transformation U_f operating on two registers Q, R with spaces C^X and C^Y, respectively,
  where U_f : |q, r⟩ ↦ |q, r ⊕ f(x)⟩, where ⊕ is some involutive group operation (e.g., XOR if
  Y is a set of bitstrings)."
  The space `C^S` of a register with basis `S` is `QState S` (`GordieHowe/Model/Quantum/Core/State.lean`). For
  `n` parallel queries the oracle is `permOp (queryPerm f)` on `QueryReg W n X Y`
  (`GordieHowe/Model/Quantum/Core/Oracle.lean`), the basis permutation that adds `f x_j` to the output register
  `R_j` of every pair `Q_j, R_j`. `Y` is an additive group and `⊕` is `+`; involutivity is not
  used.

- "We say A is a q-query algorithm if it performs at most q oracle queries (counting parallel
  queries as separate queries), and has query depth d if it invokes the oracle at most d times
  (counting parallel queries as one query)."
  An `OracleAlg Z ι d` invokes the oracle exactly `d` times, each time on all of its query
  registers. To model an algorithm that invokes it fewer times, its unitary before an extra
  oracle step moves the contents of the query registers into the work register and puts each
  output register into the uniform superposition `∑ y, |y⟩` (up to normalisation), which every
  shift `y ↦ y + c` fixes; the extra step then acts as the identity. A bound for depth `d` then
  applies with the larger `d`, and the guessing probability of AHU19 Theorem 3 also counts the
  measured query inputs of the extra steps. Counting parallel queries as separate queries: an
  algorithm with `width` query registers and query depth `depth` is modeled by its serialization,
  of query depth `width * depth`.

- "We will make use of the well-known fact that any quantum oracle algorithm A^O(z) can be
  transformed into a unitary quantum oracle algorithm with constant factor computational
  overhead and the same query number and query depth."
  The library proves this fact for finite-dimensional algorithms. A general oracle algorithm is
  `MixedAlg` (`GordieHowe/Model/Quantum/Core/MixedAlg.lean`), Heidler and Unruh's mixed adversary (CPP 2025,
  Definition 6.3, p. 248) with a final measurement: a mixed initial state, Kraus maps between
  the queries (which cover intermediate measurements whose outcomes the algorithm keeps) and a
  general final measurement. Its dilation `MixedAlg.dilate` is an `OracleAlg` with the same query
  depth and the same oracle steps, hence the same query number; its acceptance and guessing
  probabilities equal those of the general algorithm under every oracle
  (`MixedAlg.acceptProb_dilate`, `MixedAlg.guessProb_dilate`). AHU19 Theorem 3 for algorithms
  "not necessarily unitary" is `O2HSetting.o2h_mixed` (`GordieHowe/Model/Quantum/O2H/Mixed.lean`). The
  computational overhead is not modelled.

- "Such an algorithm has registers QA (for its state), and Q1, …, Qn and R1, …, Rn for query
  inputs and outputs, respectively."
  The computational basis is an arbitrary finite type `ι`. For the oracle above it is
  `QueryReg W n X Y = W × (Fin n → X × Y)`: `W` is `QA`, and the `j`-th pair is `Q_j, R_j`.
  Registers are finite-dimensional, as in AHU19 and CMS19; nothing is claimed about
  infinite-dimensional algorithms.

- "It starts with an initial state |Ψ⟩ (that may depend on the input z)."
  `OracleAlg.init : Z → QState ι`, a unit vector for each input `z` (`norm_init`).

- "Then, A alternatingly applies a fixed unitary U on all registers (independent of z and O),
  and performs parallel queries."
  `OracleAlg.step : Z → Fin (d + 1) → (QState ι ≃ₗᵢ[ℂ] QState ι)`. The run on input `z` is
  `step z 0`, oracle, `step z 1`, oracle, …, oracle, `step z d` (`OracleAlg.final`). The leading
  `step z 0` could be absorbed into `init`. Two deviations: one unitary per step in place of one
  fixed `U`, as in Heidler and Unruh's machine-checked definition of pure adversaries
  (Definition 6.2, `run_pure_adv`); and the steps may depend on the input `z` (they never depend on
  the oracle). The second loses no generality: an algorithm with `z`-dependent steps `U_z` is AHU's
  algorithm whose initial state also holds `z` in a register that no step changes, with the fixed
  unitary `∑ z, |z⟩⟨z| ⊗ U_z`. It is what lets queries to other oracles be part of the steps: AHU19
  p. 10 say "additional oracles can simply be encoded as part of z", and a query to an oracle
  encoded in `z` is a `z`-dependent basis permutation inside a step, which is not counted as a query
  to the oracle of the theorem.

- "Parallel queries apply the oracle O to Qi, Ri for each i = 1, …, n. (I.e., if O is
  implemented by U_f, we apply U_f ⊗ ⋯ ⊗ U_f between U-applications.)"
  The oracle of a run is `permOp π` for a basis permutation `π : Equiv.Perm ι`; with
  `π = queryPerm f` it is `U_f ⊗ ⋯ ⊗ U_f` on the query registers and the identity on `W`.

- "Finally, the classical output of A^O(z) is the result of a projective measurement on the
  final state of A."
  Deviation: the measurement is in the computational basis, and a general projective
  measurement is this after a basis change absorbed into `step z d`. The output bit is `1` on
  the outcomes in `OracleAlg.accept z`, so `Pr[b = 1 : b ← A^O(z)]` is
  `acceptProb π z = prob (accept z) (final π z)`. The set may depend on `z` for the same reason
  as the steps.

Classical randomness and the random input `z` are not part of `OracleAlg`: a theorem about a
random setting draws them from a finite probability distribution and averages the pure runs
(`GordieHowe/Model/Quantum/O2H/Basic.lean`).

The file also proves the pure-state core of AHU19 Theorem 3 for an arbitrary basis permutation
oracle: `norm_final_sub_le` (AHU19 Lemma 8, pp. 26–27).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- A unitary quantum oracle algorithm of query depth `d` with inputs in `Z` and computational
basis `ι`: for each input, an initial unit vector, `d + 1` unitaries applied alternately with
`d` oracle steps, and the set of computational-basis outcomes on which it outputs `1`. -/
structure OracleAlg (Z ι : Type*) [Fintype ι] (d : ℕ) where
  /-- The initial state on input `z`. -/
  init : Z → QState ι
  norm_init : ∀ z, ‖init z‖ = 1
  /-- The unitaries on input `z`; `step z k` is applied after the `k`-th oracle step
  (`step z 0` first). -/
  step : Z → Fin (d + 1) → QState ι ≃ₗᵢ[ℂ] QState ι
  /-- The outcomes of the final computational-basis measurement on which the output on input
  `z` is `1`. -/
  accept : Z → Set ι

namespace OracleAlg

variable {Z ι : Type*} [Fintype ι] {d : ℕ} (A : OracleAlg Z ι d)

/-- The unitaries on input `z` indexed by `ℕ`, extended by the identity after `step z d`. -/
noncomputable def stepAt (z : Z) (k : ℕ) : QState ι ≃ₗᵢ[ℂ] QState ι :=
  if h : k < d + 1 then A.step z ⟨k, h⟩ else LinearIsometryEquiv.refl ℂ (QState ι)

theorem stepAt_of_lt {z : Z} {k : ℕ} (h : k < d + 1) : A.stepAt z k = A.step z ⟨k, h⟩ :=
  by simp [stepAt, h]

/-- The run of `A` on input `z` with oracle `permOp π`: `stage π z k` is the state after
`step z k`, just before the `k`-th oracle step (counting from `0`). -/
noncomputable def stage (π : Equiv.Perm ι) (z : Z) : ℕ → QState ι :=
  hybrid (A.stepAt z) (fun _ => permOp π) (A.init z)

/-- The state just before oracle step `i`. -/
noncomputable def pre (π : Equiv.Perm ι) (z : Z) (i : Fin d) : QState ι :=
  A.stage π z i

/-- The final state, after `step z d`. -/
noncomputable def final (π : Equiv.Perm ι) (z : Z) : QState ι :=
  A.stage π z d

/-- The probability that `A` outputs `1` on input `z` with oracle `permOp π`. -/
noncomputable def acceptProb (π : Equiv.Perm ι) (z : Z) : ℝ :=
  prob (A.accept z) (A.final π z)

/-- The probability that the following algorithm gives an outcome in `B`: pick `i` uniformly
among the `d` oracle steps, run `A` on input `z` with oracle `permOp π` until just before
step `i`, and measure in the computational basis. With `B = queried S` this is AHU19's
`Pr[S ∩ T ≠ ∅ : T ← B^π(z)]` for fixed `S` and `z` (Theorem 3, p. 11). For `d = 0` it is `0`. -/
noncomputable def guessProb (B : Set ι) (π : Equiv.Perm ι) (z : Z) : ℝ :=
  𝔼 i, prob B (A.pre π z i)

theorem guessProb_nonneg (B : Set ι) (π : Equiv.Perm ι) (z : Z) : 0 ≤ A.guessProb B π z :=
  expect_nonneg fun _ _ => prob_nonneg B _

@[simp]
theorem norm_stage (π : Equiv.Perm ι) (z : Z) (k : ℕ) : ‖A.stage π z k‖ = 1 := by
  rw [stage, norm_hybrid, A.norm_init]

@[simp]
theorem norm_pre (π : Equiv.Perm ι) (z : Z) (i : Fin d) : ‖A.pre π z i‖ = 1 :=
  A.norm_stage π z i

@[simp]
theorem norm_final (π : Equiv.Perm ι) (z : Z) : ‖A.final π z‖ = 1 :=
  A.norm_stage π z d

/-- The states before the first `k` oracle steps on inputs `z` and `z'` agree if the initial
states agree and the steps applied so far agree. -/
theorem stage_congr {z z' : Z} (π : Equiv.Perm ι) (hinit : A.init z = A.init z') {k : ℕ}
    (hstep : ∀ j : Fin (d + 1), (j : ℕ) ≤ k → A.step z j = A.step z' j) :
    A.stage π z k = A.stage π z' k := by
  have hat : ∀ j ≤ k, A.stepAt z j = A.stepAt z' j := fun j hj => by
    by_cases h : j < d + 1
    · rw [A.stepAt_of_lt h, A.stepAt_of_lt h]
      exact hstep ⟨j, h⟩ hj
    · simp [stepAt, h]
  induction k with
  | zero => simp [stage, hat 0 le_rfl, hinit]
  | succ k ih =>
    rw [stage, hybrid_succ, ← stage, ih (fun j hj => hstep j (hj.trans k.le_succ))
      (fun j hj => hat j (hj.trans k.le_succ)), hat (k + 1) le_rfl, stage, hybrid_succ, ← stage]

/-- The states just before each oracle step on inputs `z` and `z'` agree if the initial states
agree and the steps before the last oracle step agree; `step z d` is not used. -/
theorem pre_congr {z z' : Z} (π : Equiv.Perm ι) (hinit : A.init z = A.init z')
    (hstep : ∀ k : Fin (d + 1), (k : ℕ) < d → A.step z k = A.step z' k) (i : Fin d) :
    A.pre π z i = A.pre π z' i :=
  A.stage_congr π hinit fun k hk => hstep k (hk.trans_lt i.2)

/-- The acceptance probabilities of two runs differ by at most the distance of their final
states. -/
theorem abs_acceptProb_sub_le (π π' : Equiv.Perm ι) (z : Z) :
    |A.acceptProb π z - A.acceptProb π' z| ≤ ‖A.final π z - A.final π' z‖ :=
  abs_prob_sub_le _ (A.norm_final π z) (A.norm_final π' z)

/-- The square roots of the acceptance probabilities of two runs differ by at most the
distance of their final states. -/
theorem abs_sqrt_acceptProb_sub_le (π π' : Equiv.Perm ι) (z : Z) :
    |√(A.acceptProb π z) - √(A.acceptProb π' z)| ≤ ‖A.final π z - A.final π' z‖ :=
  abs_sqrt_prob_sub_le _ _ _

/-- **AHU19 Lemma 8** (pp. 26–27), for basis-permutation oracles: if the oracle permutations
`π` and `π'` agree on every basis state outside `B`, the final states of the two runs on input
`z` are within `2 * d * √(A.guessProb B π z)`. -/
theorem norm_final_sub_le {B : Set ι} {π π' : Equiv.Perm ι} (h : ∀ r ∉ B, π r = π' r) (z : Z) :
    ‖A.final π z - A.final π' z‖ ≤ 2 * d * √(A.guessProb B π z) := by
  have hsum : ∑ i ∈ range d, ‖mask B (A.stage π z i)‖ = d * 𝔼 i, √(prob B (A.pre π z i)) := by
    have hcard := Fintype.card_mul_expect fun i : Fin d => √(prob B (A.pre π z i))
    rw [Fintype.card_fin] at hcard
    rw [hcard, Finset.sum_range]
    simp only [sqrt_prob, pre]
  refine (norm_hybrid_permOp_sub_le (A.stepAt z) (A := fun _ => B) (fun _ => h) (A.init z) d).trans ?_
  change 2 * ∑ i ∈ range d, ‖mask B (A.stage π z i)‖ ≤ _
  rw [mul_assoc, hsum]
  gcongr
  exact Real.expect_sqrt_le_sqrt_expect _ fun i => prob_nonneg B _

end OracleAlg

end GordieHowe.Quantum
