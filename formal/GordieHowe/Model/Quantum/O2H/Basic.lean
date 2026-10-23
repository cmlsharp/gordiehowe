-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Algorithm
public import GordieHowe.Foundations.ToMathlib.SqrtAverage
public import GordieHowe.Foundations.Probability.Advantage

@[expose] public section

/-!
# One-way to hiding (AHU19 Theorem 3)

AHU19 Theorem 3 (Ambainis, Hamburg, Unruh, CRYPTO 2019, ePrint 2018/904, pp. 11–12): if two
oracles `G` and `H` agree outside a set `S`, an algorithm of query depth `d` distinguishes them
with advantage at most `2 * d * √P_guess`, where `P_guess` is the probability that measuring
the query inputs just before a uniformly chosen oracle step finds an element of `S`.

`S`, `G`, `H` and the input `z` are random with an arbitrary joint distribution. Here they are
functions of an outcome `ω` of a probability distribution `μ` on a finite type `Ω`, bundled
with the agreement hypothesis as an `O2HSetting`. The three probabilities of the theorem are
`O2HSetting.pLeft`, `pRight` and `pGuess`, each the `μ`-average of the corresponding pure-run
quantity of `GordieHowe/Model/Quantum/Pure/Algorithm.lean`.

The oracles and the set may also depend on the content `w` of the work register: the oracle is
`queryPermOf (H ω)`, which applies `H ω w`, and `S ω w` is the set where `G ω w` and `H ω w` may
differ. This covers an oracle that depends on classical data the algorithm holds, such as the
logged requests of a game (`GordieHowe/Model/Quantum/Pure/Game.lean`), where the oracle in force depends on the
earlier requests. AHU19's statement is the case where nothing depends on `w` (`O2HSetting.ofFun`,
with `queryPermOf_const` and `queriedOf_const`). The proof is unchanged: Lemma 8 holds for any
two basis permutations that agree outside a set of basis states.

The proof follows AHU19 section 5.4. For each `ω`, Lemma 8 (`OracleAlg.norm_final_sub_le`)
bounds the distance of the final states by `2 * d * √(guess probability at ω)`. The two final
measurement lemmas of `GordieHowe/Model/Quantum/Core/Measure.lean` turn that into bounds on the acceptance
probabilities and on their square roots; they replace AHU19's Lemma 9 and Lemmas 3–4 (mixed
states, fidelity and Bures distance), which the pure-state model does not need. Averaging over
`μ` uses Jensen's inequality for the square root and, for the square-root form, the reverse
triangle inequality in the weighted `L²` norm (`GordieHowe/Foundations/ToMathlib/SqrtAverage.lean`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- The random data of AHU19 Theorem 3: a set `S ω w`, two oracle functions `G ω w` and `H ω w`
that agree outside `S ω w`, and an input `z ω`, all functions of an outcome `ω` drawn from `μ`,
so their joint distribution is arbitrary. The oracles and the set may depend on the content `w`
of the work register `W`. -/
structure O2HSetting (Ω Z W X Y : Type*) where
  /-- The distribution of the outcome `ω`. -/
  μ : PMF Ω
  /-- The set on which the oracles may differ. -/
  S : Ω → W → Set X
  G : Ω → W → X → Y
  H : Ω → W → X → Y
  /-- The input of the algorithm. -/
  z : Ω → Z
  /-- AHU19's hypothesis `∀ x ∉ S. G(x) = H(x)`, for each content of the work register. -/
  agree : ∀ ω w, ∀ x ∉ S ω w, G ω w x = H ω w x

namespace O2HSetting

variable {Ω Z X Y W : Type*} [Fintype Ω] [Fintype W] [Fintype X] [Fintype Y] [AddGroup Y]
  {n d : ℕ} (s : O2HSetting Ω Z W X Y) (A : OracleAlg Z (QueryReg W n X Y) d)

/-- The same setting with `G` and `H` exchanged. -/
def swap : O2HSetting Ω Z W X Y where
  μ := s.μ
  S := s.S
  G := s.H
  H := s.G
  z := s.z
  agree ω w x hx := (s.agree ω w x hx).symm

/-- `P_left = Pr[b = 1 : b ← A^H(z)]`. -/
noncomputable def pLeft : ℝ :=
  ∑ ω, (s.μ ω).toReal * A.acceptProb (queryPermOf (s.H ω)) (s.z ω)

/-- `P_right = Pr[b = 1 : b ← A^G(z)]`. -/
noncomputable def pRight : ℝ :=
  ∑ ω, (s.μ ω).toReal * A.acceptProb (queryPermOf (s.G ω)) (s.z ω)

/-- `P_guess = Pr[S ∩ T ≠ ∅ : T ← B^F(z)]`, where `B^F` picks `i` uniformly among the `d`
oracle steps, runs `A^F(z)` until just before step `i`, and measures all query input registers
in the computational basis, giving the set `T` of measured inputs (`prob_queried`). AHU19 use
`F = H`, and remark that `F = G` also works. -/
noncomputable def pGuess (F : Ω → W → X → Y) : ℝ :=
  ∑ ω, (s.μ ω).toReal * A.guessProb (queriedOf (s.S ω)) (queryPermOf (F ω)) (s.z ω)

@[simp] theorem swap_pLeft : s.swap.pLeft A = s.pRight A := rfl

@[simp] theorem swap_pRight : s.swap.pRight A = s.pLeft A := rfl

@[simp] theorem swap_pGuess (F : Ω → W → X → Y) : s.swap.pGuess A F = s.pGuess A F := rfl

omit [Fintype Ω] in
/-- AHU19 Lemma 8 at one outcome `ω`: the final states of `A^H(z)` and `A^G(z)` are within
`2 * d * √(guess probability of B^H at ω)`. -/
theorem norm_final_sub_le (ω : Ω) :
    ‖A.final (queryPermOf (s.H ω)) (s.z ω) - A.final (queryPermOf (s.G ω)) (s.z ω)‖ ≤
      2 * d * √(A.guessProb (queriedOf (s.S ω)) (queryPermOf (s.H ω)) (s.z ω)) :=
  A.norm_final_sub_le
    (queryPermOf_eq_of_notMem_queriedOf fun w x hx => (s.agree ω w x hx).symm) (s.z ω)

/-- The `μ`-average of the square root of the guess probability is at most the square root
of `pGuess` (Jensen). -/
theorem sum_mul_sqrt_guessProb_le (F : Ω → W → X → Y) :
    ∑ ω, (s.μ ω).toReal * √(A.guessProb (queriedOf (s.S ω)) (queryPermOf (F ω)) (s.z ω)) ≤
      √(s.pGuess A F) :=
  Real.sum_mul_sqrt_le_sqrt_sum_mul (fun _ => ENNReal.toReal_nonneg) s.μ.sum_toReal
    fun _ => A.guessProb_nonneg _ _ _

/-- **AHU19 Theorem 3** (pp. 11–12): "Let S ⊆ X be random. Let G, H : X → Y be random
functions satisfying ∀x ∉ S. G(x) = H(x). Let z be a random bitstring. (S, G, H, z may have
arbitrary joint distribution.) Let A be quantum oracle algorithm with query depth d (not
necessarily unitary). Let B^H be an oracle algorithm that on input z does the following: pick
i ← {1, …, d}, run A^H(z) until (just before) the i-th query, measure all query input
registers in the computational basis, output the set T of measurement outcomes. Let
P_left := Pr[b = 1 : b ← A^H(z)], P_right := Pr[b = 1 : b ← A^G(z)],
P_guess := Pr[S ∩ T ≠ ∅ : T ← B^H(z)]. Then |P_left − P_right| ≤ 2d √P_guess."

`A` is unitary. The theorem for algorithms that are not necessarily unitary is
`O2HSetting.o2h_mixed` (`GordieHowe/Model/Quantum/O2H/Mixed.lean`), derived from this one by dilation. -/
theorem o2h : GordieHowe.advantage (s.pLeft A) (s.pRight A) ≤ 2 * d * √(s.pGuess A s.H) := by
  have hw : ∀ ω, 0 ≤ (s.μ ω).toReal := fun _ => ENNReal.toReal_nonneg
  rw [GordieHowe.advantage, pLeft, pRight, ← sum_sub_distrib]
  calc |∑ ω, ((s.μ ω).toReal * A.acceptProb (queryPermOf (s.H ω)) (s.z ω) -
          (s.μ ω).toReal * A.acceptProb (queryPermOf (s.G ω)) (s.z ω))|
      ≤ ∑ ω, (s.μ ω).toReal *
          |A.acceptProb (queryPermOf (s.H ω)) (s.z ω) -
            A.acceptProb (queryPermOf (s.G ω)) (s.z ω)| := by
        refine (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun ω _ => ?_)
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw ω)]
    _ ≤ ∑ ω, (s.μ ω).toReal *
          (2 * d * √(A.guessProb (queriedOf (s.S ω)) (queryPermOf (s.H ω)) (s.z ω))) := by
        gcongr with ω
        exact (A.abs_acceptProb_sub_le _ _ _).trans (s.norm_final_sub_le A ω)
    _ = 2 * d * ∑ ω, (s.μ ω).toReal *
          √(A.guessProb (queriedOf (s.S ω)) (queryPermOf (s.H ω)) (s.z ω)) := by
        rw [mul_sum]
        exact sum_congr rfl fun ω _ => by ring
    _ ≤ 2 * d * √(s.pGuess A s.H) := by
        gcongr
        exact s.sum_mul_sqrt_guessProb_le A s.H

/-- **AHU19 Theorem 3** (pp. 11–12), square-root form: with `P_left`, `P_right` and `P_guess`
as in `o2h`, "|√P_left − √P_right| ≤ 2d √P_guess". -/
theorem o2h_sqrt : |√(s.pLeft A) - √(s.pRight A)| ≤ 2 * d * √(s.pGuess A s.H) := by
  have hw : ∀ ω, 0 ≤ (s.μ ω).toReal := fun _ => ENNReal.toReal_nonneg
  refine (Real.abs_sqrt_sum_mul_sub_sqrt_sum_mul_le hw (fun _ => prob_nonneg _ _)
    fun _ => prob_nonneg _ _).trans ?_
  have hpoint : ∀ ω, (√(A.acceptProb (queryPermOf (s.H ω)) (s.z ω)) -
      √(A.acceptProb (queryPermOf (s.G ω)) (s.z ω))) ^ 2 ≤
      (2 * d) ^ 2 * A.guessProb (queriedOf (s.S ω)) (queryPermOf (s.H ω)) (s.z ω) := fun ω => by
    rw [← Real.sq_sqrt (A.guessProb_nonneg _ _ _), ← mul_pow, ← sq_abs]
    gcongr
    exact (A.abs_sqrt_acceptProb_sub_le _ _ _).trans (s.norm_final_sub_le A ω)
  calc √(∑ ω, (s.μ ω).toReal * (√(A.acceptProb (queryPermOf (s.H ω)) (s.z ω)) -
          √(A.acceptProb (queryPermOf (s.G ω)) (s.z ω))) ^ 2)
      ≤ √(∑ ω, (s.μ ω).toReal *
          ((2 * d) ^ 2 * A.guessProb (queriedOf (s.S ω)) (queryPermOf (s.H ω)) (s.z ω))) := by
        gcongr with ω
        exact hpoint ω
    _ = 2 * d * √(s.pGuess A s.H) := by
        simp_rw [mul_left_comm _ ((2 * (d : ℝ)) ^ 2)]
        rw [← mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), pGuess]

/-- **AHU19 Theorem 3** with `B^G` in place of `B^H` ("The same result holds with B^G instead
of B^H in the definition of P_guess", p. 12). -/
theorem o2h_guessG : GordieHowe.advantage (s.pLeft A) (s.pRight A) ≤ 2 * d * √(s.pGuess A s.G) := by
  have h := s.swap.o2h A
  rwa [swap_pLeft, swap_pRight, GordieHowe.advantage_comm] at h

/-- **AHU19 Theorem 3**, square-root form, with `B^G` in place of `B^H`. -/
theorem o2h_sqrt_guessG : |√(s.pLeft A) - √(s.pRight A)| ≤ 2 * d * √(s.pGuess A s.G) := by
  have h := s.swap.o2h_sqrt A
  rwa [swap_pLeft, swap_pRight, abs_sub_comm] at h

/-! ### Oracles that do not depend on the work register -/

/-- AHU19's setting: the set and the oracles do not depend on the work register. -/
def ofFun (μ : PMF Ω) (S : Ω → Set X) (G H : Ω → X → Y) (z : Ω → Z)
    (agree : ∀ ω, ∀ x ∉ S ω, G ω x = H ω x) : O2HSetting Ω Z W X Y where
  μ := μ
  S ω _ := S ω
  G ω _ := G ω
  H ω _ := H ω
  z := z
  agree ω _ := agree ω

variable (μ : PMF Ω) (S : Ω → Set X) (G H : Ω → X → Y) (z : Ω → Z)
  (agree : ∀ ω, ∀ x ∉ S ω, G ω x = H ω x)

/-- In AHU19's setting, `pLeft` is the average acceptance probability with `queryPerm`. -/
theorem ofFun_pLeft : (ofFun (W := W) μ S G H z agree).pLeft A =
    ∑ ω, (μ ω).toReal * A.acceptProb (queryPerm (H ω)) (z ω) := by
  simp only [pLeft, ofFun, queryPermOf_const]

/-- In AHU19's setting, `pRight` is the average acceptance probability with `queryPerm`. -/
theorem ofFun_pRight : (ofFun (W := W) μ S G H z agree).pRight A =
    ∑ ω, (μ ω).toReal * A.acceptProb (queryPerm (G ω)) (z ω) := by
  simp only [pRight, ofFun, queryPermOf_const]

/-- In AHU19's setting, `pGuess` is the average guessing probability of `queried`. -/
theorem ofFun_pGuess (F : Ω → X → Y) :
    (ofFun (W := W) μ S G H z agree).pGuess A (fun ω _ => F ω) =
      ∑ ω, (μ ω).toReal * A.guessProb (queried (S ω)) (queryPerm (F ω)) (z ω) := by
  simp only [pGuess, ofFun, queryPermOf_const, queriedOf_const]

end O2HSetting

end GordieHowe.Quantum
