-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.Coefficient
public import GordieHowe.Foundations.Algebra.EqPolynomial
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# Eq-factored sumcheck: the factorization of the round polynomial

A sumcheck over a summand `eq(ρ, x) · f(x)` in which each round sends two coefficients of a
quadratic instead of the four coefficients of the cubic round polynomial (the eq-factoring of
Gruen, "Some Improvements for the PIOP for ZeroCheck", IACR ePrint 2024/108). With the variables bound in index order, the true round polynomial of round `i`
factors as

  `p_i(X) = prefix_i · eq(ρ_i, X) · q_i(X)`,   `prefix_i = ∏_{l < i} eq(ρ_l, s_l)`,

with `q_i(X) = Σ_x eq(ρ_{>i}, x) · f(s_{<i}, X, x)` (`trueRound_eq_mul`, `quad`), a quadratic
when `f` has degree at most two in each variable. The prover sends `q_i`'s coefficients `q1`,
`q2`; the incoming claim `claim = p_i(0) + p_i(1) = prefix_i · (q0 + ρ_i (q1 + q2))` fixes `q0`,
and the verifier continues with the division-free update

  `claim' = eq(ρ_i, s_i) · claim + prefix_{i+1} · ((s_i − ρ_i) · q1 + (s_i² − ρ_i) · q2)`

(`EqFactoredDeg.step`, `EqFactoredDeg.claims` at `D = 2`). No round has a consistency check;
the last claim is compared with the summand at `s`. Source:
`lib/sumcheck/keccak_skip_argument.h:323-343` and `lib/sumcheck/boolean_skip.h:250-269` at `41f8aa26`, where in characteristic two the update
reads `(1 + ρ_i + s_i) · claim + prefix_{i+1} · ((ρ_i + s_i) q1 + (ρ_i + s_i²) q2)`
(`eqLin_charTwo`: `eq(ρ, x) = 1 + (ρ + x)`) and `prefix_n = eq(ρ, s)` weights the terminal check
(`prefixEq_last`, `boolean_skip.h:265-269`). The honest prover's `q1`, `q2` are
`boolean_skip.h:157-165` and `196-212`: the eq table `e` is folded once per round,
`e[k] = e[2k] + e[2k+1]` (lines 140-150, 181, 220), so it holds `eq(ρ_{>i}, ·)` in round `i`.

Soundness and completeness are those of `GordieHowe/ProofSystem/Zerocheck/EqFactoredDeg.lean` at
`D = 2`: each update is the evaluation at `s_i` of a cubic whose endpoint sum is the incoming claim, so each round's event is `Sumcheck.Coefficient.roundEvent` of
the derived messages, of degree three.
-/

namespace GordieHowe.Sumcheck.EqFactored
open IOP

open Polynomial Coefficient GKR.LayerSumcheck
open EqPolynomial (eqPoly eqProd)

variable {K : Type} [Field K] {n : ℕ}

/-! ### One-variable `eq` and the running prefix -/

/-- `eq(ρ, x) = ρ x + (1 − ρ)(1 − x)`, one factor of `EqPolynomial.eqProd`. -/
def eqLin (ρ x : K) : K := ρ * x + (1 - ρ) * (1 - x)

@[simp] theorem eqLin_zero (ρ : K) : eqLin ρ 0 = 1 - ρ := by simp [eqLin]

@[simp] theorem eqLin_one (ρ : K) : eqLin ρ 1 = ρ := by simp [eqLin]

/-- In characteristic two the factor is `1 + ρ + x` (`eq_i = 1 + ρ_i + s`,
`keccak_skip_argument.h:335`). -/
theorem eqLin_charTwo [CharP K 2] (ρ x : K) : eqLin ρ x = 1 + (ρ + x) := by
  unfold eqLin
  linear_combination (ρ * x - ρ - x) * CharTwo.two_eq_zero (R := K)

/-- `eq(ρ, X)` as a polynomial in `X`. -/
noncomputable def eqLinPoly (ρ : K) : K[X] := C ρ * X + C (1 - ρ) * (1 - X)

@[simp] theorem eval_eqLinPoly (ρ x : K) : (eqLinPoly ρ).eval x = eqLin ρ x := by
  simp [eqLinPoly, eqLin]

/-- The running prefix `∏_{l < i} eq(ρ_l, s_l)`. -/
def prefixEq (ρ s : Fin n → K) (i : ℕ) : K :=
  ∏ l ∈ Finset.univ.filter (fun l : Fin n => l.val < i), eqLin (ρ l) (s l)

@[simp] theorem prefixEq_zero (ρ s : Fin n → K) : prefixEq ρ s 0 = 1 := by
  simp [prefixEq]

theorem prefixEq_succ (ρ s : Fin n → K) (i : Fin n) :
    prefixEq ρ s (i.val + 1) = prefixEq ρ s i * eqLin (ρ i) (s i) := by
  unfold prefixEq
  have he : Finset.univ.filter (fun l : Fin n => l.val < i.val + 1) =
      insert i (Finset.univ.filter fun l : Fin n => l.val < i.val) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [he, Finset.prod_insert (by simp), mul_comm]

/-- After the last round the prefix is `eq(ρ, s)`. -/
theorem prefixEq_last (ρ s : Fin n → K) : prefixEq ρ s n = eqProd ρ s := by
  unfold prefixEq eqProd
  rw [Finset.filter_true_of_mem fun l _ => l.isLt]
  rfl

theorem prefixEq_congr (ρ : Fin n → K) {s s' : Fin n → K} {i : ℕ}
    (hs : ∀ l : Fin n, l.val < i → s l = s' l) : prefixEq ρ s i = prefixEq ρ s' i :=
  Finset.prod_congr rfl fun l hl => by rw [hs l (Finset.mem_filter.mp hl).2]

/-! ### The verifier's claims -/

/-! ### The factored true round polynomial -/

section Factor

open MvPolynomial (eval₂)

/-- The factors of `eqPoly ρ` up to coordinate `i`. -/
noncomputable def eqUpTo (ρ : Fin n → K) (i : Fin n) : MvPolynomial (Fin n) K :=
  ∏ v ∈ Finset.univ.filter (fun v => v ≤ i),
    (MvPolynomial.C (ρ v) * MvPolynomial.X v + MvPolynomial.C (1 - ρ v) * (1 - MvPolynomial.X v))

/-- `eq(ρ_{>i}, x)`: the factors of `eqPoly ρ` after coordinate `i`. -/
noncomputable def eqAfter (ρ : Fin n → K) (i : Fin n) : MvPolynomial (Fin n) K :=
  ∏ v ∈ Finset.univ.filter (fun v => i < v),
    (MvPolynomial.C (ρ v) * MvPolynomial.X v + MvPolynomial.C (1 - ρ v) * (1 - MvPolynomial.X v))

theorem eqPoly_eq_mul (ρ : Fin n → K) (i : Fin n) : eqPoly ρ = eqUpTo ρ i * eqAfter ρ i := by
  unfold eqPoly eqUpTo eqAfter
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => v ≤ i)]
  congr 1
  exact Finset.prod_congr (Finset.filter_congr fun v _ => not_le) fun _ _ => rfl

/-- `eq(ρ_{>i}, ·)` has degree zero in coordinate `i`. -/
theorem degreeOf_eqAfter (ρ : Fin n → K) (i : Fin n) : (eqAfter ρ i).degreeOf i = 0 := by
  refine Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_prod_le i _ _).trans ?_)
  refine (Finset.sum_le_sum fun v hv => EqPolynomial.degreeOf_eqFactor_le (ρ v) v i).trans ?_
  refine (Finset.sum_eq_zero fun v hv => ?_).le
  have : i ≠ v := ne_of_lt (Finset.mem_filter.mp hv).2
  simp [this]

/-- The factors up to `i` do not read the coordinates summed after round `i`. -/
theorem eval₂_eqUpTo_update (ρ : Fin n → K) (i : Fin n) {R : Type} [CommRing R]
    (base : K →+* R) {v : Fin n} (hv : i < v) (e : Fin n → R) (x : R) :
    eval₂ base (Function.update e v x) (eqUpTo ρ i) = eval₂ base e (eqUpTo ρ i) := by
  unfold eqUpTo
  rw [MvPolynomial.eval₂_prod, MvPolynomial.eval₂_prod]
  refine Finset.prod_congr rfl fun u hu => ?_
  have hu' : u ≠ v := ne_of_lt (lt_of_le_of_lt (Finset.mem_filter.mp hu).2 hv)
  simp [Function.update_of_ne hu']

/-- At the installed prefix with `X` at coordinate `i`, the factors up to `i` are
`prefix_i · eq(ρ_i, X)`. -/
theorem eval₂_eqUpTo (ρ s : Fin n → K) (i : Fin n) :
    eval₂ C (Function.update (C ∘ prefixPoint s i) i X) (eqUpTo ρ i) =
      C (prefixEq ρ s i) * eqLinPoly (ρ i) := by
  unfold eqUpTo prefixEq
  have he : Finset.univ.filter (fun v : Fin n => v ≤ i) =
      insert i (Finset.univ.filter fun v : Fin n => v.val < i.val) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def,
      Fin.ext_iff]
    omega
  rw [he, Finset.prod_insert (by simp), MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod,
    map_prod, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvi : v.val < i.val := (Finset.mem_filter.mp hv).2
    have hne : v ≠ i := fun h => by rw [h] at hvi; omega
    simp [Function.update_of_ne hne, prefixPoint, hvi, eqLin]
  · simp [eqLinPoly]

/-- The quadratic factor of round `i`: `q_i(X) = Σ_x eq(ρ_{>i}, x) · f(s_{<i}, X, x)`. -/
noncomputable def quad (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) (s : Fin n → K) (i : Fin n) :
    K[X] :=
  roundPolynomial (eqAfter ρ i * f) (prefixPoint s i) i (suffix n (i.val + 1))

/-- **The true round polynomial factors**: `p_i(X) = prefix_i · eq(ρ_i, X) · q_i(X)`. -/
theorem trueRound_eq_mul (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) (s : Fin n → K)
    (i : Fin n) :
    trueRound (eqPoly ρ * f) s i = C (prefixEq ρ s i) * eqLinPoly (ρ i) * quad ρ f s i := by
  rw [trueRound, eqPoly_eq_mul ρ i, mul_assoc, roundPolynomial,
    marginal₂_mul_of_const _ _ _ _ _ fun v hv e x =>
      eval₂_eqUpTo_update ρ i C (Nat.lt_of_succ_le (le_of_mem_suffix hv)) e x,
    eval₂_eqUpTo]
  rfl

/-- The coefficients of the quadratic factor are marginals over the coordinates after `i` of the
coefficients of the substitution with `X` at `i` (`GKR.LayerSumcheck.coeff_roundPolynomial`). -/
theorem coeff_quad (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) (s : Fin n → K) (i : Fin n)
    (k : ℕ) :
    (quad ρ f s i).coeff k =
      marginalFn (fun e => (eval₂ C (Function.update (C ∘ e) i X) (eqAfter ρ i * f)).coeff k)
        (prefixPoint s i) (suffix n (i.val + 1)) :=
  coeff_roundPolynomial _ _ _ _ (fun h => by have := le_of_mem_suffix h; omega) k

/-- `eq(ρ_{>i}, e)`: the factors of `eqProd ρ e` after coordinate `i`. -/
def eqAfterEval (ρ : Fin n → K) (i : Fin n) (e : Fin n → K) : K :=
  ∏ v ∈ Finset.univ.filter (fun v => i < v), eqLin (ρ v) (e v)

/-- `eqAfter ρ i` does not read coordinate `i`: the substitution with `X` at `i` is the constant
`eqAfterEval ρ i e`. -/
theorem eval₂_eqAfter (ρ : Fin n → K) (i : Fin n) (e : Fin n → K) :
    eval₂ C (Function.update (C ∘ e) i X) (eqAfter ρ i) = C (eqAfterEval ρ i e) := by
  unfold eqAfter eqAfterEval
  rw [MvPolynomial.eval₂_prod, map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hne : v ≠ i := (ne_of_lt (Finset.mem_filter.mp hv).2).symm
  simp [Function.update_of_ne hne, eqLin]

theorem quad_congr (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) {s s' : Fin n → K} (i : Fin n)
    (hs : ∀ l, l < i → s l = s' l) : quad ρ f s i = quad ρ f s' i := by
  rw [quad, quad, prefixPoint_congr (i := i.val) fun l hl => hs l hl]

end Factor

end GordieHowe.Sumcheck.EqFactored
