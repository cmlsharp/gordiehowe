-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.LayerSumcheck
public import GordieHowe.ProofSystem.GKR.ClaimEvaluation
public import GordieHowe.Foundations.Probability.ChallengeEvent

@[expose] public section

/-!
# Sumcheck with coefficient messages

Round `i` of an `n`-variable sumcheck sends the `d + 1` coefficients of its
round polynomial `Σ_k c_k X^k`; the verifier checks `p(0) + p(1)` against the
incoming claim, samples `s i`, and continues with `p(s i)`. Variables are
bound in index order, coordinate `0` first, as in `BooleanSkip::prove`/`verify`
(`lib/sumcheck/boolean_skip.h`), which folds adjacent indices `2i, 2i+1`, so its first
challenge binds bit `0` of the group index. The skip itself runs the eq-factored variant
`Sumcheck.EqFactored` (two coefficients per round, no per-round check), whose soundness reduces
to `sound` here on the cubics its updates imply.

The true round polynomials are `GKR.LayerSumcheck.roundPolynomial` of the
summand at the installed prefix. `roundEvent i` is the difference between the
sent and the true round polynomial; it depends on the messages of round `i`
and on the challenges before `i` only (`roundEvent_poly_congr`).
-/

namespace GordieHowe.Sumcheck.Coefficient
open IOP

open Polynomial GKR.LayerSumcheck

variable {K : Type} [Field K] {n d : ℕ}

/-- The round polynomial `Σ_k c k · X^k` of a coefficient message. -/
noncomputable def roundPoly (c : Fin (d + 1) → K) : K[X] :=
  ∑ k, C (c k) * X ^ (k : ℕ)

theorem roundPoly_natDegree_le (c : Fin (d + 1) → K) : (roundPoly c).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp k.isLt)

theorem eval_roundPoly (c : Fin (d + 1) → K) (t : K) :
    (roundPoly c).eval t = ∑ k, c k * t ^ (k : ℕ) := by
  simp [roundPoly, eval_finsetSum]

theorem roundPoly_add (c c' : Fin (d + 1) → K) :
    roundPoly (c + c') = roundPoly c + roundPoly c' := by
  simp [roundPoly, add_mul, Finset.sum_add_distrib]

/-- The coefficients of a polynomial as a message. -/
def coeffs (q : K[X]) : Fin (d + 1) → K := fun k => q.coeff k

theorem roundPoly_coeffs {q : K[X]} (hq : q.natDegree ≤ d) : roundPoly (coeffs (d := d) q) = q := by
  conv_rhs => rw [q.as_sum_range' (d + 1) (Nat.lt_succ_of_le hq)]
  rw [← Fin.sum_univ_eq_sum_range (fun k => monomial k (q.coeff k))]
  simp [roundPoly, coeffs, C_mul_X_pow_eq_monomial]

/-- The value checked against the incoming claim. -/
noncomputable def endpointSum (c : Fin (d + 1) → K) : K :=
  (roundPoly c).eval 0 + (roundPoly c).eval 1

theorem endpointSum_add (c c' : Fin (d + 1) → K) :
    endpointSum (c + c') = endpointSum c + endpointSum c' := by
  simp only [endpointSum, roundPoly_add, eval_add]
  ring

/-- The verifier's running claims: `init`, then `p_i(s i)` after round `i`. -/
noncomputable def claims (init : K) (msg : Fin n → Fin (d + 1) → K) (s : Fin n → K) :
    Fin (n + 1) → K :=
  Fin.cases init fun i => (roundPoly (msg i)).eval (s i)

@[simp] theorem claims_zero (init : K) (msg : Fin n → Fin (d + 1) → K) (s : Fin n → K) :
    claims init msg s 0 = init := rfl

@[simp] theorem claims_succ (init : K) (msg : Fin n → Fin (d + 1) → K) (s : Fin n → K)
    (i : Fin n) : claims init msg s i.succ = (roundPoly (msg i)).eval (s i) := rfl

/-- The claims are linear in the initial claim and the messages jointly. -/
theorem claims_add (init init' : K) (msg msg' : Fin n → Fin (d + 1) → K) (s : Fin n → K)
    (i : Fin (n + 1)) :
    claims (init + init') (msg + msg') s i = claims init msg s i + claims init' msg' s i := by
  refine Fin.cases rfl (fun i => ?_) i
  simp [roundPoly_add]

/-- The verifier's checks, with `final` the value it compares the last claim to. -/
structure Accepts (init : K) (msg : Fin n → Fin (d + 1) → K) (s : Fin n → K) (final : K) :
    Prop where
  rounds : ∀ i, endpointSum (msg i) = claims init msg s i.castSucc
  final : claims init msg s (Fin.last n) = final

/-- The challenges before round `i` installed; later coordinates zero. -/
def prefixPoint (s : Fin n → K) (i : ℕ) : Fin n → K := fun v => if v.val < i then s v else 0

theorem prefixPoint_congr {s s' : Fin n → K} {i : ℕ} (h : ∀ v : Fin n, v.val < i → s v = s' v) :
    prefixPoint s i = prefixPoint s' i := by
  funext v
  unfold prefixPoint
  split_ifs with hv
  · exact h v hv
  · rfl

theorem prefixPoint_succ (s : Fin n → K) (i : Fin n) :
    prefixPoint s (i.val + 1) = Function.update (prefixPoint s i) i (s i) := by
  funext v
  by_cases hv : v = i
  · subst v
    simp [prefixPoint]
  · have hne : v.val ≠ i.val := fun h => hv (Fin.ext h)
    rw [Function.update_of_ne hv]
    unfold prefixPoint
    split_ifs <;> first | rfl | omega

theorem prefixPoint_last (s : Fin n → K) : prefixPoint s n = s := by
  funext v
  simp [prefixPoint]

/-- The variables still to be summed before round `i`. -/
def suffix (n i : ℕ) : List (Fin n) := (List.finRange n).drop i

theorem suffix_cons (i : Fin n) : suffix n i = i :: suffix n (i.val + 1) := by
  unfold suffix
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

theorem suffix_last : suffix n n = [] := by simp [suffix]

/-- Every variable still to be summed before round `i` has index at least `i`. -/
theorem le_of_mem_suffix {i : ℕ} {v : Fin n} (h : v ∈ suffix n i) : i ≤ v.val := by
  obtain ⟨j, hj, e⟩ := List.mem_drop_iff_getElem.mp h
  rw [List.getElem_finRange] at e
  rw [← e]
  simp

variable (p : MvPolynomial (Fin n) K)

/-- The true remaining sum before round `i`. -/
def trueClaim (s : Fin n → K) (i : Fin (n + 1)) : K :=
  marginal p (prefixPoint s i) (suffix n i)

/-- The true round polynomial of round `i`. -/
noncomputable def trueRound (s : Fin n → K) (i : Fin n) : K[X] :=
  roundPolynomial p (prefixPoint s i) i (suffix n (i.val + 1))

theorem trueRound_endpoints (s : Fin n → K) (i : Fin n) :
    (trueRound p s i).eval 0 + (trueRound p s i).eval 1 = trueClaim p s i.castSucc := by
  rw [trueRound, round_endpoints, trueClaim, Fin.val_castSucc, suffix_cons i]

theorem trueRound_eval (s : Fin n → K) (i : Fin n) :
    (trueRound p s i).eval (s i) = trueClaim p s i.succ := by
  rw [trueRound, round_eval, trueClaim, Fin.val_succ, prefixPoint_succ]

theorem trueClaim_last (s : Fin n → K) : trueClaim p s (Fin.last n) = MvPolynomial.eval s p := by
  rw [trueClaim, Fin.val_last, suffix_last, prefixPoint_last, marginal_final]

/-- The initial true claim is the sum of the summand over the Boolean cube. -/
theorem trueClaim_zero (s : Fin n → K) :
    trueClaim p s 0 = ∑ bits : Fin n → Bool,
      MvPolynomial.eval (fun v => GKR.LayerPolynomial.boolValue (bits v)) p := by
  rw [trueClaim, Fin.val_zero, suffix, List.drop_zero]
  exact marginal_complete p _ _ (List.nodup_finRange n) (List.mem_finRange)

theorem trueRound_natDegree_le (hp : ∀ v, p.degreeOf v ≤ d) (s : Fin n → K) (i : Fin n) :
    (trueRound p s i).natDegree ≤ d :=
  (round_degree p _ _ _).trans (hp i)

/-- Round `i` turns a false incoming claim into a true outgoing one: the
challenge is a root of the sent minus the true round polynomial. -/
noncomputable def roundEvent (hp : ∀ v, p.degreeOf v ≤ d) (msg : Fin n → Fin (d + 1) → K)
    (s : Fin n → K) (i : Fin n) : ChallengeEvent K where
  poly := roundPoly (msg i) - trueRound p s i
  deg := d
  natDegree_le := (natDegree_sub_le _ _).trans
    (max_le (roundPoly_natDegree_le _) (trueRound_natDegree_le p hp s i))

/-- The event of round `i` is fixed by the messages and the challenges before `i`. -/
theorem roundEvent_poly_congr (hp : ∀ v, p.degreeOf v ≤ d) (msg : Fin n → Fin (d + 1) → K)
    {s s' : Fin n → K} (i : Fin n) (h : ∀ v : Fin n, v < i → s v = s' v) :
    (roundEvent p hp msg s i).poly = (roundEvent p hp msg s' i).poly := by
  simp only [roundEvent, trueRound, prefixPoint_congr (i := i.val) (fun v hv => h v hv)]

/-- Soundness: if the checks pass and the last claim equals the summand at the
challenge point, the initial claim is the cube sum, or some round event occurred. -/
theorem sound (hp : ∀ v, p.degreeOf v ≤ d) {init : K} {msg : Fin n → Fin (d + 1) → K}
    {s : Fin n → K} (h : Accepts init msg s (MvPolynomial.eval s p)) :
    init = trueClaim p s 0 ∨ ∃ i, (roundEvent p hp msg s i).BadAt (s i) := by
  have key : ∀ j : Fin (n + 1), claims init msg s j = trueClaim p s j ∨
      ∃ i, (roundEvent p hp msg s i).BadAt (s i) := by
    intro j
    induction j using Fin.reverseInduction with
    | last => exact Or.inl (h.final.trans (trueClaim_last p s).symm)
    | cast i ih =>
      rcases ih with hs | hb
      · by_cases hc : claims init msg s i.castSucc = trueClaim p s i.castSucc
        · exact Or.inl hc
        · refine Or.inr ⟨i, ?_, ?_⟩
          · intro hz
            have he : roundPoly (msg i) = trueRound p s i := sub_eq_zero.mp hz
            apply hc
            rw [← h.rounds i, ← trueRound_endpoints, endpointSum, he]
          · change (roundPoly (msg i) - trueRound p s i).eval (s i) = 0
            rw [eval_sub, sub_eq_zero, trueRound_eval, ← hs, claims_succ]
      · exact Or.inr hb
  simpa using key 0

/-- The honest prover's messages: the coefficients of the true round polynomials. -/
noncomputable def honest (s : Fin n → K) : Fin n → Fin (d + 1) → K :=
  fun i => coeffs (trueRound p s i)

theorem claims_honest (hp : ∀ v, p.degreeOf v ≤ d) (s : Fin n → K) (j : Fin (n + 1)) :
    claims (trueClaim p s 0) (honest (d := d) p s) s j = trueClaim p s j := by
  refine Fin.cases rfl (fun i => ?_) j
  rw [claims_succ, honest, roundPoly_coeffs (trueRound_natDegree_le p hp s i), trueRound_eval]

/-- Completeness: the honest messages pass on the true initial claim for every
challenge vector. -/
theorem complete (hp : ∀ v, p.degreeOf v ≤ d) (s : Fin n → K) :
    Accepts (trueClaim p s 0) (honest (d := d) p s) s (MvPolynomial.eval s p) where
  rounds i := by
    rw [claims_honest p hp, endpointSum, honest,
      roundPoly_coeffs (trueRound_natDegree_le p hp s i), trueRound_endpoints]
  final := by rw [claims_honest p hp, trueClaim_last]

end GordieHowe.Sumcheck.Coefficient
