-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.EqFactored

@[expose] public section

/-!
# Eq-factored sumcheck with `D` sent coefficients

The eq-factored sumcheck of `GordieHowe/ProofSystem/Zerocheck/EqFactored.lean` for a summand `eq(ρ, x) · f(x)` with `f`
of degree at most `D` in each variable. With the variables bound in index order, round `i`'s
true round polynomial factors as `p_i(X) = prefix_i · eq(ρ_i, X) · q_i(X)` (`EqFactored.trueRound_eq_mul`) with `q_i` of degree at
most `D` (`quad_natDegree_le_degreeOf`). The prover sends the coefficients `q_1, …, q_D` of `q_i`
(`q_0` is fixed by the incoming claim), and the verifier continues with

  `claim' = eq(ρ_i, s_i) · claim + prefix_{i+1} · Σ_{d<D} (s_i^(d+1) − ρ_i) · q_{d+1}`

(`step`, `claims`). No round has a check of its own; the last claim is compared with the summand
at `s`.

Source: `lib/gordiehowe/compiler/field_skip.h` at the C++ of `a9d05d59`, `MaskedFieldSkip::rows_of`
(the comment "claim = prefix (q0 + rho_i sum_d q_d) fixes q0; the next claim is eq_i(s) claim +
prefix eq_i(s) sum_d (s^d - rho_i) q_d", and the loop over `d < D` with `sd = s^(d+1)`), with
`eq(ρ, x) = 1 − ρ − x + 2ρx` (`MaskedFieldSkip::eq`, `EqFactored.eqLin` up to `ring`); the honest
messages are `MaskedFieldSkip::prove`'s `msg = q[1..D]`, the coefficients of
`Σ_i e_i Q(x0 + X dx)`.

Soundness reduces to `Sumcheck.Coefficient` at degree `D + 1`: each update is the evaluation at
`s_i` of the polynomial `impliedRound` of degree `D + 1`, whose endpoint sum is the incoming claim
for every message (`impliedRound_endpoints`), so each round's event is
`Coefficient.roundEvent` of the derived messages (`sound`).
-/

namespace GordieHowe.Sumcheck.EqFactoredDeg
open IOP

open Polynomial Coefficient GKR.LayerSumcheck
open EqFactored (eqLin eqLinPoly prefixEq eqLin_zero eqLin_one prefixEq_succ prefixEq_congr)
open EqPolynomial (eqPoly eqProd)

variable {K : Type} [Field K] {n D : ℕ}

/-! ### The verifier's claims -/

section Claims

variable {M : Type} [AddCommGroup M] [Module K M]

/-- The verifier's update in round `i` from the incoming claim `c`:
`eq(ρ_i, s_i) · c + prefix_{i+1} · Σ_{d<D} (s_i^(d+1) − ρ_i) · q_i d`. -/
def step (ρ s : Fin n → K) (q : Fin n → Fin D → M) (i : Fin n) (c : M) : M :=
  eqLin (ρ i) (s i) • c +
    prefixEq ρ s (i.val + 1) • ∑ d : Fin D, (s i ^ (d.val + 1) - ρ i) • q i d

/-- The verifier's running claims: `init`, then `step` after each round. -/
def claims (init : M) (ρ : Fin n → K) (q : Fin n → Fin D → M) (s : Fin n → K) :
    Fin (n + 1) → M :=
  fun j => Fin.induction (motive := fun _ => M) init (fun i c => step ρ s q i c) j

@[simp] theorem claims_zero (init : M) (ρ : Fin n → K) (q : Fin n → Fin D → M) (s : Fin n → K) :
    claims init ρ q s 0 = init := rfl

theorem claims_succ (init : M) (ρ : Fin n → K) (q : Fin n → Fin D → M) (s : Fin n → K)
    (i : Fin n) : claims init ρ q s i.succ = step ρ s q i (claims init ρ q s i.castSucc) :=
  Fin.induction_succ _ _ i

/-- A `K`-linear map commutes with the claims. -/
theorem map_claims {N : Type} [AddCommGroup N] [Module K N] (φ : M →ₗ[K] N) (init : M)
    (ρ : Fin n → K) (q : Fin n → Fin D → M) (s : Fin n → K) (j : Fin (n + 1)) :
    φ (claims init ρ q s j) = claims (φ init) ρ (fun i d => φ (q i d)) s j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih => simp only [claims_succ, step, map_add, map_smul, map_sum, ih]

/-- The claims are additive in the initial claim and the messages jointly. -/
theorem claims_add (init init' : M) (ρ : Fin n → K) (q q' : Fin n → Fin D → M) (s : Fin n → K)
    (j : Fin (n + 1)) :
    claims (init + init') ρ (q + q') s j = claims init ρ q s j + claims init' ρ q' s j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
    simp only [claims_succ, step, ih, Pi.add_apply, smul_add, Finset.sum_add_distrib]
    abel

/-- Claim `j` reads the messages and the challenges before `j` only. -/
theorem claims_congr (init : M) (ρ : Fin n → K) {q q' : Fin n → Fin D → M} {s s' : Fin n → K}
    (j : Fin (n + 1)) (hq : ∀ l : Fin n, l.val < j.val → q l = q' l)
    (hs : ∀ l : Fin n, l.val < j.val → s l = s' l) :
    claims init ρ q s j = claims init ρ q' s' j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hq' : ∀ l : Fin n, l.val < i.castSucc.val → q l = q' l := fun l hl =>
      hq l (by simp only [Fin.val_succ, Fin.val_castSucc] at hl ⊢; omega)
    have hs' : ∀ l : Fin n, l.val < i.castSucc.val → s l = s' l := fun l hl =>
      hs l (by simp only [Fin.val_succ, Fin.val_castSucc] at hl ⊢; omega)
    have hi : i.val < i.succ.val := by simp
    rw [claims_succ, claims_succ, ih hq' hs', step, step, hq i hi, hs i hi,
      prefixEq_congr ρ fun l hl => hs l (by simpa using hl)]

end Claims

/-! ### Reduction to the coefficient sumcheck -/

/-- The polynomial of degree `D + 1` that the update evaluates:
`eq(ρ, X) · (c + pre · Σ_{d<D} (X^(d+1) − ρ) · q_d)`, for the incoming claim `c` and the prefix
`pre`. -/
noncomputable def impliedRound (ρ pre c : K) (q : Fin D → K) : K[X] :=
  eqLinPoly ρ * (C c + C pre * ∑ d : Fin D, (X ^ (d.val + 1) - C ρ) * C (q d))

theorem impliedRound_natDegree_le (ρ pre c : K) (q : Fin D → K) :
    (impliedRound ρ pre c q).natDegree ≤ D + 1 := by
  unfold impliedRound
  refine (natDegree_mul_le).trans ?_
  have h1 : (eqLinPoly ρ).natDegree ≤ 1 := by
    unfold eqLinPoly
    compute_degree
  have h2 : (C c + C pre * ∑ d : Fin D, (X ^ (d.val + 1) - C ρ) * C (q d)).natDegree ≤ D := by
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
    refine (natDegree_mul_C_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ (by simp)))
    rw [natDegree_X_pow]
    omega
  omega

theorem eval_impliedRound (ρ pre c : K) (q : Fin D → K) (x : K) :
    (impliedRound ρ pre c q).eval x =
      eqLin ρ x * (c + pre * ∑ d : Fin D, (x ^ (d.val + 1) - ρ) * q d) := by
  simp [impliedRound, eval_finsetSum]

/-- The implied polynomial's endpoint sum is the incoming claim, for every message. -/
theorem impliedRound_endpoints (ρ pre c : K) (q : Fin D → K) :
    (impliedRound ρ pre c q).eval 0 + (impliedRound ρ pre c q).eval 1 = c := by
  rw [eval_impliedRound, eval_impliedRound, eqLin_zero, eqLin_one]
  simp only [ne_eq, Nat.succ_ne_zero, not_false_eq_true, zero_pow, zero_sub, one_pow, neg_mul,
    Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- Each update is the implied polynomial at the round's challenge. -/
theorem claims_succ_eval (init : K) (ρ : Fin n → K) (q : Fin n → Fin D → K) (s : Fin n → K)
    (i : Fin n) :
    claims init ρ q s i.succ =
      (impliedRound (ρ i) (prefixEq ρ s i) (claims init ρ q s i.castSucc) (q i)).eval (s i) := by
  rw [claims_succ, step, eval_impliedRound, prefixEq_succ, smul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun d _ => by ring)

/-- The coefficient messages of the implied polynomials. -/
noncomputable def derived (init : K) (ρ : Fin n → K) (q : Fin n → Fin D → K) (s : Fin n → K) :
    Fin n → Fin (D + 1 + 1) → K :=
  fun i => Coefficient.coeffs (impliedRound (ρ i) (prefixEq ρ s i) (claims init ρ q s i.castSucc) (q i))

/-- The coefficient sumcheck's claims on the derived messages are the verifier's claims. -/
theorem claims_derived (init : K) (ρ : Fin n → K) (q : Fin n → Fin D → K) (s : Fin n → K)
    (j : Fin (n + 1)) :
    Coefficient.claims init (derived init ρ q s) s j = claims init ρ q s j := by
  refine Fin.cases rfl (fun i => ?_) j
  rw [Coefficient.claims_succ, derived, roundPoly_coeffs (impliedRound_natDegree_le _ _ _ _),
    claims_succ_eval]

/-- The verifier's final check is the coefficient sumcheck's acceptance of the derived
messages. -/
theorem accepts_derived {init : K} {ρ : Fin n → K} {q : Fin n → Fin D → K} {s : Fin n → K}
    {final : K} (h : claims init ρ q s (Fin.last n) = final) :
    Coefficient.Accepts init (derived init ρ q s) s final := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [claims_derived, endpointSum, derived, roundPoly_coeffs (impliedRound_natDegree_le _ _ _ _),
      impliedRound_endpoints]
  · rw [claims_derived, h]

/-- The derived message of round `i` reads the messages through `i` and the challenges before
`i` only. -/
theorem derived_congr (init : K) (ρ : Fin n → K) {q q' : Fin n → Fin D → K} {s s' : Fin n → K}
    (i : Fin n) (hq : ∀ l, l ≤ i → q l = q' l) (hs : ∀ l, l < i → s l = s' l) :
    derived init ρ q s i = derived init ρ q' s' i := by
  unfold derived
  rw [hq i le_rfl, prefixEq_congr ρ fun l hl => hs l hl,
    claims_congr init ρ i.castSucc (fun l hl => hq l (le_of_lt hl)) fun l hl => hs l hl]

/-- **Soundness.** If the last claim equals the summand at the challenge point, the initial claim
is the cube sum, or the challenge of some round is a root of that round's event: the derived
minus the true round polynomial, of degree `D + 1`. -/
theorem sound (p : MvPolynomial (Fin n) K) (hp : ∀ v, p.degreeOf v ≤ D + 1) {init : K}
    {ρ : Fin n → K} {q : Fin n → Fin D → K} {s : Fin n → K}
    (h : claims init ρ q s (Fin.last n) = MvPolynomial.eval s p) :
    init = trueClaim p s 0 ∨ ∃ i, (roundEvent p hp (derived init ρ q s) s i).BadAt (s i) :=
  Coefficient.sound p hp (accepts_derived h)

/-! ### Completeness -/

/-- The factor `q_i` has degree at most the summand's degree in variable `i`. -/
theorem quad_natDegree_le_degreeOf (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) (s : Fin n → K)
    (i : Fin n) : (EqFactored.quad ρ f s i).natDegree ≤ f.degreeOf i := by
  refine (round_degree _ _ _ _).trans ((MvPolynomial.degreeOf_mul_le i _ _).trans ?_)
  rw [EqFactored.degreeOf_eqAfter, zero_add]

/-- **The honest messages**: coefficients `1, …, D` of the factor `q_i`. -/
noncomputable def honest (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) (s : Fin n → K) :
    Fin n → Fin D → K :=
  fun i d => (EqFactored.quad ρ f s i).coeff (d.val + 1)

/-- Round `i`'s honest message reads the challenges before `i` only. -/
theorem honest_congr (ρ : Fin n → K) (f : MvPolynomial (Fin n) K) {s s' : Fin n → K} (i : Fin n)
    (hs : ∀ l, l < i → s l = s' l) : honest (D := D) ρ f s i = honest ρ f s' i := by
  funext d
  simp only [honest, EqFactored.quad_congr ρ f i hs]

/-- On the honest messages the claims are the true remaining sums. -/
theorem claims_honest (ρ : Fin n → K) {f : MvPolynomial (Fin n) K} (hf : ∀ v, f.degreeOf v ≤ D)
    (s : Fin n → K) (j : Fin (n + 1)) :
    claims (trueClaim (eqPoly ρ * f) s 0) ρ (honest (D := D) ρ f s) s j =
      trueClaim (eqPoly ρ * f) s j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hQ : ∀ x, (EqFactored.quad ρ f s i).eval x = (EqFactored.quad ρ f s i).coeff 0 +
        ∑ d : Fin D, (EqFactored.quad ρ f s i).coeff (d.val + 1) * x ^ (d.val + 1) := fun x => by
      rw [eval_eq_sum_range' (Nat.lt_succ_of_le ((quad_natDegree_le_degreeOf ρ f s i).trans (hf i))),
        Finset.sum_range_succ', Finset.sum_range, add_comm]
      simp
    rw [claims_succ, ih, ← trueRound_eval, ← trueRound_endpoints, EqFactored.trueRound_eq_mul, step,
      prefixEq_succ]
    simp only [eval_mul, eval_C, EqFactored.eval_eqLinPoly, hQ, eqLin_zero, eqLin_one, honest,
      smul_eq_mul, ne_eq, Nat.succ_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero, add_zero, one_pow, mul_one, sub_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    unfold eqLin
    ring_nf

/-- **Completeness.** On the true initial claim the honest messages pass the final check, for
every challenge vector. The hypothesis `hf` is the summand's degree bound, a parameter
condition. -/
theorem complete (ρ : Fin n → K) {f : MvPolynomial (Fin n) K} (hf : ∀ v, f.degreeOf v ≤ D)
    (s : Fin n → K) :
    claims (trueClaim (eqPoly ρ * f) s 0) ρ (honest (D := D) ρ f s) s (Fin.last n) =
      MvPolynomial.eval s (eqPoly ρ * f) := by
  rw [claims_honest ρ hf, trueClaim_last]

end GordieHowe.Sumcheck.EqFactoredDeg
