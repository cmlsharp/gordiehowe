-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MaskOracle
public import GordieHowe.Model.Quantum.Pure.QueryAlg
public import GordieHowe.Model.Quantum.O2H.FreshSecret
public import GordieHowe.Foundations.ToMathlib.SqrtAverage

@[expose] public section

/-!
# Hedged signing with a mask oracle in the quantum random-oracle model

The step of `GordieHowe/Applications/Ring/PublicW1/MaskOracle.lean` from the ideal-mask ring signer
to the hedged signer (FIPS 204 Algorithm 7: `ρ'' = H(K ‖ rnd ‖ µ)`, `y = ExpandMask(ρ'', κ)`, with
`H` and ExpandMask together a random oracle on `(rnd, point)`), for adversaries that query the
mask oracle in superposition. The other oracles are given whole, as in `PubAnonAdversary`; whole
access dominates quantum access to them.

- `Quantum.etv_born_le`, `QueryAlg.etv_outLaw_le_guess`: the measured outputs of a quantum
  algorithm with two oracles that agree outside a set `S` are within `2 t √P_guess` (AHU19
  Theorem 3, Lemma 8, pp. 11–12 and 26–27; `OracleAlg.norm_final_sub_le`), `P_guess` the
  probability that the query input before a uniformly chosen query lies in `S`.
  `QueryAlg.sum_mul_ofReal_guess_le`: for a set fixed by a secret drawn independently of the
  oracle, the bound averages to `2 t √ε`, `ε` bounding the probability that a point lies in the
  set (Jensen's inequality for the square root).
- `drawSteps`, `measChoice`, `acceptLaw`: the rounds of `seqRun` with a challenge drawn from a
  law (the measured output of a quantum algorithm `QueryAlg` with oracle access to the mask oracle,
  its answers encoded in a finite additive group `G`), and the distinguisher's measured output.
- `sum_uniform_hedged_closeQ`: the hedged rounds and the rounds with fresh masks, averaged over
  the mask oracle, are within `(Q k)² / |R| + (Q + 1) · 2 q √(Q k / |R|) + 2 Q ρ^k`. The proof
  is that of `sum_uniform_hedged_close`: draw the nonces of the first `k` attempts of every round
  up front and swap the slices of the mask oracle at those nonces with fresh masks; the union
  bound over the classical queries that hit a drawn nonce becomes one-way to hiding for each of
  the `Q` choices and the distinguisher, on the set of the mask points at the drawn nonces, in the
  rounds with the given masks and the unswapped oracle, which do not read the nonces
  (`etv_acceptLaw_swap_le`, `sum_uniform_swapErrQ_le`).
- `MaskedSigner.QAdversary`, `MaskedSigner.QDist`, `QAdversary.game`, `QAdversary.gameAt`: an
  anonymity adversary (BKM06 Definition 4) whose challenge in each round, and whose guess, is the
  measured output of a quantum algorithm with `q` queries to the mask oracle; its experiments
  against the hedged signer and against the ideal-mask signer at a fixed mask oracle.
- `MaskedSigner.advantage_le_advantageAt`: the advantage against the hedged signer is at most the
  average over the mask oracle of the advantage against the ideal-mask signer at that oracle,
  plus twice the hedged error `hedgeErrorQ`.
- `QAdversary.exists_advantageAt_le`, `QAdversary.exists_advantage_le` (one challenge, `Q = 1`):
  at a fixed mask oracle the ideal-mask signer does not read it, and the quantum adversary is the
  mixture over tables of measured challenges (`QAdversary.tableLaw`, a product law over the
  finitely many inputs of the one round) of classical adversaries (`QAdversary.atTable`), so some
  classical adversary with the same set of challenges does as well, against the distinguisher
  that guesses the likelier experiment (`PubAnonAdversary.likelierDist`; a bounded test is no
  better than the best event). The anonymity bounds for classical adversaries then apply.

**The adversary class.** In each round the adversary runs a quantum algorithm on classical
inputs (the users' coins, the whole oracle of the base scheme, the whole oracle of the compiled
argument and the history), with `q` superposition queries to the mask oracle, and the challenge
is its measured output; the guess is likewise. A general quantum algorithm with intermediate
measurements has a `QueryAlg` with the same query count and output law
(`Alg.outLaw_toQueryAlgCoh`). The adversary keeps no quantum state from one round to the next:
its state between rounds is the classical history. The reduction to classical adversaries is
proved for one challenge, the case of the ML-DSA headlines; for more rounds the history ranges
over an infinite type and the product law over tables is not a finite one. Deterministic signing
(a fixed nonce) is not covered: the bound charges the queries that find a fresh nonce.
-/

open scoped NNReal ENNReal BigOperators

/-! ### Measured outputs of quantum algorithms -/

namespace GordieHowe.Quantum

open Finset

section Born

variable {ι : Type*} [Fintype ι]

/-- The Born law of a unit vector gives a set the probability of measuring an outcome in it. -/
theorem born_toOuterMeasure (v : QState ι) (hv : ‖v‖ = 1) (S : Set ι) :
    (born v hv).toOuterMeasure S = ENNReal.ofReal (prob S v) := by
  classical
  have h1 : (born v hv).toOuterMeasure S = bornWeight v S := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype, bornWeight_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S
    · simp [Set.indicator_of_mem hi, born]
    · simp [Set.indicator_of_notMem hi]
  rw [h1, bornWeight_apply, prob, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- **Close unit vectors have close measurement laws**: the total-variation distance of the Born
laws of `v` and `w` is at most `‖v - w‖`. -/
theorem etv_born_le (v w : QState ι) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    PMF.etv (born v hv) (born w hw) ≤ ENNReal.ofReal ‖v - w‖ := by
  classical
  set p := born v hv
  set r := born w hw
  set S : Set ι := {i | r i ≤ p i}
  have hsum : PMF.etv p r + r.toOuterMeasure S = p.toOuterMeasure S := by
    unfold PMF.etv
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ S
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, tsub_add_cancel_of_le hi]
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, add_zero]
      exact tsub_eq_zero_of_le (le_of_lt (not_le.1 hi))
  have he : PMF.etv p r = p.toOuterMeasure S - r.toOuterMeasure S :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.toOuterMeasure_apply_le_one _ _)) hsum
  rw [he, born_toOuterMeasure, born_toOuterMeasure, ← ENNReal.ofReal_sub _ (prob_nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (abs_prob_sub_le S hv hw))

end Born

namespace QueryAlg

variable {X Y O : Type} [Fintype X] [Fintype Y] {t : ℕ} (A : QueryAlg X Y t O) [AddGroup Y]

/-- **Close final states give close outputs**: the measured outputs of `A` with the oracles `f`
and `g` are within the distance of the final states. -/
theorem etv_outLaw_le (f g : X → Y) :
    PMF.etv (A.outLaw f) (A.outLaw g) ≤ ENNReal.ofReal ‖A.final f - A.final g‖ :=
  (PMF.etv_map_le _ _ _).trans (etv_born_le (A.final f) (A.final g) _ _)

/-- Every output with nonzero probability is the output of some outcome of the work register. -/
theorem exists_out_of_outLaw_ne_zero (f : X → Y) {o : O} (h : A.outLaw f o ≠ 0) :
    ∃ w, A.out w = o := by
  obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 h)
  exact ⟨r.1, hr⟩

/-- **`A` with its output read by `g`** from the outcome of the work register: the same unitaries
and queries. -/
def withOut {O' : Type} (g : A.W → O') : QueryAlg X Y t O' where
  W := A.W
  init := A.init
  norm_init := A.norm_init
  step := A.step
  out := g

/-- An output read by `g` and then relabelled by `φ` is `A`'s output when `φ ∘ g = A.out`. -/
theorem outLaw_withOut_map {O' : Type} (g : A.W → O') (φ : O' → O) (h : ∀ w, φ (g w) = A.out w)
    (f : X → Y) : ((A.withOut g).outLaw f).map φ = A.outLaw f := by
  rw [outLaw, outLaw, PMF.map_comp]
  congr 1
  funext r
  exact h r.1

/-- **The guessing probability of a set `S`** with oracle `f` (AHU19 Theorem 3, p. 11): run `A`
with `f` until just before a uniformly chosen one of its `t` queries and measure the query input;
the probability that it lies in `S`. -/
noncomputable def guess (S : Set X) (f : X → Y) : ℝ :=
  (A.toOracleAlg ∅).guessProb (queried S) (queryPerm f) ()

theorem guess_nonneg (S : Set X) (f : X → Y) : 0 ≤ A.guess S f :=
  OracleAlg.guessProb_nonneg (A.toOracleAlg ∅) _ _ _

/-- **One-way to hiding for the measured output** (AHU19 Theorem 3, pp. 11–12, through Lemma 8):
if the oracles `f` and `g` agree outside `S`, the measured outputs of `A` with `f` and with `g`
are within `2 t √(guess S f)`. -/
theorem etv_outLaw_le_guess {S : Set X} {f g : X → Y} (h : ∀ x ∉ S, f x = g x) :
    PMF.etv (A.outLaw f) (A.outLaw g) ≤ ENNReal.ofReal (2 * t * √(A.guess S f)) :=
  (A.etv_outLaw_le f g).trans (ENNReal.ofReal_le_ofReal
    ((A.toOracleAlg ∅).norm_final_sub_le (queryPerm_eq_of_notMem_queried h) ()))

/-- **The guessing probability of a fresh secret set**: if every query input lies in the random
set `T σ`, `σ ← ν`, with probability at most `ε`, and the oracle `f` does not depend on `σ`, the
guessing probability of `T σ` averages to at most `ε`. -/
theorem sum_mul_guess_le {R : Type*} [Fintype R] (ν : PMF R) (T : R → Set X) (f : X → Y) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    ∑ σ, (ν σ).toReal * A.guess (T σ) f ≤ ε := by
  unfold guess OracleAlg.guessProb
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  have hc : 𝔼 _i : Fin t, ε ≤ ε := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [hε0]
    · have : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
      rw [Finset.expect_const univ_nonempty]
  refine (Finset.expect_le_expect (g := fun _ => ε) fun i _ => ?_).trans hc
  refine sum_mul_prob_queried_le ν T ((A.toOracleAlg ∅).norm_pre _ () i) fun tv => ?_
  refine le_trans (ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ fun σ hσ => ?_)) (hε (tv 0))
  obtain ⟨j, hj⟩ := hσ.1
  show tv 0 ∈ T σ
  rwa [Subsingleton.elim j 0] at hj

/-- **One-way to hiding for a fresh secret set, averaged**: under the hypothesis of
`sum_mul_guess_le`, the bound `2 t √(guess (T σ) f)` averages to at most `2 t √ε` (Jensen's
inequality for the square root). -/
theorem sum_mul_ofReal_guess_le {R : Type*} [Fintype R] (ν : PMF R) (T : R → Set X) (f : X → Y)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    ∑ σ, ν σ * ENNReal.ofReal (2 * t * √(A.guess (T σ) f)) ≤ ENNReal.ofReal (2 * t * √ε) := by
  have hw : ∀ σ, ν σ = ENNReal.ofReal (ν σ).toReal := fun σ =>
    (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
  have hL : ∑ σ, ν σ * ENNReal.ofReal (2 * t * √(A.guess (T σ) f)) =
      ENNReal.ofReal (∑ σ, (ν σ).toReal * (2 * t * √(A.guess (T σ) f))) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun σ _ => by positivity]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← hw]
  rw [hL]
  refine ENNReal.ofReal_le_ofReal ?_
  have hJ := Real.sum_mul_sqrt_le_sqrt_sum_mul (w := fun σ => (ν σ).toReal)
    (g := fun σ => A.guess (T σ) f) (fun _ => ENNReal.toReal_nonneg) (PMF.sum_toReal ν)
    fun σ => A.guess_nonneg _ _
  calc ∑ σ, (ν σ).toReal * (2 * t * √(A.guess (T σ) f))
      = 2 * t * ∑ σ, (ν σ).toReal * √(A.guess (T σ) f) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ ≤ 2 * t * √(∑ σ, (ν σ).toReal * A.guess (T σ) f) := by gcongr
    _ ≤ 2 * t * √ε := by gcongr; exact A.sum_mul_guess_le ν T f hε0 hε

end QueryAlg

end GordieHowe.Quantum

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM PMF
open GordieHowe.Quantum (QueryAlg)

/-! ### Rounds with measured choices -/

section CompareQ

variable {Ω Pub Pf Ch α Rnd Pt Mask G : Type} [Fintype Ω] [Nonempty Ω] [Fintype α] [DecidableEq α]
  [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Pt] [DecidableEq Pt]
  [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] [Fintype G] [AddGroup G] {Q : ℕ}
  (att : Ch → (Pt → Mask) → PMF (Option α)) (dflt : α)
  (rnd : (j : Fin Q) → Ω × PubHist Pub Pf j → Ch → α → PMF (Option (Pub × Pf)))
  (adm : Ch → Prop) [DecidablePred adm]

/-- **The step laws of choice laws and signature laws**: round `j` draws its challenge from
`cl j s`, signs it with the law `sig j c`, and outputs `rnd j s c x` of the signature `x`. -/
noncomputable def drawSteps (cl : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch)
    (sig : (j : Fin Q) → Ch → PMF α) : StepLaws Ω Pub Pf Q :=
  fun j s => (cl j s).bind fun c => (sig j c).bind (rnd j s c)

/-- **The rejection of the given masks of round `j`, averaged over the challenge**: the
probability that the challenge drawn from `cl j s` is admitted and its `k` attempts with the masks
`Z j` all reject. -/
noncomputable def failMassQ {k : ℕ} (cl : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch)
    (Z : Fin Q → Fin k → Pt → Mask) (j : Fin Q) (s : Ω × PubHist Pub Pf j) : ℝ≥0∞ :=
  ∑' c, cl j s c * if adm c then ∏ t, att c (Z j t) none else 0

omit [Fintype Ω] [Nonempty Ω] [DecidableEq α] [Fintype Pt] [DecidableEq Pt]
  [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] in
/-- **One round with the slices at the drawn nonces swapped, against one round with the given
masks**: the two choice laws, then the continuation after `k` rejected attempts. -/
theorem etv_drawStep_swap_le (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt) {k : ℕ}
    (cl cl' : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch) {ρ : Fin Q → Fin k → Rnd}
    (hρ : NoncesDistinct ρ) (Y : Rnd × Pt → Mask) (Z : Fin Q → Fin k → Pt → Mask) (j : Fin Q)
    (s : Ω × PubHist Pub Pf j) :
    PMF.etv (drawSteps rnd cl' (fun j c => sigNonces att dflt (swapY ρ Y Z) (ρ j) c) j s)
      (drawSteps rnd cl (fun j c => sigMasks att dflt Y (Z j) c) j s) ≤
      PMF.etv (cl' j s) (cl j s) + failMassQ att adm cl Z j s := by
  unfold drawSteps
  refine (PMF.etv_triangle _ ((cl j s).bind fun c =>
    (sigNonces att dflt (swapY ρ Y Z) (ρ j) c).bind (rnd j s c)) _).trans
      (add_le_add (PMF.etv_bind_right_le _ _ _) ?_)
  refine (PMF.etv_bind_left_le _ _ _).trans (ENNReal.tsum_le_tsum fun c => ?_)
  gcongr
  have hsig : sigNonces att dflt (swapY ρ Y Z) (ρ j) c =
      finish dflt (PMF.firstOf fun t => att c (Z j t)) (untilSome (realAtt att (swapY ρ Y Z) c)) := by
    unfold sigNonces
    simp only [maskSlice_swapY hρ]
  rw [hsig]
  by_cases ha : adm c
  · rw [if_pos ha, ← PMF.firstOf_apply_none]
    exact (PMF.etv_bind_right_le _ _ _).trans (etv_finish_le dflt _ _ _)
  · rw [if_neg ha]
    have hconst : ∀ X : PMF α, X.bind (rnd j s c) = rnd j s c dflt := fun X => by
      rw [show rnd j s c = fun _ => rnd j s c dflt from funext (hrnd j s c ha), PMF.bind_const]
    rw [hconst, hconst, PMF.etv_self]

omit [DecidableEq Pt] [DecidableEq Mask] [DecidablePred adm] in
/-- **The hedged rounds with the nonces of the first `k` attempts drawn up front.** -/
theorem seqRun_drawSteps_sigReal_eq (cl : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch) {k : ℕ}
    (Y : Rnd × Pt → Mask) (j : ℕ) (hj : j ≤ Q) :
    seqRun (drawSteps rnd cl (sigReal att dflt Y)) j hj =
      (PMF.uniformOfFintype (Fin Q → Fin k → Rnd)).bind fun ρ =>
        seqRun (drawSteps rnd cl fun j c => sigNonces att dflt Y (ρ j) c) j hj := by
  have h := bind_pi_seqRun (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Rnd))
    (fun i rv s => (cl i s).bind fun c => (sigNonces att dflt Y rv c).bind (rnd i s c)) j hj
  rw [PMF.pi_uniformOfFintype] at h
  refine Eq.trans ?_ h.symm
  refine seqRun_congr j hj fun i _ => funext fun s => ?_
  unfold drawSteps
  rw [PMF.bind_comm]
  congr 1
  funext c
  rw [← PMF.bind_bind, uniform_bind_sigNonces]
  rfl

omit [DecidableEq Rnd] [DecidablePred adm] in
/-- **The rounds with the masks of the first `k` attempts drawn up front.** -/
theorem seqRun_drawSteps_sigFresh_eq (cl : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch) {k : ℕ}
    (Y : Rnd × Pt → Mask) (j : ℕ) (hj : j ≤ Q) :
    seqRun (drawSteps rnd cl fun _ c => sigFresh att dflt k Y c) j hj =
      (PMF.uniformOfFintype (Fin Q → Fin k → Pt → Mask)).bind fun Z =>
        seqRun (drawSteps rnd cl fun j c => sigMasks att dflt Y (Z j) c) j hj := by
  have h := bind_pi_seqRun (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Pt → Mask))
    (fun i zv s => (cl i s).bind fun c => (sigMasks att dflt Y zv c).bind (rnd i s c)) j hj
  rw [PMF.pi_uniformOfFintype] at h
  refine Eq.trans ?_ h.symm
  refine seqRun_congr j hj fun i _ => funext fun s => ?_
  unfold drawSteps
  rw [PMF.bind_comm]
  congr 1
  funext c
  rw [← PMF.bind_bind, uniform_bind_sigMasks]

omit [DecidableEq Rnd] in
/-- **The rounds with `k` fresh-mask attempts against the rounds with fresh masks**: within
`Q ρ^k`, when every admitted challenge drawn has a fresh-mask attempt rejecting with probability
at most `ρ`. -/
theorem etv_seqRun_drawSteps_sigFresh_le (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt)
    (cl : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch) {k : ℕ} {ρb : ℝ≥0∞} (Y : Rnd × Pt → Mask)
    (hρ : ∀ j s c, cl j s c ≠ 0 → adm c → meanAtt att c none ≤ ρb) :
    PMF.etv (seqRun (drawSteps rnd cl fun _ c => sigFresh att dflt k Y c) Q le_rfl)
      (seqRun (drawSteps rnd cl (sigIdeal att dflt)) Q le_rfl) ≤ Q * ρb ^ k := by
  refine (etv_seqRun_le _ _ Q le_rfl).trans ?_
  have hstep : ∀ (i : Fin Q) s, PMF.etv (drawSteps rnd cl (fun _ c => sigFresh att dflt k Y c) i s)
      (drawSteps rnd cl (sigIdeal att dflt) i s) ≤ ρb ^ k := fun i s => by
    unfold drawSteps
    refine (PMF.etv_bind_left_le _ _ _).trans ?_
    calc ∑' c, cl i s c * PMF.etv ((sigFresh att dflt k Y c).bind (rnd i s c))
          ((sigIdeal att dflt i c).bind (rnd i s c))
        ≤ ∑' c, cl i s c * ρb ^ k := ENNReal.tsum_le_tsum fun c => by
          by_cases hc : cl i s c = 0
          · rw [hc, zero_mul, zero_mul]
          by_cases ha : adm c
          · gcongr
            refine (PMF.etv_bind_right_le _ _ _).trans ((etv_sigFresh_le att dflt k Y c).trans ?_)
            exact pow_le_pow_left₀ zero_le (hρ i s c hc ha) k
          · have hconst : ∀ X : PMF α, X.bind (rnd i s c) = rnd i s c dflt := fun X => by
              rw [show rnd i s c = fun _ => rnd i s c dflt from funext (hrnd i s c ha),
                PMF.bind_const]
            rw [hconst, hconst, PMF.etv_self, mul_zero]
            exact zero_le
      _ = ρb ^ k := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc ∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd cl (sigIdeal att dflt)) i (by omega) s *
        PMF.etv (drawSteps rnd cl (fun _ c => sigFresh att dflt k Y c) (Fin.castLE le_rfl i) s)
          (drawSteps rnd cl (sigIdeal att dflt) (Fin.castLE le_rfl i) s)
      ≤ ∑ _i : Fin Q, ρb ^ k := Finset.sum_le_sum fun i _ => by
        calc _ ≤ ∑' s, seqRun (drawSteps rnd cl (sigIdeal att dflt)) i (by omega) s * ρb ^ k :=
              ENNReal.tsum_le_tsum fun s => by gcongr; exact hstep _ s
          _ = ρb ^ k := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = Q * ρb ^ k := by simp

variable (enc : Mask → G) {q : ℕ}
  (algC : (j : Fin Q) → Ω × PubHist Pub Pf j → QueryAlg (Rnd × Pt) G q Ch)
  (algE : Ω × PubHist Pub Pf Q → QueryAlg (Rnd × Pt) G q Bool)

/-- **The measured choices at the mask oracle `Y`**: round `j`'s challenge is the measured
output of the quantum algorithm `algC j s` with oracle access to `Y`, its answers encoded by
`enc`. -/
noncomputable def measChoice (Y : Rnd × Pt → Mask) : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch :=
  fun j s => (algC j s).outLaw (enc ∘ Y)

/-- **The distinguisher's output** after the rounds with step laws `steps`, at the mask oracle
`Y`: the measured output of the quantum algorithm `algE s` with oracle access to `Y`. -/
noncomputable def acceptLaw (Y : Rnd × Pt → Mask) (steps : StepLaws Ω Pub Pf Q) : PMF Bool :=
  (seqRun steps Q le_rfl).bind fun s => (algE s).outLaw (enc ∘ Y)

/-- **The mask points at the drawn nonces**: the set on which the mask oracle and the oracle with
the slices at the drawn nonces swapped can differ. -/
def hitSet {k : ℕ} (ρ : Fin Q → Fin k → Rnd) : Set (Rnd × Pt) := {x | NonceHit ρ x.1}

/-- **The error of the swap** at the masks `Z` in the quantum random-oracle model: the one-way
to hiding bounds of the `Q` choices and the distinguisher (AHU19 Theorem 3, `2 q √P_guess` for the
set of the drawn nonces, in the rounds with the masks `Z` and the oracle `Y`), and the rejection
of the `k` attempts with the masks `Z`. -/
noncomputable def swapErrQ {k : ℕ} (ρ : Fin Q → Fin k → Rnd) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) : ℝ≥0∞ :=
  (∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
      sigMasks att dflt Y (Z j) c) i (by omega) s *
      (ENNReal.ofReal (2 * q * √((algC i s).guess (hitSet ρ) (enc ∘ Y))) +
        failMassQ att adm (measChoice enc algC Y) Z i s)) +
    ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
      sigMasks att dflt Y (Z j) c) Q le_rfl s *
      ENNReal.ofReal (2 * q * √((algE s).guess (hitSet ρ) (enc ∘ Y)))

omit [Fintype Ω] [Nonempty Ω] [DecidableEq α] [Fintype Rnd] [Nonempty Rnd] [Fintype Pt]
  [DecidableEq Pt] [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] [Fintype G] [AddGroup G]
  [DecidablePred adm] in
/-- The oracle with the slices at the drawn nonces swapped agrees with the mask oracle outside
the mask points at the drawn nonces. -/
theorem enc_swapY_of_notMem {k : ℕ} {ρ : Fin Q → Fin k → Rnd} (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) : ∀ x ∉ hitSet ρ, (enc ∘ Y) x = (enc ∘ swapY ρ Y Z) x :=
  fun _ hx => by simp only [Function.comp, swapY_of_not hx]

omit [DecidableEq α] [DecidableEq Pt] [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] in
/-- **The hedged rounds at the swapped oracle against the rounds with the masks `Z`**, for
distinct nonces, quantum choices and a quantum distinguisher: the distinguisher's outputs are
within the swap error. -/
theorem etv_acceptLaw_swap_le (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt)
    {k : ℕ} {ρ : Fin Q → Fin k → Rnd} (hρ : NoncesDistinct ρ) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) :
    PMF.etv (acceptLaw enc algE (swapY ρ Y Z) (drawSteps rnd (measChoice enc algC (swapY ρ Y Z))
        fun j c => sigNonces att dflt (swapY ρ Y Z) (ρ j) c))
      (acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) fun j c =>
        sigMasks att dflt Y (Z j) c)) ≤ swapErrQ att dflt rnd adm enc algC algE ρ Y Z := by
  set p := seqRun (drawSteps rnd (measChoice enc algC (swapY ρ Y Z))
    fun j c => sigNonces att dflt (swapY ρ Y Z) (ρ j) c) Q le_rfl
  set r := seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
    sigMasks att dflt Y (Z j) c) Q le_rfl
  have hS : PMF.etv p r ≤ ∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y)
      fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
        (ENNReal.ofReal (2 * q * √((algC i s).guess (hitSet ρ) (enc ∘ Y))) +
          failMassQ att adm (measChoice enc algC Y) Z i s) := by
    refine (etv_seqRun_le _ _ Q le_rfl).trans (Finset.sum_le_sum fun i _ =>
      ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _)
    refine (etv_drawStep_swap_le att dflt rnd adm hrnd _ _ hρ Y Z _ s).trans (add_le_add ?_ le_rfl)
    rw [PMF.etv_comm]
    exact (algC _ s).etv_outLaw_le_guess (enc_swapY_of_notMem enc Y Z)
  unfold acceptLaw swapErrQ
  refine (PMF.etv_triangle _ (r.bind fun s => (algE s).outLaw (enc ∘ swapY ρ Y Z)) _).trans
    (add_le_add ((PMF.etv_bind_right_le _ _ _).trans hS) ?_)
  refine (PMF.etv_bind_left_le _ _ _).trans (ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _)
  rw [PMF.etv_comm]
  exact (algE s).etv_outLaw_le_guess (enc_swapY_of_notMem enc Y Z)

omit [DecidableEq Pt] in
/-- **One mask point lies at a drawn nonce** with probability at most `Q k / |R|`. -/
theorem toReal_uniform_hitSet_le {k : ℕ} (x : Rnd × Pt) :
    ((PMF.uniformOfFintype (Fin Q → Fin k → Rnd)).toOuterMeasure {ρ | x ∈ hitSet ρ}).toReal ≤
      Q * k / Fintype.card Rnd := by
  classical
  have h := sum_uniform_nonceHit_le (Q := Q) (k := k) [x]
  have he : (PMF.uniformOfFintype (Fin Q → Fin k → Rnd)).toOuterMeasure {ρ | x ∈ hitSet ρ} =
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if ∃ y ∈ [x], NonceHit ρ y.1 then 1 else 0) := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hh : NonceHit ρ x.1
    · have hm : ρ ∈ {ρ : Fin Q → Fin k → Rnd | x ∈ hitSet ρ} := hh
      rw [Set.indicator_of_mem hm, if_pos ⟨x, List.mem_singleton_self x, hh⟩, mul_one]
    · have hm : ρ ∉ {ρ : Fin Q → Fin k → Rnd | x ∈ hitSet ρ} := hh
      rw [Set.indicator_of_notMem hm, if_neg, mul_zero]
      rintro ⟨y, hy, hy'⟩
      rw [List.mem_singleton] at hy
      exact hh (hy ▸ hy')
  rw [he]
  refine (ENNReal.toReal_mono (by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)))
        (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero))) h).trans_eq ?_
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]

omit [DecidableEq α] [DecidableEq Pt] [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] in
include att algC algE in
open Classical in
/-- **The quantum swap error averaged over the nonces**: the `Q + 1` one-way to hiding bounds
average to at most `2 q √(Q k / |R|)` each (the drawn nonces are fresh: the rounds with the
masks `Z` and the oracle `Y` do not read them). -/
theorem sum_uniform_swapErrQ_le {k : ℕ} (Y : Rnd × Pt → Mask) (Z : Fin Q → Fin k → Pt → Mask) :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        swapErrQ att dflt rnd adm enc algC algE ρ Y Z ≤
      (∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
          sigMasks att dflt Y (Z j) c) i (by omega) s *
            failMassQ att adm (measChoice enc algC Y) Z i s) +
        (Q + 1) * ENNReal.ofReal (2 * q * √(Q * k / Fintype.card Rnd)) := by
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * q * √(Q * k / Fintype.card Rnd))
  have hε0 : (0 : ℝ) ≤ Q * k / Fintype.card Rnd := by positivity
  have hO : ∀ {O : Type} (A : QueryAlg (Rnd × Pt) G q O),
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ENNReal.ofReal (2 * q * √(A.guess (hitSet ρ) (enc ∘ Y))) ≤ B := fun A =>
    A.sum_mul_ofReal_guess_le _ _ _ hε0 fun x => toReal_uniform_hitSet_le x
  unfold swapErrQ
  have hR : ∀ i : Fin Q, ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
      ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
        sigMasks att dflt Y (Z j) c) i (by omega) s *
        (ENNReal.ofReal (2 * q * √((algC i s).guess (hitSet ρ) (enc ∘ Y))) +
          failMassQ att adm (measChoice enc algC Y) Z i s) ≤
      B + ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
        sigMasks att dflt Y (Z j) c) i (by omega) s *
          failMassQ att adm (measChoice enc algC Y) Z i s := fun i => by
    rw [sum_mul_tsum_mul_comm]
    calc ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
            sigMasks att dflt Y (Z j) c) i (by omega) s *
          ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
            (ENNReal.ofReal (2 * q * √((algC i s).guess (hitSet ρ) (enc ∘ Y))) +
              failMassQ att adm (measChoice enc algC Y) Z i s)
        ≤ ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
            sigMasks att dflt Y (Z j) c) i (by omega) s *
            (B + failMassQ att adm (measChoice enc algC Y) Z i s) := by
          refine ENNReal.tsum_le_tsum fun s => ?_
          gcongr
          simp_rw [mul_add, Finset.sum_add_distrib, sum_uniform_const]
          gcongr
          exact hO (algC i s)
      _ = _ := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hE : ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
      ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
        sigMasks att dflt Y (Z j) c) Q le_rfl s *
        ENNReal.ofReal (2 * q * √((algE s).guess (hitSet ρ) (enc ∘ Y))) ≤ B := by
    rw [sum_mul_tsum_mul_comm]
    calc _ ≤ ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
          sigMasks att dflt Y (Z j) c) Q le_rfl s * B :=
          ENNReal.tsum_le_tsum fun s => by gcongr; exact hO (algE s)
      _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc _ = (∑ i : Fin Q, ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
            sigMasks att dflt Y (Z j) c) i (by omega) s *
            (ENNReal.ofReal (2 * q * √((algC i s).guess (hitSet ρ) (enc ∘ Y))) +
              failMassQ att adm (measChoice enc algC Y) Z i s)) +
        ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
            sigMasks att dflt Y (Z j) c) Q le_rfl s *
            ENNReal.ofReal (2 * q * √((algE s).guess (hitSet ρ) (enc ∘ Y))) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [mul_add, Finset.mul_sum]
    _ ≤ (∑ i : Fin Q, (B + ∑' s, seqRun (drawSteps rnd (measChoice enc algC Y) fun j c =>
          sigMasks att dflt Y (Z j) c) i (by omega) s *
            failMassQ att adm (measChoice enc algC Y) Z i s)) + B :=
        add_le_add (Finset.sum_le_sum fun i _ => hR i) hE
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

omit [DecidableEq α] [DecidableEq Rnd] in
include att in
/-- **The rejection of the given masks, averaged over the masks**: at most `ρ^k` in every round,
when every admitted challenge drawn has a fresh-mask attempt rejecting with probability at most
`ρ`. -/
theorem sum_uniform_failMassQ_le (cl : (j : Fin Q) → Ω × PubHist Pub Pf j → PMF Ch) {k : ℕ}
    {ρb : ℝ≥0∞} (Y : Rnd × Pt → Mask)
    (hρ : ∀ j s c, cl j s c ≠ 0 → adm c → meanAtt att c none ≤ ρb) (i : Fin Q) :
    ∑ Z : Fin Q → Fin k → Pt → Mask, PMF.uniformOfFintype _ Z *
        ∑' s, seqRun (drawSteps rnd cl fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
          failMassQ att adm cl Z i s ≤ ρb ^ k := by
  rw [show PMF.uniformOfFintype (Fin Q → Fin k → Pt → Mask) =
    PMF.pi (fun _ => PMF.uniformOfFintype (Fin k → Pt → Mask)) from PMF.pi_uniformOfFintype.symm]
  have h := sum_pi_seqRun_mul (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Pt → Mask))
    (fun i zv s => (cl i s).bind fun c => (sigMasks att dflt Y zv c).bind (rnd i s c)) i
    (fun zv s => ∑' c, cl i s c * if adm c then ∏ t, att c (zv t) none else 0)
  calc _ = _ := h
    _ ≤ ∑' s, seqRun (fun i s => (PMF.uniformOfFintype (Fin k → Pt → Mask)).bind fun r =>
          (cl i s).bind fun c => (sigMasks att dflt Y r c).bind (rnd i s c)) i i.2.le s *
            ρb ^ k := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        gcongr
        rw [sum_mul_tsum_mul_comm]
        calc ∑' c, cl i s c * ∑ r : Fin k → Pt → Mask, PMF.uniformOfFintype _ r *
              (if adm c then ∏ t, att c (r t) none else 0)
            ≤ ∑' c, cl i s c * ρb ^ k := ENNReal.tsum_le_tsum fun c => by
              by_cases hc : cl i s c = 0
              · rw [hc, zero_mul, zero_mul]
              gcongr
              by_cases ha : adm c
              · simp only [ha, if_true]
                rw [sum_uniform_prod_pow k fun z => att c z none]
                refine pow_le_pow_left₀ zero_le ?_ k
                refine le_trans (le_of_eq ?_) (hρ i s c hc ha)
                rw [meanAtt, PMF.bind_apply, tsum_fintype]
              · simp [ha]
          _ = ρb ^ k := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = ρb ^ k := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [DecidableEq α] [DecidableEq Pt] [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] in
/-- The distinguisher's output probabilities are within the distance of its output laws. -/
theorem eclose_apply_of_etv_le {p r : PMF Bool} {e : ℝ≥0∞} (h : PMF.etv p r ≤ e) :
    EClose (p true) (r true) e := by
  have h1 := PMF.toOuterMeasure_le_add_etv p r {true}
  have h2 := PMF.toOuterMeasure_le_add_etv r p {true}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at h1 h2
  rw [PMF.etv_comm] at h2
  exact ⟨h1.trans (add_le_add le_rfl h), h2.trans (add_le_add le_rfl h)⟩

include att algC algE in
open Classical in
/-- **The hedged signer against the signer with fresh masks in the quantum random-oracle
model**, averaged over a uniform mask oracle: for choices and a distinguisher that are quantum
algorithms with `q` queries each to the mask oracle (`algC`, `algE`; the answers encoded by
`enc`), and every admitted challenge they can output having a fresh-mask attempt rejecting with
probability at most `ρ` (`hρ`), the distinguisher's output probabilities are within
`(Q k)² / |R| + (Q + 1) · 2 q √(Q k / |R|) + 2 Q ρ^k`, for every number `k` of attempts. The proof
is that of `sum_uniform_hedged_close` with the union bound over the queries replaced by one-way to
hiding (AHU19 Theorem 3, `etv_acceptLaw_swap_le`), averaged over the fresh nonces
(`sum_uniform_swapErrQ_le`). -/
theorem sum_uniform_hedged_closeQ
    (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt) {k : ℕ} {ρb : ℝ≥0∞}
    (hρ : ∀ Y j s c, measChoice enc algC Y j s c ≠ 0 → adm c → meanAtt att c none ≤ ρb) :
    EClose (∑ Y, PMF.uniformOfFintype _ Y *
        acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) (sigReal att dflt Y)) true)
      (∑ Y, PMF.uniformOfFintype _ Y *
        acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) (sigIdeal att dflt)) true)
      ((Q * k) ^ 2 * (Fintype.card Rnd : ℝ≥0∞)⁻¹ +
        (Q + 1) * ENNReal.ofReal (2 * q * √(Q * k / Fintype.card Rnd)) + 2 * Q * ρb ^ k) := by
  set P1 : (Rnd × Pt → Mask) → (Fin Q → Fin k → Rnd) → ℝ≥0∞ := fun Y ρ =>
    acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) fun j c =>
      sigNonces att dflt Y (ρ j) c) true
  set P3 : (Rnd × Pt → Mask) → (Fin Q → Fin k → Pt → Mask) → ℝ≥0∞ := fun Y Z =>
    acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) fun j c =>
      sigMasks att dflt Y (Z j) c) true
  set PF : (Rnd × Pt → Mask) → ℝ≥0∞ := fun Y =>
    acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) fun _ c =>
      sigFresh att dflt k Y c) true
  have hle1 : ∀ (p : PMF Bool), p true ≤ 1 := fun p => PMF.coe_le_one p true
  have hsum1 : ∀ {A : Type} [Fintype A] [Nonempty A] (g : A → ℝ≥0∞), (∀ a, g a ≤ 1) →
      ∑ a, PMF.uniformOfFintype A a * g a ≤ 1 := fun g hg =>
    (Finset.sum_le_sum fun a _ => mul_le_of_le_one_right' (hg a)).trans_eq (PMF.sum_coe _)
  -- the hedged rounds, with the nonces drawn up front
  have hA : ∑ Y, PMF.uniformOfFintype _ Y *
      acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) (sigReal att dflt Y)) true =
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ∑ Y, PMF.uniformOfFintype _ Y * P1 Y ρ := by
    simp only [acceptLaw, seqRun_drawSteps_sigReal_eq att dflt rnd _ (k := k), PMF.bind_bind,
      PMF.bind_apply, tsum_fintype, Finset.mul_sum, P1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun Y _ => by ring
  -- the rounds with the masks drawn up front
  have hC1 : ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
      ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
        P3 YZ.1 YZ.2 = ∑ Y, PMF.uniformOfFintype _ Y * PF Y := by
    rw [sum_uniform_const, sum_uniform_prod]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [PF, P3, acceptLaw]
    rw [seqRun_drawSteps_sigFresh_eq att dflt rnd _ Y Q le_rfl, PMF.bind_bind, PMF.bind_apply,
      tsum_fintype]
  -- the swap
  have hB : EClose (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ∑ Y, PMF.uniformOfFintype _ Y * P1 Y ρ)
      (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
          P3 YZ.1 YZ.2)
      (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if NoncesDistinct ρ then
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            swapErrQ att dflt rnd adm enc algC algE ρ YZ.1 YZ.2 else 1)) := by
    refine EClose.wsum _ _ fun ρ => ?_
    by_cases hd : NoncesDistinct ρ
    · rw [if_pos hd]
      have hsw : ∑ Y, PMF.uniformOfFintype _ Y * P1 Y ρ =
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            P1 (swapY ρ YZ.1 YZ.2) ρ := by
        rw [sum_uniform_swapY hd fun Y => P1 Y ρ, sum_uniform_prod]
        simp only [sum_uniform_const]
      rw [hsw]
      exact EClose.wsum _ _ fun YZ => eclose_apply_of_etv_le
        (etv_acceptLaw_swap_le att dflt rnd adm enc algC algE hrnd hd YZ.1 YZ.2)
    · rw [if_neg hd]
      exact EClose.of_le_one (hsum1 _ fun Y => hle1 _) (hsum1 _ fun YZ => hle1 _)
  -- the rounds with `k` fresh-mask attempts against the rounds with fresh masks
  have hD : EClose (∑ Y, PMF.uniformOfFintype _ Y * PF Y)
      (∑ Y, PMF.uniformOfFintype _ Y *
        acceptLaw enc algE Y (drawSteps rnd (measChoice enc algC Y) (sigIdeal att dflt)) true)
      (∑ Y : Rnd × Pt → Mask, PMF.uniformOfFintype _ Y * (Q * ρb ^ k)) := by
    refine EClose.wsum _ _ fun Y => eclose_apply_of_etv_le ?_
    exact (PMF.etv_bind_right_le _ _ _).trans
      (etv_seqRun_drawSteps_sigFresh_le att dflt rnd adm hrnd _ Y (hρ Y))
  rw [sum_uniform_const] at hD
  rw [hA]
  rw [← hC1] at hD
  refine (hB.trans hD).mono ?_
  -- the error
  have hfail : ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
      (∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd (measChoice enc algC YZ.1) fun j c =>
        sigMasks att dflt YZ.1 (YZ.2 j) c) i (by omega) s *
          failMassQ att adm (measChoice enc algC YZ.1) YZ.2 i s) ≤ Q * ρb ^ k := by
    rw [sum_uniform_prod]
    calc _ ≤ ∑ Y : Rnd × Pt → Mask, PMF.uniformOfFintype _ Y * (Q * ρb ^ k) := by
          refine Finset.sum_le_sum fun Y _ => ?_
          gcongr
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          calc _ ≤ ∑ _i : Fin Q, ρb ^ k := Finset.sum_le_sum fun i _ =>
                sum_uniform_failMassQ_le att dflt rnd adm _ Y (hρ Y) i
            _ = Q * ρb ^ k := by simp
      _ = Q * ρb ^ k := sum_uniform_const _
  have hcoll := sum_uniform_not_distinct_le (Q := Q) (k := k) (Rnd := Rnd)
  have hsw : ∀ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask),
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        swapErrQ att dflt rnd adm enc algC algE ρ YZ.1 YZ.2 ≤
      (∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd (measChoice enc algC YZ.1) fun j c =>
        sigMasks att dflt YZ.1 (YZ.2 j) c) i (by omega) s *
          failMassQ att adm (measChoice enc algC YZ.1) YZ.2 i s) +
        (Q + 1) * ENNReal.ofReal (2 * q * √(Q * k / Fintype.card Rnd)) := fun YZ =>
    sum_uniform_swapErrQ_le att dflt rnd adm enc algC algE YZ.1 YZ.2
  calc (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if NoncesDistinct ρ then
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            swapErrQ att dflt rnd adm enc algC algE ρ YZ.1 YZ.2 else 1)) + Q * ρb ^ k
      ≤ (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          ((if NoncesDistinct ρ then 0 else 1) +
            ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
              swapErrQ att dflt rnd adm enc algC algE ρ YZ.1 YZ.2)) + Q * ρb ^ k := by
        gcongr with ρ
        split_ifs
        · rw [zero_add]
        · exact le_self_add
    _ = (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * (if NoncesDistinct ρ then 0 else 1)) +
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
              swapErrQ att dflt rnd adm enc algC algE ρ YZ.1 YZ.2 + Q * ρb ^ k := by
        congr 1
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun YZ _ => Finset.sum_congr rfl fun ρ _ => by ring
    _ ≤ (Q * k) ^ 2 * (Fintype.card Rnd : ℝ≥0∞)⁻¹ +
          (Q * ρb ^ k + (Q + 1) * ENNReal.ofReal (2 * q * √(Q * k / Fintype.card Rnd))) +
            Q * ρb ^ k := by
        gcongr
        calc _ ≤ ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
              ((∑ i : Fin Q, ∑' s, seqRun (drawSteps rnd (measChoice enc algC YZ.1) fun j c =>
                sigMasks att dflt YZ.1 (YZ.2 j) c) i (by omega) s *
                  failMassQ att adm (measChoice enc algC YZ.1) YZ.2 i s) +
                (Q + 1) * ENNReal.ofReal (2 * q * √(Q * k / Fintype.card Rnd))) :=
              Finset.sum_le_sum fun YZ _ => by gcongr; exact hsw YZ
          _ ≤ _ := by
              simp_rw [mul_add, Finset.sum_add_distrib, sum_uniform_const]
              gcongr
    _ = _ := by ring

end CompareQ

/-! ### Quantum adversaries against the hedged signer -/

section HedgedGameQ

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg} (W : MaskedSigner S)
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P S.Stmt k kN kS L e) {n Q : ℕ}
  (G : Type) [Fintype G] [AddGroup G]

namespace MaskedSigner

/-- **An anonymity adversary with quantum access to the mask oracle** (BKM06 Definition 4,
ePrint 2005/304, p. 6, with the keys given at the start as in CCLM22 Experiment 2, p. 21, in the
quantum random-oracle model for the mask derivation): as `PubAnonAdversary`, but the challenge of
round `j` is the measured output of a quantum algorithm with `q` queries to the mask oracle
(`QueryAlg`, CMS19 section 3.2, p. 14, in the model of AHU19 pp. 8–9: unitaries alternating with
`q` superposition queries, then a computational-basis measurement), chosen as a function of the
honest users' key-generation coins, the whole oracle `H` of the base scheme, the whole oracle of
the compiled argument and the public values and ring signatures of the earlier rounds. The mask
oracle's answers are encoded in the finite additive group `G` (the oracle unitary
`|x, y⟩ ↦ |x, y + g(x)⟩` of `queryPerm`, with `g` the mask oracle followed by the encoding). Every
outcome of the measurement is a challenge of the set whose positions hold the two users' public
keys. A general quantum algorithm with intermediate measurements and mixed states has a
`QueryAlg` with the same query count and output law (`Alg.outLaw_toQueryAlgCoh`); the adversary
keeps classical state between rounds (the history and its inputs), and its quantum state of one
round is measured at the end of the round. -/
structure QAdversary (n Q q : ℕ) : Type 1 where
  /-- The finite set of challenges the adversary may choose. -/
  choices : Finset (S.Choice n)
  /-- The quantum algorithm whose measured output is the challenge of round `j`. -/
  choose : (j : Fin Q) → (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
    PubHist S.Pub M.NIProof j → QueryAlg (W.Rnd × W.Pt) G q (S.Choice n)
  /-- Every measured challenge is in the set. -/
  choose_mem : ∀ j keys H h hist w, (choose j keys H h hist).out w ∈ choices
  /-- The positions of every measured challenge hold the two users' public keys. -/
  choose_valid : ∀ j keys H h hist w, ((choose j keys H h hist).out w).Valid S keys

/-- **A distinguisher with quantum access to the mask oracle**: on the users' coins, the oracle
of the base scheme, the oracle of the compiled argument and the history, a quantum algorithm with
`q` queries to the mask oracle whose measured output is the guess. -/
abbrev QDist (n Q q : ℕ) : Type 1 :=
  (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) → PubHist S.Pub M.NIProof Q →
    QueryAlg (W.Rnd × W.Pt) G q Bool

variable {W M G} {q : ℕ} (A : W.QAdversary M G n Q q) (D : W.QDist M G n Q q)
  (enc : W.Mask → G) (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
  (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- **The rounds of the quantum game** at the users' coins `keys`, the oracle `H` of the base
scheme, the mask oracle `Y`, in the experiment `b`, with the signing law `sig c` for the challenge
`c`: the challenge measured, then refused when the signer refuses its ring at `H`, and otherwise
signed and proved for user `b`. -/
noncomputable def QAdversary.rounds (keys : Fin n → S.KeyCoins) (H : S.Orc) (Y : W.MaskOrc)
    (b : Bool) (sig : S.Choice n → PMF (S.Pub × S.Sig)) :
    StepLaws (Query k kN kS L → Out k e) S.Pub M.NIProof Q :=
  drawSteps (fun _ s c x => roundLaw (PubAnonAdversary.proofLawAt E Qs honest H) S.stmtPub s.1
      (S.proved H b c x)) (measChoice enc (fun j s => A.choose j keys H s.1 s.2) Y) fun _ c => sig c

/-- **The experiment `b` against the hedged signer in the quantum random-oracle model**: the
honest users' coins, the oracle `H` of the base scheme and the mask oracle `Y` uniform; the rounds
of `QAdversary.rounds` with the hedged signer, whose masks are read from `Y` at fresh nonces; the
distinguisher's measured output. -/
noncomputable def QAdversary.game (b : Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
    (PMF.uniformOfFintype S.Orc).bind fun H =>
      (PMF.uniformOfFintype W.MaskOrc).bind fun Y =>
        acceptLaw enc (fun s => D keys H s.1 s.2) Y (A.rounds enc E Qs honest keys H Y b fun c =>
          W.real.signLaw (H, Y) (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg)

/-- **The anonymity advantage in the quantum random-oracle model** against the hedged signer. -/
noncomputable def QAdversary.advantage : ℝ :=
  GordieHowe.gameAdvantage (A.game D enc E Qs honest false) (A.game D enc E Qs honest true) {true}

/-- **The experiment `b` against the ideal-mask signer at the fixed mask oracle `Y`**: as
`QAdversary.game`, with the ideal-mask signer, which does not read `Y`; the adversary and the
distinguisher still query `Y`. -/
noncomputable def QAdversary.gameAt (Y : W.MaskOrc) (b : Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
    (PMF.uniformOfFintype S.Orc).bind fun H =>
      acceptLaw enc (fun s => D keys H s.1 s.2) Y
        (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b)

/-- **The advantage against the ideal-mask signer at the fixed mask oracle `Y`.** -/
noncomputable def QAdversary.advantageAt (Y : W.MaskOrc) : ℝ :=
  GordieHowe.gameAdvantage (A.gameAt D enc E Qs honest Y false) (A.gameAt D enc E Qs honest Y true)
    {true}

variable (W) in
/-- **The error of the hedged signer in the quantum random-oracle model**: the nonces of the
`Q k` first attempts collide, or one of the `Q + 1` quantum phases of `q` queries distinguishes
the mask oracle from the oracle with the slices at those nonces swapped (one-way to hiding,
`2 q √(Q k / |R|)` each), or `k` attempts all reject, each round of the two hybrids, with the
fresh-mask attempt rejecting with probability at most `ρ`. -/
noncomputable def hedgeErrorQ (Q q k : ℕ) (ρ : ℝ≥0∞) : ℝ≥0∞ :=
  (Q * k) ^ 2 * (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ +
    (Q + 1) * ENNReal.ofReal (2 * q * √(Q * k / Fintype.card W.Rnd)) + 2 * Q * ρ ^ k

omit [DecidableEq RMsg] in
/-- The hedged error in the quantum random-oracle model is finite for `ρ ≤ 1`. -/
theorem hedgeErrorQ_ne_top (W : MaskedSigner S) (Q q k : ℕ) {ρ : ℝ≥0∞} (hρ : ρ ≤ 1) :
    W.hedgeErrorQ Q q k ρ ≠ ⊤ := by
  unfold hedgeErrorQ
  have hc : (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hp : ρ ^ k ≠ ⊤ := ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hρ)
  have hn : ∀ m : ℕ, (m : ℝ≥0∞) ≠ ⊤ := fun m => ENNReal.natCast_ne_top m
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top (hn _) (hn _))) hc, ENNReal.mul_ne_top
      (ENNReal.add_ne_top.2 ⟨hn _, ENNReal.one_ne_top⟩) ENNReal.ofReal_ne_top⟩,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hn _)) hp⟩

omit [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- **At fixed users' coins, oracle of the base scheme and experiment**: the hedged game and the
game against the ideal-mask signer at a fixed mask oracle, both averaged over a uniform mask
oracle, are within the hedged error in the quantum random-oracle model. -/
theorem eclose_hedgedQ (ka : ℕ) (keys : Fin n → S.KeyCoins) (H : S.Orc) (b : Bool) {ρb : ℝ≥0∞}
    (hρ : ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → W.meanAttempt H keys c b none ≤ ρb) :
    EClose (∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
        acceptLaw enc (fun s => D keys H s.1 s.2) Y (A.rounds enc E Qs honest keys H Y b fun c =>
          W.real.signLaw (H, Y) (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg) true)
      (∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
        acceptLaw enc (fun s => D keys H s.1 s.2) Y
          (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b) true)
      (W.hedgeErrorQ Q q ka ρb) := by
  have hI : ∀ c : S.Choice n, c.signLaw H keys b =
      (untilSome (meanAtt (fun c : S.Choice n =>
        W.attempt H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg) c)).map fun o => o.getD W.dflt :=
    fun c => W.signLaw_eq H (S.sk (keys (c.user b))) _ _ _
  have core := sum_uniform_hedged_closeQ (k := ka)
    (fun c : S.Choice n => W.attempt H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg) W.dflt
    (fun j s c x => roundLaw (PubAnonAdversary.proofLawAt E Qs honest H) S.stmtPub s.1
      (S.proved H b c x)) (fun c : S.Choice n => S.Admit H c.ring c.msg) enc
    (fun j s => A.choose j keys H s.1 s.2) (fun s => D keys H s.1 s.2)
    (fun j s c hc x => by simp [PubSigner.proved, hc]) (ρb := ρb) fun Y j s c hc ha => by
      obtain ⟨w, rfl⟩ := QueryAlg.exists_out_of_outLaw_ne_zero _ _ hc
      exact hρ _ (A.choose_mem j keys H s.1 s.2 w) (A.choose_valid j keys H s.1 s.2 w) ha
  simp only [QAdversary.rounds, hI]
  exact core

omit [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The advantage of a game with a bit as outcome is the difference of the probabilities of
`true`. -/
theorem _root_.GordieHowe.gameAdvantage_true (p r : PMF Bool) :
    GordieHowe.gameAdvantage p r {true} = |(p true).toReal - (r true).toReal| := by
  have h : ∀ μ : PMF Bool, μ.toOuterMeasure (Set.ofPred fun x => x ∈ ({true} : Set Bool)) = μ true :=
    fun μ => by
      rw [show (Set.ofPred fun x => x ∈ ({true} : Set Bool)) = {true} from Set.ext fun _ => Iff.rfl,
        PMF.toOuterMeasure_apply_singleton]
  simp only [GordieHowe.gameAdvantage, GordieHowe.advantage, h]

omit [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- **Anonymity of the hedged signer in the quantum random-oracle model from anonymity of the
ideal-mask signer** (the step from the idealized signer to FIPS 204 hedged signing, with the mask
derivation `ExpandMask(H(K ‖ rnd ‖ µ), κ)` a random oracle `W.MaskOrc` queried in superposition,
and a fresh nonce `rnd` for every attempt): for an adversary and a distinguisher that are quantum
algorithms with `q` queries to the mask oracle in each round and for the guess (`QAdversary`,
`QDist`), the advantage against the hedged signer is at most the average over the mask oracle of
the advantage against the ideal-mask signer at that mask oracle, plus twice the hedged error at
every number `k` of attempts: `(Q k)² / |R| + (Q + 1) · 2 q √(Q k / |R|) + 2 Q ρ^k`, `ρ` bounding
the probability that a fresh-mask attempt of a valid admitted challenge rejects. The bound needs
the nonces to be fresh: deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_advantageAt (ka : ℕ) (ρ : (Fin n → S.KeyCoins) → S.Orc → ℝ≥0∞)
    (hρ1 : ∀ keys H, ρ keys H ≤ 1)
    (hρ : ∀ keys H, ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → ∀ b,
      W.meanAttempt H keys c b none ≤ ρ keys H) :
    A.advantage D enc E Qs honest ≤
      𝔼 Y : W.MaskOrc, A.advantageAt D enc E Qs honest Y +
        2 * 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, (W.hedgeErrorQ Q q ka (ρ keys H)).toReal := by
  set err : (Fin n → S.KeyCoins) → S.Orc → ℝ≥0∞ := fun keys H => W.hedgeErrorQ Q q ka (ρ keys H)
  have herr : ∀ keys H, err keys H ≠ ⊤ := fun keys H => hedgeErrorQ_ne_top W Q q ka (hρ1 keys H)
  set e : ℝ≥0∞ := ∑ keys, PMF.uniformOfFintype _ keys * ∑ H, PMF.uniformOfFintype _ H * err keys H
  have he : e ≠ ⊤ := ENNReal.sum_ne_top.2 fun keys _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ENNReal.sum_ne_top.2 fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (herr keys H))
  have heR : e.toReal = 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, (err keys H).toReal := by
    rw [toReal_sum_uniform_mul fun keys => ENNReal.sum_ne_top.2 fun H _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (herr keys H)]
    exact Finset.expect_congr rfl fun keys _ => toReal_sum_uniform_mul (herr keys)
  set PR : Bool → ℝ≥0∞ := fun b => A.game D enc E Qs honest b true
  set PI : W.MaskOrc → Bool → ℝ≥0∞ := fun Y b => A.gameAt D enc E Qs honest Y b true
  have hclose : ∀ b, EClose (PR b) (∑ Y, PMF.uniformOfFintype _ Y * PI Y b) e := fun b => by
    have hPR : PR b = ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
        ∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
          acceptLaw enc (fun s => D keys H s.1 s.2) Y (A.rounds enc E Qs honest keys H Y b fun c =>
            W.real.signLaw (H, Y) (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg) true := by
      simp only [PR, QAdversary.game, PMF.bind_apply, tsum_fintype]
    have hPI : ∀ Y, PI Y b = ∑ keys, PMF.uniformOfFintype _ keys *
        ∑ H : S.Orc, PMF.uniformOfFintype _ H * acceptLaw enc (fun s => D keys H s.1 s.2) Y
          (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b) true := fun Y => by
      simp only [PI, QAdversary.gameAt, PMF.bind_apply, tsum_fintype]
    have hRt : ∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y * ∑ keys, PMF.uniformOfFintype _ keys *
        ∑ H : S.Orc, PMF.uniformOfFintype _ H * acceptLaw enc (fun s => D keys H s.1 s.2) Y
          (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b) true =
        ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
          ∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y * acceptLaw enc (fun s => D keys H s.1 s.2) Y
            (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b) true := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun keys _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun Y _ => by ring
    rw [hPR]
    simp only [hPI]
    rw [hRt]
    exact EClose.wsum _ _ fun keys => EClose.wsum _ _ fun H =>
      eclose_hedgedQ A D enc E Qs honest ka keys H b fun c hc hv ha => hρ keys H c hc hv ha b
  have hfin : ∀ b, ∑ Y, PMF.uniformOfFintype _ Y * PI Y b ≤ 1 := fun b =>
    (Finset.sum_le_sum fun Y _ => mul_le_of_le_one_right' (PMF.coe_le_one _ _)).trans_eq
      (PMF.sum_coe _)
  have hreal : ∀ b, |(PR b).toReal - (∑ Y, PMF.uniformOfFintype _ Y * PI Y b).toReal| ≤ e.toReal :=
    fun b => by
      have h1 := (hclose b).1
      have h2 := (hclose b).2
      have hP : PR b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _)
      have hI : (∑ Y, PMF.uniformOfFintype _ Y * PI Y b) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (hfin b)
      have r1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI, he⟩) h1
      have r2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hP, he⟩) h2
      rw [ENNReal.toReal_add hI he] at r1
      rw [ENNReal.toReal_add hP he] at r2
      rw [abs_le]
      constructor <;> linarith
  have hmix : |(∑ Y, PMF.uniformOfFintype _ Y * PI Y false).toReal -
      (∑ Y, PMF.uniformOfFintype _ Y * PI Y true).toReal| ≤
      𝔼 Y : W.MaskOrc, A.advantageAt D enc E Qs honest Y := by
    refine (PMF.abs_sum_mul_sub_sum_mul_le _ (fun Y => PMF.coe_le_one _ _)
      fun Y => PMF.coe_le_one _ _).trans_eq ?_
    rw [PMF.sum_toReal_uniformOfFintype_mul]
    refine Finset.expect_congr rfl fun Y _ => ?_
    rw [QAdversary.advantageAt, GordieHowe.gameAdvantage_true]
  have hadv : A.advantage D enc E Qs honest = |(PR false).toReal - (PR true).toReal| :=
    GordieHowe.gameAdvantage_true _ _
  rw [hadv, ← heR]
  have h0 := hreal false
  have h1 := hreal true
  rw [abs_le] at h0 h1 hmix ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, hmix.1, hmix.2]

end MaskedSigner

end HedgedGameQ

/-! ### One round: the quantum adversary at a fixed mask oracle is a mixture of classical ones -/

section OneRound

/-- **A bound over a mixture by the best component**: some component has at least the weighted
average. -/
theorem _root_.PMF.exists_sum_toReal_mul_le {β : Type*} [Fintype β] (μ : PMF β) (F : β → ℝ) :
    ∃ b, ∑ a, (μ a).toReal * F a ≤ F b := by
  have hne : (Finset.univ : Finset β).Nonempty := by
    obtain ⟨a, -⟩ := μ.support_nonempty
    exact ⟨a, Finset.mem_univ a⟩
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ F hne
  refine ⟨b, ?_⟩
  calc ∑ a, (μ a).toReal * F a ≤ ∑ a, (μ a).toReal * F b :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hb a (Finset.mem_univ a))
          ENNReal.toReal_nonneg
    _ = F b := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

/-- **Binding a coordinate of a product law**: when `a ← p` reads only the coordinate `φ a` of
`T ← pi ν`, drawing `T` up front is drawing that coordinate after `a`. -/
theorem _root_.PMF.pi_bind_bind_coord {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {δ : ι' → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] {α' γ : Type*} (ν : ∀ i, PMF (δ i)) (p : PMF α')
    (φ : α' → ι') (g : (a : α') → δ (φ a) → PMF γ) :
    (PMF.pi ν).bind (fun T => p.bind fun a => g a (T (φ a))) =
      p.bind fun a => (ν (φ a)).bind (g a) := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  rw [sum_mul_tsum_mul_comm (fun T => PMF.pi ν T) (fun a => p a) (fun T a => g a (T (φ a)) x)]
  refine tsum_congr fun a => ?_
  congr 1
  exact PMF.sum_pi_mul_apply_coord ν (φ a) fun t => g a t x

/-- **An average of a bounded function under a bind.** -/
theorem _root_.PMF.tsum_bind_mul {α' β : Type*} (μ : PMF α') (k : α' → PMF β) (F : β → ℝ≥0∞) :
    ∑' b, μ.bind k b * F b = ∑' a, μ a * ∑' b, k a b * F b := by
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

/-- **An average of a bounded function under a map.** -/
theorem _root_.PMF.tsum_map_mul {α' β : Type*} (μ : PMF α') (g : α' → β) (F : β → ℝ≥0∞) :
    ∑' b, μ.map g b * F b = ∑' a, μ a * F (g a) := by
  classical
  rw [PMF.map, PMF.tsum_bind_mul]
  refine tsum_congr fun a => ?_
  congr 1
  rw [tsum_eq_single (g a) fun b hb => by simp [Function.comp_apply, PMF.pure_apply, hb]]
  simp [Function.comp_apply, PMF.pure_apply]

/-- **A bounded test distinguishes two laws at most as well as the likelier-outcome event**: for
`f ≤ 1`, the averages of `f` under `p` and `r` differ by at most the advantage of the event
`{a | r a < p a}`. -/
theorem _root_.PMF.abs_toReal_tsum_mul_sub_le_gameAdvantage {α' : Type*} (p r : PMF α') {f : α' → ℝ≥0∞}
    (hf : ∀ a, f a ≤ 1) :
    |(∑' a, p a * f a).toReal - (∑' a, r a * f a).toReal| ≤
      GordieHowe.gameAdvantage p r {a | r a < p a} := by
  classical
  set S : Set α' := {a | r a < p a}
  have hsum : PMF.etv p r + r.toOuterMeasure S = p.toOuterMeasure S := by
    unfold PMF.etv
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, tsub_add_cancel_of_le (le_of_lt ha)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, add_zero]
      exact tsub_eq_zero_of_le (not_lt.1 ha)
  have hle : ∀ (μ ν : PMF α'), ∑' a, μ a * f a ≤ ∑' a, ν a * f a + PMF.etv μ ν := fun μ ν => by
    unfold PMF.etv
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    calc μ a * f a ≤ (ν a + (μ a - ν a)) * f a := by gcongr; exact le_add_tsub
      _ = ν a * f a + (μ a - ν a) * f a := add_mul _ _ _
      _ ≤ ν a * f a + (μ a - ν a) := by gcongr; exact mul_le_of_le_one_right' (hf a)
  have hfin : ∀ μ : PMF α', ∑' a, μ a * f a ≠ ⊤ := fun μ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.tsum_le_tsum fun a =>
      mul_le_of_le_one_right' (hf a)).trans_eq (PMF.tsum_coe μ))
  have he : PMF.etv p r ≠ ⊤ := PMF.tsum_tsub_ne_top p r
  have hS : ∀ μ : PMF α', μ.toOuterMeasure S ≠ ⊤ := fun μ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have heR : (PMF.etv p r).toReal = (p.toOuterMeasure S).toReal - (r.toOuterMeasure S).toReal := by
    rw [← hsum, ENNReal.toReal_add he (hS r)]
    ring
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin r, he⟩) (hle p r)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin p, he⟩)
    ((hle r p).trans_eq (by rw [PMF.etv_comm]))
  rw [ENNReal.toReal_add (hfin r) he] at h1
  rw [ENNReal.toReal_add (hfin p) he] at h2
  have hadv : GordieHowe.gameAdvantage p r S =
      |(p.toOuterMeasure S).toReal - (r.toOuterMeasure S).toReal| := rfl
  rw [hadv, abs_le]
  have hpos : 0 ≤ (p.toOuterMeasure S).toReal - (r.toOuterMeasure S).toReal := by
    rw [← heR]; exact ENNReal.toReal_nonneg
  constructor
  · rw [abs_of_nonneg hpos]; linarith
  · rw [abs_of_nonneg hpos]; linarith

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg} {W : MaskedSigner S}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {M : SPBCS Mg P S.Stmt k kN kS L e} {n : ℕ}
  {G : Type} [Fintype G] [AddGroup G] {q : ℕ}

namespace PubAnonAdversary

variable (A : PubAnonAdversary S M n 1) (E : (j : ι) → (M.comp j).Encoder)
  {V : S.Orc → S.Stmt → FullTr P τ → Bool} (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type}
  [Fintype R] [Nonempty R] (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- **The distinguisher that guesses the experiment of greater probability**: it outputs `1` on
the outcomes more likely in experiment `0` than in experiment `1`. -/
def likelierDist : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
    PubHist S.Pub M.NIProof 1 → Prop :=
  fun keys H h hist => A.game E Qs honest true (keys, H, h, hist) <
    A.game E Qs honest false (keys, H, h, hist)

end PubAnonAdversary

namespace MaskedSigner

variable (A : W.QAdversary M G n 1 q) (D : W.QDist M G n 1 q) (enc : W.Mask → G)
  (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
  (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- **A table of measured challenges** of a one-round quantum adversary: at every value of the
users' coins, the oracle of the base scheme and the oracle of the compiled argument, a challenge
of the set valid for the users' coins. -/
abbrev QAdversary.Table : Type :=
  (x : (Fin n → S.KeyCoins) × S.Orc × (Query k kN kS L → Out k e)) →
    {c : A.choices // c.1.Valid S x.1}

/-- The quantum algorithm of the challenge at `x`, its output read as an entry of the table. -/
def QAdversary.entryAlg (x : (Fin n → S.KeyCoins) × S.Orc × (Query k kN kS L → Out k e)) :
    QueryAlg (W.Rnd × W.Pt) G q {c : A.choices // c.1.Valid S x.1} :=
  (A.choose 0 x.1 x.2.1 x.2.2 Fin.elim0).withOut fun w =>
    ⟨⟨_, A.choose_mem 0 x.1 x.2.1 x.2.2 Fin.elim0 w⟩, A.choose_valid 0 x.1 x.2.1 x.2.2 Fin.elim0 w⟩

open Classical in
/-- **The law of the table at the mask oracle `Y`**: every entry independent, the measured output
of its quantum algorithm with oracle access to `Y`. -/
noncomputable def QAdversary.tableLaw (Y : W.MaskOrc) : PMF A.Table :=
  PMF.pi fun x => (A.entryAlg x).outLaw (enc ∘ Y)

/-- **The adversary with its measured challenges fixed by the table `T`**, a classical adversary
against the ideal-mask signer with the same set of challenges. Averaged over the law of the table
at a mask oracle, its experiments are those of the quantum adversary at that mask oracle
(`QAdversary.gameAt_apply_eq`).

Running time: none is claimed. The table lists a measured challenge for every input; the
adversary is a component of a mixture used in the proof, and anonymity is statistical
(adversaries are unbounded). -/
def QAdversary.atTable (T : A.Table) : PubAnonAdversary S M n 1 where
  choices := A.choices
  choose _ keys H h _ := (T (keys, H, h)).1.1
  choose_mem _ keys H h _ := (T (keys, H, h)).1.2
  choose_valid _ keys H h _ := (T (keys, H, h)).2

open Classical in
/-- **The quantum adversary at a fixed mask oracle is the mixture of the adversaries at its
tables**: the probability that the distinguisher outputs `1` in the experiment `b` against the
ideal-mask signer at the mask oracle `Y` is the average over the table law at `Y` of the average
of the distinguisher's output probability over the classical experiment of the adversary at the
table. -/
theorem QAdversary.gameAt_apply_eq (Y : W.MaskOrc) (b : Bool) :
    A.gameAt D enc E Qs honest Y b true =
      ∑ T, A.tableLaw enc Y T * ∑' o, (A.atTable T).game E Qs honest b o *
        (D o.1 o.2.1 o.2.2.1 o.2.2.2).outLaw (enc ∘ Y) true := by
  set acc : (Fin n → S.KeyCoins) × S.Orc × (Query k kN kS L → Out k e) ×
      PubHist S.Pub M.NIProof 1 → ℝ≥0∞ := fun o => (D o.1 o.2.1 o.2.2.1 o.2.2.2).outLaw (enc ∘ Y) true
  -- the classical experiment at a table
  have hT : ∀ T : A.Table, ∑' o, (A.atTable T).game E Qs honest b o *
      (D o.1 o.2.1 o.2.2.1 o.2.2.2).outLaw (enc ∘ Y) true =
      ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
        ∑' s, seqRun (chooseSteps (fun j s c x => roundLaw (PubAnonAdversary.proofLawAt E Qs honest H)
          S.stmtPub s.1 (S.proved H b c x)) (fun j s => (T (keys, H, s.1)).1.1)
            (fun _ c => c.signLaw H keys b)) 1 le_rfl s * acc (keys, H, s.1, s.2) := fun T => by
    rw [PubAnonAdversary.game, PMF.tsum_bind_mul, tsum_fintype]
    refine Finset.sum_congr rfl fun keys _ => ?_
    rw [PMF.tsum_bind_mul, tsum_fintype]
    refine congrArg _ (Finset.sum_congr rfl fun H _ => ?_)
    rw [← PMF.map_bind, PMF.tsum_map_mul,
      PubAnonAdversary.tableLaw_bind_run_eq (A.atTable T) E Qs honest H keys b]
    rfl
  -- the quantum experiment at `Y`
  have hQ : A.gameAt D enc E Qs honest Y b true =
      ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
        ∑' s, seqRun (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b) 1 le_rfl s *
          acc (keys, H, s.1, s.2) := by
    simp only [QAdversary.gameAt, acceptLaw, PMF.bind_apply, tsum_fintype]
    rfl
  -- the mixture of the rounds
  have hmix : ∀ keys H, (A.tableLaw enc Y).bind (fun T =>
      seqRun (chooseSteps (fun j s c x => roundLaw (PubAnonAdversary.proofLawAt E Qs honest H)
        S.stmtPub s.1 (S.proved H b c x)) (fun j s => (T (keys, H, s.1)).1.1)
          (fun _ c => c.signLaw H keys b)) 1 le_rfl) =
      seqRun (A.rounds enc E Qs honest keys H Y b fun c => c.signLaw H keys b) 1 le_rfl := by
    intro keys H
    simp only [seqRun, QAdversary.tableLaw]
    refine (PMF.pi_bind_bind_coord (fun x => (A.entryAlg x).outLaw (enc ∘ Y))
      ((PMF.uniformOfFintype (Query k kN kS L → Out k e)).map fun h => (h, Fin.elim0))
      (fun a => (keys, H, a.1))
      (fun a t => ((t.1.1.signLaw H keys b).bind fun x => roundLaw
        (PubAnonAdversary.proofLawAt E Qs honest H) S.stmtPub a.1 (S.proved H b t.1.1 x)).map
          fun o => (a.1, Fin.snoc (α := fun _ => Option (S.Pub × M.NIProof)) a.2 o))).trans ?_
    refine congrArg _ (funext fun a => ?_)
    have ha : a.2 = Fin.elim0 := funext fun i => i.elim0
    have hlaw := (A.choose 0 keys H a.1 Fin.elim0).outLaw_withOut_map
      (fun w => (⟨⟨_, A.choose_mem 0 keys H a.1 Fin.elim0 w⟩,
        A.choose_valid 0 keys H a.1 Fin.elim0 w⟩ : {c : A.choices // c.1.Valid S keys}))
      (fun t => t.1.1) (fun _ => rfl) (enc ∘ Y)
    have hlaw' : (A.choose ⟨0, Nat.one_pos⟩ keys H a.1 Fin.elim0).outLaw (enc ∘ Y) =
        ((A.entryAlg (keys, H, a.1)).outLaw (enc ∘ Y)).map fun t => t.1.1 := hlaw.symm
    simp only [QAdversary.rounds, drawSteps, measChoice]
    rw [ha, hlaw', PMF.bind_map, PMF.map_bind]
    rfl
  have hper : ∀ keys H, ∑' s, seqRun (A.rounds enc E Qs honest keys H Y b fun c =>
      c.signLaw H keys b) 1 le_rfl s * acc (keys, H, s.1, s.2) =
      ∑ T, A.tableLaw enc Y T * ∑' s, seqRun (chooseSteps (fun j s c x =>
        roundLaw (PubAnonAdversary.proofLawAt E Qs honest H) S.stmtPub s.1 (S.proved H b c x))
          (fun j s => (T (keys, H, s.1)).1.1) (fun _ c => c.signLaw H keys b)) 1 le_rfl s *
            acc (keys, H, s.1, s.2) := fun keys H => by
    rw [← hmix keys H, PMF.tsum_bind_mul, tsum_fintype]
  rw [hQ]
  simp_rw [hT, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun keys _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [hper keys H, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

open Classical in
/-- **At a fixed mask oracle, a classical adversary does as well**: the advantage of the one-round
quantum adversary against the ideal-mask signer at the mask oracle `Y` is at most the advantage of
the classical adversary at some table, with the same set of challenges, and the distinguisher
that guesses the likelier experiment. -/
theorem QAdversary.exists_advantageAt_le (Y : W.MaskOrc) :
    ∃ T : A.Table, A.advantageAt D enc E Qs honest Y ≤
      (A.atTable T).advantage E Qs honest ((A.atTable T).likelierDist E Qs honest) := by
  set acc : (Fin n → S.KeyCoins) × S.Orc × (Query k kN kS L → Out k e) ×
      PubHist S.Pub M.NIProof 1 → ℝ≥0∞ := fun o => (D o.1 o.2.1 o.2.2.1 o.2.2.2).outLaw (enc ∘ Y) true
  have hacc : ∀ o, acc o ≤ 1 := fun o => PMF.coe_le_one _ _
  set F : A.Table → Bool → ℝ≥0∞ := fun T b => ∑' o, (A.atTable T).game E Qs honest b o * acc o
  have hF : ∀ T b, F T b ≤ 1 := fun T b => (ENNReal.tsum_le_tsum fun o =>
    mul_le_of_le_one_right' (hacc o)).trans_eq (PMF.tsum_coe _)
  obtain ⟨T, hT⟩ := PMF.exists_sum_toReal_mul_le (A.tableLaw enc Y)
    fun T => |(F T false).toReal - (F T true).toReal|
  refine ⟨T, ?_⟩
  rw [QAdversary.advantageAt, GordieHowe.gameAdvantage_true, A.gameAt_apply_eq, A.gameAt_apply_eq]
  refine ((PMF.abs_sum_mul_sub_sum_mul_le _ (fun T => hF T false) fun T => hF T true).trans hT).trans ?_
  exact PMF.abs_toReal_tsum_mul_sub_le_gameAdvantage _ _ hacc

open Classical in
/-- **The challenges of the set valid for the users' coins `keys`.** -/
noncomputable def QAdversary.validChoices (keys : Fin n → S.KeyCoins) : Finset (S.Choice n) :=
  A.choices.filter fun c => c.Valid S keys

/-- **At most `C` challenges of the set are valid for any key vector** (as
`PubAnonAdversary.ValidCountLe`). -/
def QAdversary.ValidCountLe (C : ℕ) : Prop :=
  ∀ keys : Fin n → S.KeyCoins, (A.validChoices keys).card ≤ C

omit [DecidableEq RMsg] [AddGroup G] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The adversary at every table has the quantum adversary's set of challenges. -/
theorem QAdversary.validCountLe_atTable {C : ℕ} (hC : A.ValidCountLe C) (T : A.Table) :
    (A.atTable T).ValidCountLe C :=
  hC

open Classical in
/-- **Anonymity of the hedged signer in the quantum random-oracle model, one challenge, from
anonymity against classical adversaries**: the advantage of a one-round quantum adversary against
the hedged signer is at most the average over the mask oracle `Y` of the advantage of a classical
adversary at `Y` against the ideal-mask signer (with the same set of challenges, the classical
adversary at some table of measured challenges, with the distinguisher that guesses the likelier
experiment, `QAdversary.exists_advantageAt_le`), plus twice the hedged error in the quantum
random-oracle model (`advantage_le_advantageAt`). -/
theorem QAdversary.exists_advantage_le (ka : ℕ) (ρ : (Fin n → S.KeyCoins) → S.Orc → ℝ≥0∞)
    (hρ1 : ∀ keys H, ρ keys H ≤ 1)
    (hρ : ∀ keys H, ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → ∀ b,
      W.meanAttempt H keys c b none ≤ ρ keys H) :
    ∃ T : W.MaskOrc → A.Table, A.advantage D enc E Qs honest ≤
      𝔼 Y : W.MaskOrc, (A.atTable (T Y)).advantage E Qs honest
          ((A.atTable (T Y)).likelierDist E Qs honest) +
        2 * 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, (W.hedgeErrorQ 1 q ka (ρ keys H)).toReal := by
  choose T hT using fun Y => A.exists_advantageAt_le D enc E Qs honest Y
  refine ⟨T, (advantage_le_advantageAt A D enc E Qs honest ka ρ hρ1 hρ).trans ?_⟩
  gcongr with Y
  exact hT Y

end MaskedSigner

end OneRound

/-! ### The hedged error, averaged -/

namespace MaskedSigner

variable {N : ℕ} {RMsg : Type} {S : PubSigner N RMsg}

open Classical in
/-- **The hedged error in the quantum random-oracle model at a keep bound on a good event**,
averaged: with `ρ = 1 - L` on the good event and `ρ = 1` off it, the hedged error is at most
`(Q k)² / |R| + (Q + 1) · 2 q √(Q k / |R|) + 2 Q ((1 - L)^k + Pr[¬ good])`. -/
theorem expect_toReal_hedgeErrorQ_le (W : MaskedSigner S) (Q q ka : ℕ) {α β : Type*} [Fintype α]
    [Nonempty α] [Fintype β] [Nonempty β] (Good : α → β → Prop) {L : ℝ} (hL0 : 0 ≤ L)
    (hL1 : L ≤ 1) :
    𝔼 a, 𝔼 b, (W.hedgeErrorQ Q q ka (1 - if Good a b then ENNReal.ofReal L else 0)).toReal ≤
      (Q * ka) ^ 2 * (Fintype.card W.Rnd : ℝ)⁻¹ +
        (Q + 1) * (2 * q * √(Q * ka / Fintype.card W.Rnd)) +
          2 * Q * ((1 - L) ^ ka + 𝔼 a, 𝔼 b, (if Good a b then 0 else 1 : ℝ)) := by
  have hpt : ∀ a b, (W.hedgeErrorQ Q q ka (1 - if Good a b then ENNReal.ofReal L else 0)).toReal ≤
      (Q * ka) ^ 2 * (Fintype.card W.Rnd : ℝ)⁻¹ +
        (Q + 1) * (2 * q * √(Q * ka / Fintype.card W.Rnd)) +
          2 * Q * ((1 - L) ^ ka + (if Good a b then 0 else 1 : ℝ)) := fun a b => by
    have hc : (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have hn : ∀ m : ℕ, (m : ℝ≥0∞) ≠ ⊤ := fun m => ENNReal.natCast_ne_top m
    set ρ : ℝ≥0∞ := 1 - if Good a b then ENNReal.ofReal L else 0
    have hρ1 : ρ ≤ 1 := tsub_le_self
    have hρk : (ρ ^ ka).toReal ≤ (1 - L) ^ ka + (if Good a b then 0 else 1 : ℝ) := by
      rw [ENNReal.toReal_pow]
      by_cases hG : Good a b
      · simp only [ρ, hG, if_true, add_zero]
        rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hL1) ENNReal.one_ne_top,
          ENNReal.toReal_one, ENNReal.toReal_ofReal hL0]
      · simp only [ρ, hG, if_false, tsub_zero, ENNReal.toReal_one, one_pow]
        have : 0 ≤ (1 - L) ^ ka := pow_nonneg (by linarith) ka
        linarith
    have hq : 0 ≤ 2 * (q : ℝ) * √(Q * ka / Fintype.card W.Rnd) := by positivity
    unfold hedgeErrorQ
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top (hn _) (hn _))) hc, ENNReal.mul_ne_top
          (ENNReal.add_ne_top.2 ⟨hn _, ENNReal.one_ne_top⟩) ENNReal.ofReal_ne_top⟩)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hn _))
          (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hρ1))),
      ENNReal.toReal_add (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top (hn _) (hn _))) hc) (ENNReal.mul_ne_top
          (ENNReal.add_ne_top.2 ⟨hn _, ENNReal.one_ne_top⟩) ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_add (hn _) ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal hq]
    rw [ENNReal.toReal_pow] at hρk
    have hQ : (0 : ℝ) ≤ 2 * Q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hρk hQ]
  refine (Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun b _ => hpt a b).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  exact le_rfl

end MaskedSigner

end GordieHowe.Ring
