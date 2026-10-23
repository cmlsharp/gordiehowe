-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.LayerSumcheck
public import GordieHowe.ProofSystem.GKR.ClaimEvaluation
public import GordieHowe.ProofSystem.Zerocheck.Round

@[expose] public section

/-!
# The sumcheck over the bit-index variables of a word claim

The values of the masked sumcheck that reduces a batch's opening claim, a linear claim
`Σ_{q,b} W_q[b] t_{q,b}` on the bits `t_{q,b}` of `nw` words with `2^m` bits each, to a claim at
one point `ρ ∈ K^m` of the bit index (the Binius64 shift reduction's first phase, Binius64
Blueprint section 4.7).
Bit `l` of the bit index `b` is variable `l`, bound low first (`GKR.ClaimEvaluation.binaryLabelEquiv`).

* **The summand** (`summand`): `h = Σ_q W̃_q · t̃_q`, the multilinear extensions over the bit index
  multiplied, of degree at most two in each variable (`degreeOf_summand_le`). Its sum over the cube
  is the claim (`trueClaim_zero`), and its value at `ρ` is `Σ_q W̃_q(ρ) t̃_q(ρ)` (`trueClaim_last`),
  evaluated by the executable `summandEval` (`eval_summand`).
* **The rounds**: Longfellow's degree-two round (`Sumcheck.Round`), the prover sending `p_i(0)` and
  `p_i(g)`, the verifier setting `p_i(1) = claim_i − p_i(0)` and the next claim to the
  interpolation at `ρ_i` (`claims`, `step`).
* **Soundness** (`sound`): a last claim equal to `h(ρ)` gives the input claim, or a round `i` whose
  incoming claim is false and whose outgoing claim is true (`RoundBad`); at most two values of
  `ρ_i` make round `i` bad (`card_roundBad_le`, error `2/|K|` per round).
* **Completeness** (`claims_honest`): the honest messages (`honestMsg`, computed from executable
  evaluations of the summand, reading only the challenges before their round) carry a true input
  claim to `h(ρ)`.

The weights `W` and the bits `t` are arbitrary tables; the masked reduction that runs these rounds
(`GordieHowe/ProofSystem/Zerocheck/BitSumcheckIP.lean`) reads them from the opening claim and the
committed bits.
-/

namespace GordieHowe.BitSumcheck

open MvPolynomial Polynomial GKR.LayerSumcheck GKR.ClaimEvaluation
open GKR.LayerPolynomial (Cube boolValue)
open scoped NNReal

variable {K : Type} [Field K] {m nw : ℕ}

/-! ### The summand -/

/-- A table on the bit index read on the cube (`binaryLabelEquiv`). -/
noncomputable def cubeTable (w : Fin (2 ^ m) → K) : Cube m → K :=
  fun x => w ((binaryLabelEquiv m).symm x)

/-- **The summand** `h = Σ_q W̃_q · t̃_q` over the bit-index variables. -/
noncomputable def summand (W t : Fin nw → Fin (2 ^ m) → K) : MvPolynomial (Fin m) K :=
  ∑ q, mle (cubeTable (W q)) * mle (cubeTable (t q))

/-- **The summand's value**, executable: `Σ_q W̃_q(e) t̃_q(e)`, each multilinear extension the
`eq`-weighted table (`evalTable`). -/
def summandEval (W t : Fin nw → Fin (2 ^ m) → K) (e : Fin m → K) : K :=
  ∑ q, evalTable (W q) e * evalTable (t q) e

theorem eval_summand (W t : Fin nw → Fin (2 ^ m) → K) (e : Fin m → K) :
    eval e (summand W t) = summandEval W t e := by
  simp only [summand, summandEval, map_sum, map_mul, eval_mle, evalTable_eq_value]
  rfl

/-- **The summand has degree at most two in each variable**: a sum of products of two
multilinear extensions. -/
theorem degreeOf_summand_le (W t : Fin nw → Fin (2 ^ m) → K) (v : Fin m) :
    (summand W t).degreeOf v ≤ 2 := by
  apply (degreeOf_sum_le v Finset.univ _).trans
  apply Finset.sup_le
  intro q _
  apply (degreeOf_mul_le v _ _).trans
  have h1 := mle_degreeOf_le (cubeTable (W q)) v
  have h2 := mle_degreeOf_le (cubeTable (t q)) v
  omega

/-- **The summand's sum over the cube is the linear claim** `Σ_{q,b} W_q[b] t_{q,b}`. -/
theorem sum_cube_summand (W t : Fin nw → Fin (2 ^ m) → K) :
    ∑ x : Cube m, eval (fun j => boolValue (F := K) (x j)) (summand W t) =
      ∑ q, ∑ b, W q b * t q b := by
  simp only [summand, map_sum, map_mul, mle_boolean]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Fintype.sum_equiv (binaryLabelEquiv m).symm _ _ fun x => ?_
  rfl

/-! ### The prefix of challenges and the remaining variables -/

/-- The challenges before round `i`, the later variables zero. -/
def pre (ρ : Fin m → K) (i : ℕ) : Fin m → K := fun v => if v.val < i then ρ v else 0

/-- The variables from round `i` on, in order. -/
def todo (m i : ℕ) : List (Fin m) := (List.finRange m).drop i

theorem todo_zero : todo m 0 = List.finRange m := rfl

theorem todo_last : todo m m = [] := by
  simp [todo]

theorem todo_eq_cons (i : Fin m) : todo m i = i :: todo m (i.val + 1) := by
  unfold todo
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

theorem pre_last (ρ : Fin m → K) : pre ρ m = ρ := by
  funext v
  simp [pre, v.isLt]

theorem update_pre (ρ : Fin m → K) (i : Fin m) :
    Function.update (pre ρ i) i (ρ i) = pre ρ (i.val + 1) := by
  funext v
  by_cases hv : v = i
  · subst hv
    simp [pre]
  · rw [Function.update_of_ne hv]
    have : v.val ≠ i.val := fun h => hv (Fin.ext h)
    simp only [pre]
    split_ifs <;> first | rfl | omega

theorem pre_congr {ρ ρ' : Fin m → K} {i : ℕ} (h : ∀ v : Fin m, v.val < i → ρ v = ρ' v) :
    pre ρ i = pre ρ' i := by
  funext v
  simp only [pre]
  split_ifs with hv
  · exact h v hv
  · rfl

/-! ### The true claims and the round polynomials -/

variable (W t : Fin nw → Fin (2 ^ m) → K)

/-- **The true claim of round `i`**: the summand summed over the variables from `i` on, the
earlier ones at their challenges. -/
noncomputable def trueClaim (ρ : Fin m → K) (i : ℕ) : K :=
  marginal (summand W t) (pre ρ i) (todo m i)

/-- **The true round polynomial of round `i`**: the summand with variable `i` free, the earlier
ones at their challenges, the later ones summed. -/
noncomputable def roundPoly (ρ : Fin m → K) (i : Fin m) : K[X] :=
  roundPolynomial (summand W t) (pre ρ i) i (todo m (i.val + 1))

theorem trueClaim_zero (ρ : Fin m → K) : trueClaim W t ρ 0 = ∑ q, ∑ b, W q b * t q b := by
  rw [trueClaim, todo_zero, marginal_complete _ _ _ (List.nodup_finRange m) (List.mem_finRange)]
  exact sum_cube_summand W t

theorem trueClaim_last (ρ : Fin m → K) : trueClaim W t ρ m = summandEval W t ρ := by
  rw [trueClaim, todo_last, marginal_final, pre_last, eval_summand]

theorem trueClaim_congr {ρ ρ' : Fin m → K} {i : ℕ} (h : ∀ v : Fin m, v.val < i → ρ v = ρ' v) :
    trueClaim W t ρ i = trueClaim W t ρ' i := by
  rw [trueClaim, trueClaim, pre_congr h]

theorem roundPoly_congr {ρ ρ' : Fin m → K} {i : Fin m} (h : ∀ v : Fin m, v < i → ρ v = ρ' v) :
    roundPoly W t ρ i = roundPoly W t ρ' i := by
  rw [roundPoly, roundPoly, pre_congr (i := i.val) fun v hv => h v hv]

theorem natDegree_roundPoly_le (ρ : Fin m → K) (i : Fin m) : (roundPoly W t ρ i).natDegree ≤ 2 :=
  (round_degree _ _ _ _).trans (degreeOf_summand_le W t i)

/-- The round polynomial's endpoints sum to the round's true claim. -/
theorem roundPoly_endpoints (ρ : Fin m → K) (i : Fin m) :
    (roundPoly W t ρ i).eval 0 + (roundPoly W t ρ i).eval 1 = trueClaim W t ρ i := by
  rw [roundPoly, round_endpoints, trueClaim, todo_eq_cons i]

/-- The round polynomial at the round's challenge is the next round's true claim. -/
theorem roundPoly_eval_self (ρ : Fin m → K) (i : Fin m) :
    (roundPoly W t ρ i).eval (ρ i) = trueClaim W t ρ (i.val + 1) := by
  rw [roundPoly, round_eval, update_pre, trueClaim]

/-! ### The verifier's claims -/

/-- **One round's update** (`Poly<3>::dot_interpolation`): the interpolation at `r` of the values
`p0`, `incoming − p0`, `p2` at the nodes. -/
def step (nodes : Sumcheck.Nodes K) (r incoming p0 p2 : K) : K :=
  Sumcheck.Round.coefficients nodes r 1 * (incoming - p0) +
    Sumcheck.Round.coefficients nodes r 0 * p0 + Sumcheck.Round.coefficients nodes r 2 * p2

theorem step_eq_eval (nodes : Sumcheck.Nodes K) (r incoming p0 p2 : K) :
    step nodes r incoming p0 p2 = (Sumcheck.Round.reconstruct nodes incoming p0 p2).eval r :=
  (Sumcheck.Round.reconstruct_eval nodes incoming p0 p2 r).symm

/-- **The verifier's claims** from the input claim `c0`, round `i`'s unmasked values
`msg i 0 = p_i(0)` and `msg i 1 = p_i(g)`, and the challenges `ρ`. -/
def claims (nodes : Sumcheck.Nodes K) (c0 : K) (msg : Fin m → Fin 2 → K) (ρ : Fin m → K) :
    Fin (m + 1) → K :=
  Fin.induction c0 fun i c => step nodes (ρ i) c (msg i 0) (msg i 1)

@[simp] theorem claims_zero (nodes : Sumcheck.Nodes K) (c0 : K) (msg : Fin m → Fin 2 → K)
    (ρ : Fin m → K) : claims nodes c0 msg ρ 0 = c0 := rfl

theorem claims_succ (nodes : Sumcheck.Nodes K) (c0 : K) (msg : Fin m → Fin 2 → K)
    (ρ : Fin m → K) (i : Fin m) :
    claims nodes c0 msg ρ i.succ =
      step nodes (ρ i) (claims nodes c0 msg ρ i.castSucc) (msg i 0) (msg i 1) := by
  simp only [claims, Fin.induction_succ]

/-- **The claim before round `j` reads only the values and challenges before `j`.** -/
theorem claims_congr (nodes : Sumcheck.Nodes K) (c0 : K) {msg msg' : Fin m → Fin 2 → K}
    {ρ ρ' : Fin m → K} (j : Fin (m + 1)) (hm : ∀ v : Fin m, v.val < j.val → msg v = msg' v)
    (hρ : ∀ v : Fin m, v.val < j.val → ρ v = ρ' v) :
    claims nodes c0 msg ρ j = claims nodes c0 msg' ρ' j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hi : i.val < i.succ.val := by simp
    rw [claims_succ, claims_succ, ih (fun v hv => hm v (by simp at hv ⊢; omega))
      (fun v hv => hρ v (by simp at hv ⊢; omega)), hm i hi, hρ i hi]

/-! ### Soundness -/

/-- **Round `i` is bad**: its incoming claim is false and its outgoing claim is true. -/
def RoundBad (nodes : Sumcheck.Nodes K) (c0 : K) (msg : Fin m → Fin 2 → K) (ρ : Fin m → K)
    (i : Fin m) : Prop :=
  claims nodes c0 msg ρ i.castSucc ≠ trueClaim W t ρ i ∧
    claims nodes c0 msg ρ i.succ = trueClaim W t ρ (i.val + 1)

/-- **Round `i`'s event reads only the values through `i` and the challenges through `i`.** -/
theorem roundBad_congr (nodes : Sumcheck.Nodes K) (c0 : K) {msg msg' : Fin m → Fin 2 → K}
    {ρ ρ' : Fin m → K} (i : Fin m) (hm : ∀ v : Fin m, v ≤ i → msg v = msg' v)
    (hρ : ∀ v : Fin m, v ≤ i → ρ v = ρ' v) :
    RoundBad W t nodes c0 msg ρ i ↔ RoundBad W t nodes c0 msg' ρ' i := by
  have hm' : ∀ v : Fin m, v.val < i.succ.val → msg v = msg' v :=
    fun v hv => hm v (by simp at hv; exact Fin.le_def.mpr (by omega))
  have hρ' : ∀ v : Fin m, v.val < i.succ.val → ρ v = ρ' v :=
    fun v hv => hρ v (by simp at hv; exact Fin.le_def.mpr (by omega))
  rw [RoundBad, RoundBad, claims_congr nodes c0 i.succ hm' hρ',
    claims_congr nodes c0 i.castSucc (fun v hv => hm' v (by simp at hv ⊢; omega))
      (fun v hv => hρ' v (by simp at hv ⊢; omega)),
    trueClaim_congr W t (i := i.val) (fun v hv => hρ' v (by simp; omega)),
    trueClaim_congr W t (i := i.val + 1) (fun v hv => hρ' v (by simpa using hv))]

open Classical in
/-- **At most two challenges make round `i` bad** (`Round.reconstructed_bad_challenge_count`):
the incoming claim, the values and the true round polynomial are fixed before `ρ_i`, the
outgoing claim is the reconstructed quadratic at `ρ_i` and the next true claim the true round
polynomial at `ρ_i`, both of degree at most two. -/
theorem card_roundBad_le [Fintype K] (nodes : Sumcheck.Nodes K) (c0 : K)
    (msg : Fin m → Fin 2 → K) (ρ : Fin m → K) (i : Fin m) :
    ((Finset.univ.filter fun x : K =>
        RoundBad W t nodes c0 msg (Function.update ρ i x) i).card : ℝ≥0) ≤
      (2 / Fintype.card K : ℝ≥0) * Fintype.card K := by
  have hlt : ∀ x : K, ∀ v : Fin m, v.val < i.val → Function.update ρ i x v = ρ v :=
    fun x v hv => Function.update_of_ne (fun h => by rw [h] at hv; omega) _ _
  set c := claims nodes c0 msg ρ i.castSucc
  have hc : ∀ x, claims nodes c0 msg (Function.update ρ i x) i.castSucc = c := fun x =>
    claims_congr nodes c0 i.castSucc (fun _ _ => rfl) fun v hv => hlt x v (by simpa using hv)
  have hT : ∀ x, trueClaim W t (Function.update ρ i x) i = trueClaim W t ρ i :=
    fun x => trueClaim_congr W t (hlt x)
  have hR : ∀ x, roundPoly W t (Function.update ρ i x) i = roundPoly W t ρ i :=
    fun x => roundPoly_congr W t fun v hv => hlt x v hv
  by_cases hfalse : c = trueClaim W t ρ i
  · have hempty : (Finset.univ.filter fun x : K =>
        RoundBad W t nodes c0 msg (Function.update ρ i x) i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun x _ h => h.1 (by rw [hc, hT]; exact hfalse)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hsub : (Finset.univ.filter fun x : K =>
        RoundBad W t nodes c0 msg (Function.update ρ i x) i) ⊆
        Finset.univ.filter fun x : K =>
          Sumcheck.Round.coefficients nodes x 1 * (c - msg i 0) +
            Sumcheck.Round.coefficients nodes x 0 * msg i 0 +
            Sumcheck.Round.coefficients nodes x 2 * msg i 1 = (roundPoly W t ρ i).eval x := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h2 := hx.2.2
      rw [claims_succ, hc, Function.update_self, ← roundPoly_eval_self, hR,
        Function.update_self] at h2
      exact h2
    refine le_trans ((Nat.cast_le (α := ℝ≥0)).mpr (Finset.card_le_card hsub)) ?_
    refine Sumcheck.Round.reconstructed_bad_challenge_count_nnreal nodes c (msg i 0) (msg i 1)
      (roundPoly W t ρ i) (natDegree_roundPoly_le W t ρ i) ?_
    rw [roundPoly_endpoints]
    exact hfalse

/-- **Soundness of the rounds**: when the last claim is the summand at `ρ`, the input claim is the
linear claim, or some round is bad. -/
theorem sound (nodes : Sumcheck.Nodes K) (c0 : K) (msg : Fin m → Fin 2 → K) (ρ : Fin m → K)
    (h : claims nodes c0 msg ρ (Fin.last m) = summandEval W t ρ) :
    c0 = ∑ q, ∑ b, W q b * t q b ∨ ∃ i, RoundBad W t nodes c0 msg ρ i := by
  suffices key : ∀ j : Fin (m + 1),
      claims nodes c0 msg ρ j = trueClaim W t ρ j ∨ ∃ i, RoundBad W t nodes c0 msg ρ i by
    rcases key 0 with h0 | hb
    · exact Or.inl (by rw [← trueClaim_zero W t ρ]; exact h0)
    · exact Or.inr hb
  intro j
  induction j using Fin.reverseInduction with
  | last => exact Or.inl (by rw [h, Fin.val_last, trueClaim_last])
  | cast i ih =>
    rcases ih with hs | hb
    · by_cases hi : claims nodes c0 msg ρ i.castSucc = trueClaim W t ρ i
      · exact Or.inl hi
      · exact Or.inr ⟨i, hi, by simpa using hs⟩
    · exact Or.inr hb

/-! ### The honest prover -/

/-- The node of message slot `j`: `0` for `p(0)`, the third node `g` for `p(g)`. -/
def slotNode (nodes : Sumcheck.Nodes K) (j : Fin 2) : K := ![nodes.point 0, nodes.point 2] j

/-- **The honest value of slot `j` of round `i`** (executable): the summand's evaluations summed
over the later variables, variable `i` at the slot's node and the earlier ones at their
challenges. -/
def honestMsg (nodes : Sumcheck.Nodes K) (ρ : Fin m → K) (i : Fin m) (j : Fin 2) : K :=
  marginalFn (summandEval W t) (Function.update (pre ρ i) i (slotNode nodes j)) (todo m (i.val + 1))

/-- The honest value is the true round polynomial at the slot's node. -/
theorem honestMsg_eq (nodes : Sumcheck.Nodes K) (ρ : Fin m → K) (i : Fin m) (j : Fin 2) :
    honestMsg W t nodes ρ i j = (roundPoly W t ρ i).eval (slotNode nodes j) := by
  rw [roundPoly, round_eval_marginalFn, honestMsg]
  congr 1
  funext e
  exact (eval_summand W t e).symm

/-- The honest values of round `i` read only the challenges before `i`. -/
theorem honestMsg_congr (nodes : Sumcheck.Nodes K) {ρ ρ' : Fin m → K} {i : Fin m}
    (h : ∀ v : Fin m, v < i → ρ v = ρ' v) : honestMsg W t nodes ρ i = honestMsg W t nodes ρ' i := by
  funext j
  rw [honestMsg, honestMsg, pre_congr (i := i.val) fun v hv => h v hv]

/-- **Completeness of the rounds**: from the linear claim, the honest values carry every claim to
its true value, the last one to the summand at `ρ`. -/
theorem claims_honest (nodes : Sumcheck.Nodes K) (c0 : K) (ρ : Fin m → K)
    (h0 : c0 = ∑ q, ∑ b, W q b * t q b) :
    claims nodes c0 (honestMsg W t nodes ρ) ρ (Fin.last m) = summandEval W t ρ := by
  suffices key : ∀ j : Fin (m + 1),
      claims nodes c0 (honestMsg W t nodes ρ) ρ j = trueClaim W t ρ j by
    rw [key, Fin.val_last, trueClaim_last]
  intro j
  induction j using Fin.induction with
  | zero => rw [claims_zero, h0, Fin.val_zero, trueClaim_zero]
  | succ i ih =>
    rw [claims_succ, ih, step_eq_eval, honestMsg_eq, honestMsg_eq, Fin.val_succ,
      ← roundPoly_eval_self]
    have hs : slotNode nodes 0 = 0 := by simp [slotNode, nodes.zero]
    have hg : slotNode nodes 1 = nodes.point 2 := by simp [slotNode]
    rw [Fin.val_castSucc, hs, hg, ← roundPoly_endpoints W t ρ i,
      Sumcheck.Round.reconstruct_eq_of_natDegree_le nodes (natDegree_roundPoly_le W t ρ i)]

end GordieHowe.BitSumcheck
