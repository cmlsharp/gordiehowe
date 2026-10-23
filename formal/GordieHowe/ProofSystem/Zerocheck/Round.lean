-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.LagrangeEval
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Basic.NNReal.Basic

@[expose] public section

/-!
# Longfellow's degree-two sumcheck round

The selected ZK path uses `ConstraintBuilder::next` in `lib/zk/zk_common.h`:
p(0) and p(2) are the two transmitted masked values, p(1) is reconstructed
as incoming−p(0), and the next claim is the Lagrange dot product at a fresh
challenge. Here “2” is a slot, not necessarily the field element 2:
`Field::poly_evaluation_point` gives [0,1,g] in GF(2^128) and [0,1,2]
in GoldExt. This module represents those nodes explicitly.

The polynomial root argument is the same single-round argument as ArkLib
`Sumcheck.Interaction.SingleRound.executeCommitted_soundness` at commit
0b5b67c63d74b26e38715bb90fa5d7d5a07def25 (Apache-2.0, Quang Dao), specialized
to the two Boolean endpoints and exposed as a finite counting bound. Only
Mathlib is imported for that argument; ArkLib's admitted interfaces
are not dependencies. Full Longfellow GKR layer wiring, alpha/beta challenges,
initial/final claims and protocol assembly are separate obligations.
-/

namespace GordieHowe.Sumcheck.Round
open IOP

open Polynomial
open scoped Classical NNReal

variable {F : Type} [Field F]

/-- The three interpolation nodes used by the implementation. -/
structure _root_.GordieHowe.Sumcheck.Nodes (F : Type) [Field F] where
  point : Fin 3 → F
  injective : Function.Injective point
  zero : point 0 = 0
  one : point 1 = 1

/-- Lagrange coefficients calculated by `Poly<3>::dot_interpolation::coef`. -/
def coefficients (nodes : Nodes F) (r : F) (j : Fin 3) : F :=
  Lagrange.basisEval Finset.univ nodes.point j r

/-- The coefficients are the values at `r` of the Lagrange basis on the nodes. -/
theorem coefficients_eq (nodes : Nodes F) (r : F) (j : Fin 3) :
    coefficients nodes r j = (Lagrange.basis Finset.univ nodes.point j).eval r :=
  (Lagrange.eval_basis_eq_basisEval _ _ _ _).symm

/-- Reconstruct the unique degree-two polynomial from the two revealed values
and the incoming claim. Its middle slot enforces p(0)+p(1)=incoming. -/
noncomputable def reconstruct (nodes : Nodes F) (incoming p0 p2 : F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes.point ![p0, incoming - p0, p2]

theorem reconstruct_degree (nodes : Nodes F) (incoming p0 p2 : F) :
    (reconstruct nodes incoming p0 p2).natDegree ≤ 2 := by
  apply natDegree_le_of_degree_le
  simpa [reconstruct] using
    Lagrange.degree_interpolate_le (s := Finset.univ) ![p0, incoming - p0, p2] nodes.injective.injOn

theorem reconstruct_eval_node (nodes : Nodes F) (incoming p0 p2 : F) (j : Fin 3) :
    (reconstruct nodes incoming p0 p2).eval (nodes.point j) = ![p0, incoming - p0, p2] j :=
  Lagrange.eval_interpolate_at_node _ nodes.injective.injOn (Finset.mem_univ j)

theorem reconstruct_sum (nodes : Nodes F) (incoming p0 p2 : F) :
    (reconstruct nodes incoming p0 p2).eval 0 +
      (reconstruct nodes incoming p0 p2).eval 1 = incoming := by
  rw [← nodes.zero, ← nodes.one, reconstruct_eval_node, reconstruct_eval_node]
  simp

theorem reconstruct_eval (nodes : Nodes F) (incoming p0 p2 r : F) :
    (reconstruct nodes incoming p0 p2).eval r =
      coefficients nodes r 1 * (incoming - p0) + coefficients nodes r 0 * p0 +
        coefficients nodes r 2 * p2 := by
  simp [reconstruct, Lagrange.interpolate_apply, Fin.sum_univ_three, coefficients_eq]
  ring

/-- **The honest values reconstruct the polynomial**: a polynomial of degree at most two is the
reconstruction from its endpoint sum and its values at the nodes `0` and `g`. -/
theorem reconstruct_eq_of_natDegree_le (nodes : Nodes F) {p : F[X]} (hp : p.natDegree ≤ 2) :
    reconstruct nodes (p.eval 0 + p.eval 1) (p.eval 0) (p.eval (nodes.point 2)) = p := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ nodes.injective.injOn
  · refine lt_of_le_of_lt (degree_le_of_natDegree_le hp) ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (by decide : 2 < 3)
  · intro j _
    fin_cases j <;> simp [nodes.zero, nodes.one]

/-- Any prover polynomial passing the Boolean endpoint check for a false
incoming claim differs from the correct polynomial. -/
theorem response_ne (incoming : F) (target response : F[X])
    (hfalse : incoming ≠ target.eval 0 + target.eval 1)
    (hsum : response.eval 0 + response.eval 1 = incoming) : response ≠ target := by
  intro heq
  exact hfalse (heq ▸ hsum.symm)

/-- At most two fresh challenges turn an incorrect incoming claim into the
correct outgoing evaluation, for arbitrary accepted degree-two messages. -/
theorem bad_challenge_count [Fintype F] (incoming : F) (target response : F[X])
    (htarget : target.natDegree ≤ 2) (hresponse : response.natDegree ≤ 2)
    (hfalse : incoming ≠ target.eval 0 + target.eval 1)
    (hsum : response.eval 0 + response.eval 1 = incoming) :
    (Finset.univ.filter fun r : F => response.eval r = target.eval r).card ≤ 2 := by
  have hne : response - target ≠ 0 := sub_ne_zero.mpr (response_ne incoming target response hfalse hsum)
  apply (Polynomial.card_le_degree_of_subset_roots (p := response - target) ?_).trans
  · exact (natDegree_sub_le _ _).trans (max_le hresponse htarget)
  · intro r hr
    apply (mem_roots hne).mpr
    simpa only [IsRoot, eval_sub, sub_eq_zero] using (Finset.mem_filter.mp hr).2

/-- The per-round soundness budget in the `ClaimReduction` convention. -/
theorem bad_challenge_count_nnreal [Fintype F] (incoming : F) (target response : F[X])
    (htarget : target.natDegree ≤ 2) (hresponse : response.natDegree ≤ 2)
    (hfalse : incoming ≠ target.eval 0 + target.eval 1)
    (hsum : response.eval 0 + response.eval 1 = incoming) :
    ((Finset.univ.filter fun r : F => response.eval r = target.eval r).card : ℝ≥0) ≤
      (2 / Fintype.card F : ℝ≥0) * Fintype.card F := by
  have hcard : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hcard]
  exact_mod_cast bad_challenge_count incoming target response htarget hresponse hfalse hsum

/-- The omitted-p(1) encoding enforces the endpoint check, so no such premise
is needed for Longfellow's actual two-value message. -/
theorem reconstructed_bad_challenge_count [Fintype F] (nodes : Nodes F)
    (incoming p0 p2 : F) (target : F[X]) (htarget : target.natDegree ≤ 2)
    (hfalse : incoming ≠ target.eval 0 + target.eval 1) :
    (Finset.univ.filter fun r : F =>
      coefficients nodes r 1 * (incoming - p0) + coefficients nodes r 0 * p0 +
        coefficients nodes r 2 * p2 = target.eval r).card ≤ 2 := by
  have h := bad_challenge_count incoming target (reconstruct nodes incoming p0 p2)
    htarget (reconstruct_degree nodes incoming p0 p2) hfalse (reconstruct_sum nodes incoming p0 p2)
  simpa only [reconstruct_eval] using h

/-- The reconstructed source message has the same explicit round budget. All
revealed values and committed pads are arbitrary and fixed before the fresh
challenge; their sums supply `p0` and `p2`. -/
theorem reconstructed_bad_challenge_count_nnreal [Fintype F] (nodes : Nodes F)
    (incoming p0 p2 : F) (target : F[X]) (htarget : target.natDegree ≤ 2)
    (hfalse : incoming ≠ target.eval 0 + target.eval 1) :
    ((Finset.univ.filter fun r : F =>
      coefficients nodes r 1 * (incoming - p0) + coefficients nodes r 0 * p0 +
        coefficients nodes r 2 * p2 = target.eval r).card : ℝ≥0) ≤
      (2 / Fintype.card F : ℝ≥0) * Fintype.card F := by
  have h := bad_challenge_count_nnreal incoming target (reconstruct nodes incoming p0 p2)
    htarget (reconstruct_degree nodes incoming p0 p2) hfalse (reconstruct_sum nodes incoming p0 p2)
  simpa only [reconstruct_eval] using h

/-- Semantic connection to the implemented masked recurrence. `hlag` identifies
the verifier-computed interpolation coefficients; it is a deterministic
coefficient identity, not a soundness assumption. -/
theorem transcript_step_eq_eval {PadIdx : Type} {L : ℕ}
    (layout : GKR.Transcript.Layout PadIdx L)
    (tr : GKR.Transcript F PadIdx L layout) (pads : PadIdx → F)
    (l : Fin (L + 1)) (round : Fin (layout.rounds l)) (incoming r : F)
    (nodes : Nodes F) (hlag : tr.lag l round = coefficients nodes r) :
    GKR.Transcript.step layout tr pads l incoming round =
      (reconstruct nodes incoming
        (tr.hp l round 0 + pads (layout.polyPad l round 0))
        (tr.hp l round 1 + pads (layout.polyPad l round 1))).eval r := by
  rw [reconstruct_eval]
  simp only [GKR.Transcript.step, hlag]

end GordieHowe.Sumcheck.Round
