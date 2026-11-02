-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Complete
public import GordieHowe.SPBCS.Salt
public import GordieHowe.Model.ROM.AdaptiveCompleteness
public import GordieHowe.SPBCS.Extraction.CompletenessAdaptive
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.SaltedZKProofQuery

@[expose] public section

/-!
# Adaptive completeness of the spBCS compiler

Completeness in the form of Unruh 2017 (ePrint 2017/398), Definition 5, p. 14 (the statement and
witness chosen by an adversary after querying the oracle, then proved by the honest prover with a
fresh Fiat–Shamir salt), for the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`), paper
`thm:bcs-complete` (2):

- every query of the honest prover carries its salt (`querySalt_strategy`), and its writes read
  only `leaf` and `node` queries, which carry none (`honestWrite_replaceSlice`). So when the
  inputs of salt `σ` are answered by a fresh uniform function `F` and all other inputs by an
  arbitrary oracle `g`, the honest answers are those of the prover with the fixed writes of `g`
  against `F` (`answersW_replaceSlice`);
- the counting of the fixed-statement bound for a general write function
  (`prob_sample_none_or_chOfW_mem_le`) then gives the **fresh-slice bound**
  `ε + overrun + keyCollision (t.size n) k` at every `g` (`prob_not_accepts_prove_replaceSlice_le`);
- `GordieHowe/SPBCS/CompleteNARG.lean` averages it over uniform coins and Merkle salts of the
  honest prover, and the generic theorems of `GordieHowe/Model/ROM/AdaptiveCompleteness.lean` and
  `GordieHowe/Model/QROM/AdaptiveCompleteness.lean` turn that into adaptive completeness with the
  extra term `t / 2^(8kS)` in the ROM (`GordieHowe.SPBCS.complete_rom`) and `2t / 2^(4kS)` in the
  QROM (`GordieHowe.SPBCS.complete_qrom`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open GordieHowe.QROM (replaceSlice)
open scoped ENNReal NNReal

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

variable {M}

/-! ### Fresh slices -/

section FreshSlice

variable [∀ j i, Nonempty ((P j).Challenge i)] (prv : CausalProver P t X) (x : X)
  (σ : FiatShamirSalt kS)

/-- **Every query of a prover carries its Fiat–Shamir salt**: a chain input or a final input
encodes well-formed content with the salt, and a stream point carries it. -/
theorem querySalt_strategy (wrOf : (Query k kN kS L → Out k e) → M.WriteFn) (j : ℕ)
    (ws : List (Out k e)) (h : Query k kN kS L → Out k e) :
    M.querySalt (strategy M prv x σ wrOf j ws h) = some σ := by
  unfold strategy
  split
  · rename_i u _
    cases u with
    | key p r => exact M.querySalt_transcript_encode (wf_roundContent prv x σ (wrOf h) ws p r)
    | xof => rfl
    | fin s => exact M.querySalt_transcript_encode (wf_finalContent prv x σ (wrOf h) ws s)
  · rfl

variable (E : (j : ι) → (M.comp j).Encoder) (ν : M.Pos → MerkleSalt kN)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The honest writes on a fresh slice are those of the oracle off the slice**: the writes read
only `leaf` and `node` queries, which carry no salt. -/
theorem honestWrite_replaceSlice (g F : Query k kN kS L → Out k e) :
    SPBCS.honestWrite (M := M) E ν (replaceSlice M.querySalt σ g F) =
      SPBCS.honestWrite E ν g :=
  SPBCS.honestWrite_congr_oracle E ν fun a ha => by
    simp [replaceSlice, M.querySalt_of_not_isChainQuery ha]

/-- **The honest answers on a fresh slice**: against `g` with the slice of `σ` answered by `F`,
the honest prover's answers are those of the prover with the fixed writes of `g` against `F`. -/
theorem answersW_replaceSlice (g F : Query k kN kS L → Out k e) :
    answersW prv x σ (SPBCS.honestWrite (M := M) E ν)
        (replaceSlice M.querySalt σ g F) =
      answersW prv x σ (fun _ => SPBCS.honestWrite E ν g) F := by
  unfold answersW
  rw [ansList_congr_fun _ _
    (q' := strategy M prv x σ fun _ => SPBCS.honestWrite E ν g)
    (fun i l => by simp only [strategy, honestWrite_replaceSlice]) _]
  exact ansList_congr_oracle _ _ (Dom := fun a => M.querySalt a = some σ)
    (fun i _ l => querySalt_strategy prv x σ _ i l _) (fun _ _ => rfl)
    (fun a ha => by simp [replaceSlice, ha])

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

open Classical in
/-- **The fresh-slice bound of the spBCS compiler**: for every oracle `g`, when the inputs
of the salt `σ` are answered by a fresh uniform function `F` and all other inputs by `g`, the
honest proof of the causal prover `prv`, with any Merkle salts `ν`, is rejected with probability at
most `ε + overrun + keyCollision (t.size n) k` over `F`, where `ε` bounds the probability that the
composite verifier rejects the run of `prv` over uniform challenges. The fixed-statement bound
(`prob_not_accepts_prove_le`) with the oracle off the slice fixed. -/
theorem prob_not_accepts_prove_replaceSlice_le (g : Query k kN kS L → Out k e) {ε : ℝ≥0∞}
    (hε : Pr[ch ← Chs P t : V x (prv.run x ch) ≠ true] ≤ ε) :
    Pr[F ← (Query k kN kS L → Out k e) : ¬ M.Accepts (replaceSlice M.querySalt σ g F) x
        (prove prv x σ E ν (replaceSlice M.querySalt σ g F) Q) Q] ≤
      ε + M.overrun + SPBCS.keyCollision (t.size n) k := by
  refine le_trans (QROM.probUniform_mono fun F hv => ?_)
    ((prob_sample_none_or_chOfW_mem_le prv x σ (fun _ => SPBCS.honestWrite E ν g)
      (fun _ _ _ => rfl) fun ch => V x (prv.run x ch) ≠ true).trans (by gcongr))
  have hans : answers prv x σ E ν (replaceSlice M.querySalt σ g F) =
      answersW prv x σ (fun _ => SPBCS.honestWrite E ν g) F :=
    answersW_replaceSlice prv x σ E ν g F
  by_contra hc
  push Not at hc
  obtain ⟨hs, hV⟩ := hc
  refine hv (accepts_prove prv x σ E ν _ Q (fun c => ?_) ?_)
  · rw [hans]
    exact Option.isSome_iff_ne_none.2 (hs c)
  · rw [honestCh, hans]
    exact hV

open Classical in
/-- **Completeness of the spBCS compiler for a fixed statement, at uniform coins** (paper
`thm:bcs-complete`(2) for a fixed statement, the case `t = 0`): if the composite verifier rejects
the run of the causal prover `prv r` with probability at most `ε` over uniform coins `r` and
uniform challenges (the completeness error of `def:iop-complete`), then over uniform coins and a
uniform oracle the compiled verifier rejects the honest proof, with any Merkle salts `ν` and
Fiat–Shamir salt `σ`, with probability at most `ε + overrun + keyCollision (t.size n) k`. -/
theorem prob_not_accepts_prove_coins_le {R : Type} [Fintype R] [Nonempty R]
    (prv : R → CausalProver P t X) {ε : ℝ≥0∞}
    (hε : Pr[q ← R × Chs P t : V x ((prv q.1).run x q.2) ≠ true] ≤ ε) :
    Pr[q ← R × (Query k kN kS L → Out k e) :
        ¬ M.Accepts q.2 x (prove (prv q.1) x σ E ν q.2 Q) Q] ≤
      ε + M.overrun + SPBCS.keyCollision (t.size n) k := by
  rw [ROM.probUniform_prod_eq_sum]
  refine (ROM.sum_inv_card_mul_le_add fun r =>
    (prob_not_accepts_prove_le (prv r) x σ E ν Q le_rfl).trans_eq (add_assoc _ _ _)).trans ?_
  rw [← ROM.probUniform_prod_eq_sum (fun q : R × Chs P t => V x ((prv q.1).run x q.2) ≠ true),
    add_assoc]
  gcongr

end FreshSlice

end

end GordieHowe.SPBCS
