-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.PublicValue

@[expose] public section

/-!
# A signer that refuses more rings

The signer `S.restrict Ok` refuses the rings `S` refuses and also the rings outside a predicate
`Ok` of the oracle, the ring and the message (`PubSigner.restrict`); it signs as `S` on the rest.
The two anonymity games, against the same adversary (`PubAnonAdversary.restrict`), draw the same
keys, oracles and signature table, and differ only in the rounds whose chosen ring `S` admits
and `Ok` rejects. Identical until bad (`tvDist_pubRun_le`), the advantage against `S` is at most
the advantage against `S.restrict Ok` plus twice the probability of that event
(`advantage_le_restrict_one`, one challenge, where the event is over the proof system's oracle
at the empty history). The ML-DSA ring signer publishing `w₁` uses it with `Ok` the rings of low
defect, which no longer need the check (`MLDSAPublicW1Query.lean`).

- `PubSigner.restrict`, `PubAnonAdversary.restrict`: the signer and the adversary.
- `tvDist_game_restrict_le`: the two experiments `b` are within the sum over the rounds of the
  probability that the selectors differ.
- `tvDist_game_restrict_le_one`, `advantage_le_restrict_one`: with one challenge, the selectors
  differ only where `S` admits the chosen ring and `Ok` rejects it.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {N : ℕ} {RMsg : Type}

/-- **The signer that also refuses the rings outside `Ok`**: `S` with the refusal rule
`S.Admit H R m ∧ Ok H R m`. `Ok` reads only the oracle, the ring and the message, so the rule
stays the same for every signer. -/
noncomputable def PubSigner.restrict (S : PubSigner N RMsg) (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) :
    PubSigner N RMsg :=
  { S with
    Admit := fun H R m => S.Admit H R m ∧ Ok H R m
    instDecAdmit := fun _ _ _ => @instDecidableAnd _ _ _ (Classical.dec _) }

@[simp] theorem PubSigner.restrict_admit (S : PubSigner N RMsg)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) (H : S.Orc)
    (R : RingOf S.PK N) (m : RMsg) : (S.restrict Ok).Admit H R m = (S.Admit H R m ∧ Ok H R m) :=
  rfl

@[simp] theorem PubSigner.restrict_stmt (S : PubSigner N RMsg)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) :
    (S.restrict Ok).stmt = S.stmt := rfl

@[simp] theorem PubSigner.restrict_wit (S : PubSigner N RMsg)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) :
    (S.restrict Ok).wit = S.wit := rfl

/-- Two refusal rules `p` and `p ∧ q` answer differently exactly when `p` holds and `q` fails. -/
theorem ite_some_ne_ite_some_iff {α : Type*} (p q : Prop) {_ : Decidable p}
    {_ : Decidable (p ∧ q)} (x : α) : ((if p then some x else none) ≠ (if p ∧ q then some x else none)) ↔ (p ∧ ¬ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

section Game

variable [DecidableEq RMsg] {S : PubSigner N RMsg} (Ok : S.Orc → RingOf S.PK N → RMsg → Prop)
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {M : SPBCS Mg P S.Stmt k kN kS L e} {n Q : ℕ}

namespace PubAnonAdversary

/-- **The adversary against the restricted signer**: the same challenge set and choices.

Running time: that of the adversary. This running time is argued here, not proved in Lean. -/
def restrict (A : PubAnonAdversary S M n Q) : PubAnonAdversary (S.restrict Ok) M n Q where
  choices := A.choices
  choose := A.choose
  choose_mem := A.choose_mem
  choose_valid := A.choose_valid

@[simp] theorem restrict_choose (A : PubAnonAdversary S M n Q) :
    (A.restrict Ok).choose = A.choose := rfl

variable (A : PubAnonAdversary S M n Q) (E : (j : ι) → (M.comp j).Encoder)
  {V : S.Orc → S.Stmt → FullTr P τ → Bool} (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type}
  [Fintype R] [Nonempty R] (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- **The experiments against `S` and `S.restrict Ok` are identical until the selectors
differ**: the experiment `b` against the two signers are within the average, over the users'
coins, the oracle and the signature table, of the sum over the rounds of the probability that the
two selectors choose differently (`tvDist_pubRun_le`). -/
theorem tvDist_game_restrict_le (b : Bool) :
    PMF.tvDist (A.game E Qs honest b) ((A.restrict Ok).game E Qs honest b) ≤
      ∑ keys, (PMF.uniformOfFintype (Fin n → S.KeyCoins) keys).toReal *
        ∑ H, (PMF.uniformOfFintype S.Orc H).toReal *
          ∑ T, (A.tableLaw H keys b T).toReal *
            ∑ i : Fin Q, selectDiffProb (law := proofLawAt E Qs honest H) (pubOf := S.stmtPub)
              (A.selector keys H b T) ((A.restrict Ok).selector keys H b T)
              (Fin.castLE le_rfl i) := by
  unfold game
  refine (PMF.tvDist_bind_left_le _ _ _).trans (Finset.sum_le_sum fun keys _ =>
    mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  refine (PMF.tvDist_bind_left_le _ _ _).trans (Finset.sum_le_sum fun H _ =>
    mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  refine (PMF.tvDist_bind_left_le _ _ _).trans (Finset.sum_le_sum fun T _ =>
    mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  exact (PMF.tvDist_map_le _ _ _).trans (tvDist_pubRun_le _ _ Q le_rfl)

open Classical in
/-- **With one challenge, the selectors differ only on a bad choice**: the experiments `b`
against `S` and `S.restrict Ok` are within the probability, over the users' coins, the oracle `H`
and the proof system's oracle `h`, that `S` admits the ring of the challenge chosen at the empty
history and `Ok` rejects it. -/
theorem tvDist_game_restrict_le_one (A : PubAnonAdversary S M n 1) (b : Bool) :
    PMF.tvDist (A.game E Qs honest b) ((A.restrict Ok).game E Qs honest b) ≤
      𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, 𝔼 h : Query k kN kS L → Out k e,
        (if S.Admit H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg ∧
            ¬ Ok H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg
          then 1 else 0 : ℝ) := by
  refine (A.tvDist_game_restrict_le Ok E Qs honest b).trans_eq ?_
  rw [← PMF.sum_toReal_uniformOfFintype_mul]
  refine Finset.sum_congr rfl fun keys _ => congrArg _ ?_
  rw [← PMF.sum_toReal_uniformOfFintype_mul]
  refine Finset.sum_congr rfl fun H _ => congrArg _ ?_
  have hsel : ∀ T, ∑ i : Fin 1, selectDiffProb (law := proofLawAt E Qs honest H)
      (pubOf := S.stmtPub) (A.selector keys H b T) ((A.restrict Ok).selector keys H b T)
      (Fin.castLE le_rfl i) =
      𝔼 h : Query k kN kS L → Out k e,
        (if S.Admit H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg ∧
            ¬ Ok H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg
          then 1 else 0 : ℝ) := fun T => by
    rw [Fin.sum_univ_one]
    unfold selectDiffProb
    simp only [Fin.castLE_refl, Fin.val_zero, pubRun, PMF.toOuterMeasure_map_apply]
    rw [PMF.toReal_toOuterMeasure_apply, ← PMF.sum_toReal_uniformOfFintype_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have hiff : A.selector keys H b T 0 h Fin.elim0 ≠ (A.restrict Ok).selector keys H b T 0 h
        Fin.elim0 ↔
        (S.Admit H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg ∧
          ¬ Ok H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg) := by
      unfold selector
      exact ite_some_ne_ite_some_iff _ _ _
    split_ifs with hc hb hb
    · rw [mul_one]
    · exact absurd (hiff.1 hc) hb
    · exact absurd (hiff.2 hb) hc
    · rw [mul_zero]
  simp only [hsel]
  rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

open Classical in
/-- **The advantage against `S` from the advantage against `S.restrict Ok`** with one challenge:
at most the advantage against the restricted signer plus twice the probability, over the users'
coins, the oracle and the proof system's oracle, that `S` admits the chosen ring and `Ok`
rejects it (`tvDist_game_restrict_le_one`, `PMF.abs_toOuterMeasure_sub_le_tvDist`). -/
theorem advantage_le_restrict_one (A : PubAnonAdversary S M n 1)
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof 1 → Prop) :
    A.advantage E Qs honest D ≤ (A.restrict Ok).advantage E Qs honest D +
      2 * 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, 𝔼 h : Query k kN kS L → Out k e,
        (if S.Admit H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg ∧
            ¬ Ok H (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg
          then 1 else 0 : ℝ) := by
  unfold advantage GordieHowe.gameAdvantage GordieHowe.advantage
  have t0 := A.tvDist_game_restrict_le_one Ok E Qs honest false
  have t1 := A.tvDist_game_restrict_le_one Ok E Qs honest true
  change |((A.game E Qs honest false).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal -
    ((A.game E Qs honest true).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal| ≤
      |(((A.restrict Ok).game E Qs honest false).toOuterMeasure
          {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal -
        (((A.restrict Ok).game E Qs honest true).toOuterMeasure
          {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal| + _
  set a0 := ((A.game E Qs honest false).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal
  set a1 := ((A.game E Qs honest true).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal
  set b0 := (((A.restrict Ok).game E Qs honest false).toOuterMeasure
    {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal
  set b1 := (((A.restrict Ok).game E Qs honest true).toOuterMeasure
    {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal
  have h0 : |a0 - b0| ≤ _ := (PMF.abs_toOuterMeasure_sub_le_tvDist (A.game E Qs honest false)
    ((A.restrict Ok).game E Qs honest false) {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).trans t0
  have h1 : |a1 - b1| ≤ _ := (PMF.abs_toOuterMeasure_sub_le_tvDist (A.game E Qs honest true)
    ((A.restrict Ok).game E Qs honest true) {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).trans t1
  have e1 := abs_sub_le a0 b0 a1
  have e2 := abs_sub_le b0 b1 a1
  rw [abs_sub_comm b1 a1] at e2
  linarith

end PubAnonAdversary

end Game

end GordieHowe.Ring
