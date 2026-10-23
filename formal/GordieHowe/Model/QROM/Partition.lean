-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.QueryStep
public import GordieHowe.Model.QROM.FourierCompression

@[expose] public section

/-!
# Partition measurements of the database and one query of the compressed oracle

Chen–Ding–Hsieh–Zhandry ("Post-quantum security of SNARK reductions", CDHZ26, ePrint 2025/2166),
section 5.1, p. 31, measure the compressed oracle's database by a partition `{P(i)}_i` and bound
the commutator of that measurement with one oracle query by the generalized instability of the
partition:

    Definition 5.3. The generalized instability I(P, t) of a database partition P = {P(i)}_i with
    query bound t is the maximum probability that a database D with size less than t moves to
    another partition element within one additional classical query. Formally, we let
      I(P, t) := max_i flip(P(i) → ∪_{j≠i} P(j), t).

    Corollary 5.6. For the purified measurement M := ∑_i P(i)_D ⊗ X^i_B,
      ‖[M, O^(t)_std]‖² ≤ 80 · I(P, t).

This file proves the corresponding bound for CMS19's compressed phase oracle with `t` slots
(`compressedOracle`, `GordieHowe/Model/QROM/Compressed.lean`), with our own constant `24`. A partition is given
by a label `L : DB → Λ` (the parts are its fibres); `instabPart L t` is `I(P, t)`. The purified
measurement applied to `ψ ⊗ |0⟩` is the family `(P_λ ψ)_λ`, so its commutator with a query `O` is
the family `(P_λ O ψ − O P_λ ψ)_λ`, and

    ∑_λ ‖P_λ O ψ − O P_λ ψ‖² ≤ 24 · I(L, t) · ‖ψ‖²    (`sum_norm_labelComm_le`).

The constant differs from CDHZ26's `80` because the oracle differs (their truncated standard
oracle, §4.3, pp. 29–30; ours is CMS19's phase-form `t`-slot oracle `Dec ∘ O0 ∘ Dec` with App. A's
`Dec_x`, p. 47) and the proof is ours. It follows CMS19 Lemma 5.10's block
decomposition (`GordieHowe/Model/QROM/QueryStep.lean`): on each `|x, u, z⟩` the oracle acts by `qMatrix`, whose
off-diagonal entries join only members of one block `{|D₀⟩} ∪ {|D₀ + [x ↦ y]⟩ : y}` of `Dec_x`.

1. For each output `s'`, the family over `λ` has squared norm at most
   `2 (∑_{s : L s ≠ L s'} |M s' s| |ψ s|)²` (`sum_label_sq_le`).
2. Row by row Cauchy–Schwarz inside the block of `s'` bounds the sum by the squared Frobenius norm
   of the entries joining differently labelled members of one block, times `‖ψ‖²`.
3. On one block, with `T` the `y` whose extension `D₀ + [x ↦ y]` is labelled differently from `D₀`,
   those entries have squared norm at most `12 |T| / 2^n` (`block_offLabel_le`): `2 |T| / 2^n` from
   the entries `ρ χ(y)` joining `|D₀⟩`, and `10 |T| / 2^n` from the entries `ρ² β_{w,y}` between
   extensions, of which one end is in `T` (`sum_beta_sq_le`). And `|T| / 2^n ≤ I(L, t)`.

The labels read the adversary's work register as well as the database (`labelProj`), so the
partition may depend on classical data the run holds, such as the output and recorded answers;
the bound holds with `I(L, t)` the largest instability over work-register values. The simulated
query `(I ⊗ H^n) O (I ⊗ H^n)` has the same bound (`sum_norm_labelComm_simQuery_le`).

`simStage_eq_compress_stages` writes the simulated state of a `t`-query algorithm through the runs
of the algorithm with each classical oracle, so two algorithms on the same registers whose runs
agree for every oracle have the same simulated state (used to exchange independent queries).
-/

open Finset GordieHowe.Quantum GordieHowe.IOP
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

/-! ### Generalized instability -/

section Instab

variable {X Y Λ : Type*} [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The generalized instability** `I(P, t)` of the partition of databases by a label `L`
(CDHZ26 Definition 5.3, p. 31): the largest probability, over databases `D` with `|D| < t` and
inputs `x ∉ supp(D)`, that `D + [x ↦ y]` has another label than `D`, for uniform `y`. The
maximum is a supremum in `ℝ≥0∞`. -/
noncomputable def instabPart (L : DB X Y → Λ) (t : ℕ) : ℝ≥0∞ :=
  ⨆ (D : DB X Y) (_ : D.size < t) (x : X) (_ : x ∉ D), Pr[y ← Y : L (D.extend x y) ≠ L D]

variable {L : DB X Y → Λ} {t : ℕ}

theorem le_instabPart {D : DB X Y} (hs : D.size < t) {x : X} (hx : x ∉ D) :
    Pr[y ← Y : L (D.extend x y) ≠ L D] ≤ instabPart L t :=
  le_iSup₂_of_le D hs (le_iSup₂_of_le (f := fun x (_ : x ∉ D) =>
    Pr[y ← Y : L (D.extend x y) ≠ L D]) x hx le_rfl)

theorem instabPart_le {ε : ℝ≥0∞}
    (h : ∀ D : DB X Y, D.size < t → ∀ x ∉ D, Pr[y ← Y : L (D.extend x y) ≠ L D] ≤ ε) :
    instabPart L t ≤ ε :=
  iSup₂_le fun D hs => iSup₂_le fun x hx => h D hs x hx

theorem instabPart_le_one : instabPart L t ≤ 1 :=
  instabPart_le fun _ _ _ _ => probUniform_le_one _

/-- **The partition into a property and its complement** has the instability of the property
(CDHZ26 Remark 5.5, p. 31: the generalized instability recovers CMS19's). -/
theorem instabPart_mem (P : Set (DB X Y)) : instabPart (· ∈ P) t = instab P t := by
  refine le_antisymm (instabPart_le fun D hs x hx => ?_) (max_le ?_ ?_)
  · by_cases hD : D ∈ P
    · refine (probUniform_mono fun y hy => ?_).trans (le_flipProb (Q := Pᶜ) hD hs hx |>.trans
        flipProb_to_compl_le_instab)
      exact fun h => hy (propext ⟨fun _ => hD, fun _ => h⟩)
    · refine (probUniform_mono fun y hy => ?_).trans (le_flipProb (P := Pᶜ) (Q := P) hD hs hx |>.trans
        flipProb_compl_le_instab)
      by_contra h
      exact hy (propext ⟨fun h' => absurd h' h, fun h' => absurd h' hD⟩)
  · refine flipProb_le fun D hD hs x hx => (probUniform_mono fun y hy => ?_).trans
      (le_instabPart hs hx)
    intro h
    exact hD (h ▸ hy)
  · refine flipProb_le fun D hD hs x hx => (probUniform_mono fun y hy => ?_).trans
      (le_instabPart hs hx)
    intro h
    exact hy (h ▸ hD)

/-- **A label that changes only where another changes is at most as unstable.** -/
theorem instabPart_le_instabPart {Λ' : Type*} {L' : DB X Y → Λ'}
    (h : ∀ D D', L D ≠ L D' → L' D ≠ L' D') : instabPart L t ≤ instabPart L' t :=
  instabPart_le fun _ hs _ hx => (probUniform_mono fun _ hy => h _ _ hy).trans (le_instabPart hs hx)

end Instab

/-! ### The label sum at one output -/

section LabelSum

variable {κ Λ : Type*} [Fintype κ] [Fintype Λ] [DecidableEq Λ]

/-- **The commutator of a label measurement at one output**: for coefficients `c s` and a label
`ℓ`, the family over labels `i` of `∑_s c s ([ℓ s' = i] − [ℓ s = i])` has squared norm at most
`2 (∑_{s : ℓ s ≠ ℓ s'} |c s|)²`. The part `i = ℓ s'` is `∑_{ℓ s ≠ ℓ s'} c s`; the others are
`−∑_{ℓ s = i} c s` for `i ≠ ℓ s'`. -/
theorem sum_label_sq_le (ℓ : κ → Λ) (s' : κ) (c : κ → ℂ) :
    ∑ i, ‖∑ s, c s * ((if ℓ s' = i then 1 else 0) - (if ℓ s = i then 1 else 0))‖ ^ 2 ≤
      2 * (∑ s, if ℓ s ≠ ℓ s' then ‖c s‖ else 0) ^ 2 := by
  set N : ℝ := ∑ s, if ℓ s ≠ ℓ s' then ‖c s‖ else 0
  set g : Λ → ℝ := fun i => ∑ s, if ℓ s = i ∧ ℓ s ≠ ℓ s' then ‖c s‖ else 0
  have hg0 : ∀ i, 0 ≤ g i := fun i => Finset.sum_nonneg fun s _ => by split_ifs <;> positivity
  have hgN : ∑ i, g i = N := by
    simp only [g, N]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : ℓ s ≠ ℓ s'
    · simp [hs]
    · simp [hs]
  have hterm : ∀ i, ‖∑ s, c s * ((if ℓ s' = i then 1 else 0) - (if ℓ s = i then 1 else 0))‖ ≤
      if ℓ s' = i then N else g i := by
    intro i
    by_cases h : ℓ s' = i
    · refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)).trans_eq (if_pos h).symm
      subst h
      by_cases hs : ℓ s = ℓ s' <;> simp [hs]
    · refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)).trans_eq (if_neg h).symm
      by_cases hs : ℓ s = i
      · have hi : i ≠ ℓ s' := fun e => h e.symm
        simp [h, hs, hi]
      · simp [h, hs]
  have hN : 0 ≤ N := hgN ▸ Finset.sum_nonneg fun i _ => hg0 i
  calc ∑ i, ‖∑ s, c s * ((if ℓ s' = i then 1 else 0) - (if ℓ s = i then 1 else 0))‖ ^ 2
      ≤ ∑ i, (if ℓ s' = i then N else g i) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hterm i) 2
    _ ≤ ∑ i, ((if ℓ s' = i then N else 0) ^ 2 + g i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          split_ifs
          · nlinarith [hg0 i]
          · simp
    _ = N ^ 2 + ∑ i, g i ^ 2 := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single (ℓ s') (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
        simp
    _ ≤ N ^ 2 + (∑ i, g i) ^ 2 :=
        add_le_add le_rfl (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hg0 i)
    _ = 2 * N ^ 2 := by rw [hgN]; ring

end LabelSum

/-! ### The entries between differently labelled members of one block -/

section BlockLabel

variable {Y : Type} {Λ : Type*} [Fintype Y] [DecidableEq Λ] {χ : Y → ℝ} {ρ : ℝ}

/-- **The off-label entries of one block** (step 3 of the module docstring): on the block
`{|D₀⟩} ∪ {|D₀ + [x ↦ y]⟩ : y}` with labels `ℓ`, the entries `−w(o') w(o) (φ(o') + φ(o) − 1)` of
`Dec_x Φ_u Dec_x` (`u ≠ 0^n`) between members with different labels have squared sum at most
`12 |T| / 2^n`, where `T` is the set of `y` with `ℓ(some y) ≠ ℓ(none)`. -/
theorem block_offLabel_le (hρ : ρ * ρ * Fintype.card Y = 1) (hχ : ∀ y, χ y * χ y = 1)
    (hsum : ∑ y, χ y = 0) (ℓ : Option Y → Λ) :
    ∑ o', ∑ o, (if ℓ o ≠ ℓ o' then
        (blockW ρ o' * blockW ρ o * (blockΦ χ o' + blockΦ χ o - 1)) ^ 2 else 0) ≤
      12 * (((univ.filter fun y => ℓ (some y) ≠ ℓ none).card : ℝ) / Fintype.card Y) := by
  set aT : Y → ℝ := fun y => if ℓ (some y) ≠ ℓ none then 1 else 0
  have haT : ∀ y, 0 ≤ aT y := fun y => by simp only [aT]; split_ifs <;> norm_num
  have hcard : (((univ.filter fun y => ℓ (some y) ≠ ℓ none).card : ℕ) : ℝ) = ∑ y, aT y := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hN : (Fintype.card Y : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hρ
    exact zero_ne_one hρ
  have hρρ : ρ * ρ = 1 / Fintype.card Y := by
    field_simp
    linarith
  have hnone : ∀ w, (if ℓ (some w) ≠ ℓ none then
      (blockW ρ (none : Option Y) * blockW ρ (some w) * (blockΦ χ (none : Option Y) + blockΦ χ (some w) - 1)) ^ 2 else 0) =
      aT w * (ρ * ρ) := fun w => by
    simp only [aT, blockW, blockΦ]
    split_ifs
    · have := hχ w
      linear_combination (ρ * ρ) * this
    · simp
  have hnone' : ∀ y, (if ℓ none ≠ ℓ (some y) then
      (blockW ρ (some y) * blockW ρ (none : Option Y) * (blockΦ χ (some y) + blockΦ χ (none : Option Y) - 1)) ^ 2 else 0) =
      aT y * (ρ * ρ) := fun y => by
    simp only [aT, blockW, blockΦ, ne_comm (a := ℓ none)]
    split_ifs
    · have := hχ y
      linear_combination (ρ * ρ) * this
    · simp
  have hsome : ∀ y w, (if ℓ (some w) ≠ ℓ (some y) then
      (blockW ρ (some y) * blockW ρ (some w) * (blockΦ χ (some y) + blockΦ χ (some w) - 1)) ^ 2
      else 0) ≤ (aT y + aT w) * ((ρ * ρ) ^ 2 * (χ w + χ y - 1) ^ 2) := fun y w => by
    have hpos : 0 ≤ (ρ * ρ) ^ 2 * (χ w + χ y - 1) ^ 2 := by positivity
    simp only [blockW, blockΦ]
    split_ifs with h
    · have h1 : 1 ≤ aT y + aT w := by
        simp only [aT]
        by_cases hy : ℓ (some y) = ℓ none
        · have hw : ℓ (some w) ≠ ℓ none := fun hw => h (hw.trans hy.symm)
          simp [hy, hw]
        · have := haT w
          simp only [ne_eq, hy, not_false_eq_true, if_true]
          linarith
      calc (-ρ * -ρ * (χ y + χ w - 1)) ^ 2 = (ρ * ρ) ^ 2 * (χ w + χ y - 1) ^ 2 := by ring
        _ ≤ (aT y + aT w) * ((ρ * ρ) ^ 2 * (χ w + χ y - 1) ^ 2) := le_mul_of_one_le_left hpos h1
    · exact mul_nonneg (add_nonneg (haT y) (haT w)) hpos
  have hβ : ∀ y, ∑ w, (χ w + χ y - 1) ^ 2 ≤ 5 * (Fintype.card Y : ℝ) := fun y =>
    sum_beta_sq_le hχ hsum y
  have hβ' : ∀ w, ∑ y, (χ w + χ y - 1) ^ 2 ≤ 5 * (Fintype.card Y : ℝ) := fun w => by
    simp_rw [add_comm (χ w)]
    exact sum_beta_sq_le hχ hsum w
  set A := ∑ y, aT y
  have hA : 0 ≤ A := Finset.sum_nonneg fun y _ => haT y
  have hss : ∑ y, ∑ w, (aT y + aT w) * ((ρ * ρ) ^ 2 * (χ w + χ y - 1) ^ 2) ≤
      10 * (A * (ρ * ρ)) := by
    have hsplit : ∑ y, ∑ w, (aT y + aT w) * ((ρ * ρ) ^ 2 * (χ w + χ y - 1) ^ 2) =
        (ρ * ρ) ^ 2 * (∑ y, aT y * ∑ w, (χ w + χ y - 1) ^ 2) +
          (ρ * ρ) ^ 2 * (∑ w, aT w * ∑ y, (χ w + χ y - 1) ^ 2) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => by ring
    have h1 : ∑ y, aT y * ∑ w, (χ w + χ y - 1) ^ 2 ≤ A * (5 * Fintype.card Y) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hβ y) (haT y)
    have h2 : ∑ w, aT w * ∑ y, (χ w + χ y - 1) ^ 2 ≤ A * (5 * Fintype.card Y) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hβ' w) (haT w)
    have hρ2 : 0 ≤ (ρ * ρ) ^ 2 := by positivity
    rw [hsplit]
    calc (ρ * ρ) ^ 2 * (∑ y, aT y * ∑ w, (χ w + χ y - 1) ^ 2) +
          (ρ * ρ) ^ 2 * (∑ w, aT w * ∑ y, (χ w + χ y - 1) ^ 2)
        ≤ (ρ * ρ) ^ 2 * (A * (5 * Fintype.card Y)) + (ρ * ρ) ^ 2 * (A * (5 * Fintype.card Y)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hρ2) (mul_le_mul_of_nonneg_left h2 hρ2)
      _ = 10 * (A * (ρ * ρ)) := by
          have : (ρ * ρ) ^ 2 * Fintype.card Y = ρ * ρ := by
            rw [sq, mul_assoc, hρ, mul_one]
          linear_combination (10 * A) * this
  rw [Fintype.sum_option, Fintype.sum_option]
  simp_rw [Fintype.sum_option]
  simp only [ne_eq, not_true_eq_false, if_false, zero_add]
  rw [hcard]
  calc ∑ w, (if ¬ℓ (some w) = ℓ none then
          (blockW ρ (none : Option Y) * blockW ρ (some w) * (blockΦ χ (none : Option Y) + blockΦ χ (some w) - 1)) ^ 2 else 0) +
        ∑ y, ((if ¬ℓ none = ℓ (some y) then
          (blockW ρ (some y) * blockW ρ (none : Option Y) * (blockΦ χ (some y) + blockΦ χ (none : Option Y) - 1)) ^ 2 else 0) +
          ∑ w, (if ¬ℓ (some w) = ℓ (some y) then
            (blockW ρ (some y) * blockW ρ (some w) * (blockΦ χ (some y) + blockΦ χ (some w) - 1)) ^ 2
            else 0))
      ≤ A * (ρ * ρ) + (A * (ρ * ρ) + 10 * (A * (ρ * ρ))) := by
        rw [Finset.sum_add_distrib]
        refine add_le_add (le_of_eq ?_) (add_le_add (le_of_eq ?_) ?_)
        · simp_rw [← ne_eq, hnone, ← Finset.sum_mul]
          rfl
        · simp_rw [← ne_eq, hnone', ← Finset.sum_mul]
          rfl
        · simp_rw [← ne_eq]
          exact (Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun w _ => hsome y w).trans hss
    _ = 12 * (A / Fintype.card Y) := by
        rw [hρρ]
        ring

end BlockLabel

/-! ### One query on one `|x, u, z⟩` -/

section Fiber

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ} {B : Type}
  (e : BitStr I J ≃ B) {t : ℕ} {Λ : Type*} [DecidableEq Λ]

/-- The signs `(−1)^{u·y}` of a nonzero `u` sum to `0` over `y`. -/
theorem sum_signR_dot_eq_zero {u : BitStr I J} (hu : u ≠ 0) : ∑ y, signR (u.dot y) = 0 := by
  have h := sum_signOf_dot u
  rw [if_neg hu] at h
  have : ∑ y, (signR (u.dot y) : ℂ) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [BitStr.dot_comm u y, signOf_eq]
  exact_mod_cast this

omit [DecidableEq I] [DecidableEq J] in
/-- The signs `(−1)^{0·y}` are `1`. -/
theorem signR_zero_dot (y : BitStr I J) : signR ((0 : BitStr I J).dot y) = 1 := by
  simp only [BitStr.dot_comm 0 y, BitStr.dot_zero, signR, ZMod.val_zero, pow_zero]

open Classical in
/-- The fraction of the one-entry extensions of `D₀` with another label than `D₀` is at most the
generalized instability. -/
theorem card_filter_div_le_instabPart [Fintype B] [Nonempty B] (ℓ : DB (Bits m) B → Λ)
    {x : Bits m} {D₀ : DB (Bits m) B} (hsz : D₀.size < t) (hx : x ∉ D₀) :
    ((univ.filter fun y : BitStr I J => ℓ (DB.extend D₀ x (e y)) ≠ ℓ D₀).card : ℝ) /
      Fintype.card (BitStr I J) ≤ (instabPart ℓ t).toReal := by
  have h := le_instabPart (L := ℓ) hsz hx
  rw [probUniform_eq_card_div] at h
  have hcard : (univ.filter fun b : B => ℓ (DB.extend D₀ x b) ≠ ℓ D₀).card =
      (univ.filter fun y : BitStr I J => ℓ (DB.extend D₀ x (e y)) ≠ ℓ D₀).card := by
    refine Finset.card_bij' (fun b _ => e.symm b) (fun y _ => e y) ?_ ?_ ?_ ?_ <;> simp
  have hB : Fintype.card B = Fintype.card (BitStr I J) := (Fintype.card_congr e).symm
  rw [hcard, hB] at h
  have hne : instabPart ℓ t ≠ ⊤ := (instabPart_le_one.trans_lt ENNReal.one_lt_top).ne
  have := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this

/-- The off-diagonal entries of `Dec_x Φ_u Dec_x` join only members of one block of `Dec_x`. -/
theorem qMatrix_eq_zero_of_decBlock {x : Bits m} {u : BitStr I J} {s' s : Slots I J m t}
    (hne : s' ≠ s) (h : decBlock e t x s' ≠ decBlock e t x s ∨ decBlock e t x s = none) :
    qMatrix e x u s' s = 0 := by
  classical
  rw [qMatrix, reflKernel_sandwich _ _ _ hne]
  rcases h with h | h
  · rw [if_neg h, neg_zero]
  · have hw : decAmp e t x s = 0 := by simp [decAmp, h]
    split_ifs <;> simp [hw]

open Classical in
/-- **An off-diagonal entry on one block**: between distinct members `o' ≠ o` of the block of
`D₀`, `|⟨o'| Dec_x Φ_u Dec_x |o⟩|² ≤ (w(o') w(o) (φ(o') + φ(o) − 1))²` with `w = blockW`,
`φ = blockΦ` of `χ(y) = (−1)^{u·y}`; equality for `u ≠ 0^n`, and the entry is `0` for `u = 0^n`
(`reflKernel_sandwich`). -/
theorem norm_qMatrix_blockSlot_sq_le {x : Bits m} {D₀ : DB (Bits m) B} (hx : x ∉ D₀)
    (hsz : D₀.size < t) (u : BitStr I J) {o' o : Option (BitStr I J)} (hne : o' ≠ o) :
    ‖qMatrix e x u (blockSlot e t x D₀ o') (blockSlot e t x D₀ o)‖ ^ 2 ≤
      if u = 0 then 0 else (blockW (invSqrtCardR I J) o' * blockW (invSqrtCardR I J) o *
        (blockΦ (fun y => signR (u.dot y)) o' + blockΦ (fun y => signR (u.dot y)) o - 1)) ^ 2 := by
  set g := blockSlot e t x D₀
  set ρ := invSqrtCardR I J
  set χ : BitStr I J → ℝ := fun y => signR (u.dot y)
  set φ : Slots I J m t → ℂ := fun k => dbPhase e u x (slotsDB e k)
  have hρ : ρ * ρ * Fintype.card (BitStr I J) = 1 := invSqrtCardR_sq_mul_card
  have hblk : ∀ o, decBlock e t x (g o) = some D₀ := decBlock_blockSlot e hx hsz
  have hwg : ∀ o, decAmp e t x (g o) = blockW ρ o := decAmp_blockSlot e hx hsz
  have hφg : ∀ o, φ (g o) = ((blockΦ χ o : ℝ) : ℂ) := dbPhase_blockSlot e hx hsz u
  set c : ℂ := ∑ k, (if decBlock e t x k = some D₀ then
    ((decAmp e t x k ^ 2 : ℝ) : ℂ) * φ k else 0)
  have hc : c = ∑ o'', ((blockW ρ o'' ^ 2 * blockΦ χ o'' : ℝ) : ℂ) := by
    simp only [c]
    rw [sum_block e hx hsz (fun k => ((decAmp e t x k ^ 2 : ℝ) : ℂ) * φ k)]
    refine Finset.sum_congr rfl fun o'' _ => ?_
    rw [hwg, hφg]
    push_cast
    ring
  have hq : qMatrix e x u (g o') (g o) =
      -(((blockW ρ o' * blockW ρ o : ℝ) : ℂ) * (((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - c)) := by
    rw [qMatrix, reflKernel_sandwich _ _ _ ((blockSlot_injective e hx hsz).ne hne), hblk, hblk,
      if_pos rfl, hwg, hwg]
    change -(((blockW ρ o' * blockW ρ o : ℝ) : ℂ) * (φ (g o') + φ (g o) - c)) = _
    rw [hφg, hφg]
    push_cast
    ring
  rw [hq, norm_neg]
  by_cases hu : u = 0
  · have hχ1 : ∀ y, χ y = 1 := fun y => by
      rw [show χ y = signR (u.dot y) from rfl, hu, signR_zero_dot]
    have hc2 : c = 2 := by
      rw [hc, Fintype.sum_option]
      simp only [blockW, blockΦ, hχ1]
      push_cast
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : ((ρ : ℂ) * ρ * Fintype.card (BitStr I J)) = 1 := by exact_mod_cast hρ
      linear_combination this
    have hzero : ((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - c = 0 := by
      rw [hc2]
      cases o' <;> cases o <;> simp [blockΦ, hχ1] <;> norm_num
    rw [hzero, mul_zero, norm_zero, if_pos hu]
    norm_num
  · have hsum : ∑ y, χ y = 0 := sum_signR_dot_eq_zero hu
    have hc1 : c = 1 := by
      rw [hc, Fintype.sum_option]
      simp only [blockW, blockΦ]
      push_cast
      rw [← Finset.mul_sum]
      have : ∑ y, (χ y : ℂ) = 0 := by exact_mod_cast hsum
      rw [this]
      ring
    rw [hc1, if_neg hu]
    have : ((blockW ρ o' * blockW ρ o : ℝ) : ℂ) * (((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - 1) =
        ((blockW ρ o' * blockW ρ o * (blockΦ χ o' + blockΦ χ o - 1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]

open Classical in
/-- **The squared off-label entries of one block** are at most `12 I(L, t)`: the entries of
`Dec_x Φ_u Dec_x` between members of the block of `D₀` with different labels
(`block_offLabel_le`, `card_filter_div_le_instabPart`). -/
theorem block_offLabel_qMatrix_le [Fintype B] [Nonempty B] (ℓ : DB (Bits m) B → Λ)
    {x : Bits m} {D₀ : DB (Bits m) B} (hx : x ∉ D₀) (hsz : D₀.size < t) (u : BitStr I J) :
    ∑ o', ∑ o, (if ℓ (blockDB e x D₀ o) ≠ ℓ (blockDB e x D₀ o') then
      ‖qMatrix e x u (blockSlot e t x D₀ o') (blockSlot e t x D₀ o)‖ ^ 2 else 0) ≤
      12 * (instabPart ℓ t).toReal := by
  set ρ := invSqrtCardR I J
  set χ : BitStr I J → ℝ := fun y => signR (u.dot y)
  have hρ : ρ * ρ * Fintype.card (BitStr I J) = 1 := invSqrtCardR_sq_mul_card
  have hχ : ∀ y, χ y * χ y = 1 := fun y => signR_mul_self _
  by_cases hu : u = 0
  · -- `u = 0^n`: every off-diagonal entry vanishes
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun o' _ => Finset.sum_eq_zero fun o _ => ?_))
      (by positivity)
    split_ifs with h
    · have h0 := norm_qMatrix_blockSlot_sq_le e hx hsz u (o' := o') (o := o) fun h' => h (h' ▸ rfl)
      rw [if_pos hu] at h0
      exact le_antisymm h0 (sq_nonneg _)
    · rfl
  have hle : ∀ o' o, (if ℓ (blockDB e x D₀ o) ≠ ℓ (blockDB e x D₀ o') then
      ‖qMatrix e x u (blockSlot e t x D₀ o') (blockSlot e t x D₀ o)‖ ^ 2 else 0) ≤
      (if ℓ (blockDB e x D₀ o) ≠ ℓ (blockDB e x D₀ o') then
        (blockW ρ o' * blockW ρ o * (blockΦ χ o' + blockΦ χ o - 1)) ^ 2 else 0) := fun o' o => by
    split_ifs with h
    · have h0 := norm_qMatrix_blockSlot_sq_le e hx hsz u (o' := o') (o := o) fun h' => h (h' ▸ rfl)
      rwa [if_neg hu] at h0
    · exact le_rfl
  have hsum : ∑ y, χ y = 0 := sum_signR_dot_eq_zero hu
  refine (Finset.sum_le_sum fun o' _ => Finset.sum_le_sum fun o _ => hle o' o).trans ?_
  refine (block_offLabel_le hρ hχ hsum (fun o => ℓ (blockDB e x D₀ o))).trans ?_
  gcongr
  exact card_filter_div_le_instabPart e ℓ hsz hx


open Classical in
/-- **One query on one `|x, u, z⟩` commutes with a label measurement up to `24 I(L, t)`**: for
the matrix `qMatrix e x u` of `Dec_x Φ_u Dec_x` on the database register and a label `ℓ` of
databases, the family over labels `i` of `P_i M α − M P_i α` has squared norm at most
`24 I(ℓ, t) ‖α‖²` (module docstring, steps 1–3). -/
theorem fiber_labelComm_le [Fintype B] [Nonempty B] [Fintype Λ] (x : Bits m) (u : BitStr I J)
    (ℓ : DB (Bits m) B → Λ) (α : Slots I J m t → ℂ) :
    ∑ i, ∑ s', ‖∑ s, qMatrix e x u s' s * α s *
        ((if ℓ (slotsDB e s') = i then 1 else 0) - (if ℓ (slotsDB e s) = i then 1 else 0))‖ ^ 2 ≤
      24 * (instabPart ℓ t).toReal * ∑ s, ‖α s‖ ^ 2 := by
  set blk := decBlock e t x
  set κ := (instabPart ℓ t).toReal
  set lab : Slots I J m t → Λ := fun s => ℓ (slotsDB e s)
  set E : Slots I J m t → Slots I J m t → ℝ := fun s' s =>
    if lab s ≠ lab s' then ‖qMatrix e x u s' s‖ else 0
  have hE0 : ∀ s' s, 0 ≤ E s' s := fun s' s => by simp only [E]; split_ifs <;> positivity
  have hEblk : ∀ s' s, (blk s ≠ blk s' ∨ blk s' = none) → E s' s = 0 := by
    intro s' s h
    simp only [E]
    split_ifs with hl
    · have hne : s' ≠ s := fun h' => hl (h' ▸ rfl)
      rw [qMatrix_eq_zero_of_decBlock e hne ?_, norm_zero]
      rcases h with h | h
      · exact Or.inl (Ne.symm h)
      · by_cases hb : blk s = blk s'
        · exact Or.inr (hb.trans h)
        · exact Or.inl (Ne.symm hb)
    · rfl
  -- step 1: the label sum at each output
  have h1 : ∀ s', ∑ i, ‖∑ s, qMatrix e x u s' s * α s *
      ((if lab s' = i then 1 else 0) - (if lab s = i then 1 else 0))‖ ^ 2 ≤
      2 * (∑ s, E s' s * ‖α s‖) ^ 2 := fun s' => by
    refine (sum_label_sq_le lab s' fun s => qMatrix e x u s' s * α s).trans_eq ?_
    congr 2
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [E, norm_mul]
    split_ifs <;> simp
  -- step 2: Cauchy–Schwarz inside the block of the output
  set a : Option (DB (Bits m) B) → ℝ := fun β => ∑ s, (if blk s = β then ‖α s‖ ^ 2 else 0)
  have h2 : ∀ s', (∑ s, E s' s * ‖α s‖) ^ 2 ≤ (∑ s, E s' s ^ 2) * a (blk s') := fun s' => by
    have hrw : ∑ s, E s' s * ‖α s‖ = ∑ s, E s' s * (if blk s = blk s' then ‖α s‖ else 0) :=
      Finset.sum_congr rfl fun s _ => by
        by_cases hb : blk s = blk s'
        · rw [if_pos hb]
        · rw [if_neg hb, hEblk s' s (Or.inl hb), zero_mul, zero_mul]
    rw [hrw]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  -- step 3: the off-label entries of one block
  have h3 : ∀ β, ∑ s', (if blk s' = β then ∑ s, E s' s ^ 2 else 0) ≤ 12 * κ := by
    intro β
    cases β with
    | none =>
      refine le_trans (le_of_eq (Finset.sum_eq_zero fun s' _ => ?_)) (by positivity)
      split_ifs with hb
      · exact Finset.sum_eq_zero fun s _ => by rw [hEblk s' s (Or.inr hb)]; simp
      · rfl
    | some D₀ =>
      by_cases hne : ∃ s, blk s = some D₀
      · obtain ⟨s₀, hs₀⟩ := hne
        obtain ⟨hx, hsz⟩ := decBlock_eq_some e hs₀
        set g := blockSlot e t x D₀
        have hlab : ∀ o, lab (g o) = ℓ (blockDB e x D₀ o) := fun o => by
          simp only [lab, g, slotsDB_blockSlot e hx hsz]
        have hinner : ∀ s', blk s' = some D₀ →
            ∑ s, E s' s ^ 2 = ∑ o, E s' (g o) ^ 2 := fun s' hs' => by
          rw [← sum_block e hx hsz (fun s => E s' s ^ 2)]
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs with hb
          · rfl
          · rw [hEblk s' s (Or.inl fun h => hb (h.trans hs')), sq, mul_zero]
        calc ∑ s', (if blk s' = some D₀ then ∑ s, E s' s ^ 2 else 0)
            = ∑ s', (if blk s' = some D₀ then ∑ o, E s' (g o) ^ 2 else 0) :=
              Finset.sum_congr rfl fun s' _ => by
                split_ifs with hb
                · exact hinner s' hb
                · rfl
          _ = ∑ o', ∑ o, E (g o') (g o) ^ 2 := sum_block e hx hsz (fun s' => ∑ o, E s' (g o) ^ 2)
          _ = ∑ o', ∑ o, (if ℓ (blockDB e x D₀ o) ≠ ℓ (blockDB e x D₀ o') then
                ‖qMatrix e x u (g o') (g o)‖ ^ 2 else 0) :=
              Finset.sum_congr rfl fun o' _ => Finset.sum_congr rfl fun o _ => by
                simp only [E, hlab]
                split_ifs <;> simp
          _ ≤ 12 * κ := block_offLabel_qMatrix_le e ℓ hx hsz u
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun s' _ => ?_)) (by positivity)
        rw [if_neg fun h => hne ⟨s', h⟩]
  -- assembly: group the outputs by blocks
  have hfib : ∀ G : Slots I J m t → ℝ,
      ∑ s, G s = ∑ β ∈ univ.image blk, ∑ s, (if blk s = β then G s else 0) := by
    intro G
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image blk) (g := blk)
      (fun s _ => Finset.mem_image_of_mem _ (Finset.mem_univ s)) G]
    simp_rw [Finset.sum_filter]
  have ha0 : ∀ β, 0 ≤ a β := fun β => Finset.sum_nonneg fun s _ => by split_ifs <;> positivity
  calc ∑ i, ∑ s', ‖∑ s, qMatrix e x u s' s * α s *
        ((if ℓ (slotsDB e s') = i then 1 else 0) - (if ℓ (slotsDB e s) = i then 1 else 0))‖ ^ 2
      = ∑ s', ∑ i, ‖∑ s, qMatrix e x u s' s * α s *
        ((if lab s' = i then 1 else 0) - (if lab s = i then 1 else 0))‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ s', 2 * ((∑ s, E s' s ^ 2) * a (blk s')) :=
        Finset.sum_le_sum fun s' _ => (h1 s').trans (by gcongr; exact h2 s')
    _ = ∑ β ∈ univ.image blk, 2 * (a β * ∑ s', (if blk s' = β then ∑ s, E s' s ^ 2 else 0)) := by
        rw [hfib]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        split_ifs with hb
        · rw [hb]
          ring
        · simp
    _ ≤ ∑ β ∈ univ.image blk, 2 * (a β * (12 * κ)) :=
        Finset.sum_le_sum fun β _ => by gcongr; exacts [h3 β]
    _ = 24 * κ * ∑ β ∈ univ.image blk, a β := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => by ring
    _ = 24 * κ * ∑ s, ‖α s‖ ^ 2 := by
        rw [hfib (fun s => ‖α s‖ ^ 2)]

end Fiber

/-! ### The label measurement and one query -/

section Query

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ} {B : Type}
  (e : BitStr I J ≃ B) (W : Type) [Fintype W] [DecidableEq W] (t : ℕ) {Λ : Type*}
  [DecidableEq Λ]

/-- **The projector onto a label** `P_i`: the basis states `|x, u, z, D⟩` whose label
`L z D` is `i`, where `L` reads the adversary's work register `z` and the database `D` the slots
hold. The family `(P_i)_i` is a projective measurement (`sum_norm_labelProj_sq`); applied to
`ψ ⊗ |0⟩`, CDHZ26's purified measurement `∑_i P(i) ⊗ X^i` (Corollary 5.6, p. 31) gives the family
`(P_i ψ)_i`. -/
noncomputable def labelProj (L : W → DB (Bits m) B → Λ) (i : Λ) :
    QState (SimRegister W I J m t) →L[ℂ] QState (SimRegister W I J m t) :=
  mask {b | L b.1.1 (slotsDB e b.2) = i}

variable {e W t}

omit [DecidableEq W] in
theorem labelProj_apply (L : W → DB (Bits m) B → Λ) (i : Λ) (v : QState (SimRegister W I J m t))
    (b : SimRegister W I J m t) :
    labelProj e W t L i v b = if L b.1.1 (slotsDB e b.2) = i then v b else 0 := by
  rw [labelProj, mask_apply]
  by_cases h : L b.1.1 (slotsDB e b.2) = i
  · rw [Set.indicator_of_mem (show b ∈ {b | L b.1.1 (slotsDB e b.2) = i} from h), if_pos h]
  · rw [Set.indicator_of_notMem (show b ∉ {b | L b.1.1 (slotsDB e b.2) = i} from h), if_neg h]

omit [DecidableEq W] in
/-- **The label measurement is a projective measurement**: `∑_i ‖P_i ψ‖² = ‖ψ‖²`. -/
theorem sum_norm_labelProj_sq [Fintype Λ] (L : W → DB (Bits m) B → Λ)
    (v : QState (SimRegister W I J m t)) :
    ∑ i, ‖labelProj e W t L i v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp_rw [EuclideanSpace.norm_sq_eq, labelProj_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (L b.1.1 (slotsDB e b.2)) (fun i _ hi => by simp [Ne.symm hi])
    (by simp)]
  simp

/-- **One query of the compressed oracle commutes with a label measurement up to
`24 I(L, t)`** (CDHZ26 Corollary 5.6, p. 31, for CMS19's compressed phase oracle with `t` slots,
with our constant `24`; module docstring): if every work-register value `z` has
`I(L z, t) ≤ κ`, then `∑_i ‖P_i O ψ − O P_i ψ‖² ≤ 24 κ ‖ψ‖²`. -/
theorem sum_norm_labelComm_le [Fintype B] [Nonempty B] [Fintype Λ] (L : W → DB (Bits m) B → Λ)
    {κ : ℝ} (hκ : ∀ z, (instabPart (L z) t).toReal ≤ κ) (v : QState (SimRegister W I J m t)) :
    ∑ i, ‖labelProj e W t L i (compressedOracle e W t v) -
        compressedOracle e W t (labelProj e W t L i v)‖ ^ 2 ≤ 24 * κ * ‖v‖ ^ 2 := by
  have hcomp : ∀ i (r : QueryReg W 1 (Bits m) (BitStr I J)) (s' : Slots I J m t),
      (labelProj e W t L i (compressedOracle e W t v) -
        compressedOracle e W t (labelProj e W t L i v)) (r, s') =
      ∑ s, qMatrix e (qIn r) (qAns r) s' s * v (r, s) *
        ((if L r.1 (slotsDB e s') = i then 1 else 0) - (if L r.1 (slotsDB e s) = i then 1 else 0)) := by
    intro i r s'
    rw [PiLp.sub_apply, labelProj_apply, compressedOracle_apply, compressedOracle_apply]
    simp only [labelProj_apply]
    by_cases h : L r.1 (slotsDB e s') = i
    · rw [if_pos h, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [if_pos h]
      split_ifs <;> ring
    · rw [if_neg h, zero_sub, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [if_neg h]
      split_ifs <;> ring
  calc ∑ i, ‖labelProj e W t L i (compressedOracle e W t v) -
        compressedOracle e W t (labelProj e W t L i v)‖ ^ 2
      = ∑ r, ∑ i, ∑ s', ‖∑ s, qMatrix e (qIn r) (qAns r) s' s * v (r, s) *
          ((if L r.1 (slotsDB e s') = i then 1 else 0) -
            (if L r.1 (slotsDB e s) = i then 1 else 0))‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s' _ => by rw [hcomp]
    _ ≤ ∑ r, 24 * κ * ∑ s, ‖v (r, s)‖ ^ 2 := Finset.sum_le_sum fun r _ =>
        (fiber_labelComm_le e (qIn r) (qAns r) (L r.1) fun s => v (r, s)).trans (by
          have := hκ r.1
          gcongr)
    _ = 24 * κ * ‖v‖ ^ 2 := by
        simp only [← Finset.mul_sum, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

omit [DecidableEq Λ] in
/-- A label measurement commutes with the Hadamard transform on the answer register. -/
theorem hadamard_labelProj (L : W → DB (Bits m) B → Λ) (i : Λ)
    (v : QState (SimRegister W I J m t)) :
    hadamard W t (labelProj e W t L i v) = labelProj e W t L i (hadamard W t v) :=
  kernelOp_mask (fun b' b hk => by
    have h : b'.1.1 = b.1.1 ∧ b'.2 = b.2 := by
      by_contra hne
      exact hk (if_neg fun h => hne ⟨h.1, h.2.2⟩)
    simp only [Set.mem_setOf_eq, h.1, h.2]) v

/-- **A simulated query commutes with a label measurement up to `24 I(L, t)`**: the Hadamard
transforms on the answer register commute with the label projectors and preserve the norm
(`sum_norm_labelComm_le`). -/
theorem sum_norm_labelComm_simQuery_le [Fintype B] [Nonempty B] [Fintype Λ]
    (L : W → DB (Bits m) B → Λ) {κ : ℝ} (hκ : ∀ z, (instabPart (L z) t).toReal ≤ κ)
    (v : QState (SimRegister W I J m t)) :
    ∑ i, ‖labelProj e W t L i (simQuery e W t v) - simQuery e W t (labelProj e W t L i v)‖ ^ 2 ≤
      24 * κ * ‖v‖ ^ 2 := by
  have h : ∀ i, labelProj e W t L i (simQuery e W t v) - simQuery e W t (labelProj e W t L i v) =
      hadamard W t (labelProj e W t L i (compressedOracle e W t (hadamard W t v)) -
        compressedOracle e W t (labelProj e W t L i (hadamard W t v))) := fun i => by
    simp only [simQuery, ContinuousLinearMap.comp_apply, map_sub, hadamard_labelProj]
  simp_rw [h, norm_hadamard]
  rw [← norm_hadamard (v := v)]
  exact sum_norm_labelComm_le L hκ _

end Query

/-! ### The simulated run is determined by the real runs -/

section RealRuns

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ} {B : Type}
  (e : BitStr I J ≃ B) {O : Type} {t : ℕ} (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- **The simulated state is the compressed purified run** (Zha19 Lemmas 2 and 4): up to `t`
queries, `simStage e A k` is the compression of the Fourier transform of the superposition, over
the oracle `h`, of the run of `A` with oracle `h` (`simStage_eq_compress`, `fourier_fourStage`,
`purStage_apply`). Two algorithms on the same registers whose runs agree for every oracle
therefore have the same simulated state; this is how the order of independent queries is
exchanged in the simulated run. -/
theorem simStage_eq_compress_stages {k : ℕ} (hk : k ≤ t) :
    simStage e A k = compress e t A.W (fourier _ (WithLp.toLp 2 fun b =>
      unifAmp I J m * (A.toOracleAlg ∅).stage (queryPerm b.2) () k b.1)) := by
  rw [simStage_eq_compress e A hk]
  congr 1
  have h : (WithLp.toLp 2 fun b : PurReg A.W I J m =>
      unifAmp I J m * (A.toOracleAlg ∅).stage (queryPerm b.2) () k b.1) = purStage A k := by
    ext b
    exact (purStage_apply A k b.1 b.2).symm
  rw [h, ← fourier_fourStage, fourier_fourier]

end RealRuns

end GordieHowe.QROM
