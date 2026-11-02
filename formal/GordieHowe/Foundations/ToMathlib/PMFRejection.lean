-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Bounded rejection loops

A bounded rejection loop runs up to `n` independent attempts, each of law `A : PMF (Option α)`
(`none` is a rejection), and outputs the first accepted value, or `none` if all `n` attempts
reject (`firstSome A n`, the shape of FIPS 204 Algorithm 7, ML-DSA.Sign_internal, with a bound on
the number of iterations). Facts, on finite types:

- `firstSome_eq_map_pi`: the loop is `List.findSome?` over `n` independent attempts drawn up
  front (`pi_const_succ` splits off the first draw);
- `firstSome_apply_none`, `firstSome_apply_some`: the loop rejects with probability
  `A none ^ n` and outputs `a` with probability `A (some a) · ∑ k < n, A none ^ k`;
- `condSome A h`: the law of an attempt conditioned on acceptance, with density
  `A (some a) / (1 - A none)`;
- `tvDist_firstSome_map_condSome`: the loop is at distance exactly `A none ^ n` from
  `some <$> condSome A h`.

Rejection sampling with a uniform challenge: an attempt draws `y ← P`, a uniform `c`
(`withUniform`), and accepts `(y, c)` when `acc y c` (`rejectionAttempt`, `rejectionAttempt_eq_map`).
The loop is within `(1 - p) ^ n` of the accepted law (`tvDist_firstSome_rejectionAttempt`). The accepted pair has density
`P y · |C|⁻¹ · [acc y c] / p` (`condSome_rejectionAttempt_apply`), with `p` the acceptance
probability (`acceptProb`), and the accepted challenge has density proportional to
`acceptProbAt P acc c = Pr_{y ← P}[acc y c]` (`map_snd_condSome_rejectionAttempt_apply`).

Flattening: thinning a law `S` by keeping `c` with probability `κ c` (`thin`). For
`S c = α c · u c / ∑ α u` and `κ c = min 1 (β / α c)`, the kept value has density
`u c · min (α c) β / ∑ u · min α β` (`condSome_thin_flatten_apply`), at distance at most
`∑ u · (β - α) / ∑ u · min α β` from `u` (`tvDist_condSome_thin_flatten_le`), and the bounded
loop over these thinned attempts is within that plus the rejection term `thin S κ none ^ n` of
`u` (`tvDist_firstSome_thin_flatten_le`).

About Mathlib objects only; a candidate for upstreaming with
`GordieHowe/Foundations/ToMathlib/PMFTV.lean`.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

section Loop

variable {α : Type*} [Fintype α]

/-- **The bounded rejection loop**: up to `n` independent attempts of law `A`, returning the first
accepted value, or `none` if all `n` reject. -/
noncomputable def firstSome (A : PMF (Option α)) : ℕ → PMF (Option α)
  | 0 => pure none
  | n + 1 => A.bind fun o => o.elim (firstSome A n) fun a => pure (some a)

omit [Fintype α] in
/-- The loop with no attempts rejects. -/
theorem firstSome_zero (A : PMF (Option α)) : firstSome A 0 = pure none := rfl

/-- One more attempt of the loop: accept now, or reject and run the shorter loop. -/
theorem firstSome_succ_apply (A : PMF (Option α)) (n : ℕ) (o : Option α) :
    firstSome A (n + 1) o =
      A none * firstSome A n o + ∑ a, A (some a) * (pure (some a) : PMF (Option α)) o := by
  simp only [firstSome, bind_apply, tsum_fintype, Fintype.sum_option, Option.elim]

/-- The loop rejects all `n` attempts with probability `A none ^ n`. -/
theorem firstSome_apply_none (A : PMF (Option α)) (n : ℕ) : firstSome A n none = A none ^ n := by
  induction n with
  | zero => simp [firstSome_zero]
  | succ n ih => simp [firstSome_succ_apply, ih, pow_succ, mul_comm]

/-- The loop outputs `a` with probability `A (some a) · ∑ k < n, A none ^ k`. -/
theorem firstSome_apply_some (A : PMF (Option α)) (n : ℕ) (a : α) :
    firstSome A n (some a) = A (some a) * ∑ k ∈ range n, A none ^ k := by
  induction n with
  | zero => simp [firstSome_zero]
  | succ n ih =>
    rw [firstSome_succ_apply, ih, sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
      (by simp), pure_apply_self, mul_one, sum_range_succ', pow_zero, mul_add, mul_one,
      mul_sum]
    congr 1
    simp only [Finset.mul_sum, pow_succ]
    exact sum_congr rfl fun k _ => by ring

/-- **`n + 1` independent draws** as a first draw followed by `n` more. -/
theorem pi_const_succ {β : Type*} [Fintype β] (A : PMF β) (n : ℕ) :
    (pi fun _ : Fin (n + 1) => A) = A.bind fun b => (pi fun _ : Fin n => A).map (Fin.cons b) := by
  classical
  ext f
  rw [pi_apply, Fin.prod_univ_succ, bind_apply, tsum_eq_single (f 0) fun b hb => ?_]
  · rw [map_apply, tsum_eq_single (Fin.tail f) fun g hg => ?_]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (Fin.cons_self_tail f).symm), pi_apply]
      rfl
    · refine ite_eq_right_of_eq_false _ _ (eq_false fun h => hg ?_)
      rw [h, Fin.tail_cons]
  · rw [map_apply, ENNReal.tsum_eq_zero.2 fun g => ?_, mul_zero]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun h => hb ?_)
    rw [h, Fin.cons_zero]

/-- **The loop as the first acceptance among `n` independent attempts**: `firstSome A n` is
`List.findSome?` over `n` independent attempts drawn up front. -/
theorem firstSome_eq_map_pi (A : PMF (Option α)) (n : ℕ) :
    firstSome A n = (pi fun _ : Fin n => A).map fun os => (List.finRange n).findSome? os := by
  induction n with
  | zero =>
    rw [firstSome_zero]
    simp only [List.finRange_zero, List.findSome?_nil]
    exact (map_const _ _).symm
  | succ n ih =>
    rw [pi_const_succ, map_bind, firstSome]
    congr 1
    funext o
    rw [map_comp]
    have hfs : ((fun os : Fin (n + 1) → Option α => (List.finRange (n + 1)).findSome? os) ∘
        Fin.cons o) = fun os => o.elim ((List.finRange n).findSome? os) some := by
      funext os
      simp only [Function.comp_apply, List.finRange_succ, List.findSome?_cons, Fin.cons_zero,
        List.findSome?_map]
      cases o <;> rfl
    rw [hfs]
    cases o with
    | none => exact ih
    | some a => exact (map_const _ _).symm

/-- The accepted values of an attempt carry the mass `1 - A none`. -/
theorem sum_apply_some (A : PMF (Option α)) : ∑ a, A (some a) = 1 - A none := by
  have h := sum_coe A
  rw [Fintype.sum_option] at h
  exact ENNReal.eq_sub_of_add_eq (A.apply_ne_top none) (by rw [add_comm]; exact h)

/-- An attempt rejects with probability one minus the mass of its accepted values. -/
theorem apply_none_eq_one_sub (A : PMF (Option α)) : A none = 1 - ∑ a, A (some a) := by
  rw [sum_apply_some, ENNReal.sub_sub_cancel ENNReal.one_ne_top (A.coe_le_one none)]

omit [Fintype α] in
/-- An attempt that does not always reject accepts with positive probability. -/
theorem one_sub_apply_none_ne_zero {A : PMF (Option α)} (h : A none ≠ 1) : 1 - A none ≠ 0 :=
  (tsub_pos_of_lt (lt_of_le_of_ne (A.coe_le_one none) h)).ne'

/-- **The law of an attempt conditioned on acceptance**, defined when an attempt accepts with
positive probability. -/
noncomputable def condSome (A : PMF (Option α)) (h : A none ≠ 1) : PMF α :=
  ofFintype (fun a => A (some a) / (1 - A none)) (by
    simp only [div_eq_mul_inv]
    rw [← sum_mul, sum_apply_some]
    exact ENNReal.mul_inv_cancel (one_sub_apply_none_ne_zero h) (by simp))

/-- The conditional law of an accepted value is its probability over the acceptance probability. -/
theorem condSome_apply (A : PMF (Option α)) (h : A none ≠ 1) (a : α) :
    condSome A h a = A (some a) / (1 - A none) := rfl

omit [Fintype α] in
/-- `some <$> μ` puts the mass of `a` on `some a`. -/
theorem map_some_apply_some (μ : PMF α) (a : α) : μ.map some (some a) = μ a := by
  rw [map_apply, tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

omit [Fintype α] in
/-- `some <$> μ` puts no mass on `none`. -/
theorem map_some_apply_none (μ : PMF α) : μ.map some none = 0 := by
  simp [map_apply]

/-- **A bounded rejection loop is `A none ^ n`-close to the conditional law**: the loop over `n`
attempts of law `A` is at total variation distance exactly `A none ^ n` from the law of one
attempt conditioned on acceptance. -/
theorem tvDist_firstSome_map_condSome (A : PMF (Option α)) (h : A none ≠ 1) (n : ℕ) :
    tvDist (firstSome A n) ((condSome A h).map some) = (A none ^ n).toReal := by
  rw [tvDist_eq_toReal_tsum_tsub, tsum_fintype, Fintype.sum_option, firstSome_apply_none,
    map_some_apply_none, tsub_zero, sum_eq_zero fun a _ => ?_, add_zero]
  rw [firstSome_apply_some, map_some_apply_some, condSome_apply, tsub_eq_zero_iff_le,
    div_eq_mul_inv]
  gcongr
  calc ∑ k ∈ range n, A none ^ k ≤ ∑' k, A none ^ k := ENNReal.sum_le_tsum _
    _ = (1 - A none)⁻¹ := ENNReal.tsum_geometric _

end Loop

section Rejection

variable {Y C : Type*} [Fintype Y] [Fintype C] [Nonempty C]

/-- **One rejection-sampling attempt with a uniform challenge**: draw `y ← P` and a uniform `c`,
and output `some (y, c)` if `acc y c`, else `none`. -/
noncomputable def rejectionAttempt (P : PMF Y) (acc : Y → C → Bool) : PMF (Option (Y × C)) :=
  P.bind fun y => (uniformOfFintype C).map fun c => if acc y c then some (y, c) else none

/-- The joint law of `y ← P` and an independent uniform challenge `c`. -/
noncomputable def withUniform (P : PMF Y) (C : Type*) [Fintype C] [Nonempty C] : PMF (Y × C) :=
  P.bind fun y => (uniformOfFintype C).map (Prod.mk y)

omit [Fintype Y] in
/-- An attempt is the joint draw followed by the acceptance test. -/
theorem rejectionAttempt_eq_map (P : PMF Y) (acc : Y → C → Bool) :
    rejectionAttempt P acc =
      (withUniform P C).map fun z => if acc z.1 z.2 then some z else none := by
  rw [withUniform, map_bind]
  simp only [map_comp]
  rfl

/-- The probability `Pr_{y ← P}[acc y c]` that a fixed challenge `c` is accepted. -/
noncomputable def acceptProbAt (P : PMF Y) (acc : Y → C → Bool) (c : C) : ℝ≥0∞ :=
  ∑ y, if acc y c then P y else 0

/-- The probability that one attempt accepts: `acceptProbAt` averaged over a uniform `c`. -/
noncomputable def acceptProb (P : PMF Y) (acc : Y → C → Bool) : ℝ≥0∞ :=
  ∑ c, acceptProbAt P acc c * (Fintype.card C : ℝ≥0∞)⁻¹

omit [Fintype Y] in
/-- An attempt outputs `(y, c)` with probability `P y · |C|⁻¹` if `acc y c`. -/
theorem rejectionAttempt_apply_some (P : PMF Y) (acc : Y → C → Bool) (y : Y) (c : C) :
    rejectionAttempt P acc (some (y, c)) =
      if acc y c then P y * (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [rejectionAttempt, bind_apply, tsum_eq_single y fun y' hy' => ?_]
  · rw [map_apply, tsum_eq_single c fun c' hc' => ?_]
    · by_cases h : acc y c <;> simp [h]
    · by_cases h : acc y c' <;> simp [h, Ne.symm hc']
  · rw [map_apply, ENNReal.tsum_eq_zero.2 fun c' => ?_, mul_zero]
    by_cases h : acc y' c' <;> simp [h, Ne.symm hy']

/-- The accepted pairs of an attempt carry the mass `acceptProb P acc`. -/
theorem sum_rejectionAttempt_apply_some (P : PMF Y) (acc : Y → C → Bool) :
    ∑ z : Y × C, rejectionAttempt P acc (some z) = acceptProb P acc := by
  rw [Fintype.sum_prod_type, sum_comm, acceptProb]
  refine sum_congr rfl fun c _ => ?_
  rw [acceptProbAt, sum_mul]
  exact sum_congr rfl fun y _ => by rw [rejectionAttempt_apply_some]; split_ifs <;> simp

/-- The acceptance probability is one minus the rejection probability of an attempt. -/
theorem acceptProb_eq_one_sub (P : PMF Y) (acc : Y → C → Bool) :
    acceptProb P acc = 1 - rejectionAttempt P acc none := by
  rw [← sum_rejectionAttempt_apply_some, sum_apply_some]

/-- An attempt rejects with probability `1 - acceptProb P acc`. -/
theorem rejectionAttempt_apply_none (P : PMF Y) (acc : Y → C → Bool) :
    rejectionAttempt P acc none = 1 - acceptProb P acc := by
  rw [acceptProb_eq_one_sub,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top ((rejectionAttempt P acc).coe_le_one none)]

/-- An attempt with positive acceptance probability does not always reject. -/
theorem rejectionAttempt_apply_none_ne_one {P : PMF Y} {acc : Y → C → Bool}
    (h : acceptProb P acc ≠ 0) : rejectionAttempt P acc none ≠ 1 := fun h1 =>
  h (by rw [acceptProb_eq_one_sub, h1, tsub_self])

/-- **The accepted pair of rejection sampling** has density `P y · |C|⁻¹ · [acc y c] / p`. -/
theorem condSome_rejectionAttempt_apply {P : PMF Y} {acc : Y → C → Bool}
    (h : acceptProb P acc ≠ 0) (y : Y) (c : C) :
    condSome (rejectionAttempt P acc) (rejectionAttempt_apply_none_ne_one h) (y, c) =
      (if acc y c then P y * (Fintype.card C : ℝ≥0∞)⁻¹ else 0) / acceptProb P acc := by
  rw [condSome_apply, rejectionAttempt_apply_some, ← acceptProb_eq_one_sub]

/-- **The accepted challenge of rejection sampling** has density proportional to
`acceptProbAt P acc c = Pr_{y ← P}[acc y c]`: it is `acceptProbAt P acc c · |C|⁻¹ / p`. -/
theorem map_snd_condSome_rejectionAttempt_apply {P : PMF Y} {acc : Y → C → Bool}
    (h : acceptProb P acc ≠ 0) (c : C) :
    (condSome (rejectionAttempt P acc) (rejectionAttempt_apply_none_ne_one h)).map Prod.snd c =
      acceptProbAt P acc c * (Fintype.card C : ℝ≥0∞)⁻¹ / acceptProb P acc := by
  classical
  rw [map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [sum_ite_eq, mem_univ, ite_true]
  rw [sum_congr rfl fun y _ => condSome_rejectionAttempt_apply h y c]
  simp only [acceptProbAt, div_eq_mul_inv, sum_mul, ite_mul, zero_mul]

/-- **Bounded rejection sampling is `(1 - p) ^ n`-close to the accepted law**: the loop over `n`
attempts is at total variation distance exactly `(1 - p) ^ n` from `some <$>` the law of `(y, c)`
conditioned on `acc y c`. -/
theorem tvDist_firstSome_rejectionAttempt {P : PMF Y} {acc : Y → C → Bool}
    (h : acceptProb P acc ≠ 0) (n : ℕ) :
    tvDist (firstSome (rejectionAttempt P acc) n)
        ((condSome (rejectionAttempt P acc) (rejectionAttempt_apply_none_ne_one h)).map some) =
      ((1 - acceptProb P acc) ^ n).toReal := by
  rw [tvDist_firstSome_map_condSome, rejectionAttempt_apply_none]

end Rejection

section Thin

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Keep `a` with probability `k` (output `some a`), otherwise reject (output `none`). -/
noncomputable def keepOrReject (a : α) (k : ℝ≥0∞) (hk : k ≤ 1) : PMF (Option α) :=
  ofFintype (fun o => o.elim (1 - k) fun b => if b = a then k else 0) (by
    rw [Fintype.sum_option]
    simp [tsub_add_cancel_of_le hk])

/-- **Thinning**: draw `a ← S` and keep it with probability `κ a`. -/
noncomputable def thin (S : PMF α) (κ : α → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) : PMF (Option α) :=
  S.bind fun a => keepOrReject a (κ a) (hκ a)

/-- A thinned attempt keeps `a` with probability `S a · κ a`. -/
theorem thin_apply_some (S : PMF α) (κ : α → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) (a : α) :
    thin S κ hκ (some a) = S a * κ a := by
  rw [thin, bind_apply, tsum_fintype,
    sum_eq_single a (fun b _ hb => by simp [keepOrReject, Ne.symm hb]) (by simp)]
  simp [keepOrReject]

/-- The flattening keep probability `min 1 (β / w a)` turns the weight `w a` into
`min (w a) β`. -/
theorem mul_min_one_div {w β : ℝ≥0∞} (hw : w ≠ ⊤) : w * min 1 (β / w) = min w β := by
  rcases eq_or_ne w 0 with rfl | h0
  · simp
  · rw [mul_min, mul_one, ENNReal.mul_div_cancel h0 hw]

/-- `β - w` and `min w β` add up to `β`. -/
theorem tsub_add_min (w β : ℝ≥0∞) : β - w + min w β = β := by
  rcases le_total w β with h | h
  · rw [min_eq_left h, tsub_add_cancel_of_le h]
  · rw [min_eq_right h, tsub_eq_zero_of_le h, zero_add]

variable (u : PMF α) (w : α → ℝ≥0∞) (β : ℝ≥0∞)

/-- The flattening keep probability. -/
noncomputable def flattenKeep (a : α) : ℝ≥0∞ := min 1 (β / w a)

omit [Fintype α] [DecidableEq α] in
/-- The flattening keep probability is a probability. -/
theorem flattenKeep_le_one (a : α) : flattenKeep w β a ≤ 1 := min_le_left _ _

/-- The hypotheses of flattening: `S` has density `u · w / ∑ u · w` with weights `w ≤ 1`, the
threshold is `β ≤ 1`, and the flattened mass `∑ u · min w β` is positive. -/
structure FlattenHyp (S : PMF α) : Prop where
  weight_le_one : ∀ a, w a ≤ 1
  threshold_le_one : β ≤ 1
  apply_eq : ∀ a, S a = u a * w a / ∑ b, u b * w b
  mass_ne_zero : ∑ a, u a * min (w a) β ≠ 0

variable {u w β} {S : PMF α}

omit [DecidableEq α] in
/-- The normalizer `∑ u · w` is finite. -/
theorem FlattenHyp.sum_ne_top (hS : FlattenHyp u w β S) : ∑ b, u b * w b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top <| (sum_coe u).symm ▸
    sum_le_sum fun b _ => mul_le_of_le_one_right' (hS.weight_le_one b)

omit [DecidableEq α] in
/-- The normalizer `∑ u · w` is positive. -/
theorem FlattenHyp.sum_ne_zero (hS : FlattenHyp u w β S) : ∑ b, u b * w b ≠ 0 := fun h0 =>
  hS.mass_ne_zero (le_antisymm (h0 ▸ sum_le_sum fun b _ => by gcongr; exact min_le_left _ _)
    bot_le)

/-- A flattened attempt keeps `a` with probability `u a · min (w a) β / ∑ u · w`. -/
theorem FlattenHyp.thin_apply_some (hS : FlattenHyp u w β S) (a : α) :
    thin S (flattenKeep w β) (flattenKeep_le_one w β) (some a) =
      u a * min (w a) β / ∑ b, u b * w b := by
  rw [PMF.thin_apply_some, hS.apply_eq, flattenKeep, ← mul_min_one_div
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hS.weight_le_one a))]
  simp only [div_eq_mul_inv]
  ring

/-- A flattened attempt accepts with probability `∑ u · min w β / ∑ u · w`. -/
theorem FlattenHyp.sum_thin_apply_some (hS : FlattenHyp u w β S) :
    ∑ a, thin S (flattenKeep w β) (flattenKeep_le_one w β) (some a) =
      (∑ a, u a * min (w a) β) / ∑ b, u b * w b := by
  simp only [hS.thin_apply_some, div_eq_mul_inv, sum_mul]

/-- A flattened attempt rejects with probability `1 - ∑ u · min w β / ∑ u · w`. -/
theorem FlattenHyp.thin_apply_none (hS : FlattenHyp u w β S) :
    thin S (flattenKeep w β) (flattenKeep_le_one w β) none =
      1 - (∑ a, u a * min (w a) β) / ∑ b, u b * w b := by
  rw [apply_none_eq_one_sub, hS.sum_thin_apply_some]

/-- A flattened attempt does not always reject. -/
theorem FlattenHyp.thin_apply_none_ne_one (hS : FlattenHyp u w β S) :
    thin S (flattenKeep w β) (flattenKeep_le_one w β) none ≠ 1 := by
  intro h1
  have h := sum_apply_some (thin S (flattenKeep w β) (flattenKeep_le_one w β))
  rw [h1, tsub_self, hS.sum_thin_apply_some, ENNReal.div_eq_zero_iff] at h
  exact h.elim hS.mass_ne_zero hS.sum_ne_top

/-- **The flattened law**: the kept value has density `u a · min (w a) β / ∑ u · min w β`. -/
theorem FlattenHyp.condSome_thin_apply (hS : FlattenHyp u w β S) (a : α) :
    condSome (thin S (flattenKeep w β) (flattenKeep_le_one w β)) hS.thin_apply_none_ne_one a =
      u a * min (w a) β / ∑ b, u b * min (w b) β := by
  rw [condSome_apply, ← sum_apply_some, hS.sum_thin_apply_some, hS.thin_apply_some]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hS.mass_ne_zero)
    (Or.inr (ENNReal.inv_ne_zero.2 hS.sum_ne_top)),
    inv_inv]
  calc u a * min (w a) β * (∑ b, u b * w b)⁻¹ * ((∑ b, u b * min (w b) β)⁻¹ * ∑ b, u b * w b)
      = u a * min (w a) β * (∑ b, u b * min (w b) β)⁻¹ *
          ((∑ b, u b * w b)⁻¹ * ∑ b, u b * w b) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hS.sum_ne_zero hS.sum_ne_top, mul_one]

/-- **Flattening brings the law close to `u`**: the kept value is at total variation distance at
most `∑ u · (β - w) / ∑ u · min w β` from `u`. -/
theorem FlattenHyp.tvDist_condSome_thin_le (hS : FlattenHyp u w β S) :
    tvDist (condSome (thin S (flattenKeep w β) (flattenKeep_le_one w β))
        hS.thin_apply_none_ne_one) u ≤
      ((∑ a, u a * (β - w a)) / ∑ a, u a * min (w a) β).toReal := by
  set M := ∑ a, u a * min (w a) β
  have hMβ : M ≤ β := by
    calc M ≤ ∑ a, u a * β := sum_le_sum fun a _ => by gcongr; exact min_le_right _ _
      _ = β := by rw [← sum_mul, sum_coe, one_mul]
  have hfin : (∑ a, u a * (β - w a)) / M ≠ ⊤ := by
    refine ENNReal.div_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) hS.mass_ne_zero
    calc ∑ a, u a * (β - w a) ≤ ∑ a, u a * 1 :=
          sum_le_sum fun a _ => by gcongr; exact tsub_le_self.trans hS.threshold_le_one
      _ = 1 := by simp [sum_coe]
  rw [tvDist_comm, tvDist_eq_toReal_tsum_tsub, tsum_fintype]
  refine ENNReal.toReal_mono hfin ?_
  simp only [div_eq_mul_inv, sum_mul]
  refine sum_le_sum fun a _ => ?_
  rw [hS.condSome_thin_apply, tsub_le_iff_right, div_eq_mul_inv, ← add_mul, ← mul_add,
    tsub_add_min]
  rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hS.mass_ne_zero)
    (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top (hMβ.trans hS.threshold_le_one)))]
  gcongr

/-- **The bounded flattening loop**: `n` thinned attempts are within the rejection term
`(1 - ∑ u · min w β / ∑ u · w) ^ n` plus `∑ u · (β - w) / ∑ u · min w β` of `some <$> u`. -/
theorem FlattenHyp.tvDist_firstSome_thin_le (hS : FlattenHyp u w β S) (n : ℕ) :
    tvDist (firstSome (thin S (flattenKeep w β) (flattenKeep_le_one w β)) n) (u.map some) ≤
      ((1 - (∑ a, u a * min (w a) β) / ∑ b, u b * w b) ^ n).toReal +
        ((∑ a, u a * (β - w a)) / ∑ a, u a * min (w a) β).toReal := by
  refine (tvDist_triangle _ ((condSome _ hS.thin_apply_none_ne_one).map some) _).trans ?_
  rw [tvDist_firstSome_map_condSome, hS.thin_apply_none]
  gcongr
  exact (tvDist_map_le _ _ _).trans hS.tvDist_condSome_thin_le

end Thin

end PMF
