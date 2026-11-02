-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.Interaction

@[expose] public section

/-!
# Guessing a reply's secret from its public value

A classical interaction (`GordieHowe/Foundations/Probability/Interaction.lean`) whose challenger
draws uniform independent coins `c 0, c 1, …`, one per coin-reading round, and answers the `j`-th
coin-reading move `m` (a move with `w m = 1`; `readCount` counts them) reading `c j` only through a
public value `φ m (c j)`. The secret of coin `j` is `g m (c j)` (for a signing challenger: the
signature, `none` when it refuses). Every strategy outputs the secret of coin `j` with probability
at most `γ` when the secret has average
conditional min-entropy at least `log₂ (1 / γ)` given the public value, `Σ_y max_z Pr_c[φ m c = y ∧
g m c = some z] ≤ γ` at every move (Dodis, Ostrovsky, Reyzin, Smith, "Fuzzy Extractors", SIAM J.
Comput. 38(1), 2008, Section 2.4): the strategy's move at round `j` is drawn before `c j` is read,
and what follows reads `c j` only through the reply.

- `support_cont_prefix`: the final history of a continuation extends its start.
- `cont_congr_coins`: continuations from the histories of a set closed under extension, at two coins
  giving the same input and the same replies there, agree.
- `readCount`, `readCount_append`, `readCount_singleton`, `readCount_take_add_le`, `readCount_le_take_of_le`: the number of
  coin-reading moves of a history.
- `GuessAt`: the event that the output is the secret of coin `j`.
- `sum_uniform_guess_le`: the guess of the secret from its public value, for one move.
- `tsum_cont_guess_le`: the bound at fixed other coins, from a history before the read of coin `j`.
- `sum_uniform_update`: resampling one coordinate of a uniform function.
- `tsum_coins_cont_guess_le`: the bound in the experiment.
-/

open scoped ENNReal BigOperators

namespace GordieHowe.Interaction

variable {Ω I M R O : Type*}

/-- **The final history of a continuation extends its start.** -/
theorem support_cont_prefix (σ : Strategy I M R O) (χ : Challenger Ω I M R) (ω : Ω) :
    ∀ (k : ℕ) (h : Hist M R) (p : Hist M R × O), p ∈ (cont σ χ ω h k).support →
      ∃ t, p.1 = h ++ t
  | 0, h, p, hp => by
    simp only [cont, PMF.support_map, Set.mem_image] at hp
    obtain ⟨o, -, rfl⟩ := hp
    exact ⟨[], by simp⟩
  | k + 1, h, p, hp => by
    simp only [cont, PMF.support_bind, Set.mem_iUnion] at hp
    obtain ⟨m, -, r, -, hp⟩ := hp
    obtain ⟨t, ht⟩ := support_cont_prefix σ χ ω k _ p hp
    exact ⟨(m, r) :: t, by simp [ht]⟩

/-- **Continuations at two coins with the same input and replies agree** from the histories of a
set closed under extension, when the replies agree at those histories. -/
theorem cont_congr_coins (σ : Strategy I M R O) (χ : Challenger Ω I M R) {ω ω' : Ω}
    (P : Hist M R → Prop) (hP : ∀ h m r, P h → P (h ++ [(m, r)]))
    (hin : χ.input ω = χ.input ω') (hr : ∀ h m, P h → χ.reply ω h m = χ.reply ω' h m) :
    ∀ (k : ℕ) (h : Hist M R), P h → cont σ χ ω h k = cont σ χ ω' h k
  | 0, h, _ => by simp only [cont, hin]
  | k + 1, h, hh => by
    simp only [cont, hin]
    refine congrArg _ (funext fun m => ?_)
    rw [hr h m hh]
    refine congrArg _ (funext fun r => ?_)
    exact cont_congr_coins σ χ P hP hin hr k _ (hP h m r hh)

/-- **The secret of one move is guessed from its public value with probability at most `γ`**: for
weights `F y z` of the guesses `z` at the public value `y`, of total at most one at each `y`, the
average over a uniform coin `x` of the weight of the secret `g x` at the public value `φ x` is at
most `γ`, when `Σ_y max_z Pr_x[φ x = y ∧ g x = some z] ≤ γ`. -/
theorem sum_uniform_guess_le {C Y Z : Type*} [Fintype C] [Nonempty C] [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z] (φ : C → Y) (g : C → Option Z) (F : Y → Z → ℝ≥0∞) {γ : ℝ≥0∞}
    (hγ : ∑ y, ⨆ z, (PMF.uniformOfFintype C).toOuterMeasure {x | φ x = y ∧ g x = some z} ≤ γ)
    (hF : ∀ y, ∑ z, F y z ≤ 1) :
    ∑ x, PMF.uniformOfFintype C x * (match g x with
      | some z => F (φ x) z
      | none => 0) ≤ γ := by
  classical
  set U := PMF.uniformOfFintype C
  have hmeas : ∀ y z, U.toOuterMeasure {x | φ x = y ∧ g x = some z} =
      ∑ x, if φ x = y ∧ g x = some z then U x else 0 := fun y z => by
    rw [PMF.toOuterMeasure_apply_fintype]
    exact Finset.sum_congr rfl fun x _ => by simp [Set.indicator_apply]
  have hsplit : ∀ x, U x * (match g x with
      | some z => F (φ x) z
      | none => 0) =
      ∑ y, ∑ z, (if φ x = y ∧ g x = some z then U x else 0) * F y z := fun x => by
    rcases hx : g x with _ | z₀
    · simp
    · simp only [Option.some.injEq]
      rw [Finset.sum_eq_single (φ x) (fun y _ hy => by simp [Ne.symm hy]) (by simp),
        Finset.sum_eq_single z₀ (fun z _ hz => by simp [Ne.symm hz]) (by simp)]
      simp
  calc ∑ x, U x * (match g x with
        | some z => F (φ x) z
        | none => 0)
      = ∑ y, ∑ z, U.toOuterMeasure {x | φ x = y ∧ g x = some z} * F y z := by
        simp_rw [hsplit, hmeas, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ ≤ ∑ y, ∑ z, (⨆ z', U.toOuterMeasure {x | φ x = y ∧ g x = some z'}) * F y z := by
        gcongr with y _ z _
        exact le_iSup (fun z' => U.toOuterMeasure {x | φ x = y ∧ g x = some z'}) z
    _ = ∑ y, (⨆ z', U.toOuterMeasure {x | φ x = y ∧ g x = some z'}) * ∑ z, F y z := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ y, (⨆ z', U.toOuterMeasure {x | φ x = y ∧ g x = some z'}) * 1 := by
        gcongr with y _
        exact hF y
    _ ≤ γ := by simpa using hγ

section Round

variable {C Y Z : Type*} [Fintype C] [Nonempty C] [Fintype Y] [DecidableEq Y] [Fintype Z]
  [DecidableEq Z] {N : ℕ} (σ : Strategy I M R O) (χ : Challenger (Fin N → C) I M R)
  (w : M → ℕ) (j : Fin N) (φ : M → C → Y) (g : M → C → Option Z) (guess : Hist M R × O → Z)
  (ψ : (Fin N → C) → Hist M R → M → Y → PMF R)

/-- **The number of coin-reading moves of a history**: the sum of `w` (`0` or `1`) over its
moves. -/
def readCount (h : Hist M R) : ℕ := (h.map fun p => w p.1).sum

omit [Fintype C] [Nonempty C] in
theorem readCount_append (h t : Hist M R) :
    readCount w (h ++ t) = readCount w h + readCount w t := by
  simp [readCount]

omit [Fintype C] [Nonempty C] in
@[simp] theorem readCount_singleton (m : M) (r : R) : readCount w [(m, r)] = w m := by
  simp [readCount]

omit [Fintype C] [Nonempty C] in
theorem readCount_take_add_le (h : Hist M R) {i : ℕ} {m : M} {r : R} (hi : h[i]? = some (m, r)) :
    readCount w (h.take i) + w m ≤ readCount w h := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hi
  conv_rhs => rw [← List.take_append_drop i h]
  rw [readCount_append, List.drop_eq_getElem_cons hlt, he]
  simp only [readCount, List.map_cons, List.sum_cons]
  omega

omit [Fintype C] [Nonempty C] in
theorem readCount_le_take_of_le (h t : Hist M R) {i : ℕ} (hi : h.length ≤ i) :
    readCount w h ≤ readCount w ((h ++ t).take i) := by
  rw [List.take_append, List.take_of_length_le hi, readCount_append]
  exact Nat.le_add_right _ _

/-- **The event that the output guesses the secret of the coin `j`**, at the value `x` of that
coin: some round whose move reads a coin, after `j` coin-reading rounds, has a move `m` whose
secret at `x` is the guess. -/
def GuessAt (x : C) : Set (Hist M R × O) :=
  {p | ∃ i : ℕ, ∃ m r, p.1[i]? = some (m, r) ∧ w m = 1 ∧ readCount w (p.1.take i) = j ∧
    g m x = some (guess p)}

/-- **The guess bound at fixed other coins, from a history before the read of coin `j`**: the
input and the replies other than the read of coin `j` do not read it (`hin`, `hloc`), and the
read of coin `j`, the coin-reading move after `j` reads (`w m = 1`), reads it only through the
public value (`hj`). -/
theorem tsum_cont_guess_le {γ : ℝ≥0∞} (hw : ∀ m, w m ≤ 1)
    (hin : ∀ c x, χ.input (Function.update c j x) = χ.input c)
    (hloc : ∀ c x h m, (readCount w h ≠ j ∨ w m = 0) →
      χ.reply (Function.update c j x) h m = χ.reply c h m)
    (hj : ∀ c x h m, readCount w h = j → w m = 1 →
      χ.reply (Function.update c j x) h m = ψ c h m (φ m x))
    (hγ : ∀ m, ∑ y, ⨆ z,
      (PMF.uniformOfFintype C).toOuterMeasure {x | φ m x = y ∧ g m x = some z} ≤ γ)
    (c : Fin N → C) :
    ∀ (k : ℕ) (h : Hist M R), readCount w h ≤ j →
      ∑ x, PMF.uniformOfFintype C x *
        (cont σ χ (Function.update c j x) h k).toOuterMeasure (GuessAt w j g guess x) ≤ γ
  | 0, h, hh => by
    refine le_of_eq_of_le (Finset.sum_eq_zero fun x _ => ?_) zero_le
    refine mul_eq_zero_of_right _ ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
      (Set.disjoint_left.2 fun p hp hg => ?_))
    simp only [cont, PMF.support_map, Set.mem_image] at hp
    obtain ⟨o, -, rfl⟩ := hp
    obtain ⟨i, m, r, hm, hw1, hc, -⟩ := hg
    dsimp only at hm hc
    have := readCount_take_add_le w h hm
    omega
  | k + 1, h, hh => by
    simp only [cont, PMF.toOuterMeasure_bind_apply, hin]
    -- the bound for each move
    have hmove : ∀ m, ∑ x, PMF.uniformOfFintype C x * ∑' r,
        χ.reply (Function.update c j x) h m r *
          (cont σ χ (Function.update c j x) (h ++ [(m, r)]) k).toOuterMeasure
            (GuessAt w j g guess x) ≤ γ := fun m => by
      by_cases hread : readCount w h = j ∧ w m = 1
      · -- the read of coin `j`: what follows does not read it
        obtain ⟨hc, hw1⟩ := hread
        have hlater : ∀ x r, cont σ χ (Function.update c j x) (h ++ [(m, r)]) k =
            cont σ χ c (h ++ [(m, r)]) k := fun x r =>
          cont_congr_coins σ χ (fun h' => (j : ℕ) < readCount w h')
            (fun h' m' r' hh' => by rw [readCount_append]; omega) (hin c x)
            (fun h' m' hh' => hloc c x h' m' (Or.inl (by omega))) k _
            (by rw [readCount_append, readCount_singleton]; omega)
        have hev : ∀ x r, (cont σ χ c (h ++ [(m, r)]) k).toOuterMeasure
            (GuessAt w j g guess x) ≤
              (cont σ χ c (h ++ [(m, r)]) k).toOuterMeasure {p | g m x = some (guess p)} :=
          fun x r => by
            refine PMF.toOuterMeasure_mono _ fun p hp => ?_
            obtain ⟨hp1, hs⟩ := hp
            obtain ⟨i, m', r', hm', hw', hc', hg⟩ := hp1
            have hs' : p ∈ (cont σ χ c (h ++ [(m, r)]) k).support := hs
            obtain ⟨t, ht⟩ := support_cont_prefix σ χ c k _ p hs'
            rcases lt_trichotomy i h.length with hi | hi | hi
            · -- an earlier round: it would make more than `j` reads before the read of `j`
              rw [ht, List.append_assoc, List.getElem?_append_left hi] at hm'
              rw [ht, List.append_assoc, List.take_append_of_le_length hi.le] at hc'
              have := readCount_take_add_le w h hm'
              omega
            · subst hi
              rw [ht, List.append_assoc, List.getElem?_append_right le_rfl] at hm'
              simp only [Nat.sub_self, List.cons_append, List.singleton_append,
                List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hm'
              obtain ⟨rfl, rfl⟩ := hm'
              exact hg
            · -- a later round: more than `j` reads before it
              have hle := readCount_le_take_of_le w (h ++ [(m, r)]) t (i := i)
                (by simp; omega)
              rw [← ht, readCount_append, readCount_singleton] at hle
              omega
        let F : Y → Z → ℝ≥0∞ := fun y z => ∑' r, ψ c h m y r *
          (cont σ χ c (h ++ [(m, r)]) k).toOuterMeasure {p | guess p = z}
        have hF : ∀ y, ∑ z, F y z ≤ 1 := fun y => by
          have h1 : ∀ r, ∑ z, (cont σ χ c (h ++ [(m, r)]) k).toOuterMeasure
              {p | guess p = z} = 1 := fun r => by
            simp_rw [show ∀ z, {p : Hist M R × O | guess p = z} = guess ⁻¹' {z} from
              fun _ => rfl, ← PMF.toOuterMeasure_map_apply]
            simp_rw [PMF.toOuterMeasure_apply_singleton]
            rw [← tsum_fintype (L := SummationFilter.unconditional Z), PMF.tsum_coe]
          calc ∑ z, F y z
              = ∑' r, ψ c h m y r * ∑ z, (cont σ χ c (h ++ [(m, r)]) k).toOuterMeasure
                  {p | guess p = z} := by
                simp only [F, Finset.mul_sum]
                rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
            _ = 1 := by simp_rw [h1, mul_one, PMF.tsum_coe]
            _ ≤ 1 := le_rfl
        have hpt : ∀ x, ∑' r, ψ c h m (φ m x) r *
            (cont σ χ c (h ++ [(m, r)]) k).toOuterMeasure {p | g m x = some (guess p)} =
              (match g m x with
                | some z => F (φ m x) z
                | none => 0) := fun x => by
          rcases hx : g m x with _ | z
          · simp
          · simp only [F, Option.some.injEq]
            exact tsum_congr fun r => by simp_rw [eq_comm]
        calc ∑ x, PMF.uniformOfFintype C x * ∑' r, χ.reply (Function.update c j x) h m r *
              (cont σ χ (Function.update c j x) (h ++ [(m, r)]) k).toOuterMeasure
                (GuessAt w j g guess x)
            ≤ ∑ x, PMF.uniformOfFintype C x * (match g m x with
                | some z => F (φ m x) z
                | none => 0) := by
              gcongr with x _
              rw [← hpt x, hj c x h m hc hw1]
              exact ENNReal.tsum_le_tsum fun r => by
                rw [hlater x r]
                exact mul_le_mul_right (hev x r) _
          _ ≤ γ := sum_uniform_guess_le (φ m) (g m) F (hγ m) hF
      · -- another round: the reply does not read coin `j`
        have hwm := hw m
        have hloc' : ∀ x, χ.reply (Function.update c j x) h m = χ.reply c h m := fun x =>
          hloc c x h m (by omega)
        simp_rw [hloc']
        have hh' : ∀ r, readCount w (h ++ [(m, r)]) ≤ j := fun r => by
          rw [readCount_append, readCount_singleton]
          omega
        calc ∑ x, PMF.uniformOfFintype C x * ∑' r, χ.reply c h m r *
              (cont σ χ (Function.update c j x) (h ++ [(m, r)]) k).toOuterMeasure
                (GuessAt w j g guess x)
            = ∑' r, χ.reply c h m r * ∑ x, PMF.uniformOfFintype C x *
                (cont σ χ (Function.update c j x) (h ++ [(m, r)]) k).toOuterMeasure
                  (GuessAt w j g guess x) := by
              simp_rw [Finset.mul_sum, ← ENNReal.tsum_mul_left]
              rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
              exact tsum_congr fun r => Finset.sum_congr rfl fun x _ => by ring
          _ ≤ ∑' r, χ.reply c h m r * γ := by
              gcongr with r
              exact tsum_cont_guess_le hw hin hloc hj hγ c k _ (hh' r)
          _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    calc ∑ x, PMF.uniformOfFintype C x * ∑' m, σ.next (χ.input c) h m * ∑' r,
          χ.reply (Function.update c j x) h m r *
            (cont σ χ (Function.update c j x) (h ++ [(m, r)]) k).toOuterMeasure
              (GuessAt w j g guess x)
        = ∑' m, σ.next (χ.input c) h m * ∑ x, PMF.uniformOfFintype C x * ∑' r,
            χ.reply (Function.update c j x) h m r *
              (cont σ χ (Function.update c j x) (h ++ [(m, r)]) k).toOuterMeasure
                (GuessAt w j g guess x) := by
          simp_rw [Finset.mul_sum, ← ENNReal.tsum_mul_left]
          rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          exact tsum_congr fun m => Finset.sum_congr rfl fun x _ => by ring
      _ ≤ ∑' m, σ.next (χ.input c) h m * γ := by
          gcongr with m
          exact hmove m
      _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
/-- **Resampling one coordinate of a uniform function**: the average of `F` over a uniform `c` is
the average over a uniform `c` and a uniform `x` of `F` at `c` updated at `j` to `x`. -/
theorem sum_uniform_update (F : (Fin N → C) → ℝ≥0∞) :
    ∑ c, PMF.uniformOfFintype (Fin N → C) c * F c =
      ∑ c, PMF.uniformOfFintype (Fin N → C) c *
        ∑ x, PMF.uniformOfFintype C x * F (Function.update c j x) := by
  classical
  let e : (Fin N → C) × C ≃ (Fin N → C) × C :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hsum : ∑ p : (Fin N → C) × C, F (Function.update p.1 j p.2) =
      ∑ p : (Fin N → C) × C, F p.1 :=
    Fintype.sum_equiv e _ _ fun p => rfl
  simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.sum_prod_type' (f := fun c x => F (Function.update c j x)), hsum,
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- **The guess bound in the experiment**: with uniform coins, one per coin-reading round
(`hcoins`), every strategy outputs the secret of coin `j` with probability at most `γ`. -/
theorem tsum_coins_cont_guess_le {γ : ℝ≥0∞} (hw : ∀ m, w m ≤ 1)
    (hcoins : χ.coins = PMF.uniformOfFintype (Fin N → C))
    (hin : ∀ c x, χ.input (Function.update c j x) = χ.input c)
    (hloc : ∀ c x h m, (readCount w h ≠ j ∨ w m = 0) →
      χ.reply (Function.update c j x) h m = χ.reply c h m)
    (hj : ∀ c x h m, readCount w h = j → w m = 1 →
      χ.reply (Function.update c j x) h m = ψ c h m (φ m x))
    (hγ : ∀ m, ∑ y, ⨆ z,
      (PMF.uniformOfFintype C).toOuterMeasure {x | φ m x = y ∧ g m x = some z} ≤ γ)
    (Q : ℕ) :
    ∑' c, χ.coins c * (cont σ χ c [] Q).toOuterMeasure (GuessAt w j g guess (c j)) ≤ γ := by
  rw [hcoins, tsum_fintype (L := SummationFilter.unconditional _),
    sum_uniform_update j (fun c => (cont σ χ c [] Q).toOuterMeasure (GuessAt w j g guess (c j)))]
  simp only [Function.update_self]
  calc ∑ c, PMF.uniformOfFintype (Fin N → C) c * ∑ x, PMF.uniformOfFintype C x *
        (cont σ χ (Function.update c j x) [] Q).toOuterMeasure (GuessAt w j g guess x)
      ≤ ∑ c, PMF.uniformOfFintype (Fin N → C) c * γ := by
        gcongr with c _
        exact tsum_cont_guess_le σ χ w j φ g guess ψ hw hin hloc hj hγ c Q [] (by simp [readCount])
    _ = γ := by
        rw [← Finset.sum_mul, ← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe,
          one_mul]

end Round

end GordieHowe.Interaction
