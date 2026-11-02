-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.AdaptiveCompleteness

@[expose] public section

/-!
# Searching a random oracle for a label whose predicate holds

A classical `t`-query algorithm (`ROM.Alg`, CY24 p. 20) against a uniform oracle `G : X → Y`
outputs a value with a label `l = lab o`. Each point of `X` carries a label (`κ : X → L`), and a
predicate `P l G` reads `G` only at the points of label `l` (`LocalPred`): a multi-point
predicate, such as the public ring check of a ring `l`, which reads `G` at the points
`(l, j, r)`. If every label's predicate holds with probability at most `ε` over a uniform oracle,
the output's label satisfies its predicate with probability at most `(t + 1) · ε`
(`expect_label_le`).

The proof is a first-touch argument. Either some query has the output's label, and then the
first query with that label is query `i` for one of the `t` indices `i` (`FirstTouch`), or no
query has it (`Untouched`). The event that query `i` is the first with label `l`, and the event
that the output has label `l` and no query has it, read `G` only off the points of label `l`, so
they are independent of `P l` (`expect_mul_eq_of_agree`, the uniform oracle as its values on a
set and off it). Each event has at most one label per oracle, so summing over the labels costs
`ε` for each of the `t + 1` events.

- `expect_mul_eq_of_agree`: a function of the oracle off a set of points and a function of it on
  the set are independent under the uniform oracle.
- `LocalPred`, `FirstTouch`, `Untouched`, `expect_label_le`: the search lemma.
- `expect_sum_weight_le`, `expect_weighted_label_le`: the search lemma for a label drawn from a
  law that the algorithm's output fixes (a challenge measured from a quantum algorithm).
-/

namespace GordieHowe.ROM

open Finset
open scoped BigOperators

/-! ### Independence of an oracle's values on a set and off it -/

section Independence

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The values of a uniform oracle on a set and off it are independent**: for `f` reading the
oracle only off the points `S` and `g` reading it only on `S`, `𝔼 f g = 𝔼 f · 𝔼 g`. The uniform
oracle is the pair of its restrictions to `S` and to the complement
(`Equiv.piEquivPiSubtypeProd`), uniform on the product. -/
theorem expect_mul_eq_of_agree (S : X → Prop) [DecidablePred S] (f g : (X → Y) → ℝ)
    (hf : ∀ G G' : X → Y, (∀ x, ¬ S x → G x = G' x) → f G = f G')
    (hg : ∀ G G' : X → Y, (∀ x, S x → G x = G' x) → g G = g G') :
    𝔼 G, f G * g G = (𝔼 G, f G) * 𝔼 G, g G := by
  obtain ⟨y0⟩ := ‹Nonempty Y›
  let e := Equiv.piEquivPiSubtypeProd S (fun _ : X => Y)
  let f' : ({x // ¬ S x} → Y) → ℝ := fun b => f (e.symm (fun _ => y0, b))
  let g' : ({x // S x} → Y) → ℝ := fun a => g (e.symm (a, fun _ => y0))
  have hf' : ∀ G, f G = f' (e G).2 := fun G => hf _ _ fun x hx => by
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  have hg' : ∀ G, g G = g' (e G).1 := fun G => hg _ _ fun x hx => by
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  have h1 : 𝔼 G, f G * g G = 𝔼 p : ({x // S x} → Y) × ({x // ¬ S x} → Y), f' p.2 * g' p.1 :=
    Fintype.expect_equiv e _ _ fun G => by rw [hf', hg']
  have h2 : 𝔼 G, f G = 𝔼 p : ({x // S x} → Y) × ({x // ¬ S x} → Y), f' p.2 :=
    Fintype.expect_equiv e _ _ fun G => hf' G
  have h3 : 𝔼 G, g G = 𝔼 p : ({x // S x} → Y) × ({x // ¬ S x} → Y), g' p.1 :=
    Fintype.expect_equiv e _ _ fun G => hg' G
  rw [h1, h2, h3, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_product,
    Finset.expect_product]
  simp only [Fintype.expect_const, ← Finset.expect_mul, ← Finset.mul_expect]

end Independence

/-! ### The search lemma -/

section Search

variable {X Y L C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype L] [DecidableEq L] {t : ℕ}

/-- **A predicate of the labels that reads the oracle at the points of its label only**: `P l G`
depends on `G` only through the values `G x` with `κ x = l`. -/
def LocalPred (κ : X → L) (P : L → (X → Y) → Prop) : Prop :=
  ∀ l (G G' : X → Y), (∀ x, κ x = l → G x = G' x) → (P l G ↔ P l G')

/-- **Query `i` is the first with label `l`**: query `i` of `𝒜` against `G` has label `l` and
none of the earlier queries does. -/
def FirstTouch (κ : X → L) (𝒜 : Alg X Y C t) (i : ℕ) (l : L) (G : X → Y) : Prop :=
  κ (𝒜.queryAt G i) = l ∧ ∀ x ∈ 𝒜.queries G i, κ x ≠ l

/-- **The output has label `l` and no query does.** -/
def Untouched (κ : X → L) (lab : C → L) (𝒜 : Alg X Y C t) (l : L) (G : X → Y) : Prop :=
  lab (𝒜.output G) = l ∧ ∀ x ∈ 𝒜.queries G t, κ x ≠ l

variable (κ : X → L) (𝒜 : Alg X Y C t)

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype L] [DecidableEq L] in
/-- **The first touch reads the oracle off the label's points only.** -/
theorem firstTouch_of_agree {i : ℕ} {l : L} {G G' : X → Y} (hag : ∀ x, κ x ≠ l → G x = G' x)
    (h : FirstTouch κ 𝒜 i l G) : FirstTouch κ 𝒜 i l G' := by
  have hq : 𝒜.queries G' i = 𝒜.queries G i :=
    𝒜.queries_eq_of_agree i fun a ha => (hag a (h.2 a ha)).symm
  have hat : 𝒜.queryAt G' i = 𝒜.queryAt G i := by
    rw [Alg.queryAt, Alg.queryAt, hq, List.map_congr_left fun a ha => (hag a (h.2 a ha)).symm]
  exact ⟨hat ▸ h.1, hq ▸ h.2⟩

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype L] [DecidableEq L] in
/-- **The untouched output reads the oracle off the label's points only.** -/
theorem untouched_of_agree (lab : C → L) {l : L} {G G' : X → Y}
    (hag : ∀ x, κ x ≠ l → G x = G' x) (h : Untouched κ lab 𝒜 l G) : Untouched κ lab 𝒜 l G' := by
  have hq : 𝒜.queries G' t = 𝒜.queries G t :=
    𝒜.queries_eq_of_agree t fun a ha => (hag a (h.2 a ha)).symm
  have ho : 𝒜.output G' = 𝒜.output G := 𝒜.output_eq_of_agree fun a ha => (hag a (h.2 a ha)).symm
  exact ⟨ho ▸ h.1, hq ▸ h.2⟩

open Classical in
/-- **One event with at most one label per oracle, against the predicate**: for events `E l`
reading the oracle off the points of label `l`, holding for at most one label at each oracle,
`𝔼_G ∑_l 1[E l G ∧ P l G] ≤ ε`. -/
theorem expect_sum_event_le (P : L → (X → Y) → Prop) (hP : LocalPred κ P) {ε : ℝ}
    (hε : ∀ l, 𝔼 G, (if P l G then 1 else 0 : ℝ) ≤ ε) (hε0 : 0 ≤ ε) (E : L → (X → Y) → Prop)
    (hE : ∀ l (G G' : X → Y), (∀ x, κ x ≠ l → G x = G' x) → E l G → E l G')
    (hone : ∀ G l l', E l G → E l' G → l = l') :
    𝔼 G, ∑ l, (if E l G ∧ P l G then 1 else 0 : ℝ) ≤ ε := by
  have hsplit : ∀ l G, (if E l G ∧ P l G then 1 else 0 : ℝ) =
      (if E l G then 1 else 0) * (if P l G then 1 else 0) := fun l G => by
    by_cases h1 : E l G <;> by_cases h2 : P l G <;> simp [h1, h2]
  have hind : ∀ l, 𝔼 G, (if E l G ∧ P l G then 1 else 0 : ℝ) =
      (𝔼 G, (if E l G then 1 else 0 : ℝ)) * 𝔼 G, (if P l G then 1 else 0 : ℝ) := fun l => by
    simp only [hsplit]
    refine expect_mul_eq_of_agree (fun x => κ x = l) _ _ (fun G G' hag => ?_)
      (fun G G' hag => ?_)
    · have h1 : E l G ↔ E l G' := ⟨hE l G G' hag, hE l G' G fun x hx => (hag x hx).symm⟩
      simp only [h1]
    · simp only [hP l G G' hag]
  have hsum1 : ∀ G, ∑ l, (if E l G then 1 else 0 : ℝ) ≤ 1 := fun G => by
    by_cases h : ∃ l, E l G
    · obtain ⟨l, hl⟩ := h
      rw [Finset.sum_eq_single l (fun l' _ hne => if_neg fun h' => hne (hone G l' l h' hl))
        (fun h => absurd (mem_univ l) h), if_pos hl]
    · push Not at h
      simp [h]
  rw [Finset.expect_sum_comm]
  calc ∑ l, 𝔼 G, (if E l G ∧ P l G then 1 else 0 : ℝ)
      ≤ ∑ l, (𝔼 G, (if E l G then 1 else 0 : ℝ)) * ε := Finset.sum_le_sum fun l _ => by
        rw [hind l]
        exact mul_le_mul_of_nonneg_left (hε l)
          (Finset.expect_nonneg fun G _ => by split_ifs <;> norm_num)
    _ = (𝔼 G, ∑ l, (if E l G then 1 else 0 : ℝ)) * ε := by
        rw [← Finset.sum_mul, Finset.expect_sum_comm]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right
        ((Finset.expect_le_expect fun G _ => hsum1 G).trans_eq (Fintype.expect_const 1)) hε0
    _ = ε := one_mul ε

open Classical in
/-- **The search lemma** (adaptive, multi-point predicate): for a deterministic classical
`t`-query algorithm `𝒜` (`ROM.Alg`, CY24 p. 20) against a uniform oracle, a labelling `lab` of
its outputs, and a predicate `P` of the labels that reads the oracle only at the points of its
label (`LocalPred`) and holds for each label with probability at most `ε`, the output's label
satisfies its predicate with probability at most `(t + 1) · ε`:
`𝔼_G 1[P (lab (𝒜.output G)) G] ≤ (t + 1) · ε`. The `t + 1` counts the first queries of the
labels the queries touch and the output's label when no query touches it. -/
theorem expect_label_le (P : L → (X → Y) → Prop) (hP : LocalPred κ P) {ε : ℝ}
    (hε : ∀ l, 𝔼 G, (if P l G then 1 else 0 : ℝ) ≤ ε) (lab : C → L) :
    𝔼 G, (if P (lab (𝒜.output G)) G then 1 else 0 : ℝ) ≤ (t + 1) * ε := by
  obtain ⟨y0⟩ := ‹Nonempty Y›
  have hε0 : 0 ≤ ε := (Finset.expect_nonneg fun G _ => by split_ifs <;> norm_num).trans
    (hε (lab (𝒜.output fun _ => y0)))
  have hcover : ∀ G, (if P (lab (𝒜.output G)) G then 1 else 0 : ℝ) ≤
      ∑ i : Fin t, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) +
        ∑ l, (if Untouched κ lab 𝒜 l G ∧ P l G then 1 else 0 : ℝ) := fun G => by
    have hnn : 0 ≤ ∑ i : Fin t, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => by split_ifs <;> norm_num
    have hnn' : 0 ≤ ∑ l, (if Untouched κ lab 𝒜 l G ∧ P l G then 1 else 0 : ℝ) :=
      Finset.sum_nonneg fun l _ => by split_ifs <;> norm_num
    split_ifs with hPo
    · set l := lab (𝒜.output G)
      by_cases hT : ∃ x ∈ 𝒜.queries G t, κ x = l
      · obtain ⟨j, hj, h0, h1⟩ := Alg.exists_step_of (P := fun i => ∃ x ∈ 𝒜.queries G i, κ x = l)
          (by simp [Alg.queries]) hT
        have hft : FirstTouch κ 𝒜 j l G := by
          refine ⟨?_, fun x hx hxl => h0 ⟨x, hx, hxl⟩⟩
          obtain ⟨x, hx, hxl⟩ := h1
          rw [Alg.queries_succ, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact absurd ⟨x, hx, hxl⟩ h0
          · exact hxl
        have h1le : (1 : ℝ) ≤ ∑ l', (if FirstTouch κ 𝒜 (⟨j, hj⟩ : Fin t) l' G ∧ P l' G
            then 1 else 0 : ℝ) := by
          refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun l' =>
            (if FirstTouch κ 𝒜 (⟨j, hj⟩ : Fin t) l' G ∧ P l' G then 1 else 0 : ℝ))
            (fun l' _ => by split_ifs <;> norm_num) (mem_univ l))
          exact (if_pos ⟨hft, hPo⟩).symm
        have h2 := Finset.single_le_sum (f := fun i : Fin t => ∑ l',
          (if FirstTouch κ 𝒜 i l' G ∧ P l' G then 1 else 0 : ℝ))
          (fun i _ => Finset.sum_nonneg fun l _ => by split_ifs <;> norm_num) (mem_univ ⟨j, hj⟩)
        linarith
      · push Not at hT
        have h1le : (1 : ℝ) ≤ ∑ l', (if Untouched κ lab 𝒜 l' G ∧ P l' G then 1 else 0 : ℝ) := by
          refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun l' =>
            (if Untouched κ lab 𝒜 l' G ∧ P l' G then 1 else 0 : ℝ))
            (fun l' _ => by split_ifs <;> norm_num) (mem_univ l))
          exact (if_pos ⟨⟨rfl, hT⟩, hPo⟩).symm
        linarith
    · linarith
  refine (Finset.expect_le_expect fun G _ => hcover G).trans ?_
  rw [Finset.expect_add_distrib, Finset.expect_sum_comm]
  have hft : ∀ i : Fin t, 𝔼 G, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) ≤ ε :=
    fun i => expect_sum_event_le κ P hP hε hε0 (fun l G => FirstTouch κ 𝒜 i l G)
      (fun l G G' hag h => firstTouch_of_agree κ 𝒜 hag h) fun G l l' h h' => h.1.symm.trans h'.1
  have hun : 𝔼 G, ∑ l, (if Untouched κ lab 𝒜 l G ∧ P l G then 1 else 0 : ℝ) ≤ ε :=
    expect_sum_event_le κ P hP hε hε0 (fun l G => Untouched κ lab 𝒜 l G)
      (fun l G G' hag h => untouched_of_agree κ 𝒜 lab hag h) fun G l l' h h' => h.1.symm.trans h'.1
  calc ∑ i : Fin t, 𝔼 G, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) +
        𝔼 G, ∑ l, (if Untouched κ lab 𝒜 l G ∧ P l G then 1 else 0 : ℝ)
      ≤ ∑ _i : Fin t, ε + ε := add_le_add (Finset.sum_le_sum fun i _ => hft i) hun
    _ = (t + 1) * ε := by simp; ring

open Classical in
/-- **Weighted events of total weight at most one per oracle, against the predicate**: for
weights `f l` reading the oracle off the points of label `l`, nonnegative and of total weight at
most one at each oracle, `𝔼_G ∑_l f l G · 1[P l G] ≤ ε` (`expect_mul_eq_of_agree`). -/
theorem expect_sum_weight_le (P : L → (X → Y) → Prop) (hP : LocalPred κ P) {ε : ℝ}
    (hε : ∀ l, 𝔼 G, (if P l G then 1 else 0 : ℝ) ≤ ε) (hε0 : 0 ≤ ε) (f : L → (X → Y) → ℝ)
    (hf0 : ∀ l G, 0 ≤ f l G)
    (hf : ∀ l (G G' : X → Y), (∀ x, κ x ≠ l → G x = G' x) → f l G = f l G')
    (hf1 : ∀ G, ∑ l, f l G ≤ 1) :
    𝔼 G, ∑ l, f l G * (if P l G then 1 else 0 : ℝ) ≤ ε := by
  have hind : ∀ l, 𝔼 G, f l G * (if P l G then 1 else 0 : ℝ) =
      (𝔼 G, f l G) * 𝔼 G, (if P l G then 1 else 0 : ℝ) := fun l =>
    expect_mul_eq_of_agree (fun x => κ x = l) _ _ (fun G G' hag => hf l G G' hag)
      (fun G G' hag => by simp only [hP l G G' hag])
  rw [Finset.expect_sum_comm]
  calc ∑ l, 𝔼 G, f l G * (if P l G then 1 else 0 : ℝ)
      ≤ ∑ l, (𝔼 G, f l G) * ε := Finset.sum_le_sum fun l _ => by
        rw [hind l]
        exact mul_le_mul_of_nonneg_left (hε l) (Finset.expect_nonneg fun G _ => hf0 l G)
    _ = (𝔼 G, ∑ l, f l G) * ε := by rw [← Finset.sum_mul, Finset.expect_sum_comm]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right
        ((Finset.expect_le_expect fun G _ => hf1 G).trans_eq (Fintype.expect_const 1)) hε0
    _ = ε := one_mul ε

open Classical in
/-- **The search lemma for a randomized choice of the label** (adaptive, multi-point predicate):
for a deterministic classical `t`-query algorithm `𝒜` (`ROM.Alg`, CY24 p. 20) against a uniform
oracle whose output `c` fixes a law `w c` of total weight at most one over the labels (for
instance the law of the ring of a challenge measured from a quantum algorithm that `c` describes),
and a predicate `P` of the labels that reads the oracle only at the points of its label
(`LocalPred`) and holds for each label with probability at most `ε ≥ 0`, the label drawn from
`w (𝒜.output G)` satisfies its predicate with probability at most `(t + 1) · ε`:
`𝔼_G ∑_l w (𝒜.output G) l · 1[P l G] ≤ (t + 1) · ε`. The proof is that of `expect_label_le`,
with the untouched labels weighted by `w`. -/
theorem expect_weighted_label_le (P : L → (X → Y) → Prop) (hP : LocalPred κ P) {ε : ℝ}
    (hε : ∀ l, 𝔼 G, (if P l G then 1 else 0 : ℝ) ≤ ε) (hε0 : 0 ≤ ε) (w : C → L → ℝ)
    (hw0 : ∀ c l, 0 ≤ w c l) (hw1 : ∀ c, ∑ l, w c l ≤ 1) :
    𝔼 G, ∑ l, w (𝒜.output G) l * (if P l G then 1 else 0 : ℝ) ≤ (t + 1) * ε := by
  have hw1' : ∀ c l, w c l ≤ 1 := fun c l =>
    (Finset.single_le_sum (fun l _ => hw0 c l) (mem_univ l)).trans (hw1 c)
  set f : L → (X → Y) → ℝ := fun l G =>
    w (𝒜.output G) l * (if ∀ x ∈ 𝒜.queries G t, κ x ≠ l then 1 else 0) with hfdef
  have hcover : ∀ G, ∑ l, w (𝒜.output G) l * (if P l G then 1 else 0 : ℝ) ≤
      ∑ i : Fin t, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) +
        ∑ l, f l G * (if P l G then 1 else 0 : ℝ) := fun G => by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    have hnn : 0 ≤ ∑ i : Fin t, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    have hfl0 : 0 ≤ f l G := mul_nonneg (hw0 _ _) (by split_ifs <;> norm_num)
    by_cases hPl : P l G
    · rw [if_pos hPl, mul_one, mul_one]
      by_cases hT : ∃ x ∈ 𝒜.queries G t, κ x = l
      · obtain ⟨j, hj, h0, h1⟩ := Alg.exists_step_of (P := fun i => ∃ x ∈ 𝒜.queries G i, κ x = l)
          (by simp [Alg.queries]) hT
        have hft : FirstTouch κ 𝒜 j l G := by
          refine ⟨?_, fun x hx hxl => h0 ⟨x, hx, hxl⟩⟩
          obtain ⟨x, hx, hxl⟩ := h1
          rw [Alg.queries_succ, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact absurd ⟨x, hx, hxl⟩ h0
          · exact hxl
        have h1le : (1 : ℝ) ≤ ∑ i : Fin t, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) := by
          refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun i : Fin t =>
            (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ))
            (fun i _ => by split_ifs <;> norm_num) (mem_univ ⟨j, hj⟩))
          exact (if_pos ⟨hft, hPl⟩).symm
        linarith [hw1' (𝒜.output G) l]
      · push Not at hT
        have hfw : f l G = w (𝒜.output G) l := by simp only [hfdef, if_pos hT, mul_one]
        linarith
    · rw [if_neg hPl, mul_zero, mul_zero, add_zero]
      exact hnn
  have hfagree : ∀ l (G G' : X → Y), (∀ x, κ x ≠ l → G x = G' x) →
      (∀ x ∈ 𝒜.queries G t, κ x ≠ l) → f l G = f l G' := fun l G G' hag hu => by
    have hq : 𝒜.queries G' t = 𝒜.queries G t :=
      𝒜.queries_eq_of_agree t fun a ha => (hag a (hu a ha)).symm
    have ho : 𝒜.output G' = 𝒜.output G :=
      𝒜.output_eq_of_agree fun a ha => (hag a (hu a ha)).symm
    simp only [hfdef, hq, ho]
  have hf : ∀ l (G G' : X → Y), (∀ x, κ x ≠ l → G x = G' x) → f l G = f l G' := by
    intro l G G' hag
    by_cases hu : ∀ x ∈ 𝒜.queries G t, κ x ≠ l
    · exact hfagree l G G' hag hu
    · by_cases hu' : ∀ x ∈ 𝒜.queries G' t, κ x ≠ l
      · exact (hfagree l G' G (fun x hx => (hag x hx).symm) hu').symm
      · simp only [hfdef, if_neg hu, if_neg hu', mul_zero]
  have hf0 : ∀ l G, 0 ≤ f l G := fun l G =>
    mul_nonneg (hw0 _ _) (by split_ifs <;> norm_num)
  have hf1 : ∀ G, ∑ l, f l G ≤ 1 := fun G =>
    (Finset.sum_le_sum fun l _ => mul_le_of_le_one_right (hw0 _ _)
      (by split_ifs <;> norm_num)).trans (hw1 _)
  refine (Finset.expect_le_expect fun G _ => hcover G).trans ?_
  rw [Finset.expect_add_distrib, Finset.expect_sum_comm]
  have hft : ∀ i : Fin t, 𝔼 G, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) ≤ ε :=
    fun i => expect_sum_event_le κ P hP hε hε0 (fun l G => FirstTouch κ 𝒜 i l G)
      (fun l G G' hag h => firstTouch_of_agree κ 𝒜 hag h) fun G l l' h h' => h.1.symm.trans h'.1
  have hun := expect_sum_weight_le κ P hP hε hε0 f hf0 hf hf1
  calc ∑ i : Fin t, 𝔼 G, ∑ l, (if FirstTouch κ 𝒜 i l G ∧ P l G then 1 else 0 : ℝ) +
        𝔼 G, ∑ l, f l G * (if P l G then 1 else 0 : ℝ)
      ≤ ∑ _i : Fin t, ε + ε := add_le_add (Finset.sum_le_sum fun i _ => hft i) hun
    _ = (t + 1) * ε := by simp; ring

end Search

end GordieHowe.ROM
