-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV
public import Mathlib.Algebra.BigOperators.Expect

@[expose] public section

/-!
# Oracles with uniform base components at labelled points

An oracle `H : X → Y` whose values split as `e : Y ≃ Y₁ × Y₂` (a base component in `Y₁` and a
second component in `Y₂`), with points labelled by `κ : X → Option L` (a point has at most one
label; `none` is unlabelled). The **blocks** of `H` are its base components at the points of each
label (`labelBlocks`); the rest of `H` is its values at the unlabelled points and its second
components everywhere. Two oracles **agree off the labels** if they have the same rest
(`AgreeOffLabels`). `setLabelBlocks H u` replaces the blocks of `H` by `u`.

A law of the oracle is **uniform on the labels** if two oracles that agree off the labels have the
same probability (`IsUniformOnLabels`): given the rest, the blocks are uniform. This is the form of
`IsUniformOnRange` (`GordieHowe/Model/Quantum/O2H/SaltReprogram.lean`) for components. The uniform
law satisfies it (`isUniformOnLabels_uniform`), and so does the uniform law conditioned on the rest
(`offLabelsLaw`, `isUniformOnLabels_offLabelsLaw`).

- `setLabelBlocks_eq_of_agree`: oracles that agree off the labels give the same oracle with
  replaced blocks. `ReadsBlocks e κ P`: `P l H` depends on `H` only through its block at `l`; then
  it is `blockPred e κ P l` of that block (`ReadsBlocks.blockPred_iff`).
- `agreeOffLabels_of_offLabelsLaw_ne_zero`: the conditioned law is supported on the class of
  `H₀`; `expect_setLabelBlocks_eq`: averaging uniform blocks on `H₀` is averaging under
  `offLabelsLaw e κ H₀`.
- `IsUniformOnLabels.sum_mul_eq`: under such a law, an average over the oracle is the average over
  the oracle of the average over its blocks replaced by uniform blocks.
- `IsUniformOnLabels.toReal_toOuterMeasure_eq`, `IsUniformOnLabels.toReal_uniform_eq`: so an
  event of the blocks of the oracle has the probability it has for uniform blocks
  (`PMF.toReal_toOuterMeasure_uniformOfFintype`: the fraction of the outcomes in it).

**Splitting uniform blocks at a predicate.** For a predicate `P l` of the blocks of label `l`
(the **marked** blocks), `unmarkedBlocks P l` is the set of unmarked blocks of label `l`, or every
block if all are marked. With `a` uniform on the unmarked blocks (`Fintype.piFinset`) and `σ`
uniform, `mixBlocks P a σ` takes at each label the block of `σ` if it is marked and the block of
`a` otherwise; it is uniform (`sum_sum_mix_eq_card`, `sum_sum_mixBlocks`; with the laws `unmarkedLaw P` and the
uniform law, `sum_unmarkedLaw_mixBlocks`; `piFinset_unmarkedBlocks_nonempty`,
`mem_piFinset_of_unmarkedLaw_ne_zero`). A block of `mixBlocks P a σ` is marked only if
the block of `σ` is (`marked_of_mixBlocks`), and it is the block of `a` if not
(`mixBlocks_of_not`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

variable {X Y Y₁ Y₂ L : Type*} (e : Y ≃ Y₁ × Y₂) (κ : X → Option L)

/-- **The blocks of the labels**: a base component at each point of each label. -/
abbrev LabelBlocks (κ : X → Option L) (Y₁ : Type*) := (l : L) → {x // κ x = some l} → Y₁

/-- **The blocks of an oracle**: its base components at the points of each label. -/
def labelBlocks (H : X → Y) : LabelBlocks κ Y₁ :=
  fun _ x => (e (H x.1)).1

/-- **Two oracles agree off the labels**: the same values at the unlabelled points, and the same
second components everywhere. -/
def AgreeOffLabels (H H' : X → Y) : Prop :=
  ∀ x, (κ x = none → H x = H' x) ∧ (e (H x)).2 = (e (H' x)).2

/-- **The oracle with its blocks replaced by `u`**: at a point of label `l`, the base component of
`u` and the second component of `H`; at an unlabelled point, `H`. -/
def setLabelBlocks (H : X → Y) (u : LabelBlocks κ Y₁) : X → Y := fun x =>
  match h : κ x with
  | none => H x
  | some l => e.symm (u l ⟨x, h⟩, (e (H x)).2)

/-- **A law of the oracle that is uniform on the labels given the rest**: two oracles that agree
off the labels have the same probability. -/
def IsUniformOnLabels (μH : PMF (X → Y)) : Prop :=
  ∀ H H', AgreeOffLabels e κ H H' → μH H = μH H'

variable {e κ}

/-- At an unlabelled point, the oracle with replaced blocks is the oracle. -/
theorem setLabelBlocks_of_none {H : X → Y} (u : LabelBlocks κ Y₁) {x : X} (hx : κ x = none) :
    setLabelBlocks e κ H u x = H x := by
  unfold setLabelBlocks
  split
  · rfl
  · simp_all

/-- At a point of label `l`, the oracle with replaced blocks has the base component of the block
of `l` and the second component of the oracle. -/
theorem setLabelBlocks_of_some {H : X → Y} (u : LabelBlocks κ Y₁) {x : X} {l : L}
    (hx : κ x = some l) : setLabelBlocks e κ H u x = e.symm (u l ⟨x, hx⟩, (e (H x)).2) := by
  unfold setLabelBlocks
  split
  · simp_all
  · rename_i l' h
    obtain rfl : l' = l := Option.some_injective _ (h.symm.trans hx)
    rfl

/-- The blocks of the oracle with replaced blocks are the replacement. -/
@[simp]
theorem labelBlocks_setLabelBlocks (H : X → Y) (u : LabelBlocks κ Y₁) :
    labelBlocks e κ (setLabelBlocks e κ H u) = u := by
  funext l x
  simp [labelBlocks, setLabelBlocks_of_some u x.2]

/-- An oracle agrees with itself off the labels. -/
theorem AgreeOffLabels.refl (H : X → Y) : AgreeOffLabels e κ H H := fun _ => ⟨fun _ => rfl, rfl⟩

/-- Agreement off the labels is symmetric. -/
theorem AgreeOffLabels.symm {H H' : X → Y} (h : AgreeOffLabels e κ H H') :
    AgreeOffLabels e κ H' H := fun x => ⟨fun hx => ((h x).1 hx).symm, (h x).2.symm⟩

/-- Agreement off the labels is transitive. -/
theorem AgreeOffLabels.trans {H H' H'' : X → Y} (h : AgreeOffLabels e κ H H')
    (h' : AgreeOffLabels e κ H' H'') : AgreeOffLabels e κ H H'' := fun x =>
  ⟨fun hx => ((h x).1 hx).trans ((h' x).1 hx), (h x).2.trans (h' x).2⟩

/-- Replacing the blocks keeps the rest. -/
theorem agreeOffLabels_setLabelBlocks (H : X → Y) (u : LabelBlocks κ Y₁) :
    AgreeOffLabels e κ H (setLabelBlocks e κ H u) := fun x => by
  refine ⟨fun hx => (setLabelBlocks_of_none u hx).symm, ?_⟩
  cases hx : κ x with
  | none => rw [setLabelBlocks_of_none u hx]
  | some l => simp [setLabelBlocks_of_some u hx]

/-- Replacing the blocks twice is replacing them by the second replacement. -/
@[simp]
theorem setLabelBlocks_setLabelBlocks (H : X → Y) (u u' : LabelBlocks κ Y₁) :
    setLabelBlocks e κ (setLabelBlocks e κ H u) u' = setLabelBlocks e κ H u' := by
  funext x
  cases hx : κ x with
  | none => simp [setLabelBlocks_of_none _ hx]
  | some l => simp [setLabelBlocks_of_some _ hx]

/-- An oracle that agrees with `H` off the labels is `H` with its own blocks. -/
theorem setLabelBlocks_labelBlocks_of_agree {H H' : X → Y} (h : AgreeOffLabels e κ H H') :
    setLabelBlocks e κ H (labelBlocks e κ H') = H' := by
  funext x
  cases hx : κ x with
  | none => rw [setLabelBlocks_of_none _ hx, (h x).1 hx]
  | some l =>
    rw [setLabelBlocks_of_some _ hx, (h x).2]
    simp [labelBlocks]

/-- An oracle with its own blocks is the oracle. -/
@[simp]
theorem setLabelBlocks_labelBlocks (H : X → Y) : setLabelBlocks e κ H (labelBlocks e κ H) = H :=
  setLabelBlocks_labelBlocks_of_agree (.refl H)

/-- Replacing the blocks of two oracles that agree off the labels gives the same oracle. -/
theorem setLabelBlocks_eq_of_agree {H H' : X → Y} (h : AgreeOffLabels e κ H H')
    (u : LabelBlocks κ Y₁) : setLabelBlocks e κ H u = setLabelBlocks e κ H' u := by
  rw [← setLabelBlocks_labelBlocks_of_agree h, setLabelBlocks_setLabelBlocks]

variable (e κ) in
/-- **A predicate of the labels that reads only the blocks**: `P l H` depends on `H` only through
its block at `l`. -/
def ReadsBlocks (P : L → (X → Y) → Prop) : Prop :=
  ∀ l H H', labelBlocks e κ H l = labelBlocks e κ H' l → (P l H ↔ P l H')

variable (e κ) in
/-- **A predicate of the labels as a predicate of the blocks**: the block `w` of label `l`
satisfies it if some oracle with block `w` at `l` satisfies `P l`. -/
def blockPred (P : L → (X → Y) → Prop) (l : L) (w : {x // κ x = some l} → Y₁) : Prop :=
  ∃ H, labelBlocks e κ H l = w ∧ P l H

/-- For a predicate that reads only the blocks, `P l H` is `blockPred` of the block of `H`. -/
theorem ReadsBlocks.blockPred_iff {P : L → (X → Y) → Prop} (hP : ReadsBlocks e κ P) (l : L)
    (H : X → Y) : blockPred e κ P l (labelBlocks e κ H l) ↔ P l H :=
  ⟨fun ⟨H', h, hH'⟩ => (hP l H' H h).1 hH', fun h => ⟨H, rfl, h⟩⟩

/-- Under a law uniform on the labels, replacing the blocks keeps the probability. -/
theorem IsUniformOnLabels.apply_setLabelBlocks {μH : PMF (X → Y)} (hμ : IsUniformOnLabels e κ μH)
    (H : X → Y) (u : LabelBlocks κ Y₁) : μH (setLabelBlocks e κ H u) = μH H :=
  (hμ _ _ (agreeOffLabels_setLabelBlocks H u)).symm

/-- **The uniform law is uniform on the labels.** -/
theorem isUniformOnLabels_uniform [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    IsUniformOnLabels e κ (PMF.uniformOfFintype (X → Y)) := fun _ _ _ => by
  simp only [PMF.uniformOfFintype_apply]

section Condition

variable [Fintype X] [DecidableEq X] [Fintype Y] (e κ)

open Classical in
/-- **The oracles that agree with `H₀` off the labels.** -/
noncomputable def offLabelsClass (H₀ : X → Y) : Finset (X → Y) :=
  Finset.univ.filter fun H => AgreeOffLabels e κ H H₀

/-- Membership in `offLabelsClass e κ H₀` is agreement with `H₀` off the labels. -/
theorem mem_offLabelsClass {H₀ H : X → Y} : H ∈ offLabelsClass e κ H₀ ↔ AgreeOffLabels e κ H H₀ := by
  classical
  simp [offLabelsClass]

/-- **The uniform law conditioned on the rest**: uniform on the oracles that agree with `H₀` off
the labels. -/
noncomputable def offLabelsLaw (H₀ : X → Y) : PMF (X → Y) :=
  PMF.uniformOfFinset (offLabelsClass e κ H₀)
    (show (offLabelsClass e κ H₀).Nonempty from ⟨H₀, (mem_offLabelsClass e κ).2 (.refl H₀)⟩)

variable {e κ}

/-- **The uniform law conditioned on the rest is uniform on the labels.** -/
theorem isUniformOnLabels_offLabelsLaw (H₀ : X → Y) :
    IsUniformOnLabels e κ (offLabelsLaw e κ H₀) := fun H H' h => by
  classical
  have : H ∈ offLabelsClass e κ H₀ ↔ H' ∈ offLabelsClass e κ H₀ := by
    simp only [mem_offLabelsClass]
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  rw [offLabelsLaw, PMF.uniformOfFinset_apply, PMF.uniformOfFinset_apply]
  by_cases h1 : H ∈ offLabelsClass e κ H₀
  · rw [if_pos h1, if_pos (this.1 h1)]
  · rw [if_neg h1, if_neg (mt this.2 h1)]

/-- **The conditioned law is supported on the oracles that agree with `H₀` off the labels.** -/
theorem agreeOffLabels_of_offLabelsLaw_ne_zero {H₀ H : X → Y} (h : offLabelsLaw e κ H₀ H ≠ 0) :
    AgreeOffLabels e κ H H₀ :=
  (mem_offLabelsClass e κ).1 ((PMF.mem_support_uniformOfFinset_iff _ _).1 h)

end Condition

/-! ### Averaging over the blocks -/

section Average

variable [Fintype X] [DecidableEq X] [Fintype Y] [Fintype L] [DecidableEq L] [Fintype Y₁]

/-- **Under a law uniform on the labels, the blocks may be resampled uniformly**: an average over
the oracle `H ← μH` is the average over `H ← μH` of the uniform average over blocks `u` of the
oracle with blocks `u`. The proof is the involution `(H, u) ↦ (setLabelBlocks H u, labelBlocks H)`,
which keeps `μH` of the first component. -/
theorem IsUniformOnLabels.sum_mul_eq {μH : PMF (X → Y)} (hμ : IsUniformOnLabels e κ μH)
    (g : (X → Y) → ℝ) :
    ∑ H, (μH H).toReal * g H = ∑ H, (μH H).toReal * 𝔼 u, g (setLabelBlocks e κ H u) := by
  rcases isEmpty_or_nonempty (X → Y) with hXY | ⟨⟨H₀⟩⟩
  · simp
  have hB : Nonempty (LabelBlocks κ Y₁) := ⟨labelBlocks e κ H₀⟩
  set Φ : (X → Y) × LabelBlocks κ Y₁ → (X → Y) × LabelBlocks κ Y₁ :=
    fun p => (setLabelBlocks e κ p.1 p.2, labelBlocks e κ p.1)
  have hΦ : Function.Involutive Φ := fun p => by simp [Φ]
  have hc : (Fintype.card (LabelBlocks κ Y₁) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : ∑ H, (μH H).toReal * ∑ u, g (setLabelBlocks e κ H u) =
      Fintype.card (LabelBlocks κ Y₁) * ∑ H, (μH H).toReal * g H := by
    calc ∑ H, (μH H).toReal * ∑ u, g (setLabelBlocks e κ H u)
        = ∑ p : (X → Y) × LabelBlocks κ Y₁, (μH (Φ p).1).toReal * g (Φ p).1 := by
          rw [Fintype.sum_prod_type]
          refine sum_congr rfl fun H _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun u _ => by simp [Φ, hμ.apply_setLabelBlocks]
      _ = ∑ p : (X → Y) × LabelBlocks κ Y₁, (μH p.1).toReal * g p.1 :=
          Equiv.sum_comp hΦ.toPerm (fun p => (μH p.1).toReal * g p.1)
      _ = Fintype.card (LabelBlocks κ Y₁) * ∑ H, (μH H).toReal * g H := by
          rw [Fintype.sum_prod_type, mul_sum]
          simp [mul_comm]
  have hexp : ∀ H, 𝔼 u, g (setLabelBlocks e κ H u) =
      (∑ u, g (setLabelBlocks e κ H u)) / Fintype.card (LabelBlocks κ Y₁) := fun H => by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ]
  simp only [hexp, mul_div_assoc', ← sum_div, key]
  field_simp

/-- **An event of the blocks has the probability it has for uniform blocks**, under a law uniform
on the labels: the fraction of the blocks in the event. -/
theorem IsUniformOnLabels.toReal_toOuterMeasure_eq {μH : PMF (X → Y)}
    (hμ : IsUniformOnLabels e κ μH) (B : Set (LabelBlocks κ Y₁)) [DecidablePred (· ∈ B)] :
    (μH.toOuterMeasure {H | labelBlocks e κ H ∈ B}).toReal =
      (univ.filter (· ∈ B)).card / Fintype.card (LabelBlocks κ Y₁) := by
  classical
  rw [PMF.toReal_toOuterMeasure_apply]
  have h := hμ.sum_mul_eq (fun H => if labelBlocks e κ H ∈ B then 1 else 0)
  simp only [labelBlocks_setLabelBlocks, mul_ite, mul_one, mul_zero] at h
  simp only [Set.mem_ofPred_eq]
  rw [h, Finset.expect_eq_sum_div_card, Finset.card_univ, ← sum_mul, μH.sum_toReal, one_mul,
    sum_boole]

/-- **Uniform blocks on a fixed rest are the conditioned law**: the uniform average over blocks
`u` of `g` of `H₀` with blocks `u` is the average of `g` under `offLabelsLaw e κ H₀`. -/
theorem expect_setLabelBlocks_eq (H₀ : X → Y) (g : (X → Y) → ℝ) :
    𝔼 u, g (setLabelBlocks e κ H₀ u) = ∑ H, (offLabelsLaw e κ H₀ H).toReal * g H := by
  rw [(isUniformOnLabels_offLabelsLaw H₀).sum_mul_eq g]
  have h : ∀ H, (offLabelsLaw e κ H₀ H).toReal * 𝔼 u, g (setLabelBlocks e κ H u) =
      (offLabelsLaw e κ H₀ H).toReal * 𝔼 u, g (setLabelBlocks e κ H₀ u) := fun H => by
    by_cases h0 : offLabelsLaw e κ H₀ H = 0
    · simp [h0]
    · simp only [setLabelBlocks_eq_of_agree (agreeOffLabels_of_offLabelsLaw_ne_zero h0)]
  simp only [h, ← sum_mul, PMF.sum_toReal, one_mul]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Fintype L] [DecidableEq L] [Fintype Y₁] in
/-- The probability of an event under a uniform law, in `ℝ`: the fraction of the outcomes in it. -/
theorem _root_.PMF.toReal_toOuterMeasure_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [DecidablePred (· ∈ s)] :
    ((PMF.uniformOfFintype α).toOuterMeasure s).toReal =
      (univ.filter (· ∈ s)).card / Fintype.card α := by
  rw [PMF.toReal_toOuterMeasure_apply]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Uniform blocks have the probabilities of the blocks of the oracle**, under a law uniform on
the labels. -/
theorem IsUniformOnLabels.toReal_uniform_eq {μH : PMF (X → Y)} (hμ : IsUniformOnLabels e κ μH)
    [Nonempty (LabelBlocks κ Y₁)] (B : Set (LabelBlocks κ Y₁)) :
    ((PMF.uniformOfFintype (LabelBlocks κ Y₁)).toOuterMeasure B).toReal =
      (μH.toOuterMeasure {H | labelBlocks e κ H ∈ B}).toReal := by
  classical
  rw [hμ.toReal_toOuterMeasure_eq, PMF.toReal_toOuterMeasure_uniformOfFintype]

end Average

/-! ### Splitting uniform blocks at a predicate -/

section Mix

variable [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L] [Fintype Y₁] [DecidableEq Y₁]
  (P : (l : L) → ({x // κ x = some l} → Y₁) → Prop) [∀ l, DecidablePred (P l)]

/-- **The unmarked blocks of label `l`**: the blocks not satisfying `P l`, or every block if all
satisfy it. -/
def unmarkedBlocks (l : L) : Finset ({x // κ x = some l} → Y₁) :=
  if (univ.filter fun w => ¬ P l w).Nonempty then univ.filter fun w => ¬ P l w else univ

/-- **The blocks of `σ` where they are marked, of `a` elsewhere.** -/
def mixBlocks (a σ : LabelBlocks κ Y₁) : LabelBlocks κ Y₁ :=
  fun l => if P l (σ l) then σ l else a l

variable {P}

omit [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L] [Fintype Y₁] [DecidableEq Y₁] in
/-- Where the block of `σ` is not marked, the mixed block is the block of `a`. -/
theorem mixBlocks_of_not {a σ : LabelBlocks κ Y₁} {l : L} (h : ¬ P l (σ l)) :
    mixBlocks P a σ l = a l := by
  simp [mixBlocks, h]

omit [DecidableEq Y₁] in
/-- **A mixed block is marked only if the block of `σ` is**, for `a` among the unmarked
blocks. -/
theorem marked_of_mixBlocks {a σ : LabelBlocks κ Y₁}
    (ha : a ∈ Fintype.piFinset (unmarkedBlocks P)) {l : L} (h : P l (mixBlocks P a σ l)) :
    P l (σ l) := by
  by_contra hσ
  rw [mixBlocks_of_not hσ] at h
  have hal := Fintype.mem_piFinset.1 ha l
  unfold unmarkedBlocks at hal
  split_ifs at hal with hne
  · exact (mem_filter.1 hal).2 h
  · exact hne ⟨σ l, mem_filter.2 ⟨mem_univ _, hσ⟩⟩

omit [Fintype L] in
/-- At one label, each block `w` is the mixed block of exactly `#(unmarkedBlocks P l)` pairs of an
unmarked block and a block. -/
theorem sum_sum_mix_eq_card (l : L) (w : {x // κ x = some l} → Y₁) :
    ∑ x ∈ unmarkedBlocks P l, ∑ y, (if (if P l y then y else x) = w then (1 : ℝ) else 0) =
      (unmarkedBlocks P l).card := by
  by_cases hw : P l w
  · have hin : ∀ x ∈ unmarkedBlocks P l, ∀ y, ((if P l y then y else x) = w ↔ y = w) := by
      intro x hx y
      constructor
      · intro h
        split_ifs at h with hy
        · exact h
        · unfold unmarkedBlocks at hx
          split_ifs at hx with hne
          · exact absurd (h ▸ (mem_filter.1 hx).2) (not_not.2 hw)
          · exact absurd ⟨y, mem_filter.2 ⟨mem_univ _, hy⟩⟩ hne
      · rintro rfl
        simp [hw]
    rw [sum_congr rfl fun x hx => sum_congr rfl fun y _ => if_congr (hin x hx y) rfl rfl]
    simp
  · have hne : (univ.filter fun w => ¬ P l w).Nonempty := ⟨w, mem_filter.2 ⟨mem_univ _, hw⟩⟩
    have hU : unmarkedBlocks P l = univ.filter fun w => ¬ P l w := by
      simp [unmarkedBlocks, hne]
    have hin : ∀ x y, ((if P l y then y else x) = w ↔ ¬ P l y ∧ x = w) := by
      intro x y
      by_cases hy : P l y
      · simp only [hy, ↓reduceIte, not_true_eq_false, false_and, iff_false]
        rintro rfl
        exact hw hy
      · simp [hy]
    have hwU : w ∈ unmarkedBlocks P l := by
      rw [hU]
      exact mem_filter.2 ⟨mem_univ _, hw⟩
    calc ∑ x ∈ unmarkedBlocks P l, ∑ y, (if (if P l y then y else x) = w then (1 : ℝ) else 0)
        = ∑ x ∈ unmarkedBlocks P l, (if x = w then (1 : ℝ) else 0) *
            ∑ y, (if ¬ P l y then (1 : ℝ) else 0) := by
          refine sum_congr rfl fun x _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun y _ => ?_
          rw [if_congr (hin x y) rfl rfl]
          by_cases hy : P l y <;> by_cases hx : x = w <;> simp [hy, hx]
      _ = ∑ y, (if ¬ P l y then (1 : ℝ) else 0) := by
          rw [← sum_mul, sum_ite_eq' (unmarkedBlocks P l) w, if_pos hwU, one_mul]
      _ = (unmarkedBlocks P l).card := by
          rw [sum_boole, hU]

/-- **The mixed blocks are uniform**: averaging `f` over `a` uniform on the unmarked blocks and
`σ` uniform gives the uniform average of `f`. -/
theorem sum_sum_mixBlocks (f : LabelBlocks κ Y₁ → ℝ) :
    ∑ a ∈ Fintype.piFinset (unmarkedBlocks P), ∑ σ, f (mixBlocks P a σ) =
      (Fintype.piFinset (unmarkedBlocks P)).card * ∑ u, f u := by
  have hcount : ∀ u : LabelBlocks κ Y₁,
      ∑ a ∈ Fintype.piFinset (unmarkedBlocks P), ∑ σ,
        (if mixBlocks P a σ = u then (1 : ℝ) else 0) =
      (Fintype.piFinset (unmarkedBlocks P)).card := by
    intro u
    have hprod : ∀ a σ : LabelBlocks κ Y₁, (if mixBlocks P a σ = u then (1 : ℝ) else 0) =
        ∏ l, if (if P l (σ l) then σ l else a l) = u l then (1 : ℝ) else 0 := fun a σ => by
      by_cases h : mixBlocks P a σ = u
      · rw [if_pos h]
        exact (prod_eq_one fun l _ => if_pos (congrFun h l)).symm
      · rw [if_neg h]
        obtain ⟨l, hl⟩ := Function.ne_iff.1 h
        exact (prod_eq_zero (mem_univ l) (if_neg hl)).symm
    simp only [hprod]
    rw [sum_congr rfl fun a _ => (Fintype.prod_sum fun l y =>
      if (if P l y then y else a l) = u l then (1 : ℝ) else 0).symm]
    rw [← Finset.prod_univ_sum (t := unmarkedBlocks P)
      (fun l x => ∑ y, if (if P l y then y else x) = u l then (1 : ℝ) else 0)]
    rw [Fintype.card_piFinset, Nat.cast_prod]
    exact prod_congr rfl fun l _ => sum_sum_mix_eq_card l (u l)
  calc ∑ a ∈ Fintype.piFinset (unmarkedBlocks P), ∑ σ, f (mixBlocks P a σ)
      = ∑ a ∈ Fintype.piFinset (unmarkedBlocks P), ∑ σ, ∑ u,
          (if mixBlocks P a σ = u then (1 : ℝ) else 0) * f u := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun σ _ => ?_
        simp
    _ = ∑ u, (∑ a ∈ Fintype.piFinset (unmarkedBlocks P), ∑ σ,
          (if mixBlocks P a σ = u then (1 : ℝ) else 0)) * f u := by
        symm
        simp only [sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]
    _ = (Fintype.piFinset (unmarkedBlocks P)).card * ∑ u, f u := by
        simp only [hcount, mul_sum]

variable (P) [Nonempty (LabelBlocks κ Y₁)]

/-- Some block of every label is unmarked or, if all are marked, a block. -/
theorem piFinset_unmarkedBlocks_nonempty : (Fintype.piFinset (unmarkedBlocks P)).Nonempty := by
  refine Fintype.piFinset_nonempty.2 fun l => ?_
  unfold unmarkedBlocks
  split_ifs with h
  · exact h
  · exact ⟨Classical.arbitrary (LabelBlocks κ Y₁) l, mem_univ _⟩

/-- **The uniform law on the unmarked blocks** (at every label). -/
noncomputable def unmarkedLaw : PMF (LabelBlocks κ Y₁) :=
  PMF.uniformOfFinset _ (piFinset_unmarkedBlocks_nonempty P)

variable {P}

/-- The law on the unmarked blocks is supported on the unmarked blocks. -/
theorem mem_piFinset_of_unmarkedLaw_ne_zero {a : LabelBlocks κ Y₁} (h : unmarkedLaw P a ≠ 0) :
    a ∈ Fintype.piFinset (unmarkedBlocks P) :=
  (PMF.mem_support_uniformOfFinset_iff _ _).1 h

/-- **The mixed blocks are uniform**, for `a ← unmarkedLaw P` and `σ` uniform: the average of
`g` of the mixed blocks is the uniform average of `g`. -/
theorem sum_unmarkedLaw_mixBlocks (g : LabelBlocks κ Y₁ → ℝ) :
    ∑ a, (unmarkedLaw P a).toReal * ∑ σ, (PMF.uniformOfFintype (LabelBlocks κ Y₁) σ).toReal *
      g (mixBlocks P a σ) = 𝔼 u, g u := by
  have hne := piFinset_unmarkedBlocks_nonempty P
  have hc : ((Fintype.piFinset (unmarkedBlocks P)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (card_ne_zero.2 hne)
  have hlaw : ∀ a, (unmarkedLaw P a).toReal = if a ∈ Fintype.piFinset (unmarkedBlocks P) then
      ((Fintype.piFinset (unmarkedBlocks P)).card : ℝ)⁻¹ else 0 := fun a => by
    rw [unmarkedLaw, PMF.uniformOfFinset_apply]
    split_ifs <;> simp
  simp only [hlaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ite_mul, zero_mul, ← mul_sum]
  rw [← sum_filter, Finset.filter_mem_eq_inter, univ_inter]
  simp only [mul_assoc, ← mul_sum]
  rw [sum_sum_mixBlocks, Finset.expect_eq_sum_div_card, card_univ]
  field_simp

end Mix

end GordieHowe.Quantum
