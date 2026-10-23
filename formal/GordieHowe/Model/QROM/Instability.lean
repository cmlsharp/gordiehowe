-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Database
public import GordieHowe.Foundations.Probability.Probability

@[expose] public section

/-!
# Flip probability and instability of database properties

Definitions from Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random
Oracle Model" (CMS19, ePrint 2019/834), section 5, over databases `DB X Y`
(`GordieHowe/Model/QROM/Database.lean`). `Y` is finite and nonempty; `X` may be infinite.

- `flipProb P Q t` is `flip(P → Q, t)` (Def 5.4, p. 21).
- `instab P t` is `I(P, t)` (Def 5.6, p. 22).
- `condFlip P Q t` and `condInstab P Q t` are `flip(P | Q, t)` and `I(P | Q, t)`
  (Def 5.11, p. 24).
- `collision` is `P_col` (p. 32; a collision is `D(x) = D(x')` for distinct `x`, `x'`,
  p. 29), with Lemma 6.11 (p. 33) as `instab_collision_le` and `instab_collision_lt`.

The paper's `max` over databases `D ∈ P` with `|D| < t` and `x ∉ supp(D)` ranges over
a possibly infinite index when `X` is infinite. We take the supremum `⨆` in `ℝ≥0∞`;
it is at most `1` (`flipProb_le_one`) because every term is a probability. The empty
supremum is `0`, which is the paper's convention `flip(∅ → Q) = 0`
(`flipProb_empty_left`); it also covers `t = 0`.

## Paper text

Definition 5.4, p. 21:

    The flip probability flip(P → Q, t) from property P to property Q is the
    quantity
      flip(P → Q, t) :=   max              max       Pr_y [D + [x ↦ y] ∈ Q] ,
                        D : {0,1}^m ⇀ {0,1}^n   x ∉ supp(D)
                        |D| < t, D ∈ P
    and flip(∅ → Q, t) := 0.

Definition 5.6, p. 22:

    The instability I(P, t) of a database property P with query bound t is the
    maximum probability that, for any database D containing less than t queries,
    making one additional (classical) query changes whether or not D has the
    property P. Formally, we let
      I(P, t) := max{flip(P̄ → P, t), flip(P → P̄, t)} .

Definition 5.11, p. 24:

    Let P and Q be two database properties, and let t be a query bound. We define
      flip(P | Q, t) := flip(P̄ ∩ Q → P ∩ Q, t) .
    The conditional instability I(P | Q, t) is defined as
      I(P | Q, t) := max{flip(P | Q, t), flip(P̄ | Q, t)} .

Correspondence: `flipProb`, `instab`, `condFlip`, `condInstab` are these four
quantities, with `X` for `{0,1}^m`, a finite nonempty `Y` for `{0,1}^n` (instantiated
at bit strings), `y` uniform on `Y`, and `max` replaced by `⨆` as above.
-/

namespace GordieHowe.QROM

open GordieHowe.IOP
open scoped ENNReal

section Prob

variable {Y : Type*} [Fintype Y] [Nonempty Y]

theorem probUniform_mono {E E' : Y → Prop} (h : ∀ y, E y → E' y) :
    Pr[y ← Y : E y] ≤ Pr[y ← Y : E' y] :=
  MeasureTheory.measure_mono (fun y hy => h y hy)

theorem probUniform_or_le (E E' : Y → Prop) :
    Pr[y ← Y : E y ∨ E' y] ≤ Pr[y ← Y : E y] + Pr[y ← Y : E' y] :=
  MeasureTheory.measure_union_le {y | E y} {y | E' y}

theorem probUniform_le_one (E : Y → Prop) : Pr[y ← Y : E y] ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _))

theorem probUniform_eq_zero {E : Y → Prop} (h : ∀ y, ¬ E y) : Pr[y ← Y : E y] = 0 := by
  have : {y | E y} = ∅ := Set.eq_empty_iff_forall_notMem.2 h
  simp [probUniform, this]

/-- An event contained in a finite set `S` has probability at most `|S| / |Y|`. -/
theorem probUniform_le_card_div (S : Finset Y) {E : Y → Prop} (h : ∀ y, E y → y ∈ S) :
    Pr[y ← Y : E y] ≤ S.card / Fintype.card Y := by
  classical
  calc Pr[y ← Y : E y] ≤ Pr[y ← Y : y ∈ S] := probUniform_mono h
    _ = S.card / Fintype.card Y := by rw [probUniform_eq_card_div]; simp

/-- Comparing two count fractions: `a / b ≤ c / d` when `a · d ≤ c · b`. -/
theorem natCast_div_le_natCast_div {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d ≤ c * b) :
    (a : ℝ≥0∞) / b ≤ c / d := by
  have hb' : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have hd' : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd
  calc (a : ℝ≥0∞) / b = (a * d : ℝ≥0∞) / (b * d) :=
        (ENNReal.mul_div_mul_right _ _ hd' (by simp)).symm
    _ ≤ (c * b : ℝ≥0∞) / (b * d) := ENNReal.div_le_div_right (by exact_mod_cast h) _
    _ = c / d := by rw [mul_comm (b : ℝ≥0∞), ENNReal.mul_div_mul_right _ _ hb' (by simp)]

/-- A union over a finite index type: `Pr[∃ i, E i] ≤ ∑ i, Pr[E i]`. -/
theorem probUniform_exists_le {ι : Type*} [Fintype ι] (E : ι → Y → Prop) :
    Pr[y ← Y : ∃ i, E i y] ≤ ∑ i, Pr[y ← Y : E i y] := by
  have h : {y | ∃ i, E i y} = ⋃ i, {y | E i y} := by ext y; simp
  unfold probUniform
  rw [h]
  exact MeasureTheory.measure_iUnion_fintype_le _ _

/-- A uniform draw transported along an equivalence is uniform. -/
theorem probUniform_equiv {A : Type*} [Fintype A] [Nonempty A] (e : A ≃ Y) (E : Y → Prop) :
    Pr[a ← A : E (e a)] = Pr[y ← Y : E y] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_congr e]
  congr 2
  exact Finset.card_equiv e (by simp)

/-- An event on the first component of a uniform pair has the probability of that event on a
uniform first component. -/
theorem probUniform_prod_fst {C : Type*} [Fintype C] [Nonempty C] (E : Y → Prop) :
    Pr[p ← Y × C : E p.1] = Pr[y ← Y : E y] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_prod]
  have : (Finset.univ.filter fun p : Y × C => E p.1) = (Finset.univ.filter E) ×ˢ Finset.univ := by
    ext p; simp
  rw [this, Finset.card_product, Finset.card_univ, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-- An event on a uniform pair whose section at every second component has probability at most
`c` has probability at most `c`. -/
theorem probUniform_prod_le {C : Type*} [Fintype C] [Nonempty C] (E : Y × C → Prop)
    {c : ℝ≥0∞} (h : ∀ z, Pr[y ← Y : E (y, z)] ≤ c) : Pr[p ← Y × C : E p] ≤ c := by
  classical
  rw [probUniform_eq_card_div]
  have hY : (Fintype.card Y : ℝ≥0∞) ≠ 0 := by simp
  have hcount : ∀ z, ((Finset.univ.filter fun y => E (y, z)).card : ℝ≥0∞) ≤
      c * Fintype.card Y := fun z => by
    have := h z
    rw [probUniform_eq_card_div, ENNReal.div_le_iff hY (by simp)] at this
    exact this
  have hsplit : (Finset.univ.filter E).card =
      ∑ z : C, (Finset.univ.filter fun y => E (y, z)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    refine Finset.card_bij (fun p _ => p.1) (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [← hp.2]
      exact hp.1) ?_ ?_
    · intro p hp p' hp' he
      simp only [Finset.mem_filter] at hp hp'
      exact Prod.ext he (hp.2.trans hp'.2.symm)
    · intro y hy
      exact ⟨(y, z), by simpa using hy, rfl⟩
  rw [hsplit, Nat.cast_sum, Fintype.card_prod, Nat.cast_mul,
    ENNReal.div_le_iff (by simp) (ENNReal.mul_ne_top (by simp) (by simp))]
  calc ∑ z : C, ((Finset.univ.filter fun y => E (y, z)).card : ℝ≥0∞)
      ≤ ∑ _z : C, c * Fintype.card Y := Finset.sum_le_sum fun z _ => hcount z
    _ = c * (Fintype.card Y * Fintype.card C) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **An event on the coordinates of a uniform function at an embedded index set** has the
probability of that event on a uniform function on the index set: `a ∘ φ` is uniform. -/
theorem probUniform_comp_embedding {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    [DecidableEq J]
    (φ : ι ↪ J) (E : (ι → Y) → Prop) :
    Pr[a ← (J → Y) : E (a ∘ φ)] = Pr[g ← (ι → Y) : E g] := by
  classical
  let eJ : J ≃ ι ⊕ {j // j ∉ Set.range φ} :=
    (Equiv.Set.sumCompl (Set.range φ)).symm.trans
      (Equiv.sumCongr (Equiv.ofInjective φ φ.injective).symm (Equiv.refl _))
  let e : (J → Y) ≃ (ι → Y) × ({j // j ∉ Set.range φ} → Y) :=
    (Equiv.arrowCongr eJ (Equiv.refl Y)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  have he : ∀ a, (e a).1 = a ∘ φ := by
    intro a
    funext i
    have : eJ.symm (Sum.inl i) = φ i := by
      simp [eJ, Equiv.Set.sumCompl, Equiv.ofInjective]
      rfl
    simp [e, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow, this]
  calc Pr[a ← (J → Y) : E (a ∘ φ)] = Pr[a ← (J → Y) : E (e a).1] := by simp only [he]
    _ = Pr[p ← (ι → Y) × ({j // j ∉ Set.range φ} → Y) : E p.1] :=
      probUniform_equiv e (fun p => E p.1)
    _ = _ := probUniform_prod_fst E

/-- **An event on the coordinates of a uniform dependent function at an injective index map**,
each coordinate read through an equivalence, has the probability of the event on a uniform
function of the read coordinates: the restriction is uniform. -/
theorem probUniform_restrict {J ι : Type} [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]
    {β : J → Type} [∀ j, Fintype (β j)] [∀ j, Nonempty (β j)]
    {γ : ι → Type} [∀ i, Fintype (γ i)] [∀ i, Nonempty (γ i)]
    (ψ : ι → J) (hψ : Function.Injective ψ) (e : ∀ i, β (ψ i) ≃ γ i) (E : (∀ i, γ i) → Prop) :
    Pr[a ← (∀ j, β j) : E fun i => e i (a (ψ i))] = Pr[g ← (∀ i, γ i) : E g] := by
  classical
  let e1 := Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range ψ) β
  let e2 : (∀ j : Set.range ψ, β j.1) ≃ ∀ i, γ i :=
    (Equiv.piCongrLeft (fun j : Set.range ψ => β j.1) (Equiv.ofInjective ψ hψ)).symm.trans
      (Equiv.piCongrRight e)
  have h : ∀ a : ∀ j, β j, (fun i => e i (a (ψ i))) = e2 (e1 a).1 := fun a => rfl
  simp only [h]
  rw [probUniform_equiv e1 (fun q => E (e2 q.1))]
  exact (probUniform_prod_fst (fun f => E (e2 f))).trans (probUniform_equiv e2 E)

end Prob

variable {X Y : Type*} [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- `flip(P → Q, t)` (CMS19 Def 5.4, p. 21): the largest probability, over databases
`D ∈ P` with `|D| < t` and inputs `x ∉ supp(D)`, that `D + [x ↦ y] ∈ Q` for uniform `y`.
The maximum is a supremum in `ℝ≥0∞`; the empty supremum gives `flip(∅ → Q) = 0`. -/
noncomputable def flipProb (P Q : Set (DB X Y)) (t : ℕ) : ℝ≥0∞ :=
  ⨆ (D ∈ P) (_ : D.size < t) (x : X) (_ : x ∉ D), Pr[y ← Y : D.extend x y ∈ Q]

variable {P P' Q Q' : Set (DB X Y)} {t t' : ℕ} {ε : ℝ≥0∞}

theorem flipProb_le_iff :
    flipProb P Q t ≤ ε ↔
      ∀ D ∈ P, D.size < t → ∀ x ∉ D, Pr[y ← Y : D.extend x y ∈ Q] ≤ ε := by
  simp [flipProb, iSup_le_iff]

/-- The bound used by instance-specific proofs: a uniform bound on the one-query
probability bounds the flip probability. -/
theorem flipProb_le (h : ∀ D ∈ P, D.size < t → ∀ x ∉ D, Pr[y ← Y : D.extend x y ∈ Q] ≤ ε) :
    flipProb P Q t ≤ ε :=
  flipProb_le_iff.2 h

theorem le_flipProb {D : DB X Y} (hD : D ∈ P) (hs : D.size < t) {x : X} (hx : x ∉ D) :
    Pr[y ← Y : D.extend x y ∈ Q] ≤ flipProb P Q t :=
  flipProb_le_iff.1 le_rfl D hD hs x hx

/-- `flip(∅ → Q) = 0` (CMS19 Def 5.4). -/
@[simp] theorem flipProb_empty_left : flipProb (∅ : Set (DB X Y)) Q t = 0 :=
  le_antisymm (flipProb_le fun _ h => absurd h (Set.notMem_empty _)) bot_le

theorem flipProb_le_one : flipProb P Q t ≤ 1 :=
  flipProb_le fun _D _hD _hs _x _hx => probUniform_le_one _

/-- CMS19 Proposition 5.5 (i), p. 21. -/
theorem flipProb_mono (hP : P ⊆ P') (hQ : Q ⊆ Q') : flipProb P Q t ≤ flipProb P' Q' t :=
  flipProb_le fun _ hD hs _ hx =>
    (probUniform_mono fun _ hy => hQ hy).trans (le_flipProb (hP hD) hs hx)

theorem flipProb_mono_time (h : t ≤ t') : flipProb P Q t ≤ flipProb P Q t' :=
  flipProb_le fun _ hD hs _ hx => le_flipProb hD (hs.trans_le h) hx

/-- CMS19 Proposition 5.5 (ii), p. 21. -/
theorem flipProb_union_left : flipProb (P ∪ P') Q t = max (flipProb P Q t) (flipProb P' Q t) :=
  le_antisymm
    (flipProb_le fun _ hD hs _ hx => hD.elim
      (fun h => (le_flipProb h hs hx).trans le_sup_left)
      (fun h => (le_flipProb h hs hx).trans le_sup_right))
    (max_le (flipProb_mono Set.subset_union_left le_rfl)
      (flipProb_mono Set.subset_union_right le_rfl))

/-- CMS19 Proposition 5.5 (iii), p. 22. -/
theorem flipProb_union_right_le :
    flipProb P (Q ∪ Q') t ≤ flipProb P Q t + flipProb P Q' t :=
  flipProb_le fun _ hD hs _ hx =>
    (probUniform_or_le _ _).trans (add_le_add (le_flipProb hD hs hx) (le_flipProb hD hs hx))

/-- `I(P, t)` (CMS19 Def 5.6, p. 22): the larger of `flip(P̄ → P, t)` and
`flip(P → P̄, t)`. -/
noncomputable def instab (P : Set (DB X Y)) (t : ℕ) : ℝ≥0∞ :=
  max (flipProb Pᶜ P t) (flipProb P Pᶜ t)

theorem flipProb_compl_le_instab : flipProb Pᶜ P t ≤ instab P t := le_sup_left

theorem flipProb_to_compl_le_instab : flipProb P Pᶜ t ≤ instab P t := le_sup_right

/-- Instability is symmetric (CMS19 p. 22). -/
theorem instab_compl : instab Pᶜ t = instab P t := by
  simp only [instab, compl_compl, max_comm]

theorem instab_mono_time (h : t ≤ t') : instab P t ≤ instab P t' :=
  max_le_max (flipProb_mono_time h) (flipProb_mono_time h)

theorem instab_le_one : instab P t ≤ 1 := max_le flipProb_le_one flipProb_le_one

/-- `flip(P | Q, t) := flip(P̄ ∩ Q → P ∩ Q, t)` (CMS19 Def 5.11, p. 24). -/
noncomputable def condFlip (P Q : Set (DB X Y)) (t : ℕ) : ℝ≥0∞ :=
  flipProb (Pᶜ ∩ Q) (P ∩ Q) t

/-- `I(P | Q, t) := max (flip(P | Q, t)) (flip(P̄ | Q, t))` (CMS19 Def 5.11, p. 24). -/
noncomputable def condInstab (P Q : Set (DB X Y)) (t : ℕ) : ℝ≥0∞ :=
  max (condFlip P Q t) (condFlip Pᶜ Q t)

theorem condFlip_le_condInstab : condFlip P Q t ≤ condInstab P Q t := le_sup_left

theorem condFlip_compl_le_condInstab : condFlip Pᶜ Q t ≤ condInstab P Q t := le_sup_right

/-- Conditioning on the property of all databases recovers `I(P, t)` (CMS19 p. 24). -/
@[simp] theorem condInstab_univ : condInstab P Set.univ t = instab P t := by
  simp [condInstab, condFlip, instab]

/-- CMS19 Proposition 5.12 (2), first half, p. 24. -/
theorem condFlip_le_flipProb : condFlip P Q t ≤ flipProb Pᶜ P t :=
  flipProb_mono Set.inter_subset_left Set.inter_subset_left

/-- CMS19 Proposition 5.12 (2), p. 24: `I(P | Q, t) ≤ I(P, t)`. -/
theorem condInstab_le_instab : condInstab P Q t ≤ instab P t := by
  refine max_le (condFlip_le_flipProb.trans flipProb_compl_le_instab) ?_
  have := (condFlip_le_flipProb (P := Pᶜ) (Q := Q) (t := t))
  rw [compl_compl] at this
  exact this.trans flipProb_to_compl_le_instab

/-- CMS19 Proposition 5.12 (3), p. 24: `I(P ∪ Q, t) ≤ I(P | Q̄, t) + I(Q, t)`. -/
theorem instab_union_le : instab (P ∪ Q) t ≤ condInstab P Qᶜ t + instab Q t := by
  have hsplit : P ∪ Q ⊆ (P ∩ Qᶜ) ∪ Q := by
    intro D hD
    by_cases hq : D ∈ Q
    · exact Or.inr hq
    · exact Or.inl ⟨hD.resolve_right hq, hq⟩
  refine max_le ?_ ?_
  · rw [Set.compl_union]
    calc flipProb (Pᶜ ∩ Qᶜ) (P ∪ Q) t
        ≤ flipProb (Pᶜ ∩ Qᶜ) ((P ∩ Qᶜ) ∪ Q) t := flipProb_mono le_rfl hsplit
      _ ≤ flipProb (Pᶜ ∩ Qᶜ) (P ∩ Qᶜ) t + flipProb (Pᶜ ∩ Qᶜ) Q t := flipProb_union_right_le
      _ ≤ condInstab P Qᶜ t + instab Q t :=
          add_le_add condFlip_le_condInstab
            ((flipProb_mono Set.inter_subset_right le_rfl).trans flipProb_compl_le_instab)
  · rw [Set.compl_union]
    calc flipProb (P ∪ Q) (Pᶜ ∩ Qᶜ) t
        ≤ flipProb ((P ∩ Qᶜ) ∪ Q) (Pᶜ ∩ Qᶜ) t := flipProb_mono hsplit le_rfl
      _ = max (flipProb (P ∩ Qᶜ) (Pᶜ ∩ Qᶜ) t) (flipProb Q (Pᶜ ∩ Qᶜ) t) := flipProb_union_left
      _ ≤ condInstab P Qᶜ t + instab Q t := by
          refine max_le ?_ ?_
          · refine le_add_right (le_trans ?_ condFlip_compl_le_condInstab)
            simp [condFlip]
          · exact le_add_left
              ((flipProb_mono le_rfl Set.inter_subset_right).trans flipProb_to_compl_le_instab)

/-! ### Properties pulled back along an injection

A database property `R` on `X` is a property on a larger domain `X'` through an injection
`ι : X ↪ X'`, as `restrict ι ⁻¹' R`: a database on `X'` has the property when its entries at
the images `ι x` do. Its flip probabilities and instabilities over `X'` are at most those of
`R` over `X`: one more query at an image `ι x` is one more query at `x` of the restriction,
and one more query outside the image does not change the restriction. The second case needs
the source and target properties to be disjoint, which holds for every flip in `instab` and
`condInstab`. -/

section Restrict

variable {X' : Type*} [DecidableEq X'] {ι : X ↪ X'}

/-- For disjoint `P` and `Q`, `flip(ι*P → ι*Q, t) ≤ flip(P → Q, t)`, where `ι*R` is
`restrict ι ⁻¹' R`. -/
theorem flipProb_preimage_restrict_le (hPQ : Disjoint P Q) :
    flipProb (DB.restrict ι ⁻¹' P) (DB.restrict ι ⁻¹' Q) t ≤ flipProb P Q t := by
  refine flipProb_le fun D hD hs x' hx' => ?_
  by_cases hr : x' ∈ Set.range ι
  · obtain ⟨x, rfl⟩ := hr
    simp only [Set.mem_preimage, DB.restrict_extend_image]
    exact le_flipProb (D := D.restrict ι) hD (DB.size_restrict_le.trans_lt hs)
      (DB.mem_restrict.not.2 hx')
  · simp only [Set.mem_preimage, DB.restrict_extend_of_notMem_range hr]
    rw [probUniform_eq_zero fun _ hQ => Set.disjoint_left.1 hPQ hD hQ]
    exact zero_le

theorem instab_preimage_restrict_le : instab (DB.restrict ι ⁻¹' P) t ≤ instab P t := by
  simp only [instab, ← Set.preimage_compl]
  exact max_le_max (flipProb_preimage_restrict_le disjoint_compl_left)
    (flipProb_preimage_restrict_le disjoint_compl_right)

theorem condInstab_preimage_restrict_le :
    condInstab (DB.restrict ι ⁻¹' P) (DB.restrict ι ⁻¹' Q) t ≤ condInstab P Q t := by
  simp only [condInstab, condFlip, ← Set.preimage_compl, ← Set.preimage_inter]
  refine max_le_max (flipProb_preimage_restrict_le ?_) (flipProb_preimage_restrict_le ?_)
  · exact (disjoint_compl_left.mono Set.inter_subset_left Set.inter_subset_left)
  · rw [compl_compl]
    exact (disjoint_compl_right.mono Set.inter_subset_left Set.inter_subset_left)

omit [Fintype Y] [Nonempty Y] in
theorem empty_notMem_preimage_restrict {R : Set (DB X Y)} (hR : (∅ : DB X Y) ∉ R) :
    (∅ : DB X' Y) ∉ DB.restrict ι ⁻¹' R := by
  rwa [Set.mem_preimage, DB.restrict_empty]

end Restrict

/-! ### The collision property -/

/-- `P_col` (CMS19 p. 32): the databases containing a collision, that is, distinct
`x, x' ∈ supp(D)` with `D(x) = D(x')` (p. 29). -/
def collision : Set (DB X Y) :=
  {D | ∃ x ∈ D, ∃ x' ∈ D, x ≠ x' ∧ D.lookup x = D.lookup x'}

omit [Fintype Y] [Nonempty Y] in
theorem empty_notMem_collision : (∅ : DB X Y) ∉ collision := by
  rintro ⟨x, hx, -⟩
  exact Finmap.notMem_empty hx

omit [Fintype Y] [Nonempty Y] in
/-- A collision survives a one-point extension at a new input. -/
theorem extend_mem_collision {D : DB X Y} (hD : D ∈ collision) {x : X} (hx : x ∉ D) (y : Y) :
    D.extend x y ∈ collision := by
  obtain ⟨a, ha, b, hb, hab, heq⟩ := hD
  refine ⟨a, DB.mem_extend.2 (Or.inr ha), b, DB.mem_extend.2 (Or.inr hb), hab, ?_⟩
  rw [DB.lookup_extend_of_ne (ne_of_mem_of_not_mem ha hx),
    DB.lookup_extend_of_ne (ne_of_mem_of_not_mem hb hx), heq]

omit [Fintype Y] [Nonempty Y] in
/-- A collision-free database extended at a new input has a collision only if the new
answer `y` is already an answer of `D`. -/
theorem exists_lookup_of_extend_mem_collision {D : DB X Y} (hD : D ∉ collision) {x : X}
    (hx : x ∉ D) {y : Y} (h : D.extend x y ∈ collision) : ∃ x' ∈ D, D.lookup x' = some y := by
  obtain ⟨a, ha, b, hb, hab, heq⟩ := h
  rcases DB.mem_extend.1 ha with rfl | ha' <;> rcases DB.mem_extend.1 hb with rfl | hb'
  · exact absurd rfl hab
  · rw [DB.lookup_extend_self, DB.lookup_extend_of_ne (Ne.symm hab)] at heq
    exact ⟨b, hb', heq.symm⟩
  · rw [DB.lookup_extend_self, DB.lookup_extend_of_ne hab] at heq
    exact ⟨a, ha', heq⟩
  · rw [DB.lookup_extend_of_ne (ne_of_mem_of_not_mem ha' hx),
      DB.lookup_extend_of_ne (ne_of_mem_of_not_mem hb' hx)] at heq
    exact absurd ⟨a, ha', b, hb', hab, heq⟩ hD

omit [Fintype Y] [Nonempty Y] in
/-- A set of answers of `D` has at most `|D|` elements. -/
theorem card_le_size_of_forall_lookup (D : DB X Y) (S : Finset Y)
    (hS : ∀ y ∈ S, ∃ x' ∈ D, D.lookup x' = some y) : S.card ≤ D.size := by
  classical
  refine (Finset.card_le_card_of_injOn some ?_ (Option.some_injective _).injOn).trans
    (Finset.card_image_le (s := D.keys) (f := fun x => D.lookup x))
  intro y hy
  obtain ⟨x', hx', hxy⟩ := hS y hy
  exact Finset.mem_image.2 ⟨x', Finmap.mem_keys.2 hx', hxy⟩

theorem flipProb_compl_collision_le :
    flipProb collisionᶜ (collision : Set (DB X Y)) t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y := by
  classical
  refine flipProb_le fun D hD hs x hx => ?_
  calc Pr[y ← Y : D.extend x y ∈ collision]
      ≤ (Finset.univ.filter fun y => ∃ x' ∈ D, D.lookup x' = some y).card / Fintype.card Y :=
        probUniform_le_card_div _ fun y hy =>
          Finset.mem_filter.2 ⟨Finset.mem_univ _, exists_lookup_of_extend_mem_collision hD hx hy⟩
    _ ≤ ((t - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y := by
        refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
        exact (card_le_size_of_forall_lookup D _ fun y hy => (Finset.mem_filter.1 hy).2).trans
          (by omega)

theorem flipProb_collision_compl : flipProb (collision : Set (DB X Y)) collisionᶜ t = 0 :=
  le_antisymm (flipProb_le fun _ hD _ _ hx =>
    (probUniform_eq_zero fun y hy => hy (extend_mem_collision hD hx y)).le) bot_le

/-- CMS19 Lemma 6.11, p. 33, for a general finite range `Y` (the paper takes
`Y = {0,1}^λ`, so `|Y| = 2^λ`; the proof does not use the form of `Y`), in the
sharper form `(t - 1) / |Y|`. -/
theorem instab_collision_le' :
    instab (collision : Set (DB X Y)) t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y :=
  max_le flipProb_compl_collision_le (flipProb_collision_compl.trans_le bot_le)

/-- CMS19 Lemma 6.11, p. 33, non-strict: `I(P_col, t) ≤ t / |Y|`. -/
theorem instab_collision_le :
    instab (collision : Set (DB X Y)) t ≤ (t : ℝ≥0∞) / Fintype.card Y :=
  instab_collision_le'.trans (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.sub_le t 1)) _)

/-- CMS19 Lemma 6.11, p. 33: `I(P_col, t) < t / |Y|`. The strict inequality needs
`0 < t`; at `t = 0` both sides are `0`. -/
theorem instab_collision_lt (ht : 0 < t) :
    instab (collision : Set (DB X Y)) t < (t : ℝ≥0∞) / Fintype.card Y := by
  refine instab_collision_le'.trans_lt ?_
  rw [ENNReal.div_lt_div_iff_left (by simp) (by simp)]
  exact_mod_cast Nat.sub_lt ht one_pos

end GordieHowe.QROM
