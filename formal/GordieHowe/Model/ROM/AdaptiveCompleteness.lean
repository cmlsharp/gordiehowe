-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.Interactive
public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Foundations.Probability.Probability

@[expose] public section

/-!
# Adaptive completeness of a salted argument in the classical random-oracle model

Unruh 2017 (ePrint 2017/398), Definition 5, p. 14: "for any polynomial-time oracle algorithm `A`
there is a negligible `µ` such that `Pr[(x, w) ∈ R ∧ V^H(1^η, x, π) = 0 : H ←$ Fun,
(x, w) ← A^H(1^η), π ← P^H(1^η, x, w)] ≤ µ(η)`". The statement and witness are chosen by an
adversary after querying the oracle.

Here the argument is salted: the oracle is `H : A → B`, `saltOf a` is the salt in the slot of the
input `a` (or `none`), and the honest prover draws uniform coins `r` and a uniform salt `σ` after
the adversary. The one-proof hypothesis is the **fresh-slice bound**: for every salt `σ`, every
oracle `g` and every output `o` of the adversary, the honest proof is rejected with probability at
most `δ` over uniform coins `r` when the inputs of salt `σ` are answered by a fresh uniform
function and all other inputs by `g` (`replaceSlice saltOf σ g F`). The event `Bad r σ H o` is
"`o` is a pair in the relation and the verifier with oracle `H` rejects the honest proof with
coins `r` and salt `σ`"; it is a classical statement about one proof, proved for each compiler
from the counting of its fixed-statement completeness.

**The theorem** (`Alg.prob_bad_coins_le`, `QueryBoundedAdversary.adaptiveCompleteness_coins`):
every classical `t`-query adversary without proof queries outputs `o` with `Bad r σ H o` with
probability at most `δ + t / |Sd|`.

**The argument** (our statement). Draw a fresh `F` besides `σ` and `H`.
1. (identical until bad, `t / |Sd|`) Unless one of the adversary's `t` queries carries the salt
   `σ` (`Hit`; each input carries at most one salt and `σ` is drawn after the queries), the
   adversary's output against `H` is its output against `replaceSlice saltOf σ H F`
   (`output_eq_of_agree`).
2. (exact) The map `(H, F) ↦ (replaceSlice σ H F, replaceSlice σ F H)` exchanges the slices of
   `σ` of the two functions; it is an involution, so it preserves the uniform law
   (`sliceSwap`). After it, the adversary runs against `H` and the honest proof uses `H` with the
   slice of `σ` answered by the fresh `F`: the fresh-slice bound applies at every `H`.
-/

namespace GordieHowe.ROM

open GordieHowe.IOP GordieHowe.QROM GordieHowe.QROM
open scoped ENNReal

section Slice

variable {A B Sd : Type} (saltOf : A → Option Sd) [DecidableEq Sd]

/-- **The exchange of the slices of `σ`** of two functions: `(H, F) ↦ (H with the slice of `σ`
answered by `F`, F with the slice of `σ` answered by `H`)`, an involution. -/
def sliceSwap (σ : Sd) : (A → B) × (A → B) ≃ (A → B) × (A → B) where
  toFun p := (replaceSlice saltOf σ p.1 p.2, replaceSlice saltOf σ p.2 p.1)
  invFun p := (replaceSlice saltOf σ p.1 p.2, replaceSlice saltOf σ p.2 p.1)
  left_inv p := by
    ext a <;> by_cases h : saltOf a = some σ <;> simp [replaceSlice, h]
  right_inv p := by
    ext a <;> by_cases h : saltOf a = some σ <;> simp [replaceSlice, h]

theorem replaceSlice_sliceSwap (σ : Sd) (p : (A → B) × (A → B)) :
    replaceSlice saltOf σ (sliceSwap saltOf σ p).1 (sliceSwap saltOf σ p).2 = p.1 := by
  funext a
  by_cases h : saltOf a = some σ <;> simp [sliceSwap, replaceSlice, h]

theorem replaceSlice_apply_of_ne {σ : Sd} {H F : A → B} {a : A} (h : saltOf a ≠ some σ) :
    replaceSlice saltOf σ H F a = H a := by
  simp [replaceSlice, h]

end Slice

section Uniform

variable {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]

/-- **A bound at every first coordinate** bounds the product: if `Pr[y : p (x, y)] ≤ c` for every
`x`, then `Pr[(x, y) : p (x, y)] ≤ c`. -/
theorem probUniform_prod_le {p : X × Y → Prop} {c : ℝ≥0∞} (h : ∀ x, Pr[y ← Y : p (x, y)] ≤ c) :
    Pr[z ← (X × Y) : p z] ≤ c := by
  refine (probUniform_prod_le_add p (fun _ => False) fun x _ => h x).trans ?_
  rw [probUniform_eq_zero fun _ h => h, add_zero]

/-- An event of the first coordinate has the same probability on the product. -/
theorem probUniform_prod_fst (p : X → Prop) : Pr[z ← (X × Y) : p z.1] = Pr[x ← X : p x] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_prod]
  have : (Finset.univ.filter fun z : X × Y => p z.1) = (Finset.univ.filter p) ×ˢ Finset.univ := by
    ext z
    simp
  rw [this, Finset.card_product, Finset.card_univ, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-- A uniform probability on a product is the uniform average over the first coordinate of the
probability on the second, as a finite sum. -/
theorem probUniform_prod_eq_sum (p : X × Y → Prop) :
    Pr[z ← (X × Y) : p z] = ∑ x, (Fintype.card X : ℝ≥0∞)⁻¹ * Pr[y ← Y : p (x, y)] := by
  rw [probUniform_prod_eq_tsum, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]

omit [Fintype Y] [Nonempty Y] in
/-- The uniform average of a constant is the constant. -/
theorem sum_inv_card_mul_const (c : ℝ≥0∞) : ∑ _x : X, (Fintype.card X : ℝ≥0∞)⁻¹ * c = c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

omit [Fintype Y] [Nonempty Y] in
/-- **An average of bounds with a common additive term**: if `f x ≤ g x + c` at every `x`, the
uniform average of `f` is at most that of `g` plus `c`. -/
theorem sum_inv_card_mul_le_add {f g : X → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, f x ≤ g x + c) :
    ∑ x, (Fintype.card X : ℝ≥0∞)⁻¹ * f x ≤ ∑ x, (Fintype.card X : ℝ≥0∞)⁻¹ * g x + c := by
  calc ∑ x, (Fintype.card X : ℝ≥0∞)⁻¹ * f x
      ≤ ∑ x, ((Fintype.card X : ℝ≥0∞)⁻¹ * g x + (Fintype.card X : ℝ≥0∞)⁻¹ * c) :=
        Finset.sum_le_sum fun x _ => by rw [← mul_add]; gcongr; exact h x
    _ = _ := by rw [Finset.sum_add_distrib, sum_inv_card_mul_const]

end Uniform

/-- The reordering `(r, σ, H, F) ↦ (σ, H, r, F)` of the draws of the fresh-slice reduction with
coins. -/
def coinsReorder (R S H : Type) : R × (S × (H × H)) ≃ S × (H × (R × H)) where
  toFun z := (z.2.1, z.2.2.1, z.1, z.2.2.2)
  invFun z := (z.2.2.1, z.1, z.2.1, z.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

namespace Alg

variable {A B C : Type} {t : ℕ} (𝒜 : Alg A B C t)

/-- **The queries depend only on the answers at the queries**: if `h'` agrees with `h` on the
first `i` queries against `h`, the first `i` queries against `h'` are the same. -/
theorem queries_eq_of_agree {h h' : A → B} :
    ∀ i, (∀ a ∈ 𝒜.queries h i, h' a = h a) → 𝒜.queries h' i = 𝒜.queries h i
  | 0, _ => rfl
  | i + 1, hag => by
    have hi : 𝒜.queries h' i = 𝒜.queries h i := queries_eq_of_agree i fun a ha =>
      hag a (by rw [queries]; exact List.mem_append_left _ ha)
    rw [queries, queries, hi, List.map_congr_left fun a ha =>
      hag a (by rw [queries]; exact List.mem_append_left _ ha)]

/-- **The output depends only on the answers at the queries.** -/
theorem output_eq_of_agree {h h' : A → B} (hag : ∀ a ∈ 𝒜.queries h t, h' a = h a) :
    𝒜.output h' = 𝒜.output h := by
  rw [output, output, 𝒜.queries_eq_of_agree t hag, List.map_congr_left hag]

variable [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] {Sd : Type} [Fintype Sd]
  [Nonempty Sd] [DecidableEq Sd] (saltOf : A → Option Sd)

omit [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] [DecidableEq Sd] in
/-- **A query carries a given salt with probability at most `t / |Sd|`**: over a uniform salt `σ`,
one of the `t` queries against a fixed oracle has salt `σ`. -/
theorem prob_hit_le (h : A → B) :
    Pr[σ ← Sd : ∃ a ∈ 𝒜.queries h t, saltOf a = some σ] ≤ t / Fintype.card Sd := by
  classical
  let q : Fin t → A := fun i => (𝒜.queries h t)[i.1]'(by simp)
  calc _ ≤ Pr[σ ← Sd : ∃ i : Fin t, saltOf (q i) = some σ] := QROM.probUniform_mono fun σ ⟨a, ha, hs⟩ => by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
          exact ⟨⟨i, by simpa using hi⟩, hs⟩
    _ ≤ ∑ i : Fin t, Pr[σ ← Sd : saltOf (q i) = some σ] := probUniform_exists_le _
    _ ≤ ∑ _i : Fin t, (1 : ℝ≥0∞) / Fintype.card Sd := Finset.sum_le_sum fun i _ => by
          refine (probUniform_le_card_div ((saltOf (q i)).toFinset) fun σ hσ => ?_).trans ?_
          · simp [hσ]
          · gcongr
            cases saltOf (q i) <;> simp
    _ = t / Fintype.card Sd := by simp [ENNReal.div_eq_inv_mul, mul_comm]

variable {O : Type} (𝒜 : Alg A B O t)

/-- **The fresh-slice reduction against a deterministic `t`-query algorithm** (module docstring,
steps 1 and 2): over a uniform salt `σ` and a uniform oracle `H`, the event
`Bad σ H (𝒜.output H)` has probability at most that of `Bad σ (replaceSlice saltOf σ H F) (𝒜.output H)`
over a further uniform `F`, plus `t / |Sd|`. -/
theorem prob_bad_le_fresh (Bad : Sd → (A → B) → O → Prop) :
    Pr[p ← Sd × (A → B) : Bad p.1 p.2 (𝒜.output p.2)] ≤
      Pr[q ← Sd × ((A → B) × (A → B)) :
          Bad q.1 (replaceSlice saltOf q.1 q.2.1 q.2.2) (𝒜.output q.2.1)] +
        t / Fintype.card Sd := by
  classical
  -- a fresh `F` besides `σ` and `H`
  have hext : Pr[p ← Sd × (A → B) : Bad p.1 p.2 (𝒜.output p.2)] =
      Pr[q ← Sd × ((A → B) × (A → B)) : Bad q.1 q.2.1 (𝒜.output q.2.1)] := by
    rw [← probUniform_prod_fst (Y := A → B)
      (fun p : Sd × (A → B) => Bad p.1 p.2 (𝒜.output p.2))]
    exact (QROM.probUniform_equiv (Equiv.prodAssoc Sd (A → B) (A → B)).symm
      (fun z : (Sd × (A → B)) × (A → B) => Bad z.1.1 z.1.2 (𝒜.output z.1.2))).symm
  rw [hext]
  let Hit : Sd × ((A → B) × (A → B)) → Prop := fun q =>
    ∃ a ∈ 𝒜.queries q.2.1 t, saltOf a = some q.1
  let Sw : Sd × ((A → B) × (A → B)) → Prop := fun q =>
    Bad q.1 q.2.1 (𝒜.output (replaceSlice saltOf q.1 q.2.1 q.2.2))
  have hcover : ∀ q : Sd × ((A → B) × (A → B)), Bad q.1 q.2.1 (𝒜.output q.2.1) → Sw q ∨ Hit q := by
    intro q hq
    by_cases hh : Hit q
    · exact Or.inr hh
    · left
      have : 𝒜.output (replaceSlice saltOf q.1 q.2.1 q.2.2) = 𝒜.output q.2.1 :=
        𝒜.output_eq_of_agree fun a ha =>
          replaceSlice_apply_of_ne saltOf fun hs => hh ⟨a, ha, hs⟩
      change Bad q.1 q.2.1 _
      rw [this]
      exact hq
  -- the exchange of the slices of `σ` of `H` and `F`
  have hSw : Pr[q ← Sd × ((A → B) × (A → B)) : Sw q] =
      Pr[q ← Sd × ((A → B) × (A → B)) :
        Bad q.1 (replaceSlice saltOf q.1 q.2.1 q.2.2) (𝒜.output q.2.1)] := by
    rw [← QROM.probUniform_equiv (Equiv.prodCongrRight fun σ => sliceSwap saltOf σ)]
    congr 1
    funext q
    change Bad q.1 (sliceSwap saltOf q.1 q.2).1 (𝒜.output (replaceSlice saltOf q.1
      (sliceSwap saltOf q.1 q.2).1 (sliceSwap saltOf q.1 q.2).2)) = _
    rw [replaceSlice_sliceSwap]
    rfl
  have hHit : Pr[q ← Sd × ((A → B) × (A → B)) : Hit q] ≤ t / Fintype.card Sd := by
    rw [← QROM.probUniform_equiv (Equiv.prodComm ((A → B) × (A → B)) Sd) Hit]
    exact probUniform_prod_le fun p => 𝒜.prob_hit_le saltOf p.1
  exact (QROM.probUniform_mono hcover).trans ((probUniform_or_le _ _).trans (add_le_add hSw.le hHit))

/-- **Adaptive completeness of a salted argument with coins against a deterministic `t`-query
algorithm**: if, at every salt `σ`, oracle `g` and output `o`, the event `Bad r σ H o` has
probability at most `δ` over uniform coins `r` and a fresh slice of `σ` (`hslice`), then over
uniform coins `r`, a uniform salt `σ` and a uniform oracle `H`, the event `Bad r σ H (𝒜.output H)`
has probability at most `δ + t / |Sd|`. The coins are those of the honest prover, drawn
independently of the oracle and the algorithm. -/
theorem prob_bad_coins_le {R : Type} [Fintype R] [Nonempty R] {Bad : R → Sd → (A → B) → O → Prop}
    {δ : ℝ≥0∞}
    (hslice : ∀ σ g o, Pr[q ← R × (A → B) : Bad q.1 σ (replaceSlice saltOf σ g q.2) o] ≤ δ) :
    ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[p ← Sd × (A → B) : Bad r p.1 p.2 (𝒜.output p.2)] ≤
      δ + t / Fintype.card Sd := by
  refine (sum_inv_card_mul_le_add fun r => 𝒜.prob_bad_le_fresh saltOf (Bad r)).trans
    (add_le_add ?_ le_rfl)
  rw [← probUniform_prod_eq_sum (fun z : R × (Sd × ((A → B) × (A → B))) =>
    Bad z.1 z.2.1 (replaceSlice saltOf z.2.1 z.2.2.1 z.2.2.2) (𝒜.output z.2.2.1)),
    ← QROM.probUniform_equiv (coinsReorder R Sd (A → B)).symm]
  exact probUniform_prod_le fun σ => probUniform_prod_le fun H => hslice σ H (𝒜.output H)

end Alg

namespace QueryBoundedAdversary

variable {A B Resp O : Type} {t : ℕ} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]
  {Sd : Type} [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] (saltOf : A → Option Sd)
  (𝒜 : QueryBoundedAdversary A B Empty Resp O t)

/-- **Adaptive completeness of a salted argument with coins in the classical random-oracle model**
(Unruh 2017 Definition 5, p. 14, with the honest prover's coins and salt drawn after the
adversary): if the honest proof is rejected with probability at most `δ` over uniform coins `r`
and a fresh slice of its salt, at every salt, oracle and output (`hslice`), then every
classical `t`-query adversary without proof queries outputs `o` with `Bad r σ H o` with probability at most
`δ + t / |Sd|`, over its coins, uniform coins `r`, a uniform salt `σ` and a uniform oracle `H`. -/
theorem adaptiveCompleteness_coins {R : Type} [Fintype R] [Nonempty R]
    {Bad : R → Sd → (A → B) → O → Prop} {δ : ℝ≥0∞}
    (hslice : ∀ σ g o, Pr[q ← R × (A → B) : Bad q.1 σ (replaceSlice saltOf σ g q.2) o] ≤ δ) :
    ∑' a, 𝒜.coins a * ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ *
        Pr[p ← Sd × (A → B) : Bad r p.1 p.2 ((𝒜.toAdversary.alg a).output p.2)] ≤
      δ + t / Fintype.card Sd :=
  𝒜.tsum_le fun a => (𝒜.toAdversary.alg a).prob_bad_coins_le saltOf hslice

end QueryBoundedAdversary

end GordieHowe.ROM
