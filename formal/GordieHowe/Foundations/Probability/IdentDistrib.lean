-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Algebra.Basic
public import GordieHowe.Foundations.Probability.Probability
public import Mathlib.Probability.IdentDistrib

@[expose] public section

/-!
# Identically distributed finite random variables

`IdentDistrib f g`, written `f =ᵈ g`, says that `f` applied to a uniform element of the finite
type `R` and `g` applied to a uniform element of `S` are identically distributed:
`PMF.map f (PMF.uniformOfFintype R) = PMF.map g (PMF.uniformOfFintype S)`, for nonempty `R` and
`S`. It is Mathlib's `ProbabilityTheory.IdentDistrib` at the uniform measures
(`identDistrib_iff_probabilityTheory`), stated on `PMF`s so that no measurable structure is needed.
This is the equality the zero-knowledge statements of `GordieHowe.Model.IOP.HVZK` use.
`identDistrib_iff_count` is the equivalent counting form, used by the proofs: for every value `v`,
the fraction of `R` that `f` sends to `v` equals the fraction of `S` that `g` sends to `v`.

`Uniform f` is `f =ᵈ id`: `f` sends a uniform element of `R` to a uniform element of its codomain.

The composition lemmas are those the simulator proofs use:
* `IdentDistrib.of_equiv`: a bijection of the random coins;
* `IdentDistrib.comp`: post-composition with any function;
* `IdentDistrib.prod`, `IdentDistrib.pi`: independent coins;
* `IdentDistrib.dependent`: a second component whose distribution, for each value
  of the first coins, depends on them only through the first component's
  value. This is the step that simulates one proof on the public output of an
  earlier one.

The pad lemmas `Uniform.add_const`, `Uniform.add_mem` and `Uniform.basis` say that a value masked by
an independent uniform pad is uniform, over a group, a subgroup containing the value, and a basis
combination of subfield pads. A family of messages each masked by its own pad, each value reading
only the pads of earlier messages, is uniform by `PadMasked.uniform` (`GordieHowe/Model/IOP/PadMasked.lean`).
-/

namespace GordieHowe.IOP

open Finset
open scoped Classical

variable {R S T V W : Type} [Fintype R] [Fintype S] [Fintype T]

/-- The number of coins `r` with `f r = v`. -/
noncomputable def fiber (f : R → V) (v : V) : ℕ :=
  (univ.filter fun r => f r = v).card

theorem fiber_eq_sum (f : R → V) (v : V) :
    fiber f v = ∑ r, if f r = v then 1 else 0 := by
  rw [fiber, card_filter]

/-- Fibers correspond under a bijection of the coins. -/
theorem fiber_equiv {f : R → V} {g : S → V} (e : R ≃ S) (h : ∀ r, f r = g (e r))
    (v : V) : fiber f v = fiber g v := by
  rw [fiber_eq_sum, fiber_eq_sum]
  exact Fintype.sum_equiv e _ _ fun r => by rw [h]

/-- The fiber of `k ∘ f` at `w` is the sum of the fibers of `f` over the
values in `s` that `k` sends to `w`, for any `s` containing the range of `f`. -/
theorem fiber_comp (f : R → V) (k : V → W) (w : W) {s : Finset V}
    (hs : ∀ r, f r ∈ s) :
    fiber (k ∘ f) w = ∑ v ∈ s.filter (fun v => k v = w), fiber f v := by
  rw [fiber]
  simp only [Function.comp_apply]
  rw [card_eq_sum_card_fiberwise (f := f) (t := s.filter fun v => k v = w)
    (fun r hr => mem_filter.2 ⟨hs r, (mem_filter.1 hr).2⟩)]
  refine sum_congr rfl fun v hv => ?_
  rw [mem_filter] at hv
  rw [fiber, filter_filter]
  congr 1
  refine filter_congr fun r _ => ?_
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv.2, h⟩

/-- The fibers of a map partition its coins. -/
theorem sum_fiber [Fintype V] (f : R → V) : ∑ v, fiber f v = Fintype.card R := by
  rw [← card_univ (α := R), card_eq_sum_card_fiberwise (f := f) (t := univ)
    (fun _ _ => mem_univ _)]
  rfl

@[simp] theorem fiber_id [Fintype V] (v : V) : fiber (id : V → V) v = 1 := by
  rw [fiber, card_eq_one]
  exact ⟨v, by ext; simp⟩

theorem fiber_const (v w : V) :
    fiber (fun _ : R => v) w = if v = w then Fintype.card R else 0 := by
  by_cases h : v = w <;> simp [fiber, h]

/-- The fiber of a pair whose second component depends on the first coins. -/
theorem fiber_dependent {R₂ V₂ : Type} [Fintype R₂] (f₁ : R → V) (f₂ : R → R₂ → V₂)
    (v : V) (v₂ : V₂) :
    fiber (fun r : R × R₂ => (f₁ r.1, f₂ r.1 r.2)) (v, v₂) =
      ∑ r₁ ∈ univ.filter (fun r₁ => f₁ r₁ = v), fiber (f₂ r₁) v₂ := by
  rw [fiber_eq_sum, Fintype.sum_prod_type, sum_filter]
  refine sum_congr rfl fun r₁ _ => ?_
  by_cases h : f₁ r₁ = v
  · simp [h, fiber_eq_sum]
  · simp [h]

/-- The fiber of a family is the product of the fibers. -/
theorem fiber_pi {ι : Type} [Fintype ι] [DecidableEq ι] {R' V' : ι → Type}
    [∀ i, Fintype (R' i)] (f : ∀ i, R' i → V' i) (v : ∀ i, V' i) :
    fiber (fun (r : ∀ i, R' i) i => f i (r i)) v = ∏ i, fiber (f i) (v i) := by
  rw [fiber]
  trans (Fintype.piFinset fun i => univ.filter fun x => f i x = v i).card
  · congr 1
    ext r
    simp [Fintype.mem_piFinset, funext_iff]
  · rw [Fintype.card_piFinset]
    rfl

/-- The pushforward of the uniform distribution on `R` along `f` gives `v`
the fraction of `R` that `f` sends to `v`. -/
theorem map_uniformOfFintype_apply [Nonempty R] (f : R → V) (v : V) :
    PMF.map f (PMF.uniformOfFintype R) v = (fiber f v : ENNReal) / Fintype.card R := by
  rw [PMF.map_apply, tsum_fintype, fiber, card_eq_sum_ones, Nat.cast_sum, sum_filter,
    ENNReal.div_eq_inv_mul, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  simp only [PMF.uniformOfFintype_apply, eq_comm (a := v)]
  split_ifs <;> simp

variable [Nonempty R] [Nonempty S] [Nonempty T]

/-- `f` on uniform `R` and `g` on uniform `S` have the same distribution. The
coin spaces are nonempty, so the uniform distributions exist;
`identDistrib_iff_count` is the equivalent counting form. -/
def IdentDistrib (f : R → V) (g : S → V) : Prop :=
  PMF.map f (PMF.uniformOfFintype R) = PMF.map g (PMF.uniformOfFintype S)

/-- `f =ᵈ g`: `f` on uniform coins and `g` on uniform coins are identically distributed
(`IdentDistrib`). -/
notation:50 f:51 " =ᵈ " g:51 => GordieHowe.IOP.IdentDistrib f g

/-- `IdentDistrib` as a count: for every value, the fibers of `f` and `g` have the
same proportion. -/
theorem identDistrib_iff_count {f : R → V} {g : S → V} :
    f =ᵈ g ↔ ∀ v, fiber f v * Fintype.card S = fiber g v * Fintype.card R := by
  refine ⟨fun h v => ?_, fun h => PMF.ext fun v => ?_⟩
  · have hv := DFunLike.congr_fun h v
    rw [map_uniformOfFintype_apply, map_uniformOfFintype_apply,
      ENNReal.div_eq_div_iff (by simp) (by simp) (by simp) (by simp),
      mul_comm (Fintype.card S : ENNReal), mul_comm (Fintype.card R : ENNReal)] at hv
    exact_mod_cast hv
  · rw [map_uniformOfFintype_apply, map_uniformOfFintype_apply,
      ENNReal.div_eq_div_iff (by simp) (by simp) (by simp) (by simp)]
    have := h v
    rw [mul_comm (Fintype.card S : ENNReal), mul_comm (Fintype.card R : ENNReal)]
    exact_mod_cast this

namespace IdentDistrib

theorem of_count {f : R → V} {g : S → V}
    (h : ∀ v, fiber f v * Fintype.card S = fiber g v * Fintype.card R) : f =ᵈ g :=
  identDistrib_iff_count.mpr h

theorem count {f : R → V} {g : S → V} (h : f =ᵈ g) (v : V) :
    fiber f v * Fintype.card S = fiber g v * Fintype.card R :=
  identDistrib_iff_count.mp h v

theorem refl (f : R → V) : f =ᵈ f := of_count fun _ => rfl

theorem symm {f : R → V} {g : S → V} (h : f =ᵈ g) : g =ᵈ f :=
  of_count fun v => (h.count v).symm

theorem trans {f : R → V} {g : S → V} {h : T → V}
    (hfg : f =ᵈ g) (hgh : g =ᵈ h) : f =ᵈ h := by
  refine of_count fun v => ?_
  have hS : 0 < Fintype.card S := Fintype.card_pos
  refine Nat.eq_of_mul_eq_mul_right hS ?_
  calc fiber f v * Fintype.card T * Fintype.card S
      = fiber f v * Fintype.card S * Fintype.card T := by ring
    _ = fiber g v * Fintype.card T * Fintype.card R := by rw [hfg.count v]; ring
    _ = fiber h v * Fintype.card R * Fintype.card S := by rw [hgh.count v]; ring

/-- A bijection of the coins that carries `f` to `g`. -/
theorem of_equiv {f : R → V} {g : S → V} (e : R ≃ S) (h : ∀ r, f r = g (e r)) :
    f =ᵈ g := of_count fun v => by
  rw [fiber_equiv e h, Fintype.card_congr e]

/-- Reparametrizing the first coins by a bijection preserves the law. -/
theorem comp_equiv {R' : Type} [Fintype R'] [Nonempty R'] {f : R → V} {g : S → V} (h : f =ᵈ g)
    (e : R' ≃ R) : (f ∘ e) =ᵈ g := of_count fun v => by
  rw [fiber_equiv (f := f ∘ e) (g := f) e (fun _ => rfl) v, Fintype.card_congr e]
  exact h.count v

/-- Post-composition preserves equal distributions. -/
theorem comp {f : R → V} {g : S → V} (h : f =ᵈ g) (k : V → W) :
    (k ∘ f) =ᵈ (k ∘ g) := by
  refine of_count fun w => ?_
  have hf : ∀ r, f r ∈ univ.image f ∪ univ.image g := fun r => by simp
  have hg : ∀ s, g s ∈ univ.image f ∪ univ.image g := fun s => by simp
  rw [fiber_comp f k w hf, fiber_comp g k w hg, sum_mul, sum_mul]
  exact sum_congr rfl fun v _ => h.count v

/-- Any two coin spaces give the same law to a constant. -/
theorem const (v : V) :
    (fun _ : R => v) =ᵈ (fun _ : S => v) := of_count fun w => by
  rw [fiber_const, fiber_const]
  split_ifs <;> simp [Nat.mul_comm]

/-- Independent coins: the pair of two equal laws. -/
theorem prod {R₂ S₂ V₂ : Type} [Fintype R₂] [Fintype S₂] [Nonempty R₂] [Nonempty S₂]
    {f : R → V} {g : S → V} {f₂ : R₂ → V₂} {g₂ : S₂ → V₂}
    (h : f =ᵈ g) (h₂ : f₂ =ᵈ g₂) :
    (fun r : R × R₂ => (f r.1, f₂ r.2)) =ᵈ (fun s : S × S₂ => (g s.1, g₂ s.2)) :=
  by
  refine of_count ?_
  rintro ⟨v, v₂⟩
  rw [fiber_dependent (f₂ := fun _ => f₂), fiber_dependent (f₂ := fun _ => g₂), sum_const,
    sum_const, smul_eq_mul, smul_eq_mul, Fintype.card_prod, Fintype.card_prod]
  calc fiber f v * fiber f₂ v₂ * (Fintype.card S * Fintype.card S₂)
      = (fiber f v * Fintype.card S) * (fiber f₂ v₂ * Fintype.card S₂) := by ring
    _ = (fiber g v * Fintype.card R) * (fiber g₂ v₂ * Fintype.card R₂) := by
        rw [h.count v, h₂.count v₂]
    _ = fiber g v * fiber g₂ v₂ * (Fintype.card R * Fintype.card R₂) := by ring

/-- Independent coins: a finite family of equal laws. -/
theorem pi {ι : Type} [Fintype ι] [DecidableEq ι] {R' S' V' : ι → Type}
    [∀ i, Fintype (R' i)] [∀ i, Fintype (S' i)] [∀ i, Nonempty (R' i)] [∀ i, Nonempty (S' i)]
    {f : ∀ i, R' i → V' i} {g : ∀ i, S' i → V' i} (h : ∀ i, f i =ᵈ g i) :
    (fun (r : ∀ i, R' i) i => f i (r i)) =ᵈ (fun (s : ∀ i, S' i) i => g i (s i)) := by
  refine of_count fun v => ?_
  rw [fiber_pi, fiber_pi, Fintype.card_pi, Fintype.card_pi, ← prod_mul_distrib,
    ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => (h i).count (v i)

/-- **Dependent composition.** The second component may depend on the first
coins `r₁` in any way, provided its law for fixed `r₁` is that of `g₂` at the
first component's value `f₁ r₁`. Then the pair is simulated by running `g₁`
and feeding its value to `g₂`. -/
theorem dependent {R₂ S₂ V₂ : Type} [Fintype R₂] [Fintype S₂] [Nonempty R₂] [Nonempty S₂]
    {f₁ : R → V} {g₁ : S → V} {f₂ : R → R₂ → V₂} {g₂ : V → S₂ → V₂}
    (h₁ : f₁ =ᵈ g₁) (h₂ : ∀ r₁, f₂ r₁ =ᵈ (g₂ (f₁ r₁))) :
    (fun r : R × R₂ => (f₁ r.1, f₂ r.1 r.2)) =ᵈ
      (fun s : S × S₂ => (g₁ s.1, g₂ (g₁ s.1) s.2)) := by
  refine of_count ?_
  rintro ⟨v, v₂⟩
  rw [fiber_dependent, fiber_dependent (f₂ := fun s₁ => g₂ (g₁ s₁)),
    Fintype.card_prod, Fintype.card_prod]
  have hR : (∑ r₁ ∈ univ.filter (fun r₁ => f₁ r₁ = v), fiber (f₂ r₁) v₂) *
      Fintype.card S₂ = fiber f₁ v * (fiber (g₂ v) v₂ * Fintype.card R₂) := by
    rw [sum_mul, fiber, card_eq_sum_ones, sum_mul]
    refine sum_congr rfl fun r₁ hr₁ => ?_
    rw [mem_filter] at hr₁
    rw [(h₂ r₁).count v₂, hr₁.2, one_mul]
  have hS : ∑ s₁ ∈ univ.filter (fun s₁ => g₁ s₁ = v), fiber (g₂ (g₁ s₁)) v₂ =
      fiber g₁ v * fiber (g₂ v) v₂ := by
    rw [fiber, card_eq_sum_ones, sum_mul]
    refine sum_congr rfl fun s₁ hs₁ => ?_
    rw [mem_filter] at hs₁
    rw [hs₁.2, one_mul]
  calc (∑ r₁ ∈ univ.filter (fun r₁ => f₁ r₁ = v), fiber (f₂ r₁) v₂) *
        (Fintype.card S * Fintype.card S₂)
      = (∑ r₁ ∈ univ.filter (fun r₁ => f₁ r₁ = v), fiber (f₂ r₁) v₂) *
          Fintype.card S₂ * Fintype.card S := by ring
    _ = fiber f₁ v * Fintype.card S * (fiber (g₂ v) v₂ * Fintype.card R₂) := by
        rw [hR]; ring
    _ = fiber g₁ v * Fintype.card R * (fiber (g₂ v) v₂ * Fintype.card R₂) := by
        rw [h₁.count v]
    _ = _ := by rw [hS]; ring

open MeasureTheory in
/-- **The bridge to Mathlib's `ProbabilityTheory.IdentDistrib`**: `f =ᵈ g` exactly when `f` and
`g` are identically distributed under the uniform measures, for discrete coin spaces and a value
space whose singletons are measurable. -/
theorem _root_.GordieHowe.IOP.identDistrib_iff_probabilityTheory [MeasurableSpace R]
    [DiscreteMeasurableSpace R] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace V]
    [MeasurableSingletonClass V] {f : R → V} {g : S → V} :
    (f =ᵈ g) ↔ ProbabilityTheory.IdentDistrib f g (PMF.uniformOfFintype R).toMeasure
      (PMF.uniformOfFintype S).toMeasure := by
  have hf : Measurable f := .of_discrete
  have hg : Measurable g := .of_discrete
  constructor
  · intro h
    refine ⟨hf.aemeasurable, hg.aemeasurable, ?_⟩
    rw [PMF.toMeasure_map (hf := hf), PMF.toMeasure_map (hf := hg)]
    exact congrArg PMF.toMeasure h
  · intro h
    have e := h.map_eq
    rw [PMF.toMeasure_map (hf := hf), PMF.toMeasure_map (hf := hg)] at e
    exact PMF.toMeasure_injective e

end IdentDistrib

/-- `f` sends a uniform element of `R` to a uniform element of `V`. -/
def Uniform [Fintype V] [Nonempty V] (f : R → V) : Prop := f =ᵈ (id : V → V)

namespace Uniform

theorem of_equiv [Fintype V] [Nonempty V] (e : R ≃ V) : Uniform e :=
  IdentDistrib.of_equiv e fun _ => rfl

/-- The first coordinate of a uniform pair is uniform. -/
theorem fst {B : Type} [Fintype V] [Nonempty V] [Fintype B] [Nonempty B] :
    Uniform (Prod.fst : V × B → V) := by
  classical
  refine IdentDistrib.of_count fun v => ?_
  have h : fiber (Prod.fst : V × B → V) v = Fintype.card B := by
    rw [fiber, show (univ.filter fun r : V × B => r.1 = v) = {v} ×ˢ univ by ext ⟨a, b⟩; simp [eq_comm],
      card_product, card_singleton, one_mul, card_univ]
  rw [h, fiber_id, one_mul, Fintype.card_prod, Nat.mul_comm]

/-- The second coordinate of a uniform pair is uniform. -/
theorem snd {A : Type} [Fintype A] [Nonempty A] [Fintype V] [Nonempty V] :
    Uniform (Prod.snd : A × V → V) := by
  classical
  refine IdentDistrib.of_count fun v => ?_
  have h : fiber (Prod.snd : A × V → V) v = Fintype.card A := by
    rw [fiber, show (univ.filter fun r : A × V => r.2 = v) = univ ×ˢ {v} by ext ⟨a, b⟩; simp [eq_comm],
      card_product, card_singleton, mul_one, card_univ]
  rw [h, fiber_id, one_mul, Fintype.card_prod]

/-- A uniform pad plus a fixed value is uniform. -/
theorem add_const {G : Type} [AddGroup G] [Fintype G] (a : G) :
    Uniform fun p : G => p + a :=
  of_equiv (Equiv.addRight a)

/-- A surjective additive homomorphism, plus a fixed value, sends a uniform
element to a uniform element: every fiber is a coset of the kernel. -/
theorem of_surjective {G H : Type} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (φ : G →+ H) (hφ : Function.Surjective φ) (h₀ : H) :
    Uniform fun g => φ g + h₀ := by
  have hfib : ∀ v w, fiber (fun g => φ g + h₀) v = fiber (fun g => φ g + h₀) w := by
    intro v w
    obtain ⟨gv, hgv⟩ := hφ (v - h₀)
    obtain ⟨gw, hgw⟩ := hφ (w - h₀)
    refine card_nbij' (fun g => g - gv + gw) (fun g => g - gw + gv) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
      rw [map_add, map_sub, hgv, hgw, ← hg]
      simp
    · intro g hg
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
      rw [map_add, map_sub, hgv, hgw, ← hg]
      simp
    · intro g _
      simp
    · intro g _
      simp
  refine IdentDistrib.of_count fun v => ?_
  rw [fiber_id, one_mul]
  have hsum := sum_fiber (fun g => φ g + h₀)
  simp only [hfib _ h₀, sum_const, card_univ, smul_eq_mul] at hsum
  rw [← hsum, hfib v h₀, Nat.mul_comm]

/-- A pad uniform over a subgroup `H`, plus a fixed value in `H`, has the law
of the pad. This is the case of a pad drawn from a subfield masking a value
known to lie in it. -/
theorem add_mem {G : Type} [AddGroup G] (H : AddSubgroup G) [Fintype H] {a : G}
    (ha : a ∈ H) :
    (fun p : H => (p : G) + a) =ᵈ (fun p : H => (p : G)) :=
  IdentDistrib.of_equiv (Equiv.addRight (⟨a, ha⟩ : H)) fun _ => rfl

/-- Pads `μ i` drawn uniformly from a subfield `E` and combined over an
`E`-basis `b` of `K`, plus a fixed value, are uniform over `K`. -/
theorem basis {ι E K : Type} [Fintype ι] [DecidableEq ι] [Field E] [Fintype E] [Field K]
    [Fintype K] [Algebra E K] (b : Module.Basis ι E K) (a : K) :
    Uniform fun μ : ι → E => (∑ i, μ i • b i) + a :=
  IdentDistrib.of_equiv (b.equivFun.symm.toEquiv.trans (Equiv.addRight a)) fun μ => by
    simp

/-- **An event read through a uniform map**: for `f` sending a uniform element of `R` to a uniform
element of `V`, an event on `f r` has the probability of the event on a uniform element of `V`. -/
theorem probUniform_comp [Fintype R] [Nonempty R] [Fintype V] [Nonempty V] {f : R → V}
    (h : Uniform f) (p : V → Prop) : Pr[r ← R : p (f r)] = Pr[v ← V : p v] := by
  have h' : PMF.map f (PMF.uniformOfFintype R) = PMF.uniformOfFintype V := by
    rw [show PMF.map f (PMF.uniformOfFintype R) = PMF.map id (PMF.uniformOfFintype V) from h,
      PMF.map_id]
  unfold probUniform
  rw [← h', PMF.toOuterMeasure_map_apply]
  rfl

end Uniform

end GordieHowe.IOP
