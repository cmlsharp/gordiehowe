-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# Averages over oracle values and the degree of amplitudes in the oracle

The amplitudes of a quantum run against the random oracle `g : X → Y`, read as functions of `g`,
are vectors of `QState (X → Y)`. This file defines, for such functions:

- `avgAt x f`: the average of `f` over the value of the oracle at `x`,
  `(avgAt x f) g = |Y|⁻¹ ∑_y f (g[x ↦ y])`; `avgOn S f`: the average over the values on a finite
  set `S` (`setOn S g z`: `g` with its values on `S` taken from `z`). These are the projections
  `Π_x` of Grilo, Hövelmanns, Hülsing and Majenz ("Tight adaptive reprogramming in the QROM",
  ASIACRYPT 2021, ePrint 2020/1361, section 5.1) onto the uniform superposition of the oracle
  register `F_x`, written on the amplitudes of the purified oracle: `avgAt x` is an orthogonal
  projection (`avgAt_avgAt`, `inner_avgAt_left`), and these commute (`avgAt_comm`).
- `juntas d`, `degLE d`: the functions that depend on the oracle at no more than `d` points, and
  their span, the functions of degree at most `d` (the Efron–Stein degree).

The results:

- `sum_norm_sub_avgAt_sq_le`: **a function of degree at most `d` has
  `∑_x ‖f − avgAt x f‖² ≤ d ‖f‖²`.** This is the bound `∑_S |S| ‖f_S‖² ≤ d ∑_S ‖f_S‖²` of the
  Efron–Stein decomposition `f = ∑_S f_S`; the proof is by induction on the set of points,
  splitting `f` by the projection at one point into two orthogonal parts, of degrees at most `d`
  and `d − 1` in the remaining points (`sum_norm_sub_avgAt_sq_le_of_mem_span`). It replaces the
  support decomposition of GHHM21 Lemma 1 (Lemma 2 of Alagic, Majenz, Russell and Song,
  EUROCRYPT 2020) in the proof of GHHM21 equation (12).
- `norm_sub_avgOn_sq_le`: `‖f − avgOn S f‖² ≤ ∑_{x ∈ S} ‖f − avgAt x f‖²`.
- `pmul_mem_degLE`: the pointwise product of functions of degrees at most `d₁` and `d₂` has
  degree at most `d₁ + d₂`; `mem_degLE_of_dependsOn`: a function of the values on `T` has degree
  at most `|T|`.
- `indicator_run_mem_degLE`: the indicator that a classical oracle program making at most `q`
  queries returns `r`, run against an oracle read pointwise from `g` (`ReadsPointwise`), has degree
  at most `q` (a decision tree of depth `q`).
- `prod_mem_degLE`, `indicator_comp_mem_degLE`, `ofFun_sum`, `ofFun_const_mem_degLE`: finite
  products, indicators of functions with bounded-degree value indicators, sums and constants.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GordieHowe.Quantum

namespace Junta

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]

/-! ### Setting values on a set -/

/-- **`g` with its values on `S` taken from `z`.** -/
def setOn (S : Finset X) (g z : X → Y) : X → Y :=
  fun x => if x ∈ S then z x else g x

omit [Fintype X] [Fintype Y] in
theorem setOn_apply_of_mem {S : Finset X} (g z : X → Y) {x : X} (hx : x ∈ S) :
    setOn S g z x = z x := by simp [setOn, hx]

omit [Fintype X] [Fintype Y] in
theorem setOn_apply_of_notMem {S : Finset X} (g z : X → Y) {x : X} (hx : x ∉ S) :
    setOn S g z x = g x := by simp [setOn, hx]

omit [Fintype X] [Fintype Y] in
@[simp] theorem setOn_setOn_left (S : Finset X) (g g' z : X → Y) :
    setOn S (setOn S g z) g' = setOn S g g' := by
  funext x
  by_cases hx : x ∈ S <;> simp [setOn, hx]

omit [Fintype X] [Fintype Y] in
@[simp] theorem setOn_setOn_right (S : Finset X) (g z z' : X → Y) :
    setOn S g (setOn S z z') = setOn S g z' := by
  funext x
  by_cases hx : x ∈ S <;> simp [setOn, hx]

omit [Fintype X] [Fintype Y] in
@[simp] theorem setOn_self (S : Finset X) (g : X → Y) : setOn S g g = g := by
  funext x
  by_cases hx : x ∈ S <;> simp [setOn, hx]

omit [Fintype X] [Fintype Y] in
/-- **Exchanging the values on `S`**: `(g, z) ↦ (setOn S g z, setOn S z g)` is an involution. -/
theorem setOn_swap_involutive (S : Finset X) :
    Function.Involutive fun p : (X → Y) × (X → Y) => (setOn S p.1 p.2, setOn S p.2 p.1) := by
  rintro ⟨g, z⟩
  simp only [Prod.mk.injEq]
  constructor <;> funext x <;> by_cases hx : x ∈ S <;> simp [setOn, hx]

/-- **The exchange of the values on `S`** as a permutation of pairs of oracles. -/
def swapOn (S : Finset X) : Equiv.Perm ((X → Y) × (X → Y)) :=
  (setOn_swap_involutive S).toPerm _

omit [Fintype X] [Fintype Y] in
theorem swapOn_apply (S : Finset X) (p : (X → Y) × (X → Y)) :
    swapOn S p = (setOn S p.1 p.2, setOn S p.2 p.1) := rfl

/-! ### Averages -/

/-- **The average over the value at `x`**: `(avgAt x f) g = |Y|⁻¹ ∑_y f (g[x ↦ y])`. -/
noncomputable def avgAt (x : X) : QState (X → Y) →ₗ[ℂ] QState (X → Y) where
  toFun f := WithLp.toLp 2 fun g => (Fintype.card Y : ℂ)⁻¹ * ∑ y, f (Function.update g x y)
  map_add' f f' := by
    ext g
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext g
    simp [Finset.mul_sum]
    ring_nf

theorem avgAt_apply (x : X) (f : QState (X → Y)) (g : X → Y) :
    avgAt x f g = (Fintype.card Y : ℂ)⁻¹ * ∑ y, f (Function.update g x y) := rfl

/-- **The average over the values on `S`**: `(avgOn S f) g = |Y^X|⁻¹ ∑_z f (setOn S g z)`. -/
noncomputable def avgOn (S : Finset X) : QState (X → Y) →ₗ[ℂ] QState (X → Y) where
  toFun f := WithLp.toLp 2 fun g => (Fintype.card (X → Y) : ℂ)⁻¹ * ∑ z, f (setOn S g z)
  map_add' f f' := by
    ext g
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext g
    simp [Finset.mul_sum]
    ring_nf

theorem avgOn_apply (S : Finset X) (f : QState (X → Y)) (g : X → Y) :
    avgOn S f g = (Fintype.card (X → Y) : ℂ)⁻¹ * ∑ z, f (setOn S g z) := rfl

/-! ### Functions of bounded degree -/

/-- **The functions that depend on the oracle at no more than `d` points.** -/
def juntas (d : ℕ) : Set (QState (X → Y)) :=
  {f | ∃ T : Finset X, T.card ≤ d ∧ ∀ g g' : X → Y, (∀ x ∈ T, g x = g' x) → f g = f g'}

/-- **The functions of degree at most `d`**: the span of the functions that depend on the oracle
at no more than `d` points. -/
noncomputable def degLE (d : ℕ) : Submodule ℂ (QState (X → Y)) :=
  Submodule.span ℂ (juntas d)

/-- **The pointwise product** of two functions of the oracle. -/
def pmul (f h : QState (X → Y)) : QState (X → Y) :=
  WithLp.toLp 2 fun g => f g * h g

theorem pmul_apply (f h : QState (X → Y)) (g : X → Y) : pmul f h g = f g * h g := rfl

/-- **The function `g ↦ φ g`** as a vector. -/
def ofFun (φ : (X → Y) → ℂ) : QState (X → Y) := WithLp.toLp 2 φ

theorem ofFun_apply (φ : (X → Y) → ℂ) (g : X → Y) : ofFun φ g = φ g := rfl

/-- The degree bounds increase. -/
theorem degLE_mono {d d' : ℕ} (h : d ≤ d') : (degLE d : Submodule ℂ (QState (X → Y))) ≤ degLE d' :=
  Submodule.span_mono fun _ ⟨T, hT, hf⟩ => ⟨T, hT.trans h, hf⟩

/-- **A function of the values on `T` has degree at most `|T|`.** -/
theorem mem_degLE_of_dependsOn {f : QState (X → Y)} (T : Finset X) {d : ℕ} (hT : T.card ≤ d)
    (hf : ∀ g g' : X → Y, (∀ x ∈ T, g x = g' x) → f g = f g') : f ∈ degLE d :=
  Submodule.subset_span ⟨T, hT, hf⟩

/-- **The pointwise product** as a bilinear map. -/
noncomputable def pmulₗ : QState (X → Y) →ₗ[ℂ] QState (X → Y) →ₗ[ℂ] QState (X → Y) :=
  LinearMap.mk₂ ℂ pmul
    (fun f f' h => by ext g; simp [pmul_apply, add_mul])
    (fun c f h => by ext g; simp [pmul_apply, mul_assoc])
    (fun f h h' => by ext g; simp [pmul_apply, mul_add])
    (fun c f h => by ext g; simp [pmul_apply, mul_left_comm])

theorem pmulₗ_apply (f h : QState (X → Y)) : pmulₗ f h = pmul f h := rfl

/-- The product of a `d₁`-junta and a `d₂`-junta is a `(d₁ + d₂)`-junta. -/
theorem pmul_mem_juntas {f h : QState (X → Y)} {d₁ d₂ : ℕ} (hf : f ∈ juntas d₁)
    (hh : h ∈ juntas d₂) : pmul f h ∈ juntas (d₁ + d₂) := by
  obtain ⟨T₁, hT₁, hf⟩ := hf
  obtain ⟨T₂, hT₂, hh⟩ := hh
  refine ⟨T₁ ∪ T₂, (card_union_le _ _).trans (Nat.add_le_add hT₁ hT₂), fun g g' hg => ?_⟩
  simp only [pmul_apply]
  rw [hf g g' fun x hx => hg x (mem_union_left _ hx),
    hh g g' fun x hx => hg x (mem_union_right _ hx)]

/-- **Products add degrees.** -/
theorem pmul_mem_degLE {f h : QState (X → Y)} {d₁ d₂ : ℕ} (hf : f ∈ degLE d₁)
    (hh : h ∈ degLE d₂) : pmul f h ∈ degLE (d₁ + d₂) := by
  have hm := Submodule.apply_mem_map₂ pmulₗ hf hh
  rw [degLE, degLE, Submodule.map₂_span_span] at hm
  refine Submodule.span_le.mpr ?_ hm
  rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
  exact Submodule.subset_span (pmul_mem_juntas hφ hψ)

omit [Fintype X] [Fintype Y] in
/-- **Exchanging the value at `x`**: `(g, y) ↦ (g[x ↦ y], g x)` is an involution. -/
theorem update_swap_involutive (x : X) :
    Function.Involutive fun p : (X → Y) × Y => (Function.update p.1 x p.2, p.1 x) := by
  rintro ⟨g, y⟩
  simp

/-- Reindexing a double sum over oracles and values by `(g, y) ↦ (g[x ↦ y], g x)`. -/
theorem sum_update_swap {M : Type*} [AddCommMonoid M] (x : X) (F : (X → Y) → Y → M) :
    ∑ g, ∑ y, F (Function.update g x y) (g x) = ∑ g, ∑ y, F g y := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Equiv.sum_comp ((update_swap_involutive x).toPerm _) fun p : (X → Y) × Y => F p.1 p.2

/-- **The average over the value at `x` is an orthogonal projection**: it is idempotent. -/
theorem avgAt_avgAt (x : X) (f : QState (X → Y)) : avgAt x (avgAt x f) = avgAt x f := by
  ext g
  have : Nonempty Y := ⟨g x⟩
  have hc : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avgAt_apply, Function.update_idem, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The average over the value at `x` is self-adjoint. -/
theorem inner_avgAt_left (x : X) (f h : QState (X → Y)) :
    inner ℂ (avgAt x f) h = inner ℂ f (avgAt x h) := by
  have key := sum_update_swap x fun g y =>
    (Fintype.card Y : ℂ)⁻¹ * (conj (f g) * h (Function.update g x y))
  simp only [Function.update_idem, Function.update_eq_self] at key
  simp only [PiLp.inner_apply, RCLike.inner_apply, avgAt_apply, map_mul, map_sum, map_inv₀,
    map_natCast, Finset.mul_sum, Finset.sum_mul]
  convert key using 3 <;> ring

/-- The averages at two points commute. -/
theorem avgAt_comm (x x' : X) (f : QState (X → Y)) :
    avgAt x (avgAt x' f) = avgAt x' (avgAt x f) := by
  by_cases hxx : x = x'
  · subst hxx; rfl
  ext g
  simp only [avgAt_apply, Finset.mul_sum, Function.update_comm hxx]
  rw [Finset.sum_comm]

/-- **Pythagoras**: orthogonal vectors have `‖u + v‖² = ‖u‖² + ‖v‖²`. -/
theorem norm_add_sq_of_inner_eq_zero {u v : QState (X → Y)} (h : inner ℂ u v = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  simp only [sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v h

/-- `avgAt x` is orthogonal to its complement: `⟪avgAt x u, v − avgAt x v⟫ = 0`. -/
theorem inner_avgAt_sub_avgAt (x : X) (u v : QState (X → Y)) :
    inner ℂ (avgAt x u) (v - avgAt x v) = 0 := by
  rw [inner_sub_right, inner_avgAt_left, inner_avgAt_left, avgAt_avgAt, sub_self]

/-- **Pythagoras for `avgAt x`**: `‖v‖² = ‖avgAt x v‖² + ‖v − avgAt x v‖²`. -/
theorem norm_sq_eq_avgAt (x : X) (v : QState (X → Y)) :
    ‖v‖ ^ 2 = ‖avgAt x v‖ ^ 2 + ‖v - avgAt x v‖ ^ 2 := by
  rw [← norm_add_sq_of_inner_eq_zero (inner_avgAt_sub_avgAt x v v),
    add_sub_cancel]

/-- `avgAt x` does not increase norms: `‖avgAt x v‖² ≤ ‖v‖²`. -/
theorem norm_avgAt_sq_le (x : X) (v : QState (X → Y)) : ‖avgAt x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_sq_eq_avgAt x v]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [Fintype X] [Fintype Y] in
/-- Inserting a point into `S`: `setOn (insert x S) g z = setOn S (g[x ↦ z x]) z` for `x ∉ S`. -/
theorem setOn_insert {S : Finset X} {x : X} (hx : x ∉ S) (g z : X → Y) :
    setOn (insert x S) g z = setOn S (Function.update g x (z x)) z := by
  funext w
  by_cases hw : w = x
  · subst hw; simp [setOn, hx]
  · by_cases hwS : w ∈ S <;> simp [setOn, hw, hwS]

omit [Fintype X] [Fintype Y] in
/-- `setOn S g z` does not read `z` outside `S`. -/
theorem setOn_update_right {S : Finset X} {x : X} (hx : x ∉ S) (g z : X → Y) (y : Y) :
    setOn S g (Function.update z x y) = setOn S g z := by
  funext w
  by_cases hwS : w ∈ S
  · have : w ≠ x := fun h => hx (h ▸ hwS)
    simp [setOn, hwS, this]
  · simp [setOn, hwS]

/-- Averaging over the empty set is the identity. -/
theorem avgOn_empty [Nonempty Y] (f : QState (X → Y)) : avgOn ∅ f = f := by
  ext g
  have hc : (Fintype.card (X → Y) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : ∀ z : X → Y, setOn ∅ g z = g := fun z => funext fun w => by simp [setOn]
  simp only [avgOn_apply, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Averaging over `insert x S`** is averaging over `S`, then over the value at `x`. -/
theorem avgOn_insert [Nonempty Y] {S : Finset X} {x : X} (hx : x ∉ S) (f : QState (X → Y)) :
    avgOn (insert x S) f = avgAt x (avgOn S f) := by
  ext g
  have hc : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key := sum_update_swap x fun z y => f (setOn S (Function.update g x y) z)
  simp only [setOn_update_right hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at key
  have key' : ∑ y, ∑ z, f (setOn S (Function.update g x y) z) =
      (Fintype.card Y : ℂ) * ∑ z, f (setOn S (Function.update g x (z x)) z) := by
    rw [Finset.sum_comm, ← key, Finset.mul_sum]
  simp only [avgOn_apply, avgAt_apply, setOn_insert hx, ← Finset.mul_sum, key']
  field_simp

/-- **`‖f − avgOn S f‖² ≤ ∑_{x ∈ S} ‖f − avgAt x f‖²`.** -/
theorem norm_sub_avgOn_sq_le [Nonempty Y] (S : Finset X) (f : QState (X → Y)) :
    ‖f - avgOn S f‖ ^ 2 ≤ ∑ x ∈ S, ‖f - avgAt x f‖ ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp [avgOn_empty]
  | insert x S hx ih =>
    rw [avgOn_insert hx, sum_insert hx]
    have hsplit : f - avgAt x (avgOn S f) = (f - avgAt x f) + avgAt x (f - avgOn S f) := by
      rw [map_sub]; abel
    have horth : inner ℂ (f - avgAt x f) (avgAt x (f - avgOn S f)) = 0 := by
      rw [← inner_conj_symm, inner_avgAt_sub_avgAt, map_zero]
    rw [hsplit, norm_add_sq_of_inner_eq_zero horth]
    exact add_le_add le_rfl ((norm_avgAt_sq_le x _).trans ih)

/-- `f` depends only on the values on `T`. -/
def DependsOn (f : QState (X → Y)) (T : Finset X) : Prop :=
  ∀ g g' : X → Y, (∀ x ∈ T, g x = g' x) → f g = f g'

/-- Depending on fewer points is stronger. -/
theorem DependsOn.mono {f : QState (X → Y)} {T T' : Finset X} (hf : DependsOn f T)
    (h : T ⊆ T') : DependsOn f T' :=
  fun g g' hg => hf g g' fun x hx => hg x (h hx)

/-- **`avgAt z` of a function of the values on `T`** depends only on the values on `T.erase z`. -/
theorem DependsOn.avgAt_erase {f : QState (X → Y)} {T : Finset X} (hf : DependsOn f T) (z : X) :
    DependsOn (avgAt z f) (T.erase z) := by
  intro g g' hg
  simp only [avgAt_apply]
  congr 1
  refine Finset.sum_congr rfl fun y _ => hf _ _ fun x hx => ?_
  by_cases hxz : x = z
  · subst hxz; simp
  · simp [Function.update_of_ne hxz, hg x (mem_erase.mpr ⟨hxz, hx⟩)]

/-- **`avgAt z` fixes a function that does not read `z`.** -/
theorem DependsOn.avgAt_eq_self [Nonempty Y] {f : QState (X → Y)} {T : Finset X}
    (hf : DependsOn f T) {z : X} (hz : z ∉ T) : avgAt z f = f := by
  ext g
  have hc : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : ∀ y, f (Function.update g z y) = f g := fun y => hf _ _ fun x hx => by
    have : x ≠ z := fun h => hz (h ▸ hx)
    simp [Function.update_of_ne this]
  simp only [avgAt_apply, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The Efron–Stein bound relative to a set of points `s`**: a function in the span of the
functions that depend on no more than `d` points of `s` has `∑_{x ∈ s} ‖f − avgAt x f‖² ≤ d ‖f‖²`. -/
theorem sum_norm_sub_avgAt_sq_le_of_mem_span [Nonempty Y] (s : Finset X) :
    ∀ (d : ℕ) (f : QState (X → Y)),
      f ∈ Submodule.span ℂ {f | ∃ T : Finset X, (T ∩ s).card ≤ d ∧ DependsOn f T} →
      ∑ x ∈ s, ‖f - avgAt x f‖ ^ 2 ≤ d * ‖f‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => intro d f _; simp; positivity
  | insert z s hz ih =>
    intro d f hf
    set f₀ := avgAt z f with hf₀
    set f₁ := f - avgAt z f with hf₁
    -- `f₀` has degree at most `d` in `s`
    have h₀ : f₀ ∈ Submodule.span ℂ {f | ∃ T : Finset X, (T ∩ s).card ≤ d ∧ DependsOn f T} := by
      refine (Submodule.span_le (p := (Submodule.span ℂ _).comap (avgAt z))).mpr ?_ hf
      rintro φ ⟨T, hT, hφ⟩
      refine Submodule.subset_span ⟨T.erase z, le_trans (card_le_card fun x hx => ?_) hT, hφ.avgAt_erase z⟩
      simp only [mem_inter, mem_erase, mem_insert] at hx ⊢
      exact ⟨hx.1.2, Or.inr hx.2⟩
    -- `f₁` has degree at most `d - 1` in `s`, and vanishes when `d = 0`
    have h₁ : f₁ ∈ Submodule.span ℂ {f | ∃ T : Finset X, (T ∩ s).card ≤ d - 1 ∧ DependsOn f T} ∧
        (d = 0 → f₁ = 0) := by
      have hle := (Submodule.span_le (p := ((Submodule.span ℂ
        {f | ∃ T : Finset X, (T ∩ s).card ≤ d - 1 ∧ DependsOn f T}) ⊓
        (if d = 0 then ⊥ else ⊤)).comap (LinearMap.id - avgAt z))).mpr ?_ hf
      · refine ⟨(Submodule.mem_inf.mp hle).1, fun hd => ?_⟩
        have := (Submodule.mem_inf.mp hle).2
        simpa [hd] using this
      rintro φ ⟨T, hT, hφ⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
      by_cases hzT : z ∈ T
      · have hcard : (T ∩ insert z s) = insert z (T ∩ s) := by
          ext x; simp only [mem_inter, mem_insert]; constructor
          · rintro ⟨h1, h2 | h2⟩
            · exact Or.inl h2
            · exact Or.inr ⟨h1, h2⟩
          · rintro (h | ⟨h1, h2⟩)
            · exact ⟨h ▸ hzT, Or.inl h⟩
            · exact ⟨h1, Or.inr h2⟩
        have hzs : z ∉ T ∩ s := fun h => hz (mem_inter.mp h).2
        rw [hcard, card_insert_of_notMem hzs] at hT
        have hd : d ≠ 0 := by omega
        refine Submodule.mem_inf.mpr ⟨Submodule.subset_span ⟨T, by omega, fun g g' hg => ?_⟩,
          by simp [hd]⟩
        simp only [PiLp.sub_apply]
        rw [hφ g g' hg, (hφ.avgAt_erase z).mono (erase_subset z T) g g' hg]
      · rw [hφ.avgAt_eq_self hzT, sub_self]
        exact zero_mem _
    obtain ⟨h₁, h₁0⟩ := h₁
    have hdecomp : f = f₀ + f₁ := by rw [hf₀, hf₁]; abel
    -- for `x ∈ s`, the split of `f − avgAt x f` into its two orthogonal parts
    have hx : ∀ x ∈ s, ‖f - avgAt x f‖ ^ 2 =
        ‖f₀ - avgAt x f₀‖ ^ 2 + ‖f₁ - avgAt x f₁‖ ^ 2 := by
      intro x _
      rw [norm_sq_eq_avgAt z (f - avgAt x f)]
      congr 2
      · rw [hf₀, map_sub, avgAt_comm]
      · rw [hf₁, map_sub, map_sub, avgAt_comm z x]; congr 1; abel
    rw [sum_insert hz, Finset.sum_congr rfl hx, Finset.sum_add_distrib]
    have e0 := ih d f₀ h₀
    have e1 := ih (d - 1) f₁ h₁
    have hn : ‖f‖ ^ 2 = ‖f₀‖ ^ 2 + ‖f₁‖ ^ 2 := norm_sq_eq_avgAt z f
    rw [hn]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · have := h₁0 hd
      simp only [hd, Nat.zero_sub, Nat.cast_zero, zero_mul] at e0 e1 ⊢
      rw [show f - avgAt z f = f₁ from rfl, this] at *
      simp at e0 e1 ⊢
      linarith
    · have hcast : ((d - 1 : ℕ) : ℝ) = d - 1 := by rw [Nat.cast_sub hd]; simp
      rw [hcast] at e1
      have : ‖f - avgAt z f‖ = ‖f₁‖ := rfl
      rw [this]
      nlinarith

/-- **The Efron–Stein bound for functions of bounded degree**: a function of degree at most `d`
has `∑_x ‖f − avgAt x f‖² ≤ d ‖f‖²`. -/
theorem sum_norm_sub_avgAt_sq_le [Nonempty Y] {d : ℕ} {f : QState (X → Y)} (hf : f ∈ degLE d) :
    ∑ x, ‖f - avgAt x f‖ ^ 2 ≤ d * ‖f‖ ^ 2 := by
  refine sum_norm_sub_avgAt_sq_le_of_mem_span univ d f (Submodule.span_mono ?_ hf)
  rintro φ ⟨T, hT, hφ⟩
  exact ⟨T, by rwa [inter_univ], hφ⟩

/-! ### Classical oracle programs -/

variable {X' Y' R : Type*} [Fintype Y'] [DecidableEq Y']

/-- **An oracle read pointwise from `g`**: its value at each point `a` either is the same for any
two `g` that agree at one point `x`, or does not depend on `g`. -/
def ReadsPointwise (O : (X → Y) → X' → Y') : Prop :=
  ∀ a, (∃ x, ∀ g g' : X → Y, g x = g' x → O g a = O g' a) ∨ ∀ g g' : X → Y, O g a = O g' a

omit [Fintype Y'] in
/-- **The indicator of one answer of an oracle read pointwise** has degree at most `1`. -/
theorem ReadsPointwise.indicator_mem_degLE {O : (X → Y) → X' → Y'} (hO : ReadsPointwise O)
    (a : X') (y : Y') : ofFun (fun g => if O g a = y then 1 else 0) ∈ degLE 1 := by
  rcases hO a with ⟨x, hx⟩ | hc
  · refine mem_degLE_of_dependsOn {x} (by simp) fun g g' hg => ?_
    simp only [ofFun_apply, hx g g' (hg x (mem_singleton_self x))]
  · refine mem_degLE_of_dependsOn ∅ (by simp) fun g g' _ => ?_
    simp only [ofFun_apply, hc g g']

/-- **The decision-tree bound with a guard**: if the indicator of `c` has degree at most `m` and
`p` makes at most `q` queries wherever `c` holds, the indicator that `c` holds and `p` returns `r`
has degree at most `m + q`. -/
theorem indicator_guard_run_mem_degLE [DecidableEq R] {O : (X → Y) → X' → Y'}
    (hO : ReadsPointwise O) (r : R) (p : OracleProg X' Y' R) :
    ∀ (q m : ℕ) (c : (X → Y) → Bool), ofFun (fun g => if c g then 1 else 0) ∈ degLE m →
      (∀ g, c g → (p.trace (O g)).length ≤ q) →
      ofFun (fun g => if c g ∧ p.run (O g) = r then 1 else 0) ∈ degLE (m + q) := by
  induction p with
  | pure r' =>
    intro q m c hc _
    by_cases h : r' = r
    · have : (ofFun fun g => if c g ∧ (OracleProg.pure r' : OracleProg X' Y' R).run (O g) = r
          then (1 : ℂ) else 0) = ofFun fun g => if c g then 1 else 0 :=
        congrArg ofFun (funext fun g => by simp [h])
      rw [this]
      exact degLE_mono (Nat.le_add_right m q) hc
    · have : (ofFun fun g => if c g ∧ (OracleProg.pure r' : OracleProg X' Y' R).run (O g) = r
          then (1 : ℂ) else 0) = 0 :=
        congrArg ofFun (funext fun g => by simp [h])
      rw [this]
      exact zero_mem _
  | query a k ih =>
    intro q m c hc hq
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · have : (ofFun fun g => if c g ∧ (OracleProg.query a k).run (O g) = r
          then (1 : ℂ) else 0) = 0 := by
        refine congrArg ofFun (funext fun g => ?_)
        have := hq g
        by_cases hcg : c g = true
        · have := this hcg; simp at this; omega
        · simp [hcg]
      rw [this]
      exact zero_mem _
    have hsum : (ofFun fun g => if c g ∧ (OracleProg.query a k).run (O g) = r
        then (1 : ℂ) else 0) = ∑ y, ofFun fun g =>
          if (c g && decide (O g a = y)) ∧ (k y).run (O g) = r then (1 : ℂ) else 0 := by
      ext g
      simp only [ofFun_apply, OracleProg.run_query, WithLp.ofLp_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single (O g a)]
      · by_cases h : c g = true ∧ (k (O g a)).run (O g) = r <;> simp_all
        exact if_congr Iff.rfl rfl rfl
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
    rw [hsum]
    refine Submodule.sum_mem _ fun y _ => ?_
    have hguard : ofFun (fun g => if (c g && decide (O g a = y)) then (1 : ℂ) else 0) ∈
        degLE (m + 1) := by
      have : ofFun (fun g => if (c g && decide (O g a = y)) then (1 : ℂ) else 0) =
          pmul (ofFun fun g => if c g then 1 else 0) (ofFun fun g => if O g a = y then 1 else 0) :=
        congrArg ofFun (funext fun g => by
          by_cases h1 : c g = true <;> by_cases h2 : O g a = y <;> simp [h1, h2, ofFun_apply])
      rw [this]
      exact pmul_mem_degLE hc (hO.indicator_mem_degLE a y)
    have := ih y (q - 1) (m + 1) _ hguard fun g hg => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have := hq g hg.1
      simp only [OracleProg.trace_query, List.length_cons, hg.2] at this
      omega
    rwa [show m + 1 + (q - 1) = m + q by omega] at this

/-- **A program making at most `q` queries, run against an oracle read pointwise from `g`,
returns `r` with an indicator of degree at most `q`** (a decision tree of depth `q`). -/
theorem indicator_run_mem_degLE [DecidableEq R] {O : (X → Y) → X' → Y'} (hO : ReadsPointwise O)
    (p : OracleProg X' Y' R) {q : ℕ} (hq : ∀ g, (p.trace (O g)).length ≤ q) (r : R) :
    ofFun (fun g => if p.run (O g) = r then 1 else 0) ∈ degLE q := by
  have h1 : ofFun (fun _ : X → Y => if true then (1 : ℂ) else 0) ∈ degLE 0 :=
    mem_degLE_of_dependsOn ∅ (by simp) fun _ _ _ => rfl
  have := indicator_guard_run_mem_degLE hO r p q 0 (fun _ => true) h1 fun g _ => hq g
  simpa using this

/-! ### Sums, products and indicators of bounded degree -/

section Helpers

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]

/-- `ofFun` of a finite sum is the sum of the `ofFun`s. -/
theorem ofFun_sum {κ : Type*} (s : Finset κ) (φ : κ → (X → Y) → ℂ) :
    ofFun (fun g => ∑ i ∈ s, φ i g) = ∑ i ∈ s, ofFun (φ i) := by
  ext g
  simp [ofFun_apply]

/-- `ofFun` of a scalar multiple is the scalar multiple. -/
theorem ofFun_const_mul (c : ℂ) (φ : (X → Y) → ℂ) :
    ofFun (fun g => c * φ g) = c • ofFun φ := by
  ext g
  simp [ofFun_apply]

/-- A function that does not depend on the oracle has every degree. -/
theorem ofFun_const_mem_degLE (c : ℂ) (d : ℕ) : ofFun (fun _ : X → Y => c) ∈ degLE d :=
  mem_degLE_of_dependsOn ∅ (by simp) fun _ _ _ => rfl

/-- A pointwise product of functions of degrees `a` and `b` has every degree `c ≥ a + b`. -/
theorem ofFun_mul_mem_degLE {φ ψ : (X → Y) → ℂ} {a b c : ℕ} (hφ : ofFun φ ∈ degLE a)
    (hψ : ofFun ψ ∈ degLE b) (hab : a + b ≤ c) : ofFun (fun g => φ g * ψ g) ∈ degLE c :=
  degLE_mono hab (pmul_mem_degLE hφ hψ)

/-- A product over `s` of functions of degree at most `a` has degree at most `|s| · a`. -/
theorem prod_mem_degLE {κ : Type*} [DecidableEq κ] (s : Finset κ) (φ : κ → (X → Y) → ℂ) {a : ℕ}
    (h : ∀ i ∈ s, ofFun (φ i) ∈ degLE a) :
    ofFun (fun g => ∏ i ∈ s, φ i g) ∈ degLE (s.card * a) := by
  induction s using Finset.induction_on with
  | empty => simpa using ofFun_const_mem_degLE (X := X) (Y := Y) 1 0
  | insert i s hi ih =>
    simp only [prod_insert hi, card_insert_of_notMem hi]
    exact ofFun_mul_mem_degLE (h i (mem_insert_self i s))
      (ih fun j hj => h j (mem_insert_of_mem hj)) (by rw [add_mul, one_mul, add_comm])

/-- If every value indicator of `φ` has degree at most `a`, so does the indicator of every event
of `φ`. -/
theorem indicator_comp_mem_degLE {β : Type*} [Fintype β] [DecidableEq β] (φ : (X → Y) → β)
    {a : ℕ} (h : ∀ b, ofFun (fun g => if φ g = b then 1 else 0) ∈ degLE a) (P : β → Prop)
    [DecidablePred P] : ofFun (fun g => if P (φ g) then 1 else 0) ∈ degLE a := by
  have hs : (fun g => if P (φ g) then (1 : ℂ) else 0) =
      fun g => ∑ b ∈ univ.filter P, if φ g = b then 1 else 0 := by
    funext g
    simp [Finset.sum_ite_eq]
  rw [hs, ofFun_sum]
  exact Submodule.sum_mem _ fun b _ => h b

/-- Indicators of equivalent events lie in the same submodules. -/
theorem ofFun_indicator_mem_of_iff {P P' : (X → Y) → Prop} {_ : DecidablePred P}
    {_ : DecidablePred P'} {S : Submodule ℂ (QState (X → Y))} (h : ∀ g, P g ↔ P' g)
    (h' : ofFun (fun g => if P' g then (1 : ℂ) else 0) ∈ S) :
    ofFun (fun g => if P g then (1 : ℂ) else 0) ∈ S := by
  rwa [congrArg ofFun (funext fun g => if_congr (h g) rfl rfl)]


end Helpers

end Junta

end GordieHowe.Quantum
