-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.FourierProduct
public import GordieHowe.Foundations.ToMathlib.CharacterSums
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Regularity of a linear image against a character expansion

An abstract form of the Fourier step of the HighBits regularity argument ("A shorter proof of the
stated HighBits regularity claim", 10 September 2026, Sections 2-3), proved for a fixed key and
averaged over a uniform matrix `A` of a finite group `𝒜`. The value `w = M_z A - c₀` is linear in
`A` for each mask `z` (drawn uniformly from a finite set `Zs`), and the accept indicator is a
combination `∑_t c_t ∏_i G_{t, Ψ A, v} i (w_i)` of product functions of the coordinates of `w`, for
each output `v`, that sees `A` only through `Ψ A` (in the application `Ψ A = A s₁`, through
`t₀`).

`sum_sum_norm_le` states
`𝔼_A ∑_v |p_A(v) - s_A(v)| ≤ Λ √(|V| B)` with `Λ = ∑_t |c_t|` (and `sum_sq_sum_norm_le` its
`ℓ²` form `𝔼_A (∑_v |p_A(v) - s_A(v)|)² ≤ Λ² |V| B`), where `p_A` averages over the
masks and `s_A` over uniform `w`, provided that for every `t` and every value `τ` of `Ψ`, the
pair kernels `K(ξ, η) = ∑_v Ĝ_v(ξ) conj Ĝ_v(η)` summed over the nonzero modes `(ξ, η)` that
survive the kernel average for masks `z, z'` (`Admissible`) average to at most `B`.

The steps: Fourier expansion and cancellation of the zero mode (`avg_sub_uniform_eq`); expanding
`∑_v |D_v|²` into pair kernels; averaging over `A` on the kernel of `Ψ`
(`AddChar.norm_sum_comp_mul_le`), which leaves the admissible modes and keeps the kernel inside the
`A` average (so the bound `B` is needed only for each fixed `Ψ A`); Cauchy–Schwarz over the
expansion terms; and `ℓ¹ ≤ √(|V| ℓ²)` with Jensen over `A`.
-/

open Finset ComplexConjugate
open scoped BigOperators

namespace ZMod

variable {N : ℕ} [NeZero N] {I : Type*} [Fintype I] [DecidableEq I]

/-- The dot product `ξ · u = ∑_i ξ_i u_i`. -/
def dot (ξ u : I → ZMod N) : ZMod N := ∑ i, ξ i * u i

/-- The Fourier coefficient of a product function at `ξ`: `∏_i fourierCoeff g_i ξ_i`. -/
noncomputable def prodFourier (g : I → ZMod N → ℂ) (ξ : I → ZMod N) : ℂ :=
  ∏ i, fourierCoeff (g i) (ξ i)

/-- The average of a product function over finitely many points minus its uniform average is
the sum over the nonzero modes of the Fourier coefficient times the average character. -/
theorem avg_sub_uniform_eq {ζ : Type*} (Zs : Finset ζ) (hZ : Zs.Nonempty)
    (w : ζ → I → ZMod N) (g : I → ZMod N → ℂ) :
    (#Zs : ℂ)⁻¹ * ∑ z ∈ Zs, ∏ i, g i (w z i) -
        ((N : ℂ) ^ Fintype.card I)⁻¹ * ∑ u : I → ZMod N, ∏ i, g i (u i) =
      ∑ ξ ∈ univ.erase 0, prodFourier g ξ *
        ((#Zs : ℂ)⁻¹ * ∑ z ∈ Zs, stdAddChar (dot ξ (w z))) := by
  have hN : ((N : ℂ) ^ Fintype.card I) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hZ0 : (#Zs : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hZ)
  simp_rw [prod_eq_sum_fourier g]
  have huni : ((N : ℂ) ^ Fintype.card I)⁻¹ * ∑ u : I → ZMod N, ∑ ξ : I → ZMod N,
      (∏ i, fourierCoeff (g i) (ξ i)) * stdAddChar (∑ i, ξ i * u i) = prodFourier g 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_stdAddChar_dot]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' univ (0 : I → ZMod N), if_pos (Finset.mem_univ _), prodFourier]
    field_simp
  rw [huni, Finset.sum_comm, Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have h0 : (#Zs : ℂ)⁻¹ * ∑ z ∈ Zs, (∏ i, fourierCoeff (g i) ((0 : I → ZMod N) i)) *
      stdAddChar (∑ i, (0 : I → ZMod N) i * w z i) = prodFourier g 0 := by
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, AddChar.map_zero_eq_one, mul_one,
      Finset.sum_const, nsmul_eq_mul, prodFourier]
    field_simp
  rw [h0, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [prodFourier, dot]
  ring

/-- The dot product with `ξ` as an additive map. -/
def dotHom (ξ : I → ZMod N) : (I → ZMod N) →+ ZMod N where
  toFun := dot ξ
  map_zero' := by simp [dot]
  map_add' u v := by simp [dot, mul_add, Finset.sum_add_distrib]

omit [NeZero N] [DecidableEq I] in
theorem dot_sub (ξ u v : I → ZMod N) : dot ξ (u - v) = dot ξ u - dot ξ v :=
  map_sub (dotHom ξ) u v

section Average

variable {𝒜 𝒯 V ζ : Type*} [AddCommGroup 𝒜] [Fintype 𝒜] [AddCommGroup 𝒯] [Fintype V]

/-- The pair kernel `K(ξ, η) = ∑_v Ĝ_v(ξ) · conj Ĝ_v(η)` of a family of product functions. -/
noncomputable def pairKernel (G : V → I → ZMod N → ℂ) (ξ η : I → ZMod N) : ℂ :=
  ∑ v, prodFourier (G v) ξ * conj (prodFourier (G v) η)

/-- A pair of modes `(ξ, η)` survives the average over `A` on the cosets of `ker Ψ` for masks
`z, z'`: the character `A ↦ e(ξ · M_z A - η · M_{z'} A)` is trivial on `ker Ψ`. -/
def Admissible (Ψ : 𝒜 →+ 𝒯) (M : ζ → 𝒜 →+ (I → ZMod N)) (z z' : ζ) (ξ η : I → ZMod N) : Prop :=
  ∀ K, Ψ K = 0 → stdAddChar (dot ξ (M z K) - dot η (M z' K)) = 1

open Classical in
/-- The admissible kernel mass at `τ`: the masks-averaged sum of `‖K_τ(ξ, η)‖` over the nonzero
admissible pairs of modes. -/
noncomputable def admissibleMass (Ψ : 𝒜 →+ 𝒯) (Zs : Finset ζ) (M : ζ → 𝒜 →+ (I → ZMod N))
    (G : 𝒯 → V → I → ZMod N → ℂ) (τ : 𝒯) : ℝ :=
  ∑ ξ ∈ univ.erase 0, ∑ η ∈ univ.erase 0, ((#Zs : ℝ) ^ 2)⁻¹ * ∑ z ∈ Zs, ∑ z' ∈ Zs,
    if Admissible Ψ M z z' ξ η then ‖pairKernel (G τ) ξ η‖ else 0

/-- The difference between the mask average and the uniform average of the product function of
output `v`, at the matrix `A`. -/
noncomputable def maskDiff (Ψ : 𝒜 →+ 𝒯) (Zs : Finset ζ) (M : ζ → 𝒜 →+ (I → ZMod N))
    (c₀ : I → ZMod N) (G : 𝒯 → V → I → ZMod N → ℂ) (A : 𝒜) (v : V) : ℂ :=
  (#Zs : ℂ)⁻¹ * ∑ z ∈ Zs, ∏ i, G (Ψ A) v i ((M z A - c₀) i) -
    ((N : ℂ) ^ Fintype.card I)⁻¹ * ∑ u : I → ZMod N, ∏ i, G (Ψ A) v i (u i)

open Classical in
/-- **The kernel average.** `∑_A ∑_v ‖D_A(v)‖² ≤ ∑_A admissibleMass (Ψ A)`: expanding the square
into pair kernels and averaging each character `A ↦ e(ξ · M_z A - η · M_{z'} A)` against the
kernel, which depends on `A` only through `Ψ A`, leaves the admissible pairs. -/
theorem sum_sum_normSq_maskDiff_le (Ψ : 𝒜 →+ 𝒯) (Zs : Finset ζ) (hZ : Zs.Nonempty)
    (M : ζ → 𝒜 →+ (I → ZMod N)) (c₀ : I → ZMod N) (G : 𝒯 → V → I → ZMod N → ℂ) :
    ∑ A, ∑ v, ‖maskDiff Ψ Zs M c₀ G A v‖ ^ 2 ≤ ∑ A, admissibleMass Ψ Zs M G (Ψ A) := by
  set E := univ.erase (0 : I → ZMod N)
  set κ : ℝ := ((#Zs : ℝ) ^ 2)⁻¹
  -- the phase and the character of each pair of modes and masks
  let ph : (I → ZMod N) → (I → ZMod N) → ℂ := fun ξ η => stdAddChar (dot η c₀ - dot ξ c₀)
  let ℓ : ζ → ζ → (I → ZMod N) → (I → ZMod N) → 𝒜 →+ ZMod N := fun z z' ξ η =>
    (dotHom ξ).comp (M z) - (dotHom η).comp (M z')
  have hexp : ∀ A, ∑ v, maskDiff Ψ Zs M c₀ G A v * conj (maskDiff Ψ Zs M c₀ G A v) =
      ∑ ξ ∈ E, ∑ η ∈ E, ∑ z ∈ Zs, ∑ z' ∈ Zs,
        (κ : ℂ) * ph ξ η * (pairKernel (G (Ψ A)) ξ η * dotAddChar (ℓ z z' ξ η) A) := by
    intro A
    set a : (I → ZMod N) → ℂ := fun ξ =>
      (#Zs : ℂ)⁻¹ * ∑ z ∈ Zs, stdAddChar (dot ξ (M z A - c₀))
    have hD : ∀ v, maskDiff Ψ Zs M c₀ G A v = ∑ ξ ∈ E, prodFourier (G (Ψ A) v) ξ * a ξ :=
      fun v => avg_sub_uniform_eq Zs hZ (fun z => M z A - c₀) (G (Ψ A) v)
    have hL : ∑ v, maskDiff Ψ Zs M c₀ G A v * conj (maskDiff Ψ Zs M c₀ G A v) =
        ∑ ξ ∈ E, ∑ η ∈ E, pairKernel (G (Ψ A)) ξ η * (a ξ * conj (a η)) := by
      simp_rw [hD, map_sum, map_mul, Finset.sum_mul_sum, pairKernel, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun v _ => ?_
      ring
    have hb : ∀ ξ η, a ξ * conj (a η) =
        ∑ z ∈ Zs, ∑ z' ∈ Zs, (κ : ℂ) * ph ξ η * dotAddChar (ℓ z z' ξ η) A := by
      intro ξ η
      simp only [a, map_mul, map_inv₀, map_natCast, map_sum]
      rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, dotAddChar_apply]
      have : dot ξ (M z A - c₀) + -dot η (M z' A - c₀) =
          (dot η c₀ - dot ξ c₀) + ℓ z z' ξ η A := by
        simp only [ℓ, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply, dotHom,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, dot_sub]
        ring
      rw [this, AddChar.map_add_eq_mul]
      simp only [κ]
      push_cast
      ring
    rw [hL]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
    rw [hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z' _ => ?_
    ring
  -- swap the average over `A` inside
  have hswap : ∑ A, ∑ v, maskDiff Ψ Zs M c₀ G A v * conj (maskDiff Ψ Zs M c₀ G A v) =
      ∑ ξ ∈ E, ∑ η ∈ E, ∑ z ∈ Zs, ∑ z' ∈ Zs, (κ : ℂ) * ph ξ η *
        ∑ A, pairKernel (G (Ψ A)) ξ η * dotAddChar (ℓ z z' ξ η) A := by
    simp_rw [hexp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
  have hre : ∀ A, ∑ v, ‖maskDiff Ψ Zs M c₀ G A v‖ ^ 2 =
      (∑ v, maskDiff Ψ Zs M c₀ G A v * conj (maskDiff Ψ Zs M c₀ G A v)).re := by
    intro A
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hκ0 : 0 ≤ κ := by positivity
  calc ∑ A, ∑ v, ‖maskDiff Ψ Zs M c₀ G A v‖ ^ 2
      = (∑ A, ∑ v, maskDiff Ψ Zs M c₀ G A v * conj (maskDiff Ψ Zs M c₀ G A v)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun A _ => hre A
    _ ≤ ‖∑ A, ∑ v, maskDiff Ψ Zs M c₀ G A v * conj (maskDiff Ψ Zs M c₀ G A v)‖ :=
        Complex.re_le_norm _
    _ ≤ ∑ ξ ∈ E, ∑ η ∈ E, ∑ z ∈ Zs, ∑ z' ∈ Zs, κ *
          (if Admissible Ψ M z z' ξ η then ∑ A, ‖pairKernel (G (Ψ A)) ξ η‖ else 0) := by
        rw [hswap]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z' _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0, AddChar.norm_apply,
          mul_one]
        refine mul_le_mul_of_nonneg_left ?_ hκ0
        refine (AddChar.norm_sum_comp_mul_le Ψ (dotAddChar (ℓ z z' ξ η))
          (fun τ => pairKernel (G τ) ξ η)).trans (le_of_eq (if_congr Iff.rfl rfl rfl))
    _ = ∑ A, admissibleMass Ψ Zs M G (Ψ A) := by
        simp only [admissibleMass, Finset.mul_sum]
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z' _ => ?_
        split_ifs <;> simp [Finset.mul_sum, κ]

/-- Weighted Cauchy–Schwarz: `(∑_t a_t b_t)² ≤ (∑_t a_t)(∑_t a_t b_t²)` for `a ≥ 0`. -/
theorem sq_sum_mul_le_sum_mul_sum_mul_sq {R : Type*} (s : Finset R) {a b : R → ℝ}
    (ha : ∀ t, 0 ≤ a t) : (∑ t ∈ s, a t * b t) ^ 2 ≤ (∑ t ∈ s, a t) * ∑ t ∈ s, a t * b t ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun t => √(a t)) fun t => √(a t) * b t
  have e1 : ∀ t, √(a t) * (√(a t) * b t) = a t * b t := fun t => by
    rw [← mul_assoc, Real.mul_self_sqrt (ha t)]
  have e2 : ∀ t, √(a t) ^ 2 = a t := fun t => Real.sq_sqrt (ha t)
  have e3 : ∀ t, (√(a t) * b t) ^ 2 = a t * b t ^ 2 := fun t => by rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

/-- **The second moment of the expansion.** For an expansion `∑_t c_t ∏_i G_{t, Ψ A, v} i` of
the accept indicator and admissible kernel masses at most `B` for every `t` and `τ`,
`∑_A ∑_v ‖∑_t c_t D_{t, A}(v)‖² ≤ |𝒜| · Λ² · B` with `Λ = ∑_t ‖c_t‖`: Cauchy–Schwarz over the
expansion terms and the kernel average (`sum_sum_normSq_maskDiff_le`). -/
theorem sum_sum_normSq_le {R : Type*} [Fintype R] (Ψ : 𝒜 →+ 𝒯) (Zs : Finset ζ)
    (hZ : Zs.Nonempty) (M : ζ → 𝒜 →+ (I → ZMod N)) (c₀ : I → ZMod N) (c : R → ℂ)
    (G : R → 𝒯 → V → I → ZMod N → ℂ) {B : ℝ}
    (hB : ∀ t τ, admissibleMass Ψ Zs M (G t) τ ≤ B) :
    ∑ A, ∑ v, ‖∑ t, c t * maskDiff Ψ Zs M c₀ (G t) A v‖ ^ 2 ≤
      Fintype.card 𝒜 * ((∑ t, ‖c t‖) ^ 2 * B) := by
  set Λ := ∑ t, ‖c t‖
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun t _ => norm_nonneg _
  set D := fun t A v => maskDiff Ψ Zs M c₀ (G t) A v
  -- Cauchy–Schwarz over the expansion terms
  have hpt : ∀ A v, ‖∑ t, c t * D t A v‖ ^ 2 ≤ Λ * ∑ t, ‖c t‖ * ‖D t A v‖ ^ 2 := by
    intro A v
    have h1 : ‖∑ t, c t * D t A v‖ ≤ ∑ t, ‖c t‖ * ‖D t A v‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun t _ => norm_mul _ _))
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (sq_sum_mul_le_sum_mul_sum_mul_sq _ fun t => norm_nonneg _)
  calc ∑ A, ∑ v, ‖∑ t, c t * D t A v‖ ^ 2 ≤ ∑ A, ∑ v, Λ * ∑ t, ‖c t‖ * ‖D t A v‖ ^ 2 :=
          Finset.sum_le_sum fun A _ => Finset.sum_le_sum fun v _ => hpt A v
      _ = Λ * ∑ t, ‖c t‖ * ∑ A, ∑ v, ‖D t A v‖ ^ 2 := by
          have h1 : ∀ A, ∑ v, Λ * ∑ t, ‖c t‖ * ‖D t A v‖ ^ 2 =
              Λ * ∑ t, ∑ v, ‖c t‖ * ‖D t A v‖ ^ 2 := fun A => by
            rw [← Finset.mul_sum, Finset.sum_comm]
          simp_rw [h1]
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [Finset.mul_sum]
      _ ≤ Λ * ∑ t, ‖c t‖ * (Fintype.card 𝒜 * B) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hΛ
          refine (sum_sum_normSq_maskDiff_le Ψ Zs hZ M c₀ (G t)).trans ?_
          calc ∑ A, admissibleMass Ψ Zs M (G t) (Ψ A) ≤ ∑ _A : 𝒜, B :=
                Finset.sum_le_sum fun A _ => hB t _
            _ = Fintype.card 𝒜 * B := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = Fintype.card 𝒜 * (Λ ^ 2 * B) := by
          rw [← Finset.sum_mul]
          ring

/-- **The regularity bound, `ℓ²` form.** Under the hypotheses of `sum_sum_normSq_le`,
`∑_A (∑_v ‖∑_t c_t D_{t, A}(v)‖)² ≤ |𝒜| · Λ² · |V| B`: Cauchy–Schwarz over `v` and the second
moment of the expansion. -/
theorem sum_sq_sum_norm_le {R : Type*} [Fintype R] (Ψ : 𝒜 →+ 𝒯) (Zs : Finset ζ)
    (hZ : Zs.Nonempty) (M : ζ → 𝒜 →+ (I → ZMod N)) (c₀ : I → ZMod N) (c : R → ℂ)
    (G : R → 𝒯 → V → I → ZMod N → ℂ) {B : ℝ}
    (hB : ∀ t τ, admissibleMass Ψ Zs M (G t) τ ≤ B) :
    ∑ A, (∑ v, ‖∑ t, c t * maskDiff Ψ Zs M c₀ (G t) A v‖) ^ 2 ≤
      Fintype.card 𝒜 * ((∑ t, ‖c t‖) ^ 2 * (Fintype.card V * B)) := by
  set D := fun t A v => maskDiff Ψ Zs M c₀ (G t) A v
  calc ∑ A, (∑ v, ‖∑ t, c t * D t A v‖) ^ 2
      ≤ ∑ A, (Fintype.card V : ℝ) * ∑ v, ‖∑ t, c t * D t A v‖ ^ 2 :=
        Finset.sum_le_sum fun A _ => by
          simpa only [Finset.card_univ] using
            sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => ‖∑ t, c t * D t A v‖)
    _ = Fintype.card V * ∑ A, ∑ v, ‖∑ t, c t * D t A v‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ Fintype.card V * (Fintype.card 𝒜 * ((∑ t, ‖c t‖) ^ 2 * B)) :=
        mul_le_mul_of_nonneg_left (sum_sum_normSq_le Ψ Zs hZ M c₀ c G hB) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- **The regularity bound.** For an expansion `∑_t c_t ∏_i G_{t, Ψ A, v} i` of the accept
indicator and admissible kernel masses at most `B ≥ 0` for every `t` and `τ`,
`∑_A ∑_v ‖∑_t c_t D_{t, A}(v)‖ ≤ |𝒜| · Λ · √(|V| B)` with `Λ = ∑_t ‖c_t‖`, where `D_{t, A}(v)` is
the mask average minus the uniform average of the `t`-th product function (`maskDiff`). -/
theorem sum_sum_norm_le {R : Type*} [Fintype R] (Ψ : 𝒜 →+ 𝒯) (Zs : Finset ζ) (hZ : Zs.Nonempty)
    (M : ζ → 𝒜 →+ (I → ZMod N)) (c₀ : I → ZMod N) (c : R → ℂ)
    (G : R → 𝒯 → V → I → ZMod N → ℂ) {B : ℝ}
    (hB : ∀ t τ, admissibleMass Ψ Zs M (G t) τ ≤ B) :
    ∑ A, ∑ v, ‖∑ t, c t * maskDiff Ψ Zs M c₀ (G t) A v‖ ≤
      Fintype.card 𝒜 * (∑ t, ‖c t‖) * √(Fintype.card V * B) := by
  set Λ := ∑ t, ‖c t‖
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun t _ => norm_nonneg _
  set D := fun t A v => maskDiff Ψ Zs M c₀ (G t) A v
  set X : 𝒜 → ℝ := fun A => ∑ v, ‖∑ t, c t * D t A v‖ ^ 2
  have hX0 : ∀ A, 0 ≤ X A := fun A => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hsumX : ∑ A, X A ≤ Fintype.card 𝒜 * (Λ ^ 2 * B) := sum_sum_normSq_le Ψ Zs hZ M c₀ c G hB
  -- `ℓ¹ ≤ √(|V| ℓ²)` per `A`, then over `A`
  have hv : ∀ A, ∑ v, ‖∑ t, c t * D t A v‖ ≤ √(Fintype.card V * X A) := by
    intro A
    have := Finset.sum_abs_le_sqrt_card_mul_sum_sq univ fun v => ‖∑ t, c t * D t A v‖
    simpa only [abs_norm, Finset.card_univ] using this
  have hA : ∑ A, √(Fintype.card V * X A) ≤
      √(Fintype.card 𝒜 * ∑ A, Fintype.card V * X A) := by
    have := Finset.sum_abs_le_sqrt_card_mul_sum_sq univ fun A => √(Fintype.card V * X A)
    simp only [Finset.card_univ] at this
    refine le_trans (Finset.sum_le_sum fun A _ => le_abs_self _) (this.trans (le_of_eq ?_))
    congr 2
    refine Finset.sum_congr rfl fun A _ => Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (hX0 A))
  calc ∑ A, ∑ v, ‖∑ t, c t * D t A v‖ ≤ ∑ A, √(Fintype.card V * X A) :=
        Finset.sum_le_sum fun A _ => hv A
    _ ≤ √(Fintype.card 𝒜 * ∑ A, Fintype.card V * X A) := hA
    _ ≤ √(Fintype.card 𝒜 * (Fintype.card V * (Fintype.card 𝒜 * (Λ ^ 2 * B)))) := by
        rw [← Finset.mul_sum]
        gcongr
    _ = Fintype.card 𝒜 * Λ * √(Fintype.card V * B) := by
        rw [show (Fintype.card 𝒜 : ℝ) * (Fintype.card V * (Fintype.card 𝒜 * (Λ ^ 2 * B))) =
          (Fintype.card 𝒜 * Λ) ^ 2 * (Fintype.card V * B) by ring, Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (by positivity)]

end Average

end ZMod
