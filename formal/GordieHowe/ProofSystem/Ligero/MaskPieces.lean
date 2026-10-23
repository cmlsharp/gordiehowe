-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div
public import GordieHowe.ProofSystem.Ligero.Interpolation
public import GordieHowe.Headline

@[expose] public section

/-!
# Splitting a mask polynomial into shifted pieces

A mask polynomial of degree `< D` is committed as pieces `p_m` of degree `< d_m` with shifts `s_m`,
and recombined as `Σ_m X ^ (s_m) · p_m` (`split`). This file proves the polynomial facts behind the
zero-knowledge of that representation (the paper's Appendix D.4, Mask pieces and the subfield test).

* **The covering lemma** (`exists_splitting_vanishing`): when the intervals
  `[s_m, s_m + d_m − t − 1]` cover `[0, D − 1 − t]` (`Covers`), every polynomial of degree `< D`
  that vanishes at `t` distinct points `x` is `Σ_m X ^ (s_m) · p_m` with every `p_m` of degree
  `< d_m` vanishing at the points. Proof: the polynomial is `Z · Δ'` with `Z` the vanishing
  polynomial of the points and `deg Δ' < D − t`; each monomial `X ^ e` of `Δ'` goes to a piece
  whose interval contains `e`, and that piece is multiplied by `Z`.
* **Kernel values** (`exists_kernel_eval`): under the covering condition, values `τ_m` at the
  points satisfying the recombination relation `Σ_m x ^ (s_m) · τ_m = 0` at every point are the
  values of an element of the kernel of the splitting map within the degree bounds (`kernel`):
  interpolate the values, then subtract the splitting of the interpolants' recombination given by
  the covering lemma.
* **Three pieces** (`threeShifts`, `threeBounds`): the split `A + X ^ (k − t) · C + X ^ k · B` with
  `deg A < k`, `deg C < k`, `deg B < k − 1` of a polynomial of degree `< 2k − 1` satisfies the
  covering condition when `2t ≤ k` (`covers_three`): the intervals `[0, k − t − 1]`,
  `[k − t, 2k − 2t − 1]`, `[k, 2k − 2 − t]` cover `[0, 2k − 2 − t]`. Hence the values of the pieces
  `C` and `B` of a uniform kernel element at the points are uniform
  (`kernelOpenings_surjective`).
* **Two pieces fail** (`not_covers_fin_two`): `Covers` forces the intervals to have at least `D − t`
  elements in total (`Covers.sub_le_sum`), and two pieces of degree `< k` give at most
  `2(k − t) < 2k − 1 − t` when `t ≥ 2`, for every choice of shifts. In particular (`not_covers_two`)
  the split `A + X ^ k · B` (`deg A < k`, `deg B < k − 1`) misses `e = k − 1` for `0 < t < k`. Its
  conclusion fails too: the splitting map is injective (both sides have dimension `2k − 1`, so its
  kernel is zero and the pieces are determined by the mask), and for a point `x ≠ 0` and `k ≥ 2` the
  polynomial `(X − x) · X ^ (k − 1)` vanishes at `x` while its only splitting has
  `A = −x · X ^ (k − 1)`, with `A(x) = −x ^ k ≠ 0`. Zero knowledge then fails: two honest constraint
  polynomials that agree at the opened columns can give opened piece values with different laws.
-/

namespace GordieHowe.Ligero.MaskPieces

open Polynomial

section General

variable {F ι : Type} [Field F] [Fintype ι]

/-- **The splitting map** of the shifts `s`: pieces `p_m` to `Σ_m X ^ (s_m) · p_m`. -/
noncomputable def split (s : ι → ℕ) : (ι → F[X]) →ₗ[F] F[X] :=
  ∑ m, (LinearMap.mulLeft F (X ^ s m : F[X])).comp (LinearMap.proj m)

theorem split_apply (s : ι → ℕ) (p : ι → F[X]) : split s p = ∑ m, X ^ s m * p m := by
  simp [split]

/-- **The covering condition** of the shifts `s` and degree bounds `d` for `t` points and masks of
degree `< D`: every exponent `e` with `e + t < D` lies in the interval `[s_m, s_m + d_m − t − 1]`
of some piece `m`. -/
def Covers (s d : ι → ℕ) (t D : ℕ) : Prop :=
  ∀ e, e + t < D → ∃ m, s m ≤ e ∧ e + t < s m + d m

/-- **The covering condition bounds the total interval length**: the `D − t` exponents
`0, …, D − 1 − t` lie in the union of the intervals `[s_m, s_m + d_m − t − 1]`, which has at most
`Σ_m (d_m − t)` elements (truncated subtraction: a piece with `d_m ≤ t` contributes nothing). -/
theorem Covers.sub_le_sum {s d : ι → ℕ} {t D : ℕ} (h : Covers s d t D) :
    D - t ≤ ∑ m, (d m - t) := by
  classical
  calc D - t = (Finset.range (D - t)).card := (Finset.card_range _).symm
    _ ≤ (Finset.univ.biUnion fun m => Finset.Ico (s m) (s m + (d m - t))).card := by
        refine Finset.card_le_card fun e he => ?_
        rw [Finset.mem_range] at he
        obtain ⟨m, h1, h2⟩ := h e (by omega)
        exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, Finset.mem_Ico.mpr ⟨h1, by omega⟩⟩
    _ ≤ ∑ m, (Finset.Ico (s m) (s m + (d m - t))).card := Finset.card_biUnion_le
    _ = ∑ m, (d m - t) := by simp

/-- **Paper `lem:mask-split`, part (3), two pieces**. **No two-piece split satisfies the covering
condition for `t ≥ 2`**: for any shifts `s₀, s₁`, degree bounds `d₀, d₁ ≤ k`, masks of degree
`< 2k − 1` and `2 ≤ t ≤ 2k − 2`, the two intervals have at most `2(k − t) < 2k − 1 − t` elements
together (`Covers.sub_le_sum`), so some exponent of `[0, 2k − 2 − t]` is uncovered.

The hypotheses are sharp. For `t ≥ 2k − 1` the range `[0, 2k − 2 − t]` is empty and `Covers` holds
vacuously. For `t ≤ 1` it can hold: shifts `0, k − 1` with bounds `k, k` cover `[0, 2k − 3]` when
`t = 1`, and shifts `0, k − 1` with bounds `k − 1, k` cover `[0, 2k − 2]` when `t = 0`.

This is the Ligero form of the PLONK quotient-splitting pitfall. In Gabizon–Williamson–Ciobotaru,
PLONK (ePrint 2019/953), the quotient was first committed as deterministic pieces; Sefranek, "How
(Not) to Simulate PLONK" (SCN 2024, ePrint 2024/848), showed that the hidden piece evaluations are
then functions of the quotient that the simulator does not know, and the revised PLONK blinds the
pieces with one overlapping coefficient, which is the `t = 1` case above. Haböck–Al Kindi, "A note
on adding zero-knowledge to STARK" (ePrint 2024/1037), state the multi-query condition. Here, a
split into two pieces of degree `< k` leaves an exponent at the seam uncovered as soon as two points
are opened. -/
@[headline]
theorem not_covers_fin_two {s d : Fin 2 → ℕ} {k t : ℕ} (hd : ∀ m, d m ≤ k) (ht : 2 ≤ t)
    (htk : t + 2 ≤ 2 * k) : ¬ Covers s d t (2 * k - 1) := by
  intro h
  have hsum := h.sub_le_sum
  rw [Fin.sum_univ_two] at hsum
  have hd0 := hd 0
  have hd1 := hd 1
  omega

/-- **A splitting of `Δ`** with shifts `s` and degree bounds `d`: pieces `p_m` of degree `< d_m`
with `Σ_m X ^ (s_m) · p_m = Δ`. -/
structure IsSplitting (s d : ι → ℕ) (Δ : F[X]) (p : ι → F[X]) : Prop where
  degree_lt : ∀ m, (p m).degree < d m
  split_eq : split s p = Δ

theorem IsSplitting.add {s d : ι → ℕ} {Δ Δ' : F[X]} {p p' : ι → F[X]} (h : IsSplitting s d Δ p)
    (h' : IsSplitting s d Δ' p') : IsSplitting s d (Δ + Δ') (p + p') where
  degree_lt m := (degree_add_le _ _).trans_lt (max_lt (h.degree_lt m) (h'.degree_lt m))
  split_eq := by rw [map_add, h.split_eq, h'.split_eq]

theorem IsSplitting.sub {s d : ι → ℕ} {Δ Δ' : F[X]} {p p' : ι → F[X]} (h : IsSplitting s d Δ p)
    (h' : IsSplitting s d Δ' p') : IsSplitting s d (Δ - Δ') (p - p') where
  degree_lt m := (degree_sub_le _ _).trans_lt (max_lt (h.degree_lt m) (h'.degree_lt m))
  split_eq := by rw [map_sub, h.split_eq, h'.split_eq]

/-- The vanishing polynomial of distinct points divides every polynomial vanishing at them. -/
theorem nodal_dvd {t : ℕ} {x : Fin t → F} (hx : Function.Injective x) {Δ : F[X]}
    (hzero : ∀ j, Δ.eval (x j) = 0) : Lagrange.nodal Finset.univ x ∣ Δ := by
  unfold Lagrange.nodal
  refine Finset.prod_dvd_of_coprime ?_ fun j _ => dvd_iff_isRoot.mpr (hzero j)
  exact fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C hx hij

/-- **Paper `lem:mask-split`, part (1)**. **The covering lemma**: when the intervals
`[s_m, s_m + d_m − t − 1]` cover `[0, D − 1 − t]` (`Covers`), every polynomial `Δ` of degree `< D`
that vanishes at `t` distinct points `x` has a splitting (`IsSplitting`) whose pieces all vanish at
the points. -/
@[headline]
theorem exists_splitting_vanishing {s d : ι → ℕ} {t D : ℕ} (hcov : Covers s d t D)
    {x : Fin t → F} (hx : Function.Injective x) {Δ : F[X]} (hdeg : Δ.degree < D)
    (hzero : ∀ j, Δ.eval (x j) = 0) :
    ∃ p, IsSplitting s d Δ p ∧ ∀ m j, (p m).eval (x j) = 0 := by
  classical
  by_cases hΔ : Δ = 0
  · subst hΔ
    exact ⟨0, ⟨fun m => by simp, by simp⟩, fun m j => by simp⟩
  set Z : F[X] := Lagrange.nodal Finset.univ x
  have hZm : Z.Monic := Lagrange.nodal_monic
  have hZdeg : Z.natDegree = t := by
    simp [Z, Lagrange.natDegree_nodal]
  have hZx : ∀ j, Z.eval (x j) = 0 := fun j =>
    Lagrange.eval_nodal_at_node (Finset.mem_univ j)
  obtain ⟨Δ', hΔ'⟩ := nodal_dvd hx hzero
  have hΔ'0 : Δ' ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [hΔ', mul_zero])
  have hdegN : Δ.natDegree < D := (natDegree_lt_iff_degree_lt hΔ).mpr hdeg
  have hnat : Δ.natDegree = t + Δ'.natDegree := by
    rw [hΔ', natDegree_mul hZm.ne_zero hΔ'0, hZdeg]
  have hΔ'deg : Δ'.natDegree < D - t := by omega
  choose mOf hmOf using fun e : Fin (D - t) => hcov e (by omega)
  let piece : ι → F[X] := fun m => ∑ e : Fin (D - t),
    if mOf e = m then monomial (e - s m) (Δ'.coeff e) * Z else 0
  refine ⟨piece, ⟨fun m => ?_, ?_⟩, fun m j => ?_⟩
  · refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
      fun e _ => ?_)
    split_ifs with he
    · subst he
      obtain ⟨h1, h2⟩ := hmOf e
      have h3 := natDegree_monomial_le (R := F) (Δ'.coeff e) (m := (e : ℕ) - s (mOf e))
      have h4 : (monomial ((e : ℕ) - s (mOf e)) (Δ'.coeff e) * Z).natDegree < d (mOf e) :=
        natDegree_mul_le.trans_lt (by omega)
      exact degree_le_natDegree.trans_lt (by exact_mod_cast h4)
    · exact (WithBot.bot_lt_coe _)
  · rw [split_apply]
    have hterm : ∀ m, X ^ s m * piece m = ∑ e : Fin (D - t),
        if mOf e = m then monomial e (Δ'.coeff e) * Z else 0 := by
      intro m
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs with he
      · subst he
        rw [← mul_assoc, X_pow_mul_monomial, Nat.sub_add_cancel (hmOf e).1]
      · rw [mul_zero]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Finset.sum_mul, hΔ', mul_comm]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun e => monomial e (Δ'.coeff e)) (D - t)]
    exact (as_sum_range' Δ' (D - t) hΔ'deg).symm
  · simp only [piece, eval_finsetSum]
    refine Finset.sum_eq_zero fun e _ => ?_
    split_ifs
    · rw [eval_mul, hZx, mul_zero]
    · rw [eval_zero]

variable (F) in
/-- **The kernel of the splitting map** within the degree bounds: the splittings of zero. -/
def kernel (s d : ι → ℕ) : Submodule F (ι → F[X]) where
  carrier := {p | IsSplitting s d 0 p}
  add_mem' ha hb := by simpa using ha.add hb
  zero_mem' := ⟨fun m => by simp, by simp⟩
  smul_mem' a p hp := ⟨fun m => (degree_smul_le a (p m)).trans_lt (hp.degree_lt m),
    by rw [map_smul, hp.split_eq, smul_zero]⟩

theorem mem_kernel {s d : ι → ℕ} {p : ι → F[X]} : p ∈ kernel F s d ↔ IsSplitting s d 0 p :=
  Iff.rfl

/-- Kernel elements are determined by their first `d_m` coefficients in each piece. -/
theorem kernel_coeffs_injective (s d : ι → ℕ) :
    Function.Injective fun p : kernel F s d => fun m (i : Fin (d m)) => (p.1 m).coeff i := by
  intro p p' h
  apply Subtype.ext
  funext m
  ext n
  by_cases hn : n < d m
  · exact congrFun (congrFun h m) ⟨n, hn⟩
  · have hp := (mem_kernel.mp p.2).degree_lt m
    have hp' := (mem_kernel.mp p'.2).degree_lt m
    rw [coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast not_lt.mp hn)),
      coeff_eq_zero_of_degree_lt (hp'.trans_le (by exact_mod_cast not_lt.mp hn))]

noncomputable instance [Fintype F] (s d : ι → ℕ) : Fintype (kernel F s d) := by
  classical
  exact Fintype.ofInjective _ (kernel_coeffs_injective s d)

/-- **Paper `lem:mask-split`, part (2)**. **Kernel values**: under the covering condition, values
`τ_m` at `t` distinct points satisfying the recombination relation `Σ_m x ^ (s_m) · τ_m = 0` at
every point are the values of a splitting of zero, when every piece holds `t` points (`t ≤ d_m`) and
every shifted interpolant fits under `D` (`s_m + t ≤ D`). -/
@[headline]
theorem exists_kernel_eval {s d : ι → ℕ} {t D : ℕ} (hcov : Covers s d t D) {x : Fin t → F}
    (hx : Function.Injective x) (hd : ∀ m, t ≤ d m) (hs : ∀ m, s m + t ≤ D)
    {τ : ι → Fin t → F} (hτ : ∀ j, ∑ m, x j ^ s m * τ m j = 0) :
    ∃ p, IsSplitting s d 0 p ∧ ∀ m j, (p m).eval (x j) = τ m j := by
  let R0 : ι → F[X] := fun m => LigeroInterpolation.interpolate x (τ m)
  have hR0deg : ∀ m, (R0 m).degree < t := fun m => by
    simpa [R0, LigeroInterpolation.interpolate] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (v := x) (τ m) hx.injOn
  have hR0eval : ∀ m j, (R0 m).eval (x j) = τ m j := fun m j =>
    LigeroInterpolation.interpolate_eval hx (τ m) j
  have hΔdeg : (split s R0).degree < D := by
    rw [split_apply]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
      fun m _ => ?_)
    refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_X_pow]
    by_cases h0 : R0 m = 0
    · simp [h0]
    · have h1 : (R0 m).natDegree < t := (natDegree_lt_iff_degree_lt h0).mpr (hR0deg m)
      rw [degree_eq_natDegree h0]
      exact_mod_cast (show s m + (R0 m).natDegree < D by have := hs m; omega)
  have hΔzero : ∀ j, (split s R0).eval (x j) = 0 := fun j => by
    simp only [split_apply, eval_finsetSum, eval_mul, eval_pow, eval_X, hR0eval]
    exact hτ j
  obtain ⟨R1, hR1, hR1zero⟩ := exists_splitting_vanishing hcov hx hΔdeg hΔzero
  have hR0 : IsSplitting s d (split s R0) R0 :=
    ⟨fun m => (hR0deg m).trans_le (by exact_mod_cast hd m), rfl⟩
  refine ⟨R0 - R1, by simpa using hR0.sub hR1, fun m j => ?_⟩
  simp [hR0eval, hR1zero]

end General

/-! ### Three pieces -/

section Three

variable {F : Type} [Field F]

/-- **The shifts of the three-piece split** `A + X ^ (k − t) · C + X ^ k · B`. -/
def threeShifts (k t : ℕ) : Fin 3 → ℕ := ![0, k - t, k]

/-- **The degree bounds of the three-piece split**: `deg A < k`, `deg C < k`, `deg B < k − 1`. -/
def threeBounds (k : ℕ) : Fin 3 → ℕ := ![k, k, k - 1]

theorem split_three (k t : ℕ) (p : Fin 3 → F[X]) :
    split (threeShifts k t) p = p 0 + X ^ (k - t) * p 1 + X ^ k * p 2 := by
  simp [split_apply, Fin.sum_univ_three, threeShifts]

/-- **Paper `lem:mask-split`, part (3), three pieces**. **The three-piece split satisfies the
covering condition** for masks of degree `< 2k − 1` when `2t ≤ k`: the intervals `[0, k − t − 1]`,
`[k − t, 2k − 2t − 1]` and `[k, 2k − 2 − t]` cover `[0, 2k − 2 − t]`. -/
@[headline]
theorem covers_three {k t : ℕ} (h : 2 * t ≤ k) :
    Covers (threeShifts k t) (threeBounds k) t (2 * k - 1) := by
  intro e he
  by_cases h0 : e + t < k
  · exact ⟨0, by simp [threeShifts], by simpa [threeShifts, threeBounds] using h0⟩
  by_cases h1 : e < k
  · exact ⟨1, by simp [threeShifts]; omega, by simp [threeShifts, threeBounds]; omega⟩
  · exact ⟨2, by simp [threeShifts]; omega, by simp [threeShifts, threeBounds]; omega⟩

/-- **The two-piece split does not satisfy the covering condition**: for `A + X ^ k · B` with
`deg A < k`, `deg B < k − 1`, masks of degree `< 2k − 1` and `0 < t < k`, the exponent `k − 1`
lies in neither `[0, k − t − 1]` nor `[k, 2k − 2 − t]`. For `t ≥ 2` this is an instance of
`not_covers_fin_two`; the bound `k − 1` on `B` also excludes `t = 1`, by the same count
(`Covers.sub_le_sum`). -/
theorem not_covers_two {k t : ℕ} (ht : 0 < t) (htk : t < k) :
    ¬ Covers (![0, k] : Fin 2 → ℕ) ![k, k - 1] t (2 * k - 1) := by
  intro h
  have hsum := h.sub_le_sum
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
  omega

/-- **The values of the pieces `C` and `B` of a kernel element at the points cover every pair**:
for `2t ≤ k` and `t` distinct points, every pair of value vectors is the values of the pieces `C`
and `B` of a splitting of zero (`exists_kernel_eval` with the value of `A` fixed by the
recombination relation). -/
theorem kernelOpenings_surjective [Fintype F] {k t : ℕ} (h : 2 * t ≤ k) {x : Fin t → F}
    (hx : Function.Injective x) :
    Function.Surjective fun κ : kernel F (threeShifts k t) (threeBounds k) =>
      (fun j => ((κ : Fin 3 → F[X]) 1).eval (x j), fun j => ((κ : Fin 3 → F[X]) 2).eval (x j)) := by
  rintro ⟨γ, β⟩
  let τ : Fin 3 → Fin t → F :=
    ![fun j => -(x j ^ (k - t) * γ j) - x j ^ k * β j, γ, β]
  obtain ⟨p, hp, hpe⟩ := exists_kernel_eval (covers_three h) hx
    (fun m => by fin_cases m <;> simp [threeBounds] <;> omega)
    (fun m => by fin_cases m <;> simp [threeShifts] <;> omega) (τ := τ)
    (fun j => by simp [Fin.sum_univ_three, threeShifts, τ]; ring)
  refine ⟨⟨p, mem_kernel.mpr hp⟩, ?_⟩
  ext j
  · simpa [τ] using hpe 1 j
  · simpa [τ] using hpe 2 j

end Three

end GordieHowe.Ligero.MaskPieces
