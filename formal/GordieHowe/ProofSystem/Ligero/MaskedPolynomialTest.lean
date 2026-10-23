-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder
public import Mathlib.Basic.NNReal.Basic

@[expose] public section

/-!
# Query agreement with an arbitrary committed mask oracle

A masking oracle need not be a low-degree codeword. Fix its canonical nearby
polynomial, if one exists. Any other degree-bounded response polynomial agrees
with at most N−e−1 oracle positions: otherwise it would itself be nearby and
therefore the canonical decode. This uses the proved uniqueness of Reed–Solomon
nearby decoding, and covers both failed decoding and a different response.

Sampling distinct query columns gives the corresponding power-ratio bound. The statement is
deterministic counting for a fixed response. It does not assert that a prover's mask is honestly
generated or prove the whole Ligero algebraic test; that composition must respect when the response
and queries are fixed.
-/

namespace GordieHowe.MaskedPolynomialTest

open Polynomial
open scoped Classical

variable {F : Type*} [Field F] {N : ℕ}

/-- Agreed positions between the arbitrary committed row and a response. -/
noncomputable def agreement (C : GordieHowe.RSCode F N) (u : Fin N → F) (p : F[X]) :
    Finset (Fin N) :=
  Finset.univ.filter fun j => u j = p.eval (C.D j)

/-- A degree-bounded response that is not the canonical decode must differ
from the oracle at more than the decoding radius. -/
theorem errors_gt_radius (C : GordieHowe.RSCode F N) (u : Fin N → F) (p : F[X])
    (hp : p.natDegree < C.k)
    (hother : RSCode.nearbyRows C (fun _ : Fin 1 => u) ≠ some (fun _ => p)) :
    C.e < (Finset.univ.filter fun j => u j ≠ p.eval (C.D j)).card := by
  by_contra h
  apply hother
  apply RSCode.nearbyRows_eq_some_iff.mpr
  refine ⟨fun _ => hp, ?_⟩
  simpa [RSCode.columnErrors] using (Nat.le_of_not_gt h)

/-- No maximal-radius assumption is needed: this holds for every valid
unique-decoding radius. Polynomial root counting enters through the proved
uniqueness theorem used in `nearbyRows_eq_some_iff`. -/
theorem agreement_card_le (C : GordieHowe.RSCode F N) (u : Fin N → F) (p : F[X])
    (hp : p.natDegree < C.k)
    (hother : RSCode.nearbyRows C (fun _ : Fin 1 => u) ≠ some (fun _ => p)) :
    (agreement C u p).card ≤ N - C.e - 1 := by
  have herr := errors_gt_radius C u p hp hother
  simp only [ne_eq] at herr
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (p := fun j => u j = p.eval (C.D j))
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  unfold agreement
  omega

/-- Failed canonical decoding still gives a bound for every degree-bounded
response, without assigning the masking oracle an honest polynomial. -/
theorem agreement_card_le_of_decode_none (C : GordieHowe.RSCode F N) (u : Fin N → F)
    (p : F[X]) (hp : p.natDegree < C.k)
    (hdecode : RSCode.nearbyRows C (fun _ : Fin 1 => u) = none) :
    (agreement C u p).card ≤ N - C.e - 1 :=
  agreement_card_le C u p hp (by simp [hdecode])

/-- When decoding succeeds, every different response has bounded agreement. -/
theorem agreement_card_le_of_ne_decode (C : GordieHowe.RSCode F N) (u : Fin N → F)
    (p : F[X]) (hp : p.natDegree < C.k) (fs : Fin 1 → F[X])
    (hdecode : RSCode.nearbyRows C (fun _ : Fin 1 => u) = some fs)
    (hne : p ≠ fs 0) :
    (agreement C u p).card ≤ N - C.e - 1 := by
  apply agreement_card_le C u p hp
  intro h
  have heq := Option.some.inj (hdecode.symm.trans h)
  exact hne (congrFun heq 0).symm

/-- Among injective samples of t columns, the fraction agreeing everywhere
with a noncanonical response is at most ((N−e−1)/N)^t. The inequality is
cross-multiplied in natural numbers, avoiding division and rounding. -/
theorem query_agreement_count (C : GordieHowe.RSCode F N) (u : Fin N → F) (p : F[X])
    (hp : p.natDegree < C.k)
    (hother : RSCode.nearbyRows C (fun _ : Fin 1 => u) ≠ some (fun _ => p)) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) = p.eval (C.D (q s))).card * N ^ t ≤
        (N - C.e - 1) ^ t * Fintype.card (Fin t ↪ Fin N) := by
  have hcount := Fintype.card_embedding_filter_mem_mul_le (t := t) (agreement C u p)
  simp only [agreement, Finset.mem_filter, Finset.mem_univ, true_and] at hcount
  exact hcount.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (agreement_card_le C u p hp hother) t))

/-- The maximal unique-decoding radius gives the conservative CHVY agreement
fraction. The natural subtraction and odd/even rounding are accounted for. -/
theorem maximal_radius_ratio_le (C : GordieHowe.RSCode F N)
    (he : C.e = (N - C.k) / 2) :
    ((N - C.e - 1 : ℕ) : NNReal) / N ≤
      ((N : NNReal) + C.k) / (2 * N) := by
  have hk := C.k_pos
  have hr := C.radius
  have hN : 0 < N := by omega
  have hN' : (0 : NNReal) < N := by exact_mod_cast hN
  have hnat : 2 * (N - C.e - 1) ≤ N + C.k := by omega
  have hcast : (2 : NNReal) * (N - C.e - 1 : ℕ) ≤ (N : NNReal) + C.k := by
    exact_mod_cast hnat
  apply (div_le_div_iff₀ hN' (mul_pos (by norm_num) hN')).mpr
  calc
    _ = (2 * ((N - C.e - 1 : ℕ) : NNReal)) * N := by ring
    _ ≤ ((N : NNReal) + C.k) * N := mul_le_mul_of_nonneg_right hcast (by positivity)

/-- The fixed-response query count with the published conservative power-ratio
budget, for the maximal canonical decoding radius. -/
theorem query_agreement_count_nnreal (C : GordieHowe.RSCode F N)
    (he : C.e = (N - C.k) / 2) (u : Fin N → F) (p : F[X])
    (hp : p.natDegree < C.k)
    (hother : RSCode.nearbyRows C (fun _ : Fin 1 => u) ≠ some (fun _ => p)) (t : ℕ) :
    ((Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) = p.eval (C.D (q s))).card : NNReal) ≤
      (((N : NNReal) + C.k) / (2 * N)) ^ t * Fintype.card (Fin t ↪ Fin N) := by
  have hN : 0 < N := by have := C.k_pos; have := C.radius; omega
  have hN' : (0 : NNReal) < N := by exact_mod_cast hN
  have hcount := query_agreement_count C u p hp hother t
  have hcast :
      ((Finset.univ.filter fun q : Fin t ↪ Fin N =>
        ∀ s, u (q s) = p.eval (C.D (q s))).card : NNReal) * (N : NNReal) ^ t ≤
      ((N - C.e - 1 : ℕ) : NNReal) ^ t * Fintype.card (Fin t ↪ Fin N) := by
    exact_mod_cast hcount
  have hratio :
      ((Finset.univ.filter fun q : Fin t ↪ Fin N =>
        ∀ s, u (q s) = p.eval (C.D (q s))).card : NNReal) ≤
      (((N - C.e - 1 : ℕ) : NNReal) / N) ^ t * Fintype.card (Fin t ↪ Fin N) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hN' t)]
    exact hcast
  exact hratio.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (maximal_radius_ratio_le C he) t) (by positivity))

/-- The masking response has degree less than 2k−1. When `2k − 1 ≤ N` the same
injective evaluation domain supports its own canonical unique decoder. -/
def maskCode (C : GordieHowe.RSCode F N) (hrate : 2 * C.k - 1 ≤ N) : GordieHowe.RSCode F N where
  D := C.D
  D_injective := C.D_injective
  k := 2 * C.k - 1
  e := (N - (2 * C.k - 1)) / 2
  k_pos := by have := C.k_pos; omega
  radius := by have := C.k_pos; omega

/-- Specialized published query budget for arbitrary masking oracles and
responses of degree below 2k−1. -/
theorem mask_query_agreement_count_nnreal (C : GordieHowe.RSCode F N)
    (hrate : 2 * C.k - 1 ≤ N) (u : Fin N → F) (p : F[X])
    (hp : p.natDegree < 2 * C.k - 1)
    (hother : RSCode.nearbyRows (maskCode C hrate) (fun _ : Fin 1 => u) ≠ some (fun _ => p))
    (t : ℕ) :
    ((Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) = p.eval (C.D (q s))).card : NNReal) ≤
      (((N : NNReal) + ((2 * C.k - 1 : ℕ) : NNReal)) / (2 * N)) ^ t *
        Fintype.card (Fin t ↪ Fin N) :=
  query_agreement_count_nnreal (maskCode C hrate) rfl u p hp hother t

/-- A nonzero polynomial residual can be cancelled by a fixed mask polynomial
for at most one scalar challenge. This is a deterministic cancellation lemma;
using it probabilistically requires the mask to be fixed before the scalar. -/
theorem affine_cancellation_count [Fintype F] (a b : F[X]) (ha : a ≠ 0) :
    (Finset.univ.filter fun r : F => C r * a + b = 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  apply Polynomial.C_injective
  exact mul_right_cancel₀ ha (add_right_cancel (hx'.trans hy'.symm))

end GordieHowe.MaskedPolynomialTest
