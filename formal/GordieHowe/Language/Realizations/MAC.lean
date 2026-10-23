-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Fin
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Applications.Params

@[expose] public section

/-!
# The shared-witness MAC in domain H

`chunks` packs bit wires into elements of a binary field `GF(2^w)` through its polynomial basis,
`w` bits per chunk, and `sharedWitnessMAC` evaluates `Σ_c X[c] · r[c]` with the public ladder
`r[c] = K_mac^(c+1)`. Domain A recomputes the same value through an integer accumulator; the binding
statement here is the Carter–Wegman fact both domains meet at: two chunk vectors with pads that
agree on the masked MAC either agree outright or make `K_mac` a root of a nonzero polynomial of
degree at most the chunk count.

The basis enters as a structure of field facts, discharged once for the concrete field. The
flagship's chunk width is `macChunkBits = 128` (`Basis128`).
-/

namespace GordieHowe

open Polynomial

/-- The polynomial basis `1, X, …, X^(w−1)` of `GF(2^w)` over `GF(2)`, as the
facts the gadgets need: coordinates exist, and distinct bit vectors pack to
distinct elements. -/
structure MACBasis (w : ℕ) (K : Type*) [Field K] where
  e : Fin w → K
  /-- coordinates of an element in the basis -/
  unpack : K → Fin w → Bool
  pack_unpack : ∀ x, (∑ i, if unpack x i then e i else 0) = x
  pack_injective : ∀ b b' : Fin w → Bool,
    (∑ i, if b i then e i else 0) = (∑ i, if b' i then e i else 0) → b = b'

/-- The basis at the flagship chunk width `macChunkBits = 128`. -/
abbrev Basis128 (K : Type*) [Field K] := MACBasis macChunkBits K

namespace MAC

variable {K : Type*} [Field K] {w : ℕ}

/-- Pack `w` bit wires into one field element. -/
def pack (B : MACBasis w K) (bits : Fin w → K) : K := ∑ i, bits i * B.e i

/-- Bit `i` of chunk `c` sits at position `w · c + i` of the chunked vector. -/
theorem chunk_index_lt {k c i : ℕ} (hc : c < k) (hi : i < w) : w * c + i < w * k :=
  calc w * c + i < w * c + w := by omega
    _ = w * (c + 1) := by ring
    _ ≤ w * k := Nat.mul_le_mul_left w hc

/-- Packing is injective on Boolean inputs. Booleanity is established by the
circuit's bit constraints; the basis fact concerns all Boolean vectors. -/
theorem pack_injective (B : MACBasis w K) {a b : Fin w → K}
    (ha : Bits.AllBool a) (hb : Bits.AllBool b) (h : pack B a = pack B b) : a = b := by
  classical
  have hsum : (∑ i, if a i = 1 then B.e i else 0) =
      ∑ i, if b i = 1 then B.e i else 0 := by
    rw [← Bits.packAlong_eq_of_bool B.e ha, ← Bits.packAlong_eq_of_bool B.e hb]
    exact h
  have hbool : (fun i => decide (a i = 1)) = (fun i => decide (b i = 1)) := by
    apply B.pack_injective
    simpa using hsum
  funext i
  have hi := congrFun hbool i
  rcases ha i with hai | hai <;> rcases hb i with hbi | hbi <;> simp_all

/-- `SharedWitnessMAC(X, r) = Σ_c X[c] · r[c]`. -/
def sharedWitnessMAC {k : ℕ} (X r : Fin k → K) : K := ∑ c, X c * r c

/-- The public ladder `r[c] = K_mac^(c+1)`. -/
def ladder (k : ℕ) (Kmac : K) (c : Fin k) : K := Kmac ^ ((c : ℕ) + 1)

/-- The Carter–Wegman difference `(P_H - P_A) + Σ_c (X_H[c] - X_A[c]) · X^(c+1)`
as a polynomial in the MAC key. -/
noncomputable def badPoly {k : ℕ} (XH XA : Fin k → K) (PH PA : K) : K[X] :=
  C (PH - PA) + ∑ c, C (XH c - XA c) * X ^ ((c : ℕ) + 1)

theorem badPoly_natDegree_le {k : ℕ} (XH XA : Fin k → K) (PH PA : K) :
    (badPoly XH XA PH PA).natDegree ≤ k := by
  unfold badPoly
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro c _
    exact (natDegree_C_mul_le _ _).trans (by simp)

/-- The constant coefficient is exactly the pad difference. -/
theorem badPoly_coeff_zero {k : ℕ} (XH XA : Fin k → K) (PH PA : K) :
    (badPoly XH XA PH PA).coeff 0 = PH - PA := by
  simp [badPoly, finsetSum_coeff]

/-- Positive coefficients are exactly the chunk differences. -/
theorem badPoly_coeff_succ {k : ℕ} (XH XA : Fin k → K) (PH PA : K) (c : Fin k) :
    (badPoly XH XA PH PA).coeff (c + 1) = XH c - XA c := by
  classical
  simp only [badPoly, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [Fin.val_inj]

/-- A vanishing difference polynomial forces agreement of chunks and pads. -/
theorem badPoly_eq_zero_iff {k : ℕ} (XH XA : Fin k → K) (PH PA : K) :
    badPoly XH XA PH PA = 0 ↔ XH = XA ∧ PH = PA := by
  constructor
  · intro h
    constructor
    · funext c
      apply sub_eq_zero.mp
      rw [← badPoly_coeff_succ XH XA PH PA c, h, coeff_zero]
    · apply sub_eq_zero.mp
      rw [← badPoly_coeff_zero XH XA PH PA, h, coeff_zero]
  · rintro ⟨rfl, rfl⟩
    simp [badPoly]

/-- Evaluation is the difference between the two masked MACs. -/
theorem badPoly_eval {k : ℕ} (XH XA : Fin k → K) (PH PA Kmac : K) :
    (badPoly XH XA PH PA).eval Kmac =
      (sharedWitnessMAC XH (ladder k Kmac) + PH) -
        (sharedWitnessMAC XA (ladder k Kmac) + PA) := by
  simp only [badPoly, eval_add, eval_C, eval_finsetSum, eval_mul, eval_pow, eval_X,
    sharedWitnessMAC, ladder, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The binding event in the MAC key. -/
noncomputable def bindingEvent {k : ℕ} (XH XA : Fin k → K) (PH PA : K) : ChallengeEvent K :=
  ⟨badPoly XH XA PH PA, k, badPoly_natDegree_le XH XA PH PA⟩

/-- **Paper `lem:core-mac`, part (1), in the field**: binding. If the masked MACs of two chunk
vectors with pads agree at key `K_mac`, then their chunks and pads agree, or `K_mac` is a root of
the nonzero `badPoly`. Both chunk vectors and both pads are prover-chosen. -/
theorem binding {k : ℕ} {Kmac : K} {XH XA : Fin k → K} {PH PA : K}
    (h : sharedWitnessMAC XH (ladder k Kmac) + PH = sharedWitnessMAC XA (ladder k Kmac) + PA) :
    (XH = XA ∧ PH = PA) ∨ (bindingEvent XH XA PH PA).BadAt Kmac := by
  classical
  by_cases hp : badPoly XH XA PH PA = 0
  · exact Or.inl ((badPoly_eq_zero_iff XH XA PH PA).mp hp)
  · right
    refine ⟨hp, ?_⟩
    change (badPoly XH XA PH PA).eval Kmac = 0
    rw [badPoly_eval, h, sub_self]

end MAC

end GordieHowe
