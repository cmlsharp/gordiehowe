-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.FieldSkip

@[expose] public section

/-!
# The univariate-skip zerocheck reduction

The batched-Keccak alternative (the skip zerocheck, the paper's `sec:batched-skip`) proves
`A_j(t) · B_j(t) + C_j(t) = 0` for every group `j` and every point `t` of a `w`-point domain `D` by
one univariate round followed by an eq-factored sumcheck over the group index
(`Sumcheck.EqFactored`). This file states its domain and operands over an arbitrary field `K` with
`n` group variables (`SkipDomain`, `Operands`, `Operands.Holds`).

Source: `lib/sumcheck/boolean_skip.h` (`BasicBooleanSkip` at the chi relation, degree `D = 2`,
so `extra() = (D - 1)(w - 1) = w - 1`); the masked rounds after the first are `MaskedFieldSkip`
(`lib/gordiehowe/compiler/field_skip.h`), run by `BatchKernel` (`lib/gordiehowe/compiler/batch.h`).

* Domain. The points are `embed[i]`, the image of the `i`-th element of the
  separately embedded `GF(2^8)` (the constructor of `BasicBooleanSkip`). `D` is `embed[0..w-1]`
  (the bit basis `basis(0, w, r)`, `bit_basis`) and the `w - 1` extra points are `embed[w..2w-2]`
  (the skip basis `basis(0, D(w-1)+1, r)`, `skip_basis`, read by `verify`).
  `SkipDomain.point (inl t)` is `embed[t]` and `point (inr i)` is `embed[w + i]`; distinctness is
  the structure field `injective`. The width `w` is a power of two at most `64`.
* Groups. `split` cuts each 64-bit lane word into `64 / w` groups, group `z / w` holding bits
  `z..z+w-1`; group index is `word · (64 / w) + chunk`. The group list is padded with zero rows
  (all operands zero) to a power of two (`prove`), `2^15` for 24,000 groups. The operand arrays
  here are indexed by `Fin (2^n)` after padding; the padding is data, not a hypothesis.
* Operand values. Bit `z` of a group is the operand value at `embed[z]`, so
  `A_j(T)` is the degree `≤ w - 1` interpolant of `A_j` on `D`
  (`reference_open`: `Σ_z bit_z · l_z(r)`).
* Weights. `Eqs(logn, n, batch)` (`arrays/eqs.h`, `filleq`) tabulates
  `eq(ρ, j) = ∏_l (j_l ? ρ_l : 1 - ρ_l)` with bit `l` of `j` paired with
  `ρ_l`: `PackedClaim.eqPt ρ j`.
* Messages. The skip message is `w - 1` values `g(embed[w+i])` (`prove`); the verifier's initial
  claim is `Σ_i skip_i · l_{w+i}(r)` with the `2w - 1`-point Lagrange basis (`verify`,
  `skip_basis`), that is `skipPoly(r)` with the values on `D` fixed to zero. Each sumcheck round
  sends the coefficients `q1, q2` of the quadratic `q_i` with
  `p_i(X) = prefix_i · eq(ρ_i, X) · q_i(X)` (`prove`), and the verifier updates the claim without a
  per-round check (`claim' = eq_i · claim + prefix_{i+1} · ((ρ_i + s_i) q1 + (ρ_i + s_i²) q2)`,
  `verify`; `Sumcheck.EqFactoredDeg.claims` at `D = 2`, `Sumcheck.EqFactored.eqLin_charTwo`).
  Folding is `v[i] = v[2i] + t · (v[2i] + v[2i+1])` (`prove`), so round `i` binds bit `i`.
* Terminal. `claim = eq(ρ, s) · (m_0 · m_1 + m_2)` with `eq(ρ, s)` the running prefix
  `∏ (1 + ρ_i + s_i)` (`verify`; `Sumcheck.EqFactored.prefixEq_last`,
  `EqPolynomial.eqProd_charTwo`).
* Batching. The verifier samples `u ∈ K^3` after the terminal claims; the combination `Σ u_k m_k`
  is authenticated by the packed opening (`BatchKernel`'s row on the table words, which the
  domain's packing tree opens).

**The instance of `Sumcheck.FieldSkip`.** The reduction is `Sumcheck.FieldSkip` at the relation
`Q = X₀ X₁ + X₂` (`D = 2`, three operands) on the domain `SkipDomain.toPoints`. This file keeps its
own domain type because the skip message is indexed by `Fin (w - 1)`, which is not
definitionally FieldSkip's `Fin ((2 - 1) (w - 1))` (`pointEquiv`).
-/

namespace GordieHowe.Sumcheck.UnivariateSkip
open IOP

open Polynomial
open GKR.ClaimEvaluation (binaryLabelEquiv evalTable mle value)
open EqPolynomial (eqPoly eqProd)

variable {K : Type} [Field K] {w n : ℕ}

/-- The `2w - 1` evaluation points: `point (inl t)` is the interpolation
domain `D`, `point (inr i)` the extra points. Distinctness is a fact about the field. -/
structure SkipDomain (K : Type) [Field K] (w : ℕ) where
  point : Fin w ⊕ Fin (w - 1) → K
  injective : Function.Injective point

/-- At degree two the skip message has `(2 − 1)(w − 1) = w − 1` points. -/
theorem extra_eq (w : ℕ) : (2 - 1) * (w - 1) = w - 1 := Nat.one_mul _

/-- The point index of `Sumcheck.FieldSkip` at degree two, read as this file's. -/
def pointEquiv (w : ℕ) : Fin w ⊕ Fin ((2 - 1) * (w - 1)) ≃ Fin w ⊕ Fin (w - 1) :=
  Equiv.sumCongr (Equiv.refl _) (finCongr (extra_eq w))

namespace SkipDomain

/-- **The skip domain as the points of `Sumcheck.FieldSkip` at degree two.** -/
def toPoints (dom : SkipDomain K w) : FieldSkip.SkipPoints K w 2 where
  point := dom.point ∘ pointEquiv w
  injective := dom.injective.comp (pointEquiv w).injective

/-- The skip domain of degree-two points of `Sumcheck.FieldSkip`. -/
def ofPoints (P : FieldSkip.SkipPoints K w 2) : SkipDomain K w where
  point := P.point ∘ (pointEquiv w).symm
  injective := P.injective.comp (pointEquiv w).symm.injective

/-- The skip domain of an embedding `embed : ℕ → K` injective on `[0, 2w - 1)`: the points
`embed[0], …, embed[2w - 2]` (`FieldSkip.SkipPoints.ofEmbed` at degree two). -/
def ofEmbed (embed : ℕ → K) (h : Set.InjOn embed (Set.Iio (2 * w - 1))) : SkipDomain K w :=
  ofPoints (FieldSkip.SkipPoints.ofEmbed embed
    (by rwa [extra_eq, show w + (w - 1) = 2 * w - 1 by omega]))

variable (dom : SkipDomain K w)

end SkipDomain

/-- The committed operand arrays of the `2^n` (padded) groups, indexed by the
points of `D`. -/
structure Operands (K : Type) (w n : ℕ) where
  a : Fin (2 ^ n) → Fin w → K
  b : Fin (2 ^ n) → Fin w → K
  c : Fin (2 ^ n) → Fin w → K

namespace Operands

variable (ops : Operands K w n)

/-- `A_j(t) · B_j(t) + C_j(t)`. -/
def residual (j : Fin (2 ^ n)) (t : Fin w) : K := ops.a j t * ops.b j t + ops.c j t

/-- The relation the reduction proves. -/
def Holds : Prop := ∀ j t, ops.residual j t = 0

end Operands

variable (dom : SkipDomain K w) (ops : Operands K w n)

end GordieHowe.Sumcheck.UnivariateSkip
