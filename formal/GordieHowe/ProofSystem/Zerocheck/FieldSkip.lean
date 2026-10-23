-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.EqFactoredDeg
public import GordieHowe.Foundations.ToMathlib.LagrangeEval
public import GordieHowe.Foundations.ToMathlib.MvPolynomialAeval
public import GordieHowe.Foundations.Probability.ChallengeEventMv
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# The univariate-skip zerocheck over any field, for any relation

GordieHowe's field-generic batching (`lib/gordiehowe/compiler/field_skip.h`, `MaskedFieldSkip`)
proves that a relation `Q` of total degree at most `D` on `k` operands holds on every instance
`t = r w + z` of a batch, in any characteristic. This file states the unmasked reduction;
`GordieHowe/ProofSystem/Zerocheck/UnivariateSkip.lean` reads it at `Q = a b + c` (`D = 2`, `k = 3`) in characteristic
two.

* **The skip domain** (`SkipPoints K w D`): `D (w − 1) + 1` distinct points, the first `w` the
  instances' skip coordinates (`pt`), the other `(D − 1)(w − 1)` the skip message's points.
  `SkipPoints.ofEmbed` takes them from an embedding `ℕ → K` injective below `D (w − 1) + 1`:
  `SkipPoints.integers` (the integers `0 … D (w − 1)` in characteristic above `D (w − 1)`, the C++
  odd-characteristic domain) and, in characteristic two, the elements `0 … D (w − 1)` of an
  embedded `GF(2^8)` (`SkipByteField`, as `Fields/GF2_128Skip.lean`'s `gf2_128SkipEmbed`, needing
  `D (w − 1) + 1 ≤ 256`). The Lagrange weights are `Lagrange.basisEval`; the C++ odd path's
  closed-form denominators `(−1)^(n−1−i) i! (n−1−i)!` are the same values on consecutive integers
  (not restated here).
* **The relation** (`Relation K k D`): `Q` of total degree at most `D` with no constant term
  (`FieldRelation::error`: every monomial reads an operand, so zero padding satisfies it).
* **The reduction**: the zerocheck point `ρ`, the skip message (the values of
  `g(T) = Σ_r eq(ρ, r) · Q(Â_r(T))` at the extra points), the skip challenge `r`, the
  eq-factored sumcheck with `D` coefficients per round (`EqFactoredDeg`), the `k` terminal operand
  claims, and the batching scalars `u` of the opening (`MaskedFieldSkip::opening_row`; here the
  opening is the abstract `Accepts.opening`). Events: `rhoEvent` (degree `n`), `rEvent` (degree
  `D (w − 1)`), `roundEvent i` (degree `D + 1`) and `uEvent` (degree `1`); `soundness`.
* **Merging** (`merge`): several relations `Q_i` on one operand vector combined as `Σ_i γ^i Q_i`
  with `γ` drawn before the zerocheck; one more event, `mergeEvent`, of degree `np − 1`
  (`merge_sound`).
-/

namespace GordieHowe.Sumcheck.FieldSkip
open IOP

open Polynomial
open GKR.ClaimEvaluation (binaryLabelEquiv evalTable mle value)
open GKR.LayerPolynomial (Cube boolValue)
open EqPolynomial (eqPoly eqProd)

variable {K : Type} [Field K] {w D k n : ℕ}

/-- A polynomial of degree below `m` has natural degree at most `m - 1`. -/
theorem natDegree_le_of_degree_lt {p : K[X]} {m : ℕ} (h : p.degree < m) : p.natDegree ≤ m - 1 := by
  by_cases hp : p = 0
  · simp [hp]
  · have := (natDegree_lt_iff_degree_lt hp).mpr h
    omega

/-! ### The skip domain -/

/-- The point index of the skip domain: the instances' skip coordinates `0, …, w − 1`, then the
skip message's points `w, …, D (w − 1)` (`field_skip.h`, `SkipDomain`: `points_[i]` for
`i < D (w − 1) + 1`; the prover's loop `for pt = w … points() − 1`). -/
def skipIndex : Fin w ⊕ Fin ((D - 1) * (w - 1)) → ℕ
  | Sum.inl t => t
  | Sum.inr i => w + i

theorem skipIndex_lt (x : Fin w ⊕ Fin ((D - 1) * (w - 1))) :
    skipIndex x < w + (D - 1) * (w - 1) := by
  cases x with
  | inl t => simp only [skipIndex]; omega
  | inr i => simp only [skipIndex]; omega

theorem skipIndex_injective : Function.Injective (skipIndex (w := w) (D := D)) := by
  intro x y h
  cases x <;> cases y <;> simp only [skipIndex] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

variable (K w D) in
/-- **The skip domain of a relation of degree `D`**: `w + (D − 1)(w − 1)` distinct points, which is
`D (w − 1) + 1` for `w, D ≥ 1`. `point (inl t)` is the skip coordinate `t` of an instance, `point
(inr i)` the skip message's point `w + i`. Distinctness is a fact about the field. -/
structure SkipPoints where
  /-- The points. -/
  point : Fin w ⊕ Fin ((D - 1) * (w - 1)) → K
  /-- The points are distinct. -/
  injective : Function.Injective point

/-- The skip domain of an embedding `embed : ℕ → K` injective below `w + (D − 1)(w − 1)`: the
points `embed 0, …, embed (D (w − 1))`, indexed by `skipIndex`. -/
def SkipPoints.ofEmbed (embed : ℕ → K)
    (h : Set.InjOn embed (Set.Iio (w + (D - 1) * (w - 1)))) : SkipPoints K w D where
  point x := embed (skipIndex x)
  injective x y hxy := skipIndex_injective
    (h (Set.mem_Iio.mpr (skipIndex_lt x)) (Set.mem_Iio.mpr (skipIndex_lt y)) hxy)

omit [Field K] in
theorem SkipPoints.ofEmbed_point (embed : ℕ → K)
    (h : Set.InjOn embed (Set.Iio (w + (D - 1) * (w - 1)))) (x : Fin w ⊕ Fin ((D - 1) * (w - 1))) :
    (SkipPoints.ofEmbed embed h).point x = embed (skipIndex x) :=
  rfl

/-- The natural-number cast is injective below the characteristic. General; it moves to
`GordieHowe/Foundations/ToMathlib/` when a second use appears. -/
theorem natCast_injOn_Iio_of_le (q : ℕ) [CharP K q] {N : ℕ} (hN : N ≤ q) :
    Set.InjOn (fun i : ℕ => (i : K)) (Set.Iio N) := by
  intro a ha b hb h
  have hmod : a ≡ b [MOD q] := (CharP.natCast_eq_natCast K q).mp h
  have ha' : a < q := lt_of_lt_of_le (Set.mem_Iio.mp ha) hN
  have hb' : b < q := lt_of_lt_of_le (Set.mem_Iio.mp hb) hN
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hmod

/-- **The integer skip domain** (`field_skip.h`, `SkipDomain`, odd characteristic:
`points_[i] = of_scalar(i)`): the integers `0, …, D (w − 1)`, distinct when the characteristic `q`
is at least `w + (D − 1)(w − 1)` (a parameter condition). -/
def SkipPoints.integers (q : ℕ) [CharP K q] (h : w + (D - 1) * (w - 1) ≤ q) : SkipPoints K w D :=
  SkipPoints.ofEmbed (fun i => (i : K)) (natCast_injOn_Iio_of_le q h)

/-- **The byte-subspace skip domain** (`field_skip.h`, `SkipDomain`, characteristic two:
`points_[i]` the embedded `i`-th element of `SkipByteField`): the images of `0, …, D (w − 1)`
under an embedding injective on the 256 bytes (`Fields/GF2_128Skip.lean`'s
`gf2_128SkipEmbed_injOn`), for `D (w − 1) + 1 ≤ 256` (`check(npts_ <= 256)`, a parameter
condition). -/
def SkipPoints.ofByteEmbed (embed : ℕ → K) (hinj : Set.InjOn embed (Set.Iio 256))
    (h : w + (D - 1) * (w - 1) ≤ 256) : SkipPoints K w D :=
  SkipPoints.ofEmbed embed (hinj.mono (Set.Iio_subset_Iio h))

namespace SkipPoints

variable (dom : SkipPoints K w D)

/-- The instances' skip coordinates. -/
def pt (t : Fin w) : K := dom.point (Sum.inl t)

omit [Field K] in
theorem pt_injective : Function.Injective dom.pt := dom.injective.comp Sum.inl_injective

/-- The interpolant of `w` values on the skip coordinates. -/
noncomputable def interp (x : Fin w → K) : K[X] := Lagrange.interpolate Finset.univ dom.pt x

@[simp] theorem eval_interp_pt (x : Fin w → K) (t : Fin w) :
    (dom.interp x).eval (dom.pt t) = x t :=
  Lagrange.eval_interpolate_at_node _ dom.pt_injective.injOn (Finset.mem_univ t)

/-- The interpolant's value at `r` by field operations (`Lagrange.basisEval`); equal to
`(dom.interp x).eval r` (`eval_interp`). -/
def interpEval (x : Fin w → K) (r : K) : K :=
  ∑ t, x t * Lagrange.basisEval Finset.univ dom.pt t r

theorem eval_interp (x : Fin w → K) (r : K) : (dom.interp x).eval r = dom.interpEval x r := by
  simp only [interp, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.eval_basis_eq_basisEval, interpEval]

theorem interp_natDegree_le (x : Fin w → K) : (dom.interp x).natDegree ≤ w - 1 := by
  have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (r := x) dom.pt_injective.injOn
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact natDegree_le_of_degree_lt h

/-- The claimed polynomial: zero on the skip coordinates, the skip message on the extra
points. -/
noncomputable def skipPoly (skip : Fin ((D - 1) * (w - 1)) → K) : K[X] :=
  Lagrange.interpolate Finset.univ dom.point (Sum.elim 0 skip)

@[simp] theorem skipPoly_eval_pt (skip : Fin ((D - 1) * (w - 1)) → K) (t : Fin w) :
    (dom.skipPoly skip).eval (dom.pt t) = 0 :=
  Lagrange.eval_interpolate_at_node (Sum.elim 0 skip) dom.injective.injOn
    (Finset.mem_univ (Sum.inl t))

theorem skipPoly_eval_extra (skip : Fin ((D - 1) * (w - 1)) → K) (i : Fin ((D - 1) * (w - 1))) :
    (dom.skipPoly skip).eval (dom.point (Sum.inr i)) = skip i :=
  Lagrange.eval_interpolate_at_node (Sum.elim 0 skip) dom.injective.injOn
    (Finset.mem_univ (Sum.inr i))

/-- The claimed polynomial has degree at most `D (w − 1)`. `NeZero D`: a relation has degree at
least one (a parameter condition). -/
theorem skipPoly_natDegree_le [NeZero D] (skip : Fin ((D - 1) * (w - 1)) → K) :
    (dom.skipPoly skip).natDegree ≤ D * (w - 1) := by
  have h := natDegree_le_of_degree_lt (Lagrange.degree_interpolate_lt
    (s := Finset.univ) (r := Sum.elim 0 skip) dom.injective.injOn)
  rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by have := NeZero.ne D; omega⟩
  have e : (D' + 1 - 1) * (w - 1) = D' * (w - 1) := by rw [Nat.add_sub_cancel]
  refine h.trans ?_
  rw [e, Nat.succ_mul]
  omega

/-- The verifier's initial sumcheck claim, `Σ_i skip_i · l_{w+i}(r)` over the whole domain
(`MaskedFieldSkip::rows_of`: `l = dom.basis(f, dom.points(), r)`, `claim += skip_j · l[w + j]`). -/
def skipClaim (skip : Fin ((D - 1) * (w - 1)) → K) (r : K) : K :=
  ∑ i, skip i * Lagrange.basisEval Finset.univ dom.point (Sum.inr i) r

theorem skipClaim_eq (skip : Fin ((D - 1) * (w - 1)) → K) (r : K) :
    dom.skipClaim skip r = (dom.skipPoly skip).eval r := by
  simp [skipClaim, skipPoly, Lagrange.interpolate_apply, eval_finsetSum, Fintype.sum_sum_type,
    Lagrange.eval_basis_eq_basisEval]

end SkipPoints

/-! ### The relation and the operands -/

/-- **A batched relation over `K`** (`field_skip.h`, `FieldRelation`): a polynomial `Q` in `k`
operands of total degree at most `D`, with no constant term (every monomial reads an operand;
`FieldRelation::error`), so the zero instances that pad the batch satisfy it
(`eval_zero_Q`). -/
structure Relation (K : Type) [Field K] (k D : ℕ) where
  /-- The relation's polynomial. -/
  Q : MvPolynomial (Fin k) K
  /-- Its total degree is at most `D`. -/
  totalDegree_le : Q.totalDegree ≤ D
  /-- No constant term. -/
  constantCoeff_eq : MvPolynomial.constantCoeff Q = 0

/-- The zero operands satisfy a relation. -/
theorem Relation.eval_zero_Q (R : Relation K k D) : MvPolynomial.eval 0 R.Q = 0 := by
  rw [MvPolynomial.eval_zero]
  exact R.constantCoeff_eq

/-- **The operands of a batch**, padded to `2^n · w` instances: `ops r z j` is operand `j` of
instance `t = r w + z` (`MaskedFieldSkip::prove`, `op(r, z, j) = ops[r w + z][j]`, zero beyond the
batch). -/
abbrev Operands (K : Type) (w n k : ℕ) := Fin (2 ^ n) → Fin w → Fin k → K

variable (R : Relation K k D) (ops : Operands K w n k)

/-- The relation's value on instance `r w + z`. -/
def residual (r : Fin (2 ^ n)) (z : Fin w) : K := MvPolynomial.eval (ops r z) R.Q

/-- **The batch holds**: the relation vanishes on every instance. -/
def Holds : Prop := ∀ r z, residual R ops r z = 0

variable (dom : SkipPoints K w D)

/-- `Q(Â_r(T))` for the interpolated operands of row `r`. -/
noncomputable def residualPoly (r : Fin (2 ^ n)) : K[X] :=
  MvPolynomial.aeval (fun j => dom.interp fun z => ops r z j) R.Q

@[simp] theorem residualPoly_eval_pt (r : Fin (2 ^ n)) (z : Fin w) :
    (residualPoly R ops dom r).eval (dom.pt z) = residual R ops r z := by
  simp only [residualPoly, MvPolynomial.polynomial_eval_aeval, SkipPoints.eval_interp_pt]
  rfl

theorem residualPoly_natDegree_le (r : Fin (2 ^ n)) :
    (residualPoly R ops dom r).natDegree ≤ D * (w - 1) :=
  (MvPolynomial.natDegree_aeval_le (fun _ => dom.interp_natDegree_le _) _).trans
    (Nat.mul_le_mul_right _ R.totalDegree_le)

/-- `g(T) = Σ_r eq(ρ, r) · Q(Â_r(T))`. -/
noncomputable def zeroPoly (ρ : Fin n → K) : K[X] :=
  ∑ r : Fin (2 ^ n), C (PackedClaim.eqPt ρ r) * residualPoly R ops dom r

theorem zeroPoly_natDegree_le (ρ : Fin n → K) :
    (zeroPoly R ops dom ρ).natDegree ≤ D * (w - 1) :=
  natDegree_sum_le_of_forall_le _ _ fun r _ =>
    (natDegree_C_mul_le _ _).trans (residualPoly_natDegree_le R ops dom r)

/-- `g` at a point is the `ρ`-batching of the rows' residual polynomials there. -/
theorem zeroPoly_eval (ρ : Fin n → K) (x : K) :
    (zeroPoly R ops dom ρ).eval x =
      ∑ r : Fin (2 ^ n), PackedClaim.eqPt ρ r * (residualPoly R ops dom r).eval x := by
  simp [zeroPoly, eval_finsetSum]

/-- On the skip coordinates, `g` is the `ρ`-batching of the residuals at that coordinate. -/
theorem zeroPoly_eval_pt (ρ : Fin n → K) (z : Fin w) :
    (zeroPoly R ops dom ρ).eval (dom.pt z) = evalTable (fun r => residual R ops r z) ρ := by
  simp [zeroPoly_eval, evalTable]

/-- `g` at a point by field operations, equal to the evaluation of `zeroPoly` (`zeroEval_eq`):
the prover's skip value `S(p) = Σ_r e_r Q(Σ_z L_z(p) ops(r, z))` (`MaskedFieldSkip::prove`). -/
def zeroEval (ρ : Fin n → K) (x : K) : K :=
  ∑ r : Fin (2 ^ n), PackedClaim.eqPt ρ r *
    MvPolynomial.eval (fun j => dom.interpEval (fun z => ops r z j) x) R.Q

theorem zeroEval_eq (ρ : Fin n → K) (x : K) :
    zeroEval R ops dom ρ x = (zeroPoly R ops dom ρ).eval x := by
  simp only [zeroEval, zeroPoly_eval, residualPoly, MvPolynomial.polynomial_eval_aeval,
    SkipPoints.eval_interp]

/-- The multilinear extension of operand `j` at `(s, r)`: `Σ_row eq(s, row) · Â_{row,j}(r)`. -/
noncomputable def opEval (j : Fin k) (s : Fin n → K) (r : K) : K :=
  evalTable (fun row => (dom.interp fun z => ops row z j).eval r) s

/-- The true terminal vector: the operands' multilinear extensions at `(s, r)`. -/
noncomputable def trueTerminal (s : Fin n → K) (r : K) : Fin k → K :=
  fun j => opEval ops dom j s r

/-- Operand `j` at `r`, as a table on the Boolean cube. -/
noncomputable def opTable (j : Fin k) (r : K) : Cube n → K :=
  fun b => (dom.interp fun z => ops ((binaryLabelEquiv n).symm b) z j).eval r

/-- The multilinear extension of the operand table is `opEval`. -/
theorem value_opTable (j : Fin k) (s : Fin n → K) (r : K) :
    value (opTable ops dom j r) s = opEval ops dom j s r := by
  rw [opEval, GKR.ClaimEvaluation.evalTable_eq_value]
  rfl

/-- `Q` of the operands' multilinear extensions at a fixed `r`. -/
noncomputable def residualMle (r : K) : MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (fun j => mle (opTable ops dom j r)) R.Q

theorem residualMle_degreeOf_le (r : K) (v : Fin n) :
    (residualMle R ops dom r).degreeOf v ≤ D :=
  (MvPolynomial.degreeOf_aeval_le v (fun j => GKR.ClaimEvaluation.mle_degreeOf_le _ v) _).trans
    (by simpa using R.totalDegree_le)

/-- The sumcheck summand `eq(ρ, x) · Q(Â(x))` at a fixed `r`. -/
noncomputable def summand (ρ : Fin n → K) (r : K) : MvPolynomial (Fin n) K :=
  eqPoly ρ * residualMle R ops dom r

theorem summand_degreeOf_le (ρ : Fin n → K) (r : K) (v : Fin n) :
    (summand R ops dom ρ r).degreeOf v ≤ D + 1 := by
  have he := EqPolynomial.degreeOf_eqPoly_le ρ v
  have hr := residualMle_degreeOf_le R ops dom r v
  apply (MvPolynomial.degreeOf_mul_le v _ _).trans
  omega

theorem eval_summand (ρ s : Fin n → K) (r : K) :
    MvPolynomial.eval s (summand R ops dom ρ r) =
      eqProd ρ s * MvPolynomial.eval (trueTerminal ops dom s r) R.Q := by
  simp only [summand, residualMle, map_mul, EqPolynomial.eval_eqPoly, MvPolynomial.eval_aeval,
    GKR.ClaimEvaluation.eval_mle, value_opTable]
  rfl

/-- The cube sum of the summand is `g(r)`. -/
theorem sum_summand (ρ s : Fin n → K) (r : K) :
    Coefficient.trueClaim (summand R ops dom ρ r) s 0 = (zeroPoly R ops dom ρ).eval r := by
  rw [Coefficient.trueClaim_zero, zeroPoly_eval, ← (binaryLabelEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro row _
  have he : eqProd ρ (fun v => boolValue (F := K) (binaryLabelEquiv n row v)) =
      PackedClaim.eqPt ρ row :=
    EqPolynomial.eqProd_bits ρ row.val
  simp only [summand, residualMle, map_mul, EqPolynomial.eval_eqPoly, MvPolynomial.eval_aeval,
    GKR.ClaimEvaluation.mle_boolean]
  rw [he]
  simp [opTable, residualPoly, MvPolynomial.polynomial_eval_aeval]

/-! ### The transcript and the verifier -/

/-- The prover messages: the skip values, `D` coefficients per sumcheck round, and the `k`
terminal operand claims (`MaskedFieldSkip::Proof`). -/
structure Transcript (K : Type) (w D n k : ℕ) where
  /-- The skip values at the extra points. -/
  skip : Fin ((D - 1) * (w - 1)) → K
  /-- The coefficients `q_1, …, q_D` of each round. -/
  rounds : Fin n → Fin D → K
  /-- The terminal operand claims. -/
  terminal : Fin k → K

/-- The verifier challenges, in transcript order. -/
structure Challenges (K : Type) (n k : ℕ) where
  /-- The zerocheck point. -/
  rho : Fin n → K
  /-- The skip challenge. -/
  r : K
  /-- The sumcheck challenges. -/
  s : Fin n → K
  /-- The batching scalars of the opening. -/
  u : Fin k → K

/-- The terminal identity's right side, `eq(ρ, s) · Q(m)` (`claim − prefix · Q(m − P) = 0` with
the pads removed). -/
def terminalValue (ρ s : Fin n → K) (m : Fin k → K) : K := eqProd ρ s * MvPolynomial.eval m R.Q

/-- The batched terminal claim `Σ_j u_j · m_j`. -/
def batch (u m : Fin k → K) : K := ∑ j, u j * m j

/-- **The verifier's checks**: the last sumcheck claim is the terminal identity, and `opening`,
the abstract opening: the batched terminal claims equal the batched operand multilinear extensions
at `(s, r)` (the opening row `Σ_c A_c W_c + Σ_j u_j P_j = Σ_j u_j m_j − constant`, opened by the
packing tree). -/
structure Accepts (ch : Challenges K n k) (tr : Transcript K w D n k) : Prop where
  /-- The terminal identity. -/
  sumcheck : EqFactoredDeg.claims (dom.skipClaim tr.skip ch.r) ch.rho tr.rounds ch.s
    (Fin.last n) = terminalValue R ch.rho ch.s tr.terminal
  /-- The opening. -/
  opening : batch ch.u tr.terminal = batch ch.u (trueTerminal ops dom ch.s ch.r)

/-! ### Events and soundness -/

open Classical in
/-- **The `ρ` event**: the residual table at a failing skip coordinate is nonzero and its
multilinear extension vanishes at `ρ`; degree `n`. The coordinate is chosen from the operands
alone. -/
noncomputable def rhoEvent : ChallengeEventMv K n :=
  if h : ∃ z, ∃ r, residual R ops r z ≠ 0 then
    ⟨mle fun b => residual R ops ((binaryLabelEquiv n).symm b) h.choose, n,
      GKR.ClaimEvaluation.mle_degree _⟩
  else ⟨0, n, by simp⟩

theorem rhoEvent_deg : (rhoEvent R ops).deg = n := by
  unfold rhoEvent
  split <;> rfl

/-- If the batch fails, the `ρ` event is the multilinear extension of the residual table at a
failing skip coordinate, which is nonzero at some row. -/
theorem rhoEvent_of_not_holds (h : ¬ Holds R ops) :
    ∃ z, (rhoEvent R ops).poly = mle (fun b => residual R ops ((binaryLabelEquiv n).symm b) z) ∧
      ∃ r, residual R ops r z ≠ 0 := by
  obtain ⟨r, z, hrz⟩ : ∃ r z, residual R ops r z ≠ 0 := by simpa [Holds] using h
  have hex : ∃ z, ∃ r, residual R ops r z ≠ 0 := ⟨z, r, hrz⟩
  refine ⟨hex.choose, ?_, hex.choose_spec⟩
  simp [rhoEvent, hex]

/-- **The `r` event**: `r` is a root of `g` minus the claimed polynomial; degree `D (w − 1)`. -/
noncomputable def rEvent [NeZero D] (ρ : Fin n → K) (skip : Fin ((D - 1) * (w - 1)) → K) :
    ChallengeEvent K where
  poly := zeroPoly R ops dom ρ - dom.skipPoly skip
  deg := D * (w - 1)
  natDegree_le := (natDegree_sub_le _ _).trans
    (max_le (zeroPoly_natDegree_le R ops dom ρ) (dom.skipPoly_natDegree_le skip))

/-- **The event of sumcheck round `i`**, of degree `D + 1`: the polynomial the verifier's update
implies from the skip message, the messages and the challenges before `i`, minus the true round
polynomial. -/
noncomputable def roundEvent (ρ : Fin n → K) (r : K) (skip : Fin ((D - 1) * (w - 1)) → K)
    (msg : Fin n → Fin D → K) (s : Fin n → K) (i : Fin n) : ChallengeEvent K :=
  Coefficient.roundEvent (summand R ops dom ρ r) (summand_degreeOf_le R ops dom ρ r)
    (EqFactoredDeg.derived (dom.skipClaim skip r) ρ msg s) s i

/-- A round event is fixed by the skip message, the round messages through the round and the
challenges before it. -/
theorem roundEvent_badAt_congr {ρ : Fin n → K} {r : K} {skip : Fin ((D - 1) * (w - 1)) → K}
    {msg msg' : Fin n → Fin D → K} {s s' : Fin n → K} {j : Fin n}
    (hm : ∀ l, l ≤ j → msg l = msg' l) (hs : ∀ v, v < j → s v = s' v) (x : K) :
    (roundEvent R ops dom ρ r skip msg s j).BadAt x ↔
      (roundEvent R ops dom ρ r skip msg' s' j).BadAt x := by
  have hp : (roundEvent R ops dom ρ r skip msg s j).poly =
      (roundEvent R ops dom ρ r skip msg' s' j).poly := by
    refine (Coefficient.roundEvent_poly_congr _ _ _ j hs).trans ?_
    simp only [roundEvent, Coefficient.roundEvent, EqFactoredDeg.derived_congr _ ρ j hm hs]
  simp only [ChallengeEvent.BadAt, hp]

/-- **The `u` event**: `u` is a zero of the linear form of the terminal error; degree `1`. -/
noncomputable def uEvent (s : Fin n → K) (r : K) (m : Fin k → K) : ChallengeEventMv K k where
  poly := ∑ j, MvPolynomial.C (m j - trueTerminal ops dom s r j) * MvPolynomial.X j
  deg := 1
  totalDegree_le := MvPolynomial.totalDegree_finsetSum_le fun j _ =>
    (MvPolynomial.totalDegree_mul _ _).trans
      (le_of_eq (by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]))

/-- The `u` event's polynomial at `u` is the batched terminal error. -/
theorem eval_uEvent (s : Fin n → K) (r : K) (m u : Fin k → K) :
    MvPolynomial.eval u (uEvent ops dom s r m).poly =
      batch u m - batch u (trueTerminal ops dom s r) := by
  simp only [uEvent, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, batch,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The `u` event's polynomial is nonzero when the terminal claims are not the true ones. -/
theorem uEvent_poly_ne_zero {s : Fin n → K} {r : K} {m : Fin k → K}
    (hm : m ≠ trueTerminal ops dom s r) : (uEvent ops dom s r m).poly ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hm
  intro hz
  have he := congrArg (MvPolynomial.eval (Pi.single j 1)) hz
  rw [map_zero] at he
  simp [uEvent, Pi.single_apply] at he
  exact hj (sub_eq_zero.mp he)

/-- **Soundness of the field-generic skip zerocheck.** If the verifier accepts, the batch holds,
or one challenge event occurred: `ρ` (degree `n`), `r` (degree `D (w − 1)`), a sumcheck round `i`
at `s i` (degree `D + 1`), or `u` (degree `1`). Each event is built from the operands and the
transcript before its challenge; there are no hypotheses besides acceptance and the parameter
condition `NeZero D`. -/
theorem soundness [NeZero D] {ch : Challenges K n k} {tr : Transcript K w D n k}
    (h : Accepts R ops dom ch tr) :
    Holds R ops ∨ (rhoEvent R ops).BadAt ch.rho ∨ (rEvent R ops dom ch.rho tr.skip).BadAt ch.r ∨
      (∃ i, (roundEvent R ops dom ch.rho ch.r tr.skip tr.rounds ch.s i).BadAt (ch.s i)) ∨
      (uEvent ops dom ch.s ch.r tr.terminal).BadAt ch.u := by
  by_cases hm : tr.terminal = trueTerminal ops dom ch.s ch.r
  swap
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨uEvent_poly_ne_zero ops dom hm, ?_⟩)))
    rw [eval_uEvent, h.opening, sub_self]
  have hfin : terminalValue R ch.rho ch.s tr.terminal =
      MvPolynomial.eval ch.s (summand R ops dom ch.rho ch.r) := by
    rw [eval_summand, hm]
    rfl
  have hacc := h.sumcheck
  rw [hfin] at hacc
  rcases EqFactoredDeg.sound _ (summand_degreeOf_le R ops dom ch.rho ch.r) hacc with
    hinit | hround
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inl hround)))
  rw [sum_summand, dom.skipClaim_eq] at hinit
  by_cases hP : zeroPoly R ops dom ch.rho - dom.skipPoly tr.skip = 0
  swap
  · refine Or.inr (Or.inr (Or.inl ⟨hP, ?_⟩))
    change (zeroPoly R ops dom ch.rho - dom.skipPoly tr.skip).eval ch.r = 0
    rw [eval_sub, hinit, sub_self]
  have hzp : zeroPoly R ops dom ch.rho = dom.skipPoly tr.skip := sub_eq_zero.mp hP
  by_cases hH : Holds R ops
  · exact Or.inl hH
  refine Or.inr (Or.inl ?_)
  obtain ⟨z, hpoly, row, hrow⟩ := rhoEvent_of_not_holds R ops hH
  have hv : value (fun b => residual R ops ((binaryLabelEquiv n).symm b) z) ch.rho =
      evalTable (fun row => residual R ops row z) ch.rho :=
    (GKR.ClaimEvaluation.evalTable_eq_value (fun row => residual R ops row z) ch.rho).symm
  refine ⟨?_, ?_⟩
  · rw [hpoly]
    exact GKR.ClaimEvaluation.mle_ne_zero _ ⟨binaryLabelEquiv n row, by simpa using hrow⟩
  · rw [hpoly, GKR.ClaimEvaluation.eval_mle, hv, ← zeroPoly_eval_pt, hzp, dom.skipPoly_eval_pt]

/-! ### Completeness -/

/-- The honest prover's transcript for given challenges: the skip values `g(point (inr i))`
(`zeroEval`), the coefficients `1, …, D` of each round's factor (`EqFactoredDeg.honest`), and the
true terminal claims. Round `i` reads only `ρ`, `r` and the challenges before `i`
(`EqFactoredDeg.honest_congr`). -/
noncomputable def honest (ch : Challenges K n k) : Transcript K w D n k where
  skip i := zeroEval R ops dom ch.rho (dom.point (Sum.inr i))
  rounds := EqFactoredDeg.honest ch.rho (residualMle R ops dom ch.r) ch.s
  terminal := trueTerminal ops dom ch.s ch.r

/-- For a batch that holds the honest skip message interpolates to `g`. `NeZero w`, `NeZero D`
are parameter conditions. -/
theorem skipPoly_honest [NeZero w] [NeZero D] (h : Holds R ops) (ch : Challenges K n k) :
    dom.skipPoly (honest R ops dom ch).skip = zeroPoly R ops dom ch.rho := by
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ dom.injective.injOn ?_ ?_
  · have hd := zeroPoly_natDegree_le R ops dom ch.rho
    have hw := NeZero.pos w
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by have := NeZero.ne D; omega⟩
    have hlt : (zeroPoly R ops dom ch.rho).natDegree <
        (Finset.univ : Finset (Fin w ⊕ Fin ((D' + 1 - 1) * (w - 1)))).card := by
      rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
        Nat.add_sub_cancel]
      rw [Nat.succ_mul] at hd
      omega
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hlt)
  · rintro (t | i) _
    · change (zeroPoly R ops dom ch.rho).eval (dom.pt t) = 0
      rw [zeroPoly_eval_pt]
      exact Finset.sum_eq_zero fun j _ => by simp [h j t]
    · exact (zeroEval_eq R ops dom _ _).symm

/-- **Completeness**: a batch that holds, with the honest transcript, passes every check for every
challenge. Hypotheses: the honest input `h` and the parameter conditions `NeZero w`, `NeZero D`. -/
theorem completeness [NeZero w] [NeZero D] (h : Holds R ops) (ch : Challenges K n k) :
    Accepts R ops dom ch (honest R ops dom ch) where
  sumcheck := by
    have hc := EqFactoredDeg.complete ch.rho (residualMle_degreeOf_le R ops dom ch.r) ch.s
    have h0 : dom.skipClaim (honest R ops dom ch).skip ch.r =
        Coefficient.trueClaim (summand R ops dom ch.rho ch.r) ch.s 0 := by
      rw [dom.skipClaim_eq, skipPoly_honest R ops dom h, sum_summand]
    have h1 : terminalValue R ch.rho ch.s (honest R ops dom ch).terminal =
        MvPolynomial.eval ch.s (summand R ops dom ch.rho ch.r) := by
      rw [eval_summand]
      rfl
    rw [h0, h1]
    exact hc
  opening := rfl

/-! ### Merging several relations -/

/-- **The merged relation** `Σ_i γ^i Q_i` (`lib/gordiehowe/compiler/batch.h`, several `FieldBatchPart`s; `γ` drawn
after the label `gordiehowe.field-batch.gamma`, before the zerocheck). -/
noncomputable def merge {np : ℕ} (Qs : Fin np → MvPolynomial (Fin k) K) (γ : K) :
    MvPolynomial (Fin k) K :=
  ∑ i, MvPolynomial.C (γ ^ i.val) * Qs i

theorem eval_merge {np : ℕ} (Qs : Fin np → MvPolynomial (Fin k) K) (γ : K) (x : Fin k → K) :
    MvPolynomial.eval x (merge Qs γ) = ∑ i, γ ^ i.val * MvPolynomial.eval x (Qs i) := by
  simp [merge]

/-- **The merged relation as a relation** of degree at most `D` when every part is. -/
noncomputable def Relation.merge {np : ℕ} (Rs : Fin np → Relation K k D) (γ : K) :
    Relation K k D where
  Q := FieldSkip.merge (fun i => (Rs i).Q) γ
  totalDegree_le := MvPolynomial.totalDegree_finsetSum_le fun i _ =>
    (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_C, zero_add]; exact (Rs i).totalDegree_le)
  constantCoeff_eq := by simp [FieldSkip.merge, (Rs _).constantCoeff_eq]

open Classical in
/-- **The merging event** for instances `x`: `γ` is a root of `Σ_i Q_i(x_t) X^i` at an instance `t`
where some part fails, chosen from the instances alone; degree `np − 1`. -/
noncomputable def mergeEvent {np : ℕ} (Qs : Fin np → MvPolynomial (Fin k) K) {ι : Type}
    (x : ι → Fin k → K) : ChallengeEvent K :=
  if h : ∃ t, ∃ i, MvPolynomial.eval (x t) (Qs i) ≠ 0 then
    ⟨∑ i, C (MvPolynomial.eval (x h.choose) (Qs i)) * X ^ i.val, np - 1,
      natDegree_sum_le_of_forall_le _ _ fun i _ =>
        (natDegree_C_mul_X_pow_le _ _).trans (by have := i.isLt; omega)⟩
  else ⟨0, np - 1, by simp⟩

/-- **Merging soundness**: if the merged relation vanishes on every instance, every part does, or
`γ` lies in the merging event. -/
theorem merge_sound {np : ℕ} (Qs : Fin np → MvPolynomial (Fin k) K) {ι : Type}
    (x : ι → Fin k → K) {γ : K} (h : ∀ t, MvPolynomial.eval (x t) (merge Qs γ) = 0) :
    (∀ i t, MvPolynomial.eval (x t) (Qs i) = 0) ∨ (mergeEvent Qs x).BadAt γ := by
  by_cases hall : ∀ i t, MvPolynomial.eval (x t) (Qs i) = 0
  · exact Or.inl hall
  have hex : ∃ t, ∃ i, MvPolynomial.eval (x t) (Qs i) ≠ 0 := by
    simp only [not_forall] at hall
    obtain ⟨i, t, hit⟩ := hall
    exact ⟨t, i, hit⟩
  refine Or.inr ?_
  obtain ⟨i₀, hi₀⟩ := hex.choose_spec
  have hpoly : (mergeEvent Qs x).poly =
      ∑ i, C (MvPolynomial.eval (x hex.choose) (Qs i)) * X ^ i.val := by
    simp [mergeEvent, hex]
  refine ⟨?_, ?_⟩
  · rw [hpoly]
    intro hz
    have hc := congrArg (fun p : K[X] => p.coeff i₀.val) hz
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero, Fin.val_inj] at hc
    rw [Finset.sum_ite_eq] at hc
    simp at hc
    exact hi₀ hc
  · rw [hpoly, eval_finsetSum]
    have := h hex.choose
    rw [eval_merge] at this
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact Eq.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _) this

/-- **Merging completeness**: parts that vanish on every instance give a merged relation that
vanishes, for every `γ`. -/
theorem merge_complete {np : ℕ} (Qs : Fin np → MvPolynomial (Fin k) K) {ι : Type}
    (x : ι → Fin k → K) (h : ∀ i t, MvPolynomial.eval (x t) (Qs i) = 0) (γ : K) (t : ι) :
    MvPolynomial.eval (x t) (merge Qs γ) = 0 := by
  simp [eval_merge, h]

end GordieHowe.Sumcheck.FieldSkip
