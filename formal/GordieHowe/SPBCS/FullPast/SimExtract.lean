-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimExtractGame
public import GordieHowe.Model.QROM.QueryCountExpand
public import GordieHowe.Model.QROM.AdaptiveCount

@[expose] public section

/-!
# The simulation-extraction game at one adversary, for the series–parallel base model

Objects of the weak simulation-sound extractability game (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), weak variant, for residual-state tests that make no oracle queries)
at one adaptive interactive adversary `A` with the simulation challenger running the simulator
program `Psim`, at the series–parallel base model (`GordieHowe.SPBCS.FullPast`):

- `Reg`: the composed registers; `branchQueries`: the per-branch query count of the composed
  algorithm; `Fresh`: the adversary's statement is none of its proof queries.
- `SimExtractionAdversary.tsum_le_tsum_add`: an auxiliary-input average of bounds `x a ≤ y a + c`
  is a bound `∑ x ≤ ∑ y + c`.

The theorem in the QROM is the spBCS compiler's (`GordieHowe/SPBCS/SimExtract.lean`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : Base P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-! ### The game at one adversary -/

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- The composed registers of `A` with the simulation challenger. -/
abbrev Reg := M.Register B A.toTPKindAlg Psim Q

variable (fx : X' → X)

/-- **The statement is fresh** on the composed registers. -/
def Fresh (v : Reg A Psim Q) : Prop :=
  ∀ x' ∈ queried A.toTPKindAlg Psim Q v, fx x' ≠ (advOut A.toTPKindAlg Psim Q v).stmt

variable {E₀ : (j : ι) → (M.comp j).Encoder} {VE : M.ViewEncoder E₀ Qs} {Pub : Type}
  {pub : X → Pub} {S : CausalJointSimulator VE.MV Pub} {T : M.Preimages}

/-! ### Averages over auxiliary inputs -/

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- An auxiliary-input average of bounds `x a ≤ y a + c` is a bound `∑ x ≤ ∑ y + c`. -/
theorem SimExtractionAdversary.tsum_le_tsum_add {tq Q : ℕ} (𝒜 : M.SimExtractionAdversary B X' tq Q)
    {x y : 𝒜.Aux → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, x a ≤ y a + c) :
    ∑' a, 𝒜.aux a * x a ≤ ∑' a, 𝒜.aux a * y a + c := by
  calc ∑' a, 𝒜.aux a * x a ≤ ∑' a, (𝒜.aux a * y a + 𝒜.aux a * c) :=
        ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; gcongr; exact h a
    _ = ∑' a, 𝒜.aux a * y a + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : FullPast P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-! ### The game at one adversary -/

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- **The per-branch query count of the composed algorithm.** -/
abbrev branchQueries : ℕ := A.width * A.budget + Q * Psim.q + A.width * A.post

end FullPast

end GordieHowe.SPBCS
