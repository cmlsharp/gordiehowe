-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.Ring.Transform
public import LatticeCrypto.Ring.Norms
public import GordieHowe.Model.Lattice.Search
public import GordieHowe.Foundations.ToMathlib.FintypeBytes
public import VCVio.OracleComp.Constructions.SampleableType.Basic

@[expose] public section

/-!
# Module-SIS in Hermite normal form

The module short-integer-solution problem over a negacyclic ring `R_q = Z_q[X]/(X^n + 1)`, in the
Hermite normal form `[A | I]` of the Dilithium security analysis: given `A ∈ R_q^{k×l}`, find a
nonzero `(z, u) ∈ R_q^l × R_q^k` with `A z + u = 0` and small coefficients.

## Sources

- Module-SIS: Langlois and Stehlé, *Worst-case to average-case reductions for module lattices*
  (Des. Codes Cryptogr. 75(3), 2015; ePrint 2012/090), cited as the origin of the problem by KLS18
  (below, §4.5.1) and by the Dilithium specification (below, §6.1). The library's form is that of
  the two documents below; the text of Langlois–Stehlé has not been checked against it here.
- `[I | A]` form with one bound: Kiltz, Lyubashevsky and Schaffner, *A Concrete Treatment of
  Fiat-Shamir Signatures in the Quantum Random-Oracle Model* (EUROCRYPT 2018, ePrint 2017/916),
  §4.5.1, and *CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation*
  (Version 3.1), §6.1: `Adv^MSIS_{m,k,γ}(A) = Pr[0 < ‖y‖∞ ≤ γ ∧ [I | A] · y = 0 | A ← R_q^{m×k};
  y ← A(A)]`.
- Two bounds: the Dilithium specification (Version 3.1), §6.2.2: two signatures that differ only in
  `(z, h)` give `‖z‖∞ ≤ 2(γ₁ − β)` and `‖u‖∞ ≤ 4γ₂ + 2` with `A z + u = 0`; and eq. (8),
  `ζ' = max{2(γ₁ − β), 4γ₂ + 2}`, the single bound of its MSIS term.

## The library's form

- `KernelAI norm βz βu A x`: `x = (z, u)` is nonzero, `A * z + u = 0`, `‖z‖∞ ≤ βz` and
  `‖u‖∞ ≤ βu`. The solution of `[I | A] · y = 0` with `y = (u, z)` written as `(z, u)`; the bound
  `‖y‖∞ ≤ γ` of the one-bound form is the two bounds at `βz = βu = γ` (the `∞`-norm of `y` is the
  larger of those of its two parts, as `PolyVec.cInfNorm` is a maximum over components).
- The matrix lives in the transform domain `Hat` and acts on coefficient-domain vectors by the
  vendored `TransformOps.coeffMatVecMul` (`A * z`), as FIPS 204 key generation and verification
  compute it: `ExpandA` outputs `Â` in `T_q` (FIPS 204, Algorithm 32). The sources draw `A`
  uniformly in `R_q^{k×l}`; here `Â` is uniform in `Hat^{k×l}`.
- `msisWinProb norm βz βu A`: the win probability of `A : PolyMatrix Hat k l → PMF (Option _)`
  at a uniform matrix (`Search.winProb`). `MSISHard norm βz βu 𝒜 ε`: every adversary of `𝒜` wins
  with probability at most `ε`.
- `KernelAI.mono`, `msisWinProb_mono`: larger bounds are won at least as often, so hardness at
  larger bounds gives hardness at smaller ones (`MSISHard.mono_bounds`).
- `KernelAI.of_fst_ne_zero`: a nonzero `z` makes `(z, u)` nonzero.
- The `n`-instance game and its bound `msisMultiWinProb_le` are `Search.multiValid` and
  `Search.multiWinProb_le_card_mul` at `KernelAI`.
-/

namespace GordieHowe.Lattice

open LatticeCrypto TransformOps
open scoped ENNReal

variable {Coeff : Type} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat : Type}
  [AddCommGroup Hat] [ops : TransformOps ring Hat] (norm : NormOps ring.backend) {k l : ℕ}

/-- **A solution of Module-SIS in the form `[A | I]`** with bounds `βz`, `βu`: `x = (z, u)` is
nonzero, `A * z + u = 0`, `‖z‖∞ ≤ βz` and `‖u‖∞ ≤ βu` (Dilithium specification, Version 3.1,
§6.2.2; one bound `βz = βu = γ` is §6.1 and KLS18 §4.5.1). -/
def KernelAI (βz βu : ℕ) (A : PolyMatrix Hat k l)
    (x : PolyVec ring.Poly l × PolyVec ring.Poly k) : Prop :=
  x ≠ 0 ∧ A * x.1 + x.2 = 0 ∧ PolyVec.cInfNorm norm x.1 ≤ βz ∧ PolyVec.cInfNorm norm x.2 ≤ βu

variable {norm}

/-- Larger bounds admit every solution of smaller ones. -/
theorem KernelAI.mono {βz βu βz' βu' : ℕ} (hz : βz ≤ βz') (hu : βu ≤ βu')
    {A : PolyMatrix Hat k l} {x : PolyVec ring.Poly l × PolyVec ring.Poly k}
    (h : KernelAI norm βz βu A x) : KernelAI norm βz' βu' A x :=
  ⟨h.1, h.2.1, h.2.2.1.trans hz, h.2.2.2.trans hu⟩

/-- A nonzero `z` makes `(z, u)` nonzero. -/
theorem KernelAI.of_fst_ne_zero {βz βu : ℕ} {A : PolyMatrix Hat k l}
    {x : PolyVec ring.Poly l × PolyVec ring.Poly k} (hz : x.1 ≠ 0) (hk : A * x.1 + x.2 = 0)
    (hnz : PolyVec.cInfNorm norm x.1 ≤ βz) (hnu : PolyVec.cInfNorm norm x.2 ≤ βu) :
    KernelAI norm βz βu A x :=
  ⟨fun h => hz (by rw [h]; rfl), hk, hnz, hnu⟩

variable (norm) [Fintype Hat] [DecidableEq Hat] [Nonempty Hat]

/-- **The Module-SIS win probability** of `A` in the form `[A | I]` with bounds `βz`, `βu`, at a
uniform matrix. -/
noncomputable def msisWinProb (βz βu : ℕ)
    (A : PolyMatrix Hat k l → PMF (Option (PolyVec ring.Poly l × PolyVec ring.Poly k))) : ℝ≥0∞ :=
  winProb (KernelAI norm βz βu) A

/-- **Hardness of Module-SIS for the class `𝒜`** with bounds `βz`, `βu`. -/
def MSISHard (βz βu : ℕ)
    (𝒜 : Set (PolyMatrix Hat k l → PMF (Option (PolyVec ring.Poly l × PolyVec ring.Poly k))))
    (ε : ℝ≥0∞) : Prop :=
  Hard (KernelAI norm βz βu) 𝒜 ε

variable {norm}

omit [DecidableEq Hat] in
theorem msisWinProb_mono {βz βu βz' βu' : ℕ} (hz : βz ≤ βz') (hu : βu ≤ βu')
    (A : PolyMatrix Hat k l → PMF (Option (PolyVec ring.Poly l × PolyVec ring.Poly k))) :
    msisWinProb norm βz βu A ≤ msisWinProb norm βz' βu' A :=
  winProb_mono (fun _ _ h => h.mono hz hu) A

omit [DecidableEq Hat] in
/-- Hardness at larger bounds gives hardness at smaller ones. -/
theorem MSISHard.mono_bounds {βz βu βz' βu' : ℕ} (hz : βz ≤ βz') (hu : βu ≤ βu')
    {𝒜 : Set (PolyMatrix Hat k l → PMF (Option (PolyVec ring.Poly l × PolyVec ring.Poly k)))}
    {ε : ℝ≥0∞} (h : MSISHard norm βz' βu' 𝒜 ε) : MSISHard norm βz βu 𝒜 ε :=
  Hard.mono_valid h fun _ _ hx => hx.mono hz hu

omit [DecidableEq Hat] in
/-- **The one-bound form is the two-bound form at `max`**: hardness of `MSIS_{k,ℓ,ζ'}` with
`ζ' = max βz βu` (the Dilithium specification's eq. (8) form) gives hardness with bounds `βz`,
`βu`. -/
theorem MSISHard.of_max {βz βu : ℕ}
    {𝒜 : Set (PolyMatrix Hat k l → PMF (Option (PolyVec ring.Poly l × PolyVec ring.Poly k)))}
    {ε : ℝ≥0∞} (h : MSISHard norm (max βz βu) (max βz βu) 𝒜 ε) : MSISHard norm βz βu 𝒜 ε :=
  h.mono_bounds (le_max_left _ _) (le_max_right _ _)

omit [DecidableEq Hat] in
/-- **The `n`-instance Module-SIS game** is won at most `n` times as often as the single-instance
game, by the guessing adversary (`Search.multiWinProb_le_card_mul`). -/
theorem msisMultiWinProb_le (βz βu : ℕ) {n : ℕ} [NeZero n]
    (A : (Fin n → PolyMatrix Hat k l) →
      PMF (Option (Fin n × (PolyVec ring.Poly l × PolyVec ring.Poly k)))) :
    winProb (multiValid (KernelAI norm βz βu) n) A ≤ n * msisWinProb norm βz βu (guess A) :=
  multiWinProb_le_card_mul _ A

end GordieHowe.Lattice
