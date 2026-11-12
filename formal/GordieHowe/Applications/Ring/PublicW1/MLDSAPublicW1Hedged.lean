-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Regularity
public import GordieHowe.Applications.Ring.PublicW1.MaskOracle
public import GordieHowe.Applications.MLDSA.Signing.Hedged

@[expose] public section

/-!
# Hedged masks and the keep level of the ring publishing `w₁`

FIPS 204 Algorithm 7 (ML-DSA.Sign_internal) derives the masks of a signature from a fresh
32-byte nonce `rnd`: `ρ'' = H(K ‖ rnd ‖ µ, 64)` (line 7) and `y = ExpandMask(ρ'', κ)` for the
attempt counter `κ` (line 11), with at most `T` attempts per call. The composition of `H` and
`ExpandMask` is a random oracle onto the mask box (`MaskBox p`) on the points
`(rnd, (κ, (K, (tr, m))))`.

- `keepLevel`: the keep level at the cut-off `β_min`, the defect budget `s` and the threshold
  fraction `θ`: half the signer's level `K β_min` times `θ` times the least mass `(1 - s) |V|` of
  a ring of defect at most `s`.
- `W1CouplingParams`, `W1CouplingParams.ofLt`: the coupling parameters of the anonymity and
  refusal bounds (`MLDSAW1AnonQuery.lean`, `MLDSAW1Refusal.lean`), and an instance at every
  `s < 1`.
- `expect3_le_of_mix`, `card_bytes32`: averaging a pointwise bound through a mixture, and the
  number of 32-byte strings.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

section Signer

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]


/-! ### Anonymity against the hedged signer -/


/-! ### The keep bound from the family bound -/

section KeepFromFamily

open IOP GordieHowe.SPBCS

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}

/-- **The keep level** at the cut-off `β_min`, the defect budget `s` and the threshold fraction
`θ`: half the signer's level `K β_min` times `θ` times the least mass `(1 - s) |V|` of a ring of
defect at most `s`. -/
noncomputable def keepLevel (p : Params) (βmin : ℚ≥0) (s θ : ℝ) : ℝ :=
  (standinScale p * βmin).toReal * (θ * ((1 - s) * Fintype.card (BucketVec p))) / 2


end KeepFromFamily

/-- **The coupling parameters of the anonymity and refusal bounds** at the parameter set `p`, the
cut-off `β_min` and the defect budget `s`: a threshold fraction `θ ∈ (0, 1)`, `s < 1`, and a keep
level `Lk` at most `keepLevel p βmin s θ` and at most `1`. The Prop fields are hypotheses the user
supplies; the bounds hold for every value of the data fields, and `W1CouplingParams.ofLt` gives an
instance at every `s < 1`. -/
structure W1CouplingParams (p : Params) (βmin : ℚ≥0) (s : ℝ) where
  /-- The threshold fraction. -/
  θ : ℝ
  /-- The keep level. -/
  Lk : ℝ
  /-- The threshold fraction is positive. -/
  θ_pos : 0 < θ
  /-- The threshold fraction is below one. -/
  θ_lt_one : θ < 1
  /-- The defect budget is below one. -/
  s_lt_one : s < 1
  /-- The keep level is at most `keepLevel p βmin s θ`. -/
  Lk_le_keepLevel : Lk ≤ keepLevel p βmin s θ
  /-- The keep level is at most one. -/
  Lk_le_one : Lk ≤ 1

/-- **Coupling parameters at every defect budget below one**: `θ = 1/2` and the keep level
`min (keepLevel p βmin s (1/2)) 1`. -/
noncomputable def W1CouplingParams.ofLt (p : Params) (βmin : ℚ≥0) {s : ℝ} (hs : s < 1) :
    W1CouplingParams p βmin s :=
  ⟨1 / 2, min (keepLevel p βmin s (1 / 2)) 1, by norm_num, by norm_num, hs, min_le_left _ _,
    min_le_right _ _⟩

end Signer


/-- **Averaging a pointwise bound through a mixture**: if `x a b c ≤ 𝔼_d y a b c d + 2 ε a b c`
pointwise and `𝔼_{a, b, c} y a b c d ≤ B` for every `d`, then `𝔼 x ≤ B + 2 𝔼 ε`. -/
theorem expect3_le_of_mix {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Nonempty δ] (x ε : α → β → γ → ℝ) (y : α → β → γ → δ → ℝ)
    {B : ℝ} (h : ∀ a b c, x a b c ≤ 𝔼 d, y a b c d + 2 * ε a b c)
    (hB : ∀ d, 𝔼 a, 𝔼 b, 𝔼 c, y a b c d ≤ B) :
    𝔼 a, 𝔼 b, 𝔼 c, x a b c ≤ B + 2 * 𝔼 a, 𝔼 b, 𝔼 c, ε a b c := by
  refine (Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun b _ =>
    Finset.expect_le_expect fun c _ => h a b c).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect]
  refine add_le_add ?_ le_rfl
  have e : 𝔼 a, 𝔼 b, 𝔼 c, 𝔼 d, y a b c d = 𝔼 d, 𝔼 a, 𝔼 b, 𝔼 c, y a b c d := by
    simp_rw [Finset.expect_comm (s := Finset.univ (α := γ)) (t := Finset.univ (α := δ))]
    simp_rw [Finset.expect_comm (s := Finset.univ (α := β)) (t := Finset.univ (α := δ))]
    rw [Finset.expect_comm]
  rw [e]
  exact (Finset.expect_le_expect fun d _ => hB d).trans_eq (Fintype.expect_const _)

/-! ### The hedged headlines -/

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

/-- `Bytes 32` has `2^256` values. -/
theorem card_bytes32 [inst : Fintype (_root_.MLDSA.Bytes 32)] :
    (@Fintype.card _ inst : ℝ) = 2 ^ 256 := by
  rw [Fintype.card_congr (Vector.equivFun UInt8 32), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr UInt8.equivFin, Fintype.card_fin]
  norm_num


end GordieHowe.Ring.MLDSAW1
