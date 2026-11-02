-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.Scheme
public import GordieHowe.Model.Lattice.MSIS
public import GordieHowe.Model.Lattice.MLWE

@[expose] public section

/-!
# Module-SIS at ML-DSA

The library's Module-SIS game (`GordieHowe/Model/Lattice/MSIS.lean`) at the ML-DSA ring
`R_q = Z_q[X]/(X^256 + 1)`, `q = 8380417` (FIPS 204, §6.1 and Table 1), with the matrix in `T_q`
acting by the vendored `Â * z` of key generation and verification, and the `∞`-norm
`polyVecBounded` of the ML-DSA norm checks.

- `Kernel p βz βu Â x`: the `[Â | I]` relation at the parameter set `p`; `kernel_iff` states it in
  the ML-DSA files' own terms (`x ≠ 0 ∧ Â * x.1 + x.2 = 0 ∧ polyVecBounded x.1 βz ∧
  polyVecBounded x.2 βu`).
- **Uniform matrix**: `msisWinProb normOps βz βu` at `TqMatrix p.k p.l` (the game of the sources).
- **Key-generation form with a public seed.** `keyGenMatrix p prims ξ`: the matrix
  `Â = ExpandA(ρ)` of `keyGenFromSeed p prims ξ` (FIPS 204, Algorithm 6). `KeyGenKernel`: a
  solution for that matrix. `keyGenMsisWinProb p prims βz βu A`: the challenger draws the
  key-generation seed `ξ` uniformly, gives it to the adversary (so the adversary also has `ρ`, `Â`
  and every output of key generation), and the adversary wins with a solution for `Â`.
  `keyGenMsisMultiWinProb`: `n` independent seeds, given together, and a solution for one of
  their matrices; `keyGenMsisMultiWinProb_le`: at most `n` times the single-seed win probability of
  the guessing adversary.
- **The two forms** differ only in the law of the matrix: in the key-generation form `Â` is
  `ExpandA` of the first output `ρ` of `H(ξ ‖ k ‖ l, 128)` (`keyGenMatrix_eq`), and the adversary
  holds `ξ`; in the source form `Â` is uniform. No relation between their win probabilities is
  stated here.
- **Bounds.** `msisBoundZ p = 2(γ₁ − β)` and `msisBoundU p = 4γ₂ + 2` (Dilithium specification,
  Version 3.1, §6.2.2), with their values at ML-DSA-44/65/87; `msisStrictBoundZ p = 2(γ₁ − β − 1)`,
  the bound on the difference of two responses that pass the strict check `‖z‖∞ < γ₁ − β`
  (FIPS 204, Algorithm 7 line 23 and Algorithm 8 line 13), with `msisStrictBoundZ_le`.
  `msisBounds_lt_halfModulus`: every bound is below `q / 2`, so the norm checks are not vacuous
  (the centered `∞`-norm of any vector is at most `⌊q / 2⌋`, `cInfNorm_le_halfq`).
- **MLWE parameters.** `mlweDims_mldsa44` and its siblings: `(k, l, η)` of FIPS 204 Table 1.
- **MLWE against unrestricted tests.** `card_rq`, `card_rqVec`, `card_bytes`: `|R_q| = q^256`,
  `|R_q^k| = q^(256 k)`, `|Bytes 32| = 256^32`. `not_mlweHard_univ_of_seed`: for a secret law that
  is a function of a uniform 32-byte seed (as the law of `ExpandS` on the key-generation seed is),
  the class of all `[0, 1]`-valued tests is not MLWE-hard (`MLWEHard`) at any `ε < 1/2`
  (`not_mlweHard_univ`): an algorithm that need not be efficient decides whether `t` is the
  public vector of some seed.
-/

namespace GordieHowe.Lattice

open _root_.MLDSA LatticeCrypto TransformOps
open scoped ENNReal

variable (p : Params)

/-! ### Bounds -/

/-- `2(γ₁ − β)`: the bound on `z` in the strong-unforgeability step of the Dilithium
specification (Version 3.1, §6.2.2). -/
def msisBoundZ : ℕ := 2 * (p.gamma1 - p.beta)

/-- `4γ₂ + 2`: the bound on `u` in the same step. -/
def msisBoundU : ℕ := 4 * p.gamma2 + 2

/-- `2(γ₁ − β − 1)`: the bound on `z − z'` for two responses with `‖z‖∞, ‖z'‖∞ < γ₁ − β`, the
strict check of FIPS 204 (Algorithm 7, line 23; Algorithm 8, line 13). -/
def msisStrictBoundZ : ℕ := 2 * (p.gamma1 - p.beta - 1)

theorem msisStrictBoundZ_le : msisStrictBoundZ p ≤ msisBoundZ p := by
  unfold msisStrictBoundZ msisBoundZ
  omega

theorem msisBounds_mldsa44 :
    msisBoundZ mldsa44 = 261988 ∧ msisStrictBoundZ mldsa44 = 261986 ∧
      msisBoundU mldsa44 = 380930 := by
  decide

theorem msisBounds_mldsa65 :
    msisBoundZ mldsa65 = 1048184 ∧ msisStrictBoundZ mldsa65 = 1048182 ∧
      msisBoundU mldsa65 = 1047554 := by
  decide

theorem msisBounds_mldsa87 :
    msisBoundZ mldsa87 = 1048336 ∧ msisStrictBoundZ mldsa87 = 1048334 ∧
      msisBoundU mldsa87 = 1047554 := by
  decide

/-- **The bounds are below `q / 2`** at the three parameter sets, so the norm checks of `Kernel`
are not vacuous. -/
theorem msisBounds_lt_halfModulus :
    ∀ p ∈ [mldsa44, mldsa65, mldsa87],
      msisBoundZ p < modulus / 2 ∧ msisBoundU p < modulus / 2 := by
  decide

/-- **The MLWE dimensions and secret range** `(k, l, η)` of ML-DSA-44 (FIPS 204, Table 1). -/
theorem mlweDims_mldsa44 : (mldsa44.k, mldsa44.l, mldsa44.eta) = (4, 4, 2) := rfl

/-- `(k, l, η)` of ML-DSA-65 (FIPS 204, Table 1). -/
theorem mlweDims_mldsa65 : (mldsa65.k, mldsa65.l, mldsa65.eta) = (6, 5, 4) := rfl

/-- `(k, l, η)` of ML-DSA-87 (FIPS 204, Table 1). -/
theorem mlweDims_mldsa87 : (mldsa87.k, mldsa87.l, mldsa87.eta) = (8, 7, 2) := rfl

/-! ### Cardinalities -/

theorem card_coeff : Fintype.card Coeff = modulus := ZMod.card _

theorem card_coeffFun : Fintype.card (Fin ringDegree → Coeff) = modulus ^ ringDegree := by
  rw [Fintype.card_fun, card_coeff, Fintype.card_fin]

theorem card_rq : Fintype.card Rq = modulus ^ ringDegree := by
  have hdeg : coeffRing.backend.degree = ringDegree := rfl
  rw [Fintype.card_congr coeffRing.backend.equivPi, hdeg, card_coeffFun]

theorem card_rqVec (k : ℕ) : Fintype.card (RqVec k) = (modulus ^ ringDegree) ^ k := by
  rw [Fintype.card_congr (Vector.equivFun Rq k), Fintype.card_fun, Fintype.card_fin, card_rq]

theorem card_bytes (n : ℕ) : Fintype.card (Bytes n) = 256 ^ n := by
  rw [Fintype.card_congr (Vector.equivFun UInt8 n), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr UInt8.equivFin, Fintype.card_fin]

/-! ### The relation -/

variable [nttOps : NTTRingOps]

/-- **The `[Â | I]` Module-SIS relation at ML-DSA** with bounds `βz`, `βu`. -/
abbrev Kernel (βz βu : ℕ) (aHat : TqMatrix p.k p.l) (x : RqVec p.l × RqVec p.k) : Prop :=
  KernelAI normOps βz βu aHat x

/-- The relation in the ML-DSA files' terms. -/
theorem kernel_iff (βz βu : ℕ) (aHat : TqMatrix p.k p.l) (x : RqVec p.l × RqVec p.k) :
    Kernel p βz βu aHat x ↔
      x ≠ 0 ∧ aHat * x.1 + x.2 = 0 ∧ polyVecBounded x.1 βz ∧ polyVecBounded x.2 βu :=
  Iff.rfl

/-! ### The key-generation form -/

variable (prims : Primitives p)

/-- **The matrix of key generation** at the seed `ξ`: `ExpandA` of the public seed `ρ` of
`keyGenFromSeed p prims ξ`. -/
def keyGenMatrix (ξ : Bytes 32) : TqMatrix p.k p.l :=
  prims.expandA (keyGenFromSeed p prims ξ).1.rho

/-- `ρ` is the first output of the seed expansion `H(ξ ‖ k ‖ l, 128)`. -/
theorem keyGenMatrix_eq (ξ : Bytes 32) :
    keyGenMatrix p prims ξ = prims.expandA (prims.expandSeed ξ).1 :=
  rfl

/-- **A solution for the key-generation matrix** of the seed `ξ`. -/
abbrev KeyGenKernel (βz βu : ℕ) (ξ : Bytes 32) (x : RqVec p.l × RqVec p.k) : Prop :=
  Kernel p βz βu (keyGenMatrix p prims ξ) x

/-- **The key-generation-form Module-SIS win probability**: the seed `ξ` uniform and given to the
adversary, a win with a solution for `keyGenMatrix p prims ξ`. -/
noncomputable def keyGenMsisWinProb (βz βu : ℕ)
    (A : Bytes 32 → PMF (Option (RqVec p.l × RqVec p.k))) : ℝ≥0∞ :=
  winProb (KeyGenKernel p prims βz βu) A

/-- **The `n`-seed key-generation-form Module-SIS win probability**: `n` independent uniform seeds,
given together, a win with `(i, x)` for `x` a solution for the matrix of the seed `i`. -/
noncomputable def keyGenMsisMultiWinProb (βz βu n : ℕ)
    (A : (Fin n → Bytes 32) → PMF (Option (Fin n × (RqVec p.l × RqVec p.k)))) : ℝ≥0∞ :=
  winProb (multiValid (KeyGenKernel p prims βz βu) n) A

/-- **Hardness of the key-generation form for the class `𝒜`.** -/
def KeyGenMSISHard (βz βu : ℕ) (𝒜 : Set (Bytes 32 → PMF (Option (RqVec p.l × RqVec p.k))))
    (ε : ℝ≥0∞) : Prop :=
  Hard (KeyGenKernel p prims βz βu) 𝒜 ε

/-- **`n` seeds at most `n` times one**: the `n`-seed win probability of `A` is at most `n` times
the single-seed win probability of its guessing adversary. -/
theorem keyGenMsisMultiWinProb_le (βz βu : ℕ) {n : ℕ} [NeZero n]
    (A : (Fin n → Bytes 32) → PMF (Option (Fin n × (RqVec p.l × RqVec p.k)))) :
    keyGenMsisMultiWinProb p prims βz βu n A ≤ n * keyGenMsisWinProb p prims βz βu (guess A) :=
  multiWinProb_le_card_mul _ A

theorem keyGenMsisWinProb_mono {βz βu βz' βu' : ℕ} (hz : βz ≤ βz') (hu : βu ≤ βu')
    (A : Bytes 32 → PMF (Option (RqVec p.l × RqVec p.k))) :
    keyGenMsisWinProb p prims βz βu A ≤ keyGenMsisWinProb p prims βz' βu' A :=
  winProb_mono (fun _ _ h => h.mono hz hu) A

/-! ### MLWE against unrestricted tests -/

open Classical in
/-- **MLWE at a seed-derived secret is not hard for unrestricted tests**: if the secret law is
`g` of a uniform 32-byte seed, no `ε < 1/2` bounds the advantage of every `[0, 1]`-valued test
(`not_mlweHard_univ`, with `|supp| ≤ 256^32` and `|R_q^k| ≥ q^256`). -/
theorem not_mlweHard_univ_of_seed (hk : 0 < p.k) (g : Bytes 32 → RqVec p.l × RqVec p.k) {ε : ℝ}
    (hε : ε < 1 / 2) :
    ¬ MLWEHard ((PMF.uniformOfFintype (Bytes 32)).map g)
      (Set.univ : Set (TqMatrix p.k p.l → RqVec p.k → ℝ)) ε := by
  refine not_mlweHard_univ _ (hε.trans_le ?_)
  set S := (PMF.uniformOfFintype (Bytes 32)).map g
  have hsupp : (Finset.univ.filter fun s => S s ≠ 0).card ≤ 256 ^ 32 :=
    (card_filter_map_ne_zero_le _ g).trans (card_bytes 32).le
  have hvec : 2 * 256 ^ 32 ≤ Fintype.card (RqVec p.k) := by
    rw [card_rqVec]
    calc 2 * 256 ^ 32 ≤ modulus ^ ringDegree := by norm_num [modulus, ringDegree]
      _ ≤ (modulus ^ ringDegree) ^ p.k :=
          Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hk) _
  have hpos : (0 : ℝ) < Fintype.card (RqVec p.k) := by exact_mod_cast Fintype.card_pos
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hpos]
  have h1 : ((Finset.univ.filter fun s => S s ≠ 0).card : ℝ) ≤ 256 ^ 32 := by exact_mod_cast hsupp
  have h2 : (2 : ℝ) * 256 ^ 32 ≤ Fintype.card (RqVec p.k) := by exact_mod_cast hvec
  linarith

end GordieHowe.Lattice
