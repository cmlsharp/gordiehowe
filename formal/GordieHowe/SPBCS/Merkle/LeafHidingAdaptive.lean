-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.LeafHiding
public import GordieHowe.Foundations.ToMathlib.McDiarmid
public import GordieHowe.Model.QROM.Oracle
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.NARG.Encoding
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Leaf hiding against an adaptive choice of the columns

`leaf_hiding_one` bounds the distance of one leaf digest from uniform for a column fixed
before the random function `H` is drawn. When the column may depend on `H` (an adversary that
holds the whole function chooses the statement and the witness), the bound needed is on the
expected maximum over all columns. For a family `e c : N → X` of injective encodings indexed by a
finite set `C` of columns:

    E_H max_c tvDist (digestLaw H (e c)) uniform ≤ √(|Y| / |N|) / 2 + √(log |C| / (2 |N|))

(`expect_sup'_tvDist_digestLaw_le`). This is CY24 Claim 3.4.2 (p. 36: "Claim 3.4.1 considers the
expected statistical distance for a fixed query x (or even for an empty query). However, in some
settings the adversary can choose the query, in which case we wish to consider the maximum
expected statistical distance over all queries"), which gives `2^(-(s-σ)/2) + √n · 2^(-s/2)`
for `n`-bit queries, `s`-bit salts and `σ`-bit outputs. The proof is CY24's: the distance for one
column changes by at most `1 / |N|` when `H` changes at one point of that column's encodings and
not at all elsewhere (`abs_tvDist_digestLaw_update_sub_le`), so McDiarmid's inequality and the
maximal inequality apply (`expect_sup'_le_of_boundedDiff`), with mean bound `leaf_hiding_one`.

`expect_sup'_tvDist_digestLaw_fst_le` is the form for an oracle whose answers carry the digest as
their first component (`Out k e = Digest k × (Fin e → Byte)`), and
`expect_sup'_tvDist_digestLaw_bytes_le` the form with `k`-byte digests and `2k`-byte Merkle salts.

At the leaves of the compiled proof's Merkle trees (`Query.leaf ν c`, `leafEnc`): the leaf distance
of an oracle `leafDist h`, the maximum over the columns of the distance from uniform of a leaf
digest with a uniform Merkle salt, and its expectation over a uniform oracle `expect_leafDist_le`,
at most `leafBound k kN L`. This is the leaf-equivocation step of the witness-indistinguishability
argument.
-/

open Finset PMF Real
open scoped BigOperators

namespace GordieHowe.SPBCS

variable {X Y N C : Type*} [Fintype N] [Nonempty N]

section Update

variable [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **Bounded differences of one leaf's distance from uniform.** Changing `H` at one point `x`
moves `tvDist (digestLaw H e) uniform` by at most `1 / |N|` when `x` is an encoding `e ν`, and
not at all otherwise (`e` injective). -/
theorem abs_tvDist_digestLaw_update_sub_le [Nonempty Y] {e : N → X}
    (he : Function.Injective e) (H : X → Y) (x : X) (y : Y) :
    |tvDist (digestLaw (Function.update H x y) e) (uniformOfFintype Y) -
        tvDist (digestLaw H e) (uniformOfFintype Y)| ≤
      if ∃ ν, e ν = x then (Fintype.card N : ℝ)⁻¹ else 0 := by
  classical
  refine (abs_tvDist_sub_tvDist_le _ _ _).trans ((tvDist_map_map_le _ _ _).trans ?_)
  rw [toReal_toOuterMeasure_apply]
  simp only [toReal_uniformOfFintype_apply, Function.comp_apply, Set.mem_setOf_eq]
  split_ifs with hx
  · obtain ⟨ν₀, rfl⟩ := hx
    calc ∑ ν, (if Function.update H (e ν₀) y (e ν) ≠ H (e ν) then (Fintype.card N : ℝ)⁻¹ else 0)
        ≤ ∑ ν, (if ν = ν₀ then (Fintype.card N : ℝ)⁻¹ else 0) := by
          refine sum_le_sum fun ν _ => ?_
          by_cases hν : ν = ν₀
          · subst hν
            split_ifs <;> simp_all
          · rw [Function.update_of_ne (he.ne hν)]
            simp [hν]
      _ = _ := by simp
  · refine le_of_eq (sum_eq_zero fun ν _ => ?_)
    rw [Function.update_of_ne fun h => hx ⟨ν, h⟩]
    simp

/-- The squared bounded differences of one leaf sum to `1 / |N|`. -/
theorem sum_sq_ite_exists_eq [Fintype X] {e : N → X} (he : Function.Injective e) :
    ∑ x : X, (if ∃ ν, e ν = x then (Fintype.card N : ℝ)⁻¹ else 0) ^ 2 =
      (Fintype.card N : ℝ)⁻¹ := by
  classical
  have hcard : (univ.filter fun x : X => ∃ ν, e ν = x).card = Fintype.card N := by
    rw [show (univ.filter fun x : X => ∃ ν, e ν = x) = univ.image e from by ext; simp,
      card_image_of_injective _ he, card_univ]
  simp only [ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [← sum_filter, sum_const, hcard, nsmul_eq_mul]
  have hN : (Fintype.card N : ℝ) ≠ 0 := by simp
  field_simp

end Update

section Adaptive

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype C]
  [Nonempty C]

/-- **Leaf hiding against an adaptive column** (CY24 Claim 3.4.2, p. 36): for injective encodings
`e c` indexed by a finite set of columns `C`, the expected maximum over the columns of the distance
of the leaf digest law from uniform is at most `√(|Y| / |N|) / 2 + √(log |C| / (2 |N|))`. -/
theorem expect_sup'_tvDist_digestLaw_le {e : C → N → X} (he : ∀ c, Function.Injective (e c)) :
    𝔼[H ← (X → Y) : univ.sup' univ_nonempty
        (fun c => tvDist (digestLaw H (e c)) (uniformOfFintype Y))] ≤
      √(Fintype.card Y / Fintype.card N) / 2 +
        √(Real.log (Fintype.card C) / (2 * Fintype.card N)) := by
  have h := expect_sup'_le_of_boundedDiff (ι := X) (Ω := Y)
    (fun c H => tvDist (digestLaw H (e c)) (uniformOfFintype Y))
    (fun c x => if ∃ ν, e c ν = x then (Fintype.card N : ℝ)⁻¹ else 0)
    (fun c H x y => abs_tvDist_digestLaw_update_sub_le (he c) H x y)
    (fun c => leaf_hiding_one (he c)) (fun c => (sum_sq_ite_exists_eq (he c)).le)
  refine h.trans_eq ?_
  congr 2
  field_simp

/-- The digest components of a uniform function with values in a product are a uniform
function. -/
theorem expect_comp_fst {Z : Type*} [Fintype Z] [Nonempty Z] (F : (X → Y) → ℝ) :
    𝔼[H ← (X → Y × Z) : F (Prod.fst ∘ H)] = 𝔼[H ← (X → Y) : F H] := by
  rw [← Fintype.expect_equiv (Equiv.arrowProdEquivProdArrow X (fun _ => Y) (fun _ => Z)).symm
    (fun p => F p.1) (fun H => F (Prod.fst ∘ H)) fun p => rfl]
  rw [← Finset.univ_product_univ, Finset.expect_product' univ univ fun a _ => F a]
  simp

/-- **Leaf hiding against an adaptive column, digest in the first component**: the form of
`expect_sup'_tvDist_digestLaw_le` for an oracle `H : X → Y × Z` whose hash-role answer is its
first component (`Out.digest`). -/
theorem expect_sup'_tvDist_digestLaw_fst_le {Z : Type*} [Fintype Z] [Nonempty Z]
    {e : C → N → X} (he : ∀ c, Function.Injective (e c)) :
    𝔼[H ← (X → Y × Z) : univ.sup' univ_nonempty
        (fun c => tvDist (digestLaw (Prod.fst ∘ H) (e c)) (uniformOfFintype Y))] ≤
      √(Fintype.card Y / Fintype.card N) / 2 +
        √(Real.log (Fintype.card C) / (2 * Fintype.card N)) := by
  rw [expect_comp_fst (fun H => univ.sup' univ_nonempty
    fun c => tvDist (digestLaw H (e c)) (uniformOfFintype Y))]
  exact expect_sup'_tvDist_digestLaw_le he

/-- **Leaf hiding against an adaptive column, Merkle salts twice the digest length**: with `k`-byte
digests (`|Y| = 2^(8k)`) and `2k`-byte Merkle salts (`|N| = 2^(16k)`), the bound of
`expect_sup'_tvDist_digestLaw_fst_le` is `2^(-4k) / 2 + √(log |C| / (2 · 2^(16k)))`.

Hypotheses `hY` and `hN` fix the digest and salt lengths. -/
theorem expect_sup'_tvDist_digestLaw_bytes_le {Z : Type*} [Fintype Z] [Nonempty Z] {k : ℕ}
    (hY : Fintype.card Y = 2 ^ (8 * k)) (hN : Fintype.card N = 2 ^ (16 * k))
    {e : C → N → X} (he : ∀ c, Function.Injective (e c)) :
    𝔼[H ← (X → Y × Z) : univ.sup' univ_nonempty
        (fun c => tvDist (digestLaw (Prod.fst ∘ H) (e c)) (uniformOfFintype Y))] ≤
      ((2 : ℝ) ^ (4 * k))⁻¹ / 2 + √(Real.log (Fintype.card C) / (2 * 2 ^ (16 * k))) := by
  have h := expect_sup'_tvDist_digestLaw_fst_le (Y := Y) (Z := Z) he
  rwa [sqrt_card_div_card_of_bytes hY hN, hN, Nat.cast_pow, Nat.cast_ofNat] at h

end Adaptive

section Leaves

open GordieHowe.QROM

variable {k kN kS L e : ℕ}

/-! ### The leaves of the compiled proof's Merkle trees -/

/-- The encoding of a leaf with column `c` as a function of its Merkle salt. -/
def leafEnc (c : Bytes L) (ν : MerkleSalt kN) : Query k kN kS L := .leaf ν c

theorem leafEnc_injective (c : Bytes L) : Function.Injective (leafEnc (k := k) (kN := kN) (kS := kS) c) :=
  fun _ _ h => (Query.leaf.inj h).1

/-- The digest part of the oracle. -/
def digestOf (h : Query k kN kS L → Out k e) (q : Query k kN kS L) : Digest k := (h q).digest

/-- **The leaf distance of the oracle**: the largest distance from uniform, over all columns, of
the digest of a leaf with that column and a uniform Merkle salt. -/
noncomputable def leafDist (h : Query k kN kS L → Out k e) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun c : Bytes L =>
    PMF.tvDist (digestLaw (digestOf h) (leafEnc c)) (PMF.uniformOfFintype (Digest k))

theorem leafDist_nonneg (h : Query k kN kS L → Out k e) : 0 ≤ leafDist h :=
  (PMF.tvDist_nonneg _ _).trans (Finset.le_sup' (fun c : Bytes L =>
    PMF.tvDist (digestLaw (digestOf h) (leafEnc c)) (PMF.uniformOfFintype (Digest k)))
    (Finset.mem_univ ⟨0, Fin.elim0⟩))

/-! ### The leaf term -/

/-- **The leaf bound** at `k`-byte digests, `kN`-byte Merkle salts and leaves of at most `L` bytes
(CY24 Claim 3.4.2 at `t = ∞`): `√(2^(8k) / 2^(8kN)) / 2 + √(log |Bytes L| / (2 · 2^(8kN)))`. -/
noncomputable def leafBound (k kN L : ℕ) : ℝ :=
  √((2 : ℝ) ^ (8 * k) / 2 ^ (8 * kN)) / 2 +
    √(Real.log (Fintype.card (Bytes L)) / (2 * 2 ^ (8 * kN)))

theorem leafBound_nonneg {k kN L : ℕ} : 0 ≤ leafBound k kN L := by
  unfold leafBound
  positivity

/-- **The expected leaf distance** (CY24 Claim 3.4.2 at `t = ∞`, `kN`-byte Merkle salts, `k`-byte
digests): `𝔼_h leafDist h ≤ leafBound k kN L`. -/
theorem expect_leafDist_le :
    𝔼[h ← (Query k kN kS L → Out k e) : leafDist h] ≤ leafBound k kN L := by
  have hN : (Fintype.card (MerkleSalt kN) : ℝ) = 2 ^ (8 * kN) := by
    rw [show Fintype.card (MerkleSalt kN) = 2 ^ (8 * kN) from Out.card_digest]
    push_cast
    ring
  have hY : (Fintype.card (Digest k) : ℝ) = 2 ^ (8 * k) := by
    rw [Out.card_digest]
    push_cast
    ring
  have h := expect_sup'_tvDist_digestLaw_fst_le (X := Query k kN kS L) (Y := Digest k)
    (Z := Fin e → Byte) (C := Bytes L) (N := MerkleSalt kN) fun c => leafEnc_injective c
  rw [hN, hY] at h
  refine le_of_eq_of_le (Fintype.expect_equiv (Equiv.arrowCongr (Equiv.refl _) Out.equivProd)
    (fun h => leafDist h) _ fun h => rfl) h

/-! ### The oracle on query bits -/

/-- **The oracle on queries seen through a quantum oracle `H`**: query bits in, bytes out. -/
def chainOracle (H : Bits (queryBits k kN kS L) → XOut k e) : Query k kN kS L → Out k e :=
  fun q => outEquiv k e (H (Query.toBits q))

/-- **The encoding of the compiler's oracle into the quantum oracle**: each query written as its
bits (`Query.toBits`), each answer read through `outEquiv`. The programs of the compiler run against
the quantum oracle through it (`NARG.Prover.encode`, `NARG.Simulator.encode`). -/
def queryEncoding : NARG.OracleEncoding (Query k kN kS L) (Out k e) (Bits (queryBits k kN kS L))
    (XOut k e) :=
  ⟨Query.toBits, Query.toBits.injective, outEquiv k e⟩

/-- The oracle read off a quantum oracle through `queryEncoding` is `chainOracle`. -/
@[simp] theorem decode_queryEncoding (H : Bits (queryBits k kN kS L) → XOut k e) :
    (queryEncoding (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).decode H = chainOracle H :=
  rfl

/-- **The `xof` inputs of the Fiat–Shamir salt `σ`**, by key. -/
def xofEmb (σ : FiatShamirSalt kS) : Digest k ↪ Bits (queryBits k kN kS L) :=
  ⟨fun κ => Query.toBits (.xof κ σ), fun a b hab => (Query.xof.inj (Query.toBits.injective hab)).1⟩

/-- **The largest leaf distance of an oracle on query bits**: the largest distance from uniform,
over the column bytes, of the digest of one leaf with a uniform Merkle salt under `h`. -/
noncomputable def leafMax (h : Bits (queryBits k kN kS L) → Out k e) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun col : Bytes L =>
    PMF.tvDist (digestLaw (Out.digest ∘ h) fun ν : MerkleSalt kN => Query.toBits (.leaf ν col))
      (PMF.uniformOfFintype (Digest k))

/-- The digest law of one leaf is within `leafMax` of uniform. -/
theorem tvDist_digestLaw_le_leafMax (H : Bits (queryBits k kN kS L) → XOut k e) (col : Bytes L) :
    PMF.tvDist (digestLaw (Out.digest ∘ fun b => outEquiv k e (H b))
      fun ν : MerkleSalt kN => Query.toBits (.leaf ν col)) (PMF.uniformOfFintype (Digest k)) ≤
      leafMax (fun b => outEquiv k e (H b)) :=
  Finset.le_sup' (fun col : Bytes L =>
    PMF.tvDist (digestLaw (Out.digest ∘ fun b => outEquiv k e (H b))
      fun ν : MerkleSalt kN => Query.toBits (.leaf ν col)) (PMF.uniformOfFintype (Digest k)))
    (Finset.mem_univ col)

theorem leafMax_nonneg (H : Bits (queryBits k kN kS L) → XOut k e) :
    0 ≤ leafMax (fun b => outEquiv k e (H b)) :=
  (PMF.tvDist_nonneg _ _).trans (tvDist_digestLaw_le_leafMax H (⟨0, Fin.elim0⟩ : Bytes L))

open Classical in
/-- **The Merkle salt slot of a quantum-oracle input**: the Merkle salt of the `leaf` query it
encodes, `none` if it encodes no `leaf` query. -/
noncomputable def leafSaltOfBits (b : Bits (queryBits k kN kS L)) : Option (MerkleSalt kN) :=
  (Function.partialInv Query.toBits b).bind Query.leafSalt

theorem leafSaltOfBits_toBits (q : Query k kN kS L) :
    leafSaltOfBits (Query.toBits q) = q.leafSalt := by
  classical
  simp only [leafSaltOfBits]
  rw [Function.partialInv_left Query.toBits.injective]
  rfl

/-- The Merkle salt of the default leaf, read past the last leaf of a tree. -/
def defaultSalt : MerkleSalt kN := fun _ => 0

end Leaves

end GordieHowe.SPBCS
