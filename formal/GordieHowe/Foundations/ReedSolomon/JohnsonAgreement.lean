-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder
public import GordieHowe.Foundations.ReedSolomon.CorrelatedLine
public import GordieHowe.Foundations.ReedSolomon.RowDistance
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
public import GordieHowe.Headline

@[expose] public section

/-!
# Reed--Solomon affine agreement at list-decoding radius

This file is the bridge from the vendored Johnson-radius mutual correlated agreement (MCA)
results of ArkLib (`Vendor/rs-provenance.json`, ArkLib `ace55c3e`) to the local
`GordieHowe.RSCode` interface. It states the step that the extraction of `GordieHowe.Ligero.AgreementThreshold`
needs: for tableau rows `U 0, …, U R` (row `0` the low-degree-test mask `u0`) and
coefficients `r`, if `u0 + Σ r_i U_i` agrees with a degree-`< k` polynomial on a column set `D`
of at least `A` columns, then outside an exceptional set of coefficient vectors every row agrees
with a degree-`< k` polynomial on all of `D`.

The exceptional count comes from a line certificate (`LineCertificate`, ArkLib's
`LineExactAgreementBound`): at most `B` bad challenges per line gives at most
`B · |F| ^ R / (|F| - 1)` bad coefficient vectors, density `B / (|F| - 1)`, for every number of
rows. The certificates proved by ArkLib are `lineCertificate_weightedJohnson` (the weighted
Johnson certificate, exact rational count) and `lineCertificate_johnson` (closed-form Johnson
bound at agreement `(√ρ₋ + η) N`); at unique decoding, `lineCertificate_uniqueDecoding` gives the
count `N` from the vendored BCIKS20 correlated agreement (`GordieHowe.RSCode.CorrelatedLine.correlatedAgreement`).

The radius is stated as an integer agreement threshold `A`, as in the C++ verifier and in the
column counts of `GordieHowe.Ligero.AgreementThreshold`; ArkLib's real radius `γ` is `1 - A / N` here.
-/

namespace GordieHowe.RSCode

open Polynomial RSCode CoreDefinitions
open scoped Classical NNReal

section

variable {F : Type} [Field F] {R N : ℕ}

/-- The evaluation domain of `C` as an embedding, the form ArkLib's Reed--Solomon codes use. -/
def domain (C : RSCode F N) : Fin N ↪ F := ⟨C.D, C.D_injective⟩

@[simp] theorem domain_apply (C : RSCode F N) (j : Fin N) : domain C j = C.D j := rfl

/-- **Line certificate.** ArkLib's `LineExactAgreementBound` on the domain of `C`: for every pair
of words `u v` some set of at most `B` challenges is fixed, outside which every polynomial of
degree `< C.k` agreeing with `u + z v` on at least `A` columns is `P₀ + z P₁` with `P₀ P₁` of
degree `< C.k`, and its agreement set is exactly the common agreement set of `(P₀, P₁)` with
`(u, v)`. -/
abbrev LineCertificate (C : RSCode F N) (A : ℕ) (B : ℝ) : Prop :=
  ReedSolomon.LineExactAgreementBound (domain C) C.k A B

/-- Every row of `U` agrees with its polynomial in `fs`, of degree `< C.k`, on every column of
`D`. -/
structure RowsAgreeOn (C : RSCode F N) (U : Matrix F R N) (D : Finset (Fin N))
    (fs : Fin R → F[X]) : Prop where
  degree : ∀ i, (fs i).natDegree < C.k
  agree : ∀ i, ∀ j ∈ D, (fs i).eval (C.D j) = U i j

/-- ArkLib's affine generator `(1, r)` combines the rows as `U 0 + Σ r_i U (i + 1)`
(`GordieHowe.Ligero.AffineCodeTest.projection`). -/
theorem sum_affineSpaceGenerator_mul (U : Matrix F (R + 1) N) (r : Fin R → F) (j : Fin N) :
    ∑ i, AffineSpaceGenerator F R r i * U i j = U 0 j + ∑ i, r i * U i.succ j := by
  simp [AffineSpaceGenerator, Fin.sum_univ_succ]

/-- ArkLib's affine generator `(1, r)` combines polynomials as `fs 0 + Σ r_i fs (i + 1)`
(`GordieHowe.Ligero.AffineCodeTest.projectedPolynomial`). -/
theorem sum_affineSpaceGenerator_smul (fs : Fin (R + 1) → F[X]) (r : Fin R → F) :
    ∑ i, AffineSpaceGenerator F R r i • fs i = fs 0 + ∑ i, r i • fs i.succ := by
  simp [AffineSpaceGenerator, Fin.sum_univ_succ]

open ReedSolomon.HiddenDerivative in
/-- **The hypotheses of the weighted Johnson certificate at a height `H`** (paper
`lem:mca-certificate`), parameter facts about the numbers `N` (the block length), `D` (the degree
bound `k − 1`), `A` (the agreement threshold), `m` (the multiplicity), `B` (the jet cutoff) and `H`
(the height): a positive jet cutoff, the strict cutoff `D B < m A`, and the strict slot surplus
`N Σ_{b ≤ u} (m − b)(H + 1 − b) < Σ_{j ≤ B} (m A − D j)(H + 1 − j)` with `u = min B (m − 1)`
(ArkLib `johnsonWeightedRowSlots`, `johnsonWeightedSourceSlots`). The paper also assumes `m ≥ 1`,
which follows from the strict cutoff, and `H ≥ B`, which the argument does not use. -/
structure WeightedJohnsonSurplus (N D A m B H : ℕ) : Prop where
  /-- The jet cutoff is positive. -/
  one_le_B : 1 ≤ B
  /-- The strict cutoff `D B < m A`: every source width is positive. -/
  cutoff : D * B < m * A
  /-- The strict slot surplus at the height `H`. -/
  surplus : johnsonWeightedRowSlots N m B H < johnsonWeightedSourceSlots D A m B H

open ReedSolomon.HiddenDerivative in
/-- **A weighted Johnson certificate gives the hypotheses at its height**: ArkLib's certificate
(`IsJohnsonWeightedCertificate`, at the least height `H ≥ B` of positive slope) satisfies the
strict slot surplus at `H` (ArkLib `IsJohnsonWeightedCertificate.rowSlots_lt_sourceSlots`). -/
theorem weightedJohnsonSurplus_of_certificate {N D A m B H : ℕ}
    (hcert : IsJohnsonWeightedCertificate N D A m B H) : WeightedJohnsonSurplus N D A m B H where
  one_le_B := hcert.2.1
  cutoff := hcert.2.2.1
  surplus := hcert.rowSlots_lt_sourceSlots

open Classical ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential in
/-- **Weighted Johnson exact correlated agreement at any height with a surplus**: the argument of
ArkLib's `exists_weightedJohnson_line_exactCorrelatedPair` with its certificate replaced by the
hypotheses at the height `H` (`WeightedJohnsonSurplus`). ArkLib's symbolic certificate
(`exists_weighted_johnson_symbolic_certificate`) takes any height with a strict slot surplus; the
ordinary power equation (`exists_baseExceptional_ordinaryPowerEquation`) and the line transfer then
give one set of at most `johnsonWeightedRefinedExceptionCount n D A B H` challenges, chosen before
the challenge and the candidate, outside which every polynomial of degree at most `D` agreeing with
`f + z g` on at least `A` points has an exact correlated pair, over an arbitrary field. -/
theorem exists_line_exactCorrelatedPair_of_surplus {n D A m B H : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (hW : WeightedJohnsonSurplus n D A m B H) (hD : 1 ≤ D) (hDA : D + 1 ≤ A)
    (hAn : A ≤ n) (hB : B ≤ 2 * D + 1) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ johnsonWeightedRefinedExceptionCount n D A B H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  obtain ⟨cert⟩ := exists_weighted_johnson_symbolic_certificate (k := D + 1) hD hW.cutoff le_rfl
    (by simpa only [johnsonWeightedRowSlots, johnsonWeightedU, johnsonWeightedSourceSlots,
      johnsonSourceSlotCount] using hW.surplus) domain f g
  have hQ : cert.Q ≠ 0 := by
    intro hz
    apply (cert.specialization_sound (RingHom.id F) 0).1
    rw [hz, map_zero]
  obtain ⟨ex, hcard, hgood⟩ := exists_baseExceptional_ordinaryPowerEquation (ℓ := 1)
    domain ![f, g] cert.Q D H B (D + 1) A hQ (by omega) (by omega) (by omega) hDA
    cert.challengeDegree_le cert.jetDegree_le
  rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos n D 1 B H A (D + 1) hW.one_le_B,
    ordinaryUnifiedPowerFactorAt_succ_eq n D 1 B H A hDA hAn,
    ordinaryUnifiedPowerFactorRaw_one_eq_johnsonWeightedRefinedExceptionCount hB] at hcard
  refine ⟨ex, hcard, fun z hz P hdegree hagree ↦ ?_⟩
  have hsound := (cert.specialization_sound (RingHom.id F) z).2
    (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) P hdegree hagree
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have heval : Polynomial.eval₂RingHom (RingHom.id F) z = (Polynomial.aeval z).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  have hword : powerBatchedWord ![f, g] z = fun i ↦ f i + z * g i :=
    powerBatchedWord_pair_eq f g (RingHom.id F) z
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
    (hgood z hz P hdegree (by simpa only [heval, challengeSpecialization] using hsound)
      (by rwa [hword]))

open ReedSolomon.HiddenDerivative in
/-- **Paper `lem:mca-certificate`: the weighted Johnson line certificate at any height `H` with a
strict slot surplus.** For a code of dimension `D + 1 ≥ 2` at agreement threshold `D + 1 ≤ A ≤ N`,
a jet cutoff `1 ≤ B ≤ 2D + 1`, the strict cutoff `D B < m A` and the strict slot surplus at `H`
(`WeightedJohnsonSurplus`), the line certificate holds with the exact rational exception count
`johnsonWeightedRefinedExceptionCount N D A B H` (`E(n, k, A; m, B, H)` of the paper). There is no
field size or characteristic condition. -/
@[headline]
theorem lineCertificate_of_surplus (C : RSCode F N) {D A m B H : ℕ}
    (hW : WeightedJohnsonSurplus N D A m B H) (hk : C.k = D + 1) (hD : 1 ≤ D)
    (hDA : D + 1 ≤ A) (hAN : A ≤ N) (hB : B ≤ 2 * D + 1) :
    LineCertificate C A (johnsonWeightedRefinedExceptionCount N D A B H : ℝ) := by
  intro f g
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_line_exactCorrelatedPair_of_surplus (domain C) f g hW hD hDA hAN hB
  refine ⟨ex, by exact_mod_cast hcard, fun z hz P hP hagree => ?_⟩
  rw [hk] at hP ⊢
  obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP (by convert hagree)
  refine ⟨pair.1, pair.2, hp0, hp1, by simpa [ReedSolomon.correlatedPairSpecialization] using heq,
    ?_⟩
  rw [← hset]
  ext i
  simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

open ReedSolomon.HiddenDerivative in
/-- **Weighted Johnson line certificate** at ArkLib's least height (ArkLib
`IsJohnsonWeightedCertificate`): `lineCertificate_of_surplus` at the certificate's height
(`weightedJohnsonSurplus_of_certificate`). -/
theorem lineCertificate_weightedJohnson (C : RSCode F N) {D A m B H : ℕ}
    (hcert : IsJohnsonWeightedCertificate N D A m B H) (hk : C.k = D + 1) (hD : 1 ≤ D)
    (hDA : D + 1 ≤ A) (hAN : A ≤ N) (hB : B ≤ 2 * D + 1) :
    LineCertificate C A (johnsonWeightedRefinedExceptionCount N D A B H : ℝ) :=
  lineCertificate_of_surplus C (weightedJohnsonSurplus_of_certificate hcert) hk hD hDA hAN hB

/-- A line certificate with at most `B` exceptional challenges per line is one with at most
`B' ≥ B` (ArkLib `LineExactAgreementBound.mono`). -/
theorem LineCertificate.mono {C : RSCode F N} {A : ℕ} {B B' : ℝ} (h : LineCertificate C A B)
    (hB : B ≤ B') : LineCertificate C A B' :=
  ReedSolomon.LineExactAgreementBound.mono h hB

open ReedSolomon.HiddenDerivative in
/-- **A weighted Johnson line certificate with a natural exceptional count**: the line certificate
of `lineCertificate_weightedJohnson`, whose exact rational count is at most the natural `count`,
for a code of dimension `D + 1 ≥ 2` at agreement threshold `D + 1 ≤ A ≤ N` and a weighted Johnson
certificate `(m, B, H)` with jet cutoff `B ≤ 2D + 1`. Every hypothesis is arithmetic on the
numbers and `C.k`, so a configuration discharges them by kernel computation. -/
theorem lineCertificate_of_weightedJohnson (C : RSCode F N) {D A m B H count : ℕ}
    (hcert : IsJohnsonWeightedCertificate N D A m B H) (hk : C.k = D + 1) (hD : 1 ≤ D)
    (hDA : D + 1 ≤ A) (hAN : A ≤ N) (hB : B ≤ 2 * D + 1)
    (hcount : johnsonWeightedRefinedExceptionCount N D A B H ≤ count) :
    LineCertificate C A count :=
  (lineCertificate_weightedJohnson C hcert hk hD hDA hAN hB).mono (by exact_mod_cast hcount)

open ReedSolomon.HiddenDerivative in
/-- **Johnson line certificate** (ArkLib `exists_johnson_line_exactCorrelatedPair_ceil`). For a
code of dimension `D + 1 ≥ 2` with `D ≤ N - 2` and slack `η > 0`, at agreement threshold
`⌈(√ρ₋ + η) N⌉` (`johnsonAgreement N D η = √ρ₋ + η ≤ 1`) the line certificate holds with
`johnsonExceptionCount` exceptions. -/
theorem lineCertificate_johnson (C : RSCode F N) {D : ℕ} {eta : ℝ} (hk : C.k = D + 1)
    (hD : 1 ≤ D) (hDN : D ≤ N - 2) (heta : 0 < eta) (ha : johnsonAgreement N D eta ≤ 1) :
    LineCertificate C ⌈johnsonAgreement N D eta * N⌉₊
      (johnsonExceptionCount N D ⌈johnsonAgreement N D eta * N⌉₊ eta) := by
  intro f g
  obtain ⟨ex, hcard, hgood⟩ :=
    ReedSolomon.exists_johnson_line_exactCorrelatedPair_ceil (domain C) f g hD hDN heta ha
  refine ⟨ex, hcard, fun z hz P hP hagree => ?_⟩
  rw [hk] at hP ⊢
  obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP (by convert hagree)
  refine ⟨pair.1, pair.2, hp0, hp1, by simpa [ReedSolomon.correlatedPairSpecialization] using heq,
    ?_⟩
  rw [← hset]
  ext i
  simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

variable [Fintype F]

omit [Fintype F] in
/-- A word agreeing with a polynomial on at least `A` columns disagrees with it on at most
`N − A`. -/
theorem card_filter_ne_le_of_agreement (C : RSCode F N) {A : ℕ} (w : Fin N → F) (P : F[X])
    (h : A ≤ (ReedSolomon.polynomialAgreementSet (domain C) w P).card) :
    (Finset.univ.filter fun j => w j ≠ P.eval (C.D j)).card ≤ N - A := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun j => P.eval (C.D j) = w j)
  have hag : ReedSolomon.polynomialAgreementSet (domain C) w P =
      Finset.univ.filter fun j => P.eval (C.D j) = w j := by
    ext j
    rw [ReedSolomon.mem_polynomialAgreementSet, Finset.mem_filter, domain_apply]
    simp
  have hne : (Finset.univ.filter fun j => w j ≠ P.eval (C.D j)) =
      Finset.univ.filter fun j => ¬ P.eval (C.D j) = w j := by
    ext j; simp [eq_comm]
  rw [hag] at h
  rw [hne]
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  omega

/-- For a column where `(f, g)` differs from `(a, b)`, at most one `z` makes
`f + z g = a + z b` there. -/
theorem card_filter_line_eq_le_one {f g a b : F} (h : f ≠ a ∨ g ≠ b) :
    (Finset.univ.filter fun z : F => f + z * g = a + z * b).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun x hx y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  rcases h with h | h
  · by_cases hg : g = b
    · subst hg; exact absurd (add_right_cancel hx) h
    · have : (x - y) * (g - b) = 0 := by linear_combination hx - hy
      rcases mul_eq_zero.mp this with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd (sub_eq_zero.mp h0) hg
  · have : (x - y) * (g - b) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.mp this with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (sub_eq_zero.mp h0) h

/-- **Unique-decoding line certificate** (BCIKS20 Theorem 1.4 at unique decoding, through
`CorrelatedLine.correlatedAgreement`). At an agreement threshold `A` with `N ≤ A + e` (at
most `e` disagreements, `2e + k ≤ N`), the line certificate holds with at most `N` exceptional
challenges: if more than `N` challenges have a nearby polynomial, the rows have nearby polynomials
`(p, q)` off a set `S` of at most `e` columns, and each column of `S` makes at most one challenge
agree by cancellation; otherwise the challenges with a nearby polynomial are the exceptions. -/
theorem lineCertificate_uniqueDecoding (C : RSCode F N) {A : ℕ} (hA : N ≤ A + C.e) :
    LineCertificate C A N := by
  intro f g
  let G : Finset F := Finset.univ.filter fun z : F => ∃ p : F[X], p.natDegree < C.k ∧
    (Finset.univ.filter fun j => f j + z * g j ≠ p.eval (C.D j)).card ≤ C.e
  have hnear : ∀ z (P : F[X]),
      A ≤ (ReedSolomon.polynomialAgreementSet (domain C) (fun i => f i + z * g i) P).card →
      (Finset.univ.filter fun j => f j + z * g j ≠ P.eval (C.D j)).card ≤ C.e := fun z P h =>
    (card_filter_ne_le_of_agreement C _ P h).trans (by omega)
  have hdeg : ∀ P : F[X], P.degree < (C.k : WithBot ℕ) → P.natDegree < C.k := fun P hP => by
    by_cases h0 : P = 0
    · simp [h0, C.k_pos]
    · exact (natDegree_lt_iff_degree_lt h0).2 hP
  by_cases hG : G.card ≤ N
  · refine ⟨G, by exact_mod_cast hG, fun z hz P hP hag => absurd ?_ hz⟩
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨P, hdeg P hP, hnear z P hag⟩
  · obtain ⟨p, q, hp, hq, hS⟩ :=
      (CorrelatedLine.correlatedAgreement C f g (Nat.lt_of_not_ge hG)).witness
    let S := Finset.univ.filter fun j => f j ≠ p.eval (C.D j) ∨ g j ≠ q.eval (C.D j)
    let E : Finset F := S.biUnion fun j => Finset.univ.filter fun z : F =>
      f j + z * g j = p.eval (C.D j) + z * q.eval (C.D j)
    have hE : E.card ≤ N := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ j ∈ S, _ ≤ ∑ _j ∈ S, 1 := Finset.sum_le_sum fun j hj =>
            card_filter_line_eq_le_one (Finset.mem_filter.mp hj).2
        _ = S.card := by simp
        _ ≤ N := hS.trans (by have := C.radius; omega)
    refine ⟨E, by exact_mod_cast hE, fun z hz P hP hag => ?_⟩
    have hpq : (p + Polynomial.C z * q).natDegree < C.k :=
      (natDegree_add_le _ _).trans_lt (max_lt hp
        ((natDegree_C_mul_le _ _).trans_lt hq))
    have herr : (Finset.univ.filter fun j =>
        f j + z * g j ≠ (p + Polynomial.C z * q).eval (C.D j)).card ≤ C.e := by
      refine (Finset.card_le_card fun j hj => ?_).trans hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_add, eval_mul, eval_C] at hj ⊢
      by_contra hc
      push Not at hc
      exact hj (by rw [hc.1, hc.2])
    have heq : P = p + Polynomial.C z * q :=
      polynomial_unique_at C C.e C.radius (fun j => f j + z * g j) P _ (hdeg P hP) hpq
        (hnear z P hag) herr
    refine ⟨p, q, (degree_le_natDegree.trans_lt (by exact_mod_cast hp)),
      (degree_le_natDegree.trans_lt (by exact_mod_cast hq)), heq, ?_⟩
    ext j
    rw [ReedSolomon.mem_polynomialAgreementSet, ReedSolomon.mem_commonPolynomialAgreementSet]
    simp only [heq, eval_add, eval_mul, eval_C, domain_apply]
    constructor
    · intro h
      by_contra hc
      have hjS : j ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra h'
        push Not at h'
        exact hc ⟨h'.1.symm, h'.2.symm⟩
      exact hz (Finset.mem_biUnion.mpr ⟨j, hjS, by simp [← h]⟩)
    · rintro ⟨h1, h2⟩
      rw [h1, h2]

/-- **Density of an exceptional set**: a set of at most `B · |F| ^ R / (|F| - 1)` coefficient
vectors (the count of `exists_exceptional_rowsAgreeOn`) is at most a `B / (|F| - 1)` fraction of
all coefficient vectors, in the counting form of the round-by-round proofs
(`GordieHowe.IOP.card_le_iff_probUniform_le`). -/
theorem card_le_density {E : Finset (Fin R → F)} {B : ℝ≥0}
    (hE : (E.card : ℝ) ≤ B * (Fintype.card F : ℝ) ^ R / ((Fintype.card F : ℝ) - 1)) :
    (E.card : ℝ≥0) ≤ B / (Fintype.card F - 1) * Fintype.card (Fin R → F) := by
  have hF : (1 : ℝ≥0) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hF, Fintype.card_fun, Fintype.card_fin]
  rwa [div_mul_eq_mul_div]

/-- **Exact row agreement outside an exceptional set**. Given a line
certificate at agreement threshold `A ≥ C.k`, for every tableau `U` there is a set `E` of at most
`B · |F| ^ R / (|F| - 1)` coefficient vectors such that for `r ∉ E`: every polynomial `p` of
degree `< C.k` that agrees with `U 0 + Σ r_i U (i + 1)` on a column set `D` of at least `A`
columns is `fs 0 + Σ r_i fs (i + 1)` for polynomials `fs` of degree `< C.k` that agree with the
rows on all of `D`.

`E` depends on `U` only, not on `p` or `D`. This is ArkLib's
`exists_affine_exceptionalSet_full_agreement_of_exactLine` at radius `1 - A / N`; its side
condition `k ≤ N (1 - radius)` is `hkA`. -/
theorem exists_exceptional_rowsAgreeOn (C : RSCode F N) {A : ℕ} {B : ℝ}
    (hline : LineCertificate C A B) (hkA : C.k ≤ A) (U : Matrix F (R + 1) N) :
    ∃ E : Finset (Fin R → F),
      (E.card : ℝ) ≤ B * (Fintype.card F : ℝ) ^ R / ((Fintype.card F : ℝ) - 1) ∧
      ∀ r ∉ E, ∀ ⦃p : F[X]⦄ ⦃D : Finset (Fin N)⦄, p.natDegree < C.k → A ≤ D.card →
        (∀ j ∈ D, p.eval (C.D j) = U 0 j + ∑ i, r i * U i.succ j) →
        ∃ fs, RowsAgreeOn C U D fs ∧ p = fs 0 + ∑ i, r i • fs i.succ := by
  have hB : 0 ≤ B := by
    obtain ⟨ex, hex, -⟩ := hline 0 0
    exact (Nat.cast_nonneg _).trans hex
  have hF : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  by_cases hAN : A ≤ N
  swap
  · refine Exists.intro (∅ : Finset (Fin R → F)) (And.intro ?_ ?_)
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact div_nonneg (mul_nonneg hB (by positivity)) (by linarith)
    intro r _ p D _ hD _
    exact absurd (hD.trans (by simpa using D.card_le_univ)) hAN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast C.k_pos.trans_le (hkA.trans hAN)
  have hrad : (Fintype.card (Fin N) : ℝ) * (1 - (1 - A / N)) = A := by
    rw [Fintype.card_fin]
    field_simp
    ring
  obtain ⟨E, hE, hgood⟩ := ReedSolomon.exists_affine_exceptionalSet_full_agreement_of_exactLine
    (domain C) B hline (1 - A / N) (by rw [hrad, Nat.ceil_natCast])
    (by rw [hrad]; exact_mod_cast hkA) U
  refine ⟨E, hE, fun r hr p D hp hD hagree => ?_⟩
  have hdeg : p.degree < C.k := degree_le_natDegree.trans_lt (by exact_mod_cast hp)
  have hsub : D ⊆ Finset.univ.filter fun j =>
      p.eval (domain C j) = ∑ i, AffineSpaceGenerator F R r i * U i j := by
    intro j hj
    simp [sum_affineSpaceGenerator_mul, hagree j hj]
  obtain ⟨P₀, hP₀, hpeq, hiff⟩ := hgood r hr p hdeg (by
    rw [hrad]
    exact_mod_cast hD.trans (Finset.card_le_card hsub))
  refine ⟨P₀, ⟨fun i => ?_, fun i j hj => ?_⟩, hpeq.trans (sum_affineSpaceGenerator_smul P₀ r)⟩
  · by_cases h0 : P₀ i = 0
    · simp [h0, C.k_pos]
    · exact (natDegree_lt_iff_degree_lt h0).2 (hP₀ i)
  · simpa using (hiff j).1 (Finset.mem_filter.mp (hsub hj)).2 i

end

end GordieHowe.RSCode
