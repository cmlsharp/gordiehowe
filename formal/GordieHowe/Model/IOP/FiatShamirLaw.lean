-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Laws of self-consistent choices

**The law of a self-consistent choice.** For coins `r` with any law, let `X r ρ` be what is
observed at the values `ρ`, and `fs r` a self-consistent choice of them (for a Fiat–Shamir run of
a prover, the challenges). If `fs r = ρ` holds exactly when a predicate `Q ρ` holds of `X r ρ`,
then (`map_fixedPoint_apply`)

    Pr_r[(X r (fs r), fs r) = (o, ρ)] = Pr_r[X r ρ = o] · 1[Q ρ o].

**Choices close to uniform.** When the choices over a uniform oracle are only dominated by
uniform values up to `η`, the distance between two fixed-point laws is on average at most the
uniform average of the distance between the observed data, plus `η`
(`GordieHowe.SPBCS.expect_tvDist_map_fixedPoint_le`). For witness indistinguishability of the compiled proof
this file also holds the adversary's choices (`GordieHowe.SPBCS.WIChoice`) and the salt term
`SPBCS.saltTerm k c = √(log c / (2 · 2^(8k)))`. The witness-indistinguishability argument is in the
paper's Appendix I.2, Completeness, zero knowledge and witness indistinguishability.
-/

namespace GordieHowe.IOP

open ProtocolSpec

/-! ### The law of a self-consistent choice -/

section FixedPoint

variable {R R₀ R₁ C O : Type*}

/-- **The fixed-point law.** Coins `r` with law `p`; `X r ρ` is what is observed at the
challenges `ρ`, and `fs r` is the challenge vector consistent with the coins, characterized by
`fs r = ρ ↔ Q ρ (X r ρ)`. The law of `(X r (fs r), fs r)` at `(o, ρ)` is the law of `X · ρ`
at `o` when `Q ρ o`, and zero otherwise. -/
theorem map_fixedPoint_apply (p : PMF R) (X : R → C → O) {fs : R → C} {Q : C → O → Prop}
    (hfs : ∀ r ρ, fs r = ρ ↔ Q ρ (X r ρ)) (o : O) (ρ : C) [Decidable (Q ρ o)] :
    p.map (fun r => (X r (fs r), fs r)) (o, ρ) = if Q ρ o then p.map (X · ρ) o else 0 := by
  have key : ∀ r, ((o, ρ) = (X r (fs r), fs r)) ↔ (Q ρ o ∧ o = X r ρ) := fun r => by
    constructor
    · intro h
      obtain ⟨ho, rfl⟩ := Prod.mk.inj h
      refine ⟨?_, ho⟩
      rw [ho]
      exact (hfs r (fs r)).1 rfl
    · rintro ⟨hq, rfl⟩
      rw [(hfs r ρ).2 hq]
  rw [PMF.map_apply]
  split_ifs with hq
  · rw [PMF.map_apply]
    refine tsum_congr fun r => ?_
    by_cases h : (o, ρ) = (X r (fs r), fs r)
    · rw [ite_eq_left h, ite_eq_left ((key r).1 h).2]
    · rw [ite_eq_right h, ite_eq_right fun h' => h ((key r).2 ⟨hq, h'⟩)]
  · exact (tsum_congr fun r => ite_eq_right fun h => hq ((key r).1 h).1).trans tsum_zero

end FixedPoint

end GordieHowe.IOP

namespace GordieHowe.SPBCS

open GordieHowe.IOP
open scoped ENNReal NNReal BigOperators

/-! ### Fixed-point laws at challenges close to uniform -/

section FixedPoint

/-- **An average along a map**: `∑' b, p.map f b * Φ b = ∑' a, p a * Φ (f a)`. -/
theorem tsum_map_apply_mul {α β : Type*} (p : PMF α) (f : α → β) (Φ : β → ℝ≥0∞) :
    ∑' b, p.map f b * Φ b = ∑' a, p a * Φ (f a) := by
  classical
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a) fun b hb => by simp [hb]]
  simp

/-- A uniform average of finite values, read in `ℝ`. -/
theorem toReal_tsum_uniformOfFintype_mul {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ≥0∞)
    (hf : ∀ a, f a ≠ ⊤) :
    (∑' a, PMF.uniformOfFintype α a * f a).toReal = 𝔼 a, (f a).toReal := by
  rw [tsum_fintype, ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hf a),
    Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_mul, PMF.toReal_uniformOfFintype_apply, inv_mul_eq_div]

/-- **The excess from event bounds**: if every event has probability under `p` at most its
probability under `q` plus `η`, the excess `∑' a, (p a - q a)` is at most `η` (at the event
`{a | q a < p a}`). -/
theorem tsum_tsub_le_of_toOuterMeasure_le {α : Type*} (p q : PMF α) {η : ℝ≥0∞}
    (h : ∀ s : Set α, p.toOuterMeasure s ≤ q.toOuterMeasure s + η) : ∑' a, (p a - q a) ≤ η := by
  classical
  set s : Set α := {a | q a < p a}
  have hs : ∑' a, (p a - q a) + q.toOuterMeasure s = p.toOuterMeasure s := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ s
    · have ha' : q a < p a := ha
      simp only [Set.indicator_of_mem ha]
      exact tsub_add_cancel_of_le ha'.le
    · have ha' : p a ≤ q a := not_lt.1 ha
      simp only [Set.indicator_of_notMem ha, add_zero]
      exact tsub_eq_zero_of_le ha'
  have hq : q.toOuterMeasure s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one q s)
  have hle := h s
  rw [← hs, add_comm (q.toOuterMeasure s) η] at hle
  exact (ENNReal.add_le_add_iff_right hq).1 hle

/-- **Averages under a law dominated by the uniform law up to `η`**: if every event on `F g`
for uniform `g` has probability at most its uniform probability plus `η`, then for `ψ` with values
in `[0, 1]` the average of `ψ (F g)` is at most the uniform average of `ψ` plus `η`. -/
theorem expect_comp_le_of_probUniform_le {G C : Type} [Fintype G] [Nonempty G] [Fintype C]
    [Nonempty C] (F : G → C) {η : ℝ≥0∞} (hη : η ≠ ⊤)
    (hdom : ∀ B : Set C, Pr[g ← G : F g ∈ B] ≤ Pr[ρ ← C : ρ ∈ B] + η) {ψ : C → ℝ}
    (hψ0 : ∀ ρ, 0 ≤ ψ ρ) (hψ1 : ∀ ρ, ψ ρ ≤ 1) :
    𝔼 g, ψ (F g) ≤ 𝔼 ρ, ψ ρ + η.toReal := by
  set ν := (PMF.uniformOfFintype G).map F
  set q := PMF.uniformOfFintype C
  have hex : ∑' ρ, (ν ρ - q ρ) ≤ η := tsum_tsub_le_of_toOuterMeasure_le ν q fun B => by
    rw [PMF.toOuterMeasure_map_apply]
    exact hdom B
  set Ψ : C → ℝ≥0∞ := fun ρ => ENNReal.ofReal (ψ ρ)
  have hΨ1 : ∀ ρ, Ψ ρ ≤ 1 := fun ρ => ENNReal.ofReal_le_one.2 (hψ1 ρ)
  have hle : ∑' ρ, ν ρ * Ψ ρ ≤ ∑' ρ, q ρ * Ψ ρ + ∑' ρ, (ν ρ - q ρ) := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun ρ => ?_
    calc ν ρ * Ψ ρ ≤ (q ρ + (ν ρ - q ρ)) * Ψ ρ := by gcongr; exact le_add_tsub
      _ = q ρ * Ψ ρ + (ν ρ - q ρ) * Ψ ρ := add_mul _ _ _
      _ ≤ q ρ * Ψ ρ + (ν ρ - q ρ) := by gcongr; exact mul_le_of_le_one_right' (hΨ1 ρ)
  have hreal : ∀ ρ, (Ψ ρ).toReal = ψ ρ := fun ρ => ENNReal.toReal_ofReal (hψ0 ρ)
  have hL : 𝔼 g, ψ (F g) = (∑' ρ, ν ρ * Ψ ρ).toReal := by
    rw [tsum_map_apply_mul, toReal_tsum_uniformOfFintype_mul _ fun g => ENNReal.ofReal_ne_top]
    exact Finset.expect_congr rfl fun g _ => (hreal (F g)).symm
  have hR : 𝔼 ρ, ψ ρ = (∑' ρ, q ρ * Ψ ρ).toReal := by
    rw [toReal_tsum_uniformOfFintype_mul _ fun g => ENNReal.ofReal_ne_top]
    exact Finset.expect_congr rfl fun ρ _ => (hreal ρ).symm
  have hqfin : ∑' ρ, q ρ * Ψ ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((ENNReal.tsum_le_tsum fun ρ => mul_le_of_le_one_right' (hΨ1 ρ)).trans_eq q.tsum_coe)
  rw [hL, hR, ← ENNReal.toReal_add hqfin hη]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hqfin, hη⟩) (hle.trans (add_le_add le_rfl hex))

open Classical in
/-- **Two fixed-point laws at challenges close to uniform.** Two provers with uniform coins
`c : Cn` reveal `X c ρ` and `X' c ρ` at the challenges `ρ`; at each value `g` of an oracle their
challenges `fs g c` and `fs' g c` are the self-consistent ones for one consistency relation
`Qg g` (`hfs`, `hfs'`), and for every fixed coins the first prover's challenges over uniform `g`
are dominated by uniform challenges up to `η` (`hdom`). Then the average over `g` of the distance
between the laws of (revealed data, challenges) is at most the average over uniform challenges of
the distance between the laws of the revealed data, plus `η`.

The distance at `g` is the average over the coins of `Φ (X c (fs g c), fs g c)`, where `Φ (o, ρ)`
is the fraction of the mass of `o` under the first law at `ρ` that exceeds the second
(`map_fixedPoint_apply`); averaging over `g` at fixed coins costs `η` (`hdom`,
`expect_comp_le_of_probUniform_le`), and the average of `Φ` at uniform challenges is the distance
of the revealed data. -/
theorem expect_tvDist_map_fixedPoint_le {G Cn C O : Type} [Fintype G] [Nonempty G] [Fintype Cn]
    [Nonempty Cn] [Fintype C] [Nonempty C] (X X' : Cn → C → O) (fs fs' : G → Cn → C)
    (Qg : G → C → O → Prop) (hfs : ∀ g c ρ, fs g c = ρ ↔ Qg g ρ (X c ρ))
    (hfs' : ∀ g c ρ, fs' g c = ρ ↔ Qg g ρ (X' c ρ)) {η : ℝ≥0∞} (hη : η ≠ ⊤)
    (hdom : ∀ c (B : Set C), Pr[g ← G : fs g c ∈ B] ≤ Pr[ρ ← C : ρ ∈ B] + η) :
    𝔼 g, PMF.tvDist ((PMF.uniformOfFintype Cn).map fun c => (X c (fs g c), fs g c))
        ((PMF.uniformOfFintype Cn).map fun c => (X' c (fs' g c), fs' g c)) ≤
      𝔼 ρ, PMF.tvDist ((PMF.uniformOfFintype Cn).map (X · ρ))
        ((PMF.uniformOfFintype Cn).map (X' · ρ)) + η.toReal := by
  set p := PMF.uniformOfFintype Cn
  let μ : C → PMF O := fun ρ => p.map (X · ρ)
  let μ' : C → PMF O := fun ρ => p.map (X' · ρ)
  let Φ : O × C → ℝ≥0∞ := fun a => (μ a.2 a.1 - μ' a.2 a.1) / μ a.2 a.1
  have hΦ1 : ∀ a, Φ a ≤ 1 := fun a =>
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact tsub_le_self)
  have hΦt : ∀ a, Φ a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.one_ne_top (hΦ1 a)
  have hmulΦ : ∀ a, μ a.2 a.1 * Φ a = μ a.2 a.1 - μ' a.2 a.1 := fun a => by
    by_cases h0 : μ a.2 a.1 = 0
    · simp [h0]
    · exact ENNReal.mul_div_cancel h0 (PMF.apply_ne_top _ _)
  let ψ : Cn → C → ℝ := fun c ρ => (Φ (X c ρ, ρ)).toReal
  have hψ0 : ∀ c ρ, 0 ≤ ψ c ρ := fun _ _ => ENNReal.toReal_nonneg
  have hψ1 : ∀ c ρ, ψ c ρ ≤ 1 := fun c ρ =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hΦ1 (X c ρ, ρ))
  have hA : ∀ g, PMF.tvDist (p.map fun c => (X c (fs g c), fs g c))
      (p.map fun c => (X' c (fs' g c), fs' g c)) = 𝔼 c, ψ c (fs g c) := fun g => by
    rw [PMF.tvDist_eq_toReal_tsum_tsub]
    have hpt : ∀ a, (p.map fun c => (X c (fs g c), fs g c)) a -
        (p.map fun c => (X' c (fs' g c), fs' g c)) a =
          (p.map fun c => (X c (fs g c), fs g c)) a * Φ a := by
      rintro ⟨o, ρ⟩
      rw [map_fixedPoint_apply p X (hfs g) o ρ, map_fixedPoint_apply p X' (hfs' g) o ρ]
      split_ifs
      · exact (hmulΦ (o, ρ)).symm
      · simp
    rw [tsum_congr hpt, tsum_map_apply_mul, toReal_tsum_uniformOfFintype_mul _ fun c => hΦt _]
  have hB : ∀ ρ, PMF.tvDist (μ ρ) (μ' ρ) = 𝔼 c, ψ c ρ := fun ρ => by
    rw [PMF.tvDist_eq_toReal_tsum_tsub]
    have hpt : ∀ o, μ ρ o - μ' ρ o = μ ρ o * Φ (o, ρ) := fun o => (hmulΦ (o, ρ)).symm
    rw [tsum_congr hpt]
    change (∑' o, (p.map (X · ρ)) o * Φ (o, ρ)).toReal = _
    rw [tsum_map_apply_mul, toReal_tsum_uniformOfFintype_mul _ fun c => hΦt _]
  have hC : ∀ c, 𝔼 g, ψ c (fs g c) ≤ 𝔼 ρ, ψ c ρ + η.toReal := fun c =>
    expect_comp_le_of_probUniform_le (fun g => fs g c) hη (hdom c) (hψ0 c) (hψ1 c)
  calc 𝔼 g, PMF.tvDist (p.map fun c => (X c (fs g c), fs g c))
        (p.map fun c => (X' c (fs' g c), fs' g c))
      = 𝔼 g, 𝔼 c, ψ c (fs g c) := Finset.expect_congr rfl fun g _ => hA g
    _ = 𝔼 c, 𝔼 g, ψ c (fs g c) := Finset.expect_comm _ _ _
    _ ≤ 𝔼 c, (𝔼 ρ, ψ c ρ + η.toReal) := Finset.expect_le_expect fun c _ => hC c
    _ = 𝔼 ρ, 𝔼 c, ψ c ρ + η.toReal := by
        rw [Finset.expect_add_distrib, Finset.expect_comm, Fintype.expect_const]
    _ = 𝔼 ρ, PMF.tvDist (μ ρ) (μ' ρ) + η.toReal := by
        congr 1
        exact Finset.expect_congr rfl fun ρ _ => (hB ρ).symm

end FixedPoint

/-! ### Witness indistinguishability: the adversary's choices and the salt term -/

/-- **A choice of a witness-indistinguishability adversary**: a statement and two witnesses for
it. -/
structure WIChoice (X W : Type) where
  /-- The statement. -/
  stmt : X
  /-- The witness answered in the experiment `D_0`. -/
  wit₀ : W
  /-- The witness answered in the experiment `D_1`. -/
  wit₁ : W

/-- **The salt term**: `√(log c / (2 · 2^(8k)))` for `c` choices of the adversary (its
statement and witness pairs, `WIAdversary.choices`) and `k`-byte Fiat–Shamir salts. -/
noncomputable def saltTerm (k c : ℕ) : ℝ := √(Real.log c / (2 * 2 ^ (8 * k)))

theorem saltTerm_nonneg (k c : ℕ) : 0 ≤ saltTerm k c := Real.sqrt_nonneg _

/-- The salt term grows with the number of choices (`Real.log 0 = 0`). -/
theorem saltTerm_mono (k : ℕ) {c c' : ℕ} (h : c ≤ c') : saltTerm k c ≤ saltTerm k c' := by
  have hlog : Real.log c ≤ Real.log c' := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · rw [Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg c'
    · exact Real.log_le_log (Nat.cast_pos.2 hc) (Nat.cast_le.2 h)
  unfold saltTerm
  gcongr

end GordieHowe.SPBCS
