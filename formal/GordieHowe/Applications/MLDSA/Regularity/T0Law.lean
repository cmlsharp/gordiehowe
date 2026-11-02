-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.StandinError
public import GordieHowe.Applications.MLDSA.Regularity.T0Mgf
public import GordieHowe.Foundations.ToMathlib.AddHomExpect
public import GordieHowe.Foundations.ToMathlib.LayerCake

@[expose] public section

/-!
# The law of `t₀` under a uniform matrix, and its tail over keys

The key is `t = A s₁ + s₂` with `A = NTT⁻¹(Â)` uniform, and `t₀` is the low part of Power2Round
(FIPS 204 Algorithm 6 line 6, Algorithm 35). `S = ‖t₀‖₂² = ∑_j ‖t₀,j‖²` (`t0SqNorm`).

**Zero slots.** `zeroSlots s₁` is the set `Z(s₁)` of slots `j` (roots `r_j = ζ^(2j+1)` of
`X^256 + 1`, `SlotTransform.lean`) at which every component of `s₁` vanishes; `d = #Z(s₁)`.

**The top coefficients are uniform** (`expect_topCoeffs`). Every row of `A s₁` ranges over the
polynomials vanishing on `Z(s₁)` (`exists_sum_mul_eq`, slot by slot), and such a polynomial has
arbitrary top coefficients `c ≥ d`: `g = h - (h mod P)` with `P = ∏_{j ∈ Z} (X - r_j)` monic of
degree `d` (`exists_vanishing_top`). So `A ↦ (top coefficients of A s₁)` is an additive surjection
onto `Z_q^{k (256 - d)}` (`topCoeffs_surjective`) and sends the uniform `A` to the uniform law
(`expect_comp_of_surjective`).

**The exponential moment** (`expect_exp_t0SqNorm_le`): for `λ ≥ 0`,
`𝔼_Â exp(λ S) ≤ φ(λ)^(k (256 - d)) · exp(λ k d 4096²)` with `φ(λ) = 𝔼_{r ∈ Z_q} exp(λ x_r²)`
(`t0SqMgf`), `x_r` the low part of `r`. `t0ChordBound` bounds `φ` by the chord interpolant of
`y ↦ exp(λ' y)` at the nodes `m/8` (`t0SqMgf_le_t0ChordBound`, from `T0Mgf.lean`).

**Keys** (section `Keys`). `SecretCoeffs p` holds the coefficients of `(s₁, s₂)` in `[-η, η]`
(`EtaCoeff`, `card_etaCoeff`: `2η + 1` values), the range of `ExpandS` (FIPS 204 Algorithm 33);
`secretOfCoeffs` reads them as polynomials. For a uniform box secret and any set `D` of slots,
`Pr[D ⊆ Z(s₁)] ≤ (2η + 1)^(-ℓ #D)` (`expect_subset_secretZeroSlots_le`): a nonzero polynomial with
support below `#D` has fewer than `#D` roots (`eq_zero_of_low_of_vanishing`), so the top
`256 - #D` coefficients of a box polynomial vanishing on `D` determine it. Consequently
`𝔼 (1 + x)^d ≤ (1 + x (2η + 1)^(-ℓ))^256` for `x ≥ 0`
(`expect_one_add_pow_card_secretZeroSlots_le`) and
`Pr[d ≥ d₀] ≤ C(256, d₀) (2η + 1)^(-ℓ d₀)` (`expect_le_card_secretZeroSlots_le`).

**The layered tail** (`expect_expect_le_layers`, `expect_expect_le_layers_chord`). For a monotone
`f`, a grid `a_0 ≤ … ≤ a_N` with `a_N ≥ 256 k · 4096²` and bounds `f(a_i) ≤ U_i` with
`U_0 ≤ … ≤ U_N`,
`𝔼_{s, Â} f(S) ≤ U_0 + ∑_{i<N} (U_{i+1} - U_i) · exp(-λ_i a_i) · Φ_i^(256 k) ·
(1 + ((exp(λ_i 4096²)/Φ_i)^k - 1)/(2η + 1)^ℓ)^256` for rates `λ_i ≥ 0` and bounds
`φ(λ_i) ≤ Φ_i ≤ exp(λ_i 4096²)`: the layer-cake bound (`expect_le_layers_of_le`), Chernoff's
bound for each key (`expect_indicator_lt_t0SqNorm_le`), and the key average of its zero-slot
factor. The grid, the rates and `f` are parameters; `f` is meant to bound the inverse square of a
weight lower bound that decreases in `S`. With the chord bound `Φ_i = t0ChordBound λ'_i`, the
factor of layer `i` is `t0TailBound p λ'_i a_i`, bounded through rational bounds on `exp(λ'_i/8)`
by `t0TailBound_le_exp` (`t0ChordBound_eq_t0ChordPoly`).

**Per-component rates** (section `Rates`). `t0CompSqNorm t₀ m = ‖t₀,m‖₂²`, so
`S = ∑_m ‖t₀,m‖₂²` (`sum_t0CompSqNorm`). With a rate `λ_m ≥ 0` per component,
`𝔼_Â exp(∑_m λ_m ‖t₀,m‖₂²) ≤ ∏_m φ(λ_m)^(256 - d) exp(λ_m d 4096²)`
(`expect_exp_sum_mul_t0CompSqNorm_le`), and over keys, for `φ(λ_m) ≤ Φ_m ≤ exp(λ_m 4096²)`,
`𝔼_{s, Â} exp(∑_m λ_m ‖t₀,m‖₂²) ≤
(∏_m Φ_m)^256 (1 + (∏_m exp(λ_m 4096²)/Φ_m - 1)/(2η + 1)^ℓ)^256`
(`expect_expect_exp_sum_mul_t0CompSqNorm_le`; with the chord bound,
`expect_expect_exp_sum_mul_t0CompSqNorm_le_chord`). Chernoff's bound with the rate `λ + μ` on
one component and `λ` on the others gives the joint tail of `S` and that component
(`expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le`), and a union over the components
the joint tail of `S` and the largest component
(`expect_expect_indicator_le_t0SqNorm_and_exists_le_t0CompSqNorm_le`). The bound of one component
is `jointTailBound`, bounded through rational bounds on `exp(λ'/8)` and `exp((λ' + μ')/8)` by
`jointTailBound_le_exp`.
-/

open Finset Real Polynomial
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA

/-! ### Zero slots and polynomials with prescribed top coefficients -/

section Slots

variable {l : ℕ}

/-- **The zero slots of `s₁`**: the slots `j` (roots `r_j = ζ^(2j+1)` of `X^256 + 1`) at which
every component of `s₁` vanishes, `Z(s₁) = {j | ∀ b, ŝ₁,b(j) = 0}`. -/
def zeroSlots (s : Fin l → Rq) : Finset (Fin ringDegree) :=
  univ.filter fun j => ∀ b, slotEval (slotRoot j) (s b) = 0

/-- Evaluation at a root of `X^256 + 1` commutes with finite sums. -/
theorem slotEval_sum {r : Coeff} (hr : r ^ ringDegree = -1) {ι : Type*} (s : Finset ι)
    (f : ι → Rq) : slotEval r (∑ i ∈ s, f i) = ∑ i ∈ s, slotEval r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact slotEval_zero hr
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, ← ih]
    exact slotEval_add hr _ _

/-- **Every polynomial vanishing on the zero slots is an `R_q`-combination of `s₁`**: if
`ĝ(j) = 0` for every `j ∈ Z(s₁)`, then `g = ∑_b a_b s₁,b` for some `a`. At a slot off `Z(s₁)`
some `ŝ₁,b(j) ≠ 0`; put `â_b(j) = ĝ(j) / ŝ₁,b(j)` there and `0` elsewhere. -/
theorem exists_sum_mul_eq (s : Fin l → Rq) (g : Rq)
    (hg : ∀ j ∈ zeroSlots s, slotEval (slotRoot j) g = 0) :
    ∃ a : Fin l → Rq, ∑ b, a b * s b = g := by
  classical
  let v : Fin l → Fin ringDegree → Coeff := fun b j =>
    if h : ∃ b', slotEval (slotRoot j) (s b') ≠ 0 then
      (if b = h.choose then slotVec g j / slotEval (slotRoot j) (s b) else 0)
    else 0
  let a : Fin l → Rq := fun b => Function.surjInv slotVec_bijective.2 (v b)
  have ha : ∀ b, slotVec (a b) = v b := fun b => Function.surjInv_eq slotVec_bijective.2 (v b)
  refine ⟨a, slotVec_injective (funext fun j => ?_)⟩
  have hr := slotRoot_pow j
  simp only [slotVec]
  rw [slotEval_sum hr]
  simp_rw [slotEval_mul hr]
  have hav : ∀ b, slotEval (slotRoot j) (a b) = v b j := fun b => congrFun (ha b) j
  simp_rw [hav]
  by_cases h : ∃ b', slotEval (slotRoot j) (s b') ≠ 0
  · simp only [v, h, ↓reduceDIte, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' univ h.choose, slotVec]
    simp only [mem_univ, ↓reduceIte]
    exact div_mul_cancel₀ _ h.choose_spec
  · simp only [v, h, ↓reduceDIte, zero_mul, sum_const_zero]
    simp only [ne_eq, not_exists, not_not] at h
    exact (hg j (mem_filter.2 ⟨mem_univ _, h⟩)).symm

/-- The coefficient positions `c ≥ d`, the top `256 - d` coefficients. -/
def topPositions (d : ℕ) : Finset (Fin ringDegree) :=
  univ.filter fun c => d ≤ (c : ℕ)

/-- There are `256 - d` positions `c ≥ d`. -/
theorem card_topPositions (d : ℕ) : #(topPositions d) = ringDegree - d := by
  have h : (topPositions d).map Fin.valEmbedding = Finset.Ico d ringDegree := by
    ext c
    simp only [topPositions, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_Ico]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c.isLt⟩
    · rintro ⟨hc, hc'⟩
      exact ⟨⟨c, hc'⟩, hc, rfl⟩
  rw [← card_map Fin.valEmbedding, h, Nat.card_Ico]

/-- The polynomial `∑_{c < 256} g_c X^c` evaluates at `r` to `slotEval r` of the coefficient
vector. -/
theorem slotEval_polyOf_coeff {g : Coeff[X]} (hg : g.natDegree < ringDegree) (r : Coeff) :
    slotEval r (polyOf fun c => g.coeff c) = g.eval r := by
  rw [eval_eq_sum_range' hg, ← Fin.sum_univ_eq_sum_range, slotEval]
  simp only [polyOf_get]

/-- **Prescribed top coefficients on the zero slots' ideal**: for any finite set `Z` of slots and
any `u`, some `g ∈ R_q` vanishes at every slot of `Z` and has `g_c = u_c` for `c ≥ #Z`. Take
`h = ∑_c u_c X^c` and `g = h - (h mod P)` with `P = ∏_{j ∈ Z} (X - r_j)` monic of degree `#Z`. -/
theorem exists_vanishing_top (Z : Finset (Fin ringDegree)) (u : Fin ringDegree → Coeff) :
    ∃ g : Rq, (∀ j ∈ Z, slotEval (slotRoot j) g = 0) ∧
      ∀ c : Fin ringDegree, #Z ≤ (c : ℕ) → g.get c = u c := by
  classical
  set P : Coeff[X] := ∏ j ∈ Z, (X - C (slotRoot j))
  have hP : P.Monic := monic_prod_X_sub_C _ _
  have hPdeg : P.degree = #Z := by
    rw [degree_eq_natDegree hP.ne_zero, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  set h : Coeff[X] := ∑ c : Fin ringDegree, C (u c) * X ^ (c : ℕ)
  have hcoeff : ∀ c : Fin ringDegree, h.coeff c = u c := fun c => by
    simp only [h, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single c (fun c' _ hc' => by
      simp only [mul_ite, mul_one, mul_zero]
      exact ite_eq_right_iff.2 fun hcc => absurd (Fin.ext hcc.symm) hc') (by simp)]
    simp
  have hhdeg : h.degree < ringDegree := by
    refine (degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun c _ => ?_
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast c.isLt
  have hZ : #Z ≤ ringDegree := by
    simpa using Finset.card_le_univ Z
  have hmod : (h %ₘ P).degree < #Z := hPdeg ▸ degree_modByMonic_lt h hP
  set g0 := h - h %ₘ P
  have hg0deg : g0.natDegree < ringDegree := by
    by_cases h0 : g0 = 0
    · rw [h0, natDegree_zero]
      norm_num [ringDegree]
    refine (natDegree_lt_iff_degree_lt h0).2 ?_
    refine (degree_sub_le _ _).trans_lt (max_lt hhdeg ?_)
    exact hmod.trans_le (by exact_mod_cast hZ)
  refine ⟨polyOf fun c => g0.coeff c, fun j hj => ?_, fun c hc => ?_⟩
  · rw [slotEval_polyOf_coeff hg0deg]
    have hg0 : g0 = P * (h /ₘ P) := by
      have := modByMonic_add_div h P
      simp only [g0]
      rw [sub_eq_iff_eq_add', this]
    rw [hg0, eval_mul, eval_prod, Finset.prod_eq_zero hj (by simp), zero_mul]
  · rw [polyOf_get]
    simp only [g0, coeff_sub, hcoeff]
    rw [coeff_eq_zero_of_degree_lt (hmod.trans_le (by exact_mod_cast hc)), sub_zero]

end Slots

/-! ### The top coefficients of `A s₁` are uniform -/

section Uniform

variable {k l : ℕ}

/-- The index set of the top `256 - d` coefficients of every component of `R_q^k`. -/
def topIndex (k d : ℕ) : Finset (Fin k × Fin ringDegree) :=
  univ ×ˢ topPositions d

/-- There are `k (256 - d)` top coefficients. -/
theorem card_topIndex (k d : ℕ) : #(topIndex k d) = k * (ringDegree - d) := by
  rw [topIndex, card_product, card_univ, Fintype.card_fin, card_topPositions]

/-- **The top coefficients of `A s₁`**: coefficient `c ≥ d` of component `i` of `∑_b A_{ib} s₁,b`. -/
noncomputable def topCoeffs (s : Fin l → Rq) (d : ℕ) (A : Fin k → Fin l → Rq) : topIndex k d → Coeff :=
  fun x => (∑ b, A x.1.1 b * s b).get x.1.2

/-- The top coefficients of `A s₁` are additive in `A`. -/
theorem topCoeffs_add (s : Fin l → Rq) (d : ℕ) (A B : Fin k → Fin l → Rq) :
    topCoeffs s d (A + B) = topCoeffs s d A + topCoeffs s d B := by
  funext x
  have h : ∑ b, (A + B) x.1.1 b * s b = ∑ b, A x.1.1 b * s b + ∑ b, B x.1.1 b * s b :=
    (Finset.sum_congr rfl fun b _ => rq_add_mul _ _ _).trans Finset.sum_add_distrib
  change (∑ b, (A + B) x.1.1 b * s b).get x.1.2 = (∑ b, A x.1.1 b * s b).get x.1.2 +
    (∑ b, B x.1.1 b * s b).get x.1.2
  rw [h]
  exact map_add (getHom x.1.2) _ _

/-- **The top `256 - d` coefficients of `A s₁` take every value**, for `d = #Z(s₁)`: each row of
`A s₁` ranges over all polynomials vanishing on `Z(s₁)` (`exists_sum_mul_eq`), and those have
arbitrary top coefficients (`exists_vanishing_top`). -/
theorem topCoeffs_surjective (s : Fin l → Rq) :
    Function.Surjective (topCoeffs (k := k) s #(zeroSlots s)) := by
  classical
  intro u
  have hrow : ∀ i : Fin k, ∃ a : Fin l → Rq, ∀ (c : Fin ringDegree)
      (hc : #(zeroSlots s) ≤ (c : ℕ)),
      (∑ b, a b * s b).get c = u ⟨(i, c), mem_product.2 ⟨mem_univ _,
        mem_filter.2 ⟨mem_univ _, hc⟩⟩⟩ := by
    intro i
    obtain ⟨g, hg0, hgtop⟩ := exists_vanishing_top (zeroSlots s) fun (c : Fin ringDegree) =>
      if hc : #(zeroSlots s) ≤ (c : ℕ) then u ⟨(i, c), mem_product.2 ⟨mem_univ _,
        mem_filter.2 ⟨mem_univ _, hc⟩⟩⟩ else 0
    obtain ⟨a, ha⟩ := exists_sum_mul_eq s g hg0
    refine ⟨a, fun c hc => ?_⟩
    rw [ha, hgtop c hc]
    simp only [hc, ↓reduceDIte]
  choose A hA using hrow
  refine ⟨A, funext fun x => ?_⟩
  obtain ⟨⟨i, c⟩, hx⟩ := x
  exact hA i c (mem_filter.1 (mem_product.1 hx).2).2

/-- **The top coefficients of `A s₁` under a uniform `A` are uniform**: for every
`F`, `𝔼_A F(top(A s₁)) = 𝔼_u F(u)`, with `top` the coefficients `c ≥ #Z(s₁)` of every row. -/
theorem expect_topCoeffs (s : Fin l → Rq) (F : (topIndex k #(zeroSlots s) → Coeff) → ℝ) :
    𝔼 A : Fin k → Fin l → Rq, F (topCoeffs s #(zeroSlots s) A) = 𝔼 u, F u :=
  GordieHowe.expect_comp_of_surjective (topCoeffs_add s _) (topCoeffs_surjective s) F

end Uniform

/-! ### The exponential moment of `‖t₀‖₂²` -/

section Mgf

variable {p : Params}

attribute [local instance] concreteNTTRingOps

/-- **The exponential moment of one squared `t₀` coefficient of a uniform key**:
`φ(λ) = 𝔼_{r ∈ Z_q} exp(λ x_r²)` with `x_r` the low part of Power2Round (FIPS 204 Algorithm 35)
of `r`. -/
noncomputable def t0SqMgf (lam : ℝ) : ℝ :=
  𝔼 r : Coeff, exp (lam * ((power2RoundLowCoeff r : ℤ) : ℝ) ^ 2)

/-- Translation leaves `φ` unchanged: `𝔼_r exp(λ x_{r + a}²) = φ(λ)`. -/
theorem expect_exp_sq_add_eq_t0SqMgf (lam : ℝ) (a : Coeff) :
    𝔼 r : Coeff, exp (lam * ((power2RoundLowCoeff (r + a) : ℤ) : ℝ) ^ 2) = t0SqMgf lam :=
  Fintype.expect_equiv (Equiv.addRight a) _ _ fun _ => rfl

/-- `‖t₀‖₂²` of the key `keyOf sk₀ τ` through the coefficients of `t = τ + s₂`. -/
theorem t0SqNorm_keyOf (sk₀ : SecretKey p) (τ : Fin p.k → Rq) :
    t0SqNorm (keyOf sk₀ τ).t0 = ∑ x : Fin p.k × Fin ringDegree,
      ((power2RoundLowCoeff ((τ x.1).get x.2 + (sk₀.s2.get x.1).get x.2) : ℤ) : ℝ) ^ 2 := by
  have h : (keyOf sk₀ τ).t0 = GordieHowe.MLDSA.t0Of p (Vector.ofFn τ + sk₀.s2) := rfl
  rw [h, t0SqNorm_edgeT0Of]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rqVecCoeffs_apply, rqVec_add_get_get, Vector.get_ofFn]

/-- `x_r² ≤ 4096²` for the low part `x_r` of Power2Round. -/
theorem power2RoundLowCoeff_sq_le (r : Coeff) : ((power2RoundLowCoeff r : ℤ) : ℝ) ^ 2 ≤ 4096 ^ 2 := by
  have h : |((power2RoundLowCoeff r : ℤ) : ℝ)| ≤ 4096 := by exact_mod_cast abs_power2RoundLowCoeff_le r
  nlinarith [abs_nonneg ((power2RoundLowCoeff r : ℤ) : ℝ), sq_abs ((power2RoundLowCoeff r : ℤ) : ℝ)]

/-- **The exponential moment of `‖t₀‖₂²` under a uniform matrix**: for `λ ≥ 0` and every key,
with `d = #Z(s₁)` the number of zero slots of `s₁`,
`𝔼_Â exp(λ ‖t₀‖₂²) ≤ φ(λ)^(k (256 - d)) · exp(λ k d 4096²)`, where `t₀` is the low part of
`t = A s₁ + s₂`, `A = NTT⁻¹(Â)`. The top `256 - d` coefficients of every row of `A s₁` are
uniform and independent (`expect_topCoeffs`), and each other coefficient has `x² ≤ 4096²`. -/
theorem expect_exp_t0SqNorm_le (sk₀ : SecretKey p) {lam : ℝ} (hlam : 0 ≤ lam) :
    𝔼 aHat : TqMatrix p.k p.l, exp (lam * t0SqNorm
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0) ≤
      t0SqMgf lam ^ (p.k * (ringDegree - #(zeroSlots fun b => sk₀.s1.get b))) *
        exp (lam * (p.k * #(zeroSlots fun b => sk₀.s1.get b) * 4096 ^ 2)) := by
  classical
  have := concreteNTTRingLaws
  set s : Fin p.l → Rq := fun b => sk₀.s1.get b
  set d := #(zeroSlots s)
  set T := topIndex p.k d
  set v : (Fin p.k → Fin p.l → Rq) → Fin p.k × Fin ringDegree → ℝ := fun A x =>
    ((power2RoundLowCoeff ((∑ b, A x.1 b * s b).get x.2 + (sk₀.s2.get x.1).get x.2) : ℤ) : ℝ) ^ 2
  set G : T → Coeff → ℝ := fun y r =>
    exp (lam * ((power2RoundLowCoeff (r + (sk₀.s2.get y.1.1).get y.1.2) : ℤ) : ℝ) ^ 2)
  set C := exp (lam * (p.k * d * 4096 ^ 2))
  have hd : d ≤ ringDegree := by simpa [d] using Finset.card_le_univ (zeroSlots s)
  have hTc : #Tᶜ = p.k * d := by
    rw [card_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, card_topIndex]
    rw [Nat.mul_sub, Nat.sub_sub_self (Nat.mul_le_mul_left _ hd)]
  -- Pointwise: the coefficients off `T` contribute at most `4096²` each.
  have hpt : ∀ A, exp (lam * ∑ x, v A x) ≤ C * ∏ y : T, G y (topCoeffs s d A y) := by
    intro A
    rw [← Finset.sum_add_sum_compl T, mul_add, exp_add, mul_comm]
    have hoff : ∑ x ∈ Tᶜ, v A x ≤ p.k * d * 4096 ^ 2 := by
      calc ∑ x ∈ Tᶜ, v A x ≤ ∑ _x ∈ Tᶜ, (4096 : ℝ) ^ 2 :=
            Finset.sum_le_sum fun x _ => power2RoundLowCoeff_sq_le _
        _ = p.k * d * 4096 ^ 2 := by rw [sum_const, hTc, nsmul_eq_mul]; push_cast; ring
    gcongr
    · exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hoff hlam)
    · rw [Finset.mul_sum, exp_sum, ← Finset.prod_coe_sort T]
      exact le_of_eq rfl
  have hkey : ∀ aHat : TqMatrix p.k p.l,
      t0SqNorm (keyOf sk₀ (keyMap s (matOfHat aHat))).t0 = ∑ x, v (matOfHat aHat) x := fun aHat =>
    t0SqNorm_keyOf sk₀ _
  calc 𝔼 aHat : TqMatrix p.k p.l, exp (lam * t0SqNorm (keyOf sk₀ (keyMap s (matOfHat aHat))).t0)
      = 𝔼 A : Fin p.k → Fin p.l → Rq, exp (lam * ∑ x, v A x) := by
        simp_rw [hkey]
        exact Fintype.expect_bijective _ matOfHat_bijective _ _ fun _ => rfl
    _ ≤ 𝔼 A : Fin p.k → Fin p.l → Rq, C * ∏ y : T, G y (topCoeffs s d A y) :=
        Finset.expect_le_expect fun A _ => hpt A
    _ = C * 𝔼 u : T → Coeff, ∏ y : T, G y (u y) := by
        rw [← Finset.mul_expect, expect_topCoeffs s (fun u => ∏ y : T, G y (u y))]
    _ = C * t0SqMgf lam ^ (p.k * (ringDegree - d)) := by
        rw [PMF.expect_prod_apply G]
        simp_rw [G, expect_exp_sq_add_eq_t0SqMgf]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, card_topIndex]
    _ = _ := mul_comm _ _

end Mgf

/-! ### Zero slots of a uniform box secret -/

section Keys

/-- A coefficient vector of degree below `#D` vanishing at the roots `r_j`, `j ∈ D`, is zero
(a nonzero polynomial of degree below `#D` has fewer than `#D` roots). -/
theorem eq_zero_of_low_of_vanishing (D : Finset (Fin ringDegree)) (w : Fin ringDegree → Coeff)
    (hlow : ∀ c : Fin ringDegree, #D ≤ (c : ℕ) → w c = 0)
    (hv : ∀ j ∈ D, ∑ c, w c * slotRoot j ^ (c : ℕ) = 0) : w = 0 := by
  classical
  set P : Coeff[X] := ∑ c : Fin ringDegree, C (w c) * X ^ (c : ℕ)
  have hcoeff : ∀ c : Fin ringDegree, P.coeff c = w c := fun c => by
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single c (fun c' _ hc' => by
      simp only [mul_ite, mul_one, mul_zero]
      exact ite_eq_right_iff.2 fun hcc => absurd (Fin.ext hcc.symm) hc') (by simp)]
    simp
  have hcoeff' : ∀ m : ℕ, ringDegree ≤ m → P.coeff m = 0 := fun m hm => by
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    refine Finset.sum_eq_zero fun c _ => ?_
    have : m ≠ (c : ℕ) := by have := c.isLt; omega
    simp [this]
  have hdeg : P.degree < #D := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    by_cases hm' : m < ringDegree
    · rw [show m = ((⟨m, hm'⟩ : Fin ringDegree) : ℕ) from rfl, hcoeff]
      exact hlow _ (by exact_mod_cast hm)
    · exact hcoeff' m (not_lt.1 hm')
  have hP : P = 0 := by
    by_contra hP0
    refine hP0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (f := fun j : D => slotRoot j) (fun j j' h => Subtype.ext (slotRoot_injective h))
      (fun j => ?_) ?_)
    · rw [eval_finsetSum]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      exact hv j j.2
    · rw [Fintype.card_coe]
      exact (natDegree_lt_iff_degree_lt hP0).2 hdeg
  funext c
  rw [← hcoeff c, hP, coeff_zero, Pi.zero_apply]

/-- The coefficients of absolute value at most `η`: the alphabet of `ExpandS`
(FIPS 204 Algorithm 33, `RejBoundedPoly` outputs coefficients in `[-η, η]`). -/
abbrev EtaCoeff (η : ℕ) := {x : Coeff // (LatticeCrypto.centeredRepr x).natAbs ≤ η}

/-- `0 ∈ [-η, η]`. -/
instance (η : ℕ) : Nonempty (EtaCoeff η) :=
  ⟨⟨0, by rw [LatticeCrypto.centeredRepr_eq_valMinAbs, ZMod.valMinAbs_zero]; simp⟩⟩

/-- `[-η, η]` has `2η + 1` elements modulo `q` when `2η < q`. -/
theorem card_etaCoeff {η : ℕ} (hη : 2 * η < modulus) : Fintype.card (EtaCoeff η) = 2 * η + 1 := by
  classical
  have himg : (univ.filter fun x : Coeff => (LatticeCrypto.centeredRepr x).natAbs ≤ η) =
      (Finset.Icc (-(η : ℤ)) η).image fun z : ℤ => (z : Coeff) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_Icc]
    constructor
    · intro hx
      refine ⟨LatticeCrypto.centeredRepr x, ?_, ?_⟩
      · constructor <;> omega
      · rw [LatticeCrypto.centeredRepr_eq_valMinAbs, ZMod.coe_valMinAbs]
    · rintro ⟨z, hz, rfl⟩
      rw [LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le z (b := η) (by omega) hη]
      omega
  rw [Fintype.card_subtype, himg, card_image_of_injOn]
  · simp only [Int.card_Icc]
    omega
  · intro z hz z' hz' h
    have hz1 : z.natAbs ≤ η := by
      have := Finset.mem_coe.1 hz
      rw [mem_Icc] at this
      omega
    have hz2 : z'.natAbs ≤ η := by
      have := Finset.mem_coe.1 hz'
      rw [mem_Icc] at this
      omega
    have h1 := LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le z hz1 hη
    have h2 := LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le z' hz2 hη
    simp only at h
    rw [← h1, ← h2, h]

/-- **A box polynomial vanishes on `D` with probability at most `#A^-#D`**: for coefficients
`f` uniform on `A^256`, `A ↪ Z_q`, `Pr[f(r_j) = 0 ∀ j ∈ D] ≤ #A^-#D`. The top `256 - #D`
coefficients determine the rest (`eq_zero_of_low_of_vanishing`), so at most `#A^(256 - #D)` of
the `#A^256` coefficient vectors vanish on `D`. -/
theorem expect_vanishing_le_of_injective {A : Type*} [Fintype A] [Nonempty A] {ι : A → Coeff}
    (hι : Function.Injective ι) (D : Finset (Fin ringDegree)) :
    𝔼 f : Fin ringDegree → A,
        (if ∀ j ∈ D, ∑ c, ι (f c) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) ≤
      ((Fintype.card A : ℝ)⁻¹) ^ #D := by
  classical
  have hD : #D ≤ ringDegree := by simpa using Finset.card_le_univ D
  have hinj : ∀ f g : Fin ringDegree → A,
      (∀ j ∈ D, ∑ c, ι (f c) * slotRoot j ^ (c : ℕ) = 0) →
      (∀ j ∈ D, ∑ c, ι (g c) * slotRoot j ^ (c : ℕ) = 0) →
      (fun c : topPositions #D => f c) = (fun c : topPositions #D => g c) → f = g := by
    intro f g hf hg hfg
    have hfg' := eq_zero_of_low_of_vanishing D (fun c => ι (f c) - ι (g c)) (fun c hc => by
      have := congrFun hfg ⟨c, mem_filter.2 ⟨mem_univ _, hc⟩⟩
      simp only at this
      rw [this, sub_self]) (fun j hj => by
      simp only [sub_mul, Finset.sum_sub_distrib, hf j hj, hg j hj, sub_self])
    funext c
    exact hι (sub_eq_zero.1 (congrFun hfg' c))
  have hcard : #(univ.filter fun f : Fin ringDegree → A =>
      ∀ j ∈ D, ∑ c, ι (f c) * slotRoot j ^ (c : ℕ) = 0) ≤
      Fintype.card A ^ (ringDegree - #D) := by
    refine (Finset.card_le_card_of_injOn (t := univ)
      (fun f : Fin ringDegree → A => fun c : topPositions #D => f c)
      (fun f _ => Finset.mem_univ _) fun f hf g hg h => hinj f g ?_ ?_ h).trans ?_
    · exact (mem_filter.1 (mem_coe.1 hf)).2
    · exact (mem_filter.1 (mem_coe.1 hg)).2
    · rw [card_univ, Fintype.card_fun, Fintype.card_coe, card_topPositions]
  have hE : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  rw [Fintype.expect_eq_sum_div_card, ← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_le_iff₀ (by positivity), inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  calc _ ≤ (Fintype.card A : ℝ) ^ (ringDegree - #D) * (Fintype.card A : ℝ) ^ #D := by
        gcongr
        exact_mod_cast hcard
    _ = (Fintype.card A : ℝ) ^ ringDegree := by rw [← pow_add, Nat.sub_add_cancel hD]

/-- **The secrets of `ExpandS` as coefficient arrays**: the coefficients of `s₁ ∈ R_q^ℓ` and
`s₂ ∈ R_q^k`, each in `[-η, η]` (FIPS 204 Algorithm 33). -/
abbrev SecretCoeffs (p : Params) :=
  (Fin p.l → Fin ringDegree → EtaCoeff p.eta) × (Fin p.k → Fin ringDegree → EtaCoeff p.eta)

/-- The secret `(s₁, s₂)` with the coefficients `e`. -/
noncomputable def secretOfCoeffs {p : Params} (e : SecretCoeffs p) : RqVec p.l × RqVec p.k :=
  (Vector.ofFn fun m => polyOf fun c => (e.1 m c : Coeff),
    Vector.ofFn fun m => polyOf fun c => (e.2 m c : Coeff))

/-- A polynomial with coefficients in `[-η, η]` is `η`-bounded. -/
theorem polyBounded_polyOf {η : ℕ} (f : Fin ringDegree → EtaCoeff η) :
    polyBounded (polyOf fun c => (f c : Coeff)) η := by
  unfold polyBounded
  rw [polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
  intro i
  rw [polyOf_get]
  exact (f i).2

/-- **The secrets of coefficient arrays are `η`-bounded**. -/
theorem secretOfCoeffs_bounded {p : Params} (e : SecretCoeffs p) :
    polyVecBounded (secretOfCoeffs e).1 p.eta ∧ polyVecBounded (secretOfCoeffs e).2 p.eta :=
  ⟨Spec.polyVecBounded_ofFn fun _ => polyBounded_polyOf _,
    Spec.polyVecBounded_ofFn fun _ => polyBounded_polyOf _⟩

/-- The zero slots of the `s₁` of a coefficient array. -/
noncomputable abbrev secretZeroSlots {p : Params} (e : SecretCoeffs p) : Finset (Fin ringDegree) :=
  zeroSlots fun b => (secretOfCoeffs e).1.get b

/-- **A uniform box secret has `D ⊆ Z(s₁)` with probability at most `(#E^-ℓ)^#D`**, `E` the
alphabet `[-η, η]` (`#E = 2η + 1`, `card_etaCoeff`): each of the `ℓ` independent components
vanishes on `D` with probability at most `#E^-#D` (`expect_vanishing_le_of_injective`). -/
theorem expect_subset_secretZeroSlots_le {p : Params} (D : Finset (Fin ringDegree)) :
    𝔼 e : SecretCoeffs p, (if D ⊆ secretZeroSlots e then 1 else 0 : ℝ) ≤
      (((Fintype.card (EtaCoeff p.eta) : ℝ)⁻¹) ^ p.l) ^ #D := by
  have hind : ∀ e : SecretCoeffs p, (if D ⊆ secretZeroSlots e then 1 else 0 : ℝ) =
      ∏ b : Fin p.l, (if ∀ j ∈ D, ∑ c, ((e.1 b c : EtaCoeff p.eta) : Coeff) *
        slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) := by
    intro e
    rw [Finset.prod_boole]
    have hiff : D ⊆ secretZeroSlots e ↔ ∀ b : Fin p.l, ∀ j ∈ D,
        ∑ c, ((e.1 b c : EtaCoeff p.eta) : Coeff) * slotRoot j ^ (c : ℕ) = 0 := by
      simp only [secretZeroSlots, zeroSlots, subset_iff, mem_filter, mem_univ, true_and,
        secretOfCoeffs, Vector.get_ofFn, slotEval, polyOf_get]
      exact ⟨fun h b j hj => h hj b, fun h j hj b => h b j hj⟩
    simp only [mem_univ, true_implies, hiff]
  simp_rw [hind]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp only [Finset.expect_const Finset.univ_nonempty]
  rw [PMF.expect_prod_apply (fun (b : Fin p.l) (f : Fin ringDegree → EtaCoeff p.eta) =>
    (if ∀ j ∈ D, ∑ c, ((f c : EtaCoeff p.eta) : Coeff) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ))]
  rw [← pow_mul, mul_comm, pow_mul]
  conv_rhs => rw [show p.l = #(univ : Finset (Fin p.l)) by simp, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun b _ => Finset.expect_nonneg fun f _ => by split_ifs <;> norm_num)
    fun b _ => expect_vanishing_le_of_injective Subtype.val_injective D

/-- **The key average of `(1 + x)^d(s₁)`**: for a uniform box secret and `x ≥ 0`,
`𝔼 (1 + x)^#Z(s₁) ≤ (1 + x · #E^-ℓ)^256` (`expect_one_add_pow_card_le`). -/
theorem expect_one_add_pow_card_secretZeroSlots_le {p : Params} {x : ℝ} (hx : 0 ≤ x) :
    𝔼 e : SecretCoeffs p, (1 + x) ^ #(secretZeroSlots e) ≤
      (1 + x * ((Fintype.card (EtaCoeff p.eta) : ℝ)⁻¹) ^ p.l) ^ ringDegree := by
  have h := GordieHowe.expect_one_add_pow_card_le (Z := fun e : SecretCoeffs p => secretZeroSlots e)
    hx expect_subset_secretZeroSlots_le
  rwa [Fintype.card_fin] at h

/-- **Many zero slots are rare**: `Pr[#Z(s₁) ≥ d₀] ≤ C(256, d₀) · (#E^-ℓ)^d₀` for a uniform box
secret (a union bound over the `d₀`-subsets of slots). -/
theorem expect_le_card_secretZeroSlots_le {p : Params} (d₀ : ℕ) :
    𝔼 e : SecretCoeffs p, (if d₀ ≤ #(secretZeroSlots e) then 1 else 0 : ℝ) ≤
      (ringDegree.choose d₀ : ℝ) * (((Fintype.card (EtaCoeff p.eta) : ℝ)⁻¹) ^ p.l) ^ d₀ := by
  have h := GordieHowe.expect_indicator_le_card_le_choose_mul_pow
    (Z := fun e : SecretCoeffs p => secretZeroSlots e) d₀ expect_subset_secretZeroSlots_le
  rwa [Fintype.card_fin] at h

end Keys

/-! ### The layered tail over keys and matrices -/

section Tail

variable {p : Params}

attribute [local instance] concreteNTTRingOps

/-- The secret key `sk` with `(s₁, s₂)` replaced by the secret of the coefficient array `e`;
`keyOf` recomputes `t₀` from the matrix. -/
noncomputable def keyOfCoeffs (sk : SecretKey p) (e : SecretCoeffs p) : SecretKey p :=
  { sk with s1 := (secretOfCoeffs e).1, s2 := (secretOfCoeffs e).2 }

/-- `‖t₀‖₂² ≤ 256 k · 4096²`. -/
theorem t0SqNorm_keyOf_le (sk₀ : SecretKey p) (τ : Fin p.k → Rq) :
    t0SqNorm (keyOf sk₀ τ).t0 ≤ p.k * ringDegree * 4096 ^ 2 := by
  rw [t0SqNorm_keyOf]
  calc _ ≤ ∑ _x : Fin p.k × Fin ringDegree, (4096 : ℝ) ^ 2 :=
        Finset.sum_le_sum fun x _ => power2RoundLowCoeff_sq_le _
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-- **The Chernoff bound on `‖t₀‖₂²` for one key**: for `λ ≥ 0` and `φ(λ) ≤ Φ`,
`Pr_Â[‖t₀‖₂² > a] ≤ exp(-λ a) · Φ^(256 k) · (exp(λ 4096²) / Φ)^(k d)`, `d = #Z(s₁)`. -/
theorem expect_indicator_lt_t0SqNorm_le (sk₀ : SecretKey p) {lam Φ a : ℝ} (hlam : 0 ≤ lam)
    (hΦ : t0SqMgf lam ≤ Φ) :
    𝔼 aHat : TqMatrix p.k p.l, (if a < t0SqNorm
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 then 1 else 0 : ℝ) ≤
      exp (-(lam * a)) * Φ ^ (p.k * ringDegree) *
        ((exp (lam * 4096 ^ 2) / Φ) ^ p.k) ^ #(zeroSlots fun b => sk₀.s1.get b) := by
  set d := #(zeroSlots fun b => sk₀.s1.get b)
  have hφ0 : 0 < t0SqMgf lam := Finset.expect_pos (fun r _ => exp_pos _) Finset.univ_nonempty
  have hΦp : 0 < Φ := hφ0.trans_le hΦ
  have hd : d ≤ ringDegree := by
    simpa [d] using Finset.card_le_univ (zeroSlots fun b => sk₀.s1.get b)
  refine (GordieHowe.expect_indicator_lt_le_exp_mul_expect_exp a hlam).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((expect_exp_t0SqNorm_le sk₀ hlam).trans ?_) (exp_pos _).le
  have hsplit : Φ ^ (p.k * ringDegree) = Φ ^ (p.k * (ringDegree - d)) * Φ ^ (p.k * d) := by
    rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hd]
  have hexp : exp (lam * (p.k * d * 4096 ^ 2)) = exp (lam * 4096 ^ 2) ^ (p.k * d) := by
    rw [← exp_nat_mul]
    push_cast
    ring_nf
  have hr : Φ ^ (p.k * d) * ((exp (lam * 4096 ^ 2) ^ p.k / Φ ^ p.k) ^ d) =
      exp (lam * 4096 ^ 2) ^ (p.k * d) := by
    rw [div_pow, ← pow_mul, ← pow_mul]
    field_simp
  change t0SqMgf lam ^ (p.k * (ringDegree - d)) * exp (lam * (p.k * d * 4096 ^ 2)) ≤ _
  rw [div_pow, hsplit, mul_assoc (Φ ^ (p.k * (ringDegree - d))), hr, hexp]
  gcongr

/-- **The layered tail of `‖t₀‖₂²` over uniform box secrets and a uniform matrix**: for a monotone
`f`, a grid `a_0 ≤ … ≤ a_N` with `a_N ≥ 256 k · 4096²` (the largest `‖t₀‖₂²`), bounds
`f(a_i) ≤ U_i` with `U_0 ≤ … ≤ U_N`, rates `λ_i ≥ 0` and bounds `φ(λ_i) ≤ Φ_i ≤ exp(λ_i 4096²)`,
`𝔼_{s, Â} f(‖t₀‖₂²) ≤ U_0 + ∑_{i < N} (U_{i+1} - U_i) · exp(-λ_i a_i) · Φ_i^(256 k) ·
(1 + ((exp(λ_i 4096²)/Φ_i)^k - 1) / (2η + 1)^ℓ)^256`.
Each layer pays the Chernoff bound of one key (`expect_indicator_lt_t0SqNorm_le`), whose zero-slot
factor `ρ^(k d)` is averaged over the key (`expect_one_add_pow_card_secretZeroSlots_le`). -/
theorem expect_expect_le_layers (sk : SecretKey p) (hη : 2 * p.eta < modulus) {f : ℝ → ℝ}
    (hf : Monotone f) {a U : ℕ → ℝ} {N : ℕ} (ha : ∀ i < N, a i ≤ a (i + 1))
    (hU : ∀ i < N, U i ≤ U (i + 1)) (hfU : ∀ i ≤ N, f (a i) ≤ U i)
    (hN : (p.k * ringDegree * 4096 ^ 2 : ℝ) ≤ a N) {lam Φ : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hΦ : ∀ i < N, t0SqMgf (lam i) ≤ Φ i) (hΦe : ∀ i < N, Φ i ≤ exp (lam i * 4096 ^ 2)) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l, f (t0SqNorm (keyOf (keyOfCoeffs sk e)
        (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤
      U 0 + ∑ i ∈ range N, (U (i + 1) - U i) *
        (exp (-(lam i * a i)) * Φ i ^ (p.k * ringDegree) *
          (1 + ((exp (lam i * 4096 ^ 2) / Φ i) ^ p.k - 1) / (2 * p.eta + 1) ^ p.l) ^ ringDegree) := by
  have := concreteNTTRingLaws
  have : Nonempty (TqMatrix p.k p.l) := ⟨(matOfHat_bijective.2 0).choose⟩
  set P : ℕ → SecretCoeffs p → ℝ := fun i e => 𝔼 aHat : TqMatrix p.k p.l,
    (if a i < t0SqNorm (keyOf (keyOfCoeffs sk e)
      (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 then 1 else 0 : ℝ)
  have hinner : ∀ e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l, f (t0SqNorm (keyOf
      (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤
      U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * P i e := fun e =>
    GordieHowe.expect_le_layers_of_le hf ha hU hfU fun aHat => (t0SqNorm_keyOf_le _ _).trans hN
  have hlayer : ∀ i < N, 𝔼 e, P i e ≤ exp (-(lam i * a i)) * Φ i ^ (p.k * ringDegree) *
      (1 + ((exp (lam i * 4096 ^ 2) / Φ i) ^ p.k - 1) / (2 * p.eta + 1) ^ p.l) ^ ringDegree := by
    intro i hi
    have hΦp : 0 < Φ i := (Finset.expect_pos (fun r _ => exp_pos _) Finset.univ_nonempty).trans_le
      (hΦ i hi)
    have hx : 0 ≤ (exp (lam i * 4096 ^ 2) / Φ i) ^ p.k - 1 := by
      rw [sub_nonneg]
      exact one_le_pow₀ ((one_le_div hΦp).2 (hΦe i hi))
    calc 𝔼 e, P i e ≤ 𝔼 e : SecretCoeffs p, exp (-(lam i * a i)) * Φ i ^ (p.k * ringDegree) *
          (1 + ((exp (lam i * 4096 ^ 2) / Φ i) ^ p.k - 1)) ^ #(secretZeroSlots e) :=
          Finset.expect_le_expect fun e _ => by
            rw [add_sub_cancel]
            exact expect_indicator_lt_t0SqNorm_le (keyOfCoeffs sk e) (hlam i) (hΦ i hi)
      _ = exp (-(lam i * a i)) * Φ i ^ (p.k * ringDegree) * 𝔼 e : SecretCoeffs p,
          (1 + ((exp (lam i * 4096 ^ 2) / Φ i) ^ p.k - 1)) ^ #(secretZeroSlots e) :=
          (Finset.mul_expect _ _ _).symm
      _ ≤ _ := by
          gcongr
          refine (expect_one_add_pow_card_secretZeroSlots_le hx).trans_eq ?_
          rw [card_etaCoeff hη, inv_pow, div_eq_mul_inv]
          push_cast
          rfl
  calc _ ≤ 𝔼 e : SecretCoeffs p, (U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * P i e) :=
        Finset.expect_le_expect fun e _ => hinner e
    _ = U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * 𝔼 e, P i e := by
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
          Finset.expect_sum_comm]
        simp_rw [← Finset.mul_expect]
    _ ≤ _ := by
        gcongr with i hi
        · exact sub_nonneg.2 (hU i (mem_range.1 hi))
        · exact hlayer i (mem_range.1 hi)

/-! ### The chord bound on `φ` -/

/-- **The chord bound on `φ` at the nine nodes `m/8`**, as a function of `λ' = 4096² λ`:
`∑_{m ≤ 8} μ_m exp(λ' m / 8)` with the node masses `μ_m` of `expect_exp_t0_sq_le_eight`. -/
noncomputable def t0ChordBound (lam : ℝ) : ℝ :=
  517808834095/2196876034048 * exp 0 +
    214483308369/1098438017024 * exp (lam / 8) +
    558506814195/4393752068096 * exp (lam / 4) +
    225827764569/2196876034048 * exp (3 * lam / 8) +
    779803530693/8787504136192 * exp (lam / 2) +
    174117721173/2196876034048 * exp (5 * lam / 8) +
    635293578843/8787504136192 * exp (3 * lam / 4) +
    293945934117/4393752068096 * exp (7 * lam / 8) +
    70154445933/2196876034048 * exp lam

/-- `φ(λ' / 4096²) ≤ t0ChordBound λ'` (`expect_exp_t0_sq_le_eight`). -/
theorem t0SqMgf_le_t0ChordBound (lam : ℝ) : t0SqMgf (lam / 4096 ^ 2) ≤ t0ChordBound lam := by
  refine le_trans (le_of_eq ?_) (expect_exp_t0_sq_le_eight lam)
  rw [t0SqMgf, Fintype.expect_eq_sum_div_card]
  refine congrArg (· / (Fintype.card Coeff : ℝ)) (Finset.sum_congr rfl fun r _ => ?_)
  refine congrArg exp ?_
  ring

/-- The chord bound lies below its largest node value: `t0ChordBound λ' ≤ exp λ'` for `λ' ≥ 0`
(the masses sum to `1`). -/
theorem t0ChordBound_le_exp {lam : ℝ} (hlam : 0 ≤ lam) : t0ChordBound lam ≤ exp lam := by
  unfold t0ChordBound
  calc _ ≤ 517808834095/2196876034048 * exp lam +
        214483308369/1098438017024 * exp lam +
        558506814195/4393752068096 * exp lam +
        225827764569/2196876034048 * exp lam +
        779803530693/8787504136192 * exp lam +
        174117721173/2196876034048 * exp lam +
        635293578843/8787504136192 * exp lam +
        293945934117/4393752068096 * exp lam +
        70154445933/2196876034048 * exp lam := by
        gcongr <;> linarith
    _ = exp lam := by ring

/-- **The chord polynomial**: `t0ChordBound λ' = t0ChordPoly (exp(λ'/8))`
(`t0ChordBound_eq_t0ChordPoly`), `∑_{m ≤ 8} μ_m E^m` with the node masses `μ_m`. -/
noncomputable def t0ChordPoly (E : ℝ) : ℝ :=
  517808834095/2196876034048 + 214483308369/1098438017024 * E +
    558506814195/4393752068096 * E ^ 2 + 225827764569/2196876034048 * E ^ 3 +
    779803530693/8787504136192 * E ^ 4 + 174117721173/2196876034048 * E ^ 5 +
    635293578843/8787504136192 * E ^ 6 + 293945934117/4393752068096 * E ^ 7 +
    70154445933/2196876034048 * E ^ 8

/-- The chord bound is the chord polynomial at `exp(λ'/8)`. -/
theorem t0ChordBound_eq_t0ChordPoly (lam : ℝ) : t0ChordBound lam = t0ChordPoly (exp (lam / 8)) := by
  simp only [t0ChordBound, t0ChordPoly, ← exp_nat_mul]
  push_cast
  ring_nf
  rw [exp_zero, one_mul]

/-- The chord polynomial is monotone on `[0, ∞)`. -/
theorem t0ChordPoly_le_t0ChordPoly {E E' : ℝ} (hE : 0 ≤ E) (h : E ≤ E') :
    t0ChordPoly E ≤ t0ChordPoly E' := by
  unfold t0ChordPoly
  gcongr

/-- The chord polynomial is positive on `[0, ∞)`. -/
theorem t0ChordPoly_pos {E : ℝ} (hE : 0 ≤ E) : 0 < t0ChordPoly E := by
  unfold t0ChordPoly
  positivity

/-- **The tail factor of one layer** at the rate `λ'` (in units of `4096⁻²`) and the level `a`:
`exp(-λ' a / 4096²) · Φ^(256 k) · (1 + ((exp λ' / Φ)^k - 1) / (2η + 1)^ℓ)^256` with
`Φ = t0ChordBound λ'`, the factor of `expect_expect_le_layers_chord`. -/
noncomputable def t0TailBound (p : Params) (lam a : ℝ) : ℝ :=
  exp (-(lam * (a / 4096 ^ 2))) * t0ChordBound lam ^ (p.k * ringDegree) *
    (1 + ((exp lam / t0ChordBound lam) ^ p.k - 1) / (2 * p.eta + 1) ^ p.l) ^ ringDegree

/-- **The tail factor from bounds on `exp(λ'/8)`**: for `λ' ≥ 0`, `0 ≤ E_lo ≤ exp(λ'/8) ≤ E_hi`,
`t0ChordPoly E_hi ≤ exp r` and `E_hi^8 / t0ChordPoly E_lo ≤ ρ`,
`t0TailBound p λ' a ≤ exp(-λ' a / 4096² + 256 k r + 256 (ρ^k - 1) / (2η + 1)^ℓ)`. -/
theorem t0TailBound_le_exp (p : Params) {lam a El Eh r ρ : ℝ} (hlam : 0 ≤ lam) (hEl0 : 0 ≤ El)
    (hEl : El ≤ exp (lam / 8)) (hEh : exp (lam / 8) ≤ Eh) (hr : t0ChordPoly Eh ≤ exp r)
    (hρ' : Eh ^ 8 / t0ChordPoly El ≤ ρ) :
    t0TailBound p lam a ≤ exp (-(lam * (a / 4096 ^ 2)) + (p.k * ringDegree : ℕ) * r +
      ringDegree * ((ρ ^ p.k - 1) / (2 * p.eta + 1) ^ p.l)) := by
  set Φ := t0ChordBound lam with hΦdef
  have hΦ : Φ = t0ChordPoly (exp (lam / 8)) := t0ChordBound_eq_t0ChordPoly lam
  have hE0 := (exp_pos (lam / 8)).le
  have hPl : 0 < t0ChordPoly El := t0ChordPoly_pos hEl0
  have hΦl : t0ChordPoly El ≤ Φ := hΦ ▸ t0ChordPoly_le_t0ChordPoly hEl0 hEl
  have hΦu : Φ ≤ exp r := (hΦ ▸ t0ChordPoly_le_t0ChordPoly hE0 hEh).trans hr
  have hΦ0 : 0 < Φ := hPl.trans_le hΦl
  have hΦe : Φ ≤ exp lam := t0ChordBound_le_exp hlam
  have hlam8 : exp lam = exp (lam / 8) ^ 8 := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hρ1 : 1 ≤ exp lam / Φ := (one_le_div hΦ0).2 hΦe
  have hρ : exp lam / Φ ≤ ρ := by
    rw [hlam8]
    exact (div_le_div₀ (by positivity) (pow_le_pow_left₀ hE0 hEh 8) hPl hΦl).trans hρ'
  have hG : (0 : ℝ) < (2 * p.eta + 1) ^ p.l := by positivity
  set x := ((exp lam / Φ) ^ p.k - 1) / (2 * p.eta + 1) ^ p.l
  set x' := (ρ ^ p.k - 1) / (2 * p.eta + 1) ^ p.l
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.2 (one_le_pow₀ hρ1)) hG.le
  have hxx : x ≤ x' := by
    refine div_le_div_of_nonneg_right (sub_le_sub_right ?_ 1) hG.le
    exact pow_le_pow_left₀ (zero_le_one.trans hρ1) hρ _
  have h1 : Φ ^ (p.k * ringDegree) ≤ exp ((p.k * ringDegree : ℕ) * r) := by
    rw [exp_nat_mul]
    exact pow_le_pow_left₀ hΦ0.le hΦu _
  have h2 : (1 + x) ^ ringDegree ≤ exp (ringDegree * x') := by
    rw [exp_nat_mul]
    refine pow_le_pow_left₀ (by linarith) ?_ _
    exact (by linarith [add_one_le_exp x] : 1 + x ≤ exp x).trans (exp_le_exp.2 hxx)
  calc t0TailBound p lam a = exp (-(lam * (a / 4096 ^ 2))) * Φ ^ (p.k * ringDegree) *
        (1 + x) ^ ringDegree := rfl
    _ ≤ exp (-(lam * (a / 4096 ^ 2))) * exp ((p.k * ringDegree : ℕ) * r) *
        exp (ringDegree * x') := by gcongr
    _ = _ := by rw [← exp_add, ← exp_add]

/-- **The layered tail with the chord bound**: `expect_expect_le_layers` with
`λ_i = λ'_i / 4096²` and `Φ_i = t0ChordBound λ'_i`, for rates `λ'_i ≥ 0` in units of `4096⁻²`:
`𝔼_{s, Â} f(‖t₀‖₂²) ≤ U_0 + ∑_{i < N} (U_{i+1} - U_i) · t0TailBound p λ'_i a_i`. Every term of the
right side is explicit. -/
theorem expect_expect_le_layers_chord (sk : SecretKey p) (hη : 2 * p.eta < modulus)
    {f : ℝ → ℝ} (hf : Monotone f) {a U : ℕ → ℝ} {N : ℕ} (ha : ∀ i < N, a i ≤ a (i + 1))
    (hU : ∀ i < N, U i ≤ U (i + 1)) (hfU : ∀ i ≤ N, f (a i) ≤ U i)
    (hN : (p.k * ringDegree * 4096 ^ 2 : ℝ) ≤ a N) {lam : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l, f (t0SqNorm (keyOf (keyOfCoeffs sk e)
        (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤
      U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * t0TailBound p (lam i) (a i) := by
  have h := expect_expect_le_layers sk hη hf ha hU hfU hN (lam := fun i => lam i / 4096 ^ 2)
    (Φ := fun i => t0ChordBound (lam i)) (fun i => div_nonneg (hlam i) (by norm_num))
    (fun i _ => t0SqMgf_le_t0ChordBound (lam i))
    (fun i _ => by
      rw [div_mul_cancel₀ _ (by norm_num)]
      exact t0ChordBound_le_exp (hlam i))
  refine h.trans_eq ?_
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [t0TailBound, div_mul_cancel₀ _ (by norm_num : (4096 : ℝ) ^ 2 ≠ 0), div_mul_eq_mul_div,
    mul_div_assoc]

end Tail

/-! ### Per-component rates -/

section Rates

variable {p : Params}

attribute [local instance] concreteNTTRingOps

/-- **The squared norm of one component of `t₀`**: `‖t₀,m‖₂² = ∑_i t₀,m,i²` over the centered
coefficients. -/
noncomputable def t0CompSqNorm {k : ℕ} (t0 : RqVec k) (m : Fin k) : ℝ :=
  ∑ i, (centeredVec t0 m i : ℝ) ^ 2

/-- `‖t₀‖₂² = ∑_m ‖t₀,m‖₂²`. -/
theorem sum_t0CompSqNorm {k : ℕ} (t0 : RqVec k) : ∑ m, t0CompSqNorm t0 m = t0SqNorm t0 := by
  rw [t0SqNorm, Fintype.sum_prod_type]
  rfl

/-- A product over `Fin k` with one rate raised at `m₀`:
`∏_m f(λ + [m = m₀] μ) = f(λ)^(k - 1) · f(λ + μ)`. -/
theorem prod_add_ite_eq {k : ℕ} (f : ℝ → ℝ) (m₀ : Fin k) (lam mu : ℝ) :
    ∏ m, f (lam + if m = m₀ then mu else 0) = f lam ^ (k - 1) * f (lam + mu) := by
  rw [← prod_erase_mul univ _ (mem_univ m₀)]
  simp only [↓reduceIte]
  congr 1
  rw [prod_congr rfl fun m hm =>
      (show f (lam + if m = m₀ then mu else 0) = f lam by simp [ne_of_mem_erase hm]), prod_const,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- The rate-weighted norm `∑_m λ_m ‖t₀,m‖₂²` of `keyOf sk₀ τ` through the coefficients of
`t = τ + s₂`. -/
theorem sum_mul_t0CompSqNorm_keyOf (sk₀ : SecretKey p) (τ : Fin p.k → Rq) (lam : Fin p.k → ℝ) :
    ∑ m, lam m * t0CompSqNorm (keyOf sk₀ τ).t0 m = ∑ x : Fin p.k × Fin ringDegree,
      lam x.1 *
        ((power2RoundLowCoeff ((τ x.1).get x.2 + (sk₀.s2.get x.1).get x.2) : ℤ) : ℝ) ^ 2 := by
  have h : (keyOf sk₀ τ).t0 = GordieHowe.MLDSA.t0Of p (Vector.ofFn τ + sk₀.s2) := rfl
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => ?_
  rw [t0CompSqNorm, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [h, centeredVec_edgeT0Of, rqVec_add_get_get, Vector.get_ofFn]

/-- The coefficients off the top: `(topIndex k d)ᶜ = univ ×ˢ (topPositions d)ᶜ`. -/
theorem compl_topIndex (k d : ℕ) : (topIndex k d)ᶜ = univ ×ˢ (topPositions d)ᶜ := by
  ext x
  simp [topIndex]

/-- Each component has `d` coefficients off the top: `∑_{x ∉ top} f(x.1) = ∑_m d f(m)` for
`d ≤ 256`. -/
theorem sum_compl_topIndex {k d : ℕ} (f : Fin k → ℝ) (hd : d ≤ ringDegree) :
    ∑ x ∈ (topIndex k d)ᶜ, f x.1 = ∑ m, f m * d := by
  rw [compl_topIndex, sum_product]
  refine sum_congr rfl fun m _ => ?_
  change ∑ _y ∈ (topPositions d)ᶜ, f m = f m * d
  rw [sum_const, card_compl, Fintype.card_fin, card_topPositions, nsmul_eq_mul,
    Nat.sub_sub_self hd, mul_comm]

/-- Each component has `256 - d` top coefficients: `∏_{x ∈ top} f(x.1) = ∏_m f(m)^(256 - d)`. -/
theorem prod_topIndex {k : ℕ} (f : Fin k → ℝ) (d : ℕ) :
    ∏ y : topIndex k d, f y.1.1 = ∏ m, f m ^ (ringDegree - d) := by
  rw [Finset.prod_coe_sort (topIndex k d) (fun x => f x.1), topIndex, prod_product]
  refine prod_congr rfl fun m _ => ?_
  change ∏ _y ∈ topPositions d, f m = f m ^ (ringDegree - d)
  rw [prod_const, card_topPositions]

/-- **The exponential moment of the component norms under a uniform matrix, with a rate per
component**: for rates `λ_m ≥ 0` and every key, with `d = #Z(s₁)`,
`𝔼_Â exp(∑_m λ_m ‖t₀,m‖₂²) ≤ ∏_m φ(λ_m)^(256 - d) · exp(λ_m d 4096²)`. With equal rates this
is `expect_exp_t0SqNorm_le`. -/
theorem expect_exp_sum_mul_t0CompSqNorm_le (sk₀ : SecretKey p) {lam : Fin p.k → ℝ}
    (hlam : ∀ m, 0 ≤ lam m) :
    𝔼 aHat : TqMatrix p.k p.l, exp (∑ m, lam m * t0CompSqNorm
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 m) ≤
      ∏ m, (t0SqMgf (lam m) ^ (ringDegree - #(zeroSlots fun b => sk₀.s1.get b)) *
        exp (lam m * (#(zeroSlots fun b => sk₀.s1.get b) * 4096 ^ 2))) := by
  classical
  have := concreteNTTRingLaws
  set s : Fin p.l → Rq := fun b => sk₀.s1.get b
  set d := #(zeroSlots s)
  set T := topIndex p.k d
  set v : (Fin p.k → Fin p.l → Rq) → Fin p.k × Fin ringDegree → ℝ := fun A x =>
    ((power2RoundLowCoeff ((∑ b, A x.1 b * s b).get x.2 + (sk₀.s2.get x.1).get x.2) : ℤ) : ℝ) ^ 2
  set G : T → Coeff → ℝ := fun y r =>
    exp (lam y.1.1 * ((power2RoundLowCoeff (r + (sk₀.s2.get y.1.1).get y.1.2) : ℤ) : ℝ) ^ 2)
  set C := exp (∑ m, lam m * (d * 4096 ^ 2))
  have hd : d ≤ ringDegree := by simpa [d] using Finset.card_le_univ (zeroSlots s)
  -- Pointwise: the coefficients off `T` contribute at most `λ_m 4096²` each.
  have hpt : ∀ A, exp (∑ x, lam x.1 * v A x) ≤ C * ∏ y : T, G y (topCoeffs s d A y) := by
    intro A
    rw [← Finset.sum_add_sum_compl T, exp_add, mul_comm]
    have hoff : ∑ x ∈ Tᶜ, lam x.1 * v A x ≤ ∑ m, lam m * (d * 4096 ^ 2) := by
      calc ∑ x ∈ Tᶜ, lam x.1 * v A x ≤ ∑ x ∈ Tᶜ, lam x.1 * (4096 : ℝ) ^ 2 :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (power2RoundLowCoeff_sq_le _) (hlam x.1)
        _ = ∑ m, lam m * (d * 4096 ^ 2) := by
            rw [← sum_mul, sum_compl_topIndex lam hd, sum_mul]
            exact sum_congr rfl fun m _ => by ring
    gcongr
    · exact exp_le_exp.2 hoff
    · rw [exp_sum, ← Finset.prod_coe_sort T]
      exact le_of_eq rfl
  have hkey : ∀ aHat : TqMatrix p.k p.l,
      ∑ m, lam m * t0CompSqNorm (keyOf sk₀ (keyMap s (matOfHat aHat))).t0 m =
        ∑ x, lam x.1 * v (matOfHat aHat) x := fun aHat =>
    sum_mul_t0CompSqNorm_keyOf sk₀ _ lam
  calc 𝔼 aHat : TqMatrix p.k p.l,
        exp (∑ m, lam m * t0CompSqNorm (keyOf sk₀ (keyMap s (matOfHat aHat))).t0 m)
      = 𝔼 A : Fin p.k → Fin p.l → Rq, exp (∑ x, lam x.1 * v A x) := by
        simp_rw [hkey]
        exact Fintype.expect_bijective _ matOfHat_bijective _ _ fun _ => rfl
    _ ≤ 𝔼 A : Fin p.k → Fin p.l → Rq, C * ∏ y : T, G y (topCoeffs s d A y) :=
        Finset.expect_le_expect fun A _ => hpt A
    _ = C * 𝔼 u : T → Coeff, ∏ y : T, G y (u y) := by
        rw [← Finset.mul_expect, expect_topCoeffs s (fun u => ∏ y : T, G y (u y))]
    _ = C * ∏ m, t0SqMgf (lam m) ^ (ringDegree - d) := by
        rw [PMF.expect_prod_apply G]
        simp_rw [G, expect_exp_sq_add_eq_t0SqMgf]
        exact congrArg (C * ·) (prod_topIndex (fun m => t0SqMgf (lam m)) d)
    _ = _ := by rw [prod_mul_distrib, ← exp_sum, mul_comm]

/-- **The joint exponential moment of the component norms over keys and matrices**: for rates
`λ_m ≥ 0` and bounds `φ(λ_m) ≤ Φ_m ≤ exp(λ_m 4096²)`, over uniform box secrets and a uniform
matrix,
`𝔼_{s, Â} exp(∑_m λ_m ‖t₀,m‖₂²) ≤
(∏_m Φ_m)^256 · (1 + (∏_m exp(λ_m 4096²)/Φ_m - 1) / (2η + 1)^ℓ)^256`.
Each key pays `(∏_m Φ_m)^256 ρ^d` with `ρ = ∏_m exp(λ_m 4096²)/Φ_m`
(`expect_exp_sum_mul_t0CompSqNorm_le`), and `ρ^d` is averaged over the key
(`expect_one_add_pow_card_secretZeroSlots_le`). -/
theorem expect_expect_exp_sum_mul_t0CompSqNorm_le (sk : SecretKey p) (hη : 2 * p.eta < modulus)
    {lam Φ : Fin p.k → ℝ} (hlam : ∀ m, 0 ≤ lam m) (hΦ : ∀ m, t0SqMgf (lam m) ≤ Φ m)
    (hΦe : ∀ m, Φ m ≤ exp (lam m * 4096 ^ 2)) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l, exp (∑ m, lam m * t0CompSqNorm
        (keyOf (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b)
          (matOfHat aHat))).t0 m) ≤
      (∏ m, Φ m) ^ ringDegree *
        (1 + ((∏ m, exp (lam m * 4096 ^ 2) / Φ m) - 1) / (2 * p.eta + 1) ^ p.l) ^ ringDegree := by
  have hφ0 : ∀ m, 0 < t0SqMgf (lam m) := fun m =>
    Finset.expect_pos (fun r _ => exp_pos _) Finset.univ_nonempty
  have hΦp : ∀ m, 0 < Φ m := fun m => (hφ0 m).trans_le (hΦ m)
  set ρ := ∏ m, exp (lam m * 4096 ^ 2) / Φ m with hρ
  have hρ1 : 1 ≤ ρ := by
    have := prod_le_prod₀ (s := univ) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      fun m _ => (one_le_div (hΦp m)).2 (hΦe m)
    rwa [prod_const_one] at this
  -- One key: `(∏_m Φ_m)^256 ρ^d`.
  have hkey : ∀ sk₀ : SecretKey p, 𝔼 aHat : TqMatrix p.k p.l, exp (∑ m, lam m * t0CompSqNorm
      (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 m) ≤
      (∏ m, Φ m) ^ ringDegree * (1 + (ρ - 1)) ^ #(zeroSlots fun b => sk₀.s1.get b) := by
    intro sk₀
    set d := #(zeroSlots fun b => sk₀.s1.get b)
    have hd : d ≤ ringDegree := by
      simpa [d] using Finset.card_le_univ (zeroSlots fun b => sk₀.s1.get b)
    refine (expect_exp_sum_mul_t0CompSqNorm_le sk₀ hlam).trans ?_
    rw [add_sub_cancel, hρ, ← prod_pow, ← prod_pow, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun m _ => mul_nonneg (pow_nonneg (hφ0 m).le _) (exp_pos _).le)
      fun m _ => ?_
    have he : exp (lam m * (d * 4096 ^ 2)) = exp (lam m * 4096 ^ 2) ^ d := by
      rw [← exp_nat_mul]
      ring_nf
    have hsplit : Φ m ^ ringDegree = Φ m ^ (ringDegree - d) * Φ m ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    have hr : Φ m ^ ringDegree * (exp (lam m * 4096 ^ 2) / Φ m) ^ d =
        Φ m ^ (ringDegree - d) * exp (lam m * 4096 ^ 2) ^ d := by
      have := (hΦp m).ne'
      rw [hsplit, div_pow]
      field_simp
    rw [he, hr]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hφ0 m).le (hΦ m) _) (by positivity)
  calc _ ≤ 𝔼 e : SecretCoeffs p, (∏ m, Φ m) ^ ringDegree * (1 + (ρ - 1)) ^ #(secretZeroSlots e) :=
        Finset.expect_le_expect fun e _ => hkey (keyOfCoeffs sk e)
    _ = (∏ m, Φ m) ^ ringDegree * 𝔼 e : SecretCoeffs p, (1 + (ρ - 1)) ^ #(secretZeroSlots e) :=
        (Finset.mul_expect _ _ _).symm
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (prod_nonneg fun m _ => (hΦp m).le) _)
        refine (expect_one_add_pow_card_secretZeroSlots_le (sub_nonneg.2 hρ1)).trans_eq ?_
        rw [card_etaCoeff hη, inv_pow, div_eq_mul_inv]
        push_cast
        rfl

/-- **The joint exponential moment with the chord bound**: for rates `λ'_m ≥ 0` in units of
`4096⁻²`, over uniform box secrets and a uniform matrix,
`𝔼_{s, Â} exp(∑_m λ'_m ‖t₀,m‖₂² / 4096²) ≤ (∏_m Φ(λ'_m))^256 ·
(1 + (∏_m exp(λ'_m)/Φ(λ'_m) - 1) / (2η + 1)^ℓ)^256` with `Φ = t0ChordBound`. -/
theorem expect_expect_exp_sum_mul_t0CompSqNorm_le_chord (sk : SecretKey p)
    (hη : 2 * p.eta < modulus) {lam : Fin p.k → ℝ} (hlam : ∀ m, 0 ≤ lam m) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l, exp (∑ m, lam m / 4096 ^ 2 * t0CompSqNorm
        (keyOf (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b)
          (matOfHat aHat))).t0 m) ≤
      (∏ m, t0ChordBound (lam m)) ^ ringDegree *
        (1 + ((∏ m, exp (lam m) / t0ChordBound (lam m)) - 1) / (2 * p.eta + 1) ^ p.l) ^
          ringDegree := by
  have h := expect_expect_exp_sum_mul_t0CompSqNorm_le sk hη (lam := fun m => lam m / 4096 ^ 2)
    (Φ := fun m => t0ChordBound (lam m)) (fun m => div_nonneg (hlam m) (by norm_num))
    (fun m => t0SqMgf_le_t0ChordBound (lam m))
    (fun m => by
      rw [div_mul_cancel₀ _ (by norm_num)]
      exact t0ChordBound_le_exp (hlam m))
  refine h.trans_eq ?_
  simp only [div_mul_cancel₀ _ (show (4096 : ℝ) ^ 2 ≠ 0 by norm_num)]

/-- **The joint tail of `‖t₀‖₂²` and one component**: for `λ, μ ≥ 0`, levels `a, b` and a
component `m₀`, over uniform box secrets and a uniform matrix,
`Pr[‖t₀‖₂² ≥ a, ‖t₀,m₀‖₂² ≥ b] ≤ exp(-(λ a + μ b)/4096²) · (Φ(λ)^(k-1) Φ(λ+μ))^256 ·
(1 + (ρ(λ)^(k-1) ρ(λ+μ) - 1) / (2η + 1)^ℓ)^256` with `Φ = t0ChordBound` and
`ρ(λ) = exp(λ)/Φ(λ)`: Chernoff's bound with the rate `λ + μ` on component `m₀` and `λ` on the
others (`expect_expect_exp_sum_mul_t0CompSqNorm_le_chord`). -/
theorem expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le (sk : SecretKey p)
    (hη : 2 * p.eta < modulus) (m₀ : Fin p.k) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (a b : ℝ) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        (if a ≤ t0SqNorm (keyOf (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b)
          (matOfHat aHat))).t0 ∧ b ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
            (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m₀
          then 1 else 0 : ℝ) ≤
      exp (-((lam * a + mu * b) / 4096 ^ 2)) *
        (t0ChordBound lam ^ (p.k - 1) * t0ChordBound (lam + mu)) ^ ringDegree *
        (1 + ((exp lam / t0ChordBound lam) ^ (p.k - 1) *
          (exp (lam + mu) / t0ChordBound (lam + mu)) - 1) / (2 * p.eta + 1) ^ p.l) ^
          ringDegree := by
  set r : Fin p.k → ℝ := fun m => lam + if m = m₀ then mu else 0 with hr
  have hr0 : ∀ m, 0 ≤ r m := fun m => by
    simp only [hr]
    split_ifs <;> linarith
  have hsum : ∀ t0 : RqVec p.k, ∑ m, r m / 4096 ^ 2 * t0CompSqNorm t0 m =
      (lam * t0SqNorm t0 + mu * t0CompSqNorm t0 m₀) / 4096 ^ 2 := fun t0 => by
    have hm : ∀ m, r m / 4096 ^ 2 * t0CompSqNorm t0 m = (lam * t0CompSqNorm t0 m +
        if m = m₀ then mu * t0CompSqNorm t0 m else 0) / 4096 ^ 2 := fun m => by
      simp only [hr]
      split_ifs <;> ring
    rw [sum_congr rfl fun m _ => hm m, ← sum_div, sum_add_distrib, ← mul_sum, sum_t0CompSqNorm]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  -- Pointwise Chernoff: `1[a ≤ S ∧ b ≤ S_{m₀}] ≤ exp(-(λa + μb)/4096²) exp((λS + μS_{m₀})/4096²)`.
  have hpt : ∀ t0 : RqVec p.k, (if a ≤ t0SqNorm t0 ∧ b ≤ t0CompSqNorm t0 m₀ then 1 else 0 : ℝ) ≤
      exp (-((lam * a + mu * b) / 4096 ^ 2)) *
        exp (∑ m, r m / 4096 ^ 2 * t0CompSqNorm t0 m) := fun t0 => by
    rw [← exp_add, hsum]
    split_ifs with h
    · refine one_le_exp ?_
      have h1 := mul_le_mul_of_nonneg_left h.1 hlam
      have h2 := mul_le_mul_of_nonneg_left h.2 hmu
      have : (lam * a + mu * b) / 4096 ^ 2 ≤ (lam * t0SqNorm t0 + mu * t0CompSqNorm t0 m₀) /
          4096 ^ 2 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith
    · exact (exp_pos _).le
  have hchord := expect_expect_exp_sum_mul_t0CompSqNorm_le_chord sk hη hr0
  rw [prod_add_ite_eq t0ChordBound m₀ lam mu,
    prod_add_ite_eq (fun x => exp x / t0ChordBound x) m₀ lam mu] at hchord
  calc _ ≤ 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        exp (-((lam * a + mu * b) / 4096 ^ 2)) * exp (∑ m, r m / 4096 ^ 2 * t0CompSqNorm
          (keyOf (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b)
            (matOfHat aHat))).t0 m) :=
        Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ => hpt _
    _ = exp (-((lam * a + mu * b) / 4096 ^ 2)) * 𝔼 e : SecretCoeffs p,
        𝔼 aHat : TqMatrix p.k p.l, exp (∑ m, r m / 4096 ^ 2 * t0CompSqNorm
          (keyOf (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b)
            (matOfHat aHat))).t0 m) := by
        simp_rw [← Finset.mul_expect]
    _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hchord (exp_pos _).le

/-- **The joint tail of `‖t₀‖₂²` and the largest component**: under the hypotheses of
`expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le`,
`Pr[‖t₀‖₂² ≥ a, max_m ‖t₀,m‖₂² ≥ b]` is at most `k` times its bound (a union over the
components). -/
theorem expect_expect_indicator_le_t0SqNorm_and_exists_le_t0CompSqNorm_le (sk : SecretKey p)
    (hη : 2 * p.eta < modulus) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (a b : ℝ) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        (if a ≤ t0SqNorm (keyOf (keyOfCoeffs sk e) (keyMap (fun b => (keyOfCoeffs sk e).s1.get b)
          (matOfHat aHat))).t0 ∧ ∃ m, b ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
            (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m
          then 1 else 0 : ℝ) ≤
      p.k * (exp (-((lam * a + mu * b) / 4096 ^ 2)) *
        (t0ChordBound lam ^ (p.k - 1) * t0ChordBound (lam + mu)) ^ ringDegree *
        (1 + ((exp lam / t0ChordBound lam) ^ (p.k - 1) *
          (exp (lam + mu) / t0ChordBound (lam + mu)) - 1) / (2 * p.eta + 1) ^ p.l) ^
          ringDegree) := by
  have hpt : ∀ t0 : RqVec p.k, (if a ≤ t0SqNorm t0 ∧ ∃ m, b ≤ t0CompSqNorm t0 m then 1 else 0 : ℝ) ≤
      ∑ m, (if a ≤ t0SqNorm t0 ∧ b ≤ t0CompSqNorm t0 m then 1 else 0 : ℝ) := fun t0 => by
    split_ifs with h
    · obtain ⟨ha, m, hm⟩ := h
      refine le_trans ?_ (single_le_sum (f := fun m =>
        (if a ≤ t0SqNorm t0 ∧ b ≤ t0CompSqNorm t0 m then 1 else 0 : ℝ))
        (fun j _ => by split_ifs <;> norm_num) (mem_univ m))
      simp [ha, hm]
    · exact sum_nonneg fun j _ => by split_ifs <;> norm_num
  refine (Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ =>
    hpt _).trans ?_
  simp_rw [Finset.expect_sum_comm]
  refine (sum_le_sum fun m _ =>
    expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le sk hη m hlam hmu a b).trans_eq ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The joint tail factor** at rates `λ', μ' ≥ 0` (units of `4096⁻²`) and levels `a, b`:
`exp(-(λ' a + μ' b)/4096²) · (Φ(λ')^(k-1) Φ(λ' + μ'))^256 ·
(1 + (ρ(λ')^(k-1) ρ(λ' + μ') - 1) / (2η + 1)^ℓ)^256` with `Φ = t0ChordBound` and
`ρ(λ') = exp λ' / Φ(λ')`, the bound of
`expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le`. -/
noncomputable def jointTailBound (p : Params) (lam mu a b : ℝ) : ℝ :=
  exp (-((lam * a + mu * b) / 4096 ^ 2)) *
    (t0ChordBound lam ^ (p.k - 1) * t0ChordBound (lam + mu)) ^ ringDegree *
    (1 + ((exp lam / t0ChordBound lam) ^ (p.k - 1) *
      (exp (lam + mu) / t0ChordBound (lam + mu)) - 1) / (2 * p.eta + 1) ^ p.l) ^ ringDegree

/-- **Bounds on the chord bound from bounds on `exp(λ'/8)`**: for `λ' ≥ 0`,
`0 ≤ E_lo ≤ exp(λ'/8) ≤ E_hi`, `t0ChordPoly E_hi ≤ exp r` and `E_hi^8 / t0ChordPoly E_lo ≤ ρ`:
`0 < Φ(λ') ≤ exp r` and `1 ≤ exp λ' / Φ(λ') ≤ ρ` with `Φ = t0ChordBound`. -/
theorem t0ChordBound_bounds {lam El Eh r ρ : ℝ} (hlam : 0 ≤ lam) (hEl0 : 0 ≤ El)
    (hEl : El ≤ exp (lam / 8)) (hEh : exp (lam / 8) ≤ Eh) (hr : t0ChordPoly Eh ≤ exp r)
    (hρ' : Eh ^ 8 / t0ChordPoly El ≤ ρ) :
    0 < t0ChordBound lam ∧ t0ChordBound lam ≤ exp r ∧ 1 ≤ exp lam / t0ChordBound lam ∧
      exp lam / t0ChordBound lam ≤ ρ := by
  have hΦ : t0ChordBound lam = t0ChordPoly (exp (lam / 8)) := t0ChordBound_eq_t0ChordPoly lam
  have hE0 := (exp_pos (lam / 8)).le
  have hPl : 0 < t0ChordPoly El := t0ChordPoly_pos hEl0
  have hΦl : t0ChordPoly El ≤ t0ChordBound lam := hΦ ▸ t0ChordPoly_le_t0ChordPoly hEl0 hEl
  have hΦ0 : 0 < t0ChordBound lam := hPl.trans_le hΦl
  have hlam8 : exp lam = exp (lam / 8) ^ 8 := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨hΦ0, (hΦ ▸ t0ChordPoly_le_t0ChordPoly hE0 hEh).trans hr,
    (one_le_div hΦ0).2 (t0ChordBound_le_exp hlam), ?_⟩
  rw [hlam8]
  exact (div_le_div₀ (by positivity) (pow_le_pow_left₀ hE0 hEh 8) hPl hΦl).trans hρ'

/-- **The joint tail factor from bounds on `exp(λ'/8)` and `exp((λ' + μ')/8)`**: with the
hypotheses of `t0ChordBound_bounds` at `λ'` (`E_lo, E_hi, r, ρ`) and at `λ' + μ'`
(`E'_lo, E'_hi, r', ρ'`), for `k ≥ 1`,
`jointTailBound p λ' μ' a b ≤ exp(-(λ' a + μ' b)/4096² + 256 (k - 1) r + 256 r' +
256 (ρ^(k-1) ρ' - 1) / (2η + 1)^ℓ)`. -/
theorem jointTailBound_le_exp (p : Params) {lam mu a b El Eh r ρ El' Eh' r' ρ' : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hEl0 : 0 ≤ El) (hEl : El ≤ exp (lam / 8))
    (hEh : exp (lam / 8) ≤ Eh) (hr : t0ChordPoly Eh ≤ exp r) (hρ : Eh ^ 8 / t0ChordPoly El ≤ ρ)
    (hEl0' : 0 ≤ El') (hEl' : El' ≤ exp ((lam + mu) / 8)) (hEh' : exp ((lam + mu) / 8) ≤ Eh')
    (hr' : t0ChordPoly Eh' ≤ exp r') (hρ' : Eh' ^ 8 / t0ChordPoly El' ≤ ρ') :
    jointTailBound p lam mu a b ≤ exp (-((lam * a + mu * b) / 4096 ^ 2) +
      ((p.k - 1) * ringDegree : ℕ) * r + ringDegree * r' +
        ringDegree * ((ρ ^ (p.k - 1) * ρ' - 1) / (2 * p.eta + 1) ^ p.l)) := by
  obtain ⟨h0, hu, h1, hρu⟩ := t0ChordBound_bounds hlam hEl0 hEl hEh hr hρ
  obtain ⟨h0', hu', h1', hρu'⟩ := t0ChordBound_bounds (add_nonneg hlam hmu) hEl0' hEl' hEh' hr' hρ'
  have hG : (0 : ℝ) < (2 * p.eta + 1) ^ p.l := by positivity
  set x := ((exp lam / t0ChordBound lam) ^ (p.k - 1) *
    (exp (lam + mu) / t0ChordBound (lam + mu)) - 1) / (2 * p.eta + 1) ^ p.l
  set x' := (ρ ^ (p.k - 1) * ρ' - 1) / (2 * p.eta + 1) ^ p.l
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.2 (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ h1) h1')) hG.le
  have hxx : x ≤ x' := by
    refine div_le_div_of_nonneg_right (sub_le_sub_right ?_ 1) hG.le
    exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans h1) hρu _) hρu'
      (zero_le_one.trans h1') (pow_nonneg ((zero_le_one.trans h1).trans hρu) _)
  have hP : (t0ChordBound lam ^ (p.k - 1) * t0ChordBound (lam + mu)) ^ ringDegree ≤
      exp (((p.k - 1) * ringDegree : ℕ) * r + ringDegree * r') := by
    rw [exp_add, exp_nat_mul, exp_nat_mul, pow_mul, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact mul_le_mul (pow_le_pow_left₀ h0.le hu _) hu' h0'.le (by positivity)
  have h2 : (1 + x) ^ ringDegree ≤ exp (ringDegree * x') := by
    rw [exp_nat_mul]
    refine pow_le_pow_left₀ (by linarith) ?_ _
    exact (by linarith [add_one_le_exp x] : 1 + x ≤ exp x).trans (exp_le_exp.2 hxx)
  calc jointTailBound p lam mu a b = exp (-((lam * a + mu * b) / 4096 ^ 2)) *
        (t0ChordBound lam ^ (p.k - 1) * t0ChordBound (lam + mu)) ^ ringDegree *
        (1 + x) ^ ringDegree := rfl
    _ ≤ exp (-((lam * a + mu * b) / 4096 ^ 2)) *
        exp (((p.k - 1) * ringDegree : ℕ) * r + ringDegree * r') * exp (ringDegree * x') := by
        gcongr
    _ = _ := by
        rw [← exp_add, ← exp_add]
        congr 1
        ring

end Rates

end GordieHowe.MLDSA.Regularity
