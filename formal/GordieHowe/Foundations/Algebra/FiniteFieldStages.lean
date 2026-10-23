-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.RelativePackingBijective
public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Foundations.Fields.BinarySpreadBasis
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section

/-!
# The subfields and the packing stages of a finite field

For a finite field `K` of `p^n` elements (`p > 1` its characteristic) the packing facts that
GordieHowe's packing tree needs exist for every degree that divides `n`:

* **the subfields** (`card_fixedField_of_dvd`): for `k ∣ n` the fixed field `F_{p^k}` of
  `x ↦ x^(p^k)` has `p^k` elements, from the root count of `X^(p^k) − X` and `|K| ≤ |F_{p^k}|^(n/k)`
  (`card_le_fixedField_pow`); two dividing degrees with the same fixed field are equal
  (`fixedField_injOn_dvd`); `F_{p^n}` is `K` (`fixedField_eq_top`);
* **the dual bases** (`RelativeBasis.traceDualOf`): for `m d ∣ n`, every basis `β` of
  `F_{p^(m d)}` over `F_{p^m}` has a trace-dual basis in `F_{p^(m d)}`. The extension of finite
  fields is separable, so its trace form is nondegenerate (Mathlib's `traceForm_nondegenerate`), and
  its trace is `Σ_{k<d} φ^k` (Mathlib's `FiniteField.algebraMap_trace_eq_sum_pow`, our `relTrace`,
  `relTrace_eq_algebraMap_trace`);
* **a basis exists** (`exists_basis`), so every such stage has a stage basis
  (`StageBasis.ofFixedField`).

The constructions here are noncomputable (Mathlib's dual basis of a nondegenerate form); they show
that the packing facts exist, while the concrete fields certify theirs by computation.
-/

namespace GordieHowe.RelativePacking

open PackingStage Polynomial

variable {K : Type} [Field K] {p : ℕ} [ExpChar K p]

/-- `F_{p^a}` lies in `F_{p^b}` when `a ∣ b`. -/
theorem fixedField_le_of_dvd {a b : ℕ} (h : a ∣ b) : fixedField K p a ≤ fixedField K p b := by
  obtain ⟨k, rfl⟩ := h
  exact fixedField_le_mul a k

variable [Fintype K]

/-- **`F_{p^k}` has at most `p^k` elements**: its elements are roots of `X^(p^k) − X`. -/
theorem card_fixedField_le {k : ℕ} (hk : k ≠ 0) (hp : 1 < p) :
    Nat.card (fixedField K p k) ≤ p ^ k := by
  classical
  have hP : (X ^ p ^ k - X : K[X]) ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero K hk hp
  let Z : Finset K := Finset.univ.filter (· ∈ fixedField K p k)
  have hZ : Z.val ⊆ (X ^ p ^ k - X : K[X]).roots := by
    intro z hz
    have hz' : z ∈ fixedField K p k := (Finset.mem_filter.mp hz).2
    rw [mem_fixedField_iff_pow] at hz'
    rw [Polynomial.mem_roots hP]
    simp [hz']
  have hle := Polynomial.card_le_degree_of_subset_roots hZ
  rw [FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hk hp] at hle
  have hcard : Nat.card (fixedField K p k) = Z.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  exact hle

/-- **`F_{p^k}` has `p^k` elements** for `k ∣ n`, `|K| = p^n`. -/
theorem card_fixedField_of_dvd {n k : ℕ} (hK : Fintype.card K = p ^ n) (hn : n ≠ 0)
    (hk : k ∣ n) (hp : 1 < p) : Nat.card (fixedField K p k) = p ^ k := by
  obtain ⟨r, rfl⟩ := hk
  have hk0 : k ≠ 0 := left_ne_zero_of_mul hn
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hn
  have : RelFrobeniusOrder K p k r := RelFrobeniusOrder.of_card hK (Nat.pos_of_ne_zero hr0)
  have h1 := card_le_fixedField_pow K p k r
  have h2 := card_fixedField_le (K := K) hk0 hp
  rw [Nat.card_eq_fintype_card, hK, pow_mul] at h1
  by_contra hne
  have hlt := lt_of_le_of_ne h2 hne
  exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_left hlt hr0))

/-- **`F_{p^n}` is `K`** when `|K| = p^n`. -/
theorem fixedField_eq_top {n : ℕ} (hK : Fintype.card K = p ^ n) : fixedField K p n = ⊤ := by
  ext x
  simp only [Subfield.mem_top, iff_true]
  rw [mem_fixedField_iff_pow, ← hK]
  exact FiniteField.pow_card x

/-- **The subfield of each dividing degree is unique**: dividing degrees with the same fixed field
are equal. -/
theorem fixedField_injOn_dvd {n a b : ℕ} (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p)
    (ha : a ∣ n) (hb : b ∣ n) (h : fixedField K p a = fixedField K p b) : a = b := by
  have hca := card_fixedField_of_dvd hK hn ha hp
  have hcb := card_fixedField_of_dvd hK hn hb hp
  rw [h, hcb] at hca
  exact Nat.pow_right_injective hp hca.symm

/-! ### The stage `F_{p^m} < F_{p^(m d)}` as an algebra -/

variable (K p) in
/-- **`F_{p^(m d)}` as an algebra over `F_{p^m}`**, by the inclusion. -/
noncomputable abbrev stageAlgebra (m d : ℕ) : Algebra (fixedField K p m) (fixedField K p (m * d)) :=
  (Subfield.inclusion (fixedField_le_mul (K := K) (p := p) m d)).toAlgebra

section Stage

variable {n m d : ℕ}

attribute [local instance] stageAlgebra

omit [Fintype K] in
/-- The algebra map of the stage is the inclusion. -/
theorem stageAlgebra_algebraMap_coe (b : fixedField K p m) :
    ((algebraMap (fixedField K p m) (fixedField K p (m * d)) b : fixedField K p (m * d)) : K) =
      (b : K) :=
  rfl

omit [Fintype K] in
/-- A scalar multiple in the stage is the product in `K`. -/
theorem stageAlgebra_smul_coe (b : fixedField K p m) (x : fixedField K p (m * d)) :
    ((b • x : fixedField K p (m * d)) : K) = (b : K) * (x : K) :=
  rfl

/-- **The degree of the stage is `d`**, for `m d ∣ n`. -/
theorem finrank_stage (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p) (hmd : m * d ∣ n) :
    Module.finrank (fixedField K p m) (fixedField K p (m * d)) = d := by
  have hm : m ∣ n := Dvd.dvd.trans (Dvd.intro d rfl) hmd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hmd
    exact hn hmd
  have hT := card_fixedField_of_dvd hK hn hmd hp
  have hB := card_fixedField_of_dvd hK hn hm hp
  have hc := Module.natCard_eq_pow_finrank (K := fixedField K p m) (V := fixedField K p (m * d))
  rw [hT, hB, ← pow_mul] at hc
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0)
    (Nat.pow_right_injective hp hc)).symm

/-- **The trace of the stage is `relTrace`**: `Tr_{F_{p^(m d)}/F_{p^m}}(x) = Σ_{k<d} x^(p^(m k))`
(Mathlib's `FiniteField.algebraMap_trace_eq_sum_pow`). -/
theorem relTrace_eq_algebraMap_trace (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p)
    (hmd : m * d ∣ n) (x : fixedField K p (m * d)) :
    relTrace p m d (x : K) =
      ((algebraMap (fixedField K p m) (fixedField K p (m * d))
        (Algebra.trace (fixedField K p m) (fixedField K p (m * d)) x) : fixedField K p (m * d)) :
          K) := by
  have hm : m ∣ n := Dvd.dvd.trans (Dvd.intro d rfl) hmd
  rw [FiniteField.algebraMap_trace_eq_sum_pow, finrank_stage hK hn hp hmd,
    card_fixedField_of_dvd hK hn hm hp, relTrace, Fin.sum_univ_eq_sum_range (fun k => phi p m k _)]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [phi_def, pow_mul]

/-- **A basis of the stage**, as elements of `K`: `β` in `F_{p^(m d)}` whose combinations with
coefficients in `F_{p^m}` are injective. -/
structure StageIndependent (p m d : ℕ) [ExpChar K p] (β : Fin d → K) : Prop where
  /-- The basis lies in `F_{p^(m d)}`. -/
  mem : ∀ i, β i ∈ fixedField K p (m * d)
  /-- The combinations are injective. -/
  injective : Function.Injective fun c : Fin d → fixedField K p m => ∑ i, β i * (c i : K)

/-- **A basis of the stage exists**, for `m d ∣ n`. -/
theorem exists_stageIndependent (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p)
    (hmd : m * d ∣ n) : ∃ β : Fin d → K, StageIndependent p m d β := by
  let b := Module.finBasisOfFinrankEq (fixedField K p m) (fixedField K p (m * d))
    (finrank_stage hK hn hp hmd)
  refine ⟨fun i => (b i : K), fun i => (b i).2, ?_⟩
  intro c c' h
  apply b.equivFun.symm.injective
  rw [b.equivFun_symm_apply, b.equivFun_symm_apply]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum, stageAlgebra_smul_coe]
  simpa only [mul_comm] using h

/-- **The Mathlib basis of an independent family.** -/
noncomputable def StageIndependent.basis (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p)
    (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β) :
    Module.Basis (Fin d) (fixedField K p m) (fixedField K p (m * d)) :=
  basisOfLinearIndependentOfCardEqFinrank' (b := fun i => ⟨β i, hβ.mem i⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h0 : ∑ j, β j * (g j : K) = ∑ j, β j * ((0 : Fin d → fixedField K p m) j : K) := by
        have := congrArg (fun x : fixedField K p (m * d) => (x : K)) hg
        simp only [AddSubmonoidClass.coe_finsetSum, stageAlgebra_smul_coe, ZeroMemClass.coe_zero] at this
        simpa [mul_comm] using this
      exact congrFun (hβ.injective h0) i)
    (by rw [Fintype.card_fin, finrank_stage hK hn hp hmd])

theorem StageIndependent.basis_apply (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p)
    (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β) (i : Fin d) :
    ((hβ.basis hK hn hp hmd i : fixedField K p (m * d)) : K) = β i := by
  simp [StageIndependent.basis]

/-- **The trace-dual basis of a basis of the stage** (`RelativeBasis`): the basis `β` and Mathlib's
dual basis of the trace form, nondegenerate for the separable extension
`F_{p^m} < F_{p^(m d)}`. -/
noncomputable def RelativeBasis.traceDualOf (hK : Fintype.card K = p ^ n) (hn : n ≠ 0)
    (hp : 1 < p) (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β) :
    RelativeBasis K p m d where
  β := β
  dual i := ((Algebra.traceForm (fixedField K p m) (fixedField K p (m * d))).dualBasis
    (traceForm_nondegenerate _ _) (hβ.basis hK hn hp hmd) i : fixedField K p (m * d))
  trace_dual i j := by
    rw [← hβ.basis_apply hK hn hp hmd j, ← Subfield.coe_mul, relTrace_eq_algebraMap_trace hK hn hp hmd]
    have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate
      (fixedField K p m) (fixedField K p (m * d))) (hβ.basis hK hn hp hmd) i j
    rw [Algebra.traceForm_apply] at h
    rw [h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]

theorem RelativeBasis.traceDualOf_β (hK : Fintype.card K = p ^ n) (hn : n ≠ 0) (hp : 1 < p)
    (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β) :
    (RelativeBasis.traceDualOf hK hn hp hmd hβ).β = β :=
  rfl

/-- **The stage basis of `F_{p^m} < F_{p^(m d)}`** from a basis of the stage (`traceDualOf`). -/
noncomputable def StageIndependent.stageBasis (hK : Fintype.card K = p ^ n) (hn : n ≠ 0)
    (hp : 1 < p) (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β) :
    StageBasis K p m d :=
  StageBasis.ofFixedField (RelativeBasis.traceDualOf hK hn hp hmd hβ) hβ.mem
    fun i => (((Algebra.traceForm (fixedField K p m) (fixedField K p (m * d))).dualBasis
      (traceForm_nondegenerate _ _) (hβ.basis hK hn hp hmd) i : fixedField K p (m * d))).2

/-- **The coordinates of a combination** in the stage basis are its coefficients. -/
theorem StageIndependent.coord_stageBasis (hK : Fintype.card K = p ^ n) (hn : n ≠ 0)
    (hp : 1 < p) (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β)
    (c : Fin d → fixedField K p m) (j : Fin d) :
    (hβ.stageBasis hK hn hp hmd).coord (∑ i, β i * (c i : K)) j = c j :=
  RelativePacking.coord_pack (RelativeBasis.traceDualOf hK hn hp hmd hβ) (fun i => (c i).2) j

/-- **Every element of the stage's top is a combination** of an independent family. -/
theorem StageIndependent.exists_eq_sum (hK : Fintype.card K = p ^ n) (hn : n ≠ 0)
    (hp : 1 < p) (hmd : m * d ∣ n) {β : Fin d → K} (hβ : StageIndependent p m d β) {x : K}
    (hx : x ∈ fixedField K p (m * d)) : ∃ c : Fin d → fixedField K p m, x = ∑ i, β i * (c i : K) := by
  let b := hβ.basis hK hn hp hmd
  refine ⟨b.repr ⟨x, hx⟩, ?_⟩
  have h := congrArg (fun y : fixedField K p (m * d) => (y : K)) (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, stageAlgebra_smul_coe] at h
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, hβ.basis_apply hK hn hp hmd i]

end Stage

end GordieHowe.RelativePacking
