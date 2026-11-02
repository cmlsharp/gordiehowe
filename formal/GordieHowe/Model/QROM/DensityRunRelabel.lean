-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.CohTest

@[expose] public section

/-!
# Relabelling the work register of a density-matrix run

Two density-matrix runs of the compressed-oracle simulation (`densityRun`) whose Kraus operators
agree along a permutation `τ` of the work register, on the basis states whose work register lies in
a set `S` that the first family keeps, are related by `τ`: the second run from the relabelled
initial state is the relabelled first run (`densityRun_relabel`). The simulated query leaves the
work register alone, so it commutes with `τ` (`simQueryKernel_simWorkPerm`).

- `simWorkPerm`: a permutation of the work register on the simulation register.
- `hadamardKernel_simWorkPerm`, `decKernel_simWorkPerm`, `phaseKernel_simWorkPerm`,
  `simQueryKernel_simWorkPerm`: the kernels of the simulated query are invariant (they keep the
  work register, `simQueryKernel_work`).
- `KrausMap.apply_submatrix_of_op`, `KrausMap.apply_supported`: a Kraus map along a permutation,
  and on a set of basis states.
- `densityRun_relabel`: the two runs.
-/

open Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.QROM

open GordieHowe.Quantum

/-! ### Kraus maps along a permutation -/

namespace KrausMapRelabel

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **Two Kraus maps that agree along a permutation** `π` on the columns in `S`: on a matrix
supported on `S × S`, the second applied to the relabelled matrix is the relabelled first. -/
theorem apply_submatrix_of_op (K K' : KrausMap R ι ι) (π : Equiv.Perm ι) (S : Set ι)
    (hop : ∀ r a b, b ∈ S → K'.op r (π a) (π b) = K.op r a b) (M : Matrix ι ι ℂ)
    (hM : ∀ a b, M a b ≠ 0 → a ∈ S ∧ b ∈ S) :
    K' (M.submatrix π.symm π.symm) = (K M).submatrix π.symm π.symm := by
  ext x y
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp π]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hab : M a b = 0
  · simp [hab]
  · obtain ⟨ha, hb⟩ := hM a b hab
    have hx : K'.op r x (π a) = K.op r (π.symm x) a := by
      conv_lhs => rw [← π.apply_symm_apply x]
      exact hop r _ _ ha
    have hy : K'.op r y (π b) = K.op r (π.symm y) b := by
      conv_lhs => rw [← π.apply_symm_apply y]
      exact hop r _ _ hb
    rw [hx, hy]

/-- **A Kraus map that keeps `S`** (on the columns in `S`, its rows are in `S`) maps a matrix
supported on `S × S` to one. -/
theorem apply_supported (K : KrausMap R ι ι) (S : Set ι)
    (hK : ∀ r a b, b ∈ S → K.op r a b ≠ 0 → a ∈ S) (M : Matrix ι ι ℂ)
    (hM : ∀ a b, M a b ≠ 0 → a ∈ S ∧ b ∈ S) :
    ∀ a b, (K M) a b ≠ 0 → a ∈ S ∧ b ∈ S := by
  intro a b h
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  rw [Finset.sum_mul] at hc
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have h3 := right_ne_zero_of_mul hd
  obtain ⟨hdS, hcS⟩ := hM d c h2
  refine ⟨hK r a d hdS h1, hK r b c hcS fun h0 => h3 (by rw [h0, star_zero])⟩

end KrausMapRelabel

/-! ### The simulated query along a permutation of the work register -/

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B)

section Kernels

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- **A permutation of the work register on the simulation register.** -/
def simWorkPerm (σ : Equiv.Perm W) : Equiv.Perm (SimRegister W I J m t) :=
  (σ.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

theorem simWorkPerm_apply (σ : Equiv.Perm W) (b : SimRegister W I J m t) :
    simWorkPerm σ b = ((σ b.1.1, b.1.2), b.2) :=
  rfl

omit [Fintype W] in
theorem hadamardKernel_simWorkPerm (σ : Equiv.Perm W) (b' b : SimRegister W I J m t) :
    hadamardKernel W t (simWorkPerm σ b') (simWorkPerm σ b) = hadamardKernel W t b' b := by
  simp only [hadamardKernel, simWorkPerm_apply, σ.injective.eq_iff]

omit [Fintype W] in
theorem decKernel_simWorkPerm (σ : Equiv.Perm W) (b' b : SimRegister W I J m t) :
    decKernel e W t (simWorkPerm σ b') (simWorkPerm σ b) = decKernel e W t b' b := by
  obtain ⟨⟨w', q'⟩, s'⟩ := b'
  obtain ⟨⟨w, q⟩, s⟩ := b
  simp only [decKernel, simWorkPerm_apply, Prod.mk.injEq, σ.injective.eq_iff]
  rfl

omit [DecidableEq I] [DecidableEq J] [Fintype W] in
theorem phaseKernel_simWorkPerm (σ : Equiv.Perm W) (b' b : SimRegister W I J m t) :
    phaseKernel e W t (simWorkPerm σ b') (simWorkPerm σ b) = phaseKernel e W t b' b := by
  obtain ⟨⟨w', q'⟩, s'⟩ := b'
  obtain ⟨⟨w, q⟩, s⟩ := b
  simp only [phaseKernel, simWorkPerm_apply, Prod.mk.injEq, σ.injective.eq_iff]

/-- A product kernel of kernels invariant under a permutation is invariant. -/
theorem mulKernel_perm {κ : Type*} [Fintype κ] (π : Equiv.Perm κ) {K₁ K₂ : κ → κ → ℂ}
    (h₁ : ∀ a b, K₁ (π a) (π b) = K₁ a b) (h₂ : ∀ a b, K₂ (π a) (π b) = K₂ a b) (a b : κ) :
    ∑ c, K₁ (π a) c * K₂ c (π b) = ∑ c, K₁ a c * K₂ c b := by
  rw [← Equiv.sum_comp π]
  simp only [h₁, h₂]

/-- **The kernel of the simulated query is invariant under a permutation of the work
register.** -/
theorem simQueryKernel_simWorkPerm (σ : Equiv.Perm W) (b' b : SimRegister W I J m t) :
    simQueryKernel e W t (simWorkPerm σ b') (simWorkPerm σ b) = simQueryKernel e W t b' b := by
  have h4 : ∀ a b : SimRegister W I J m t,
      ∑ c, decKernel e W t (simWorkPerm σ a) c * hadamardKernel W t c (simWorkPerm σ b) =
        ∑ c, decKernel e W t a c * hadamardKernel W t c b :=
    mulKernel_perm _ (decKernel_simWorkPerm e σ) (hadamardKernel_simWorkPerm σ)
  have h3 : ∀ a b : SimRegister W I J m t,
      ∑ c, phaseKernel e W t (simWorkPerm σ a) c *
        ∑ c', decKernel e W t c c' * hadamardKernel W t c' (simWorkPerm σ b) =
      ∑ c, phaseKernel e W t a c * ∑ c', decKernel e W t c c' * hadamardKernel W t c' b :=
    mulKernel_perm (K₂ := fun i j => ∑ c', decKernel e W t i c' * hadamardKernel W t c' j) _
      (phaseKernel_simWorkPerm e σ) h4
  have h2 : ∀ a b : SimRegister W I J m t,
      ∑ c, decKernel e W t (simWorkPerm σ a) c * ∑ c₁, phaseKernel e W t c c₁ *
        ∑ c', decKernel e W t c₁ c' * hadamardKernel W t c' (simWorkPerm σ b) =
      ∑ c, decKernel e W t a c * ∑ c₁, phaseKernel e W t c c₁ *
        ∑ c', decKernel e W t c₁ c' * hadamardKernel W t c' b :=
    mulKernel_perm (K₂ := fun i j => ∑ c₁, phaseKernel e W t i c₁ *
      ∑ c', decKernel e W t c₁ c' * hadamardKernel W t c' j) _ (decKernel_simWorkPerm e σ) h3
  exact mulKernel_perm (K₂ := fun i j => ∑ c₁, decKernel e W t i c₁ *
    ∑ c₂, phaseKernel e W t c₁ c₂ * ∑ c', decKernel e W t c₂ c' * hadamardKernel W t c' j) _
    (hadamardKernel_simWorkPerm σ) h2 b' b

end Kernels

/-! ### The density-matrix run along a permutation of the work register -/

section Run

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}

/-- **The density-matrix runs along a permutation of the work register**: for Kraus maps `K'` that
agree with `K` along `τ` on the basis states whose work register lies in `S` (`hop`), for `K` that
keep `S` (`hK`), and for an initial state supported on `S`, the run of `K'` from the relabelled
initial state is the relabelled run of `K`, and the run of `K` stays supported on `S`. -/
theorem densityRun_relabel (τ : Equiv.Perm V) (S : Set V)
    (K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (hop : ∀ i r (a b : QueryReg V 1 (Bits m) (BitStr I J)), b.1 ∈ S →
      (K' i).op r ((τ.prodCongr (Equiv.refl _)) a) ((τ.prodCongr (Equiv.refl _)) b) =
        (K i).op r a b)
    (hK : ∀ i r (a b : QueryReg V 1 (Bits m) (BitStr I J)), b.1 ∈ S → (K i).op r a b ≠ 0 →
      a.1 ∈ S)
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (hρ : ∀ a b, ρ₀ a b ≠ 0 → a.1 ∈ S ∧ b.1 ∈ S) :
    ∀ n, densityRun e K' (ρ₀.submatrix (τ.prodCongr (Equiv.refl _)).symm
        (τ.prodCongr (Equiv.refl _)).symm) n =
        (densityRun e K ρ₀ n).submatrix (simWorkPerm τ).symm (simWorkPerm τ).symm ∧
      ∀ a b, densityRun e K ρ₀ n a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S := by
  set π := simWorkPerm (I := I) (J := J) (m := m) (t := t) τ
  have hopT : ∀ i r (a b : SimRegister V I J m t), b ∈ {p | p.1.1 ∈ S} →
      ((K' i).tensorId (Slots I J m t)).op r (π a) (π b) =
        ((K i).tensorId (Slots I J m t)).op r a b := fun i r a b hb => by
    simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply]
    rw [show (π a).1 = (τ.prodCongr (Equiv.refl _)) a.1 from rfl,
      show (π b).1 = (τ.prodCongr (Equiv.refl _)) b.1 from rfl, hop i r a.1 b.1 hb]
    rfl
  have hKT : ∀ i r (a b : SimRegister V I J m t), b ∈ {p | p.1.1 ∈ S} →
      ((K i).tensorId (Slots I J m t)).op r a b ≠ 0 → a ∈ {p | p.1.1 ∈ S} := fun i r a b hb h => by
    simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply] at h
    exact hK i r a.1 b.1 hb (left_ne_zero_of_mul h)
  have hstep : ∀ (k : ℕ) (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S) →
      KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) k (M.submatrix π.symm π.symm) =
        (KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M).submatrix π.symm π.symm ∧
      ∀ a b, KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M a b ≠ 0 →
        a.1.1 ∈ S ∧ b.1.1 ∈ S := fun k M hM => by
    unfold KrausMap.stepAt
    split_ifs with hk
    · exact ⟨KrausMapRelabel.apply_submatrix_of_op _ _ π {p : SimRegister V I J m t | p.1.1 ∈ S}
        (hopT ⟨k, hk⟩) M hM,
        KrausMapRelabel.apply_supported _ {p : SimRegister V I J m t | p.1.1 ∈ S} (hKT ⟨k, hk⟩) M
          hM⟩
    · exact ⟨rfl, hM⟩
  have hQ : (Matrix.of (simQueryKernel e V t)).submatrix π.symm π.symm =
      Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    conv_rhs => rw [← π.apply_symm_apply a, ← π.apply_symm_apply b]
    exact (simQueryKernel_simWorkPerm e τ _ _).symm
  have hquery : ∀ M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ,
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S) →
      Matrix.of (simQueryKernel e V t) * M.submatrix π.symm π.symm *
          (Matrix.of (simQueryKernel e V t))ᴴ =
        (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ).submatrix
          π.symm π.symm ∧
      ∀ a b, (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
        Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a b ≠ 0 →
        a.1.1 ∈ S ∧ b.1.1 ∈ S := fun M hM => by
    refine ⟨?_, fun a b h => ?_⟩
    · rw [← Matrix.submatrix_mul_equiv _ _ _ π.symm, ← Matrix.submatrix_mul_equiv _ _ _ π.symm,
        ← Matrix.conjTranspose_submatrix, hQ]
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply] at h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hc)
      have h1 := simQueryKernel_work e (left_ne_zero_of_mul hd)
      have h2 := simQueryKernel_work e (fun h0 => right_ne_zero_of_mul hc (by rw [h0, star_zero]))
      obtain ⟨hdS, hcS⟩ := hM d c (right_ne_zero_of_mul hd)
      exact ⟨h1 ▸ hdS, h2 ▸ hcS⟩
  intro n
  induction n with
  | zero =>
    have hi : (ρ₀.submatrix (τ.prodCongr (Equiv.refl _)).symm (τ.prodCongr (Equiv.refl _)).symm ⊗ₖ
        Matrix.single (dbSlots e t (∅ : DB (Bits m) B)) (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ)) =
        (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
          (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ)).submatrix π.symm π.symm := by
      ext a b
      rfl
    have hs : ∀ a b, (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
        (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ)) a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S :=
      fun a b h => hρ a.1 b.1 (left_ne_zero_of_mul (by simpa [Matrix.kroneckerMap_apply] using h))
    obtain ⟨h1, h2⟩ := hstep 0 _ hs
    refine ⟨?_, h2⟩
    simp only [densityRun]
    rw [hi, h1]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨q1, q2⟩ := hquery _ ih2
    obtain ⟨s1, s2⟩ := hstep (n + 1) _ q2
    refine ⟨?_, s2⟩
    simp only [densityRun]
    rw [ih1, q1, s1]

end Run

end GordieHowe.QROM
