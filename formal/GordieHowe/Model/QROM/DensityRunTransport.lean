-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandCohRelabel

@[expose] public section

/-!
# Two density-matrix runs related by permutations carried between the steps

Two families of Kraus maps `K'` and `K` on `QueryReg V 1 (Bits m) (BitStr I J)`, with permutations
`P i` carried into step `i` (`P 0 = 1`): step `i` of `K'` read after `P i` is step `i` of `K`
followed by `P (i + 1)`, on the states supported on `S i`, which `K` carries to `S (i + 1)`. When
each `P (i + 1)` commutes with the simulated query and the query keeps the supports, the
density-matrix run of `K'` (`densityRun`) is that of `K` relabelled by the carried permutation
(`densityRun_transport`); at the end, with `P (t + 1) = 1`, the runs are equal.

The simulated query commutes with a permutation that keeps the query pair and acts on the work
register through the query input (`QueryPairFix`, `simQueryKernel_queryPairFix`).

- `QueryPairFix`, `simQueryKernel_queryPairFix`.
- `simPerm'`: a permutation of the query registers on the simulation register.
- `KrausMapRelabel.Rel2`, `KrausMapRelabel.apply_submatrix_of_rel2`: Kraus maps related by two
  permutations; `Supp`, `tensorId_apply_submatrix_of`, `tensorId_supp_of`: channel identities and
  supports through the identity on a second factor.
- `densityRun_transport`.
-/

open Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B)

/-! ### Permutations that keep the query pair -/

section Kernels

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

omit [Fintype W] [DecidableEq W] in
/-- **A permutation that keeps the query pair** and acts on the work register through a
permutation `τ x` chosen by the query input `x`. -/
def QueryPairFix {X Y : Type} (σ : Equiv.Perm (QueryReg W 1 X Y)) : Prop :=
  ∃ τ : X → Equiv.Perm W, ∀ p, σ p = (τ (p.2 0).1 p.1, p.2)

/-- A permutation of the query registers on the simulation register. -/
def simPerm' (σ : Equiv.Perm (QueryReg W 1 (Bits m) (BitStr I J))) :
    Equiv.Perm (SimRegister W I J m t) :=
  σ.prodCongr (Equiv.refl _)

theorem simPerm'_apply (σ : Equiv.Perm (QueryReg W 1 (Bits m) (BitStr I J)))
    (b : SimRegister W I J m t) : simPerm' σ b = (σ b.1, b.2) :=
  rfl

variable {σ : Equiv.Perm (QueryReg W 1 (Bits m) (BitStr I J))}

omit [Fintype W] in
theorem hadamardKernel_queryPairFix (hσ : QueryPairFix σ) (b' b : SimRegister W I J m t) :
    hadamardKernel W t (simPerm' σ b') (simPerm' σ b) = hadamardKernel W t b' b := by
  obtain ⟨τ, hτ⟩ := hσ
  simp only [hadamardKernel, simPerm'_apply, hτ, qIn, qAns]
  by_cases hx : (b'.1.2 0).1 = (b.1.2 0).1
  · simp only [hx, (τ _).injective.eq_iff]
  · simp [hx]

omit [Fintype W] in
theorem decKernel_queryPairFix (hσ : QueryPairFix σ) (b' b : SimRegister W I J m t) :
    decKernel e W t (simPerm' σ b') (simPerm' σ b) = decKernel e W t b' b := by
  obtain ⟨τ, hτ⟩ := hσ
  have hq : ∀ p : QueryReg W 1 (Bits m) (BitStr I J), qIn (σ p) = qIn p := fun p => by
    rw [hτ]
  simp only [decKernel, simPerm'_apply, σ.injective.eq_iff, hq]

omit [DecidableEq I] [DecidableEq J] [Fintype W] in
theorem phaseKernel_queryPairFix (hσ : QueryPairFix σ) (b' b : SimRegister W I J m t) :
    phaseKernel e W t (simPerm' σ b') (simPerm' σ b) = phaseKernel e W t b' b := by
  obtain ⟨τ, hτ⟩ := hσ
  have hq : ∀ p : QueryReg W 1 (Bits m) (BitStr I J), qIn (σ p) = qIn p := fun p => by
    rw [hτ]
  have ha : ∀ p : QueryReg W 1 (Bits m) (BitStr I J), qAns (σ p) = qAns p := fun p => by
    rw [hτ]
  unfold phaseKernel
  by_cases h : b' = b
  · subst h
    simp only [if_true, simPerm'_apply, hq, ha]
  · rw [if_neg ((simPerm' (t := t) σ).injective.ne h), if_neg h]

/-- **The kernel of the simulated query is invariant under a permutation that keeps the query
pair** (`QueryPairFix`). -/
theorem simQueryKernel_queryPairFix (hσ : QueryPairFix σ) (b' b : SimRegister W I J m t) :
    simQueryKernel e W t (simPerm' σ b') (simPerm' σ b) = simQueryKernel e W t b' b := by
  have h4 : ∀ a b : SimRegister W I J m t,
      ∑ c, decKernel e W t (simPerm' σ a) c * hadamardKernel W t c (simPerm' σ b) =
        ∑ c, decKernel e W t a c * hadamardKernel W t c b :=
    mulKernel_perm _ (decKernel_queryPairFix e hσ) (hadamardKernel_queryPairFix hσ)
  have h3 : ∀ a b : SimRegister W I J m t,
      ∑ c, phaseKernel e W t (simPerm' σ a) c *
        ∑ c', decKernel e W t c c' * hadamardKernel W t c' (simPerm' σ b) =
      ∑ c, phaseKernel e W t a c * ∑ c', decKernel e W t c c' * hadamardKernel W t c' b :=
    mulKernel_perm (K₂ := fun i j => ∑ c', decKernel e W t i c' * hadamardKernel W t c' j) _
      (phaseKernel_queryPairFix e hσ) h4
  have h2 : ∀ a b : SimRegister W I J m t,
      ∑ c, decKernel e W t (simPerm' σ a) c * ∑ c₁, phaseKernel e W t c c₁ *
        ∑ c', decKernel e W t c₁ c' * hadamardKernel W t c' (simPerm' σ b) =
      ∑ c, decKernel e W t a c * ∑ c₁, phaseKernel e W t c c₁ *
        ∑ c', decKernel e W t c₁ c' * hadamardKernel W t c' b :=
    mulKernel_perm (K₂ := fun i j => ∑ c₁, phaseKernel e W t i c₁ *
      ∑ c', decKernel e W t c₁ c' * hadamardKernel W t c' j) _ (decKernel_queryPairFix e hσ) h3
  exact mulKernel_perm (K₂ := fun i j => ∑ c₁, decKernel e W t i c₁ *
    ∑ c₂, phaseKernel e W t c₁ c₂ * ∑ c', decKernel e W t c₂ c' * hadamardKernel W t c' j) _
    (hadamardKernel_queryPairFix hσ) h2 b' b

end Kernels

/-! ### Kraus maps related by two permutations -/

namespace KrausMapRelabel

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **Two Kraus maps related by the permutations `σ'` after and `σ` before**, on the columns in
`S`: `K'.op r (σ' a) (σ b) = K.op r a b`. -/
def Rel2 (σ' σ : Equiv.Perm ι) (S : Set ι) (K' K : KrausMap R ι ι) : Prop :=
  ∀ r a b, b ∈ S → K'.op r (σ' a) (σ b) = K.op r a b

/-- **Two Kraus maps related by two permutations**: on a matrix supported on `S × S`, the first
applied to the matrix relabelled by `σ` is the second applied to it, relabelled by `σ'`. -/
theorem apply_submatrix_of_rel2 {K' K : KrausMap R ι ι} {σ' σ : Equiv.Perm ι} {S : Set ι}
    (hop : Rel2 σ' σ S K' K) (M : Matrix ι ι ℂ) (hM : ∀ a b, M a b ≠ 0 → a ∈ S ∧ b ∈ S) :
    K' (M.submatrix σ.symm σ.symm) = (K M).submatrix σ'.symm σ'.symm := by
  ext x y
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hab : M a b = 0
  · simp [hab]
  · obtain ⟨ha, hb⟩ := hM a b hab
    have hx : K'.op r x (σ a) = K.op r (σ'.symm x) a := by
      conv_lhs => rw [← σ'.apply_symm_apply x]
      exact hop r _ _ ha
    have hy : K'.op r y (σ b) = K.op r (σ'.symm y) b := by
      conv_lhs => rw [← σ'.apply_symm_apply y]
      exact hop r _ _ hb
    rw [hx, hy]

end KrausMapRelabel

/-! ### The density-matrix runs with carried permutations -/

section Run

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}

/-- **A matrix supported on `S × S`**: its nonzero entries have both indices in `S`. -/
def Supp {ι : Type*} (S : Set ι) (M : Matrix ι ι ℂ) : Prop :=
  ∀ a b, M a b ≠ 0 → a ∈ S ∧ b ∈ S

/-- **A channel identity with carried permutations, tensored with the identity**: if `K'` read
after `σ` is `K` followed by `σ'` on the matrices supported on `S`, the same holds for the maps
tensored with the identity on `D`, on the matrices supported on the basis states whose first part
lies in `S`. -/
theorem tensorId_apply_submatrix_of {R R' : Type*} {ι D : Type} [Fintype R] [Fintype R'] [Fintype ι]
    [DecidableEq ι] [Fintype D] [DecidableEq D] {K' : KrausMap R' ι ι} {K : KrausMap R ι ι}
    {σ' σ : Equiv.Perm ι} {S : Set ι}
    (h : ∀ ρ, Supp S ρ → K' (ρ.submatrix σ.symm σ.symm) = (K ρ).submatrix σ'.symm σ'.symm)
    (M : Matrix (ι × D) (ι × D) ℂ) (hM : Supp {p | p.1 ∈ S} M) :
    (K'.tensorId D) (M.submatrix (σ.prodCongr (Equiv.refl D)).symm
        (σ.prodCongr (Equiv.refl D)).symm) =
      ((K.tensorId D) M).submatrix (σ'.prodCongr (Equiv.refl D)).symm
        (σ'.prodCongr (Equiv.refl D)).symm := by
  ext ⟨k, d⟩ ⟨k', d'⟩
  rw [KrausMap.tensorId_apply_submatrix, Matrix.submatrix_apply]
  change _ = (K.tensorId D) M (σ'.symm k, d) (σ'.symm k', d')
  rw [KrausMap.tensorId_apply_submatrix]
  have hb : Supp S (M.submatrix (·, d) (·, d')) := fun a b hab => hM _ _ hab
  rw [show (M.submatrix (σ.prodCongr (Equiv.refl D)).symm
      (σ.prodCongr (Equiv.refl D)).symm).submatrix (·, d) (·, d') = (M.submatrix (·, d) (·, d')).submatrix σ.symm σ.symm from rfl, h _ hb]
  rfl

/-- **Supports through a map tensored with the identity.** -/
theorem tensorId_supp_of {R : Type*} {ι D : Type} [Fintype R] [Fintype ι] [DecidableEq ι]
    [Fintype D] [DecidableEq D] {K : KrausMap R ι ι} {S S' : Set ι} (h : ∀ ρ, Supp S ρ → Supp S' (K ρ))
    (M : Matrix (ι × D) (ι × D) ℂ) (hM : Supp {p | p.1 ∈ S} M) :
    Supp {p | p.1 ∈ S'} ((K.tensorId D) M) := by
  rintro ⟨k, d⟩ ⟨k', d'⟩ hne
  rw [KrausMap.tensorId_apply_submatrix] at hne
  exact h _ (fun a b hab => hM _ _ hab) k k' hne

/-- **Two density-matrix runs with permutations carried between the steps**: for Kraus maps `K'`
whose step `i`, read after `P i`, is step `i` of `K` followed by `P (i + 1)` on the matrices
supported on `S i` (`h1`), `K` carrying `S i` to `S (i + 1)` (`h2`), the carried permutations
commuting with the simulated query (`hQ`), the query keeping the supports (`hSQ`), `P 0 = 1` and
an initial state supported on `S 0`: the run of `K'` is the run of `K` relabelled by the carried
permutation, and the run of `K` stays supported. -/
theorem densityRun_transport {R' : Type} [Fintype R']
    (K' : Fin (t + 1) → KrausMap R' (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (P : ℕ → Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J)))
    (S : ℕ → Set (QueryReg V 1 (Bits m) (BitStr I J))) (hP0 : P 0 = 1)
    (h1 : ∀ (i : Fin (t + 1)) ρ, Supp (S i) ρ →
      K' i (ρ.submatrix (P i).symm (P i).symm) =
        (K i ρ).submatrix (P (i + 1)).symm (P (i + 1)).symm)
    (h2 : ∀ (i : Fin (t + 1)) ρ, Supp (S i) ρ → Supp (S (i + 1)) (K i ρ))
    (hQ : ∀ i, QueryPairFix (P (i + 1)))
    (hSQ : ∀ i (b' b : SimRegister V I J m t), simQueryKernel e V t b' b ≠ 0 → b.1 ∈ S (i + 1) →
      b'.1 ∈ S (i + 1))
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (hρ : Supp (S 0) ρ₀) :
    ∀ n ≤ t, densityRun e K' ρ₀ n =
        (densityRun e K ρ₀ n).submatrix (simPerm' (P (n + 1))).symm (simPerm' (P (n + 1))).symm ∧
      Supp {p | p.1 ∈ S (n + 1)} (densityRun e K ρ₀ n) := by
  have hstep : ∀ (k : ℕ) (hk : k < t + 1)
      (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      Supp {p | p.1 ∈ S k} M →
      KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) k
          (M.submatrix (simPerm' (P k)).symm (simPerm' (P k)).symm) =
        (KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M).submatrix
          (simPerm' (P (k + 1))).symm (simPerm' (P (k + 1))).symm ∧
      Supp {p | p.1 ∈ S (k + 1)} (KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M) :=
    fun k hk M hM => by
      rw [KrausMap.stepAt_of_lt _ hk, KrausMap.stepAt_of_lt _ hk]
      exact ⟨tensorId_apply_submatrix_of (h1 ⟨k, hk⟩) M hM, tensorId_supp_of (h2 ⟨k, hk⟩) M hM⟩
  have hquery : ∀ (k : ℕ) (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      Supp {p | p.1 ∈ S (k + 1)} M →
      Matrix.of (simQueryKernel e V t) *
          M.submatrix (simPerm' (P (k + 1))).symm (simPerm' (P (k + 1))).symm *
          (Matrix.of (simQueryKernel e V t))ᴴ =
        (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ).submatrix
          (simPerm' (P (k + 1))).symm (simPerm' (P (k + 1))).symm ∧
      Supp {p | p.1 ∈ S (k + 1)}
        (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
          Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) := fun k M hM => by
    set π := simPerm' (I := I) (J := J) (m := m) (t := t) (P (k + 1))
    have hQk : (Matrix.of (simQueryKernel e V t)).submatrix π.symm π.symm =
        Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.of_apply]
      conv_rhs => rw [← π.apply_symm_apply a, ← π.apply_symm_apply b]
      exact (simQueryKernel_queryPairFix e (hQ k) _ _).symm
    refine ⟨?_, fun a b h => ?_⟩
    · rw [← Matrix.submatrix_mul_equiv _ _ _ π.symm, ← Matrix.submatrix_mul_equiv _ _ _ π.symm,
        ← Matrix.conjTranspose_submatrix, hQk]
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply] at h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hc)
      obtain ⟨hdS, hcS⟩ := hM d c (right_ne_zero_of_mul hd)
      exact ⟨hSQ k a d (left_ne_zero_of_mul hd) hdS,
        hSQ k b c (fun h0 => right_ne_zero_of_mul hc (by rw [h0, star_zero])) hcS⟩
  intro n hn
  induction n with
  | zero =>
    have hi : (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
        (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ)) =
        (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
          (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ)).submatrix (simPerm' (P 0)).symm
          (simPerm' (P 0)).symm := by
      rw [hP0]
      ext a b
      rfl
    have hs : Supp {p | p.1 ∈ S 0} (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
        (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ)) :=
      fun a b h => hρ a.1 b.1 (left_ne_zero_of_mul (by simpa [Matrix.kroneckerMap_apply] using h))
    obtain ⟨h1', h2'⟩ := hstep 0 (by omega) _ hs
    refine ⟨?_, h2'⟩
    simp only [densityRun]
    exact (congrArg (KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) 0) hi).trans h1'
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨q1, q2⟩ := hquery n _ ih2
    obtain ⟨s1, s2⟩ := hstep (n + 1) (by omega) _ q2
    refine ⟨?_, s2⟩
    simp only [densityRun]
    rw [ih1, q1, s1]

end Run

end GordieHowe.QROM
