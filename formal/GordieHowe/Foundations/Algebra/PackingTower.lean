-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.FiniteFieldStages
public import GordieHowe.Headline

@[expose] public section

/-!
# Unpacking along a tower of subfields through the product basis

For subfields `A ⊆ B ⊆ T` of a field `K`, with `A = F_{p^m}` the fixed field of `φ = x ↦ x^(p^m)`
and `B = F_{p^(m d')}`, a basis `a` of `B` over `A` and a basis `b` of `T` over `B`, each with its
trace-dual basis (`StageBasis`), the products `a_i b_j`, indexed `j d' + i` (ordered by `j`, then
`i`; Mathlib's `finProdFinEquiv` on `(j, i)`), are a basis of `T` over `A` with trace-dual basis
`a*_i b*_j` (`StageBasis.tower`), and decoding through the product basis is decoding through `b`
followed by decoding through `a` on each coordinate (`StageBasis.coord_tower`). The paper's
`lem:unpack-tower` (`StageBasis.unpack_tower`).

The proof is the paper's: the trace is transitive, `Tr_{T/A} = Tr_{B/A} ∘ Tr_{T/B}`
(`relTrace_tower`, reindexing the sum of Frobenius powers), and `Tr_{T/B}` is `B`-linear (`relTrace_mul_left`).

The decoding identity (`RelativeBasis.coord_tower`) needs only that the dual basis of `a` lies in
`B`; it holds for every word of `K`.
-/

namespace GordieHowe

open RelativePacking

namespace RelativePacking

variable {K : Type*} [Field K] {p : ℕ} [ExpChar K p] {m m' d d' : ℕ}

/-- **`φ_{p^(m a)}^k` is `φ_{p^m}^(a k)`.** -/
theorem phi_mul_left (a k : ℕ) (x : K) : phi p (m * a) k x = phi p m (a * k) x := by
  rw [phi_def, phi_def, mul_assoc]

/-- **Membership in `F_{p^(m a)}` is being fixed by `φ_{p^m}^a`.** -/
theorem mem_fixedField_mul_iff {a : ℕ} {x : K} : x ∈ fixedField K p (m * a) ↔ phi p m a x = x := by
  rw [mem_fixedField_iff_pow, phi_def]

/-- **Transitivity of the trace** in the order of the product index `finProdFinEquiv (j, i)`,
`j < d`, `i < d'`: `Tr_{F_{p^(m d' d)}/F_{p^m}} = Tr_{F_{p^(m d')}/F_{p^m}} ∘
Tr_{F_{p^(m d' d)}/F_{p^(m d')}}` (`relTrace_tower`, whose degree is written `d' d`). -/
theorem relTrace_tower_mul (x : K) :
    relTrace p m (d * d') x = relTrace p m d' (relTrace p (m * d') d x) := by
  have h := relTrace_tower (p := p) (m₁ := m) (D₁ := d') (D₂ := d) rfl x
  rwa [Nat.mul_comm d' d] at h

/-- **The product of two relative bases** of `B/A` (`a`, with its basis and dual basis in
`B = F_{p^m'}`, `m' = m d'`) and `T/B` (`b`): basis `a_i b_j` and dual basis `a*_i b*_j` at the
index `finProdFinEquiv (j, i) = j d' + i`. -/
def RelativeBasis.tower (a : RelativeBasis K p m d') (b : RelativeBasis K p m' d)
    (hm : m' = m * d') (haβ : ∀ i, a.β i ∈ fixedField K p m')
    (hadual : ∀ i, a.dual i ∈ fixedField K p m') : RelativeBasis K p m (d * d') where
  β k := a.β (finProdFinEquiv.symm k).2 * b.β (finProdFinEquiv.symm k).1
  dual k := a.dual (finProdFinEquiv.symm k).2 * b.dual (finProdFinEquiv.symm k).1
  trace_dual k l := by
    subst hm
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective l
    simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    rw [relTrace_tower_mul (d := d) (d' := d'),
      show a.dual i * b.dual j * (a.β i' * b.β j') = a.dual i * a.β i' * (b.dual j * b.β j') by ring,
      relTrace_mul_left ((fixedField K p (m * d')).mul_mem (hadual i) (haβ i')), b.trace_dual]
    by_cases hj : j = j'
    · simp only [hj, ↓reduceIte, mul_one, a.trace_dual, true_and]
    · simp only [hj, ↓reduceIte, mul_zero, false_and, relTrace_zero]

variable (a : RelativeBasis K p m d') (b : RelativeBasis K p m' d) (hm : m' = m * d')
  (haβ : ∀ i, a.β i ∈ fixedField K p m') (hadual : ∀ i, a.dual i ∈ fixedField K p m')

/-- The product basis at `(j, i)` is `a_i b_j`. -/
theorem RelativeBasis.tower_β (j : Fin d) (i : Fin d') :
    (a.tower b hm haβ hadual).β (finProdFinEquiv (j, i)) = a.β i * b.β j := by
  simp only [RelativeBasis.tower, Equiv.symm_apply_apply]

/-- The product dual basis at `(j, i)` is `a*_i b*_j`. -/
theorem RelativeBasis.tower_dual (j : Fin d) (i : Fin d') :
    (a.tower b hm haβ hadual).dual (finProdFinEquiv (j, i)) = a.dual i * b.dual j := by
  simp only [RelativeBasis.tower, Equiv.symm_apply_apply]

/-- **Decoding through the product basis is decoding through `b`, then through `a`**: coordinate
`(j, i)` of `W` over `A` is coordinate `i` over `A` of coordinate `j` of `W` over `B`, for every
`W ∈ K`. -/
theorem RelativeBasis.coord_tower (W : K) (j : Fin d) (i : Fin d') :
    coord (a.tower b hm haβ hadual) W (finProdFinEquiv (j, i)) = coord a (coord b W j) i := by
  subst hm
  rw [coord, RelativeBasis.tower_dual, relTrace_tower_mul (d := d) (d' := d'), mul_assoc,
    relTrace_mul_left (hadual i)]
  rfl

end RelativePacking

namespace PackingStage

variable {K : Type} [Field K] {p : ℕ} [ExpChar K p] {m m' d d' : ℕ}

/-- The basis of a stage `B < T` lies in `F_{p^(m d)}`, `B = F_{p^m}`. -/
theorem StageBasis.β_mem_fixedField (S : StageBasis K p m d) (j : Fin d) :
    S.β j ∈ fixedField K p (m * d) :=
  mem_fixedField_mul_iff.mpr (S.top_fixed _ (S.β_mem j))

/-- The dual basis of a stage `B < T` lies in `F_{p^(m d)}`, `B = F_{p^m}`. -/
theorem StageBasis.dual_mem_fixedField (S : StageBasis K p m d) (j : Fin d) :
    S.dual j ∈ fixedField K p (m * d) :=
  mem_fixedField_mul_iff.mpr (S.top_fixed _ (S.dual_mem j))

/-- **A stage basis is independent**: its combinations with coefficients in `B` are injective
(decoding inverts them, `coord_pack`), and it lies in `F_{p^(m d)}`. With `|K| = p^n` and
`m d ∣ n` it is a Mathlib basis (`StageIndependent.basis`). -/
theorem StageBasis.stageIndependent (S : StageBasis K p m d) : StageIndependent p m d S.β where
  mem := S.β_mem_fixedField
  injective c c' h := funext fun j => Subtype.ext <| by
    have hc := S.coord_pack (c := fun i => (c i : K)) (fun i => (c i).2) j
    have hc' := S.coord_pack (c := fun i => (c' i : K)) (fun i => (c' i).2) j
    rw [← hc, ← hc']
    exact congrArg (S.coord · j) h

/-- **The product stage basis** of a stage `A < B` (`Sa`, `A = F_{p^m}`, `[B : A] = d'`) and a stage
`B' < T` with `B' = F_{p^m'}`, `m' = m d'` (`Sb`): the stage `A < T` with the product basis
(`RelativeBasis.tower`), `[T : A]` dividing `d d'`. -/
def StageBasis.tower (Sa : StageBasis K p m d') (Sb : StageBasis K p m' d) (hm : m' = m * d') :
    StageBasis K p m (d * d') where
  β k := Sa.β (finProdFinEquiv.symm k).2 * Sb.β (finProdFinEquiv.symm k).1
  dual k := Sa.dual (finProdFinEquiv.symm k).2 * Sb.dual (finProdFinEquiv.symm k).1
  trace_dual := (Sa.toRelativeBasis.tower Sb.toRelativeBasis hm (hm ▸ Sa.β_mem_fixedField)
    (hm ▸ Sa.dual_mem_fixedField)).trace_dual
  top := Sb.top
  top_fixed y hy := by
    subst hm
    rw [show d * d' = d' * d from Nat.mul_comm d d', ← phi_mul_left]
    exact Sb.top_fixed y hy
  base_le := (hm ▸ fixedField_le_mul m d').trans Sb.base_le
  β_mem k := Sb.top.mul_mem (Sb.base_le (hm ▸ Sa.β_mem_fixedField _)) (Sb.β_mem _)
  dual_mem k := Sb.top.mul_mem (Sb.base_le (hm ▸ Sa.dual_mem_fixedField _)) (Sb.dual_mem _)

variable (Sa : StageBasis K p m d') (Sb : StageBasis K p m' d) (hm : m' = m * d')

/-- The top of the product stage is the top of `Sb`. -/
theorem StageBasis.tower_top : (Sa.tower Sb hm).top = Sb.top :=
  rfl

/-- The product basis at `(j, i)` is `a_i b_j`. -/
theorem StageBasis.tower_β (j : Fin d) (i : Fin d') :
    (Sa.tower Sb hm).β (finProdFinEquiv (j, i)) = Sa.β i * Sb.β j := by
  simp only [StageBasis.tower, Equiv.symm_apply_apply]

/-- The product dual basis at `(j, i)` is `a*_i b*_j`. -/
theorem StageBasis.tower_dual (j : Fin d) (i : Fin d') :
    (Sa.tower Sb hm).dual (finProdFinEquiv (j, i)) = Sa.dual i * Sb.dual j := by
  simp only [StageBasis.tower, Equiv.symm_apply_apply]

/-- **Decoding through the product stage** at `(j, i)` is decoding through `Sb` at `j`, then through
`Sa` at `i`, for every word `W ∈ K`. -/
theorem StageBasis.coord_tower (W : K) (j : Fin d) (i : Fin d') :
    (Sa.tower Sb hm).coord W (finProdFinEquiv (j, i)) = Sa.coord (Sb.coord W j) i :=
  RelativeBasis.coord_tower Sa.toRelativeBasis Sb.toRelativeBasis hm (hm ▸ Sa.β_mem_fixedField)
    (hm ▸ Sa.dual_mem_fixedField) W j i

/-- **The conclusions of the paper's `lem:unpack-tower`** for the stages `Sa` (`A < B`, `[B : A] =
d'`) and `Sb` (`B < T`, `[T : B] = d`, `B = F_{p^m'}`, `hm : m' = m d'`): the products `a_i b_j` at index `finProdFinEquiv (j, i)`
(ordered by `j`, then `i`) are a basis of `T` over `A` (`independent`, `top`), whose dual basis is
`a*_i b*_j` (`β_apply`, `dual_apply`, `trace_dual`), and decoding through it is decoding through `b`
followed by decoding through `a` componentwise (`unpack`). -/
structure UnpacksTower : Prop where
  /-- The basis at `(j, i)` is `a_i b_j`. -/
  β_apply : ∀ j i, (Sa.tower Sb hm).β (finProdFinEquiv (j, i)) = Sa.β i * Sb.β j
  /-- The dual basis at `(j, i)` is `a*_i b*_j`. -/
  dual_apply : ∀ j i, (Sa.tower Sb hm).dual (finProdFinEquiv (j, i)) = Sa.dual i * Sb.dual j
  /-- The products lie in `T`. -/
  top : ∀ k, (Sa.tower Sb hm).β k ∈ Sb.top
  /-- The products are independent over `A`. -/
  independent : StageIndependent p m (d * d') (Sa.tower Sb hm).β
  /-- The products of the duals are the trace-dual basis over `A`. -/
  trace_dual : ∀ k l, relTrace p m (d * d') ((Sa.tower Sb hm).dual k * (Sa.tower Sb hm).β l) =
    if k = l then 1 else 0
  /-- `unpack_{T/A} = unpack_{B/A} ∘ unpack_{T/B}`, componentwise. -/
  unpack : ∀ (W : K) j i, (Sa.tower Sb hm).coord W (finProdFinEquiv (j, i)) =
    Sa.coord (Sb.coord W j) i

/-- **Paper `lem:unpack-tower`** (transitivity of unpacking): for subfields `A ⊆ B ⊆ T` of `K`,
`A = F_{p^m}`, `B = F_{p^m'}` with `m' = m d'`, a basis of `B` over `A` and a basis of `T` over `B` with their
dual bases (`Sa`, `Sb`), the products `a_i b_j`, ordered by `j` and then `i`, form a basis of `T`
over `A` with dual basis `a*_i b*_j`, and for this basis `unpack_{T/A} = unpack_{B/A} ∘ unpack_{T/B}`
with `unpack_{B/A}` applied componentwise. In a finite `K` of `p^n` elements with `m d d' ∣ n` the
independent family is a Mathlib basis of `F_{p^(m d d')}` over `F_{p^m}` (`StageIndependent.basis`). -/
@[headline]
theorem unpack_tower : UnpacksTower Sa Sb hm where
  β_apply := Sa.tower_β Sb hm
  dual_apply := Sa.tower_dual Sb hm
  top := (Sa.tower Sb hm).β_mem
  independent := (Sa.tower Sb hm).stageIndependent
  trace_dual := (Sa.tower Sb hm).trace_dual
  unpack := Sa.coord_tower Sb hm

end PackingStage

end GordieHowe
