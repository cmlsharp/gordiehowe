-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftRun

@[expose] public section

/-!
# A query algorithm with request points, its steps read after writes and drops

`simLaw_withSteps_of_write_drop`: a query algorithm with request points on the registers of the
expanded coherent run of `A'` whose steps are its steps read after writes acting as `σ` on the core
register and then after the lifts of permutations `β` of the core's query registers has the law of
the expanded coherent run of `A'` read after `σ` and then `β`.

- `cohLiftQ_trans`, `cohLiftQ_queryWorkPerm`, `cohPrecompPermQ_trans`,
  `cohPrecompPermQ_queryWorkPerm`, `QueryAlg.precompPerm_trans`: the lifts compose.
- `simLaw_steps_transportQ`: `simLaw_steps_of_dilationQ` along an equation of the algorithms.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (k : ℕ)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem cohLiftQ_trans {V : Type} (π₁ π₂ : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) :
    cohLiftQ k (π₁.trans π₂) = (cohLiftQ k π₁).trans (cohLiftQ k π₂) :=
  Equiv.ext fun _ => rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem cohLiftQ_queryWorkPerm {V : Type} (s : Equiv.Perm V) :
    cohLiftQ k (queryWorkPerm (m := m) (I := I) (J := J) s) =
      expBasisPerm k (s.prodCongr (Equiv.refl Bool)) :=
  Equiv.ext fun _ => rfl

section Alg

variable (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C) {O : Type} (A : Alg (Bits m) (BitStr I J) O) (g : Option O → C)

theorem cohPrecompPermQ_trans (σ β : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (i : Fin (A.depth + k + 1)) :
    cohPrecompPermQ k A (fun j => (σ j).trans (β j)) i =
      (cohPrecompPermQ k A σ i).trans (cohPrecompPermQ k A β i) := by
  unfold cohPrecompPermQ
  split_ifs
  · exact cohLiftQ_trans k _ _
  · rfl

theorem cohPrecompPermQ_queryWorkPerm (σ : Fin (A.depth + 1) → Equiv.Perm A.V)
    (i : Fin (A.depth + k + 1)) :
    cohPrecompPermQ k A (fun j => queryWorkPerm (σ j)) i = cohPrecompPerm k A σ i := by
  unfold cohPrecompPermQ cohPrecompPerm
  split_ifs
  · exact cohLiftQ_queryWorkPerm k _
  · rfl

/-- **`simLaw_steps_of_dilationQ` along an equation of the algorithms.** -/
theorem simLaw_steps_transportQ (hA : A.TracePreserving)
    (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E k (A.toQueryAlgCoh.mapOut g) = Q)
    (S : Fin (A.depth + k + 1) →
      QState (QueryReg Q.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg Q.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (QueryAlg.precompPerm
      (hQ ▸ expandCohDilation A g e E k :
        Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
          (Option (A.R ⊕ Bool))) (cohPrecompPermQ k A σ) i)).trans (Q.step i)) :
    simLaw e { Q with step := S } =
      simLaw e (expandAdv e E k ((A.precomp σ).toQueryAlgCoh.mapOut g)) := by
  subst hQ
  exact simLaw_steps_of_dilationQ e E k A g σ hA (expandCohDilation A g e E k) (fun _ => rfl) rfl
    (fun _ => rfl) S hS

/-- The lifts of `σ` through the dilation carried along an equation of the algorithms, between
registers related by `HEq`. -/
theorem precompPermQ_transport_heq
    (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E k (A.toQueryAlgCoh.mapOut g) = Q) (i : Fin (A.depth + k + 1))
    (p : QueryReg Q.W 1 (Bits m) (BitStr I J))
    (p' : QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J))
    (hp : HEq p p') :
    HEq (QueryAlg.precompPerm (hQ ▸ expandCohDilation A g e E k :
        Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
          (Option (A.R ⊕ Bool))) (cohPrecompPermQ k A σ) i p)
      (QueryAlg.precompPerm (expandCohDilation A g e E k) (cohPrecompPermQ k A σ) i p') := by
  subst hQ
  obtain rfl := eq_of_heq hp
  rfl

end Alg

end GordieHowe.QROM

namespace GordieHowe.Quantum

theorem QueryAlg.precompPerm_trans {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] {t : ℕ} {Q : QueryAlg X Y t O} {V Anc R : Type} [Fintype V] [DecidableEq V]
    [Fintype Anc] [Fintype R] (D : Q.Dilation V Anc R)
    (π₁ π₂ : Fin (t + 1) → Equiv.Perm (QueryReg V 1 X Y)) (i : Fin (t + 1)) :
    QueryAlg.precompPerm D (fun j => (π₁ j).trans (π₂ j)) i =
      (QueryAlg.precompPerm D π₁ i).trans (QueryAlg.precompPerm D π₂ i) :=
  Equiv.ext fun p => by
    simp only [QueryAlg.precompPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl

theorem permOp_trans' {ι : Type*} [Fintype ι] (π σ : Equiv.Perm ι) :
    permOp (π.trans σ) = (permOp π).trans (permOp σ) :=
  LinearIsometryEquiv.ext fun _ => rfl

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B)
  {Req' Resp' C : Type}
  (E' : Expansion (Bits m) B C) (k : ℕ) {O' : Type} (A' : Alg (Bits m) (BitStr I J) O')
  (g : Option O' → C) (σ : Fin (A'.depth + 1) → Equiv.Perm A'.V)
  (β : Fin (A'.depth + 1) → Equiv.Perm (QueryReg A'.V 1 (Bits m) (BitStr I J)))

/-- **A query algorithm with request points whose registers are the expanded coherent run of `A'`,
with its steps read after writes acting as `σ` on the core register (`h1`, `h2`) and then after
permutations `B'` acting as the lifts of `β` (`hB`, `hS`)**, has the law of the expanded coherent run of `A'` read after `σ` and then
`β`, for a trace-preserving `A'`. -/
theorem simLaw_withSteps_of_write_drop (hA : A'.TracePreserving)
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req' Resp' (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hG : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = G.withSteps G.step)
    (π' : Fin (A'.depth + k + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hT : QueryReg G.W 1 (Bits m) (BitStr I J) =
      QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J))
    (h1 : ∀ (i : Fin (A'.depth + k + 1)) p (h : (i : ℕ) < A'.depth + 1),
      HEq (π' i p) (cohLiftAt e E' k A' g (σ ⟨i, h⟩) (cast hT p)))
    (h2 : ∀ (i : Fin (A'.depth + k + 1)) p, ¬ (i : ℕ) < A'.depth + 1 → π' i p = p)
    (B' : Fin (A'.depth + k + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hB : ∀ (i : Fin (A'.depth + k + 1)) p,
      HEq (B' i p) (QueryAlg.precompPerm (expandCohDilation A' g e E' k) (cohPrecompPermQ k A' β) i
        (cast hT p)))
    (S : Fin (A'.depth + k + 1) →
      QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (π' i)).trans ((permOp (B' i)).trans (G.step i))) :
    simLaw e (G.withSteps S) =
      simLaw e (expandAdv e E' k ((A'.precomp fun j =>
        (queryWorkPerm (σ j)).trans (β j)).toQueryAlgCoh.mapOut g)) := by
  refine simLaw_steps_transportQ k e E' A' g hA (fun j => (queryWorkPerm (σ j)).trans (β j))
    (G.withSteps G.step) hG S fun i => ?_
  rw [hS i]
  have hπ : π' i = QueryAlg.precompPerm
      (hG ▸ expandCohDilation A' g e E' k :
        (G.withSteps G.step).Dilation (ExpandAdv.ExpansionRegister (X := Bits m) (Y := BitStr I J) k
          (A'.V × Bool)) A'.HaltAnc (Option (A'.R ⊕ Bool)))
      (cohPrecompPermQ k A' fun j => queryWorkPerm (σ j)) i := by
    refine Equiv.ext fun p => ?_
    have he : (cohPrecompPermQ k A' fun j => queryWorkPerm (σ j)) = cohPrecompPerm k A' σ :=
      funext fun i => cohPrecompPermQ_queryWorkPerm k A' σ i
    rw [he]
    by_cases h : (i : ℕ) < A'.depth + 1
    · exact eq_of_heq ((h1 i p h).trans
        (precompPerm_transport_heq e E' k A' g σ _ hG h p _ (cast_heq hT p).symm).symm)
    · exact (h2 i p h).trans (precompPerm_transport_ge' e E' k A' g σ _ hG h p).symm
  have hc : (cohPrecompPermQ k A' fun j => (queryWorkPerm (σ j)).trans (β j)) =
      fun i => (cohPrecompPermQ k A' (fun j => queryWorkPerm (σ j)) i).trans
        (cohPrecompPermQ k A' β i) :=
    funext fun i => cohPrecompPermQ_trans k A' _ _ i
  have hb : B' i = QueryAlg.precompPerm
      (hG ▸ expandCohDilation A' g e E' k :
        (G.withSteps G.step).Dilation (ExpandAdv.ExpansionRegister (X := Bits m) (Y := BitStr I J) k
          (A'.V × Bool)) A'.HaltAnc (Option (A'.R ⊕ Bool))) (cohPrecompPermQ k A' β) i :=
    Equiv.ext fun p => eq_of_heq ((hB i p).trans
      (precompPermQ_transport_heq k e E' A' g β _ hG i p _ (cast_heq hT p).symm).symm)
  rw [hc, QueryAlg.precompPerm_trans, permOp_trans', hπ, hb]
  rfl

/-- **A query algorithm with request points on the registers of the expanded coherent run of
`A'`, with its steps read after writes acting as `σ` on the core register (`h1`, `h2`) and then
after the lifts of `β`** (`hS`), has the law of the expanded coherent run of `A'` read after `σ`
and then `β`, for a trace-preserving `A'`. -/
theorem simLaw_ofQueryAlg_withSteps_drop (hA : A'.TracePreserving)
    (req : Fin (A'.depth + k + 1) → (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W → Req')
    (write : Fin (A'.depth + k + 1) → Option Resp' →
      Equiv.Perm (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W)
    (hrw : ∀ k b w, req k (write k b w) = req k w)
    (π' : Fin (A'.depth + k + 1) →
      Equiv.Perm (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (h1 : ∀ (i : Fin (A'.depth + k + 1)) p (h : (i : ℕ) < A'.depth + 1),
      π' i p = cohLiftAt e E' k A' g (σ ⟨i, h⟩) p)
    (h2 : ∀ (i : Fin (A'.depth + k + 1)) p, ¬ (i : ℕ) < A'.depth + 1 → π' i p = p)
    (S : Fin (A'.depth + k + 1) →
      QState (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
        QState (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (π' i)).trans ((permOp (QueryAlg.precompPerm
      (expandCohDilation A' g e E' k) (cohPrecompPermQ k A' β) i)).trans
        ((expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).step i))) :
    simLaw e ((ReqQueryAlg.ofQueryAlg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)) req write
      hrw).withSteps S) =
      simLaw e (expandAdv e E' k ((A'.precomp fun j =>
        (queryWorkPerm (σ j)).trans (β j)).toQueryAlgCoh.mapOut g)) := by
  refine simLaw_steps_of_dilationQ e E' k A' g (fun j => (queryWorkPerm (σ j)).trans (β j)) hA
    (expandCohDilation A' g e E' k) (fun _ => rfl) rfl (fun _ => rfl) S fun i => ?_
  rw [hS i]
  have hπ : π' i = QueryAlg.precompPerm (expandCohDilation A' g e E' k)
      (cohPrecompPermQ k A' fun j => queryWorkPerm (σ j)) i := by
    refine Equiv.ext fun p => ?_
    have he : (cohPrecompPermQ k A' fun j => queryWorkPerm (σ j)) = cohPrecompPerm k A' σ :=
      funext fun i => cohPrecompPermQ_queryWorkPerm k A' σ i
    rw [he]
    by_cases h : (i : ℕ) < A'.depth + 1
    · exact (h1 i p h).trans (precompPerm_cohPrecompPerm_of_lt e E' k A' g σ h p).symm
    · exact (h2 i p h).trans (precompPerm_cohPrecompPerm_of_ge e E' k A' g σ h p).symm
  have hc : (cohPrecompPermQ k A' fun j => (queryWorkPerm (σ j)).trans (β j)) =
      fun i => (cohPrecompPermQ k A' (fun j => queryWorkPerm (σ j)) i).trans
        (cohPrecompPermQ k A' β i) :=
    funext fun i => cohPrecompPermQ_trans k A' _ _ i
  rw [hc, QueryAlg.precompPerm_trans, permOp_trans', hπ]
  rfl

/-- **A permutation of the core's query registers on the registers of the expanded coherent run
of `A'`**: on the core register and the query register. -/
def cohLiftQAt (π : Equiv.Perm (QueryReg A'.V 1 (Bits m) (BitStr I J))) :
    Equiv.Perm (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) where
  toFun p := (((((π (p.1.1.1.1, p.2)).1, p.1.1.1.2), p.1.1.2), p.1.2), (π (p.1.1.1.1, p.2)).2)
  invFun p := (((((π.symm (p.1.1.1.1, p.2)).1, p.1.1.1.2), p.1.1.2), p.1.2),
    (π.symm (p.1.1.1.1, p.2)).2)
  left_inv p := by
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    rfl
  right_inv p := by
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    rfl

/-- **The lift of `β` on the registers of the expanded coherent run**, at a step of `A'`: `β` on
the core register and the query register. -/
theorem precompPerm_cohPrecompPermQ_of_lt {i : Fin (A'.depth + k + 1)} (h : (i : ℕ) < A'.depth + 1) :
    QueryAlg.precompPerm (expandCohDilation A' g e E' k) (cohPrecompPermQ k A' β) i =
      cohLiftQAt e E' k A' g (β ⟨i, h⟩) := by
  refine Equiv.ext fun p => ?_
  unfold QueryAlg.precompPerm cohPrecompPermQ
  rw [dif_pos h]
  rfl

/-- The lift of `β` after the steps of `A'` is the identity. -/
theorem precompPerm_cohPrecompPermQ_of_ge {i : Fin (A'.depth + k + 1)} (h : ¬ (i : ℕ) < A'.depth + 1) :
    QueryAlg.precompPerm (expandCohDilation A' g e E' k) (cohPrecompPermQ k A' β) i = 1 := by
  refine Equiv.ext fun p => ?_
  unfold QueryAlg.precompPerm cohPrecompPermQ
  rw [dif_neg h]
  simp

/-- **The lifts of `β` on the registers of the expanded coherent run of `A'`**, written out:
`cohLiftQAt` at the steps of `A'`, the identity after them. -/
noncomputable def cohDropAt (i : Fin (A'.depth + k + 1)) :
    Equiv.Perm (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) :=
  if h : (i : ℕ) < A'.depth + 1 then cohLiftQAt e E' k A' g (β ⟨i, h⟩) else 1

theorem cohDropAt_eq (i : Fin (A'.depth + k + 1)) :
    cohDropAt e E' k A' g β i =
      QueryAlg.precompPerm (expandCohDilation A' g e E' k) (cohPrecompPermQ k A' β) i := by
  unfold cohDropAt
  split_ifs with h
  · exact (precompPerm_cohPrecompPermQ_of_lt e E' k A' g β h).symm
  · exact (precompPerm_cohPrecompPermQ_of_ge e E' k A' g β h).symm

/-- **Permutations of the registers of the expanded coherent run of `A'` carried to `G`'s** along
an equation of the registers. -/
def castPerms
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req' Resp' (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hT : QueryReg G.W 1 (Bits m) (BitStr I J) =
      QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J))
    (B' : Fin (A'.depth + k + 1) →
      Equiv.Perm (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (i : Fin (A'.depth + k + 1)) : Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)) :=
  (Equiv.cast hT).trans ((B' i).trans (Equiv.cast hT).symm)

/-- **`simLaw_withSteps_of_write_drop` with the drops given on the registers of the expanded
coherent run** (`hB`) and carried to `G`'s along `hT`. -/
theorem simLaw_withSteps_of_write_dropE (hA : A'.TracePreserving)
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req' Resp' (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hG : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = G.withSteps G.step)
    (π' : Fin (A'.depth + k + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hT : QueryReg G.W 1 (Bits m) (BitStr I J) =
      QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J))
    (h1 : ∀ (i : Fin (A'.depth + k + 1)) p (h : (i : ℕ) < A'.depth + 1),
      HEq (π' i p) (cohLiftAt e E' k A' g (σ ⟨i, h⟩) (cast hT p)))
    (h2 : ∀ (i : Fin (A'.depth + k + 1)) p, ¬ (i : ℕ) < A'.depth + 1 → π' i p = p)
    (B' : Fin (A'.depth + k + 1) →
      Equiv.Perm (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (hB : ∀ i, B' i = QueryAlg.precompPerm (expandCohDilation A' g e E' k) (cohPrecompPermQ k A' β) i)
    (S : Fin (A'.depth + k + 1) →
      QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (π' i)).trans ((permOp (castPerms e E' k A' g G hT B' i)).trans
      (G.step i))) :
    simLaw e (G.withSteps S) =
      simLaw e (expandAdv e E' k ((A'.precomp fun j =>
        (queryWorkPerm (σ j)).trans (β j)).toQueryAlgCoh.mapOut g)) :=
  simLaw_withSteps_of_write_drop e E' k A' g σ β hA G hG π' hT h1 h2
    (castPerms e E' k A' g G hT B')
    (fun i p => by
      unfold castPerms
      rw [← hB i]
      exact cast_heq _ _) S hS

theorem ReqQueryAlg.withPerm_withSteps {Req'' Resp'' O'' : Type} {t : ℕ}
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req'' Resp'' t O'')
    (b : Fin (t + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (S : Fin (t + 1) →
      QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    (G.withPerm b).withSteps S = G.withSteps S :=
  rfl

end GordieHowe.Quantum
