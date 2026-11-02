-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftExt

@[expose] public section

/-!
# Operations on lists of additions per step

Lists of additions per step (`StepAdds`) read through a part of a larger register, pulled back
along a partial map of the steps, and concatenated, with their permutations.

- `RegLens.liftPerm`, `RegLens.liftPerm_one`, `RegLens.liftPerm_mul`: a permutation of a part
  as a permutation of the register; `RegLens.liftPerm_comp`, `RegLens.liftPerm_transport`,
  `fstLens_liftPerm`: through a part of a part, an equivalence and the first factor.
- `StepAdds.comap`, `StepAdds.comap_perm`: the additions on a part of a larger register.
- `StepAdds.conjAt`, `StepAdds.conjAt_perm`: the additions conjugated by a permutation per step.
- `optFin`, `optFin_rec`, `StepAdds.optSteps`, `StepAdds.optSteps_perm`, `StepAdds.reindex`,
  `StepAdds.reindex_perm`, `StepAdds.pullOpt`, `StepAdds.pullOpt_perm`: the additions after the
  step `σ k'` before step `k'`, none where `σ k' = none`.
- `StepAdds.append`, `StepAdds.perm_append`: two lists of additions, the first one first.
-/

namespace GordieHowe.Quantum

/-- **A permutation of a part as a permutation of the register**: the part of `z` replaced by
its image under `π`. -/
def RegLens.liftPerm {Z Z' : Type*} (ℓ : RegLens Z' Z) (π : Equiv.Perm Z) : Equiv.Perm Z' where
  toFun z := ℓ.set z (π (ℓ.get z))
  invFun z := ℓ.set z (π.symm (ℓ.get z))
  left_inv z := by simp
  right_inv z := by simp

theorem RegLens.liftPerm_one {Z Z' : Type*} (ℓ : RegLens Z' Z) : ℓ.liftPerm 1 = 1 :=
  Equiv.ext fun z => by simp [RegLens.liftPerm]

theorem RegLens.liftPerm_mul {Z Z' : Type*} (ℓ : RegLens Z' Z) (π σ : Equiv.Perm Z) :
    ℓ.liftPerm (π * σ) = ℓ.liftPerm π * ℓ.liftPerm σ :=
  Equiv.ext fun z => by simp [RegLens.liftPerm]

/-- **A permutation of a part of a part** is the lift of its lift. -/
theorem RegLens.liftPerm_comp {Z V U : Type*} (ℓ : RegLens Z V) (ℓ' : RegLens V U)
    (π : Equiv.Perm U) : (ℓ.comp ℓ').liftPerm π = ℓ.liftPerm (ℓ'.liftPerm π) :=
  rfl

/-- **A permutation of a part read through an equivalence** `g` is the lift conjugated by `g`. -/
theorem RegLens.liftPerm_transport {Z Z' V : Type*} (ℓ : RegLens Z V) (g : Z' ≃ Z)
    (π : Equiv.Perm V) : (ℓ.transport g).liftPerm π = g.symm.permCongr (ℓ.liftPerm π) :=
  rfl

/-- **A permutation of the first factor** is its product with the identity. -/
theorem fstLens_liftPerm {W U : Type*} (π : Equiv.Perm W) :
    (fstLens W U).liftPerm π = π.prodCongr (Equiv.refl U) :=
  rfl

namespace StepAdds

variable {Z Z' K K' X V : Type*} [AddGroup V] (P : StepAdds Z K X V)

/-- **The additions on a part of a larger register**: each addition writes the part `L k i` of
the part `ℓ`, its branches and point read from the part `ℓ`. -/
def comap (ℓ : RegLens Z' Z) : StepAdds Z' K X V where
  nb := P.nb
  L k i := ℓ.comp (P.L k i)
  on k i z := P.on k i (ℓ.get z)
  x k i z := P.x k i (ℓ.get z)
  on_set k i z v := by
    change P.on k i (ℓ.get (ℓ.set z ((P.L k i).set (ℓ.get z) v))) = P.on k i (ℓ.get z)
    rw [ℓ.get_set, P.on_set]
  x_set k i z v := by
    change P.x k i (ℓ.get (ℓ.set z ((P.L k i).set (ℓ.get z) v))) = P.x k i (ℓ.get z)
    rw [ℓ.get_set, P.x_set]

/-- **The additions on a part are the additions of the part.** -/
theorem comap_perm (ℓ : RegLens Z' Z) (ω : X → V) (k : K) :
    (P.comap ℓ).perm ω k = ℓ.liftPerm (P.perm ω k) := by
  unfold StepAdds.perm
  rw [seqPerm_map ℓ.liftPerm ℓ.liftPerm_one ℓ.liftPerm_mul]
  exact congrArg _ (funext fun i => Equiv.ext fun z => rfl)

/-- **The additions conjugated by the permutations `C k`**: each addition after step `k` read
through `C k` (`RegLens.transport`), its branches and point read after `C k`. -/
def conjAt (C : K → Equiv.Perm Z) : StepAdds Z K X V where
  nb := P.nb
  L k i := (P.L k i).transport (C k)
  on k i z := P.on k i (C k z)
  x k i z := P.x k i (C k z)
  on_set k i z v := by
    change P.on k i (C k ((C k).symm ((P.L k i).set (C k z) v))) = P.on k i (C k z)
    rw [Equiv.apply_symm_apply, P.on_set]
  x_set k i z v := by
    change P.x k i (C k ((C k).symm ((P.L k i).set (C k z) v))) = P.x k i (C k z)
    rw [Equiv.apply_symm_apply, P.x_set]

/-- **The conjugated additions are the additions conjugated by `C k`.** -/
theorem conjAt_perm (C : K → Equiv.Perm Z) (ω : X → V) (k : K) :
    (P.conjAt C).perm ω k = (C k)⁻¹ * P.perm ω k * C k := by
  unfold StepAdds.perm
  rw [seqPerm_map (fun π => (C k)⁻¹ * π * C k) (by group) (fun a b => by group)]
  exact congrArg _ (funext fun i => Equiv.ext fun z => rfl)

end StepAdds

/-- **A family of values indexed by `Fin (nb k)`, at an optional `k`**: none at `none`. -/
def optFin {K α : Type*} (nb : K → ℕ) (f : ∀ k, Fin (nb k) → α) :
    ∀ o : Option K, Fin (o.elim 0 nb) → α
  | none, i => i.elim0
  | some k, i => f k i

/-- **A statement at every optional index** holds when it holds at every `some k`. -/
theorem optFin_rec {K : Type*} {nb : K → ℕ} {Pr : ∀ o : Option K, Fin (o.elim 0 nb) → Prop}
    (h : ∀ k i, Pr (some k) i) : ∀ o i, Pr o i
  | none, i => i.elim0
  | some k, i => h k i

namespace StepAdds

variable {Z K K' X V : Type*} [AddGroup V] (P : StepAdds Z K X V)

/-- **The additions after an optional step**, none at `none`. -/
def optSteps : StepAdds Z (Option K) X V where
  nb o := o.elim 0 P.nb
  L := optFin P.nb P.L
  on := optFin P.nb P.on
  x := optFin P.nb P.x
  on_set := optFin_rec (Pr := fun o i => (optFin P.nb P.L o i).Indep (optFin P.nb P.on o i))
    fun k i => P.on_set k i
  x_set := optFin_rec (Pr := fun o i => (optFin P.nb P.L o i).Indep (optFin P.nb P.x o i))
    fun k i => P.x_set k i

theorem optSteps_perm (ω : X → V) : ∀ o : Option K, P.optSteps.perm ω o = o.elim 1 (P.perm ω)
  | none => rfl
  | some _ => rfl

/-- **The additions read at the steps `g k'`.** -/
def reindex (g : K' → K) : StepAdds Z K' X V where
  nb k' := P.nb (g k')
  L k' := P.L (g k')
  on k' := P.on (g k')
  x k' := P.x (g k')
  on_set k' := P.on_set (g k')
  x_set k' := P.x_set (g k')

theorem reindex_perm (g : K' → K) (ω : X → V) (k' : K') :
    (P.reindex g).perm ω k' = P.perm ω (g k') :=
  rfl

/-- **The additions after step `σ k'` before step `k'`**, none where `σ k' = none`. -/
def pullOpt (σ : K' → Option K) : StepAdds Z K' X V :=
  P.optSteps.reindex σ

/-- **The pulled-back additions** are those after `σ k'`, the identity where `σ k' = none`. -/
theorem pullOpt_perm (σ : K' → Option K) (ω : X → V) (k' : K') :
    (P.pullOpt σ).perm ω k' = (σ k').elim 1 (P.perm ω) :=
  P.optSteps_perm ω (σ k')

/-- **Two lists of additions, the first one first.** -/
def append (Q : StepAdds Z K X V) : StepAdds Z K X V where
  nb k := P.nb k + Q.nb k
  L k := Fin.append (P.L k) (Q.L k)
  on k := Fin.append (P.on k) (Q.on k)
  x k := Fin.append (P.x k) (Q.x k)
  on_set k i := Fin.addCases (motive := fun i => (Fin.append (P.L k) (Q.L k) i).Indep
    (Fin.append (P.on k) (Q.on k) i)) (fun j => by
      simp only [Fin.append_left]
      exact P.on_set k j) (fun j => by
      simp only [Fin.append_right]
      exact Q.on_set k j) i
  x_set k i := Fin.addCases (motive := fun i => (Fin.append (P.L k) (Q.L k) i).Indep
    (Fin.append (P.x k) (Q.x k) i)) (fun j => by
      simp only [Fin.append_left]
      exact P.x_set k j) (fun j => by
      simp only [Fin.append_right]
      exact Q.x_set k j) i

/-- **The additions of two lists, the first one first.** -/
theorem perm_append (Q : StepAdds Z K X V) (ω : X → V) (k : K) :
    (P.append Q).perm ω k = Q.perm ω k * P.perm ω k := by
  unfold StepAdds.perm
  rw [← seqPerm_append]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Equiv.ext fun d => ?_
    simp only [StepAdds.add, RegAdd.perm_apply, StepAdds.append, Fin.append_left]
  · refine Equiv.ext fun d => ?_
    simp only [StepAdds.add, RegAdd.perm_apply, StepAdds.append, Fin.append_right]

end StepAdds

end GordieHowe.Quantum
