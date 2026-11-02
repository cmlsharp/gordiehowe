-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandCohTransport

@[expose] public section

/-!
# The expanded coherent run with its steps read after permutations of the query registers

The results of the precomposition section of `GordieHowe/Model/QROM/ExpandCohRelabel.lean`
(`simLaw_precompSteps_expandCoh`, `simLaw_steps_of_dilation`), for permutations `σ i` of the core
algorithm's query registers `QueryReg A.V 1 X Y` (which may read the query register) rather than
of its work register.

- `cohLiftQ`, `expPrecompPermQ`, `cohPrecompPermQ`: `σ` on the expansion's basis and on the
  system of the expanded coherent purification.
- `liftKraus_permConj_opQ`, `expKraus_precomp_opQ`, `expKraus_precomp_applyQ`,
  `densityRun_precomp_liftMatQ`.
- `simLaw_precompSteps_expandCohQ`, `simLaw_precompSteps_of_dilationQ`,
  `simLaw_steps_of_dilationQ`.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (e : BitStr I J ≃ B)

variable (E : Expansion (Bits m) B C) (k : ℕ)

/-- **A permutation of the query registers of `V` on the system of the expanded coherent
purification**, with the identity on the halting flag. -/
def cohLiftQ {V : Type} (π : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) :
    Equiv.Perm (QueryReg (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (V × Bool)) 1
      (Bits m) (BitStr I J)) :=
  (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (V × Bool)))).symm.permCongr
    ((liftE k π).prodCongr (Equiv.refl Bool))

section CohPrecompQ

variable {O : Type} (A : Alg (Bits m) (BitStr I J) O) (g : Option O → C)
  (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 (Bits m) (BitStr I J)))

/-- `σ` on the expansion's basis, the identity after `A`'s steps. -/
def expPrecompPermQ (i : Fin (A.depth + k + 1)) :
    Equiv.Perm (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V) :=
  if h : (i : ℕ) < A.depth + 1 then liftE k (σ ⟨i, h⟩) else 1

/-- `σ` on the system of the expanded coherent purification, the identity after `A`'s steps. -/
def cohPrecompPermQ (i : Fin (A.depth + k + 1)) :
    Equiv.Perm (QueryReg (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) 1
      (Bits m) (BitStr I J)) :=
  if h : (i : ℕ) < A.depth + 1 then cohLiftQ k (σ ⟨i, h⟩) else 1

theorem liftKraus_permConj_opQ {V R : Type} [Fintype V] [DecidableEq V] [Fintype R]
    (K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)))
    (s : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) (r : R)
    (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    (ExpandAdv.liftKraus k (K.permConj s (Equiv.refl _))).op r a b =
      (ExpandAdv.liftKraus k K).op r a (liftE k s b) := by
  change ((K.op r).submatrix (Equiv.refl _).symm s ⊗ₖ (1 : Matrix _ _ ℂ))
      (registerSplit k V a) (registerSplit k V b) =
    (K.op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V (liftE k s b))
  rw [liftE_apply, Equiv.apply_symm_apply, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
  rfl

/-- **The expansion's Kraus maps of `A.precomp σ` are those of `A` read after `σ`.** -/
theorem expKraus_precomp_opQ (o : A.V → C) (i : Fin (A.depth + k + 1)) :
    (expKraus e E k (A.precomp σ).step o i).op =
      ((expKraus e E k A.step o i).permConj (expPrecompPermQ k A σ i) 1).op := by
  funext r
  ext a b
  change _ = (expKraus e E k A.step o i).op r a (expPrecompPermQ k A σ i b)
  obtain ⟨i, hi⟩ := i
  unfold expKraus expPrecompPermQ
  dsimp only [Alg.precomp]
  by_cases h1 : i < A.depth
  · rw [dif_pos h1, dif_pos h1, dif_pos (show i < A.depth + 1 by omega)]
    cases r with
    | none => rfl
    | some r => exact liftKraus_permConj_opQ k (A.step _) (σ _) r a b
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : i = A.depth
    · rw [if_pos h2, if_pos h2, dif_pos (show i < A.depth + 1 by omega)]
      cases r with
      | none => rfl
      | some r =>
        have hl : (⟨i, by omega⟩ : Fin (A.depth + 1)) = Fin.last A.depth := Fin.ext h2
        change (ExpandAdv.liftKraus k ((A.step (Fin.last A.depth)).permConj
            (σ (Fin.last A.depth)) (Equiv.refl _))).op r
            ((expPerm e E k o 0).symm a) b =
          (ExpandAdv.liftKraus k (A.step (Fin.last A.depth))).op r
            ((expPerm e E k o 0).symm a) (liftE k (σ ⟨i, by omega⟩) b)
        rw [hl]
        exact liftKraus_permConj_opQ k _ _ r _ b
    · rw [if_neg h2, if_neg h2, dif_neg (show ¬ i < A.depth + 1 by omega)]
      rfl

theorem expKraus_precomp_applyQ (o : A.V → C) (i : Fin (A.depth + k + 1))
    (ρ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V) ℂ) :
    (expKraus e E k (A.precomp σ).step o i) ρ =
      ((expKraus e E k A.step o i).permConj (expPrecompPermQ k A σ i) 1) ρ := by
  simp only [KrausMap.apply, expKraus_precomp_opQ e E k A σ o i]

/-- **The flag stays `false` in the precomposed expanded coherent run**: its density-matrix run is
the run of the Kraus maps of `A.precomp σ` and the expansion, with the halting flag `false`. -/
theorem densityRun_precomp_liftMatQ (hA : A.TracePreserving) {n : ℕ} (hn : n ≤ A.depth + k) :
    densityRun e ((expandCohDilation A g e E k).precomp (cohPrecompPermQ k A σ)).kraus
        (expandCohDilation A g e E k).init n =
      liftMat (simAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
        (densityRun e (expKraus e E k (A.precomp σ).step
          fun v => g (some (A.out v)))
          ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) n)
        (Matrix.single false false 1) := by
  have hinit : (expandCohDilation A g e E k).init =
      liftMat (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
        ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
          (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V))
        (Matrix.single false false 1) := by
    rw [← expInit_liftMat]
    have hc : (A.cohDilation.mapOut g).init =
        liftMat (QueryAlg.queryAncSplit (Equiv.refl (A.V × Bool))) A.init.mat
          (Matrix.single false false 1) := by
      ext x y
      rfl
    rw [← hc]
    ext x y
    rfl
  rw [hinit]
  refine densityRun_liftMat e (expAncSplit k (Equiv.refl _)) _ _ _ (n := A.depth + k + 1)
    (fun i hi => ?_) _ n (by omega)
  have hl := (liftsAt_expandCoh e E k A g hA i).permConj_left_single
    (π' := cohPrecompPermQ k A σ i) (π := expPrecompPermQ k A σ i)
    (fun x => by
      unfold cohPrecompPermQ
      split_ifs <;> rfl)
    (fun y => by
      unfold cohPrecompPermQ expPrecompPermQ
      split_ifs <;> rfl)
  intro ρ
  rw [show ((expandCohDilation A g e E k).precomp (cohPrecompPermQ k A σ)).kraus i =
    ((expandCohDilation A g e E k).kraus i).permConj (cohPrecompPermQ k A σ i) 1 from rfl, hl ρ]
  congr 1
  exact (expKraus_precomp_applyQ e E k A σ _ i ρ).symm

open Classical in
/-- **The expanded coherent run with its steps read after `σ` has the law of the expanded coherent
run of `A.precomp σ`**, for a trace-preserving `A`. -/
theorem simLaw_precompSteps_expandCohQ (hA : A.TracePreserving) :
    simLaw e (QueryAlg.precompSteps (expandCohDilation A g e E k) (cohPrecompPermQ k A σ)) =
      simLaw e (expandAdv e E k ((A.precomp σ).toQueryAlgCoh.mapOut g)) := by
  ext T
  rw [simLaw_dilation e ((expandCohDilation A g e E k).precomp (cohPrecompPermQ k A σ))
      (expOut e E k (cohOut A g)) (fun w => rfl) T,
    simLaw_expandCoh_eq e E k _ (Alg.tracePreserving_precomp hA _) g T]
  change ∑ x, _ * ENNReal.ofReal (densityRun e
    ((expandCohDilation A g e E k).precomp (cohPrecompPermQ k A σ)).kraus
    (expandCohDilation A g e E k).init (A.depth + k) x x).re = _
  rw [densityRun_precomp_liftMatQ e E k A g σ hA le_rfl]
  erw [sum_diag_liftMat_single]
  rfl

open Classical in
/-- **The law of a dilated algorithm with its steps read after `σ`**, for a dilation with the
Kraus maps and initial state of the expanded coherent purification of `A` and its output: that of
the expanded coherent run of `A.precomp σ`, for a trace-preserving `A`. -/
theorem simLaw_precompSteps_of_dilationQ (hA : A.TracePreserving)
    {Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k)}
    (D : Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
      (Option (A.R ⊕ Bool)))
    (hk : ∀ i, D.kraus i = (expandCohDilation A g e E k).kraus i)
    (hinit : D.init = (expandCohDilation A g e E k).init)
    (hout : ∀ w, Q.out w = expOut e E k (cohOut A g) (D.equiv w).1) :
    simLaw e (QueryAlg.precompSteps D (cohPrecompPermQ k A σ)) =
      simLaw e (expandAdv e E k ((A.precomp σ).toQueryAlgCoh.mapOut g)) := by
  ext T
  rw [simLaw_dilation e (D.precomp (cohPrecompPermQ k A σ)) (expOut e E k (cohOut A g)) hout T,
    simLaw_expandCoh_eq e E k _ (Alg.tracePreserving_precomp hA _) g T]
  have hD : densityRun e (D.precomp (cohPrecompPermQ k A σ)).kraus
      (D.precomp (cohPrecompPermQ k A σ)).init (A.depth + k) =
      densityRun e ((expandCohDilation A g e E k).precomp (cohPrecompPermQ k A σ)).kraus
        (expandCohDilation A g e E k).init (A.depth + k) := by
    change densityRun e (fun i => (D.kraus i).permConj (cohPrecompPermQ k A σ i) 1) D.init _ =
      densityRun e (fun i => ((expandCohDilation A g e E k).kraus i).permConj
        (cohPrecompPermQ k A σ i) 1) _ _
    simp only [hk, hinit]
  rw [hD, densityRun_precomp_liftMatQ e E k A g σ hA le_rfl]
  erw [sum_diag_liftMat_single]
  rfl

/-- **The dilated algorithm with given steps, read after `σ`**, has the law of the expanded
coherent run of `A.precomp σ`: for steps `S i = U_i ∘ π i` (`hS`) with `π` the precomposition of
`σ` through the dilation. -/
theorem simLaw_steps_of_dilationQ (hA : A.TracePreserving)
    {Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k)}
    (D : Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
      (Option (A.R ⊕ Bool)))
    (hk : ∀ i, D.kraus i = (expandCohDilation A g e E k).kraus i)
    (hinit : D.init = (expandCohDilation A g e E k).init)
    (hout : ∀ w, Q.out w = expOut e E k (cohOut A g) (D.equiv w).1)
    (S : Fin (A.depth + k + 1) →
      QState (QueryReg Q.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
        QState (QueryReg Q.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (QueryAlg.precompPerm D (cohPrecompPermQ k A σ) i)).trans (Q.step i)) :
    simLaw e { Q with step := S } =
      simLaw e (expandAdv e E k ((A.precomp σ).toQueryAlgCoh.mapOut g)) := by
  have h : S = (QueryAlg.precompSteps D (cohPrecompPermQ k A σ)).step := funext hS
  rw [← simLaw_precompSteps_of_dilationQ e E k A g σ hA D hk hinit hout, h]
  rfl

end CohPrecompQ

end GordieHowe.QROM
