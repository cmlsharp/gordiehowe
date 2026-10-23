-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRun
public import GordieHowe.Model.QROM.ExpandAdv

@[expose] public section

/-!
# The expanded adversary of a dilated algorithm is a dilation

`expandAdv e' E k Q` (`GordieHowe/Model/QROM/ExpandAdv.lean`) runs `Q` and then the classical expansion `E` on
its output. If `Q` is a dilation (`QueryAlg.Dilation`) whose output is read from the system part of
its work register, then so is `expandAdv e' E k Q` (`QueryAlg.Dilation.expand`): its system is the
expansion register over `Q`'s system, its Kraus maps are `Q`'s Kraus maps on `Q`'s registers
tensored with the identity on the stash and the answer slots, followed after the last one by the
classical steps of the expansion as basis permutations of the system (`expKraus`). The steps of
the expansion read `Q`'s output, so they leave the ancilla alone. With `reduce_simStage_dilation`
(`GordieHowe/Model/QROM/DensityRun.lean`), tracing the ancilla out of the compressed-oracle simulation of the
expanded adversary gives the density-matrix run of these Kraus maps.
-/

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder

namespace GordieHowe.Quantum

namespace KrausMap

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **A Kraus map on a relabelled basis**: the operators conjugated by the relabelling
`e : ι ≃ κ`. -/
def relabel (K : KrausMap R ι ι) (e : ι ≃ κ) : KrausMap R κ κ where
  op r := (K.op r).submatrix e.symm e.symm
  sum_le := by
    have h : ∑ r, ((K.op r).submatrix e.symm e.symm)ᴴ * (K.op r).submatrix e.symm e.symm =
        (∑ r, (K.op r)ᴴ * K.op r).submatrix e.symm e.symm := by
      rw [submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    rw [h, Matrix.le_iff]
    have h1 : (1 : Matrix κ κ ℂ) = (1 : Matrix ι ι ℂ).submatrix e.symm e.symm :=
      (submatrix_one_equiv e.symm).symm
    rw [h1]
    exact (Matrix.le_iff.1 K.sum_le).submatrix e.symm

/-- The relabelled map acts on relabelled matrices as the map does. -/
theorem relabel_apply_submatrix (K : KrausMap R ι ι) (e : ι ≃ κ) (ρ : Matrix ι ι ℂ) :
    K.relabel e (ρ.submatrix e.symm e.symm) = (K ρ).submatrix e.symm e.symm := by
  simp only [KrausMap.apply, relabel, conjTranspose_submatrix, submatrix_mul_equiv,
    submatrix_sum]

end KrausMap

/-- A basis permutation of the system relabels the cross matrix. -/
theorem cross_permOp_prodCongr {ι A : Type*} [Fintype ι] [Fintype A] (π : Equiv.Perm ι)
    (φ χ : QState (ι × A)) :
    cross (permOp (π.prodCongr (Equiv.refl A)) φ) (permOp (π.prodCongr (Equiv.refl A)) χ) =
      (cross φ χ).submatrix π.symm π.symm := by
  ext i j
  simp [Equiv.prodCongr_symm]

/-- The Kraus map of a basis permutation applied to a matrix. -/
theorem identity_permConj_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (ρ : Matrix ι ι ℂ) :
    ((KrausMap.identity ι).permConj 1 π) ρ = ρ.submatrix π.symm π.symm := by
  rw [KrausMap.permConj_apply, KrausMap.id_apply]
  rfl

/-! ### Matrices that preserve a label of the basis -/

/-- A dilation of `Q` is a dilation of `Q.mapOut g`, which runs the same unitaries. -/
def QueryAlg.Dilation.mapOut {X Y O O' : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] {t : ℕ} {Q : QueryAlg X Y t O} {V Anc R : Type} [Fintype V] [DecidableEq V]
    [Fintype Anc] [Fintype R] (D : Q.Dilation V Anc R) (g : O → O') :
    (Q.mapOut g).Dilation V Anc R where
  equiv := D.equiv
  kraus := D.kraus
  clean := D.clean
  init := D.init
  reduce_init := D.reduce_init
  supported_init := D.supported_init
  supported_step := D.supported_step
  cross_step := D.cross_step

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (e' : Y ≃ B) (E : Expansion X B C) (k : ℕ)

namespace ExpandAdv

/-- The expansion register over `W ≃ V × Anc`, with the ancilla last. -/
def expAncSplit {W V Anc : Type} (σ : W ≃ V × Anc) :
    ExpansionRegister (X := X) (Y := Y) k W ≃ ExpansionRegister (X := X) (Y := Y) k V × Anc where
  toFun w := (((σ w.1).1, w.2), (σ w.1).2)
  invFun p := (σ.symm (p.1.1, p.2), p.1.2)
  left_inv w := by simp
  right_inv p := by simp

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical steps of the expansion leave the ancilla alone**: when the output is read from
the system part `(σ w).1` of the work register, `expPerm` commutes with the split of the work
register. -/
theorem queryAncSplit_expPerm {W V Anc : Type} (σ : W ≃ V × Anc) (o : V → C) (j : ℕ)
    (b : ExpBasis (X := X) (Y := Y) k W) :
    QueryAlg.queryAncSplit (expAncSplit k σ) (expPerm e' E k (fun w => o (σ w).1) j b) =
      (expPerm e' E k o j (QueryAlg.queryAncSplit (expAncSplit k σ) b).1,
        (QueryAlg.queryAncSplit (expAncSplit k σ) b).2) := by
  obtain ⟨⟨w, s, a⟩, q⟩ := b
  cases j with
  | zero => simp [expPerm, stashPerm, movePerm, expAncSplit, prevQuery]
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs <;> simp [movePerm, addAnsPerm, subAnsPerm, expAncSplit, prevQuery]

variable {V Anc R : Type} [Fintype V] [DecidableEq V] [Fintype Anc] [Fintype R]

/-- **A Kraus map of `Q`'s registers on the expansion's registers**: tensored with the identity
on the stash and the answer slots. -/
noncomputable def liftKraus (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) :
    KrausMap R (ExpBasis (X := X) (Y := Y) k V) (ExpBasis (X := X) (Y := Y) k V) :=
  (K.tensorId ((X × Y) × (Fin k → Y))).relabel (registerSplit k V).symm

/-- **The Kraus maps of the expanded adversary**: `Q`'s Kraus maps lifted to the expansion's
registers for the first `t` steps; the last one followed by `expPerm 0`; then the basis
permutations `expPerm (i − t)`. -/
noncomputable def expKraus {t : ℕ} (K : Fin (t + 1) → KrausMap R (QueryReg V 1 X Y)
      (QueryReg V 1 X Y)) (o : V → C) (i : Fin (t + k + 1)) :
    KrausMap (Option R) (ExpBasis (X := X) (Y := Y) k V) (ExpBasis (X := X) (Y := Y) k V) :=
  if h : (i : ℕ) < t then (liftKraus k (K ⟨i, by omega⟩)).optionSome
  else if (i : ℕ) = t then
    ((liftKraus k (K (Fin.last t))).permConj 1 (expPerm e' E k o 0)).optionSome
  else ((KrausMap.identity _).permConj 1 (expPerm e' E k o (i - t))).optionNone R

variable {W : Type} [Fintype W] [DecidableEq W]

omit [DecidableEq X] [Inhabited X] [DecidableEq Y] [AddCommGroup Y] [DecidableEq V]
  [DecidableEq W] in
/-- The relabelling of the expansion's basis by the split of the work register, through the split
of the expansion's registers into `Q`'s registers and the fresh ones. -/
theorem relabel_queryAncSplit_lift_eq (σ : W ≃ V × Anc) (Ψ : QState (QueryReg W 1 X Y ×
      ((X × Y) × (Fin k → Y)))) :
    relabel (QueryAlg.queryAncSplit (expAncSplit k σ)) (relabel (registerSplit k W).symm Ψ) =
      relabel ((registerSplit k V).symm.prodCongr (Equiv.refl Anc))
        (relabel (ctrlSplit (QueryAlg.queryAncSplit σ)) Ψ) := by
  ext p
  simp [Equiv.prodCongr_symm, registerSplit, expAncSplit]

omit [DecidableEq X] [Inhabited X] [DecidableEq Y] [AddCommGroup Y] [DecidableEq V]
  [DecidableEq W] in
theorem relabel_ctrlSplit_registerSplit (σ : W ≃ V × Anc)
    (φ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)) :
    relabel (ctrlSplit (QueryAlg.queryAncSplit σ))
        (relabel (registerSplit k W)
          (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)).symm φ)) =
      relabel ((registerSplit k V).prodCongr (Equiv.refl Anc)) φ := by
  ext p
  simp [Equiv.prodCongr_symm, registerSplit, expAncSplit]
  rfl

omit [Inhabited X] [AddCommGroup Y] [DecidableEq W] in
/-- **A lifted step of `Q`, on cross matrices**: if `U` acts on cross matrices over the ancilla as
`K` on vectors supported on `S`, then `lift k U` acts on them as `liftKraus k K`. -/
theorem cross_lift (σ : W ≃ V × Anc) (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y))
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) {S : Set Anc}
    (hU : ∀ φ χ : QState (QueryReg V 1 X Y × Anc), Supported {p | p.2 ∈ S} φ →
      Supported {p | p.2 ∈ S} χ →
        cross (relabel (QueryAlg.queryAncSplit σ) (U (relabel (QueryAlg.queryAncSplit σ).symm φ)))
          (relabel (QueryAlg.queryAncSplit σ) (U (relabel (QueryAlg.queryAncSplit σ).symm χ))) =
          K (cross φ χ))
    {φ χ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)} (hφ : Supported {p | p.2 ∈ S} φ)
    (hχ : Supported {p | p.2 ∈ S} χ) :
    cross (relabel (QueryAlg.queryAncSplit (expAncSplit k σ))
          (lift k U (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)).symm φ)))
        (relabel (QueryAlg.queryAncSplit (expAncSplit k σ))
          (lift k U (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)).symm χ))) =
      liftKraus k K (cross φ χ) := by
  have hsupp : ∀ {ψ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)},
      Supported {p | p.2 ∈ S} ψ → Supported {p | p.2 ∈ S}
        (relabel (ctrlSplit (QueryAlg.queryAncSplit σ))
          (relabel (registerSplit k W)
            (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)).symm ψ))) := fun h p hp => by
    rw [relabel_ctrlSplit_registerSplit, relabel_apply]
    exact h _ hp
  simp only [lift, LinearIsometryEquiv.trans_apply, relabel_symm]
  rw [relabel_queryAncSplit_lift_eq, relabel_queryAncSplit_lift_eq, cross_relabel_prodCongr,
    cross_controlled _ U K hU (hsupp hφ) (hsupp hχ), relabel_ctrlSplit_registerSplit,
    relabel_ctrlSplit_registerSplit, cross_relabel_prodCongr, liftKraus,
    ← KrausMap.relabel_apply_submatrix]
  simp

omit [DecidableEq X] [Inhabited X] [DecidableEq Y] [AddCommGroup Y] [DecidableEq V]
  [DecidableEq W] in
/-- A lifted step of `Q` keeps the support on ancilla states as `Q`'s step does. -/
theorem supported_lift (σ : W ≃ V × Anc)
    (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y)) {S S' : Set Anc}
    (hU : ∀ φ : QState (QueryReg V 1 X Y × Anc), Supported {p | p.2 ∈ S} φ →
      Supported {p | p.2 ∈ S'}
        (relabel (QueryAlg.queryAncSplit σ) (U (relabel (QueryAlg.queryAncSplit σ).symm φ))))
    {φ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)} (hφ : Supported {p | p.2 ∈ S} φ) :
    Supported {p | p.2 ∈ S'} (relabel (QueryAlg.queryAncSplit (expAncSplit k σ))
      (lift k U (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)).symm φ))) := by
  have hs : Supported {p | p.2 ∈ S}
      (relabel (ctrlSplit (QueryAlg.queryAncSplit σ))
        (relabel (registerSplit k W)
          (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)).symm φ))) := fun p hp => by
    rw [relabel_ctrlSplit_registerSplit, relabel_apply]
    exact hφ _ hp
  simp only [lift, LinearIsometryEquiv.trans_apply, relabel_symm]
  rw [relabel_queryAncSplit_lift_eq]
  intro p hp
  rw [relabel_apply]
  exact Supported.controlled_ctrlSplit _ U hU hs _ hp

omit [DecidableEq Y] [DecidableEq V] [DecidableEq W] in
/-- A classical step of the expansion, on the split basis. -/
theorem relabel_permOp_expPerm (σ : W ≃ V × Anc) (o : V → C) (j : ℕ)
    (x : QState (ExpBasis (X := X) (Y := Y) k W)) :
    relabel (QueryAlg.queryAncSplit (expAncSplit k σ))
        (permOp (expPerm e' E k (fun w => o (σ w).1) j) x) =
      permOp ((expPerm e' E k o j).prodCongr (Equiv.refl Anc))
        (relabel (QueryAlg.queryAncSplit (expAncSplit k σ)) x) :=
  (OracleAlg.permOp_relabel (QueryAlg.queryAncSplit (expAncSplit k σ))
    (π' := (expPerm e' E k o j).prodCongr (Equiv.refl Anc))
    (fun b => by rw [queryAncSplit_expPerm]; rfl) x).symm

omit [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [DecidableEq V] [DecidableEq W] in
theorem relabel_relabel_symm' {ι κ : Type} [Fintype ι] [Fintype κ] (τ : ι ≃ κ) (φ : QState κ) :
    relabel τ (relabel τ.symm φ) = φ := by
  ext p
  simp

end ExpandAdv

/-! ### The dilation of the expanded adversary -/

namespace ExpandAdv

variable {V Anc R O : Type} [Fintype V] [DecidableEq V] [Fintype Anc] [Fintype R] {t : ℕ}
  {Q : QueryAlg X Y t C} (D : Q.Dilation V Anc R) (o : V → C)

omit [DecidableEq X] [Inhabited X] [DecidableEq Y] [AddCommGroup Y] [DecidableEq V] in
theorem supported_permOp_prodCongr {S : Set Anc} (π : Equiv.Perm (ExpBasis (X := X) (Y := Y) k V))
    {φ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)} (hφ : Supported {p | p.2 ∈ S} φ) :
    Supported {p | p.2 ∈ S} (permOp (π.prodCongr (Equiv.refl Anc)) φ) :=
  hφ.permOp fun _ hr => hr

/-- The fresh registers in their initial content, reduced: `reduce` of `v ⊗ |r⟩` on the split
basis is `reduce v ⊗ |r⟩⟨r|`. -/
theorem reduce_ctrlSplit_tensorKet {ι κ A F : Type} [Fintype ι] [Fintype κ] [Fintype A]
    [Fintype F] [DecidableEq F] (τ : ι ≃ κ × A) (v : QState ι) (r : F) :
    reduce (relabel (ctrlSplit τ) (tensorKet v r)) =
      reduce (relabel τ v) ⊗ₖ Matrix.single r r (1 : ℂ) := by
  ext ⟨x, f⟩ ⟨x', f'⟩
  simp only [reduce_apply, relabel_apply, ctrlSplit_symm_apply, tensorKet_apply,
    kroneckerMap_apply, Matrix.single_apply]
  by_cases hf : f = r <;> by_cases hf' : f' = r
  · subst hf hf'
    simp
  · simp [hf, hf', Ne.symm hf']
  · simp [hf, hf', Ne.symm hf]
  · simp [hf, hf', Ne.symm hf, Ne.symm hf']

/-- The fresh registers in their initial content keep the support on ancilla states. -/
theorem supported_ctrlSplit_tensorKet {ι κ A F : Type} [Fintype ι] [Fintype κ] [Fintype A]
    [Fintype F] [DecidableEq F] (τ : ι ≃ κ × A) {S : Set A} {v : QState ι}
    (hv : Supported {p | p.2 ∈ S} (relabel τ v)) (r : F) :
    Supported {p | p.2 ∈ S} (relabel (ctrlSplit τ) (tensorKet v r)) := fun p hp => by
  simp only [relabel_apply, ctrlSplit_symm_apply, tensorKet_apply]
  rw [show v (τ.symm (p.1.1, p.2)) = 0 from by simpa using hv (p.1.1, p.2) hp, zero_mul]

variable (hout : ∀ w, Q.out w = o (D.equiv w).1)
include hout

theorem expStep_out (i : ℕ) : expStep e' E k Q Q.out i = expStep e' E k Q (fun w => o (D.equiv w).1) i := by
  rw [show Q.out = fun w => o (D.equiv w).1 from funext hout]

omit hout [DecidableEq X] [Inhabited X] [DecidableEq Y] [AddCommGroup Y] in
theorem stepAt_eq {i : ℕ} (hi : i < t + 1) : (Q.toOracleAlg ∅).stepAt () i = Q.step ⟨i, hi⟩ :=
  OracleAlg.stepAt_of_lt _ hi

/-- **Each step of the expanded adversary acts on cross matrices over the ancilla as its Kraus
map.** -/
theorem cross_expStep (i : ℕ) (hi : i < t + k + 1)
    {φ χ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)}
    (hφ : Supported {p | p.2 ∈ D.clean (min i (t + 1))} φ)
    (hχ : Supported {p | p.2 ∈ D.clean (min i (t + 1))} χ) :
    cross (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv))
          (expStep e' E k Q Q.out i (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv)).symm φ)))
        (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv))
          (expStep e' E k Q Q.out i (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv)).symm χ))) =
      expKraus e' E k D.kraus o ⟨i, hi⟩ (cross φ χ) := by
  rw [expStep_out e' E k D o hout]
  unfold expKraus expStep
  by_cases h1 : i < t
  · rw [ite_cond_eq_true _ _ (eq_true h1), dif_pos h1, KrausMap.optionSome_apply, stepAt_eq (Q := Q) (by omega)]
    rw [Nat.min_eq_left (by omega)] at hφ hχ
    exact cross_lift k D.equiv _ _ (D.cross_step ⟨i, by omega⟩) hφ hχ
  · rw [ite_cond_eq_false _ _ (eq_false h1), dif_neg h1]
    by_cases h2 : i = t
    · subst h2
      rw [ite_cond_eq_true _ _ (eq_true rfl), ite_cond_eq_true _ _ (eq_true rfl), KrausMap.optionSome_apply, KrausMap.permConj_apply,
        stepAt_eq (Q := Q) (Nat.lt_succ_self _)]
      rw [Nat.min_eq_left (by omega)] at hφ hχ
      simp only [LinearIsometryEquiv.trans_apply]
      rw [relabel_permOp_expPerm, relabel_permOp_expPerm, cross_permOp_prodCongr,
        cross_lift k D.equiv _ _ (D.cross_step ⟨i, Nat.lt_succ_self i⟩) hφ hχ]
      simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, submatrix_id_id]
      rfl
    · rw [ite_cond_eq_false _ _ (eq_false h2), ite_cond_eq_false _ _ (eq_false h2), KrausMap.optionNone_apply, identity_permConj_apply,
        relabel_permOp_expPerm, relabel_permOp_expPerm, relabel_relabel_symm',
        relabel_relabel_symm', cross_permOp_prodCongr]

/-- **Each step of the expanded adversary keeps the ancilla clean.** -/
theorem supported_expStep (i : ℕ) {φ : QState (ExpBasis (X := X) (Y := Y) k V × Anc)}
    (hφ : Supported {p | p.2 ∈ D.clean (min i (t + 1))} φ) :
    Supported {p | p.2 ∈ D.clean (min (i + 1) (t + 1))}
      (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv))
        (expStep e' E k Q Q.out i (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv)).symm φ))) := by
  rw [expStep_out e' E k D o hout]
  unfold expStep
  by_cases h1 : i < t
  · rw [ite_cond_eq_true _ _ (eq_true h1), stepAt_eq (Q := Q) (by omega)]
    rw [Nat.min_eq_left (by omega)] at hφ
    rw [Nat.min_eq_left (by omega)]
    exact supported_lift k D.equiv _ (D.supported_step ⟨i, by omega⟩) hφ
  · rw [ite_cond_eq_false _ _ (eq_false h1)]
    by_cases h2 : i = t
    · subst h2
      rw [ite_cond_eq_true _ _ (eq_true rfl), stepAt_eq (Q := Q) (Nat.lt_succ_self _)]
      rw [Nat.min_eq_left (by omega)] at hφ
      simp only [LinearIsometryEquiv.trans_apply]
      have h := supported_lift k D.equiv _ (D.supported_step ⟨i, Nat.lt_succ_self i⟩) hφ
      rw [relabel_permOp_expPerm]
      exact supported_permOp_prodCongr k _ (by simpa [Nat.min_self] using h)
    · rw [ite_cond_eq_false _ _ (eq_false h2), relabel_permOp_expPerm, relabel_relabel_symm']
      rw [Nat.min_eq_right (by omega)] at hφ
      rw [Nat.min_eq_right (by omega)]
      exact supported_permOp_prodCongr k _ hφ

omit hout in
theorem reduce_init_expand :
    reduce (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv)) (embed k Q.init)) =
      (D.init ⊗ₖ Matrix.single (fresh (X := X) (Y := Y) k) (fresh k) (1 : ℂ)).submatrix
        (registerSplit k V) (registerSplit k V) := by
  rw [embed, relabel_queryAncSplit_lift_eq, ← cross_self, cross_relabel_prodCongr, cross_self,
    reduce_ctrlSplit_tensorKet, D.reduce_init]
  simp

omit hout in
theorem supported_init_expand :
    Supported {p | p.2 ∈ D.clean (min 0 (t + 1))}
      (relabel (QueryAlg.queryAncSplit (expAncSplit k D.equiv)) (embed k Q.init)) := by
  rw [embed, relabel_queryAncSplit_lift_eq, Nat.zero_min]
  intro p hp
  rw [relabel_apply]
  exact supported_ctrlSplit_tensorKet _ D.supported_init _ _ hp

/-- **The expanded adversary of a dilated algorithm is a dilation**, when the output of `Q` is read
from the system part of its work register: the system is the expansion register over `V`, the
Kraus maps are `expKraus`, and the ancilla is clean before step `n` when it is clean for `Q`
before step `min n (t + 1)`. -/
noncomputable def expandDilation :
    (expandAdv e' E k Q).Dilation (ExpansionRegister (X := X) (Y := Y) k V) Anc (Option R) where
  equiv := expAncSplit k D.equiv
  kraus := expKraus e' E k D.kraus o
  clean n := D.clean (min n (t + 1))
  init := (D.init ⊗ₖ Matrix.single (fresh (X := X) (Y := Y) k) (fresh k) (1 : ℂ)).submatrix
    (registerSplit k V) (registerSplit k V)
  reduce_init := reduce_init_expand k D
  supported_init := supported_init_expand k D
  supported_step i _ hφ := supported_expStep e' E k D o hout i hφ
  cross_step i _ _ hφ hχ := cross_expStep e' E k D o hout i i.2 hφ hχ

end ExpandAdv

/-! ### The halting flag of the expanded coherent purification -/

namespace ExpandAdv

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- The classical steps of the expansion do not change the work register. -/
theorem expPerm_fst_fst {W : Type} (o : W → C) (j : ℕ) (b : ExpBasis (X := X) (Y := Y) k W) :
    (expPerm e' E k o j b).1.1 = b.1.1 := by
  obtain ⟨⟨w, s, a⟩, q⟩ := b
  cases j with
  | zero => rfl
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs <;> rfl

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
theorem expPerm_symm_fst_fst {W : Type} (o : W → C) (j : ℕ) (b : ExpBasis (X := X) (Y := Y) k W) :
    ((expPerm e' E k o j).symm b).1.1 = b.1.1 := by
  conv_rhs => rw [← Equiv.apply_symm_apply (expPerm e' E k o j) b]
  rw [expPerm_fst_fst]

end ExpandAdv

/-! ### Runs that vanish at a label of the work register -/

/-! ### The expanded coherent purification of a core algorithm -/

section Coherent

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B' : Type} (e : BitStr I J ≃ B') {O : Type} (A : Alg (Bits m) (BitStr I J) O)
  (g : Option O → C)

/-- The output of `A.toQueryAlgCoh.mapOut g` read from the system register `(v, b)`. -/
def cohOut (v : A.V × Bool) : C :=
  g (if v.2 then none else some (A.out v.1))

/-- **The expanded coherent purification of `A` as a dilation.** -/
noncomputable def expandCohDilation (e' : BitStr I J ≃ B) (E : Expansion (Bits m) B C) (k : ℕ) :
    (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)).Dilation
      (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
      (Option (A.R ⊕ Bool)) :=
  ExpandAdv.expandDilation e' E k (A.cohDilation.mapOut g) (cohOut A g) fun _ => rfl

/-- **Route 3′ step 1 for the expanded coherent purification**: tracing the ancilla out of the
compressed-oracle simulation of `expandAdv e' E k (A.toQueryAlgCoh.mapOut g)` gives, after step
`n ≤ A.depth + k`, the density-matrix run of `expKraus`: the halting completions of `A`'s Kraus
maps tensored with the identity on the stash and the answer slots, then the expansion's basis
permutations. The run takes only these Kraus maps and the initial reduced state. -/
theorem reduce_simStage_expandAdv_toQueryAlgCoh (e' : BitStr I J ≃ B) (E : Expansion (Bits m) B C)
    (k : ℕ) {n : ℕ} (hn : n ≤ A.depth + k) :
    reduce (relabel (simAncSplit (expandCohDilation A g e' E k).equiv)
        (simStage e (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)) n)) =
      densityRun e (expandCohDilation A g e' E k).kraus (expandCohDilation A g e' E k).init n :=
  reduce_simStage_dilation e (expandCohDilation A g e' E k) hn

end Coherent

end GordieHowe.QROM
