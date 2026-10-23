-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandAt
public import GordieHowe.Model.QROM.Partition
public import GordieHowe.Model.QROM.Swap
public import GordieHowe.Model.QROM.Lifting

@[expose] public section

/-!
# Measuring a database partition before a segment of queries

The simulated run of the inserted expansion `𝒜_E = expandAt e E k 𝒜 s κ` (`GordieHowe/Model/QROM/ExpandAt.lean`):
after the expansion (its step `s + k`) the simulated state `φ` holds the expansion's answers. A
partition of databases labelled by `L c a D` (the control `c = κ w`, the answers `a` and the
database `D`; `labelProj`) is measured there in the Extract′ game (`extractAtProb`) and at the
end in the simulated run (`foldedProb`). Between them come `t − s` simulated queries and `𝒜`'s
unitaries after step `s`.

- `simQuery_simStage_eq_compress`: the simulated state just before a unitary is the compression
  of the Fourier transform of the superposition, over the oracle, of the runs with that oracle
  just after the query (Zha19 Lemmas 2 and 4), so each of its database slices is a linear
  combination of runs with classical oracles (`compress_fourier_apply`).
- `simStep_labelProj_comm`: on those states `𝒜_E`'s unitaries after the expansion commute with
  the label projections, when `𝒜`'s unitaries keep the classes of `κ` on its runs
  (`KeepsClasses`); with the answers written, a label projection acts on each class of the
  answers as a projection onto a class of `κ` (`ExpandAt.lift_mask_embedAns`).
- `abs_foldedProb_sub_extractAtProb_le`: the two probabilities differ by at most
  `(t − s) √(24 κ)`, `κ` bounding the generalized instability of every partition `L c a`
  (`norm_segRun_famDiff_le` with `sum_norm_labelComm_simQuery_le`, and `abs_norm_sq_sub_le`).
-/

open GordieHowe.Quantum

namespace GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ} {B : Type}
  (e : BitStr I J ≃ B)

/-! ### Database slices of compressed purified states -/

section Slices

variable {W : Type} [Fintype W] [DecidableEq W] (t : ℕ)

/-- **The database slices of a compressed Fourier transform**: at each database basis state `s`
the slice is a linear combination of the oracle slices, with coefficients that depend on `s`
and the oracle only. -/
theorem compress_fourier_apply (ψ : QState (PurReg W I J m)) (r : QueryReg W 1 (Bits m) (BitStr I J))
    (s : Slots I J m t) :
    compress e t W (fourier _ ψ) (r, s) =
      ∑ F, (∑ F', fdb e t F' s * fourierK F' F) * ψ (r, F) := by
  rw [compress, kernelMap_idLeft_apply]
  simp_rw [fourier_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun F' _ => by ring

variable {O : Type} {T : ℕ} (A : QueryAlg (Bits m) (BitStr I J) T O)

/-- **The simulated state just before a unitary**: for `k' < T`, the simulated query applied to
`simStage A k'` is the compression of the Fourier transform of the superposition, over the
oracle `F`, of `A`'s run with oracle `F` after its query `k' + 1` (Zha19 Lemmas 2 and 4). -/
theorem simQuery_simStage_eq_compress {k' : ℕ} (hk : k' < T) :
    simQuery e A.W T (simStage e A k') = compress e T A.W (fourier _ (WithLp.toLp 2 fun b =>
      unifAmp I J m * permOp (queryPerm b.2) ((A.toOracleAlg ∅).stage (queryPerm b.2) () k') b.1)) := by
  have hsupp : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F < T}} (fourStage A k') :=
    fun b hb => supported_fourStage A k' b fun h => hb (lt_of_le_of_lt h hk)
  rw [simStage_eq_compress e A hk.le, simQuery_compress e A.W hsupp]
  congr 1
  have h1 : fourQuery (fourStage A k') = fourier _ (stO A.W (purStage A k')) := by
    rw [← fourier_fourStage, ← fourier_fourQuery, fourier_fourier]
  rw [h1]
  congr 1
  ext ⟨r, F⟩
  rw [stO, controlled_apply]
  have : (WithLp.toLp 2 fun r' => purStage A k' (r', F) : QState _) =
      unifAmp I J m • (A.toOracleAlg ∅).stage (queryPerm F) () k' := by
    ext r'
    rw [purStage_apply]
    rfl
  rw [this, map_smul]
  rfl

/-- A database slice of a compressed Fourier transform as a linear combination of the oracle
slices. -/
theorem slice_compress_fourier (ψ : QState (PurReg W I J m)) (s : Slots I J m t) :
    (WithLp.toLp 2 fun r => compress e t W (fourier _ ψ) (r, s) : QState _) =
      ∑ F, (∑ F', fdb e t F' s * fourierK F' F) • (WithLp.toLp 2 fun r => ψ (r, F) : QState _) := by
  ext r
  simp only [compress_fourier_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul]

end Slices

/-! ### The runs of the inserted expansion after the expansion -/

section AfterExpansion

open ExpandAdv ExpandAt

variable {C C' : Type} (E : Expansion (Bits m) B C) (k : ℕ) {t : ℕ}
  (𝒜 : QueryAlg (Bits m) (BitStr I J) t C') {s : ℕ} (κ : 𝒜.W → C)

/-- **The run of the inserted expansion after it, with oracle `H`**: `𝒜`'s run with the
expansion's answers written (`hybrid_expAtStep_of_le`). -/
theorem stage_expandAt (H : Bits m → BitStr I J) (hs : s ≤ t) (hκ : KeepsClasses 𝒜 s κ) {j : ℕ}
    (hj : s + j ≤ t) :
    ((expandAt e E k 𝒜 s κ).toOracleAlg ∅).stage (queryPerm H) () (s + k + j) =
      embedAns k (ansOf e E k 𝒜 κ H) ((𝒜.toOracleAlg ∅).stage (queryPerm H) () (s + j)) := by
  have h := hybrid_expAtStep_of_le e E k 𝒜 κ H hs hκ j hj
  have hf : (𝒜.toOracleAlg ∅).stage (queryPerm H) () (s + j) =
      hybrid ((𝒜.toOracleAlg ∅).stepAt ()) (fun _ => permOp (queryPerm H)) 𝒜.init (s + j) := rfl
  rw [hf, ← h]
  refine hybrid_congr_le _ _ _ fun i hi => ?_
  exact (expandAt e E k 𝒜 s κ).toOracleAlg ∅ |>.stepAt_of_lt (by omega)

/-- The unitary of the inserted expansion after the expansion is `𝒜`'s unitary on its registers. -/
theorem stepAt_expandAt_of_gt {j : ℕ} (hj1 : 1 ≤ j) (hj : s + j ≤ t) :
    ((expandAt e E k 𝒜 s κ).toOracleAlg ∅).stepAt () (s + k + j) =
      lift k ((𝒜.toOracleAlg ∅).stepAt () (s + j)) := by
  rw [OracleAlg.stepAt_of_lt _ (by omega)]
  show expAtStep e E k 𝒜 s κ (s + k + j) = _
  simp only [expAtStep, if_neg (show ¬ s + k + j < s by omega),
    if_neg (show s + k + j ≠ s by omega), if_neg (show ¬ s + k + j < s + k by omega),
    if_neg (show s + k + j ≠ s + k by omega), show s + k + j - k = s + j by omega]

/-- **The simulated final state of the inserted expansion lives where `𝒜`'s final states live**:
if every final state of `𝒜` with a classical oracle vanishes outside `{Q}` on the work register,
the simulated final state of `𝒜_E` vanishes outside `{Q}` on `𝒜`'s part of its work register
(`simStage_eq_compress_stages`, `stage_expandAt`, `embedAns_apply`). -/
theorem simState_expandAt_eq_zero (hs : s ≤ t) (hκ : KeepsClasses 𝒜 s κ) {Q : 𝒜.W → Prop}
    (hQ : ∀ (H : Bits m → BitStr I J) (r : QueryReg 𝒜.W 1 (Bits m) (BitStr I J)), 𝒜.final H r ≠ 0 → Q r.1)
    {b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k)} (hb : ¬ Q b.1.1.1) :
    simState e (expandAt e E k 𝒜 s κ) b = 0 := by
  obtain ⟨r, sl⟩ := b
  rw [simState, simStage_eq_compress_stages e _ le_rfl, compress_fourier_apply]
  refine Finset.sum_eq_zero fun F _ => ?_
  have h := stage_expandAt e E k 𝒜 κ F hs hκ (j := t - s) (by omega)
  rw [show s + k + (t - s) = t + k by omega, show s + (t - s) = t by omega] at h
  have hz : ((expandAt e E k 𝒜 s κ).toOracleAlg ∅).stage (queryPerm F) () (t + k) r = 0 := by
    rw [h]
    erw [embedAns_apply]
    split_ifs
    · by_contra hne
      exact hb (hQ F _ hne)
    · rfl
  change _ * (unifAmp I J m * _) = 0
  rw [hz, mul_zero, mul_zero]

/-- **CMS19 Proposition 8.11 for the inserted expansion** (`winO_expandAdv` with
`expandAt_realLaw`): if every accepted outcome of `𝒜`, expanded by `E` read through `π`, wins the
base game `G`, then the probability of acceptance is at most the probability that `𝒜_E` wins
`G` against the random oracle. -/
theorem winO_expandAt [Fintype B] [Nonempty B] (π : C' → C) (hs : s ≤ t)
    (hκ : KeepsClasses 𝒜 s κ)
    (hout : ∀ (H : Bits m → BitStr I J) (r : QueryReg 𝒜.W 1 (Bits m) (BitStr I J)), 𝒜.final H r ≠ 0 →
      κ r.1 = π (𝒜.out r.1))
    {G : BaseGame (Bits m) B C' k} {Acc : Set (Outcome C' (Bits m) B)}
    (hG : ∀ p ∈ Acc, (E.comapIn π).expand p.oracle p.out ∈ G) :
    (𝒜.realLaw e).toOuterMeasure Acc ≤ winO e (expandAt e E k 𝒜 s κ) G := by
  rw [winO, expandAt_realLaw e E k 𝒜 κ π hs hκ hout, PMF.toOuterMeasure_map_apply]
  exact MeasureTheory.measure_mono fun p hp => ⟨hG p hp, fun _ => rfl⟩

variable {Λ : Type*} [DecidableEq Λ] (L : C → (Fin k → B) → DB (Bits m) B → Λ)

/-- **A lifted unitary commutes with a label projection on a compressed superposition of states
with answers written** (module docstring): if each oracle slice of `ψ` is a multiple of
`embedAns` of a state `w F` on which `U` keeps the classes of `κ`, then `U ⊗ 1` commutes with the
projection onto the label `i` on `compress (fourier ψ)`. -/
theorem controlled_lift_labelProj_comm {T : ℕ} (U : QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
      QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J)))
    (A : (Bits m → BitStr I J) → C → Fin k → BitStr I J)
    (w : (Bits m → BitStr I J) → QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J)))
    (hU : ∀ F (T : Set C), U (mask {r | κ r.1 ∈ T} (w F)) = mask {r | κ r.1 ∈ T} (U (w F)))
    (c : ℂ) (ψ : QState (PurReg (ExpansionRegister (X := Bits m) (Y := BitStr I J) k 𝒜.W) I J m))
    (hψ : ∀ F, (WithLp.toLp 2 fun b => ψ (b, F) : QState _) =
      c • embedAns k (fun w' => A F (κ w')) (w F)) (i : Λ) :
    controlled (fun _ => lift k U)
        (labelProj e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k 𝒜.W) T
          (fun w' D => L (κ w'.1) (fun j => e (w'.2.2 j)) D) i
          (compress e T _ (fourier _ ψ))) =
      labelProj e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k 𝒜.W) T
          (fun w' D => L (κ w'.1) (fun j => e (w'.2.2 j)) D) i
        (controlled (fun _ => lift k U) (compress e T _ (fourier _ ψ))) := by
  ext ⟨b, sl⟩
  rw [controlled_apply, labelProj_apply, controlled_apply]
  set M : C → (Bits m × BitStr I J) × (Fin k → BitStr I J) → Prop :=
    fun c z => L c (fun j => e (z.2 j)) (slotsDB e sl) = i
  have hslice : (WithLp.toLp 2 fun b' => labelProj e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k 𝒜.W) T
        (fun w' D => L (κ w'.1) (fun j => e (w'.2.2 j)) D) i (compress e T _ (fourier _ ψ)) (b', sl) :
          QState _) =
      mask {b' | M (κ (registerSplit k 𝒜.W b').1.1) (registerSplit k 𝒜.W b').2}
        (WithLp.toLp 2 fun b' => compress e T _ (fourier _ ψ) (b', sl)) := by
    ext b'
    rw [labelProj_apply, mask_apply]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rfl
  have hper : ∀ F, lift k U (mask {b' | M (κ (registerSplit k 𝒜.W b').1.1) (registerSplit k 𝒜.W b').2}
      (embedAns k (fun w' => A F (κ w')) (w F))) =
      mask {b' | M (κ (registerSplit k 𝒜.W b').1.1) (registerSplit k 𝒜.W b').2}
        (lift k U (embedAns k (fun w' => A F (κ w')) (w F))) := fun F =>
    lift_mask_embedAns k κ U (A F) M (hU F)
  rw [hslice, slice_compress_fourier]
  simp_rw [hψ, map_sum, map_smul, hper]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, mask_apply, Set.indicator_apply,
    Set.mem_setOf_eq, smul_eq_mul]
  by_cases hc : L (κ b.1.1) (fun j => e (b.1.2.2 j)) (slotsDB e sl) = i
  · have hc' : M (κ (registerSplit k 𝒜.W b).1.1) (registerSplit k 𝒜.W b).2 := hc
    rw [if_pos hc]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [if_pos hc']
  · have hc' : ¬ M (κ (registerSplit k 𝒜.W b).1.1) (registerSplit k 𝒜.W b).2 := hc
    rw [if_neg hc]
    refine Finset.sum_eq_zero fun F _ => ?_
    rw [if_neg hc', mul_zero, mul_zero]

/-- **The label of a work register value of the inserted expansion and a database**: `L` at the
control `κ w`, the answer slots read through `e`, and the database. -/
def labelOf (w : (expandAt e E k 𝒜 s κ).W) (D : DB (Bits m) B) : Λ :=
  L (κ w.1) (fun j => e (w.2.2 j)) D

/-- **The unitaries after the expansion commute with the label projections** on the simulated
states they act on, when `𝒜`'s unitaries after step `s` keep the classes of `κ`
(`controlled_lift_labelProj_comm` at the slices given by `simQuery_simStage_eq_compress` and
`stage_expandAt`). -/
theorem simStep_labelProj_comm (hs : s ≤ t) (hκ : KeepsClasses 𝒜 s κ) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : s + j ≤ t) (i : Λ) :
    simStep (expandAt e E k 𝒜 s κ) (s + k + j)
        (labelProj e (expandAt e E k 𝒜 s κ).W (t + k) (labelOf e E k 𝒜 κ L) i
          (simQuery e (expandAt e E k 𝒜 s κ).W (t + k)
            (simStage e (expandAt e E k 𝒜 s κ) (s + k + (j - 1))))) =
      labelProj e (expandAt e E k 𝒜 s κ).W (t + k) (labelOf e E k 𝒜 κ L) i
        (simStep (expandAt e E k 𝒜 s κ) (s + k + j)
          (simQuery e (expandAt e E k 𝒜 s κ).W (t + k)
            (simStage e (expandAt e E k 𝒜 s κ) (s + k + (j - 1))))) := by
  set U := (𝒜.toOracleAlg ∅).stepAt () (s + j)
  set w : (Bits m → BitStr I J) → QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J)) := fun F =>
    permOp (queryPerm F) ((𝒜.toOracleAlg ∅).stage (queryPerm F) () (s + (j - 1)))
  have hU : ∀ F (T : Set C), U (mask {r | κ r.1 ∈ T} (w F)) = mask {r | κ r.1 ∈ T} (U (w F)) :=
    fun F T => by
      have := hκ F (s + j) (by omega) hj T
      rw [show s + j - 1 = s + (j - 1) by omega] at this
      exact this
  have hψ : ∀ F, (WithLp.toLp 2 fun b => (WithLp.toLp 2 fun b' : PurReg (expandAt e E k 𝒜 s κ).W I J m =>
      unifAmp I J m * permOp (queryPerm b'.2) (((expandAt e E k 𝒜 s κ).toOracleAlg ∅).stage
        (queryPerm b'.2) () (s + k + (j - 1))) b'.1 : QState _) (b, F) : QState _) =
      unifAmp I J m • embedAns k (fun w' => ansUpTo e E k F (κ w') k) (w F) := fun F => by
    have h1 := stage_expandAt e E k 𝒜 κ F hs hκ (j := j - 1) (by omega)
    have h2 := congrArg (fun v => v) (queryPerm_embedAns k F (ansOf e E k 𝒜 κ F)
      ((𝒜.toOracleAlg ∅).stage (queryPerm F) () (s + (j - 1))))
    ext b
    change unifAmp I J m * (permOp (queryPerm F) (((expandAt e E k 𝒜 s κ).toOracleAlg ∅).stage
      (queryPerm F) () (s + k + (j - 1)))) b = unifAmp I J m * (embedAns k (ansOf e E k 𝒜 κ F) (w F)) b
    rw [h1]
    erw [h2]
  have hstep : simStep (expandAt e E k 𝒜 s κ) (s + k + j) = controlled fun _ => lift k U := by
    rw [simStep, stepAt_expandAt_of_gt e E k 𝒜 κ hj1 hj]
    rfl
  rw [simQuery_simStage_eq_compress e (expandAt e E k 𝒜 s κ) (by omega), hstep]
  exact controlled_lift_labelProj_comm e k 𝒜 κ L U (fun F c => ansUpTo e E k F c k) w hU
    (unifAmp I J m) _ hψ i

end AfterExpansion

/-! ### Measuring before the segment and at the end -/

section Swap

open ExpandAdv ExpandAt

/-- **The projection of the direct sum onto an event of the label and the work register**: the
member `i` is projected onto `S` if `i ∈ R` and is removed otherwise. -/
noncomputable def famMask {κ Λ : Type*} [Fintype κ] (R : Set Λ) (S : Set κ) :
    (PiLp 2 fun _ : Λ => QState κ) →ₗ[ℂ] PiLp 2 fun _ : Λ => QState κ := by
  classical
  exact
  { toFun := fun f => WithLp.toLp 2 fun i => if i ∈ R then mask S (f i) else 0
    map_add' := fun f g => by
      ext i : 1
      by_cases h : i ∈ R <;> simp [h]
    map_smul' := fun c f => by
      ext i : 1
      by_cases h : i ∈ R <;> simp [h] }

theorem famMask_apply {κ Λ : Type*} [Fintype κ] (R : Set Λ) (S : Set κ)
    (f : PiLp 2 fun _ : Λ => QState κ) (i : Λ) :
    famMask R S f i = (by classical exact if i ∈ R then mask S (f i) else 0) := by
  classical
  simp only [famMask, LinearMap.coe_mk, AddHom.coe_mk]

theorem norm_famMask_sq_add {κ Λ : Type*} [Fintype κ] [Fintype Λ] (R : Set Λ) (S : Set κ)
    (f : PiLp 2 fun _ : Λ => QState κ) :
    ‖famMask R S f‖ ^ 2 + ‖f - famMask R S f‖ ^ 2 = ‖f‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.sub_apply, famMask_apply]
  split_ifs
  · have h : f i - mask S (f i) = mask Sᶜ (f i) := by
      rw [sub_eq_iff_eq_add', mask_add_mask_compl]
    rw [h, ← norm_sq_eq_norm_mask_sq_add]
  · simp

/-- **Born probabilities of an event of the label and the work register move by at most the
distance of the families** (`abs_norm_sq_sub_le` at `famMask`): for two families whose squared
norms sum to `1`. -/
theorem abs_sum_mask_sub_le {κ Λ : Type*} [Fintype κ] [Fintype Λ] (R : Set Λ) (S : Set κ)
    (x y : Λ → QState κ) (hx : ∑ i, ‖x i‖ ^ 2 = 1) (hy : ∑ i, ‖y i‖ ^ 2 = 1) :
    |‖famMask R S (famVec x)‖ ^ 2 - ‖famMask R S (famVec y)‖ ^ 2| ≤
      ‖famVec fun i => x i - y i‖ := by
  have ha : ‖famVec x‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [norm_famVec_sq, hx, one_pow])
  have hb : ‖famVec y‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [norm_famVec_sq, hy, one_pow])
  have := abs_norm_sq_sub_le (famMask R S) (norm_famMask_sq_add R S) ha hb
  exact this.trans_eq rfl

variable {C C' : Type} (E : Expansion (Bits m) B C) (k : ℕ) {t : ℕ}
  (𝒜 : QueryAlg (Bits m) (BitStr I J) t C') (s : ℕ) (κ : 𝒜.W → C)

/-- The unitaries of the segment after the expansion: the identity, then `𝒜_E`'s unitaries after
step `s + k`. -/
noncomputable def segUnitary (j : ℕ) :
    QState (SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k)) →ₗ[ℂ]
      QState (SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k)) :=
  if j = 0 then LinearMap.id
  else (simStep (expandAt e E k 𝒜 s κ) (s + k + j)).toLinearEquiv.toLinearMap

/-- The simulated query of the segment. -/
noncomputable def segQuery :
    QState (SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k)) →ₗ[ℂ]
      QState (SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k)) :=
  (simQuery e (expandAt e E k 𝒜 s κ).W (t + k)).toLinearMap

theorem segRun_simStage : ∀ j,
    segRun (segUnitary e E k 𝒜 s κ) (segQuery e E k 𝒜 s κ) j (simStage e (expandAt e E k 𝒜 s κ) (s + k)) =
      simStage e (expandAt e E k 𝒜 s κ) (s + k + j)
  | 0 => by simp [segRun, segUnitary]
  | j + 1 => by
    rw [segRun, segRun_simStage j]
    simp only [segUnitary, Nat.add_one_ne_zero, if_false, segQuery]
    rfl

theorem segInput_simStage (j : ℕ) :
    segInput (segUnitary e E k 𝒜 s κ) (segQuery e E k 𝒜 s κ) (simStage e (expandAt e E k 𝒜 s κ) (s + k))
        (j + 1) =
      simQuery e (expandAt e E k 𝒜 s κ).W (t + k) (simStage e (expandAt e E k 𝒜 s κ) (s + k + j)) := by
  rw [segInput, segRun_simStage]
  rfl

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (L : C → (Fin k → B) → DB (Bits m) B → Λ)
  (P : (expandAt e E k 𝒜 s κ).W → Prop) (R : Set Λ)

open Classical in
/-- **The probability that the label is in `R` and the work register satisfies `P`**, measured at
the end of the simulated run of `𝒜_E` (the folded order: the label measured after the
segment). -/
noncomputable def foldedProb : ℝ :=
  ∑ i, if i ∈ R then ‖mask {b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k) | P b.1.1}
    (labelProj e (expandAt e E k 𝒜 s κ).W (t + k) (labelOf e E k 𝒜 κ L) i
      (simState e (expandAt e E k 𝒜 s κ)))‖ ^ 2 else 0

open Classical in
/-- **The probability of the same event in the Extract′ order**: the label measured right after
the expansion (`labelProj` at `simStage (s + k)`), then the segment of `t − s` simulated queries
and `𝒜`'s unitaries, then the work register measured. -/
noncomputable def extractAtProb : ℝ :=
  ∑ i, if i ∈ R then ‖mask {b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k) | P b.1.1}
    (segRun (segUnitary e E k 𝒜 s κ) (segQuery e E k 𝒜 s κ) (t - s)
      (labelProj e (expandAt e E k 𝒜 s κ).W (t + k) (labelOf e E k 𝒜 κ L) i
        (simStage e (expandAt e E k 𝒜 s κ) (s + k))))‖ ^ 2 else 0

omit [DecidableEq Λ] in
theorem norm_famMask_famVec_sq {κ : Type*} [Fintype κ] (S : Set κ) (x : Λ → QState κ) :
    ‖famMask R S (famVec x)‖ ^ 2 = (by classical exact ∑ i, if i ∈ R then ‖mask S (x i)‖ ^ 2 else 0) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [famMask_apply]
  split_ifs <;> simp

/-- **The Extract′ order changes the probability by at most `(t − s) √(24 κ)`** (the swap
lemma): `𝒜`'s unitaries after step `s` keep the classes of `κ`, and every partition `L c a` has
generalized instability at most `κ` at the query bound `t + k` (CDHZ26 Definition 5.3, p. 31;
`sum_norm_labelComm_simQuery_le`, `norm_segRun_famDiff_le`, `abs_norm_sq_sub_le`). -/
theorem abs_foldedProb_sub_extractAtProb_le [Fintype B] [Nonempty B] [Nonempty C] (hs : s ≤ t)
    (hκ : KeepsClasses 𝒜 s κ) {κI : ℝ} (hI : ∀ c a, (instabPart (L c a) (t + k)).toReal ≤ κI) :
    |foldedProb e E k 𝒜 s κ L P R - extractAtProb e E k 𝒜 s κ L P R| ≤
      (t - s : ℕ) * Real.sqrt (24 * κI) := by
  classical
  let _ : Fintype (SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k)) := instFintypeProd _ _
  set φ := simStage e (expandAt e E k 𝒜 s κ) (s + k)
  set Pj : Λ → _ := fun i =>
    (labelProj e (expandAt e E k 𝒜 s κ).W (t + k) (labelOf e E k 𝒜 κ L) i).toLinearMap
  set U := segUnitary e E k 𝒜 s κ
  set O := segQuery e E k 𝒜 s κ
  set S := {b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k) | P b.1.1}
  have hφ : ‖φ‖ = 1 := norm_simStage e _ _
  have hU : ∀ j v, ‖U j v‖ = ‖v‖ := fun j v => by
    simp only [U, segUnitary]
    split_ifs
    · rfl
    · exact LinearIsometryEquiv.norm_map _ v
  have hO : ∀ v, ‖O v‖ = ‖v‖ := fun v => norm_simQuery e v
  have hκI : 0 ≤ κI := ENNReal.toReal_nonneg.trans (hI (Classical.arbitrary C) fun _ => Classical.arbitrary B)
  have hε : ∀ v, ‖famVec fun i => Pj i (O v) - O (Pj i v)‖ ≤ Real.sqrt (24 * κI) * ‖v‖ := by
    intro v
    refine norm_famVec_le_of_sum_sq_le (by positivity) ?_
    have h := sum_norm_labelComm_simQuery_le (e := e) (W := (expandAt e E k 𝒜 s κ).W) (t := t + k)
      (labelOf e E k 𝒜 κ L) (κ := κI) (fun z => hI _ _) v
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact h
  have hcomm : ∀ j i, U j (Pj i (segInput U O φ j)) = Pj i (U j (segInput U O φ j)) := by
    intro j i
    rcases j with _ | j
    · simp [U, segUnitary]
    · by_cases hj : s + (j + 1) ≤ t
      · rw [segInput_simStage]
        simp only [U, segUnitary, Nat.add_one_ne_zero, if_false, Pj]
        have := simStep_labelProj_comm e E k 𝒜 κ L hs hκ (j := j + 1) (by omega) hj i
        simpa using this
      · -- past the last unitary the steps are the identity
        have hid : ∀ v, U (j + 1) v = v := fun v => by
          simp only [U, segUnitary, Nat.add_one_ne_zero, if_false]
          change simStep (expandAt e E k 𝒜 s κ) (s + k + (j + 1)) v = v
          ext b
          rw [simStep, controlled_apply, OracleAlg.stepAt, dif_neg (by omega)]
          rfl
        rw [hid, hid]
  have hswap := norm_segRun_famDiff_le Pj hU hO hε hcomm (t - s)
  have hx : ∑ i, ‖Pj i (simState e (expandAt e E k 𝒜 s κ))‖ ^ 2 = 1 := by
    have := sum_norm_labelProj_sq (e := e) (labelOf e E k 𝒜 κ L) (simState e (expandAt e E k 𝒜 s κ))
    have hn : ‖simState e (expandAt e E k 𝒜 s κ)‖ = 1 := norm_simStage e _ _
    rw [hn] at this
    simpa [Pj] using this
  have hy : ∑ i, ‖segRun U O (t - s) (Pj i φ)‖ ^ 2 = 1 := by
    simp_rw [norm_segRun hU hO]
    have := sum_norm_labelProj_sq (e := e) (labelOf e E k 𝒜 κ L) φ
    rw [hφ] at this
    simpa [Pj] using this
  have hrun : segRun U O (t - s) φ = simState e (expandAt e E k 𝒜 s κ) := by
    rw [segRun_simStage, show s + k + (t - s) = t + k by omega]
    rfl
  have h := abs_sum_mask_sub_le R S (fun i => Pj i (simState e (expandAt e E k 𝒜 s κ)))
    (fun i => segRun U O (t - s) (Pj i φ)) hx hy
  rw [norm_famMask_famVec_sq, norm_famMask_famVec_sq] at h
  rw [← hrun] at h
  refine le_trans (le_of_eq ?_) (h.trans ?_)
  · rw [foldedProb, extractAtProb, ← hrun]
    rfl
  calc ‖famVec fun i => Pj i (segRun U O (t - s) φ) - segRun U O (t - s) (Pj i φ)‖
      ≤ (t - s : ℕ) * Real.sqrt (24 * κI) * ‖φ‖ := hswap
    _ = (t - s : ℕ) * Real.sqrt (24 * κI) := by rw [hφ, mul_one]

/-- **The folded probability is the Born probability of the event at the end**: the label in `R`
and the work register in `P`. -/
theorem foldedProb_eq_norm_mask :
    foldedProb e E k 𝒜 s κ L P R =
      ‖mask {b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k) |
        P b.1.1 ∧ labelOf e E k 𝒜 κ L b.1.1 (slotsDB e b.2) ∈ R} (simState e (expandAt e E k 𝒜 s κ))‖ ^ 2 := by
  classical
  set v := simState e (expandAt e E k 𝒜 s κ)
  set lab := fun b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k) =>
    labelOf e E k 𝒜 κ L b.1.1 (slotsDB e b.2)
  have h : ∀ i, (if i ∈ R then ‖mask {b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k) | P b.1.1}
      (labelProj e (expandAt e E k 𝒜 s κ).W (t + k) (labelOf e E k 𝒜 κ L) i v)‖ ^ 2 else 0) =
      ∑ b, (if i ∈ R ∧ P b.1.1 ∧ lab b = i then ‖v b‖ ^ 2 else 0) := fun i => by
    by_cases hi : i ∈ R
    · rw [if_pos hi, EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [mask_apply, Set.indicator_apply, Set.mem_setOf_eq, labelProj_apply]
      by_cases hP : P b.1.1 <;> by_cases hl : lab b = i
      · rw [if_pos hP, if_pos hl, if_pos ⟨hi, hP, hl⟩]
      · rw [if_pos hP, if_neg hl, if_neg (fun hc => hl hc.2.2)]
        simp
      · rw [if_neg hP, if_neg (fun hc => hP hc.2.1)]
        simp
      · rw [if_neg hP, if_neg (fun hc => hP hc.2.1)]
        simp
    · rw [if_neg hi]
      exact (Finset.sum_eq_zero fun b _ => if_neg (fun hc => hi hc.1)).symm
  rw [foldedProb]
  refine (Finset.sum_congr rfl fun i _ => h i :
    _ = ∑ i, ∑ b, (if i ∈ R ∧ P b.1.1 ∧ lab b = i then ‖v b‖ ^ 2 else 0)).trans ?_
  rw [Finset.sum_comm, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mask_apply]
  by_cases hP : P b.1.1 <;> by_cases hl : lab b ∈ R
  · rw [Finset.sum_eq_single (lab b) (fun i _ hne => by simp [Ne.symm hne]) (by simp)]
    simp [hP, hl, lab]
  · rw [Finset.sum_eq_zero fun i _ => by
      split_ifs with hc
      · exact absurd (hc.2.2 ▸ hc.1) hl
      · rfl]
    simp [hl, lab]
  · rw [Finset.sum_eq_zero fun i _ => by simp [hP]]
    simp [hP]
  · rw [Finset.sum_eq_zero fun i _ => by simp [hP]]
    simp [hP]

/-- **An event of the simulated run's outcome is bounded by the folded probability** when on the
support of the simulated final state the event implies the work-register predicate `P` and a label
in `R` (`foldedProb_eq_norm_mask`, `bornWeight_apply_eq_sum`). -/
theorem simLaw_le_ofReal_foldedProb {R' : BaseGame.Tuple (Bits m) B C' k → DB (Bits m) B → Prop}
    (h : ∀ b : SimRegister (expandAt e E k 𝒜 s κ).W I J m (t + k),
      simState e (expandAt e E k 𝒜 s κ) b ≠ 0 →
      R' ((expandAt e E k 𝒜 s κ).out b.1.1) (slotsDB e b.2) →
      P b.1.1 ∧ labelOf e E k 𝒜 κ L b.1.1 (slotsDB e b.2) ∈ R) :
    simLaw e (expandAt e E k 𝒜 s κ) {p | R' p.1 p.2} ≤ ENNReal.ofReal (foldedProb e E k 𝒜 s κ L P R) := by
  classical
  set v := simState e (expandAt e E k 𝒜 s κ)
  have hS : ENNReal.ofReal (foldedProb e E k 𝒜 s κ L P R) = bornWeight v
      {b | P b.1.1 ∧ labelOf e E k 𝒜 κ L b.1.1 (slotsDB e b.2) ∈ R} := by
    rw [foldedProb_eq_norm_mask, bornWeight_apply, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hS, simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply_eq_sum,
    bornWeight_apply_eq_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs with h1 h2
  · exact le_rfl
  · by_cases hb : v b = 0
    · show ‖v b‖ₑ ^ 2 ≤ 0
      simp [hb]
    · exact absurd (h b hb h1) h2
  · exact bot_le
  · exact le_rfl

end Swap

end GordieHowe.QROM
