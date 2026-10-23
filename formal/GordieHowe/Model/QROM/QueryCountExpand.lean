-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.QueryCount

@[expose] public section

/-!
# The per-branch count of an expanded adversary

The expanded adversary of CMS19 Proposition 8.11 (`expandAdv e E K 𝒜`, `GordieHowe/Model/QROM/ExpandAdv.lean`)
runs `𝒜` with fresh registers beside its work register and then makes `K` classical queries. If
every branch of `𝒜` queries at no more than `b` of its steps (`QueryCount`), every branch of the
expanded adversary queries at no more than `b + K` (`QueryCount.expandAdv`): before `𝒜`'s last
step the run is `𝒜`'s with the fresh registers appended (`appendS`), which a simulated query and
`𝒜`'s lifted steps keep (`simQuery_appendS`, `simStepS_expandAdv_appendS`), and the `K` expansion
queries are counted on every branch.
-/

open Finset GordieHowe.Quantum
open scoped BigOperators

namespace GordieHowe.QROM

open ExpandAdv

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} (e : BitStr I J ≃ B) (K : ℕ)

/-! ### The fresh registers on the simulated run -/

section Append

variable {W : Type} [Fintype W] [DecidableEq W] {s : ℕ}

/-- The expansion's work register beside `W`, on the basis of `Sim*`. -/
abbrev ExpSim (W : Type) (s : ℕ) :=
  SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) K W) I J m s

/-- **The fresh registers appended on the simulated run**: the stash `(default, 0)` and the answer
slots `0` beside the work register `W`. -/
noncomputable def appendS (v : QState (SimRegister W I J m s)) :
    QState (ExpSim (I := I) (J := J) (m := m) K W s) :=
  WithLp.toLp 2 fun b => v ((b.1.1.1, b.1.2), b.2) * if b.1.1.2 = fresh K then 1 else 0

omit [DecidableEq W] in
theorem appendS_apply (v : QState (SimRegister W I J m s)) (b : ExpSim (I := I) (J := J) (m := m) K W s) :
    appendS K v b = v ((b.1.1.1, b.1.2), b.2) * if b.1.1.2 = fresh K then 1 else 0 :=
  rfl

/-- The basis of the expanded simulated run as the basis of the simulated run and the fresh
registers. -/
def expSplit (W : Type) (s : ℕ) :
    ExpSim (I := I) (J := J) (m := m) K W s ≃
      SimRegister W I J m s × ((Bits m × BitStr I J) × (Fin K → BitStr I J)) where
  toFun b := (((b.1.1.1, b.1.2), b.2), b.1.1.2)
  invFun p := (((p.1.1.1, p.2), p.1.1.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq W] in
/-- **An operator that reads the work register only through equalities commutes with appending the
fresh registers.** -/
theorem kernelOp_appendS {K'' : ExpSim (I := I) (J := J) (m := m) K W s →
      ExpSim (I := I) (J := J) (m := m) K W s → ℂ}
    {K₀ : SimRegister W I J m s → SimRegister W I J m s → ℂ}
    (hK : ∀ b' (x : SimRegister W I J m s), K'' b' (((x.1.1, fresh K), x.1.2), x.2) =
      if b'.1.1.2 = fresh K then K₀ ((b'.1.1.1, b'.1.2), b'.2) x else 0)
    (v : QState (SimRegister W I J m s)) :
    kernelOp K'' (appendS K v) = appendS K (kernelOp K₀ v) := by
  classical
  letI : Fintype (SimRegister W I J m s × ((Bits m × BitStr I J) × (Fin K → BitStr I J))) :=
    @instFintypeProd _ _ inferInstance inferInstance
  ext b'
  rw [kernelOp_apply, appendS_apply, kernelOp_apply, ← (expSplit K W s).symm.sum_comp,
    Fintype.sum_prod_type]
  have hinner : ∀ x : SimRegister W I J m s,
      ∑ f, K'' b' ((expSplit K W s).symm (x, f)) * appendS K v ((expSplit K W s).symm (x, f)) =
        K'' b' (((x.1.1, fresh K), x.1.2), x.2) * v x := by
    intro x
    rw [Finset.sum_eq_single (fresh K)]
    · simp [expSplit, appendS_apply]
    · intro f _ hf
      simp [expSplit, appendS_apply, hf]
    · simp
  simp_rw [hinner, hK]
  by_cases hb : b'.1.1.2 = fresh K
  · simp [hb]
  · simp [hb]

/-- **A simulated query commutes with appending the fresh registers**: the Hadamard transform,
`Dec` and `O0` read the work register only through equalities. -/
theorem simQuery_appendS (v : QState (SimRegister W I J m s)) :
    simQuery e _ s (appendS K v) = appendS K (simQuery e W s v) := by
  classical
  have hH : ∀ x : QState (SimRegister W I J m s),
      hadamard _ s (appendS K x) = appendS K (hadamard W s x) := fun x =>
    kernelOp_appendS K (fun b' y => by
      obtain ⟨⟨⟨w', f'⟩, q'⟩, d'⟩ := b'
      obtain ⟨⟨yw, yq⟩, yd⟩ := y
      by_cases hb : f' = fresh K
      · subst hb
        simp
      · simp [hb]) x
  have hD : ∀ x : QState (SimRegister W I J m s),
      decOp e _ s (appendS K x) = appendS K (decOp e W s x) := fun x => by
    rw [decOp_eq, decOp_eq]
    exact kernelOp_appendS K (fun b' y => by
      obtain ⟨⟨⟨w', f'⟩, q'⟩, d'⟩ := b'
      obtain ⟨⟨yw, yq⟩, yd⟩ := y
      by_cases hb : f' = fresh K
      · subst hb
        simp
      · simp [hb]) x
  have hP : ∀ x : QState (SimRegister W I J m s),
      phaseOp e _ s (appendS K x) = appendS K (phaseOp e W s x) := fun x =>
    kernelOp_appendS K (fun b' y => by
      obtain ⟨⟨⟨w', f'⟩, q'⟩, d'⟩ := b'
      obtain ⟨⟨yw, yq⟩, yd⟩ := y
      by_cases hb : f' = fresh K
      · subst hb
        simp
      · simp [hb]) x
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply, hH, hD, hP]

omit [DecidableEq W] in
/-- Appending the fresh registers commutes with a projection of the database register. -/
theorem dbProj_appendS (P : Set (DB (Bits m) B)) (v : QState (SimRegister W I J m s)) :
    dbProj e _ s P (appendS K v) = appendS K (dbProj e W s P v) := by
  ext b
  simp only [dbProj_eq, mask_apply, appendS_apply, Set.indicator, dbSet, Set.mem_setOf_eq]
  by_cases h1 : InP e s P b.2 <;> by_cases h2 : b.1.1.2 = fresh K <;> simp [h1, h2]

omit [DecidableEq W] in
/-- Appending the fresh registers commutes with a projection of `𝒜`'s work register. -/
theorem mask_appendS (S : Set W) (v : QState (SimRegister W I J m s)) :
    mask (workSet _ s {w : ExpansionRegister (X := Bits m) (Y := BitStr I J) K W | w.1 ∈ S})ᶜ
      (appendS K v) = appendS K (mask (workSet W s S)ᶜ v) := by
  ext b
  simp only [mask_apply, appendS_apply, Set.indicator, workSet, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  by_cases h1 : b.1.1.1 ∈ S <;> by_cases h2 : b.1.1.2 = fresh K <;> simp [h1, h2]

end Append

/-! ### The count of the expanded adversary -/

section Expand

variable {B' C : Type} (e' : BitStr I J ≃ B') (E : Expansion (Bits m) B' C) {t : ℕ}
  (𝒜 : QueryAlg (Bits m) (BitStr I J) t C)

/-- `𝒜`'s step `j < t`, lifted to the expanded adversary, on the simulated run with the fresh
registers appended. -/
theorem simStepS_expandAdv_appendS {s j : ℕ} (hj : j < t) (v : QState (SimRegister 𝒜.W I J m s)) :
    simStepS (expandAdv e' E K 𝒜) s j (appendS K v) = appendS K (simStepS 𝒜 s j v) := by
  have hstep : ((expandAdv e' E K 𝒜).toOracleAlg ∅).stepAt () j =
      lift K ((𝒜.toOracleAlg ∅).stepAt () j) := by
    rw [OracleAlg.stepAt_of_lt _ (by omega)]
    simp only [QueryAlg.toOracleAlg, expandAdv, expStep, if_pos hj]
    rfl
  ext ⟨r, d⟩
  have key : ((expandAdv e' E K 𝒜).toOracleAlg ∅).stepAt () j
      (WithLp.toLp 2 fun i => appendS K v (i, d)) =
      ExpandAdv.embed K ((𝒜.toOracleAlg ∅).stepAt () j (WithLp.toLp 2 fun i => v (i, d))) := by
    rw [hstep]
    have hslice : (WithLp.toLp 2 fun i => appendS K v (i, d) :
        QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)) =
        ExpandAdv.embed K (WithLp.toLp 2 fun i => v (i, d)) := by
      ext ⟨⟨w, f⟩, q⟩
      rfl
    exact (congrArg (lift K ((𝒜.toOracleAlg ∅).stepAt () j)) hslice).trans (lift_embed K _ _)
  exact congrArg (fun x => x r) key

theorem simQuery_appendS_expandAdv {s : ℕ} (v : QState (SimRegister 𝒜.W I J m s)) :
    (simQuery e (expandAdv e' E K 𝒜).W s (appendS K v) :
      QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) = appendS K (simQuery e 𝒜.W s v) :=
  simQuery_appendS e K v

theorem dbProj_appendS_expandAdv {s : ℕ} (P : Set (DB (Bits m) B))
    (v : QState (SimRegister 𝒜.W I J m s)) :
    (dbProj e (expandAdv e' E K 𝒜).W s P (appendS K v) :
      QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) = appendS K (dbProj e 𝒜.W s P v) :=
  dbProj_appendS e K P v

theorem mask_appendS_expandAdv {s : ℕ} (S : Set 𝒜.W) (v : QState (SimRegister 𝒜.W I J m s)) :
    (mask (workSet (expandAdv e' E K 𝒜).W s {w : ExpansionRegister (X := Bits m) (Y := BitStr I J)
      K 𝒜.W | w.1 ∈ S})ᶜ (appendS K v) : QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) =
      appendS K (mask (workSet 𝒜.W s S)ᶜ v) :=
  mask_appendS K S v

/-- The classical steps of the expansion do not change `𝒜`'s work register. -/
theorem expPerm_fst (o : 𝒜.W → C) (i : ℕ) (r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W) :
    (expPerm e' E K o i r).1.1 = r.1.1 := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [expPerm, Equiv.trans_apply]
    change (recordPerm K i r).1.1 = r.1.1
    unfold recordPerm
    split_ifs <;> rfl

/-- A vector with the fresh registers in their initial content is `embed` of its restriction. -/
theorem eq_embed_of_supported {u : QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)}
    (hu : Supported {r | r.1.2 = fresh K} u) :
    u = ExpandAdv.embed K (WithLp.toLp 2 fun r => u ((r.1, fresh K), r.2)) := by
  ext ⟨⟨w, f⟩, q⟩
  simp only [ExpandAdv.embed, relabel_apply, tensorKet_apply, registerSplit, Equiv.coe_fn_symm_mk]
  by_cases hf : f = fresh K
  · subst hf
    simp
  · rw [hu _ hf]
    simp [hf]

theorem embed_supported {S : Set (QueryReg 𝒜.W 1 (Bits m) (BitStr I J))}
    {u : QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J))} (hu : Supported S u) :
    Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W | (r.1.1, r.2) ∈ S ∧
      r.1.2 = fresh K} (ExpandAdv.embed K u) := by
  intro r hr
  simp only [ExpandAdv.embed, relabel_apply, tensorKet_apply, registerSplit, Equiv.symm_symm,
    Equiv.coe_fn_mk]
  by_cases hf : r.1.2 = fresh K
  · rw [hu _ fun h => hr ⟨h, hf⟩, zero_mul]
  · simp [hf]

/-- The steps of the expanded adversary. -/
theorem stepAt_expandAdv (i : ℕ) (hi : i < t + K + 1) :
    ((expandAdv e' E K 𝒜).toOracleAlg ∅).stepAt () i = expStep e' E K 𝒜 𝒜.out i := by
  rw [OracleAlg.stepAt_of_lt _ hi]
  rfl

variable {e 𝒜} {b : ℕ} (h : QueryCount e 𝒜 b)

/-- The records of the expanded adversary: `𝒜`'s for its queries, and every branch makes the
expansion queries. -/
def expandC : ℕ → Set (expandAdv e' E K 𝒜).W :=
  fun i => if i < t then {w | w.1 ∈ h.C i} else Set.univ

/-- The supports of the expanded adversary: `𝒜`'s with the fresh registers in their initial
content before `𝒜`'s last step, `𝒜`'s final support after it. -/
def expandG : ℕ → Set (expandAdv e' E K 𝒜).W :=
  fun k => if k < t then {w | w.1 ∈ h.G k ∧ w.2 = fresh K} else {w | w.1 ∈ h.G t}

/-- The vectors of the simulated run of the expanded adversary: `𝒜`'s with the fresh registers
appended, before `𝒜`'s last step. -/
def expandInv (s : ℕ) : ℕ → Set (QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) :=
  fun k => if k < t then
    {v | ∃ u ∈ h.Inv s k, (appendS K u : QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) = v}
  else Set.univ

theorem countBelow_expandC (n : ℕ) (w : (expandAdv e' E K 𝒜).W) :
    countBelow (expandC K e' E h) n w = countBelow h.C (min n t) w.1 + (n - t) := by
  induction n with
  | zero => simp [countBelow_zero]
  | succ n ih =>
    rw [countBelow_succ, ih]
    by_cases hn : n < t
    · rw [min_eq_left (by omega : n + 1 ≤ t), min_eq_left hn.le, countBelow_succ]
      rw [show expandC K e' E h n = {w | w.1 ∈ h.C n} from if_pos hn]
      have h1 : n + 1 - t = 0 := by omega
      have h2 : n - t = 0 := by omega
      rw [h1, h2]
      by_cases hc : w.1 ∈ h.C n <;> simp [hc]
    · rw [min_eq_right (by omega : t ≤ n + 1), min_eq_right (by omega : t ≤ n)]
      rw [show expandC K e' E h n = Set.univ from if_neg hn]
      simp only [Set.mem_univ, if_true]
      omega

/-- `𝒜`'s lifted step keeps a support of `𝒜`'s work register that its step keeps, with the fresh
registers in their initial content. -/
theorem lift_supported {S S' : Set 𝒜.W}
    {U : QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J))}
    (hU : ∀ u, Supported {r | r.1 ∈ S} u → Supported {r | r.1 ∈ S'} (U u))
    {v : QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)}
    (hv : Supported {r | r.1.1 ∈ S ∧ r.1.2 = fresh K} v) :
    Supported {r | r.1.1 ∈ S' ∧ r.1.2 = fresh K} (lift K U v) := by
  rw [eq_embed_of_supported K 𝒜 (hv.mono fun _ h => h.2), lift_embed]
  refine (embed_supported K 𝒜 (hU _ fun r hr => ?_)).mono fun _ h => ⟨h.1, h.2⟩
  exact hv _ fun h => hr h.1

/-- The classical steps of the expansion keep every support of `𝒜`'s work register. -/
theorem expPerm_supported (o : 𝒜.W → C) (i : ℕ) {S : Set 𝒜.W}
    {v : QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)}
    (hv : Supported {r | r.1.1 ∈ S} v) :
    Supported {r | r.1.1 ∈ S} (permOp (expPerm e' E K o i) v) :=
  hv.permOp fun r hr => by
    change (expPerm e' E K o i r).1.1 ∈ S
    rw [expPerm_fst]
    exact hr

theorem expand_init :
    Supported {r | r.1 ∈ expandG K e' E h 0}
      (((expandAdv e' E K 𝒜).toOracleAlg ∅).stepAt () 0 (expandAdv e' E K 𝒜).init) := by
  rw [stepAt_expandAdv K e' E 𝒜 0 (by omega)]
  have hemb : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
      r.1.1 ∈ h.G 0 ∧ r.1.2 = fresh K} (lift K ((𝒜.toOracleAlg ∅).stepAt () 0) (ExpandAdv.embed K 𝒜.init)) := by
    rw [lift_embed]
    exact (embed_supported K 𝒜 h.init).mono fun _ h => ⟨h.1, h.2⟩
  by_cases ht : 0 < t
  · simp only [expStep, if_pos ht]
    refine hemb.mono fun r hr => ?_
    change r.1 ∈ expandG K e' E h 0
    simp only [expandG, if_pos ht]
    exact hr
  · have ht0 : t = 0 := by omega
    simp only [expStep, if_neg ht, if_pos ht0.symm]
    have hemb' := hemb
    rw [← congrArg ((𝒜.toOracleAlg ∅).stepAt ()) ht0] at hemb'
    have key : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W | r.1 ∈ expandG K e' E h 0}
        (permOp (expPerm e' E K 𝒜.out 0) (lift K ((𝒜.toOracleAlg ∅).stepAt () t)
          (ExpandAdv.embed K 𝒜.init))) := by
      refine (expPerm_supported K e' E 𝒜.out 0 (hemb'.mono fun _ h => h.1)).mono fun r hr => ?_
      change r.1 ∈ expandG K e' E h 0
      simp only [expandG, if_neg ht]
      show r.1.1 ∈ h.G t
      rw [congrArg h.G ht0]
      exact hr
    exact key

theorem expand_stepG {k : ℕ} (hk : k < t + K)
    {v : QState (QueryReg (expandAdv e' E K 𝒜).W 1 (Bits m) (BitStr I J))}
    (hv : Supported {r | r.1 ∈ expandG K e' E h k} v) :
    Supported {r | r.1 ∈ expandG K e' E h (k + 1)}
      (((expandAdv e' E K 𝒜).toOracleAlg ∅).stepAt () (k + 1) v) := by
  rw [stepAt_expandAdv K e' E 𝒜 (k + 1) (by omega)]
  by_cases h1 : k + 1 < t
  · have hk' : k < t := by omega
    simp only [expStep, if_pos h1]
    have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
        r.1.1 ∈ h.G k ∧ r.1.2 = fresh K} v := fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ expandG K e' E h k := h'
          rwa [show expandG K e' E h k = {w | w.1 ∈ h.G k ∧ w.2 = fresh K} from if_pos hk'] at h'')
    refine (lift_supported K (fun u hu => h.stepG k (by omega) u hu) hv').mono fun r hr => ?_
    change r.1 ∈ expandG K e' E h (k + 1)
    simp only [expandG, if_pos h1]
    exact hr
  · by_cases h2 : k + 1 = t
    · have hk' : k < t := by omega
      simp only [expStep, if_neg h1, if_pos h2]
      have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
          r.1.1 ∈ h.G k ∧ r.1.2 = fresh K} v := fun r hr => hv r fun h' => hr (by
            have h'' : r.1 ∈ expandG K e' E h k := h'
            rwa [show expandG K e' E h k = {w | w.1 ∈ h.G k ∧ w.2 = fresh K} from if_pos hk'] at h'')
      have hl := lift_supported K (fun u hu => h.stepG k (by omega) u hu) hv'
      rw [congrArg ((𝒜.toOracleAlg ∅).stepAt ()) h2] at hl
      have key : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
          r.1 ∈ expandG K e' E h (k + 1)}
          (permOp (expPerm e' E K 𝒜.out 0) (lift K ((𝒜.toOracleAlg ∅).stepAt () t) v)) := by
        refine (expPerm_supported K e' E 𝒜.out 0 (hl.mono fun _ h => h.1)).mono fun r hr => ?_
        change r.1 ∈ expandG K e' E h (k + 1)
        simp only [expandG, if_neg h1]
        show r.1.1 ∈ h.G t
        rw [← congrArg h.G h2]
        exact hr
      exact key
    · have hk' : ¬ k < t := by omega
      simp only [expStep, if_neg h1, if_neg h2]
      have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W | r.1.1 ∈ h.G t} v :=
        fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ expandG K e' E h k := h'
          rwa [show expandG K e' E h k = {w | w.1 ∈ h.G t} from if_neg hk'] at h'')
      refine (expPerm_supported K e' E 𝒜.out _ hv').mono fun r hr => ?_
      change r.1 ∈ expandG K e' E h (k + 1)
      simp only [expandG, if_neg h1]
      exact hr

/-- **A step of the expanded adversary keeps a record of `𝒜`'s work register** that `𝒜`'s steps
keep. -/
theorem expand_stepKeep {T : Set 𝒜.W} {k : ℕ} (hk : k < t + K)
    (hT : k + 1 ≤ t → ∀ u, Supported {r | r.1 ∈ T ∩ h.G k} u →
      Supported {r | r.1 ∈ T} ((𝒜.toOracleAlg ∅).stepAt () (k + 1) u))
    {v : QState (QueryReg (expandAdv e' E K 𝒜).W 1 (Bits m) (BitStr I J))}
    (hv : Supported {r | r.1.1 ∈ T ∧ r.1 ∈ expandG K e' E h k} v) :
    Supported {r | r.1.1 ∈ T} (((expandAdv e' E K 𝒜).toOracleAlg ∅).stepAt () (k + 1) v) := by
  rw [stepAt_expandAdv K e' E 𝒜 (k + 1) (by omega)]
  by_cases h1 : k + 1 ≤ t
  · have hk' : k < t := by omega
    have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
        r.1.1 ∈ T ∩ h.G k ∧ r.1.2 = fresh K} v := fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ expandG K e' E h k := h'.2
          rw [show expandG K e' E h k = {w | w.1 ∈ h.G k ∧ w.2 = fresh K} from if_pos hk'] at h''
          exact ⟨⟨h'.1, h''.1⟩, h''.2⟩)
    have hl := lift_supported K (hT h1) hv'
    by_cases h2 : k + 1 < t
    · simp only [expStep, if_pos h2]
      exact hl.mono fun _ h => h.1
    · have h3 : k + 1 = t := by omega
      simp only [expStep, if_neg h2, if_pos h3]
      rw [congrArg ((𝒜.toOracleAlg ∅).stepAt ()) h3] at hl
      have key : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W | r.1.1 ∈ T}
          (permOp (expPerm e' E K 𝒜.out 0) (lift K ((𝒜.toOracleAlg ∅).stepAt () t) v)) :=
        expPerm_supported K e' E 𝒜.out 0 (hl.mono fun _ h => h.1)
      exact key
  · simp only [expStep, if_neg (show ¬ k + 1 < t by omega), if_neg (show ¬ k + 1 = t by omega)]
    exact expPerm_supported K e' E 𝒜.out _ (hv.mono fun _ h => h.1)

theorem expand_count : ∀ k ≤ t + K, ∀ w ∈ expandG K e' E h k,
    countBelow (expandC K e' E h) (min (k + 1) (t + K)) w ≤ b + K := by
  intro k hk w hw
  rw [countBelow_expandC]
  by_cases hkt : k < t
  · rw [show expandG K e' E h k = {w | w.1 ∈ h.G k ∧ w.2 = fresh K} from if_pos hkt] at hw
    have hc := h.count k hkt.le w.1 hw.1
    rw [min_eq_left (by omega : k + 1 ≤ t)] at hc
    rw [min_eq_left (by omega : k + 1 ≤ t + K), min_eq_left (by omega : k + 1 ≤ t)]
    omega
  · rw [show expandG K e' E h k = {w | w.1 ∈ h.G t} from if_neg hkt] at hw
    have hc := h.count t le_rfl w.1 hw
    rw [min_eq_right (Nat.le_succ t)] at hc
    rw [min_eq_right (by omega : t ≤ min (k + 1) (t + K))]
    have : min (k + 1) (t + K) - t ≤ K := by omega
    omega

theorem simInitS_expandAdv (s : ℕ) :
    simInitS e (expandAdv e' E K 𝒜) s = appendS K (simInitS e 𝒜 s) := by
  ext ⟨⟨⟨w, f⟩, q⟩, d⟩
  change (𝒜.init (w, q) * (if f = fresh K then 1 else 0)) *
      (if d = dbSlots e s (∅ : DB (Bits m) B) then 1 else 0) =
    (𝒜.init (w, q) * (if d = dbSlots e s (∅ : DB (Bits m) B) then 1 else 0)) *
      (if f = fresh K then 1 else 0)
  ring

theorem expand_inv_init (s : ℕ) :
    simStepS (expandAdv e' E K 𝒜) s 0 (simInitS e (expandAdv e' E K 𝒜) s) ∈ expandInv K e' E h s 0 := by
  unfold expandInv
  split_ifs with h0
  · rw [simInitS_expandAdv, simStepS_expandAdv_appendS K e' E 𝒜 h0]
    exact ⟨_, h.inv_init s, rfl⟩
  · trivial

theorem expand_inv_step (s : ℕ) {k : ℕ} (hk : k < t + K)
    {v : QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)} (hv : v ∈ expandInv K e' E h s k) :
    simStepS (expandAdv e' E K 𝒜) s (k + 1) (simQuery e _ s v) ∈ expandInv K e' E h s (k + 1) := by
  unfold expandInv at hv ⊢
  by_cases h2 : k + 1 < t
  · rw [if_pos h2]
    rw [if_pos (by omega : k < t)] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨_, h.inv_step s k (by omega) _ hu, ?_⟩
    rw [simQuery_appendS_expandAdv, simStepS_expandAdv_appendS K e' E 𝒜 h2]
  · rw [if_neg h2]
    trivial

theorem expand_inv_dbProj (s k : ℕ) (P : Set (DB (Bits m) B))
    (v : QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) (hv : v ∈ expandInv K e' E h s k) :
    dbProj e _ s P v ∈ expandInv K e' E h s k := by
  unfold expandInv at hv ⊢
  by_cases h1 : k < t
  · rw [if_pos h1] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    rw [dbProj_appendS_expandAdv]
    exact ⟨_, h.inv_dbProj s k P u hu, rfl⟩
  · rw [if_neg h1]
    trivial

theorem expand_pad (s : ℕ) {k : ℕ} (hk : k < t + K)
    {v : QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)} (hv : v ∈ expandInv K e' E h s k) :
    simQuery e (expandAdv e' E K 𝒜).W s (mask (workSet (expandAdv e' E K 𝒜).W s (expandC K e' E h k))ᶜ v) =
      mask (workSet (expandAdv e' E K 𝒜).W s (expandC K e' E h k))ᶜ v := by
  by_cases h1 : k < t
  · have hv' := hv
    unfold expandInv at hv'
    rw [if_pos h1] at hv'
    obtain ⟨u, hu, hvu⟩ := hv'
    have hvb : ∀ b, v b = u ((b.1.1.1, b.1.2), b.2) * (if b.1.1.2 = fresh K then 1 else 0) :=
      fun b => by rw [← hvu]; rfl
    have hb : ∀ b : SimRegister (expandAdv e' E K 𝒜).W I J m s,
        b ∈ (workSet (expandAdv e' E K 𝒜).W s (expandC K e' E h k))ᶜ ↔ b.1.1.1 ∉ h.C k := by
      intro b
      change ¬ b.1.1 ∈ expandC K e' E h k ↔ _
      rw [show expandC K e' E h k = {w | w.1 ∈ h.C k} from if_pos h1]
      rfl
    have e1 : mask (workSet (expandAdv e' E K 𝒜).W s (expandC K e' E h k))ᶜ v =
        (appendS K (mask (workSet 𝒜.W s (h.C k))ᶜ u) :
          QState (SimRegister (expandAdv e' E K 𝒜).W I J m s)) := by
      ext b
      by_cases hc : b.1.1.1 ∈ h.C k
      · rw [mask_apply_of_notMem _ (fun h' => ((hb b).1 h') hc)]
        change 0 = (mask (workSet 𝒜.W s (h.C k))ᶜ u) ((b.1.1.1, b.1.2), b.2) * _
        rw [mask_apply_of_notMem _ (show ((b.1.1.1, b.1.2), b.2) ∉ (workSet 𝒜.W s (h.C k))ᶜ from
          fun h' => h' hc)]
        simp
      · rw [mask_apply_of_mem _ ((hb b).2 hc), hvb]
        change _ = (mask (workSet 𝒜.W s (h.C k))ᶜ u) ((b.1.1.1, b.1.2), b.2) * _
        rw [mask_apply_of_mem _ (show ((b.1.1.1, b.1.2), b.2) ∈ (workSet 𝒜.W s (h.C k))ᶜ from hc)]
    rw [e1, simQuery_appendS_expandAdv, h.pad s k h1 u hu]
  · have h0 : mask (workSet (expandAdv e' E K 𝒜).W s (expandC K e' E h k))ᶜ v = 0 := by
      ext b
      rw [mask_apply_of_notMem]
      · rfl
      · intro hb
        apply hb
        change b.1.1 ∈ expandC K e' E h k
        rw [show expandC K e' E h k = Set.univ from if_neg h1]
        trivial
    rw [h0, map_zero]

/-- **The per-branch count of the expanded adversary** (`QueryCount`, our construction): if every
branch of `𝒜` queries at no more than `b` of its steps, every branch of the expanded adversary
`expandAdv e' E K 𝒜` queries at no more than `b + K`: `𝒜`'s records for its queries, and the
expansion's `K` queries on every branch. -/
noncomputable def QueryCount.expandAdv : QueryCount e (QROM.expandAdv e' E K 𝒜) (b + K) where
  C := expandC K e' E h
  G := expandG K e' E h
  Inv := expandInv K e' E h
  init := expand_init K e' E h
  stepG k hk _ hv := expand_stepG K e' E h hk hv
  stepC i k hik hk _ hv := by
    by_cases hi : i < t
    · rw [show expandC K e' E h i = {w | w.1 ∈ h.C i} from if_pos hi]
      exact expand_stepKeep K e' E h hk (fun hk1 u hu => h.stepC i k hik (by omega) u hu)
        (fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ expandC K e' E h i := h'.1
          rw [show expandC K e' E h i = {w | w.1 ∈ h.C i} from if_pos hi] at h''
          exact ⟨h'', h'.2⟩))
    · rw [show expandC K e' E h i = Set.univ from if_neg hi]
      exact fun r hr => absurd trivial hr
  stepCc i k hik hk _ hv := by
    by_cases hi : i < t
    · rw [show expandC K e' E h i = {w | w.1 ∈ h.C i} from if_pos hi]
      exact expand_stepKeep K e' E h (T := (h.C i)ᶜ) hk
        (fun hk1 u hu => h.stepCc i k hik (by omega) u hu)
        (fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ (expandC K e' E h i)ᶜ := h'.1
          rw [show expandC K e' E h i = {w | w.1 ∈ h.C i} from if_pos hi] at h''
          exact ⟨h'', h'.2⟩))
    · have hv0 : ∀ r, ‹QState (QueryReg _ 1 (Bits m) (BitStr I J))› r = 0 := fun r => hv r (by
        rintro ⟨h1, -⟩
        apply h1
        rw [show expandC K e' E h i = Set.univ from if_neg hi]
        trivial)
      have : ‹QState (QueryReg _ 1 (Bits m) (BitStr I J))› = 0 := by
        ext r
        exact hv0 r
      rw [this, map_zero]
      exact fun _ _ => rfl
  count := expand_count K e' E h
  inv_init := expand_inv_init K e' E h
  inv_step s k hk _ hv := expand_inv_step K e' E h s hk hv
  inv_dbProj s k P v hv := expand_inv_dbProj K e' E h s k P v hv
  pad s k hk _ hv := expand_pad K e' E h s hk hv

end Expand

end GordieHowe.QROM
