-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.Quantum.O2H.Budget

@[expose] public section

/-!
# The measured-database bound with a per-branch query count

CMS19 Lemma 5.9 (`measured_norm_le`, `GordieHowe/Model/QROM/Compressed.lean`) charges every query of a
`t`-query algorithm, and Lemma 5.10 (`query_step_le`, `GordieHowe/Model/QROM/QueryStep.lean`) takes the
instability at the size `t` of the database register. When the branches of an algorithm decide at
run time at which of its query steps they query (the others are padded so that the query does
nothing), the bound should charge each branch only for the steps at which it queries. This file
proves `Pr[D ∈ R] ≤ b² · 6 · I(R, b)` when every branch queries at no more than `b` of the steps
(`Lifting.measured_le_of_queryCount`): CMS19's bound `t² · 6 · I(R, t)` with `t` replaced by `b`.

## The hypothesis (`QueryCount`)

Sets `C i` of the work register record that query `i` is made: the steps after query `i` keep `C i`
and its complement, and every work-register content possible before query `k` (`G k`) lies in at
most `b` of the sets `C i` for `i ≤ k`. Off `C i`, query `i` is the identity in the simulated run:
on a family `Inv` of vectors that contains the simulated run, is kept by the steps and by the
projections of the database register, a simulated query fixes the part outside `C k`
(`QueryCount.pad`). For a padded query this holds because its answer register is in the uniform
superposition, on which the compressed phase oracle acts as the identity.

## The argument (our statement; the hybrid is CMS19's Lemma 5.9, p. 23)

Let `u` be the simulated run with the projection `P̄` onto the databases outside `R` after every
query (`projStage`). Then the final state `v` of the simulated run is `u_t` plus a sum over the
queries `i` of the part `P O P̄ u_i` that query `i` moves into `R`, carried to the end by the run
(`exists_simStage_sub_eq_sum`). That part lies on `C i` (off `C i` the query is the identity), so
Cauchy–Schwarz basis state by basis state (`norm_sum_sq_le_of_count`) gives
`‖P v‖² ≤ b ∑ᵢ ‖P O P̄ (C i) u_i‖²`. On `C i` the database has fewer than `b` entries
(`supported_projStage_size`: a query changes the size by at most one, `dbPot`), so each term is
at most `6 I(R, b) ‖(C i) u_i‖²` (`norm_dbProj_compressedOracle_sq_le`), and the weights
`‖(C i) u_i‖²` sum to at most `b`: the potential `∑_r |u_k(r)|² (b − cnt_k(r))` drops by
`‖(C k) u_k‖²` at query `k` (`potential_succ_le`).
-/

open Finset GordieHowe.Quantum
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} (e : BitStr I J ≃ B)

/-! ### The potential of a database at the query input -/

section Potential

open Classical in
/-- **The potential of a database at an input `x`**: its size, plus one if `x` is not in it. `Dec_x`
joins only databases of equal potential (`dbPot_of_decBlock`), so a query keeps it, and a query
changes the size of the database by at most one. -/
noncomputable def dbPot (x : Bits m) (D : DB (Bits m) B) : ℕ :=
  D.size + if x ∈ D then 0 else 1

theorem size_le_dbPot (x : Bits m) (D : DB (Bits m) B) : D.size ≤ dbPot x D :=
  Nat.le_add_right _ _

theorem dbPot_le_size_add_one (x : Bits m) (D : DB (Bits m) B) : dbPot x D ≤ D.size + 1 := by
  unfold dbPot
  split_ifs <;> omega

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The members of the block of `D₀` for `Dec_x` have potential `|D₀| + 1` at `x`. -/
theorem dbPot_of_decBlock {x : Bits m} {s : Slots I J m t} {D₀ : DB (Bits m) B}
    (h : decBlock e t x s = some D₀) : dbPot x (slotsDB e s) = D₀.size + 1 := by
  obtain ⟨hx, hsz⟩ := decBlock_eq_some e h
  obtain ⟨o, rfl⟩ := exists_blockSlot_of_decBlock e h
  rw [slotsDB_blockSlot e hx hsz]
  cases o with
  | none => simp [dbPot, blockDB, hx]
  | some y => simp [dbPot, blockDB, DB.size_extend_of_notMem hx, DB.mem_extend]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The base database of the block of `s` has at most the entries of `s`'s database. -/
theorem size_le_of_decBlock {x : Bits m} {s : Slots I J m t} {D₀ : DB (Bits m) B}
    (h : decBlock e t x s = some D₀) : D₀.size ≤ (slotsDB e s).size := by
  have h1 := dbPot_of_decBlock e h
  have h2 := dbPot_le_size_add_one x (slotsDB e s)
  omega

variable (W t) in
/-- The basis states of `Sim*` whose database has potential at the query input at most `f` of the
work register. -/
def potSet (f : W → ℕ) : Set (SimRegister W I J m t) :=
  {b | dbPot (qIn b.1) (slotsDB e b.2) ≤ f b.1.1}

variable (W t) in
/-- The basis states of `Sim*` whose database register holds a database state with at most `f`
entries, `f` a function of the work register. -/
def sizeLe (f : W → ℕ) : Set (SimRegister W I J m t) :=
  {b | IsDBState e b.2 ∧ (slotsDB e b.2).size ≤ f b.1.1}

theorem supported_decOp_potSet {f : W → ℕ} {v : QState (SimRegister W I J m t)}
    (hv : Supported (potSet e W t f) v) : Supported (potSet e W t f) (decOp e W t v) := by
  classical
  rw [decOp_eq]
  refine hv.kernelOp fun b' b hb hb' => ?_
  split_ifs with h1
  · have hne : b'.2 ≠ b.2 := fun h2 => hb' (by rwa [show b' = b from Prod.ext h1 h2])
    unfold reflKernel
    rw [if_neg hne, zero_sub, neg_eq_zero]
    split_ifs with h3
    · by_cases hn : decBlock e t (qIn b.1) b.2 = none
      · have h0 : decAmp e t (qIn b.1) b.2 = 0 := by simp [decAmp, hn]
        simp [h0]
      · obtain ⟨D₀, hD⟩ := Option.ne_none_iff_exists'.1 hn
        exfalso
        apply hb'
        change dbPot (qIn b'.1) (slotsDB e b'.2) ≤ f b'.1.1
        rw [h1, dbPot_of_decBlock e (h3.trans hD), ← dbPot_of_decBlock e hD]
        exact hb
    · rfl
  · rfl

/-- `O0` is diagonal, so it keeps every support. -/
theorem supported_phaseOp_of {S : Set (SimRegister W I J m t)} {v : QState (SimRegister W I J m t)}
    (hv : Supported S v) : Supported S (phaseOp e W t v) :=
  hv.kernelOp fun b' b hb hb' => by
    rw [if_neg]
    rintro rfl
    exact hb' hb

/-- The Hadamard transform changes only the answer register, so it keeps every support that does
not depend on it. -/
theorem supported_hadamard_of {S : Set (SimRegister W I J m t)}
    (hS : ∀ b' b : SimRegister W I J m t, b'.1.1 = b.1.1 → qIn b'.1 = qIn b.1 → b'.2 = b.2 →
      (b' ∈ S ↔ b ∈ S))
    {v : QState (SimRegister W I J m t)} (hv : Supported S v) : Supported S (hadamard W t v) :=
  hv.kernelOp fun b' b hb hb' => by
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hb' ((hS b' b h1 h2 h3).2 hb)

/-- **A simulated query keeps the potential**: `Dec` joins only databases of equal potential at
the query input, and `O0` and the Hadamard transform change neither. -/
theorem supported_simQuery_potSet {f : W → ℕ} {v : QState (SimRegister W I J m t)}
    (hv : Supported (potSet e W t f) v) : Supported (potSet e W t f) (simQuery e W t v) := by
  have hH : ∀ b' b : SimRegister W I J m t, b'.1.1 = b.1.1 → qIn b'.1 = qIn b.1 → b'.2 = b.2 →
      (b' ∈ potSet e W t f ↔ b ∈ potSet e W t f) := by
    intro b' b h1 h2 h3
    simp only [potSet, Set.mem_setOf_eq, h1, h2, h3]
  rw [simQuery, compressedOracle]
  simp only [ContinuousLinearMap.comp_apply]
  exact supported_hadamard_of hH (supported_decOp_potSet e (supported_phaseOp_of e
    (supported_decOp_potSet e (supported_hadamard_of hH hv))))

/-- **A simulated query adds at most one entry to the database.** -/
theorem supported_simQuery_sizeLe {f : W → ℕ} {v : QState (SimRegister W I J m t)}
    (hv : Supported (sizeLe e W t f) v) :
    Supported (sizeLe e W t fun w => f w + 1) (simQuery e W t v) := by
  have hdb : Supported (DBSupport e W t) v := hv.mono fun b hb => hb.1
  have hpot : Supported (potSet e W t fun w => f w + 1) v := hv.mono fun b hb =>
    (dbPot_le_size_add_one _ _).trans (Nat.add_le_add_right hb.2 1)
  refine ((supported_simQuery e hdb).inter (supported_simQuery_potSet e hpot)).mono ?_
  rintro b ⟨h1, h2⟩
  exact ⟨h1, (size_le_dbPot _ _).trans h2⟩

/-! ### Simulated queries and the work register -/

/-- The basis states of `Sim*` whose work register lies in `S`. -/
abbrev workSet (W : Type) (t : ℕ) (S : Set W) : Set (SimRegister W I J m t) :=
  {b | b.1.1 ∈ S}

/-- **A simulated query commutes with the projections of the work register**: the Hadamard
transform, `Dec` and `O0` act on the query and database registers only. -/
theorem simQuery_mask_workSet (S : Set W) (v : QState (SimRegister W I J m t)) :
    simQuery e W t (mask (workSet W t S) v) = mask (workSet W t S) (simQuery e W t v) := by
  classical
  have hH : ∀ w : QState (SimRegister W I J m t),
      hadamard W t (mask (workSet W t S) w) = mask (workSet W t S) (hadamard W t w) :=
    kernelOp_mask fun b' b hk => by
      have h : b'.1.1 = b.1.1 := by
        by_contra hne
        exact hk (if_neg fun h => hne h.1)
      simp only [Set.mem_setOf_eq, h]
  have hD : ∀ w : QState (SimRegister W I J m t),
      decOp e W t (mask (workSet W t S) w) = mask (workSet W t S) (decOp e W t w) := by
    intro w
    rw [decOp_eq]
    exact kernelOp_mask (fun b' b hk => by
      have h : b'.1 = b.1 := by
        by_contra hne
        exact hk (if_neg hne)
      simp only [Set.mem_setOf_eq, h]) w
  have hP : ∀ w : QState (SimRegister W I J m t),
      phaseOp e W t (mask (workSet W t S) w) = mask (workSet W t S) (phaseOp e W t w) :=
    kernelOp_mask fun b' b hk => by
      have h : b' = b := by
        by_contra hne
        exact hk (if_neg hne)
      rw [h]
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply, hH, hD, hP]

/-- A simulated query keeps the supports of the work register. -/
theorem supported_simQuery_workSet {S : Set W} {v : QState (SimRegister W I J m t)}
    (hv : Supported (workSet W t S) v) : Supported (workSet W t S) (simQuery e W t v) := by
  rw [← hv.mask_eq_self, simQuery_mask_workSet]
  exact supported_mask _ _

omit [DecidableEq W] in
/-- Projections of the work register and of the database register commute. -/
theorem mask_workSet_dbProj (S : Set W) (P : Set (DB (Bits m) B))
    (v : QState (SimRegister W I J m t)) :
    mask (workSet W t S) (dbProj e W t P v) = dbProj e W t P (mask (workSet W t S) v) := by
  ext b
  simp only [dbProj_eq, mask_apply]
  by_cases h1 : b ∈ workSet W t S <;> by_cases h2 : b ∈ dbSet e W t P <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]

omit [DecidableEq W] in
/-- A projection of the database register keeps every support. -/
theorem Supported.dbProj {S : Set (SimRegister W I J m t)} {v : QState (SimRegister W I J m t)}
    (hv : Supported S v) (P : Set (DB (Bits m) B)) : Supported S (QROM.dbProj e W t P v) := by
  intro b hb
  simp only [dbProj_eq, mask_apply]
  exact Set.indicator_apply_eq_zero.2 fun _ => hv b hb

omit [DecidableEq W] in
/-- The projections onto a database property and onto its complement are orthogonal. -/
theorem dbProj_dbProj_compl (P : Set (DB (Bits m) B)) (v : QState (SimRegister W I J m t)) :
    dbProj e W t P (dbProj e W t Pᶜ v) = 0 := by
  classical
  ext b
  simp only [dbProj_eq, mask_apply, Set.indicator_apply]
  split_ifs with h1 h2
  · exact absurd rfl (ne_of_inP e h1 h2)
  · rfl
  · rfl

omit [DecidableEq W] in
/-- **A step controlled on the database register keeps a support of the work register** that its
unitary keeps. -/
theorem supported_controlled_workSet {S S' : Set W}
    {U : QState (QueryReg W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg W 1 (Bits m) (BitStr I J))}
    (hU : ∀ v, Supported {r | r.1 ∈ S} v → Supported {r | r.1 ∈ S'} (U v))
    {v : QState (SimRegister W I J m t)} (hv : Supported (workSet W t S) v) :
    Supported (workSet W t S') (controlled (fun _ => U) v) := by
  rintro ⟨r, s⟩ hr
  rw [controlled_apply]
  refine hU _ (fun r' hr' => hv (r', s) hr') r hr

omit [DecidableEq W] in
/-- A projection keeps every support. -/
theorem supported_mask_of {S T : Set (SimRegister W I J m t)} {v : QState (SimRegister W I J m t)}
    (h : Supported S v) : Supported S (mask T v) := fun b hb => by
  rw [mask_apply]
  exact Set.indicator_apply_eq_zero.2 fun _ => h b hb

omit [DecidableEq W] in
/-- A step controlled on the database register commutes, on vectors whose work register lies in
`G`, with a projection of the work register whose set and complement (within `G`) its unitary
keeps. -/
theorem controlled_mask_workSet {S G : Set W}
    {U : QState (QueryReg W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg W 1 (Bits m) (BitStr I J))}
    (hU : ∀ v, Supported {r | r.1 ∈ S ∩ G} v → Supported {r | r.1 ∈ S} (U v))
    (hUc : ∀ v, Supported {r | r.1 ∈ Sᶜ ∩ G} v → Supported {r | r.1 ∈ Sᶜ} (U v))
    {v : QState (SimRegister W I J m t)} (hv : Supported (workSet W t G) v) :
    mask (workSet W t S) (controlled (fun _ => U) v) =
      controlled (fun _ => U) (mask (workSet W t S) v) := by
  have h1 : Supported (workSet W t S) (controlled (fun _ => U) (mask (workSet W t S) v)) :=
    supported_controlled_workSet hU ((supported_mask _ _).inter (supported_mask_of hv))
  have h2 : Supported (workSet W t Sᶜ) (controlled (fun _ => U) (mask (workSet W t S)ᶜ v)) :=
    supported_controlled_workSet hUc (((supported_mask _ _).mono fun b hb => hb).inter
      (supported_mask_of hv))
  conv_lhs => rw [← mask_add_mask_compl (workSet W t S) v, map_add, map_add]
  rw [h1.mask_eq_self, h2.mask_eq_zero (T := workSet W t S) fun b hb hb' => hb' hb, add_zero]

end Potential

/-! ### A padded query is the identity in the simulated run -/

section Padded

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- **`I ⊗ H^n` is an involution.** -/
theorem hadamard_hadamard (v : QState (SimRegister W I J m t)) :
    hadamard W t (hadamard W t v) = v := by
  set M : (W × Bits m × Slots I J m t) → BitStr I J → BitStr I J → ℂ :=
    fun _ u' u => invSqrtCard I J * signOf (u'.dot u)
  have hK : ∀ b' b : SimRegister W I J m t,
      (if b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2 then
        invSqrtCard I J * signOf ((qAns b'.1).dot (qAns b.1)) else 0) =
      if (answerSplit W t b').1 = (answerSplit W t b).1 then
        M (answerSplit W t b).1 (answerSplit W t b').2 (answerSplit W t b).2 else 0 := by
    intro b' b
    simp [answerSplit, M]
  refine kernelOp_kernelOp_of_inv (fun b'' b => ?_) v
  simp_rw [hK]
  rw [Fintype.sum_equiv (answerSplit W t) _
    (fun c => (if (answerSplit W t b'').1 = c.1 then M c.1 (answerSplit W t b'').2 c.2 else 0) *
      (if c.1 = (answerSplit W t b).1 then
        M (answerSplit W t b).1 c.2 (answerSplit W t b).2 else 0)) fun _ => rfl,
    blockKernel_inv M (fun _ i k => hadamardMatrix_inv i k)]
  simp only [(answerSplit W t).injective.eq_iff]

/-- **A vector that does not depend on the answer register**: its entries at the basis states that
differ only in the answer register are equal. A padded query's answer register is in the uniform
superposition, so the part of the run it acts on is of this form. -/
def AnsConst (v : QState (SimRegister W I J m t)) : Prop :=
  ∀ (b : SimRegister W I J m t) (u : BitStr I J), v (withAns b.1 u, b.2) = v b

omit [DecidableEq W] in
theorem AnsConst.add {v w : QState (SimRegister W I J m t)} (hv : AnsConst v) (hw : AnsConst w) :
    AnsConst (v + w) := fun b u => by
  rw [PiLp.add_apply, PiLp.add_apply, hv, hw]

/-- **In the phase basis a vector that does not depend on the answer register has answer `0`**:
`∑_y (−1)^{u·y} = 0` for `u ≠ 0`. -/
theorem supported_hadamard_of_ansConst {v : QState (SimRegister W I J m t)} (hv : AnsConst v) :
    Supported {b : SimRegister W I J m t | qAns b.1 = 0} (hadamard W t v) := by
  rintro ⟨r, s⟩ hr
  rw [hadamard_eq_ansH, ansH_apply]
  have hc : ∀ u, v (withAns r u, s) = v (withAns r 0, s) := fun u => by
    rw [← hv (withAns r 0, s) u, withAns_withAns]
  simp_rw [hc, ← Finset.sum_mul, hk]
  rw [← Finset.mul_sum]
  have h0 : ∑ u : BitStr I J, signOf ((qAns r).dot u) = 0 := by
    simp_rw [BitStr.dot_comm (qAns r)]
    rw [sum_signOf_dot, if_neg (show ¬ qAns r = 0 from hr)]
  rw [h0, mul_zero, zero_mul]

/-- **The compressed phase oracle is the identity on answer `0`**: `O0` multiplies by
`(−1)^{0·D(x)} = 1`, and `Dec` is an involution that keeps the answer register. -/
theorem compressedOracle_eq_self {w : QState (SimRegister W I J m t)}
    (hw : Supported {b : SimRegister W I J m t | qAns b.1 = 0} w) :
    compressedOracle e W t w = w := by
  classical
  have hdec : ∀ x : QState (SimRegister W I J m t),
      Supported {b : SimRegister W I J m t | qAns b.1 = 0} x →
      Supported {b : SimRegister W I J m t | qAns b.1 = 0} (decOp e W t x) := by
    intro x hx
    rw [decOp_eq]
    refine hx.kernelOp fun b' b hb hb' => ?_
    rw [if_neg]
    rintro h
    exact hb' (show qAns b'.1 = 0 by rw [h]; exact hb)
  have hphase : ∀ x : QState (SimRegister W I J m t),
      Supported {b : SimRegister W I J m t | qAns b.1 = 0} x → phaseOp e W t x = x := by
    intro x hx
    ext b
    rw [phaseOp, kernelOp_apply, Finset.sum_eq_single b (fun c _ hc => by rw [if_neg (Ne.symm hc),
      zero_mul]) (by simp), if_pos rfl]
    by_cases hb : qAns b.1 = 0
    · have h1 : dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) = 1 := by
        unfold dbPhase
        split
        · rfl
        · rw [hb, BitStr.dot_comm, BitStr.dot_zero]
          rfl
      rw [h1, one_mul]
    · rw [hx b hb, mul_zero]
  rw [compressedOracle]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hphase _ (hdec w hw), decOp_decOp]

/-- **A simulated query fixes a vector that does not depend on the answer register**: a padded
query is the identity in `Sim*`. -/
theorem simQuery_eq_self_of_ansConst {v : QState (SimRegister W I J m t)} (hv : AnsConst v) :
    simQuery e W t v = v := by
  rw [simQuery]
  simp only [ContinuousLinearMap.comp_apply]
  rw [compressedOracle_eq_self e (supported_hadamard_of_ansConst hv), hadamard_hadamard]

end Padded

/-! ### Counting weighted by a function of the work register -/

section Weighted

variable {ι : Type*} [Fintype ι]

/-- A vector's squared amplitudes weighted by a function of the basis state are its squared
masses on the level sets of the function, weighted. -/
theorem sum_norm_sq_mul_eq {κ : Type*} [DecidableEq κ] (f : ι → κ) (F : κ → ℝ) (v : QState ι) :
    ∑ r, ‖v r‖ ^ 2 * F (f r) = ∑ c ∈ univ.image f, F c * ‖mask {r | f r = c} v‖ ^ 2 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image f) (g := f)
    (fun r _ => Finset.mem_image_of_mem _ (Finset.mem_univ r))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [norm_mask_sq, Finset.mul_sum]
  refine Finset.sum_congr (by ext; simp) fun r hr => ?_
  simp only [Finset.mem_filter] at hr
  rw [hr.2, mul_comm]

/-- Vectors with the same masses on the level sets of `f` have the same weighted squared
amplitudes. -/
theorem sum_norm_sq_mul_congr {κ : Type*} [DecidableEq κ] (f : ι → κ) (F : κ → ℝ)
    {v v' : QState ι} (h : ∀ c, ‖mask {r | f r = c} v‖ = ‖mask {r | f r = c} v'‖) :
    ∑ r, ‖v r‖ ^ 2 * F (f r) = ∑ r, ‖v' r‖ ^ 2 * F (f r) := by
  rw [sum_norm_sq_mul_eq, sum_norm_sq_mul_eq]
  refine Finset.sum_congr rfl fun c _ => by rw [h c]

end Weighted

/-! ### The per-branch count -/

section Count

variable {O : Type} {t : ℕ}

/-- The number of queries below `k` recorded in the work-register content `w`: the sets `C i`,
`i < k`, that contain it. -/
noncomputable def countBelow {W : Type} (C : ℕ → Set W) (k : ℕ) (w : W) : ℕ :=
  open Classical in ((range k).filter fun i => w ∈ C i).card

theorem countBelow_zero {W : Type} (C : ℕ → Set W) (w : W) : countBelow C 0 w = 0 := by
  simp [countBelow]

open Classical in
theorem countBelow_mono {W : Type} (C : ℕ → Set W) {k k' : ℕ} (h : k ≤ k') (w : W) :
    countBelow C k w ≤ countBelow C k' w := by
  unfold countBelow
  exact card_le_card (filter_subset_filter _ (range_subset_range.2 h))

open Classical in
theorem countBelow_succ {W : Type} (C : ℕ → Set W) (k : ℕ) (w : W) :
    countBelow C (k + 1) w = countBelow C k w + if w ∈ C k then 1 else 0 := by
  unfold countBelow
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hk => by simp at hk)]
  · rfl

/-- **A step of `A` on the simulated run with `s` database slots**: `A`'s unitary `step k`,
extended by the identity on the database register (`simStep` is the case `s = t`). -/
noncomputable def simStepS (A : QueryAlg (Bits m) (BitStr I J) t O) (s k : ℕ) :
    QState (SimRegister A.W I J m s) ≃ₗᵢ[ℂ] QState (SimRegister A.W I J m s) :=
  controlled fun _ => (A.toOracleAlg ∅).stepAt () k

/-- **The initial state of the simulated run with `s` database slots**: `A`'s initial state and
the empty database (`simInit` is the case `s = t`). -/
noncomputable def simInitS (A : QueryAlg (Bits m) (BitStr I J) t O) (s : ℕ) :
    QState (SimRegister A.W I J m s) :=
  WithLp.toLp 2 fun b => A.init b.1 * (if b.2 = dbSlots e s (∅ : DB (Bits m) B) then 1 else 0)

/-- **A per-branch count of the queries of `A`**, at most `b` on every branch. The sets `C i` of the
work register record that query `i` is made: the steps after query `i` keep `C i` and its complement
on `G k` (`stepC`, `stepCc`). The sets `G k` hold the work-register contents possible before query
`k` (`init`, `stepG`), and each lies in at most `b` of the sets `C i` with `i ≤ k` (`count`). For
every number `s` of database slots, the family `Inv s k` of vectors of the simulated run before
query `k` contains the simulated run (`inv_init`, `inv_step`) and is kept by the projections of the
database register (`inv_dbProj`); on it a simulated query fixes the part outside `C k` (`pad`). For
a padded query this holds because its answer register is in the uniform superposition. The families
are stated for every slot count so that the count passes to an algorithm that runs `A` and then
makes further queries (`expandAdv`), whose database register has more slots. -/
structure QueryCount (A : QueryAlg (Bits m) (BitStr I J) t O) (b : ℕ) where
  /-- The work-register contents that make query `i`. -/
  C : ℕ → Set A.W
  /-- The work-register contents possible before query `k`. -/
  G : ℕ → Set A.W
  /-- Vectors of the simulated run with `s` database slots before query `k`. -/
  Inv : (s : ℕ) → ℕ → Set (QState (SimRegister A.W I J m s))
  init : Supported {r | r.1 ∈ G 0} ((A.toOracleAlg ∅).stepAt () 0 A.init)
  stepG : ∀ k < t, ∀ v, Supported {r | r.1 ∈ G k} v → Supported {r | r.1 ∈ G (k + 1)} ((A.toOracleAlg ∅).stepAt () (k + 1) v)
  stepC : ∀ i k, i ≤ k → k < t → ∀ v, Supported {r | r.1 ∈ C i ∩ G k} v →
    Supported {r | r.1 ∈ C i} ((A.toOracleAlg ∅).stepAt () (k + 1) v)
  stepCc : ∀ i k, i ≤ k → k < t → ∀ v, Supported {r | r.1 ∈ (C i)ᶜ ∩ G k} v →
    Supported {r | r.1 ∈ (C i)ᶜ} ((A.toOracleAlg ∅).stepAt () (k + 1) v)
  count : ∀ k ≤ t, ∀ w ∈ G k, countBelow C (min (k + 1) t) w ≤ b
  inv_init : ∀ s, simStepS A s 0 (simInitS e A s) ∈ Inv s 0
  inv_step : ∀ s, ∀ k < t, ∀ v ∈ Inv s k, simStepS A s (k + 1) (simQuery e A.W s v) ∈ Inv s (k + 1)
  inv_dbProj : ∀ s k (P : Set (DB (Bits m) B)) v, v ∈ Inv s k → dbProj e A.W s P v ∈ Inv s k
  pad : ∀ s, ∀ k < t, ∀ v ∈ Inv s k,
    simQuery e A.W s (mask (workSet A.W s (C k))ᶜ v) = mask (workSet A.W s (C k))ᶜ v

variable (A : QueryAlg (Bits m) (BitStr I J) t O) (R : Set (DB (Bits m) B))

/-- **The simulated run projected off `R` after every query** (proof-internal): the simulated run
of `A` (`simStage`) with the projection `P̄` onto the databases outside `R` applied after each
query. -/
noncomputable def projStage : ℕ → QState (SimRegister A.W I J m t)
  | 0 => simStage e A 0
  | k + 1 => simStep A (k + 1) (dbProj e A.W t Rᶜ (simQuery e A.W t (projStage k)))

theorem projStage_zero : projStage e A R 0 = simStage e A 0 :=
  rfl

theorem projStage_succ (k : ℕ) : projStage e A R (k + 1) =
    simStep A (k + 1) (dbProj e A.W t Rᶜ (simQuery e A.W t (projStage e A R k))) :=
  rfl

theorem simStage_succ (k : ℕ) :
    simStage e A (k + 1) = simStep A (k + 1) (simQuery e A.W t (simStage e A k)) :=
  rfl

/-- The sum of two vectors supported in `S` is supported in `S`. -/
theorem _root_.GordieHowe.Quantum.Supported.add {ι : Type*} [Fintype ι] {S : Set ι} {v w : QState ι}
    (hv : Supported S v) (hw : Supported S w) : Supported S (v + w) := fun r hr => by
  rw [PiLp.add_apply, hv r hr, hw r hr, add_zero]

/-- A linear map applied to the zero vector. -/
theorem _root_.GordieHowe.Quantum.Supported.of_forall_eq_zero {ι : Type*} [Fintype ι] {S : Set ι}
    {v : QState ι} (hv : ∀ r, v r = 0) : Supported S v := fun r _ => hv r

/-- The projected run is supported on database states. -/
theorem supported_projStage_db (k : ℕ) : Supported (DBSupport e A.W t) (projStage e A R k) := by
  induction k with
  | zero => exact supported_simStage e A 0
  | succ k ih =>
    exact Supported.controlled (Q := {s | IsDBState e s}) _
      (Supported.dbProj e (supported_simQuery e ih) _)

/-- The simulated run starts with the empty database, outside `R`. -/
theorem dbProj_simStage_zero (hR : (∅ : DB (Bits m) B) ∉ R) :
    dbProj e A.W t R (simStage e A 0) = 0 := by
  have h0 : dbProj e A.W t R (simInit e A) = 0 := by
    ext b
    rw [dbProj_eq, mask_apply]
    by_cases hb : b ∈ dbSet e A.W t R
    · rw [Set.indicator_of_mem hb]
      obtain ⟨D, hDP, hDt, hbD⟩ := hb
      simp only [simInit]
      rw [if_neg, mul_zero]
      · rfl
      intro h'
      rw [hbD] at h'
      have := (dbSlots_inj e (by simp) hDt).1 h'
      exact hR (this ▸ hDP)
    · rw [Set.indicator_of_notMem hb]
      rfl
  change dbProj e A.W t R (simStep A 0 (simInit e A)) = 0
  rw [← simStep_dbProj, h0, map_zero]

/-- **The projected run lies outside `R`**: `P̄ u_k = u_k`. -/
theorem dbProj_compl_projStage (hR : (∅ : DB (Bits m) B) ∉ R) (k : ℕ) :
    dbProj e A.W t Rᶜ (projStage e A R k) = projStage e A R k := by
  cases k with
  | zero =>
    have h := dbProj_add_dbProj_compl e (P := R) (supported_simStage e A 0)
    rw [dbProj_simStage_zero e A R hR, zero_add] at h
    exact h
  | succ k =>
    rw [projStage_succ, ← simStep_dbProj, dbProj_eq, mask_mask]

theorem dbProj_projStage (hR : (∅ : DB (Bits m) B) ∉ R) (k : ℕ) :
    dbProj e A.W t R (projStage e A R k) = 0 := by
  rw [← dbProj_compl_projStage e A R hR k, dbProj_dbProj_compl]

namespace QueryCount

variable {e A R} {b : ℕ} (h : QueryCount e A b)

open Classical in
/-- **The steps after query `k` keep the number of queries recorded below `j ≤ k + 1`**, so the
classes `{countBelow C j ∈ N}` of the work register. -/
theorem supported_step_countBelow {k : ℕ} (hk : k < t) :
    ∀ j ≤ k + 1, ∀ (N : Set ℕ) (v : QState (QueryReg A.W 1 (Bits m) (BitStr I J))),
      Supported {r | countBelow h.C j r.1 ∈ N} v → Supported {r | r.1 ∈ h.G k} v →
        Supported {r | countBelow h.C j r.1 ∈ N} ((A.toOracleAlg ∅).stepAt () (k + 1) v) := by
  intro j
  induction j with
  | zero =>
    intro _ N v hv _
    by_cases h0 : 0 ∈ N
    · intro r hr
      exact absurd (by rw [Set.mem_setOf_eq, countBelow_zero]; exact h0) hr
    · have hv0 : v = 0 := by
        ext r
        exact hv r (by rw [Set.mem_setOf_eq, countBelow_zero]; exact h0)
      rw [hv0, map_zero]
      exact Supported.of_forall_eq_zero fun _ => rfl
  | succ j ih =>
    intro hj N v hv hG
    have hjk : j ≤ k := by omega
    set N' : Set ℕ := {n | n + 1 ∈ N}
    have h1 : Supported ({r | countBelow h.C j r.1 ∈ N'} ∩ {r | r.1 ∈ h.C j})
        (mask {r : QueryReg A.W 1 (Bits m) (BitStr I J) | r.1 ∈ h.C j} v) := by
      intro r hr
      by_cases hc : r.1 ∈ h.C j
      · rw [mask_apply_of_mem _ (show r ∈ {r : QueryReg A.W 1 (Bits m) (BitStr I J) | r.1 ∈ h.C j}
          from hc)]
        refine hv r fun hN => hr ⟨?_, hc⟩
        simp only [Set.mem_setOf_eq, countBelow_succ, if_pos hc] at hN
        exact hN
      · exact mask_apply_of_notMem _ (show r ∉ {r : QueryReg A.W 1 (Bits m) (BitStr I J) |
          r.1 ∈ h.C j} from hc)
    have h2 : Supported ({r | countBelow h.C j r.1 ∈ N} ∩ {r | r.1 ∈ h.C j}ᶜ)
        (mask {r : QueryReg A.W 1 (Bits m) (BitStr I J) | r.1 ∈ h.C j}ᶜ v) := by
      intro r hr
      by_cases hc : r.1 ∈ h.C j
      · exact mask_apply_of_notMem _ (show r ∉ {r : QueryReg A.W 1 (Bits m) (BitStr I J) |
          r.1 ∈ h.C j}ᶜ from fun h' => h' hc)
      · rw [mask_apply_of_mem _ (show r ∈ {r : QueryReg A.W 1 (Bits m) (BitStr I J) |
          r.1 ∈ h.C j}ᶜ from hc)]
        refine hv r fun hN => hr ⟨?_, hc⟩
        simp only [Set.mem_setOf_eq, countBelow_succ, if_neg hc, add_zero] at hN
        exact hN
    have hG1 : Supported {r | r.1 ∈ h.G k}
        (mask {r : QueryReg A.W 1 (Bits m) (BitStr I J) | r.1 ∈ h.C j} v) := fun r hr => by
      rw [mask_apply]
      exact Set.indicator_apply_eq_zero.2 fun _ => hG r hr
    have hG2 : Supported {r | r.1 ∈ h.G k}
        (mask {r : QueryReg A.W 1 (Bits m) (BitStr I J) | r.1 ∈ h.C j}ᶜ v) := fun r hr => by
      rw [mask_apply]
      exact Set.indicator_apply_eq_zero.2 fun _ => hG r hr
    have g1 := (ih (by omega) N' _ (h1.mono Set.inter_subset_left) hG1).inter
      (h.stepC j k hjk hk _ ((h1.mono Set.inter_subset_right).inter hG1))
    have g2 := (ih (by omega) N _ (h2.mono Set.inter_subset_left) hG2).inter
      (h.stepCc j k hjk hk _ ((h2.mono Set.inter_subset_right).inter hG2))
    rw [← mask_add_mask_compl {r : QueryReg A.W 1 (Bits m) (BitStr I J) | r.1 ∈ h.C j} v, map_add]
    refine (g1.mono ?_).add (g2.mono ?_)
    · rintro r ⟨hN, hc⟩
      simp only [Set.mem_setOf_eq, countBelow_succ, if_pos (show r.1 ∈ h.C j from hc)]
      exact hN
    · rintro r ⟨hN, hc⟩
      simp only [Set.mem_setOf_eq, countBelow_succ,
        if_neg (show r.1 ∉ h.C j from hc), add_zero]
      exact hN

/-- The simulated step after query `k` commutes with the projections onto the classes of the
number of queries recorded below `k + 1`. -/
theorem simStep_mask_countBelow {k : ℕ} (hk : k < t) (c : ℕ) {v : QState (SimRegister A.W I J m t)}
    (hv : Supported (workSet A.W t (h.G k)) v) :
    mask (workSet A.W t {w | countBelow h.C (k + 1) w = c}) (simStep A (k + 1) v) =
      simStep A (k + 1) (mask (workSet A.W t {w | countBelow h.C (k + 1) w = c}) v) :=
  controlled_mask_workSet (S := {w | countBelow h.C (k + 1) w = c}) (G := h.G k)
    (fun x hx => h.supported_step_countBelow hk (k + 1) le_rfl {c} x
      (hx.mono fun _ hr => hr.1) (hx.mono fun _ hr => hr.2))
    (fun x hx => h.supported_step_countBelow hk (k + 1) le_rfl {c}ᶜ x
      (hx.mono fun _ hr => hr.1) (hx.mono fun _ hr => hr.2)) hv

theorem projStage_mem_inv {k : ℕ} (hk : k ≤ t) : projStage e A R k ∈ h.Inv t k := by
  induction k with
  | zero => exact h.inv_init t
  | succ k ih =>
    rw [projStage_succ, simStep_dbProj]
    exact h.inv_dbProj t _ _ _ (h.inv_step t k (by omega) _ (ih (by omega)))

/-- The simulated run before query `k` has its work register in `G k`. -/
theorem supported_simStage_G {k : ℕ} (hk : k ≤ t) :
    Supported (workSet A.W t (h.G k)) (simStage e A k) := by
  induction k with
  | zero =>
    rintro ⟨r, s⟩ hr
    change simStep A 0 (simInit e A) (r, s) = 0
    rw [simStep, controlled_apply]
    by_cases hs : s = dbSlots e t (∅ : DB (Bits m) B)
    · have : (WithLp.toLp 2 fun i' => simInit e A (i', s) :
          QState (QueryReg A.W 1 (Bits m) (BitStr I J))) = A.init := by
        ext i'
        simp [simInit, hs]
      rw [this]
      exact h.init r hr
    · have : (WithLp.toLp 2 fun i' => simInit e A (i', s) :
          QState (QueryReg A.W 1 (Bits m) (BitStr I J))) = 0 := by
        ext i'
        simp [simInit, hs]
      rw [this, map_zero]
      rfl
  | succ k ih =>
    rw [simStage_succ]
    exact supported_controlled_workSet (h.stepG k (by omega))
      (supported_simQuery_workSet e (ih (by omega)))

theorem supported_projStage_G {k : ℕ} (hk : k ≤ t) :
    Supported (workSet A.W t (h.G k)) (projStage e A R k) := by
  induction k with
  | zero => exact h.supported_simStage_G (Nat.zero_le _)
  | succ k ih =>
    rw [projStage_succ]
    exact supported_controlled_workSet (h.stepG k (by omega))
      (Supported.dbProj e (supported_simQuery_workSet e (ih (by omega))) _)

/-- On the work-register contents possible before query `k < t` that make query `k`, fewer than
`b` queries are recorded below `k`. -/
theorem countBelow_lt {k : ℕ} (hk : k < t) {w : A.W} (hG : w ∈ h.G k) (hC : w ∈ h.C k) :
    countBelow h.C k w < b := by
  have h1 := h.count k hk.le w hG
  rw [min_eq_left (by omega), countBelow_succ, if_pos hC] at h1
  omega

/-- **The database of the projected run before query `k` has at most `countBelow C k` entries**:
a query outside `C` is the identity, and a query adds at most one entry
(`supported_simQuery_sizeLe`). -/
theorem supported_projStage_size {k : ℕ} (hk : k ≤ t) :
    Supported (sizeLe e A.W t (countBelow h.C k)) (projStage e A R k) := by
  induction k with
  | zero =>
    have hsupp : Supported {p : SimRegister A.W I J m t | p.2 ∈ ({dbSlots e t ∅} : Set _)}
        (simStage e A 0) := by
      refine Supported.controlled (Q := {dbSlots e t (∅ : DB (Bits m) B)}) _ ?_
      intro p hp
      simp only [simInit, mul_ite, mul_one, mul_zero]
      rw [if_neg (by simpa using hp)]
    refine hsupp.mono fun p hp => ?_
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hp
    refine ⟨hp ▸ isDBState_dbSlots e (by simp), ?_⟩
    rw [hp, slotsDB_dbSlots e (by simp), countBelow_zero]
    rfl
  | succ k ih =>
    have hk' : k < t := by omega
    set u := projStage e A R k
    have hu := ih (by omega)
    have hpad := h.pad t k hk' u (h.projStage_mem_inv (by omega))
    have hsplit : simQuery e A.W t u = simQuery e A.W t (mask (workSet A.W t (h.C k)) u) +
        mask ((workSet A.W t (h.C k))ᶜ) u := by
      rw [← hpad, ← map_add]
      congr 1
      exact (mask_add_mask_compl _ u).symm
    have ha : Supported (sizeLe e A.W t (countBelow h.C (k + 1)))
        (simQuery e A.W t (mask (workSet A.W t (h.C k)) u)) := by
      have hm : Supported (sizeLe e A.W t (countBelow h.C k) ∩ workSet A.W t (h.C k))
          (mask (workSet A.W t (h.C k)) u) :=
        ?_
      · have g := (supported_simQuery_sizeLe e (hm.mono Set.inter_subset_left)).inter
          (supported_simQuery_workSet e (hm.mono Set.inter_subset_right))
        refine g.mono ?_
        rintro p ⟨⟨hdb, hsz⟩, hc⟩
        refine ⟨hdb, ?_⟩
        rw [countBelow_succ, if_pos (show p.1.1 ∈ h.C k from hc)]
        exact hsz
      · intro p hp
        by_cases hc : p ∈ workSet A.W t (h.C k)
        · rw [mask_apply_of_mem _ hc]
          exact hu p fun h' => hp ⟨h', hc⟩
        · exact mask_apply_of_notMem _ hc
    have hc : Supported (sizeLe e A.W t (countBelow h.C (k + 1)))
        (mask ((workSet A.W t (h.C k))ᶜ) u) := by
      intro p hp
      by_cases hc : p ∈ (workSet A.W t (h.C k))ᶜ
      · rw [mask_apply_of_mem _ hc]
        refine hu p fun h' => hp ⟨h'.1, ?_⟩
        rw [countBelow_succ, if_neg (show p.1.1 ∉ h.C k from hc), add_zero]
        exact h'.2
      · exact mask_apply_of_notMem _ hc
    rw [projStage_succ, simStep_dbProj]
    refine Supported.dbProj e ?_ _
    rw [hsplit]
    -- the step keeps the classes of the count and the database register
    have hstep : ∀ x : QState (SimRegister A.W I J m t),
        Supported (sizeLe e A.W t (countBelow h.C (k + 1))) x →
        Supported (workSet A.W t (h.G k)) x →
        Supported (sizeLe e A.W t (countBelow h.C (k + 1))) (simStep A (k + 1) x) := by
      intro x hx hxG
      rintro ⟨r, s⟩ hrs
      rw [simStep, controlled_apply]
      by_cases hdb : IsDBState e s
      · refine h.supported_step_countBelow hk' (k + 1) le_rfl {n | (slotsDB e s).size ≤ n} _
          (fun r' hr' => hx (r', s) fun h' => hr' h'.2) (fun r' hr' => hxG (r', s) hr') r
          fun h' => hrs ⟨hdb, h'⟩
      · have : (WithLp.toLp 2 fun i' => x (i', s) :
            QState (QueryReg A.W 1 (Bits m) (BitStr I J))) = 0 := by
          ext i'
          exact hx (i', s) fun h' => hdb h'.1
        rw [this, map_zero]
        rfl
    have huG := h.supported_projStage_G (R := R) (k := k) (by omega)
    exact hstep _ (ha.add hc) ((supported_simQuery_workSet e (supported_mask_of huG)).add
      (supported_mask_of huG))

open Classical in
/-- **The potential of the projected run**: `∑_r |u_k(r)|² (b − countBelow C k r)`. -/
noncomputable def potential (R : Set (DB (Bits m) B)) (k : ℕ) : ℝ :=
  ∑ p, ‖projStage e A R k p‖ ^ 2 * ((b : ℝ) - countBelow h.C k p.1.1)

/-- A simulated query preserves the masses on the classes of a function of the work register. -/
theorem norm_mask_simQuery {κ : Type} (f : A.W → κ) (c : κ) (v : QState (SimRegister A.W I J m t)) :
    ‖mask {p : SimRegister A.W I J m t | f p.1.1 = c} (simQuery e A.W t v)‖ =
      ‖mask {p : SimRegister A.W I J m t | f p.1.1 = c} v‖ := by
  have := simQuery_mask_workSet e (W := A.W) (t := t) {w | f w = c} v
  change ‖mask (workSet A.W t {w | f w = c}) (simQuery e A.W t v)‖ = _
  rw [← this, norm_simQuery]
  rfl

open Classical in
/-- **The potential drops by the weight of the querying branches** at each query:
`Ψ (k + 1) + ‖(C k) u_k‖² ≤ Ψ k`. -/
theorem potential_succ_le {k : ℕ} (hk : k < t) :
    h.potential R (k + 1) + ‖mask (workSet A.W t (h.C k)) (projStage e A R k)‖ ^ 2 ≤
      h.potential R k := by
  set u := projStage e A R k with hu_def
  set F : ℕ → ℝ := fun c => (b : ℝ) - c
  set y := simQuery e A.W t u
  set a := simQuery e A.W t (mask (workSet A.W t (h.C k)) u)
  set c := mask ((workSet A.W t (h.C k))ᶜ) u
  have hpad := h.pad t k hk u (h.projStage_mem_inv (by omega))
  have hy : y = a + c := by
    simp only [y, a, c]
    rw [← hpad, ← map_add, mask_add_mask_compl]
  have haC : Supported (workSet A.W t (h.C k)) a :=
    supported_simQuery_workSet e (supported_mask _ _)
  have hcC : Supported ((workSet A.W t (h.C k))ᶜ) c := supported_mask _ _
  have hyG : Supported (workSet A.W t (h.G k)) y :=
    supported_simQuery_workSet e (h.supported_projStage_G (by omega))
  -- 1. the step keeps the classes of the count
  have h1 : h.potential R (k + 1) =
      ∑ p, ‖dbProj e A.W t Rᶜ y p‖ ^ 2 * F (countBelow h.C (k + 1) p.1.1) := by
    rw [potential, projStage_succ]
    refine sum_norm_sq_mul_congr (fun p : SimRegister A.W I J m t => countBelow h.C (k + 1) p.1.1)
      F fun c' => ?_
    have := h.simStep_mask_countBelow hk c' (Supported.dbProj e hyG Rᶜ)
    change ‖mask (workSet A.W t {w | countBelow h.C (k + 1) w = c'}) _‖ =
      ‖mask (workSet A.W t {w | countBelow h.C (k + 1) w = c'}) _‖
    rw [this, LinearIsometryEquiv.norm_map]
  -- 2. the projection only removes weight, on terms of nonnegative weight
  have h2 : ∑ p, ‖dbProj e A.W t Rᶜ y p‖ ^ 2 * F (countBelow h.C (k + 1) p.1.1) ≤
      ∑ p, ‖y p‖ ^ 2 * F (countBelow h.C (k + 1) p.1.1) := by
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : p.1.1 ∈ h.G k
    · have hF : 0 ≤ F (countBelow h.C (k + 1) p.1.1) := by
        have := h.count k hk.le _ hp
        rw [min_eq_left (by omega)] at this
        simp only [F, sub_nonneg]
        exact_mod_cast this
      refine mul_le_mul_of_nonneg_right ?_ hF
      rw [dbProj_eq, mask_apply]
      by_cases hm : p ∈ dbSet e A.W t Rᶜ
      · rw [Set.indicator_of_mem hm]
      · rw [Set.indicator_of_notMem hm, norm_zero]
        exact sq_nonneg _ |>.trans_eq' (by ring)
    · have h0 : y p = 0 := hyG p hp
      have h0' : dbProj e A.W t Rᶜ y p = 0 := by
        rw [dbProj_eq, mask_apply]
        exact Set.indicator_apply_eq_zero.2 fun _ => h0
      rw [h0, h0']
  -- 3. split the query into the querying and the padded branches
  have h3 : ∑ p, ‖y p‖ ^ 2 * F (countBelow h.C (k + 1) p.1.1) =
      ∑ p, ‖a p‖ ^ 2 * (F (countBelow h.C k p.1.1) - 1) +
        ∑ p, ‖c p‖ ^ 2 * F (countBelow h.C k p.1.1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hy, PiLp.add_apply, countBelow_succ]
    by_cases hp : p.1.1 ∈ h.C k
    · rw [hcC p (fun h' => h' hp), add_zero, if_pos hp]
      simp only [F, norm_zero]
      push_cast
      ring
    · rw [haC p hp, zero_add, if_neg hp, add_zero]
      simp only [norm_zero]
      ring
  -- 4. the query keeps the weighted mass of the querying branches
  have h4 : ∑ p, ‖a p‖ ^ 2 * (F (countBelow h.C k p.1.1) - 1) =
      ∑ p, ‖mask (workSet A.W t (h.C k)) u p‖ ^ 2 * (F (countBelow h.C k p.1.1) - 1) :=
    sum_norm_sq_mul_congr (fun p : SimRegister A.W I J m t => countBelow h.C k p.1.1)
      (fun c' => F c' - 1) fun c' => norm_mask_simQuery (countBelow h.C k) c' _
  -- 5. recombine
  have h5 : ∑ p, ‖mask (workSet A.W t (h.C k)) u p‖ ^ 2 * (F (countBelow h.C k p.1.1) - 1) +
      ∑ p, ‖c p‖ ^ 2 * F (countBelow h.C k p.1.1) =
      h.potential R k - ‖mask (workSet A.W t (h.C k)) u‖ ^ 2 := by
    rw [potential, ← hu_def, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p ∈ workSet A.W t (h.C k)
    · rw [mask_apply_of_mem _ hp, hcC p (fun h' => h' hp)]
      simp only [F, norm_zero]
      ring
    · rw [mask_apply_of_notMem _ hp, show c p = u p from mask_apply_of_mem _ hp]
      simp only [F, norm_zero]
      ring
  rw [h1]
  linarith [h2, h3, h4, h5]

theorem potential_zero : h.potential R 0 = b := by
  rw [potential, projStage_zero]
  simp only [countBelow_zero, Nat.cast_zero, sub_zero]
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq, norm_simStage, one_pow, one_mul]

theorem potential_nonneg : 0 ≤ h.potential R t := by
  refine Finset.sum_nonneg fun p _ => ?_
  by_cases hp : p.1.1 ∈ h.G t
  · have h1 := h.count t le_rfl _ hp
    rw [min_eq_right (Nat.le_succ t)] at h1
    exact mul_nonneg (sq_nonneg _) (by rw [sub_nonneg]; exact_mod_cast h1)
  · rw [h.supported_projStage_G le_rfl p hp, norm_zero]
    simp

/-- **The querying branches weigh at most `b` in all**: `∑_{k < t} ‖(C k) u_k‖² ≤ b`, by the
potential (`potential_succ_le`). -/
theorem sum_norm_mask_sq_le :
    ∑ k ∈ range t, ‖mask (workSet A.W t (h.C k)) (projStage e A R k)‖ ^ 2 ≤ b := by
  have key : ∀ n ≤ t, (∑ k ∈ range n, ‖mask (workSet A.W t (h.C k)) (projStage e A R k)‖ ^ 2) +
      h.potential R n ≤ b := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Finset.sum_range_zero, zero_add, h.potential_zero]
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ]
      have h1 := h.potential_succ_le (R := R) (k := n) (by omega)
      have h2 := ih (by omega)
      linarith
  linarith [key t le_rfl, h.potential_nonneg (R := R)]

/-- **The query moves weight into `R` only from the querying branches**: off `C k` the query is
the identity, and the projected run lies outside `R`. -/
theorem dbProj_simQuery_projStage (hR : (∅ : DB (Bits m) B) ∉ R) {k : ℕ} (hk : k < t) :
    dbProj e A.W t R (simQuery e A.W t (projStage e A R k)) =
      dbProj e A.W t R (simQuery e A.W t (mask (workSet A.W t (h.C k)) (projStage e A R k))) := by
  set u := projStage e A R k
  have hpad := h.pad t k hk u (h.projStage_mem_inv hk.le)
  have hsplit : simQuery e A.W t u = simQuery e A.W t (mask (workSet A.W t (h.C k)) u) +
      mask (workSet A.W t (h.C k))ᶜ u := by
    rw [← hpad, ← map_add, mask_add_mask_compl]
  have h0 : dbProj e A.W t R (mask (workSet A.W t (h.C k))ᶜ u) = 0 := by
    rw [show (workSet A.W t (h.C k))ᶜ = workSet A.W t (h.C k)ᶜ from rfl, ← mask_workSet_dbProj e,
      dbProj_projStage e A R hR k, map_zero]
  rw [hsplit, map_add, h0, add_zero]

/-- **One query from the querying branches of the projected run**: their database has fewer than
`b` entries (`supported_projStage_size`, `countBelow_lt`), so CMS19's Lemma 5.10 applies at the
instability `I(R, b)` (`norm_dbProj_compressedOracle_sq_le`). -/
theorem norm_dbProj_simQuery_sq_le [Fintype B] [Nonempty B] (hR : (∅ : DB (Bits m) B) ∉ R)
    {k : ℕ} (hk : k < t) :
    ‖dbProj e A.W t R (simQuery e A.W t (projStage e A R k))‖ ^ 2 ≤
      6 * (instab R b).toReal * ‖mask (workSet A.W t (h.C k)) (projStage e A R k)‖ ^ 2 := by
  set u := projStage e A R k
  set x := mask (workSet A.W t (h.C k)) u
  have hx : dbProj e A.W t Rᶜ x = x := by
    simp only [x]
    rw [← mask_workSet_dbProj e, dbProj_compl_projStage e A R hR k]
  set S : Set (SimRegister A.W I J m t) :=
    sizeLe e A.W t (countBelow h.C k) ∩ workSet A.W t (h.C k) ∩ workSet A.W t (h.G k)
  have hxS : Supported S x := by
    intro p hp
    by_cases hc : p ∈ workSet A.W t (h.C k)
    · rw [show x p = u p from mask_apply_of_mem _ hc]
      by_cases hs : p ∈ sizeLe e A.W t (countBelow h.C k)
      · exact h.supported_projStage_G hk.le p fun hG => hp ⟨⟨hs, hc⟩, hG⟩
      · exact h.supported_projStage_size hk.le p hs
    · exact mask_apply_of_notMem _ hc
  have hHS : Supported S (hadamard A.W t x) := by
    refine supported_hadamard_of (fun b' b h1 _ h3 => ?_) hxS
    simp only [S, sizeLe, workSet, Set.mem_inter_iff, Set.mem_setOf_eq, h1, h3]
  have hv : ∀ (p : SimRegister A.W I J m t) (D₀ : DB (Bits m) B),
      decBlock e t (qIn p.1) p.2 = some D₀ → b ≤ D₀.size → hadamard A.W t x p = 0 := by
    intro p D₀ hD hbD
    by_contra hne
    have hpS : p ∈ S := by
      by_contra hn
      exact hne (hHS p hn)
    obtain ⟨⟨⟨-, hsz⟩, hC⟩, hG⟩ := hpS
    have h1 := size_le_of_decBlock e hD
    have h2 := h.countBelow_lt hk hG hC
    omega
  have heq : dbProj e A.W t R (simQuery e A.W t x) = hadamard A.W t
      (dbProj e A.W t R (compressedOracle e A.W t (dbProj e A.W t Rᶜ (hadamard A.W t x)))) := by
    simp only [simQuery, ContinuousLinearMap.comp_apply]
    rw [hadamard_dbProj, ← hadamard_dbProj e Rᶜ, hx]
  rw [h.dbProj_simQuery_projStage hR hk, heq, norm_hadamard]
  calc _ ≤ 6 * (instab R b).toReal * ‖hadamard A.W t x‖ ^ 2 :=
        norm_dbProj_compressedOracle_sq_le e A.W R b _ hv
    _ = _ := by rw [norm_hadamard]

/-- **The hybrid as a sum** (CMS19 Lemma 5.9, p. 23, with the projected run): the simulated run
before query `k` is the projected run plus, for each earlier query `i`, the part `P O P̄ u_i` that
query `i` moved into `R`, carried to step `k` by the simulated run; that part lies on `C i`. -/
theorem exists_simStage_sub_eq_sum (hR : (∅ : DB (Bits m) B) ∉ R) :
    ∀ k ≤ t, ∃ z : ℕ → QState (SimRegister A.W I J m t),
      (∀ i < k, Supported (workSet A.W t (h.C i) ∩ workSet A.W t (h.G k)) (z i)) ∧
      (∀ i < k, ‖z i‖ = ‖dbProj e A.W t R (simQuery e A.W t (projStage e A R i))‖) ∧
      simStage e A k - projStage e A R k = ∑ i ∈ range k, z i := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [projStage_zero, sub_self, Finset.sum_range_zero]⟩
  | succ k ih =>
    intro hk
    have hk' : k < t := by omega
    obtain ⟨z, hzS, hzN, hz⟩ := ih (by omega)
    set u := projStage e A R k
    set w := dbProj e A.W t R (simQuery e A.W t u)
    have hstepC : ∀ i ≤ k, ∀ y : QState (SimRegister A.W I J m t),
        Supported (workSet A.W t (h.C i) ∩ workSet A.W t (h.G k)) y →
        Supported (workSet A.W t (h.C i) ∩ workSet A.W t (h.G (k + 1))) (simStep A (k + 1) y) :=
      fun i hi y hy => (supported_controlled_workSet (S := h.C i ∩ h.G k) (h.stepC i k hi hk')
        (hy.mono fun _ hb => hb)).inter
        (supported_controlled_workSet (h.stepG k hk') (hy.mono Set.inter_subset_right))
    have hsQ : ∀ i, ∀ y : QState (SimRegister A.W I J m t),
        Supported (workSet A.W t (h.C i) ∩ workSet A.W t (h.G k)) y →
        Supported (workSet A.W t (h.C i) ∩ workSet A.W t (h.G k)) (simQuery e A.W t y) :=
      fun i y hy => (supported_simQuery_workSet e (hy.mono Set.inter_subset_left)).inter
        (supported_simQuery_workSet e (hy.mono Set.inter_subset_right))
    have hwS : Supported (workSet A.W t (h.C k) ∩ workSet A.W t (h.G k)) w := by
      simp only [w]
      rw [h.dbProj_simQuery_projStage hR hk']
      refine Supported.dbProj e (hsQ k _ ?_) _
      exact (supported_mask _ _).inter (by
        intro p hp
        rw [mask_apply]
        exact Set.indicator_apply_eq_zero.2 fun _ => h.supported_projStage_G hk'.le p hp)
    refine ⟨fun i => if i < k then simStep A (k + 1) (simQuery e A.W t (z i))
      else simStep A (k + 1) w, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · dsimp only
      by_cases hik : i < k
      · rw [if_pos hik]
        exact hstepC i hik.le _ (hsQ i _ (hzS i hik))
      · rw [if_neg hik]
        have : i = k := by omega
        subst this
        exact hstepC i le_rfl _ hwS
    · dsimp only
      by_cases hik : i < k
      · rw [if_pos hik, LinearIsometryEquiv.norm_map, norm_simQuery, hzN i hik]
      · rw [if_neg hik, LinearIsometryEquiv.norm_map]
        have : i = k := by omega
        subst this
        rfl
    · rw [Finset.sum_range_succ, if_neg (lt_irrefl k)]
      have hsum : ∑ i ∈ range k, (if i < k then simStep A (k + 1) (simQuery e A.W t (z i))
          else simStep A (k + 1) w) = simStep A (k + 1) (simQuery e A.W t (∑ i ∈ range k, z i)) := by
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi)
      have hdec : simQuery e A.W t u - dbProj e A.W t Rᶜ (simQuery e A.W t u) = w := by
        have := dbProj_add_dbProj_compl e (P := R)
          (supported_simQuery e (supported_projStage_db e A R k))
        rw [sub_eq_iff_eq_add]
        exact this.symm
      rw [hsum, simStage_succ, projStage_succ, ← map_sub, ← map_add]
      congr 1
      rw [← hz, map_sub, ← hdec]
      abel

include h in
/-- **The weight of `R` in the simulated run**: `‖P |Sim*(A)⟩‖² ≤ b² · 6 I(R, b)`. -/
theorem norm_dbProj_simState_sq_le [Fintype B] [Nonempty B] (hR : (∅ : DB (Bits m) B) ∉ R) :
    ‖dbProj e A.W t R (simState e A)‖ ^ 2 ≤ (b : ℝ) ^ 2 * 6 * (instab R b).toReal := by
  classical
  obtain ⟨z, hzS, hzN, hz⟩ := h.exists_simStage_sub_eq_sum hR t le_rfl
  set κ := (instab R b).toReal
  have hκ : 0 ≤ κ := ENNReal.toReal_nonneg
  have hP : dbProj e A.W t R (simState e A) = dbProj e A.W t R (∑ i ∈ range t, z i) := by
    rw [simState, ← hz, map_sub, dbProj_projStage e A R hR t, sub_zero]
  have hcount : ∀ r : SimRegister A.W I J m t, r ∈ workSet A.W t (h.G t) →
      ((range t).filter fun i => r ∈ workSet A.W t (h.C i)).card ≤ b := by
    intro r hr
    have h1 := h.count t le_rfl _ hr
    rw [min_eq_right (Nat.le_succ t)] at h1
    refine le_of_eq_of_le ?_ h1
    unfold countBelow
    congr 1
  have hCS := norm_sum_sq_le_of_count (range t) b z (fun i => workSet A.W t (h.C i))
    (workSet A.W t (h.G t)) (fun i hi => hzS i (Finset.mem_range.1 hi)) hcount
  have hterm : ∀ i ∈ range t, ‖z i‖ ^ 2 ≤
      6 * κ * ‖mask (workSet A.W t (h.C i)) (projStage e A R i)‖ ^ 2 := fun i hi => by
    rw [hzN i (Finset.mem_range.1 hi)]
    exact h.norm_dbProj_simQuery_sq_le hR (Finset.mem_range.1 hi)
  have hsum := h.sum_norm_mask_sq_le (R := R)
  calc ‖dbProj e A.W t R (simState e A)‖ ^ 2 ≤ ‖∑ i ∈ range t, z i‖ ^ 2 := by
        rw [hP]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_mask_le _ _) 2
    _ ≤ b * ∑ i ∈ range t, ‖z i‖ ^ 2 := hCS
    _ ≤ b * ∑ i ∈ range t, 6 * κ * ‖mask (workSet A.W t (h.C i)) (projStage e A R i)‖ ^ 2 := by
        gcongr with i hi
        exact hterm i hi
    _ = b * (6 * κ) * ∑ i ∈ range t, ‖mask (workSet A.W t (h.C i)) (projStage e A R i)‖ ^ 2 := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ b * (6 * κ) * b := by gcongr
    _ = (b : ℝ) ^ 2 * 6 * κ := by ring

end QueryCount

/-- **The measured-database bound with a per-branch query count** (our statement; CMS19 Lemmas
5.9 and 5.10, p. 22, with each branch charged for its own queries): if every branch of `𝒜` queries
at no more than `b` of its `t` query steps (`QueryCount`), then for a database property `R` with
`∅ ∉ R`, `Pr[D ∈ R] ≤ b² · 6 · I(R, b)`. With `b = t` and every step counted this is CMS19's
`t² · 6 · I(R, t)` (`Lifting.measured_le`). -/
theorem Lifting.measured_le_of_queryCount [Fintype B] [Nonempty B] {C : Type} {k b : ℕ}
    (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (h : QueryCount e 𝒜 b) (R : Set (DB (Bits m) B))
    (hR : (∅ : DB (Bits m) B) ∉ R) :
    dbProb e 𝒜 R ≤ (b : ℝ≥0∞) ^ 2 * 6 * instab R b := by
  have hne : instab R b ≠ ⊤ := (instab_le_one.trans_lt ENNReal.one_lt_top).ne
  rw [measured_prob, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖dbProj e 𝒜.W t R (simState e 𝒜)‖ ^ 2) ≤
        ENNReal.ofReal ((b : ℝ) ^ 2 * 6 * (instab R b).toReal) :=
        ENNReal.ofReal_le_ofReal (h.norm_dbProj_simState_sq_le hR)
    _ = (b : ℝ≥0∞) ^ 2 * 6 * instab R b := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_toReal hne]

/-- The measured-database bound with a per-branch query count for a union (as CMS19's proof of
Lemma 5.13, p. 25): for `∅ ∉ P` and `∅ ∉ Q`,
`Pr[D ∈ P ∪ Q] ≤ b² · 6 · (I(P | Q̄, b) + I(Q, b))`. -/
theorem Lifting.dbProb_union_le_of_queryCount [Fintype B] [Nonempty B] {C : Type} {k b : ℕ}
    (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (h : QueryCount e 𝒜 b) {P Q : Set (DB (Bits m) B)}
    (hP : (∅ : DB (Bits m) B) ∉ P) (hQ : (∅ : DB (Bits m) B) ∉ Q) :
    dbProb e 𝒜 (P ∪ Q) ≤ (b : ℝ≥0∞) ^ 2 * 6 * (condInstab P Qᶜ b + instab Q b) :=
  (Lifting.measured_le_of_queryCount e 𝒜 h _ fun h0 => h0.elim hP hQ).trans
    (by gcongr; exact instab_union_le)

end Count

end GordieHowe.QROM
