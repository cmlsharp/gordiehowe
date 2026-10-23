-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Budget
public import GordieHowe.Model.Quantum.Core.Born

@[expose] public section

/-!
# A post phase of query batches as query slots

A final unitary of the form `post H = U (b - 1) ∘ queryPerm H ∘ ⋯ ∘ U 0 ∘ queryPerm H` (`postN`)
makes `b` batches of `n` parallel queries to the final oracle `H`. The post phase of an adversary
with run-time kinds has this form (`KindAlg.postOpN`). This file moves those batches into
`b` further query slots of a distinguisher with no final unitary (`Distinguisher.withPostSlots`):
the workspace gains a flag, cleared during the slots of `D` and set by step `m`, and a branch with
the flag set queries. The two games accept with the same probability against every environment
(`acceptProbAt_withPostSlots`), and a budget of `q` query slots of `D` gives a budget of `q + b`
query slots of the new distinguisher (`Budget.withPostSlots`). So every query of the post phase is
counted by the budget, and the O2H bounds for games without a final unitary apply.

- `embV e v`: a vector on `ι` placed along an injective map `e : ι → κ` (zero off its range).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Vectors placed along an injective map -/

section Embed

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open Classical in
/-- **The vector `v` placed along `e`**: the amplitude of `e i` is that of `i`, and the amplitude
of a basis state off the range of `e` is zero. -/
noncomputable def embV (e : ι → κ) (v : QState ι) : QState κ :=
  WithLp.toLp 2 (Function.extend e (fun i => v i) 0)

variable {e : ι → κ}

theorem embV_apply_self (he : Function.Injective e) (v : QState ι) (i : ι) :
    embV e v (e i) = v i := by
  classical
  simp [embV, he.extend_apply]

theorem embV_apply_of_notMem (v : QState ι) {j : κ} (hj : j ∉ Set.range e) : embV e v j = 0 := by
  classical
  simp only [embV, WithLp.ofLp_toLp]
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hj ⟨i, hi⟩]
  rfl

/-- **A permutation that commutes with `e` acts on the placed vector as on the vector.** -/
theorem permOp_embV (he : Function.Injective e) {π : Equiv.Perm ι} {π' : Equiv.Perm κ}
    (h : ∀ i, π' (e i) = e (π i)) (v : QState ι) :
    permOp π' (embV e v) = embV e (permOp π v) := by
  ext j
  rw [permOp_apply]
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    have hs : π'.symm (e i) = e (π.symm i) := by
      rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
    rw [hs, embV_apply_self he, embV_apply_self he, permOp_apply]
  · have hs : π'.symm j ∉ Set.range e := fun ⟨i, hi⟩ => hj ⟨π i, by
      rw [← h, hi, Equiv.apply_symm_apply]⟩
    rw [embV_apply_of_notMem _ hs, embV_apply_of_notMem _ hj]

/-- The probability of a set in the placed vector is that of its preimage. -/
theorem prob_embV (he : Function.Injective e) (S : Set κ) (v : QState ι) :
    prob S (embV e v) = prob (e ⁻¹' S) v := by
  classical
  rw [prob, prob, norm_mask_sq, norm_mask_sq, sum_filter, sum_filter]
  rw [← sum_subset (subset_univ (univ.image e)) fun j _ hj => by
    rw [embV_apply_of_notMem _ fun ⟨i, hi⟩ => hj (mem_image.2 ⟨i, mem_univ _, hi⟩)]
    simp]
  rw [sum_image fun a _ b _ h => he h]
  refine sum_congr rfl fun i _ => ?_
  simp [embV_apply_self he]

theorem embV_zero : embV e (0 : QState ι) = 0 := by
  classical
  ext j
  simp only [embV, WithLp.ofLp_toLp]
  unfold Function.extend
  split_ifs <;> rfl

/-- A placed vector is supported in every set containing the images of a support. -/
theorem Supported.embV (he : Function.Injective e) {S : Set ι} {T : Set κ} {v : QState ι} (hv : Supported S v)
    (hST : ∀ i ∈ S, e i ∈ T) : Supported T (Quantum.embV e v) := by
  intro j hj
  by_cases hr : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hr
    rw [embV_apply_self he v i]
    exact hv i fun h => hj (hST i h)
  · exact embV_apply_of_notMem v hr

/-- Placing along an injective map keeps the norm. -/
theorem norm_embV (he : Function.Injective e) (v : QState ι) : ‖embV e v‖ = ‖v‖ := by
  have h := prob_embV he Set.univ v
  rw [prob_univ, Set.preimage_univ, prob_univ] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end Embed

/-! ### A flag on the workspace -/

section Flag

variable {W X Y Req A : Type*} {n : ℕ}

/-- The distinguisher's registers with a flag on the workspace, as the registers and the flag. -/
def flagSplitD : DReg (W × Bool) n X Y Req A ≃ DReg W n X Y Req A × Bool where
  toFun d := (((d.1.1.1, d.1.2.1, d.1.2.2), d.2), d.1.1.2)
  invFun p := (((p.1.1.1, p.2), p.1.1.2.1, p.1.1.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The flag flipped. -/
def flagFlip : Equiv.Perm (DReg (W × Bool) n X Y Req A) :=
  Function.Involutive.toPerm (fun d => (((d.1.1.1, !d.1.1.2), d.1.2), d.2)) fun d => by simp

/-- The basis state `d` with the flag `f`. -/
def withFlag (f : Bool) (d : DReg W n X Y Req A) : DReg (W × Bool) n X Y Req A :=
  flagSplitD.symm (d, f)

theorem withFlag_injective (f : Bool) :
    Function.Injective (withFlag (W := W) (n := n) (X := X) (Y := Y) (Req := Req) (A := A) f) :=
  fun _ _ h => congrArg Prod.fst (flagSplitD.symm.injective h)

theorem withFlag_mem_range_iff {f g : Bool} {d : DReg W n X Y Req A} :
    withFlag g d ∈ Set.range (withFlag f) ↔ g = f := by
  constructor
  · rintro ⟨d', h⟩
    exact (congrArg Prod.snd (flagSplitD.symm.injective h)).symm
  · rintro rfl
    exact ⟨d, rfl⟩

theorem flagSplitD_symm_eq_withFlag (p : DReg W n X Y Req A × Bool) :
    flagSplitD.symm p = withFlag p.2 p.1 :=
  rfl

/-- Every basis state is a basis state with a flag. -/
theorem exists_withFlag (d : DReg (W × Bool) n X Y Req A) : ∃ g d0, d = withFlag g d0 :=
  ⟨(flagSplitD d).2, (flagSplitD d).1, rfl⟩

theorem flagFlip_withFlag (f : Bool) (d : DReg W n X Y Req A) :
    flagFlip (withFlag f d) = withFlag (!f) d :=
  rfl

variable [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]

/-- **A unitary on the registers, tensored with the identity on the flag.** -/
noncomputable def flagLift (U : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    QState (DReg (W × Bool) n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg (W × Bool) n X Y Req A) :=
  (relabel flagSplitD).trans ((controlled fun _ => U).trans (relabel flagSplitD.symm))

theorem flagLift_apply (U : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (x : QState (DReg (W × Bool) n X Y Req A)) (g : Bool) (d : DReg W n X Y Req A) :
    flagLift U x (withFlag g d) = U (WithLp.toLp 2 fun d' => x (withFlag g d')) d := by
  simp only [flagLift, LinearIsometryEquiv.trans_apply, relabel_apply]
  exact controlled_apply _ _ _ _

/-- The slice of a placed vector at a flag. -/
theorem slice_embV_withFlag (f g : Bool) (v : QState (DReg W n X Y Req A)) :
    (WithLp.toLp 2 fun d' => embV (withFlag f) v (withFlag g d') : QState (DReg W n X Y Req A)) =
      if g = f then v else 0 := by
  ext d'
  split_ifs with h
  · subst h
    rw [WithLp.ofLp_toLp, embV_apply_self (withFlag_injective _)]
  · rw [WithLp.ofLp_toLp, embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff])]
    rfl

theorem flagLift_embV (U : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (f : Bool) (v : QState (DReg W n X Y Req A)) :
    flagLift U (embV (withFlag f) v) = embV (withFlag f) (U v) := by
  ext d
  obtain ⟨g, d0, rfl⟩ := exists_withFlag d
  rw [flagLift_apply, slice_embV_withFlag]
  split_ifs with h
  · subst h
    rw [embV_apply_self (withFlag_injective _)]
  · rw [map_zero, embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff])]
    rfl

theorem flagFlip_embV (f : Bool) (v : QState (DReg W n X Y Req A)) :
    permOp flagFlip (embV (withFlag f) v) = embV (withFlag (!f)) v := by
  ext d
  obtain ⟨g, d0, rfl⟩ := exists_withFlag d
  rw [permOp_apply, show flagFlip.symm (withFlag g d0) = withFlag (!g) d0 from rfl]
  by_cases h : g = !f
  · subst h
    rw [Bool.not_not, embV_apply_self (withFlag_injective _), embV_apply_self (withFlag_injective _)]
  · rw [embV_apply_of_notMem _ (by rw [withFlag_mem_range_iff]; cases f <;> cases g <;> simp_all),
      embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff])]

end Flag


/-! ### Log-controlled unitaries -/

section LogControlled

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ}

/-- The slice of a log-controlled run at the logs `lg` is the unitary of `lg` applied to the slice. -/
theorem slice_logControlled
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) (lg : LogReg Req m) :
    (WithLp.toLp 2 fun d => logControlled U v (splitLogs.symm (d, lg)) :
      QState (DReg W n X Y Req A)) = U lg (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))) := by
  ext d
  rw [WithLp.ofLp_toLp, logControlled_apply]
  simp only [Equiv.apply_symm_apply]

/-- **Composing log-controlled unitaries.** -/
theorem logControlled_trans
    (U V : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) :
    logControlled (fun lg => (V lg).trans (U lg)) v = logControlled U (logControlled V v) := by
  ext r
  rw [logControlled_apply, logControlled_apply, slice_logControlled]
  rfl

/-- The log-controlled identity is the identity. -/
theorem logControlled_refl (v : QState (GameReg W n X Y Req A m)) :
    logControlled (fun _ => LinearIsometryEquiv.refl ℂ (QState (DReg W n X Y Req A))) v = v := by
  ext r
  rw [logControlled_apply]
  rfl

variable [AddGroup Y]

/-- **The oracle of the logs, as a log-controlled unitary**, is the basis permutation that applies
the oracle `H lg` of the logs to the query registers. -/
theorem logControlled_queryPerm (H : LogReg Req m → X → Y) (v : QState (GameReg W n X Y Req A m)) :
    logControlled (fun lg => permOp (queryPerm (H lg))) v =
      permOp (queryPermOf fun s => H s.2.2.2) v := by
  ext r
  rw [logControlled_apply, permOp_apply, permOp_apply]
  congr 1

end LogControlled


/-! ### Logs extended by blank slots -/

section Ext

variable {W X Y Req A : Type*} {n m : ℕ} (b : ℕ)

/-- The logs of `m` slots extended by `b` blank logs. -/
def extLogs (lg : LogReg Req m) : LogReg Req (m + b) :=
  fun i => if h : (i : ℕ) < m then lg ⟨i, h⟩ else none

theorem extLogs_injective : Function.Injective (extLogs (Req := Req) (m := m) b) := fun lg lg' h => by
  funext i
  have := congrFun h (Fin.castAdd b i)
  simpa [extLogs] using this

theorem extLogs_of_lt (lg : LogReg Req m) {k : ℕ} (hk : k < m) :
    extLogs b lg ⟨k, by omega⟩ = lg ⟨k, hk⟩ := by
  simp [extLogs, hk]

theorem extLogs_of_le (lg : LogReg Req m) {k : ℕ} (hk : m ≤ k) (h : k < m + b) :
    extLogs b lg ⟨k, h⟩ = none := by
  simp [extLogs, not_lt.2 hk]

theorem extLogs_update [DecidableEq Req] (lg : LogReg Req m) {k : ℕ} (hk : k < m) (x : Option Req) :
    Function.update (extLogs b lg) ⟨k, by omega⟩ x = extLogs b (Function.update lg ⟨k, hk⟩ x) := by
  funext i
  by_cases hi : (i : ℕ) = k
  · obtain ⟨i, hi'⟩ := i
    simp only at hi
    subst hi
    simp [extLogs, hk]
  · rw [Function.update_of_ne (fun e => hi (by rw [e]))]
    simp only [extLogs]
    split_ifs with h
    · rw [Function.update_of_ne (fun e => hi (by simpa using congrArg Fin.val e))]
    · rfl

/-- The requests before every slot are those of the logs before the extension. -/
theorem requestsBefore_extLogs (lg : LogReg Req m) :
    ∀ k, requestsBefore (extLogs b lg) k = requestsBefore lg k
  | 0 => rfl
  | k + 1 => by
    rw [requestsBefore, requestsBefore, requestsBefore_extLogs lg k]
    congr 1
    by_cases hk : k < m
    · rw [dif_pos (by omega : k < m + b), dif_pos hk, extLogs_of_lt b lg hk]
    · rw [dif_neg hk]
      split_ifs with h
      · rw [extLogs_of_le b lg (not_lt.1 hk) h]
        rfl
      · rfl

theorem requests_extLogs (lg : LogReg Req m) : requests (extLogs b lg) = requests lg := by
  rw [requests, requestsBefore_extLogs, requests,
    requestsBefore_eq_of_blank (Nat.le_add_right m b) fun k' hk' => absurd k'.2 (by omega)]

/-- The registers other than the query registers, with a flag on the workspace and the extended
logs. -/
def embS (f : Bool) (s : W × Req × Option A × LogReg Req m) :
    (W × Bool) × Req × Option A × LogReg Req (m + b) :=
  ((s.1, f), s.2.1, s.2.2.1, extLogs b s.2.2.2)

/-- **A game basis state with a flag and extended logs.** -/
def embR (f : Bool) (r : GameReg W n X Y Req A m) : GameReg (W × Bool) n X Y Req A (m + b) :=
  (embS b f r.1, r.2)

theorem embR_injective (f : Bool) :
    Function.Injective (embR (W := W) (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m) b f) := by
  rintro ⟨⟨w, rq, rs, lg⟩, qs⟩ ⟨⟨w', rq', rs', lg'⟩, qs'⟩ h
  simp only [embR, embS, Prod.mk.injEq] at h
  obtain ⟨⟨⟨hw, -⟩, hrq, hrs, hlg⟩, hqs⟩ := h
  rw [hw, hrq, hrs, extLogs_injective b hlg, hqs]

theorem splitLogs_symm_withFlag (f : Bool) (d : DReg W n X Y Req A) (lg : LogReg Req m) :
    splitLogs.symm (withFlag f d, extLogs b lg) = embR b f (splitLogs.symm (d, lg)) :=
  rfl

theorem splitLogs_symm_mem_range_embR {f : Bool} {d : DReg (W × Bool) n X Y Req A}
    {lg' : LogReg Req (m + b)}
    (h : splitLogs.symm (d, lg') ∈ Set.range (embR (n := n) (X := X) (Y := Y) (A := A) b f)) :
    lg' ∈ Set.range (extLogs b) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r.1.2.2.2, congrArg (fun x => (splitLogs x).2) hr⟩

end Ext

/-! ### The distinguisher with the post phase as slots -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [AddGroup Y]

/-- **A post phase of `i` query batches**: the oracle `H` applied to the query registers, then
`U 0`; …; the oracle, then `U (i - 1)`. -/
noncomputable def postN (U : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (H : X → Y) : ℕ → (QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
  | 0 => LinearIsometryEquiv.refl ℂ _
  | i + 1 => (postN U H i).trans ((permOp (queryPerm H)).trans (U i))

/-- The steps of `withPostSlots`: the steps of `D` with the flag clear, the flag set after step
`m`, then the unitaries of the post phase. -/
noncomputable def postSlotStep (U : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (k : ℕ) : QState (DReg (W × Bool) n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg (W × Bool) n X Y Req A) :=
  if k < m then flagLift (D.stepAt k)
  else if k = m then (flagLift (D.stepAt m)).trans (permOp flagFlip)
  else flagLift (U (k - m - 1))

/-- **The distinguisher with the post phase as `b` query slots** (module docstring): workspace
`W × Bool`; a branch requests when `D` does and the flag is clear; steps `postSlotStep`; it accepts
when `D` does, whatever the flag.

Running time: that of `D` and its post phase: the steps of `D` and the unitaries `U i` with one more
qubit carried, one flip of it, and the `b` query batches of the post phase as `b` slots. This
running time is argued here, not proved in Lean. -/
noncomputable def withPostSlots (U : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (b : ℕ) : Distinguisher (W × Bool) X Y Req A n (m + b) where
  kind w := D.kind w.1 && !w.2
  init := embV (withFlag false) D.init
  norm_init := by
    rw [norm_embV (withFlag_injective false), D.norm_init]
  step k := D.postSlotStep U k
  accept := {d | (flagSplitD d).1 ∈ D.accept}

section Events

variable [DecidableEq Req] [DecidableEq A] {Ω : Type*} {St : Type _} {Q : ℕ}
  [OracleState St X Y] (E : Env Ω Req A X Y Q St)
  (U : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (b : ℕ)

theorem kind_withPostSlots (f : Bool) (w : W) :
    (D.withPostSlots U b).kind (w, f) = (D.kind w && !f) :=
  rfl

theorem oracle_extLogs (ω : Ω) (lg : LogReg Req m) : E.oracle ω (extLogs b lg) = E.oracle ω lg := by
  simp only [Env.oracle, requests_extLogs]

theorem answer_extLogs (ω : Ω) (lg : LogReg Req m) {k : ℕ} (hk : k < m) :
    E.answer ω (extLogs b lg) ⟨k, by omega⟩ = E.answer ω lg ⟨k, hk⟩ := by
  simp only [Env.answer, extLogs_of_lt b lg hk, requestsBefore_extLogs]

/-- **A slot of `D` on a basis state with the flag clear.** -/
theorem eventPerm_withPostSlots_embR (ω : Ω) {k : ℕ} (hk : k < m) (r : GameReg W n X Y Req A m) :
    (D.withPostSlots U b).eventPerm E ω k (embR b false r) = embR b false (D.eventPerm E ω k r) := by
  obtain ⟨⟨w, rq, rs, lg⟩, qs⟩ := r
  have hk' : k < m + b := by omega
  simp only [eventPerm, dif_pos hk, dif_pos hk', Equiv.trans_apply, Env.requestPerm,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, embR, embS, copyPerm_apply, respondPerm_apply,
    kind_withPostSlots, Bool.not_false, Bool.and_true]
  by_cases hw : D.kind w
  · simp only [hw, if_true, extLogs_of_lt b lg hk, extLogs_update b lg hk, answer_extLogs E b ω _ hk]
    simp [Env.oraclePerm, queryPermOf_apply, kind_withPostSlots, hw, embR, embS]
  · simp only [hw, Bool.false_eq_true, if_false]
    simp [Env.oraclePerm, queryPermOf_apply, kind_withPostSlots, hw, embR, embS, oracle_extLogs]

/-- **A post slot on a basis state with the flag set** applies the oracle of the logs. -/
theorem eventPerm_withPostSlots_embR_post (ω : Ω) {i : ℕ} (hi : i < b) (r : GameReg W n X Y Req A m) :
    (D.withPostSlots U b).eventPerm E ω (m + i) (embR b true r) =
      embR b true (queryPermOf (fun s => E.oracle ω s.2.2.2) r) := by
  obtain ⟨⟨w, rq, rs, lg⟩, qs⟩ := r
  simp only [eventPerm, dif_pos (by omega : m + i < m + b), Equiv.trans_apply, Env.requestPerm,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, embR, embS, copyPerm_apply, respondPerm_apply,
    kind_withPostSlots, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
  simp [Env.oraclePerm, queryPermOf_apply, kind_withPostSlots, embR, embS, oracle_extLogs]

end Events

section Vectors

variable (b : ℕ)

theorem embR_withFlag_ne {f g : Bool} (h : g ≠ f) (d : DReg W n X Y Req A) (lg : LogReg Req m) :
    embR b g (splitLogs.symm (d, lg)) ∉ Set.range (embR (n := n) (X := X) (Y := Y) (A := A) b f) := by
  rintro ⟨r, hr⟩
  exact h (congrArg (fun x => x.1.1.2) hr).symm

/-- The slice of a placed game vector at extended logs. -/
theorem slice_embV_embR (f : Bool) (v : QState (GameReg W n X Y Req A m)) (lg : LogReg Req m) :
    (WithLp.toLp 2 fun d' => embV (embR b f) v (splitLogs.symm (d', extLogs b lg)) :
      QState (DReg (W × Bool) n X Y Req A)) =
      embV (withFlag f) (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))) := by
  ext d'
  obtain ⟨g, d0, rfl⟩ := exists_withFlag d'
  rw [WithLp.ofLp_toLp, splitLogs_symm_withFlag]
  by_cases h : g = f
  · subst h
    rw [embV_apply_self (embR_injective b g), embV_apply_self (withFlag_injective g)]
  · rw [embV_apply_of_notMem _ (embR_withFlag_ne b h d0 lg),
      embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff])]

/-- The slice of a placed game vector at logs that are not extended logs is zero. -/
theorem slice_embV_embR_of_notMem (f : Bool) (v : QState (GameReg W n X Y Req A m))
    {lg' : LogReg Req (m + b)} (hlg : lg' ∉ Set.range (extLogs b)) :
    (WithLp.toLp 2 fun d' => embV (embR b f) v (splitLogs.symm (d', lg')) :
      QState (DReg (W × Bool) n X Y Req A)) = 0 := by
  ext d'
  rw [WithLp.ofLp_toLp, embV_apply_of_notMem _ fun h => hlg (splitLogs_symm_mem_range_embR b h)]
  rfl

/-- Every game basis state with a flag is a state of a distinguisher basis state and logs. -/
theorem exists_splitLogs_symm (r : GameReg (W × Bool) n X Y Req A (m + b)) :
    ∃ d lg, r = splitLogs.symm (d, lg) :=
  ⟨(splitLogs r).1, (splitLogs r).2, rfl⟩

/-- **A unitary with the flag carried, controlled by nothing, on a placed vector.** -/
theorem logControlled_flagLift_embV (V : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (f : Bool) (v : QState (GameReg W n X Y Req A m)) :
    logControlled (fun _ => flagLift V) (embV (embR b f) v) =
      embV (embR b f) (logControlled (fun _ => V) v) := by
  ext r
  obtain ⟨d', lg', rfl⟩ := exists_splitLogs_symm b r
  rw [logControlled_apply]
  simp only [Equiv.apply_symm_apply]
  by_cases hlg : lg' ∈ Set.range (extLogs b)
  · obtain ⟨lg, rfl⟩ := hlg
    rw [slice_embV_embR, flagLift_embV]
    obtain ⟨g, d0, rfl⟩ := exists_withFlag d'
    rw [splitLogs_symm_withFlag]
    by_cases h : g = f
    · subst h
      rw [embV_apply_self (withFlag_injective g), embV_apply_self (embR_injective b g),
        logControlled_apply]
      rfl
    · rw [embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff]),
        embV_apply_of_notMem _ (embR_withFlag_ne b h d0 lg)]
  · rw [slice_embV_embR_of_notMem b f v hlg, map_zero,
      embV_apply_of_notMem _ fun h => hlg (splitLogs_symm_mem_range_embR b h)]
    rfl

/-- **Flipping the flag on a placed vector.** -/
theorem logControlled_flagFlip_embV (f : Bool) (v : QState (GameReg W n X Y Req A m)) :
    logControlled (fun _ => permOp flagFlip) (embV (embR b f) v) = embV (embR b (!f)) v := by
  ext r
  obtain ⟨d', lg', rfl⟩ := exists_splitLogs_symm b r
  rw [logControlled_apply]
  simp only [Equiv.apply_symm_apply]
  by_cases hlg : lg' ∈ Set.range (extLogs b)
  · obtain ⟨lg, rfl⟩ := hlg
    rw [slice_embV_embR, flagFlip_embV]
    obtain ⟨g, d0, rfl⟩ := exists_withFlag d'
    rw [splitLogs_symm_withFlag]
    by_cases h : g = !f
    · subst h
      rw [embV_apply_self (withFlag_injective _), embV_apply_self (embR_injective b _)]
    · rw [embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff]),
        embV_apply_of_notMem _ (embR_withFlag_ne b h d0 lg)]
  · rw [slice_embV_embR_of_notMem b f v hlg, map_zero,
      embV_apply_of_notMem _ fun h => hlg (splitLogs_symm_mem_range_embR b h)]
    rfl

end Vectors

section Stages

variable [DecidableEq Req] [DecidableEq A] {Ω : Type*} {St : Type _} {Q : ℕ}
  [OracleState St X Y] (E : Env Ω Req A X Y Q St)
  (U : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (b : ℕ)

theorem extLogs_eq_none_iff (lg : LogReg Req m) :
    (extLogs b lg = fun _ => none) ↔ lg = fun _ => none := by
  constructor
  · intro h
    funext i
    simpa [extLogs] using congrFun h (Fin.castAdd b i)
  · rintro rfl
    funext i
    simp [extLogs]

theorem gameInit_withPostSlots :
    (D.withPostSlots U b).gameInit = embV (embR b false) D.gameInit := by
  ext r
  obtain ⟨d', lg', rfl⟩ := exists_splitLogs_symm b r
  simp only [gameInit, WithLp.ofLp_toLp, Equiv.apply_symm_apply]
  by_cases hlg : lg' ∈ Set.range (extLogs b)
  · obtain ⟨lg, rfl⟩ := hlg
    obtain ⟨g, d0, rfl⟩ := exists_withFlag d'
    rw [splitLogs_symm_withFlag]
    by_cases h : g = false
    · subst h
      rw [embV_apply_self (embR_injective b false)]
      simp only [gameInit, WithLp.ofLp_toLp, Equiv.apply_symm_apply, extLogs_eq_none_iff]
      split_ifs
      · exact embV_apply_self (withFlag_injective false) _ _
      · rfl
    · rw [embV_apply_of_notMem _ (embR_withFlag_ne b h d0 lg)]
      split_ifs
      · exact embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff])
      · rfl
  · rw [embV_apply_of_notMem _ fun h => hlg (splitLogs_symm_mem_range_embR b h),
      if_neg fun h => hlg ⟨fun _ => none, by rw [h, extLogs_eq_none_iff]⟩]

theorem stepAt_withPostSlots {k : ℕ} (hk : k ≤ m + b) :
    (D.withPostSlots U b).stepAt k = D.postSlotStep U k := by
  simp [stepAt, show k < m + b + 1 by omega, withPostSlots]

/-- A step of `D` before step `m`, with the flag clear. -/
theorem liftedStep_withPostSlots_lt {k : ℕ} (hk : k < m) (v : QState (GameReg W n X Y Req A m)) :
    (D.withPostSlots U b).liftedStep k (embV (embR b false) v) =
      embV (embR b false) (D.liftedStep k v) := by
  rw [liftedStep, stepAt_withPostSlots D U b (by omega), postSlotStep, if_pos hk,
    logControlled_flagLift_embV]
  rfl

/-- Step `m`: the last step of `D`, then the flag set. -/
theorem liftedStep_withPostSlots_m (v : QState (GameReg W n X Y Req A m)) :
    (D.withPostSlots U b).liftedStep m (embV (embR b false) v) =
      embV (embR b true) (D.liftedStep m v) := by
  rw [liftedStep, stepAt_withPostSlots D U b (by omega), postSlotStep, if_neg (lt_irrefl m),
    if_pos rfl, logControlled_trans (fun _ => permOp flagFlip) (fun _ => flagLift (D.stepAt m)),
    logControlled_flagLift_embV, logControlled_flagFlip_embV]
  rfl

/-- A step of the post phase, with the flag set. -/
theorem liftedStep_withPostSlots_post {i : ℕ} (hi : i < b) (v : QState (GameReg W n X Y Req A m)) :
    (D.withPostSlots U b).liftedStep (m + 1 + i) (embV (embR b true) v) =
      embV (embR b true) (logControlled (fun _ => U i) v) := by
  rw [liftedStep, stepAt_withPostSlots D U b (by omega), postSlotStep, if_neg (by omega),
    if_neg (by omega), show m + 1 + i - m - 1 = i by omega, logControlled_flagLift_embV]

/-- The game state before every slot of `D`, with the flag clear. -/
theorem stage_withPostSlots_lt (ω : Ω) : ∀ k < m,
    (D.withPostSlots U b).stage E ω k = embV (embR b false) (D.stage E ω k)
  | 0, hk => by
    rw [stage, stage, hybrid_zero, hybrid_zero, gameInit_withPostSlots,
      liftedStep_withPostSlots_lt D U b hk]
  | k + 1, hk => by
    rw [stage_succ, stage_succ, stage_withPostSlots_lt ω k (by omega),
      permOp_embV (embR_injective b false) (eventPerm_withPostSlots_embR D E U b ω (by omega)),
      liftedStep_withPostSlots_lt D U b hk]

/-- The game state after step `m`, with the flag set. -/
theorem stage_withPostSlots_m (ω : Ω) :
    (D.withPostSlots U b).stage E ω m = embV (embR b true) (D.stage E ω m) := by
  rcases m with _ | k
  · rw [stage, stage, hybrid_zero, hybrid_zero, gameInit_withPostSlots,
      liftedStep_withPostSlots_m]
  · rw [stage_succ, stage_succ, stage_withPostSlots_lt D E U b ω k (by omega),
      permOp_embV (embR_injective b false) (eventPerm_withPostSlots_embR D E U b ω (by omega)),
      liftedStep_withPostSlots_m]

/-- The game state of `D` after step `m` and `i` batches of the post phase. -/
noncomputable def postRun (ω : Ω) : ℕ → QState (GameReg W n X Y Req A m)
  | 0 => D.stage E ω m
  | i + 1 => logControlled (fun _ => U i) (permOp (queryPermOf fun s => E.oracle ω s.2.2.2)
      (postRun ω i))

/-- The game state after `i` post slots. -/
theorem stage_withPostSlots_post (ω : Ω) : ∀ i ≤ b,
    (D.withPostSlots U b).stage E ω (m + i) = embV (embR b true) (D.postRun E U ω i)
  | 0, _ => stage_withPostSlots_m D E U b ω
  | i + 1, hi => by
    rw [← add_assoc, stage_succ, stage_withPostSlots_post ω i (by omega),
      permOp_embV (embR_injective b true) (eventPerm_withPostSlots_embR_post D E U b ω (by omega)),
      show m + i + 1 = m + 1 + i by omega, liftedStep_withPostSlots_post D U b (by omega)]
    rfl

/-- The post phase of `i` batches, as log-controlled unitaries. -/
theorem postRun_eq (ω : Ω) : ∀ i,
    D.postRun E U ω i = logControlled (fun lg => postN U (E.oracle ω lg) i) (D.stage E ω m)
  | 0 => (logControlled_refl _).symm
  | i + 1 => by
    rw [postRun, postRun_eq ω i, ← logControlled_queryPerm, ← logControlled_trans,
      ← logControlled_trans]
    rfl

/-- **The final state of the distinguisher with post slots** is the final state of `D` with the
post phase, placed with the flag set. -/
theorem final_withPostSlots (ω : Ω) :
    (D.withPostSlots U b).final E noPost ω =
      embV (embR b true) (D.final E (fun H => postN U H b) ω) := by
  simp only [final, run, noPost]
  rw [logControlled_refl, stage_withPostSlots_post D E U b ω b le_rfl, postRun_eq]

/-- **The post phase as slots** (module docstring): on every tape and every set of logs, the
distinguisher with the post phase as `b` query slots and no final unitary accepts with the
probability of `D` with the post phase `postN U · b`. -/
theorem acceptProbAt_withPostSlots (ω : Ω) :
    (D.withPostSlots U b).acceptProbAt E noPost ω = D.acceptProbAt E (fun H => postN U H b) ω := by
  rw [acceptProbAt, final_withPostSlots, prob_embV (embR_injective b true), acceptProbAt]
  rfl

theorem acceptProb_withPostSlots [Fintype Ω] :
    (D.withPostSlots U b).acceptProb E noPost = D.acceptProb E (fun H => postN U H b) := by
  simp only [acceptProb, acceptProbAt_withPostSlots]

end Stages

section Budget

variable (U : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (b : ℕ)

/-- The slice of a vector at a flag. -/
def sliceF (f : Bool) (v : QState (DReg (W × Bool) n X Y Req A)) : QState (DReg W n X Y Req A) :=
  WithLp.toLp 2 fun d => v (withFlag f d)

/-- A vector supported on the flag `f` is its slice placed with the flag `f`. -/
theorem eq_embV_sliceF {f : Bool} {v : QState (DReg (W × Bool) n X Y Req A)}
    (hv : Supported {d | d.workspace.2 = f} v) : v = embV (withFlag f) (sliceF f v) := by
  ext d
  obtain ⟨g, d0, rfl⟩ := exists_withFlag d
  by_cases h : g = f
  · subst h
    rw [embV_apply_self (withFlag_injective g)]
    rfl
  · rw [embV_apply_of_notMem _ (by rwa [withFlag_mem_range_iff]), hv _ h]


/-- A vector supported in an empty set is zero. -/
theorem eq_zero_of_supported_empty {ι : Type*} [Fintype ι] {S : Set ι} {v : QState ι}
    (hv : Supported S v) (hS : ∀ r, r ∉ S) : v = 0 := by
  ext r
  exact hv r (hS r)

theorem supported_zero {ι : Type*} [Fintype ι] (S : Set ι) : Supported S (0 : QState ι) :=
  fun _ _ => rfl

/-- The slice at a flag of a vector supported on a set of workspaces with that flag. -/
theorem Supported.sliceF {f : Bool} {S : Set (W × Bool)} {v : QState (DReg (W × Bool) n X Y Req A)}
    (hv : Supported {d | d.workspace ∈ S} v) :
    Supported {d : DReg W n X Y Req A | (d.workspace, f) ∈ S} (Distinguisher.sliceF f v) :=
  fun d hd => hv (withFlag f d) hd

theorem Supported.flag {S : Set (W × Bool)} {f : Bool} {v : QState (DReg (W × Bool) n X Y Req A)}
    (hv : Supported {d | d.workspace ∈ S} v) (hS : ∀ w ∈ S, w.2 = f) :
    Supported {d | d.workspace.2 = f} v :=
  fun d hd => hv d fun h => hd (hS _ h)

/-- **The budget of the distinguisher with post slots**: before slot `k < m`, the workspaces of
the budget of `D` with the flag clear and at most `q` query slots; before post slot `i`, the flag
set and at most `q + i` query slots. -/
def Budget.withPostSlots {q : ℕ} (bud : D.Budget q) : (D.withPostSlots U b).Budget (q + b) where
  inv k c := if k < m then {w | w.2 = false ∧ w.1 ∈ bud.inv k c ∧ c ≤ q}
    else {w | w.2 = true ∧ c ≤ q + (k - m)}
  init hm := by
    change Supported _ (D.postSlotStep U 0 (embV (withFlag false) D.init))
    by_cases hm0 : 0 < m
    · simp only [postSlotStep, hm0, ↓reduceIte]
      rw [flagLift_embV, stepAt, dif_pos (by omega)]
      refine (bud.init hm0).embV (withFlag_injective false) fun d hd => ?_
      exact ⟨rfl, hd, Nat.zero_le _⟩
    · obtain rfl : m = 0 := by omega
      simp only [postSlotStep, lt_irrefl, ↓reduceIte]
      rw [LinearIsometryEquiv.trans_apply, flagLift_embV, flagFlip_embV]
      refine (show Supported Set.univ _ from fun _ h => absurd trivial h).embV
        (withFlag_injective _) fun d _ => ?_
      exact ⟨rfl, by omega⟩
  step k hk c bb v hv := by
    change Supported _ (D.postSlotStep U (k + 1) v)
    by_cases hkm : k < m
    · -- a slot of `D`: the flag is clear
      have hv' : Supported {d | d.workspace ∈ {w : W × Bool | (w.2 = false ∧ w.1 ∈ bud.inv k c ∧
          c ≤ q) ∧ (D.kind w.1 && !w.2) = bb}} v := fun d hd => hv d fun h => hd (by
        have h1 := h.1
        rw [if_pos hkm] at h1
        exact ⟨h1, h.2⟩)
      rw [eq_embV_sliceF (Supported.flag hv' fun w hw => hw.1.1)]
      have hu := Supported.sliceF (f := false) hv'
      by_cases hcq : (if bb then c else c + 1) ≤ q
      · have hu' : Supported {d : DReg W n X Y Req A | d.workspace ∈ bud.inv k c ∧
            D.kind d.workspace = bb} (sliceF false v) := fun d hd => hu d fun h => hd
          ⟨h.1.2.1, by simpa using h.2⟩
        by_cases hk1 : k + 1 < m
        · simp only [postSlotStep, hk1, if_true]
          rw [flagLift_embV, stepAt, dif_pos (by omega)]
          refine (bud.step k hk1 c bb _ hu').embV (withFlag_injective false) fun d hd => ?_
          exact ⟨rfl, hd, hcq⟩
        · obtain rfl : m = k + 1 := by omega
          simp only [postSlotStep, lt_irrefl, ↓reduceIte]
          rw [LinearIsometryEquiv.trans_apply, flagLift_embV, flagFlip_embV]
          refine (show Supported Set.univ _ from fun _ h => absurd trivial h).embV
            (withFlag_injective _) fun d _ => ?_
          exact ⟨rfl, by omega⟩
      · have h0 : sliceF false v = 0 := eq_zero_of_supported_empty hu fun d hd => by
          obtain ⟨⟨-, hw, hc⟩, hb⟩ := hd
          simp only [Bool.not_false, Bool.and_true] at hb
          cases bb
          · exact hcq (by simpa using bud.cap k hkm c _ hw hb)
          · exact hcq (by simpa using hc)
        rw [h0, embV_zero, map_zero]
        exact supported_zero _
    · -- a post slot: the flag is set and the branch queries
      have hv' : Supported {d | d.workspace ∈ {w : W × Bool | (w.2 = true ∧ c ≤ q + (k - m)) ∧
          (D.kind w.1 && !w.2) = bb}} v := fun d hd => hv d fun h => hd (by
        have h1 := h.1
        rw [if_neg hkm] at h1
        exact ⟨h1, h.2⟩)
      rw [eq_embV_sliceF (Supported.flag hv' fun w hw => hw.1.1)]
      simp only [postSlotStep, show ¬ (k + 1 < m) by omega, show ¬ (k + 1 = m) by omega,
        if_false]
      rw [flagLift_embV]
      by_cases hcq : bb = false ∧ c ≤ q + (k - m)
      · obtain ⟨rfl, hc⟩ := hcq
        refine (show Supported Set.univ _ from fun _ h => absurd trivial h).embV
          (withFlag_injective _) fun d _ => ?_
        exact ⟨rfl, by simp only [Bool.false_eq_true, ite_false]; omega⟩
      · have h0 : sliceF true v = 0 := eq_zero_of_supported_empty (Supported.sliceF (f := true) hv')
          fun d hd => by
            obtain ⟨⟨-, hc⟩, hb⟩ := hd
            simp only [Bool.not_true, Bool.and_false] at hb
            exact hcq ⟨hb.symm, hc⟩
        rw [h0, map_zero, embV_zero]
        exact supported_zero _
  cap k hk c w hw hkind := by
    split_ifs at hw with hkm
    · obtain ⟨hf, hw1, -⟩ := hw
      have : D.kind w.1 = false := by
        change (D.kind w.1 && !w.2) = false at hkind
        rwa [hf, Bool.not_false, Bool.and_true] at hkind
      exact (bud.cap k hkm c w.1 hw1 this).trans_le (Nat.le_add_right q b)
    · obtain ⟨-, hc⟩ := hw
      omega

end Budget

end Distinguisher

end GordieHowe.Quantum
