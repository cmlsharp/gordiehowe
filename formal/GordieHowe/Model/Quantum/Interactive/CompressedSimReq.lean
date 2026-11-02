-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Compressed
public import GordieHowe.Model.Quantum.Core.Dilation
public import GordieHowe.Model.Quantum.Interactive.PureGameRun
public import GordieHowe.Model.Quantum.Interactive.PureTest
public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.Quantum.Interactive.TPRun

@[expose] public section

/-!
# Query algorithms with classical request points

A query algorithm (`Quantum.QueryAlg`) whose steps also read a classical request from the work
register and write the reply of a challenger into it (a *request point* before each step): the
reply is a function `a k r` of the step number `k` and the request `r`, the same at every branch,
and writing it leaves the request unchanged. Each request is copied into a log register: this
coherent copy is how a classical request is measured (deferred measurement, Nielsen–Chuang
section 4.4), so that the branches with different requests do not interfere.

The file gives the pieces of the compressed-oracle simulation `Sim*` (CMS19 section 3.6) of such an
algorithm that the simulating distinguisher (`GordieHowe/Model/Quantum/Interactive/CoSimQuery.lean`)
runs in its workspace.

- `ReqQueryAlg`, `ReqQueryAlg.req_write_symm`: the data. `ReqQueryAlg.reqPerm a k`: the request
  point of step `k`; `ReqQueryAlg.logSplit`, `ReqQueryAlg.instStep`, `ReqQueryAlg.inst a`: the
  query algorithm with the replies `a`.
- `vEmb`, `vEmb_apply`, `permOp_vEmb`, `vEmb_permOp`, `vEmb_congr`, `sum_norm_vEmb_sq`,
  `controlled_vEmb`, `vEmb_vEmb`, `relabel_eq_vEmb`, `tensorKet_eq_vEmb`: vectors embedded along a
  basis map.
- `simQueryIso`, `simQueryIso_apply`, `wsSplit`, `wsSlice`, `wsSlice_kernelOp`,
  `wsSlice_hadamard`, `wsSlice_decOp`, `wsSlice_phaseOp`, `wsSlice_simQuery`, `simQuery_prod`: the
  simulated query as a unitary, and on a work register with a passive factor.
- `ReqQueryAlg.withPerm`, `ReqQueryAlg.withPerm_one`: each step read after a permutation.
- `ReqQueryAlg.SimW`, `ReqQueryAlg.simInitG`, `ReqQueryAlg.stepSim`, `ReqQueryAlg.storeOf`,
  `ReqQueryAlg.controlled_trans`, `ReqQueryAlg.reqPermSim`, `ReqQueryAlg.simStep_inst`: the
  simulation register with a store of the replies, its initial state and steps.
- `ReqQueryAlg.LogsAt`, `ReqQueryAlg.LogsAt.eq_none`, `ReqQueryAlg.storeOf_update`,
  `ReqQueryAlg.length_requestsBefore_of_logsAt`, `ReqQueryAlg.preV`, `ReqQueryAlg.simStage_eq_preV`,
  `ReqQueryAlg.supp_controlled_ws`, `ReqQueryAlg.preV_supp`: the instance's simulated run before
  each step, with its logs filled exactly below the step.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.Quantum

/-- **A query algorithm with a classical request point before each step**: work register `W`, the
initial state and the unitaries of a query algorithm with `t` queries, and before step `k` the
request `req k w` read from the work register and the reply written by the permutation `write k b`,
which leaves the request unchanged (`req_write`). -/
structure ReqQueryAlg (X Y Req Resp : Type) [Fintype X] [Fintype Y] (t : ℕ) (O : Type) where
  /-- The work register. -/
  W : Type
  [instFintype : Fintype W]
  [instDecidableEq : DecidableEq W]
  /-- The initial state. -/
  init : QState (QueryReg W 1 X Y)
  norm_init : ‖init‖ = 1
  /-- The unitaries; `step k` is applied after the request point of step `k`. -/
  step : Fin (t + 1) → QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y)
  /-- The request of the request point of step `k`. -/
  req : Fin (t + 1) → W → Req
  /-- The reply `b` written into the work register at the request point of step `k`. -/
  write : Fin (t + 1) → Option Resp → Equiv.Perm W
  /-- Writing a reply leaves the request unchanged. -/
  req_write : ∀ k b w, req k (write k b w) = req k w
  /-- The output read from a computational-basis outcome of the work register. -/
  out : W → O

attribute [instance] ReqQueryAlg.instFintype ReqQueryAlg.instDecidableEq

namespace ReqQueryAlg

variable {X Y Req Resp O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Req] [Fintype Req] {t : ℕ} (G : ReqQueryAlg X Y Req Resp t O)

/-- Undoing a reply leaves the request unchanged. -/
theorem req_write_symm (k : Fin (t + 1)) (b : Option Resp) (w : G.W) :
    G.req k ((G.write k b).symm w) = G.req k w := by
  conv_rhs => rw [← (G.write k b).apply_symm_apply w]
  rw [G.req_write]

/-- **The request point of step `k`** with the replies `a`: the reply `a k r` to the request `r`
of the work register is written into it, and `r` is copied into log `k` (the swap of `none` and
`some r`: a blank log becomes `some r`). -/
def reqPerm (a : ℕ → Req → Option Resp) (k : Fin (t + 1)) :
    Equiv.Perm (G.W × LogReg Req (t + 1)) where
  toFun p := (G.write k (a k (G.req k p.1)) p.1,
    Function.update p.2 k (Equiv.swap none (some (G.req k p.1)) (p.2 k)))
  invFun p := ((G.write k (a k (G.req k p.1))).symm p.1,
    Function.update p.2 k (Equiv.swap none (some (G.req k p.1)) (p.2 k)))
  left_inv p := by
    obtain ⟨w, lg⟩ := p
    simp only [G.req_write, Equiv.symm_apply_apply, Function.update_self, Equiv.swap_apply_self,
      Function.update_idem, Function.update_eq_self]
  right_inv p := by
    obtain ⟨w, lg⟩ := p
    simp only [G.req_write_symm, Equiv.apply_symm_apply, Function.update_self,
      Equiv.swap_apply_self, Function.update_idem, Function.update_eq_self]

/-- The registers of the instance as the algorithm's registers and the logs. -/
def logSplit : QueryReg (G.W × LogReg Req (t + 1)) 1 X Y ≃ QueryReg G.W 1 X Y × LogReg Req (t + 1) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Step `k` of the instance** with the replies `a`: the request point (`reqPerm`), then the
algorithm's unitary `step k` with the identity on the logs. -/
noncomputable def instStep (a : ℕ → Req → Option Resp) (k : Fin (t + 1)) :
    QState (QueryReg (G.W × LogReg Req (t + 1)) 1 X Y) ≃ₗᵢ[ℂ]
      QState (QueryReg (G.W × LogReg Req (t + 1)) 1 X Y) :=
  (permOp ((G.reqPerm a k).prodCongr (Equiv.refl _))).trans
    ((relabel G.logSplit).trans ((controlled fun _ => G.step k).trans (relabel G.logSplit.symm)))

/-- **The query algorithm with the replies `a`**: work register `W` with the logs, the initial state
with blank logs, step `k` the request point of step `k` then `step k` (`instStep`), the output read
from `W`. -/
noncomputable def inst (a : ℕ → Req → Option Resp) : QueryAlg X Y t O where
  W := G.W × LogReg Req (t + 1)
  init := relabel G.logSplit.symm (tensorKet G.init (fun _ => none))
  norm_init := by rw [LinearIsometryEquiv.norm_map, norm_tensorKet, G.norm_init]
  step k := G.instStep a k
  out p := G.out p.1

end ReqQueryAlg

/-! ### Vectors embedded along a basis map -/

section VEmb

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- **A vector embedded along a basis map `f`**: the amplitude at `b` is the sum of the amplitudes
at the basis states `f` maps to `b`. For an injective `f` it moves each amplitude to its image. -/
def vEmb (f : α → β) (v : QState α) : QState β :=
  WithLp.toLp 2 fun b => ∑ a, if f a = b then v a else 0

theorem vEmb_apply (f : α → β) (v : QState α) (b : β) :
    vEmb f v b = ∑ a, if f a = b then v a else 0 :=
  rfl

/-- A basis permutation after an embedding is the embedding along the composed map. -/
theorem permOp_vEmb (π : Equiv.Perm β) (f : α → β) (v : QState α) :
    permOp π (vEmb f v) = vEmb (π ∘ f) v := by
  ext b
  simp only [permOp_apply, vEmb_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = π.symm b
  · rw [if_pos h, if_pos (by rw [h, Equiv.apply_symm_apply])]
  · rw [if_neg h, if_neg fun h' => h (by rw [← h', Equiv.symm_apply_apply])]

/-- An embedding after a basis permutation is the embedding along the composed map. -/
theorem vEmb_permOp [DecidableEq α] (π : Equiv.Perm α) (f : α → β) (v : QState α) :
    vEmb f (permOp π v) = vEmb (f ∘ π) v := by
  ext b
  simp only [vEmb_apply, permOp_apply, Function.comp_apply]
  exact (Fintype.sum_equiv π.symm _ _ fun a => by simp).trans rfl

/-- Embeddings along maps that agree on the support of `v` are equal. -/
theorem vEmb_congr {f g : α → β} {v : QState α} (h : ∀ a, v a ≠ 0 → f a = g a) :
    vEmb f v = vEmb g v := by
  ext b
  simp only [vEmb_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hv : v a = 0
  · simp [hv]
  · rw [h a hv]

/-- **The Born weights of an embedding along an injective map** are those of the vector, read
through the map. -/
theorem sum_norm_vEmb_sq {f : α → β} (hf : Function.Injective f) (v : QState α) (g : β → ℝ) :
    ∑ b, g b * ‖vEmb f v b‖ ^ 2 = ∑ a, g (f a) * ‖v a‖ ^ 2 := by
  classical
  have hb : ∀ b, vEmb f v b = if h : ∃ a, f a = b then v h.choose else 0 := by
    intro b
    rw [vEmb_apply]
    split_ifs with h
    · rw [Finset.sum_eq_single h.choose (fun a _ ha => if_neg fun h' => ha (hf (h'.trans
        h.choose_spec.symm))) (fun h' => absurd (Finset.mem_univ _) h'), if_pos h.choose_spec]
    · exact Finset.sum_eq_zero fun a _ => if_neg fun h' => h ⟨a, h'⟩
  simp only [hb]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) fun b _ hb' => by
    rw [dif_neg fun ⟨a, ha⟩ => hb' (Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩)]; simp,
    Finset.sum_image fun a _ a' _ h => hf h]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
  rw [dif_pos hex, hf hex.choose_spec]

/-- **A unitary on one factor commutes with an embedding that keeps that factor**: for
decompositions `σ : β ≃ S × R` and `τ : α ≃ S × M` and a map `g` of the other factors, the unitary
`V` on `S` applied after embedding along `σ⁻¹ ∘ (id × g) ∘ τ` is the embedding of `V` applied on
`S`. -/
theorem controlled_vEmb {S R M : Type*} [Fintype S] [Fintype R] [Fintype M] [DecidableEq S]
    [DecidableEq R] (σ : β ≃ S × R) (τ : α ≃ S × M) (g : M → R)
    (V : QState S ≃ₗᵢ[ℂ] QState S) (v : QState α) :
    relabel σ.symm (controlled (fun _ => V) (relabel σ
        (vEmb (fun a => σ.symm ((τ a).1, g (τ a).2)) v))) =
      vEmb (fun a => σ.symm ((τ a).1, g (τ a).2))
        (relabel τ.symm (controlled (fun _ => V) (relabel τ v))) := by
  classical
  ext b
  obtain ⟨⟨s, r⟩, rfl⟩ : ∃ p, σ.symm p = b := ⟨σ b, σ.symm_apply_apply b⟩
  simp only [relabel_apply, Equiv.symm_symm, Equiv.apply_symm_apply, controlled_apply, vEmb_apply]
  -- the slice of the embedding at `r` is the sum of the slices of `v` over the labels `g⁻¹ r`
  have hslice : (WithLp.toLp 2 fun x : S => ∑ a, if σ.symm ((τ a).1, g (τ a).2) = σ.symm (x, r)
      then v a else 0 : QState S) =
      ∑ m : M, if g m = r then (WithLp.toLp 2 fun x : S => v (τ.symm (x, m)) : QState S) else 0 := by
    ext x
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    rw [← Fintype.sum_equiv τ.symm (fun p : S × M => if σ.symm (p.1, g p.2) = σ.symm (x, r) then
      v (τ.symm p) else 0) _ (fun p => by simp), Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x (fun y _ hy => Finset.sum_eq_zero fun m _ => by
      rw [if_neg fun h => hy (Prod.mk.inj (σ.symm.injective h)).1]) (fun h => absurd
        (Finset.mem_univ _) h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : g m = r
    · simp [hm]
    · rw [if_neg fun h => hm (Prod.mk.inj (σ.symm.injective h)).2, if_neg hm]
      rfl
  rw [hslice, map_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  have hL : ∀ m : M, (V (if g m = r then (WithLp.toLp 2 fun x : S => v (τ.symm (x, m)) : QState S)
      else 0)) s = if g m = r then V (WithLp.toLp 2 fun x : S => v (τ.symm (x, m))) s else 0 := by
    intro m
    split_ifs <;> simp
  simp only [hL]
  rw [← Fintype.sum_equiv τ.symm (fun p : S × M => if σ.symm (p.1, g p.2) = σ.symm (s, r) then
      V (WithLp.toLp 2 fun x => v (τ.symm (x, p.2))) p.1 else 0) _
      (fun p => by simp only [Equiv.apply_symm_apply]; rfl),
    Fintype.sum_prod_type, Finset.sum_eq_single s ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : g m = r
    · rw [if_pos hm, if_pos (by rw [hm])]
    · rw [if_neg hm, if_neg fun h => hm (Prod.mk.inj (σ.symm.injective h)).2]
  · intro y _ hy
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg fun h => hy (Prod.mk.inj (σ.symm.injective h)).1]

/-- Embeddings compose. -/
theorem vEmb_vEmb {γ' : Type*} [Fintype γ'] [DecidableEq α] (f : α → β) (g : γ' → α)
    (v : QState γ') : vEmb f (vEmb g v) = vEmb (f ∘ g) v := by
  ext b
  simp only [vEmb_apply, Function.comp_apply]
  have h1 : ∀ a, (if f a = b then ∑ x, (if g x = a then v x else 0) else 0) =
      ∑ x, if f a = b then (if g x = a then v x else 0) else 0 := by
    intro a
    split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (g x) (fun a _ ha => by split_ifs with h h' <;> first | rfl |
    exact absurd h'.symm ha) (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- A relabelling is the embedding along the equivalence. -/
theorem relabel_eq_vEmb [DecidableEq α] (σ : α ≃ β) (v : QState α) : relabel σ v = vEmb σ v := by
  ext b
  rw [relabel_apply, vEmb_apply, Finset.sum_eq_single (σ.symm b) (fun a _ ha => if_neg fun h =>
    ha (by rw [← h, Equiv.symm_apply_apply])) (fun h => absurd (Finset.mem_univ _) h),
    if_pos (Equiv.apply_symm_apply σ b)]

/-- A vector beside a basis state is the embedding along `x ↦ (x, r₀)`. -/
theorem tensorKet_eq_vEmb {R : Type*} [Fintype R] [DecidableEq R] [DecidableEq α] (v : QState α)
    (r₀ : R) : tensorKet v r₀ = vEmb (fun x => (x, r₀)) v := by
  ext ⟨x, r⟩
  rw [tensorKet_apply, vEmb_apply, Finset.sum_eq_single x (fun a _ ha => if_neg fun h =>
    ha (Prod.mk.inj h).1) (fun h => absurd (Finset.mem_univ _) h)]
  by_cases hr : r = r₀
  · subst hr
    simp
  · rw [if_neg hr, if_neg fun h => hr (Prod.mk.inj h).2.symm, mul_zero]

end VEmb

/-! ### The simulated query on a work register with a passive factor -/

section Natural

open GordieHowe.QROM

variable {m t : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B) (W L : Type) [Fintype W] [DecidableEq W] [Fintype L] [DecidableEq L]

/-- **The simulated query as a unitary** (`simQuery`, which preserves norms, `norm_simQuery`). -/
noncomputable def simQueryIso :
    QState (SimRegister W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister W I J m t) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (simQuery (B := B) e W t).toLinearMap
      norm_map' := norm_simQuery e } rfl

theorem simQueryIso_apply (v : QState (SimRegister W I J m t)) :
    simQueryIso e W v = simQuery e W t v :=
  rfl

/-- The simulation register of the work register `W × L` as that of `W` and the factor `L`. -/
def wsSplit : SimRegister (W × L) I J m t ≃ SimRegister W I J m t × L where
  toFun b := (((b.1.1.1, b.1.2), b.2), b.1.1.2)
  invFun p := (((p.1.1.1, p.2), p.1.1.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {W L}

/-- The slice of a vector of the simulation register of `W × L` at the value `l` of `L`. -/
def wsSlice (v : QState (SimRegister (W × L) I J m t)) (l : L) : QState (SimRegister W I J m t) :=
  WithLp.toLp 2 fun x => v ((wsSplit W L).symm (x, l))

/-- **A kernel that keeps the passive factor acts slice by slice**: if the kernel `K` on `W × L` is
the kernel `K₀` on `W` between basis states with the same value of `L`, and `0` between the others,
then each slice of `kernelOp K v` is `kernelOp K₀` of the slice. -/
theorem wsSlice_kernelOp {K : SimRegister (W × L) I J m t → SimRegister (W × L) I J m t → ℂ}
    {K₀ : SimRegister W I J m t → SimRegister W I J m t → ℂ}
    (hK : ∀ b' b, K b' b = if (wsSplit W L b').2 = (wsSplit W L b).2 then
      K₀ (wsSplit W L b').1 (wsSplit W L b).1 else 0)
    (v : QState (SimRegister (W × L) I J m t)) (l : L) :
    wsSlice (kernelOp K v) l = kernelOp K₀ (wsSlice v l) := by
  ext x
  simp only [wsSlice, kernelOp_apply, hK, Equiv.apply_symm_apply]
  rw [← Fintype.sum_equiv (wsSplit W L).symm (fun p : SimRegister W I J m t × L =>
      (if l = p.2 then K₀ x p.1 else 0) * v ((wsSplit W L).symm p)) _
      (fun p => by simp only [Equiv.apply_symm_apply]), Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_eq_single l (fun l' _ hl => Finset.sum_eq_zero fun y _ => by
      rw [if_neg fun h => hl h.symm, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem wsSlice_hadamard (v : QState (SimRegister (W × L) I J m t)) (l : L) :
    wsSlice (QROM.hadamard (W × L) t v) l = QROM.hadamard W t (wsSlice v l) := by
  unfold QROM.hadamard
  refine wsSlice_kernelOp (fun b' b => ?_) v l
  obtain ⟨⟨⟨w', l'⟩, q'⟩, s'⟩ := b'
  obtain ⟨⟨⟨w, l₀⟩, q⟩, s₀⟩ := b
  simp only [wsSplit, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases hl : l' = l₀
  · subst hl
    simp only [qIn, qAns, and_true, ↓reduceIte]
    try exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · simp [hl]

theorem wsSlice_decOp (v : QState (SimRegister (W × L) I J m t)) (l : L) :
    wsSlice (decOp e (W × L) t v) l = decOp e W t (wsSlice v l) := by
  unfold decOp
  refine wsSlice_kernelOp (fun b' b => ?_) v l
  obtain ⟨⟨⟨w', l'⟩, q'⟩, s'⟩ := b'
  obtain ⟨⟨⟨w, l₀⟩, q⟩, s₀⟩ := b
  simp only [wsSplit, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases hl : l' = l₀
  · subst hl
    simp only [qIn, qAns, and_true, ↓reduceIte]
    try exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · simp [hl]

theorem wsSlice_phaseOp (v : QState (SimRegister (W × L) I J m t)) (l : L) :
    wsSlice (phaseOp e (W × L) t v) l = phaseOp e W t (wsSlice v l) := by
  unfold phaseOp
  refine wsSlice_kernelOp (fun b' b => ?_) v l
  obtain ⟨⟨⟨w', l'⟩, q'⟩, s'⟩ := b'
  obtain ⟨⟨⟨w, l₀⟩, q⟩, s₀⟩ := b
  simp only [wsSplit, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases hl : l' = l₀
  · subst hl
    simp only [qIn, qAns, and_true, ↓reduceIte]
    try exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · simp [hl]

/-- **The simulated query acts slice by slice on a passive factor of the work register.** -/
theorem wsSlice_simQuery (v : QState (SimRegister (W × L) I J m t)) (l : L) :
    wsSlice (simQuery e (W × L) t v) l = simQuery e W t (wsSlice v l) := by
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply, wsSlice_hadamard,
    wsSlice_decOp, wsSlice_phaseOp]

variable (W L) in
/-- **The simulated query on `W × L` is that on `W` with the identity on `L`.** -/
theorem simQuery_prod (v : QState (SimRegister (W × L) I J m t)) :
    simQuery e (W × L) t v =
      relabel (wsSplit W L).symm (controlled (fun _ => simQueryIso e W) (relabel (wsSplit W L) v)) := by
  ext b
  have h := congrArg (fun u : QState (SimRegister W I J m t) => u (wsSplit W L b).1)
    (wsSlice_simQuery e v (wsSplit W L b).2)
  simp only [wsSlice, Prod.mk.eta, Equiv.symm_apply_apply] at h
  rw [h]
  rfl

end Natural

/-! ### The adversary holding the compressed-oracle simulation, with real requests -/

namespace ReqQueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)
  (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Inhabited X] [AddGroup Y]
  [Inhabited Req]

/-- The workspace of the simulating adversary: the simulation register of `G` (its registers and
the database slots) and a store of the replies, one per request point. -/
abbrev SimW : Type := SimRegister G.W I J m t × (Fin (t + 1) → Option Resp)

instance SimW.instFintype : Fintype (G.SimW (I := I) (J := J) (m := m)) :=
  instFintypeProd _ _

instance SimW.instDecidableEq : DecidableEq (G.SimW (I := I) (J := J) (m := m)) :=
  instDecidableEqProd

instance SimW.instFintypeDReg : Fintype (DReg (G.SimW (I := I) (J := J) (m := m)) 1 X Y Req Resp) :=
  instFintypeProd _ _

instance SimW.instDecidableEqDReg :
    DecidableEq (DReg (G.SimW (I := I) (J := J) (m := m)) 1 X Y Req Resp) :=
  DReg.instDecidableEq

/-- The initial state of `G` with the empty database. -/
noncomputable def simInitG : QState (SimRegister G.W I J m t) :=
  tensorKet G.init (dbSlots e t (∅ : DB (Bits m) B))

/-- `G`'s unitary `step k` on the simulation register, with the identity on the database. -/
noncomputable def stepSim (k : Fin (t + 1)) :
    QState (SimRegister G.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister G.W I J m t) :=
  controlled fun _ => G.step k

/-! ### The registers of the mixed game of the simulating adversary -/

variable (a : ℕ → Req → Option Resp)

/-- The replies of the logged requests: store `j` holds the reply `a j r` to the request `r` of
log `j`, and nothing for a blank log. -/
def storeOf (lg : LogReg Req (t + 1)) : Fin (t + 1) → Option Resp :=
  fun j => (lg j).bind (a j)

/-! ### The steps of the mixed game -/

/-! ### The steps as operations on the simulation register and permutations -/

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Inhabited Req] in
/-- A controlled composition is the composition of the controlled unitaries. -/
theorem controlled_trans {ι L : Type*} [Fintype ι] [Fintype L] (A₁ A₂ : QState ι ≃ₗᵢ[ℂ] QState ι)
    (v : QState (ι × L)) :
    controlled (fun _ => A₁.trans A₂) v = controlled (fun _ => A₂) (controlled (fun _ => A₁) v) := by
  ext ⟨i, l⟩
  rfl

/-- The request point of step `k` on the instance's simulation register. -/
def reqPermSim (k : Fin (t + 1)) : Equiv.Perm (SimRegister (G.W × LogReg Req (t + 1)) I J m t) :=
  ((G.reqPerm a k).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

/-- **The instance's step on its simulation register**: the request point, then `G`'s step with
the identity on the logs and the database. -/
theorem simStep_inst (k : Fin (t + 1)) (v : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) :
    simStep (G.inst a) k v = relabel (wsSplit G.W (LogReg Req (t + 1))).symm
      (controlled (fun _ => stepSim G k) (relabel (wsSplit G.W (LogReg Req (t + 1)))
        (permOp (reqPermSim G a k) v))) := by
  rw [simStep, OracleAlg.stepAt_of_lt _ k.2]
  rfl

/-! ### The request points -/

/-- The logs filled exactly below `k`. -/
def LogsAt (k : ℕ) (lg : LogReg Req (t + 1)) : Prop :=
  ∀ j : Fin (t + 1), ((j : ℕ) < k ↔ (lg j).isSome)

omit [Fintype Req] [DecidableEq Req] in
theorem LogsAt.eq_none {k : Fin (t + 1)} {lg : LogReg Req (t + 1)} (h : LogsAt k lg) :
    lg k = none := by
  have := (h k).not.1 (lt_irrefl _)
  simpa using this

theorem storeOf_update {lg : LogReg Req (t + 1)} (k : Fin (t + 1)) (r : Req) :
    storeOf a (Function.update lg k (some r)) = Function.update (storeOf a lg) k (a k r) := by
  funext j
  by_cases h : j = k
  · subst h
    simp [storeOf]
  · simp [storeOf, Function.update_of_ne h]

variable {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω)

omit [Fintype Req] [DecidableEq Req] in
/-- The logs filled exactly below `k` hold `k` requests before slot `k`. -/
theorem length_requestsBefore_of_logsAt {k : ℕ} (hk : k ≤ t + 1) {lg : LogReg Req (t + 1)}
    (h : LogsAt k lg) : (requestsBefore lg k).length = k := by
  suffices ∀ j ≤ k, (requestsBefore lg j).length = j from this k le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjt : j < t + 1 := by omega
    rw [requestsBefore_succ_of_lt lg hjt, List.length_append, ih (by omega)]
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((h ⟨j, hjt⟩).1 (by simp; omega))
    simp [hr]

variable [Nonempty Y]

/-! ### The instance's simulated run -/

/-- **The instance's simulated run before step `k`**: the initial state with the empty database,
then after step `k` the simulated query. `simStage k` is `simStep k` of it (`simStage_eq_preV`). -/
noncomputable def preV : ℕ → QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)
  | 0 => simInit e (G.inst a)
  | k + 1 => simQuery e (G.inst a).W t (simStage e (G.inst a) k)

theorem simStage_eq_preV (k : ℕ) : simStage e (G.inst a) k = simStep (G.inst a) k (preV e G a k) := by
  cases k with
  | zero => simp only [simStage, preV, Nat.rec_zero]
  | succ k => simp only [simStage, preV, Nat.rec_add_one]

/-- A vector supported on the basis states whose logs satisfy `P` stays so under a unitary of the
simulation register with the identity on the logs. -/
theorem supp_controlled_ws {P : LogReg Req (t + 1) → Prop}
    (V : QState (SimRegister G.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister G.W I J m t))
    {v : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)}
    (hv : ∀ b, v b ≠ 0 → P (wsSplit G.W (LogReg Req (t + 1)) b).2) (b) :
    relabel (wsSplit G.W (LogReg Req (t + 1))).symm (controlled (fun _ => V)
      (relabel (wsSplit G.W (LogReg Req (t + 1))) v)) b ≠ 0 →
      P (wsSplit G.W (LogReg Req (t + 1)) b).2 := by
  intro hb
  by_contra hP
  apply hb
  rw [relabel_apply, Equiv.symm_symm, controlled_apply]
  have h0 : (WithLp.toLp 2 fun i' => relabel (wsSplit G.W (LogReg Req (t + 1))) v
      (i', (wsSplit G.W (LogReg Req (t + 1)) b).2) : QState (SimRegister G.W I J m t)) = 0 := by
    ext i'
    rw [relabel_apply]
    by_contra hne
    exact hP (by simpa using hv _ hne)
  rw [h0, map_zero]
  rfl

/-- **The logs of the instance's simulated run before step `k` are filled exactly below `k`.** -/
theorem preV_supp (k : ℕ) (hk : k ≤ t + 1) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : preV e G a k b ≠ 0) : LogsAt k (wsSplit G.W (LogReg Req (t + 1)) b).2 := by
  induction k generalizing b with
  | zero =>
    obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b
    have hlg : lg = fun _ => none := by
      by_contra h
      apply hb
      change (G.inst a).init ((w, lg), qs) * _ = 0
      simp [ReqQueryAlg.inst, relabel_apply, tensorKet_apply, logSplit, h]
    subst hlg
    intro j
    simp [wsSplit]
  | succ k ih =>
    have hk' : k < t + 1 := by omega
    have hq : preV e G a (k + 1) = relabel (wsSplit G.W (LogReg Req (t + 1))).symm
        (controlled (fun _ => simQueryIso e G.W) (relabel (wsSplit G.W (LogReg Req (t + 1)))
          (simStage e (G.inst a) k))) :=
      simQuery_prod e G.W (LogReg Req (t + 1)) (simStage e (G.inst a) k)
    rw [hq] at hb
    refine supp_controlled_ws G _ (fun b' hb' => ?_) b hb
    rw [simStage_eq_preV, simStep_inst G a ⟨k, hk'⟩] at hb'
    refine supp_controlled_ws G _ (fun b'' hb'' => ?_) b' hb'
    rw [permOp_apply] at hb''
    have h := ih (by omega) _ hb''
    obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b''
    simp only [wsSplit, Equiv.coe_fn_mk, reqPermSim, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
      Equiv.refl_symm, Equiv.coe_refl, Prod.map, id] at h ⊢
    set p := (G.reqPerm a ⟨k, hk'⟩).symm (w, lg) with hp
    have hlg : lg = Function.update p.2 ⟨k, hk'⟩ (Equiv.swap none (some (G.req ⟨k, hk'⟩ p.1))
        (p.2 ⟨k, hk'⟩)) := by
      have := congrArg Prod.snd ((G.reqPerm a ⟨k, hk'⟩).apply_symm_apply (w, lg))
      rw [← hp] at this
      exact this.symm
    have hpk : p.2 ⟨k, hk'⟩ = none := LogsAt.eq_none (k := ⟨k, hk'⟩) h
    rw [hlg, hpk, Equiv.swap_apply_left]
    intro j
    by_cases hj : j = ⟨k, hk'⟩
    · subst hj
      simp
    · rw [Function.update_of_ne hj, ← h j]
      have : (j : ℕ) ≠ k := fun h' => hj (Fin.ext h')
      omega

/-! ### The initial state -/

/-! ### One slot of the mixed game -/

/-! ### The run of the mixed game -/

variable [Nonempty Y] (C₂ : Challenger X Y Req Resp) (aC : C₂.Coins → ℕ → Req → Option Resp)
  (hR : t + 1 ≤ C₂.Q)
  (hdet : ∀ c (k : Fin (t + 1)) (hist : List (HistoryEntry Req Resp)) (w : G.W) (H' : X → Y),
    hist.length = k → (C₂.respond c hist (G.req k w)).run H' = ⟨aC c k (G.req k w), []⟩)
  (H : X → Y) (c : C₂.Coins)

end ReqQueryAlg

open GordieHowe.QROM in
/-- **A query algorithm with request points with each step read after a permutation `b`.** -/
noncomputable abbrev ReqQueryAlg.withPerm {m : ℕ} {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {Req'' Resp'' O'' : Type} {t : ℕ}
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req'' Resp'' t O'')
    (b : Fin (t + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    ReqQueryAlg (Bits m) (BitStr I J) Req'' Resp'' t O'' :=
  { G with step := fun i => (permOp (b i)).trans (G.step i) }

open GordieHowe.QROM in
/-- `G` read after identities is `G`. -/
theorem ReqQueryAlg.withPerm_one {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] {Req'' Resp'' O'' : Type} {t : ℕ}
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req'' Resp'' t O'') :
    (G.withPerm fun _ => 1) = G :=
  rfl

end GordieHowe.Quantum
