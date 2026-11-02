-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridge

@[expose] public section

/-!
# The simulated run of a query algorithm whose steps write replies, as an instance with logs

A query algorithm on the registers of a query algorithm with request points `G` (`ReqQueryAlg`),
with `G`'s initial state and output and other unitaries `S k` (`ReqQueryAlg.withSteps`), whose step
`k` is `G`'s step after writing a reply `rep k` read from the work register (`ctrlWrite`), on the
vectors of its compressed-oracle simulation: if the reply is `a k` at the earlier requests and the
request, and the steps keep the earlier requests, then its `simLaw` is that of the instance with
logs `G.instLog a` (`ReqQueryAlg.simLaw_withSteps_eq_instLog`). The logs of the instance are copies
of the requests that the work register keeps (`hist`).

- `withSteps`, `ctrlWrite`, `simPerm`, `hist`, `iotaH`: the objects.
- `controlled_vEmb_graph`: a unitary that keeps the fibres of a label commutes with the embedding
  along the label's graph; `supported_simQuery_work`: the simulated query keeps every function of
  the work register; `bornWeight_vEmb`: Born weights along an injective embedding.
- `reqPermLogSim_iotaH`, `simStage_instLog_eq`, `preI_eq`: the request point, one step and all
  steps of the two runs.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.Quantum

namespace ReqQueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)

/-- **`G`'s registers, initial state and output with the unitaries `S`.** -/
def withSteps (S : Fin (t + 1) → QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
    QState (QueryReg G.W 1 (Bits m) (BitStr I J))) : QueryAlg (Bits m) (BitStr I J) t O where
  W := G.W
  init := G.init
  norm_init := G.norm_init
  step := S
  out := G.out

/-- **The reply `rep w` written at the request point `k`**, as a permutation of the work register,
for a reply that writing leaves unchanged (`hrep`). -/
def ctrlWrite (k : Fin (t + 1)) (rep : G.W → Option Resp)
    (hrep : ∀ x w, rep (G.write k x w) = rep w) : Equiv.Perm G.W where
  toFun w := G.write k (rep w) w
  invFun w := (G.write k (rep w)).symm w
  left_inv w := by simp [hrep]
  right_inv w := by
    have h : rep ((G.write k (rep w)).symm w) = rep w := by
      conv_rhs => rw [← (G.write k (rep w)).apply_symm_apply w]
      rw [hrep]
    simp [h]

/-- A permutation of the work register on the simulation register. -/
def simPerm (σ : Equiv.Perm G.W) : Equiv.Perm (SimRegister G.W I J m t) :=
  (σ.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

/-- **The requests before step `k`**, read from the work register: log `j` holds the request of
the request point `j` for `j < k`, nothing for the later ones. -/
def hist (k : ℕ) (s : SimRegister G.W I J m t) : LogReg Req (t + 1) :=
  fun j => if (j : ℕ) < k then some (G.req j s.1.1) else none

/-- **A basis state of `G`'s simulation register with its requests before step `k` as logs.** -/
def iotaH (k : ℕ) (s : SimRegister G.W I J m t) : SimRegister (G.W × LogReg Req (t + 1)) I J m t :=
  (wsSplit G.W (LogReg Req (t + 1))).symm (s, G.hist k s)

/-- The request point of step `k` with replies that read the earlier requests, on the instance's
simulation register. -/
def reqPermLogSim (a : ℕ → List Req → Req → Option Resp) (k : Fin (t + 1)) :
    Equiv.Perm (SimRegister (G.W × LogReg Req (t + 1)) I J m t) :=
  ((G.reqPermLog a k).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

/-- **The instance with logs' step on its simulation register**: the request point, then `G`'s step
with the identity on the logs and the database. -/
theorem simStep_instLog (a : ℕ → List Req → Req → Option Resp) (k : Fin (t + 1))
    (v : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) :
    simStep (G.instLog a) k v = relabel (wsSplit G.W (LogReg Req (t + 1))).symm
      (controlled (fun _ => stepSim G k) (relabel (wsSplit G.W (LogReg Req (t + 1)))
        (permOp (G.reqPermLogSim a k) v))) := by
  rw [simStep, OracleAlg.stepAt_of_lt _ k.2]
  rfl

/-! ### Embeddings along the graph of a label -/

section Graph

variable {W L : Type} [Fintype W] [DecidableEq W] [Fintype L] [DecidableEq L]

/-- A vector is the sum of its parts on the fibres of a label. -/
theorem sum_mask_fibre {κ : Type} [Fintype κ] (H : κ → L) (p : QState κ) :
    ∑ l, mask {s | H s = l} p = p := by
  ext s
  simp only [WithLp.ofLp_sum, Finset.sum_apply, mask_apply]
  rw [Finset.sum_eq_single (H s) (fun l _ hl => Set.indicator_of_notMem (fun h => hl h.symm) _)
    (fun h => absurd (Finset.mem_univ _) h)]
  exact Set.indicator_of_mem (show s ∈ {x | H x = H s} from rfl) _

/-- **A unitary that keeps the fibres of a label commutes with the embedding along the label's
graph**: for a label `H` of the simulation register of `W`, if `U` maps the part of `p` on each
fibre of `H` into that fibre, then `U` with the identity on `L`, after embedding `p` along
`s ↦ (s, H s)`, is the embedding of `U p`. -/
theorem controlled_vEmb_graph (H : SimRegister W I J m t → L)
    (U : QState (SimRegister W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister W I J m t))
    (p : QState (SimRegister W I J m t))
    (hU : ∀ l, Supported {s | H s = l} (U (mask {s | H s = l} p))) :
    relabel (wsSplit W L).symm (controlled (fun _ => U) (relabel (wsSplit W L)
        (vEmb (fun s => (wsSplit W L).symm (s, H s)) p))) =
      vEmb (fun s => (wsSplit W L).symm (s, H s)) (U p) := by
  ext z
  obtain ⟨⟨x, l⟩, rfl⟩ : ∃ q, (wsSplit W L).symm q = z := ⟨wsSplit W L z, by simp⟩
  have hslice : (WithLp.toLp 2 fun y => relabel (wsSplit W L)
      (vEmb (fun s => (wsSplit W L).symm (s, H s)) p) (y, l) : QState (SimRegister W I J m t)) =
      mask {s | H s = l} p := by
    ext y
    rw [relabel_apply, vEmb_apply, mask_apply]
    rw [Finset.sum_eq_single y (fun s _ hs => if_neg fun h => hs (Prod.mk.inj
      ((wsSplit W L).symm.injective h)).1) (fun h => absurd (Finset.mem_univ _) h)]
    by_cases hy : H y = l
    · rw [if_pos (by rw [hy]), Set.indicator_of_mem (show y ∈ {s | H s = l} from hy)]
    · rw [if_neg fun h => hy (Prod.mk.inj ((wsSplit W L).symm.injective h)).2,
        Set.indicator_of_notMem (show y ∉ {s | H s = l} from hy)]
  rw [relabel_apply, Equiv.symm_symm, Equiv.apply_symm_apply, controlled_apply, hslice, vEmb_apply]
  rw [Finset.sum_eq_single x (fun s _ hs => if_neg fun h => hs (Prod.mk.inj
    ((wsSplit W L).symm.injective h)).1) (fun h => absurd (Finset.mem_univ _) h)]
  conv_rhs => rw [← sum_mask_fibre H p, map_sum]
  by_cases hx : H x = l
  · rw [if_pos (by rw [hx])]
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single l (fun l' _ hl' => hU l' x (fun h => hl' (h.symm.trans hx)))
      (fun h => absurd (Finset.mem_univ _) h)]
  · rw [if_neg fun h => hx (Prod.mk.inj ((wsSplit W L).symm.injective h)).2]
    exact hU l x hx

/-- **The simulated query keeps every function of the work register**: a vector supported where
`f` of the work register is in `P` stays so. -/
theorem supported_simQuery_work {P : Set W} {v : QState (SimRegister W I J m t)}
    (hv : Supported {s | s.1.1 ∈ P} v) (e : BitStr I J ≃ B) :
    Supported {s | s.1.1 ∈ P} (simQuery e W t v) := by
  have hH : ∀ u : QState (SimRegister W I J m t), Supported {s | s.1.1 ∈ P} u →
      Supported {s | s.1.1 ∈ P} (QROM.hadamard W t u) := fun u hu => by
    refine Supported.kernelOp (fun b' b hb hb' => ?_) hu
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hb' (by simpa [h] using hb)
  have hD : ∀ u : QState (SimRegister W I J m t), Supported {s | s.1.1 ∈ P} u →
      Supported {s | s.1.1 ∈ P} (decOp e W t u) := fun u hu => by
    refine Supported.kernelOp (fun b' b hb hb' => ?_) hu
    rw [if_neg]
    intro h
    exact hb' (by simpa [h] using hb)
  have hP : ∀ u : QState (SimRegister W I J m t), Supported {s | s.1.1 ∈ P} u →
      Supported {s | s.1.1 ∈ P} (phaseOp e W t u) := fun u hu => by
    refine Supported.kernelOp (fun b' b hb hb' => ?_) hu
    rw [if_neg]
    rintro rfl
    exact hb' hb
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply]
  exact hH _ (hD _ (hP _ (hD _ (hH _ hv))))

end Graph

/-! ### The simulated runs -/

section Run

variable (a : ℕ → List Req → Req → Option Resp)
  (S : Fin (t + 1) → QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
    QState (QueryReg G.W 1 (Bits m) (BitStr I J)))

/-- The simulated run of `G.withSteps S` before step `k`. -/
noncomputable def preQ : ℕ → QState (SimRegister G.W I J m t)
  | 0 => simInit e (G.withSteps S)
  | k + 1 => simQuery e (G.withSteps S).W t (simStage e (G.withSteps S) k)

/-- The simulated run of `G.instLog a` before step `k`. -/
noncomputable def preI : ℕ → QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)
  | 0 => simInit e (G.instLog a)
  | k + 1 => simQuery e (G.instLog a).W t (simStage e (G.instLog a) k)

/-- The simulated run of `G.withSteps S` after step `k`, on `G`'s simulation register. -/
noncomputable def stageQ (k : ℕ) : QState (SimRegister G.W I J m t) :=
  simStage e (G.withSteps S) k

/-- The simulated run of `G.instLog a` after step `k`, on its simulation register. -/
noncomputable def stageI (k : ℕ) : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t) :=
  simStage e (G.instLog a) k

theorem simStage_withSteps (k : ℕ) :
    simStage e (G.withSteps S) k = simStep (G.withSteps S) k (preQ e G S k) := by
  cases k with
  | zero => simp only [simStage, preQ, Nat.rec_zero]
  | succ k => simp only [simStage, preQ, Nat.rec_add_one]

theorem simStage_instLog (k : ℕ) :
    simStage e (G.instLog a) k = simStep (G.instLog a) k (preI e G a k) := by
  cases k with
  | zero => simp only [simStage, preI, Nat.rec_zero]
  | succ k => simp only [simStage, preI, Nat.rec_add_one]

theorem simStep_withSteps (k : Fin (t + 1)) (v : QState (SimRegister G.W I J m t)) :
    simStep (G.withSteps S) k v = controlled (fun _ => S k) v := by
  rw [simStep, OracleAlg.stepAt_of_lt _ k.2]
  rfl

/-- The initial simulated state of the instance with logs is the embedding of `G`'s with blank
logs. -/
theorem preI_zero : preI e G a 0 = vEmb (G.iotaH 0) (preQ e G S 0) := by
  ext b
  obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b
  change G.init (w, qs) * (if lg = (fun _ => none) then 1 else 0) *
      (if sl = dbSlots e t (∅ : DB (Bits m) B) then 1 else 0) =
    ∑ s, if G.iotaH 0 s = (((w, lg), qs), sl) then
      G.init s.1 * (if s.2 = dbSlots e t (∅ : DB (Bits m) B) then 1 else 0) else 0
  rw [Finset.sum_eq_single ((w, qs), sl) (fun s _ hs => if_neg fun h => hs (by
      have h1 := congrArg (fun b : SimRegister (G.W × LogReg Req (t + 1)) I J m t => b.1.1.1) h
      have h2 := congrArg (fun b : SimRegister (G.W × LogReg Req (t + 1)) I J m t => b.1.2) h
      have h3 := congrArg (fun b : SimRegister (G.W × LogReg Req (t + 1)) I J m t => b.2) h
      exact Prod.ext (Prod.ext h1 h2) h3)) (fun h => absurd (Finset.mem_univ _) h)]
  have hh : ∀ s : SimRegister G.W I J m t, G.hist 0 s = fun _ => none := fun s => by
    funext j
    simp [hist]
  by_cases h1 : lg = fun _ => none
  · subst h1
    have hi : G.iotaH 0 ((w, qs), sl) = (((w, fun _ => none), qs), sl) := by
      simp [iotaH, hh, wsSplit]
    rw [if_pos hi]
    simp
  · rw [if_neg h1, mul_zero, zero_mul, if_neg]
    intro h
    apply h1
    have := congrArg (fun b : SimRegister (G.W × LogReg Req (t + 1)) I J m t => b.1.1.2) h
    simp only [iotaH, hh, wsSplit] at this
    exact this.symm

variable {rep : Fin (t + 1) → G.W → Option Resp}
  (hrep : ∀ k x w, rep k (G.write k x w) = rep k w)

include hrep in
/-- **The logged request point at the requests before step `k`**: from a basis state with its
requests before step `k` as logs, the request point is the controlled write of the reply `rep k`
(when it is `a k` at those requests, `hA`) with the request of step `k` added to the logs. -/
theorem reqPermLogSim_iotaH (hreqW : ∀ k x w j, G.req j (G.write k x w) = G.req j w)
    (k : Fin (t + 1)) (s : SimRegister G.W I J m t)
    (hA : rep k s.1.1 = a k (requestsBefore (G.hist k s) k) (G.req k s.1.1)) :
    G.reqPermLogSim a k (G.iotaH k s) =
      G.iotaH (k + 1) (G.simPerm (G.ctrlWrite k (rep k) (hrep k)) s) := by
  obtain ⟨⟨w, qs⟩, sl⟩ := s
  simp only at hA
  have hk : G.hist k (((w, qs), sl) : SimRegister G.W I J m t) k = none := by
    simp [hist]
  have hl : Function.update (G.hist k (((w, qs), sl) : SimRegister G.W I J m t)) k
      (Equiv.swap none (some (G.req k w)) (G.hist k (((w, qs), sl) : SimRegister G.W I J m t) k)) =
      G.hist (k + 1) (((G.write k (rep k w) w, qs), sl) : SimRegister G.W I J m t) := by
    rw [hk, Equiv.swap_apply_left]
    funext j
    by_cases hj : j = k
    · subst hj
      simp [hist, hreqW]
    · rw [Function.update_of_ne hj]
      have : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
      simp only [hist, hreqW]
      by_cases hjk : (j : ℕ) < k
      · rw [if_pos hjk, if_pos (by omega)]
      · rw [if_neg hjk, if_neg (by omega)]
  simp only [reqPermLogSim, iotaH, wsSplit, simPerm, ctrlWrite, reqPermLog, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  rw [← hA, hl]

variable (Good : ℕ → Set (SimRegister G.W I J m t))

include hrep in
/-- **One step of the two runs**: if the instance's run before step `k` is the embedding of the
other's (supported on `Good k`), so is the instance's run after step `k`, along the requests before
step `k + 1`. -/
theorem simStage_instLog_eq (hreqW : ∀ k x w j, G.req j (G.write k x w) = G.req j w)
    (hS : ∀ (k : Fin (t + 1)) q, Supported (Good k) q →
      controlled (fun _ => S k) q = stepSim G k (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))
    (hA : ∀ (k : Fin (t + 1)) s, s ∈ Good k →
      rep k s.1.1 = a k (requestsBefore (G.hist k s) k) (G.req k s.1.1))
    (hP : ∀ (k : Fin (t + 1)) q, Supported (Good k) q → ∀ l,
      Supported {s | G.hist (k + 1) s = l} (stepSim G k (mask {s | G.hist (k + 1) s = l}
        (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))))
    (k : ℕ) (hk : k < t + 1) (hI : preI e G a k = vEmb (G.iotaH k) (preQ e G S k))
    (hQ : Supported (Good k) (preQ e G S k)) :
    @Eq (QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) (simStage e (G.instLog a) k)
      (vEmb (G.iotaH (k + 1)) (stageQ e G S k)) := by
  set σ := G.ctrlWrite ⟨k, hk⟩ (rep ⟨k, hk⟩) (hrep ⟨k, hk⟩)
  rw [simStage_instLog]
  show @Eq (QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t))
    (simStep (G.instLog a) (⟨k, hk⟩ : Fin (t + 1)) (preI e G a k)) _
  rw [hI, simStep_instLog G a ⟨k, hk⟩, permOp_vEmb,
    vEmb_congr (v := preQ e G S k) (f := ⇑(G.reqPermLogSim a ⟨k, hk⟩) ∘ G.iotaH k)
      (g := G.iotaH (k + 1) ∘ G.simPerm σ)
      (fun s hs => G.reqPermLogSim_iotaH a hrep hreqW ⟨k, hk⟩ s
        (hA ⟨k, hk⟩ s (by by_contra h; exact hs (hQ s h)))),
    ← vEmb_permOp]
  have hg := controlled_vEmb_graph (L := LogReg Req (t + 1)) (G.hist (k + 1)) (stepSim G ⟨k, hk⟩)
    (permOp (G.simPerm σ) (preQ e G S k)) (hP ⟨k, hk⟩ _ hQ)
  unfold iotaH
  rw [hg, ← hS ⟨k, hk⟩ _ hQ, stageQ, simStage_withSteps]
  change _ = vEmb _ (simStep (G.withSteps S) (⟨k, hk⟩ : Fin (t + 1)) _)
  rw [simStep_withSteps]
  rfl

include hrep in
/-- **The two simulated runs**: before every step `k ≤ t`, the instance's run is the embedding of
the other's along the requests before step `k`, and the other's is supported on `Good k`. -/
theorem preI_eq (hreqW : ∀ k x w j, G.req j (G.write k x w) = G.req j w)
    (hS : ∀ (k : Fin (t + 1)) q, Supported (Good k) q →
      controlled (fun _ => S k) q = stepSim G k (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))
    (hA : ∀ (k : Fin (t + 1)) s, s ∈ Good k →
      rep k s.1.1 = a k (requestsBefore (G.hist k s) k) (G.req k s.1.1))
    (hP : ∀ (k : Fin (t + 1)) q, Supported (Good k) q → ∀ l,
      Supported {s | G.hist (k + 1) s = l} (stepSim G k (mask {s | G.hist (k + 1) s = l}
        (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))))
    (h0 : Supported (Good 0) (preQ e G S 0))
    (hG : ∀ (k : Fin (t + 1)) q, (k : ℕ) < t → Supported (Good k) q →
      Supported (Good (k + 1)) (simQuery e G.W t (controlled (fun _ => S k) q))) :
    ∀ k ≤ t, preI e G a k = vEmb (G.iotaH k) (preQ e G S k) ∧ Supported (Good k) (preQ e G S k) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨preI_zero e G a S, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨hI, hQ⟩ := ih (by omega)
    have hst := simStage_instLog_eq e G a S hrep Good hreqW hS hA hP k (by omega) hI hQ
    have hq : ∀ v : QState (SimRegister G.W I J m t),
        relabel (wsSplit G.W (LogReg Req (t + 1))).symm (controlled (fun _ => simQueryIso e G.W)
          (relabel (wsSplit G.W (LogReg Req (t + 1))) (vEmb (fun s => (wsSplit G.W
            (LogReg Req (t + 1))).symm (s, G.hist (k + 1) s)) v))) =
        vEmb (fun s => (wsSplit G.W (LogReg Req (t + 1))).symm (s, G.hist (k + 1) s))
          (simQueryIso e G.W v) := fun v =>
      controlled_vEmb_graph (G.hist (k + 1)) (simQueryIso e G.W) v fun l =>
        supported_simQuery_work (P := {w | (fun j : Fin (t + 1) =>
          if (j : ℕ) < k + 1 then some (G.req j w) else none) = l})
          (fun s hs => Set.indicator_of_notMem hs _) e
    refine ⟨?_, ?_⟩
    · change simQuery e (G.instLog a).W t (simStage e (G.instLog a) k) = _
      rw [hst]
      have h1 := simQuery_prod e G.W (LogReg Req (t + 1))
        (vEmb (G.iotaH (k + 1)) (stageQ e G S k))
      refine h1.trans ?_
      unfold iotaH
      exact hq _
    · have hk' : k < t + 1 := by omega
      have := hG ⟨k, hk'⟩ (preQ e G S k) (by simp; omega) hQ
      change Supported _ (simQuery e (G.withSteps S).W t (simStage e (G.withSteps S) k))
      rw [simStage_withSteps]
      change Supported _ (simQuery e G.W t (simStep (G.withSteps S) (⟨k, hk'⟩ : Fin (t + 1)) _))
      rw [simStep_withSteps]
      exact this

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype Req] [Fintype Resp]
  [DecidableEq Resp] in
/-- **The Born weights of an embedding along an injective map** are those of the vector on the
preimage. -/
theorem bornWeight_vEmb {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (v : QState α) (T : Set β) :
    bornWeight (vEmb f v) T = bornWeight v (f ⁻¹' T) := by
  classical
  have hb : ∀ b, vEmb f v b = if h : ∃ a, f a = b then v h.choose else 0 := by
    intro b
    rw [vEmb_apply]
    split_ifs with h
    · rw [Finset.sum_eq_single h.choose (fun a _ ha => if_neg fun h' => ha (hf (h'.trans
        h.choose_spec.symm))) (fun h' => absurd (Finset.mem_univ _) h'), if_pos h.choose_spec]
    · exact Finset.sum_eq_zero fun a _ => if_neg fun h' => h ⟨a, h'⟩
  rw [bornWeight_apply_eq_sum, bornWeight_apply_eq_sum]
  simp only [hb]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) fun b _ hb' => by
    have hn : ¬ ∃ a, f a = b := fun ⟨a, ha⟩ => hb' (Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩)
    simp [Set.indicator_apply, hn],
    Finset.sum_image fun a _ a' _ h => hf h]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
  rw [Set.indicator_apply, Set.indicator_apply, dif_pos hex, hf hex.choose_spec]
  rfl

theorem iotaH_injective (k : ℕ) : Function.Injective (G.iotaH (I := I) (J := J) (m := m) k) := by
  intro s s' h
  have := congrArg (wsSplit G.W (LogReg Req (t + 1))) h
  simp only [iotaH, Equiv.apply_symm_apply, Prod.mk.injEq] at this
  exact this.1

include hrep in
/-- **The simulated law of a query algorithm whose steps write replies is that of the instance
with logs**: for `G`'s registers, initial state and output with steps `S` (`withSteps`) such that,
on the vectors of the simulated run (supported on `Good k` before step `k`, `h0`, `hG`), step `k`
is `G`'s step after writing the reply `rep k` (`hS`), the reply is `a k` at the earlier requests
(`hA`), and `G`'s step keeps the requests up to `k` (`hP`; writing keeps every request, `hreqW`),
`simLaw` of `G.withSteps S` is that of `G.instLog a`. -/
theorem simLaw_withSteps_eq_instLog (hreqW : ∀ k x w j, G.req j (G.write k x w) = G.req j w)
    (hS : ∀ (k : Fin (t + 1)) q, Supported (Good k) q →
      controlled (fun _ => S k) q = stepSim G k (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))
    (hA : ∀ (k : Fin (t + 1)) s, s ∈ Good k →
      rep k s.1.1 = a k (requestsBefore (G.hist k s) k) (G.req k s.1.1))
    (hP : ∀ (k : Fin (t + 1)) q, Supported (Good k) q → ∀ l,
      Supported {s | G.hist (k + 1) s = l} (stepSim G k (mask {s | G.hist (k + 1) s = l}
        (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))))
    (h0 : Supported (Good 0) (preQ e G S 0))
    (hG : ∀ (k : Fin (t + 1)) q, (k : ℕ) < t → Supported (Good k) q →
      Supported (Good (k + 1)) (simQuery e G.W t (controlled (fun _ => S k) q))) :
    simLaw e (G.withSteps S) = simLaw e (G.instLog a) := by
  obtain ⟨hI, hQ⟩ := preI_eq e G a S hrep Good hreqW hS hA hP h0 hG t le_rfl
  have hst := simStage_instLog_eq e G a S hrep Good hreqW hS hA hP t (by omega) hI hQ
  ext T
  rw [simLaw, simLaw, MeasureTheory.OuterMeasure.map_apply, MeasureTheory.OuterMeasure.map_apply]
  have hst' : stageI e G a t = vEmb (G.iotaH (t + 1)) (stageQ e G S t) := hst
  change bornWeight (stageQ e G S t) ((fun b => (G.out b.1.1, slotsDB e b.2)) ⁻¹' T) =
    bornWeight (stageI e G a t) ((fun b => (G.out b.1.1.1, slotsDB e b.2)) ⁻¹' T)
  rw [hst', bornWeight_vEmb (G.iotaH_injective (t + 1))]
  rfl

end Run

end ReqQueryAlg

end GordieHowe.Quantum
