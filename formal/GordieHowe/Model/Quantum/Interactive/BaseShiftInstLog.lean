-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftSteps
public import GordieHowe.Model.Quantum.Pure.MultiRelayRun

@[expose] public section

/-!
# The instance with logs of a query algorithm with request points read after permutations

`ReqQueryAlg.simLaw_withPerm_withSteps_eq_instLog`: `simLaw_withSteps_eq_instLog` for
`G.withPerm b`, from its hypotheses for `G`, writes that keep the supports `Good` both ways
(`hWG`), and two facts on the permutations `b`: they keep the supports (`hbG`) and every request
(`hbR`). The permutations act after the writes, as in the run.

- `controlled_permOp_eq`, `ReqQueryAlg.stepSim_withPerm`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

theorem controlled_permOp_eq {ι L : Type*} [Fintype ι] [Fintype L] (π : Equiv.Perm ι)
    (v : QState (ι × L)) :
    controlled (fun _ => permOp π) v = permOp (π.prodCongr (Equiv.refl L)) v := by
  ext ⟨i, l⟩
  rfl

namespace ReqQueryAlg

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I]
  [DecidableEq J] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)
  (b : Fin (t + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)))

omit [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
theorem stepSim_withPerm (k : Fin (t + 1)) (v : QState (SimRegister G.W I J m t)) :
    stepSim (G.withPerm b) k v = stepSim G k (permOp ((b k).prodCongr (Equiv.refl _)) v) := by
  change controlled (fun _ => (permOp (b k)).trans (G.step k)) v = _
  rw [controlled_trans, controlled_permOp_eq]
  rfl

variable (a : ℕ → List Req → Req → Option Resp) {rep : Fin (t + 1) → G.W → Option Resp}
  (hrep : ∀ k x w, rep k (G.write k x w) = rep k w) (Good : ℕ → Set (SimRegister G.W I J m t))

/-- **`simLaw_withSteps_eq_instLog` for `G.withPerm b`**: with the hypotheses of
`simLaw_withSteps_eq_instLog` for `G` with the steps after the writes of the replies, writes that
keep the supports both ways (`hWG`), and permutations `b` that keep the supports (`hbG`) and keep
every request (`hbR`), `simLaw` of `G.withPerm b` with the steps after the writes is that of its
instance with logs. The permutations `b` act after the writes, in the order of the run. -/
theorem simLaw_withPerm_withSteps_eq_instLog
    (hreqW : ∀ k x w j, G.req j (G.write k x w) = G.req j w)
    (hA : ∀ (k : Fin (t + 1)) s, s ∈ Good k →
      rep k s.1.1 = a k (requestsBefore (G.hist k s) k) (G.req k s.1.1))
    (hP : ∀ (k : Fin (t + 1)) q, Supported (Good k) q → ∀ l,
      Supported {s | G.hist (k + 1) s = l} (stepSim G k (mask {s | G.hist (k + 1) s = l}
        (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))))
    (h0 : Supported (Good 0) (preQ e G (fun k =>
      (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr (Equiv.refl _))).trans (G.step k)) 0))
    (hG : ∀ (k : Fin (t + 1)) q, (k : ℕ) < t → Supported (Good k) q →
      Supported (Good (k + 1)) (simQuery e G.W t (controlled (fun _ =>
        (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr (Equiv.refl _))).trans (G.step k)) q)))
    (hWG : ∀ (k : Fin (t + 1)) s, s ∈ Good k →
      G.simPerm (G.ctrlWrite k (rep k) (hrep k)) s ∈ Good k ∧
        (G.simPerm (G.ctrlWrite k (rep k) (hrep k))).symm s ∈ Good k)
    (hbG : ∀ (k : Fin (t + 1)) s, s ∈ Good k → (b k).prodCongr (Equiv.refl _) s ∈ Good k)
    (hbR : ∀ k j p, G.req j (b k p).1 = G.req j p.1) :
    simLaw e ((G.withPerm b).withSteps fun k =>
        (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr (Equiv.refl _))).trans
          ((G.withPerm b).step k)) =
      simLaw e ((G.withPerm b).instLog a) := by
  have hgood : ∀ (k : Fin (t + 1)) q, Supported (Good k) q →
      Supported (Good k) (permOp ((b k).prodCongr (Equiv.refl _)) q) := fun k q hq =>
    hq.permOp fun r hr => hbG k r hr
  have hhist : ∀ (k : Fin (t + 1)) j s, G.hist j ((b k).prodCongr (Equiv.refl _) s) = G.hist j s :=
    fun k j s => funext fun i => by
      simp only [hist]
      split_ifs
      · exact congrArg some (hbR k i s.1)
      · rfl
  -- the vector read before the write, whose write is `b` after the write of `q`
  have hpre : ∀ (k : Fin (t + 1)) q, Supported (Good k) q →
      Supported (Good k) (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))).symm
        (permOp ((b k).prodCongr (Equiv.refl _))
          (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))) ∧
      permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k)))
        (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))).symm
          (permOp ((b k).prodCongr (Equiv.refl _))
            (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))) =
        permOp ((b k).prodCongr (Equiv.refl _))
          (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q) := fun k q hq => by
    refine ⟨((hgood k _ (hq.permOp fun r hr => (hWG k r hr).1)).permOp
      fun r hr => (hWG k r hr).2), ?_⟩
    ext r
    simp only [permOp_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  refine simLaw_withSteps_eq_instLog e (G.withPerm b) a _ hrep Good hreqW (fun k q _ => ?_) hA
    (fun k q hq l => ?_) h0 (fun k q hk hq => ?_)
  · change controlled (fun _ => (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr
      (Equiv.refl _))).trans ((G.withPerm b).step k)) q =
        controlled (fun _ => (G.withPerm b).step k) (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q)
    rw [controlled_trans, controlled_permOp_eq]
    rfl
  · rw [stepSim_withPerm]
    change Supported _ (stepSim G k (permOp ((b k).prodCongr (Equiv.refl _))
      (mask {s | G.hist (k + 1) s = l} (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))))
    rw [← mask_permOp_of_inv (fun s => by
      change G.hist (k + 1) ((b k).prodCongr (Equiv.refl _) s) = l ↔ G.hist (k + 1) s = l
      rw [hhist]), ← (hpre k q hq).2]
    exact hP k _ (hpre k q hq).1 l
  · have h : controlled (fun _ =>
        (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr (Equiv.refl _))).trans
          ((G.withPerm b).step k)) q =
        controlled (fun _ =>
          (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr (Equiv.refl _))).trans (G.step k))
          (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))).symm
            (permOp ((b k).prodCongr (Equiv.refl _))
              (permOp (G.simPerm (G.ctrlWrite k (rep k) (hrep k))) q))) := by
      change controlled (fun _ => (permOp ((G.ctrlWrite k (rep k) (hrep k)).prodCongr
        (Equiv.refl _))).trans ((permOp (b k)).trans (G.step k))) q = _
      rw [controlled_trans, controlled_trans, controlled_trans]
      simp only [controlled_permOp_eq]
      congr 1
      exact ((hpre k q hq).2).symm
    rw [h]
    exact hG k _ hk (hpre k q hq).1

end ReqQueryAlg

end GordieHowe.Quantum
