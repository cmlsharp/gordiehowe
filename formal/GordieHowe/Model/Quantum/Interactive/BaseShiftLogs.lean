-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridgeDrop
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeSlots

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg GordieHowe.Quantum.bridgeAlgDrop
  GordieHowe.Quantum.bridgeAlgAdds

/-!
# The logged requests of the bridge with the drops

The drops of the local queries (`bridgeDrop`) keep the absorbed logs, the halting flag and the
ancilla of the bridge's registers, and change the adversary's workspace only on the part of the
local queries. So the supports of the bridge's simulated run carry over to the bridge with the
drops (`bridgeAlgDrop`), and with them the statements on its logged requests.

- `baseDrop_logs`, `baseDrop_work`, `mem_T_of_set`, `slotCohSet_congr_set`, `bridgeDrop_slotWSet`,
  `bridgeDrop_slotInitW`: the drops keep the supports of the bridge's run, for sets `T` that
  writing the part keeps (`hTD`).
- `bridgeAlgDrop_slotLogs`: the slot form (`bridgeAlg_withPerm_slotLogs` at the drops);
  `bridgeAlgDrop_logs`: every logged request of the bridge with the drops is the dummy or an outer
  request of a logged request of the absorbed logs the output reads.
- `addsDrop_keeps`, `slotCohSet_univ_congr`, `slotWSet_univ_congr`, `slotInitW_univ_congr`,
  `bridgeDropAdds_keeps`, `bridgeDropAdds_slotWSet_univ`, `bridgeDropAdds_slotInitW_univ`,
  `bridgeAlgAdds_logs`: the logs statement for the drops of a list of additions
  (`bridgeAlgAdds`); `bridgeAlgDrops_logs`: for any drops that keep the absorbed logs, the halting
  flag and the ancilla (`bridgeAlgDrops`).
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM


variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
  (D : A.BaseW Y₁) (ω : Bits m → Y₁)

omit [Nonempty (Bits m)] in
/-- **The drops keep the absorbed logs** of the composition's register. -/
theorem baseDrop_logs (n : ℕ) (x : QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :
    (baseDrop C₁ F D ω (tab₀ A) n x).1.1.adv.workspace.1.1.logs = x.1.1.adv.workspace.1.1.logs := by
  rcases baseDrop_fst A C₁ F D ω n x with h1 | ⟨v, h1⟩
  · rw [h1]
  · rw [h1]
    rfl

/-! ### The slot form -/

section Slots

variable (T : ℕ → Set ((A.W × Req) × LogReg Req A.slots))

omit [Nonempty (Bits m)] in
/-- **The drops change the adversary's workspace and request register only on the part**, or not
at all. -/
theorem baseDrop_work (n : ℕ) (x : QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :
    ((baseDrop C₁ F D ω (tab₀ A) n x).1.1.adv.workspace.1.1.work,
        (baseDrop C₁ F D ω (tab₀ A) n x).1.1.adv.workspace.1.1.request) =
      (x.1.1.adv.workspace.1.1.work, x.1.1.adv.workspace.1.1.request) ∨
    ∃ v, ((baseDrop C₁ F D ω (tab₀ A) n x).1.1.adv.workspace.1.1.work,
        (baseDrop C₁ F D ω (tab₀ A) n x).1.1.adv.workspace.1.1.request) =
      (D.Lw.set x.1.1.adv.workspace.1.1.work v, x.1.1.adv.workspace.1.1.request) := by
  rcases baseDrop_fst A C₁ F D ω n x with h1 | ⟨v, h1⟩
  · left
    rw [h1]
  · right
    refine ⟨v, ?_⟩
    rw [h1]
    rfl

omit [Nonempty (Bits m)] [AddGroup Y₁] in
variable {T} in
/-- **The workspace, request register and logs stay in `T n` after writing the part**, for sets
that writing the part keeps (`hTD`). -/
theorem mem_T_of_set
    (hTD : ∀ n (x : (A.W × Req) × LogReg Req A.slots) v, x ∈ T n →
      ((D.Lw.set x.1.1 v, x.1.2), x.2) ∈ T n)
    {c c'} (hl : cohLogs A C₁ F d₀ c' = cohLogs A C₁ F d₀ c)
    (hw : cohWork A C₁ F d₀ c' = cohWork A C₁ F d₀ c ∨
      ∃ v, cohWork A C₁ F d₀ c' = (D.Lw.set (cohWork A C₁ F d₀ c).1 v, (cohWork A C₁ F d₀ c).2))
    (n : ℕ) (h : (cohWork A C₁ F d₀ c, cohLogs A C₁ F d₀ c) ∈ T n) :
    (cohWork A C₁ F d₀ c', cohLogs A C₁ F d₀ c') ∈ T n := by
  rw [hl]
  rcases hw with hw | ⟨v, hw⟩
  · rw [hw]
    exact h
  · rw [hw]
    exact hTD n _ v h

omit [Nonempty (Bits m)] [AddGroup Y₁] in
variable {T} in
/-- **`slotCohSet` after writing the part**, for sets `T` that writing the part keeps (`hTD`). -/
theorem slotCohSet_congr_set
    (hTD : ∀ n (x : (A.W × Req) × LogReg Req A.slots) v, x ∈ T n →
      ((D.Lw.set x.1.1 v, x.1.2), x.2) ∈ T n)
    {N : Set (Option (Fin A.slots) × Req₂)} {k : ℕ} {c c'}
    (hc : c ∈ slotCohSet A C₁ F d₀ T N k)
    (hl : cohLogs A C₁ F d₀ c' = cohLogs A C₁ F d₀ c)
    (hw : cohWork A C₁ F d₀ c' = cohWork A C₁ F d₀ c ∨
      ∃ v, cohWork A C₁ F d₀ c' = (D.Lw.set (cohWork A C₁ F d₀ c).1 v, (cohWork A C₁ F d₀ c).2))
    (hf : c'.1.2 = c.1.2) (ha : c'.2 = c.2) :
    c' ∈ slotCohSet A C₁ F d₀ T N k := by
  have hE : ∀ q ∈ N, ∃ j r, q.1 = some j ∧ cohLogs A C₁ F d₀ c' j = some r ∧
      F.outer (A.reqCount (cohLogs A C₁ F d₀ c') j) r = some q.2 := fun q hq => by
    obtain ⟨j, r, h1, h2, h3⟩ := slotCohSet_outer A C₁ F d₀ T hc q hq
    exact ⟨j, r, h1, (congrFun hl j).trans h2,
      (congrArg (fun l => F.outer (A.reqCount l j) r) hl).trans h3⟩
  have hT := mem_T_of_set A C₁ F d₀ D hTD hl hw
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, by rw [hf]; exact h2, by rw [ha]; exact h3⟩
  unfold ReprogrammedCircuit.segOut KindAlg.wsG at h1 ⊢
  split_ifs at h1 ⊢ <;>
    exact ⟨fun j hj => (congrFun hl j).trans (h1.1 j hj), hE, hT _ h1.2.2⟩

/-- **The drops keep the supports `slotWSet` of the bridge's run**, for sets `T` that writing the
part keeps. -/
theorem bridgeDrop_slotWSet
    (hTD : ∀ n (x : (A.W × Req) × LogReg Req A.slots) v, x ∈ T n →
      ((D.Lw.set x.1.1 v, x.1.2), x.2) ∈ T n)
    (N : Set (Option (Fin A.slots) × Req₂)) (n : ℕ) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    (hp : p.1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T N n) :
    (bridgeDrop e A C₁ F d₂ E kq d₀ D ω k p).1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T N n := by
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDrop_apply_lt e A C₁ F d₂ E kq d₀ D ω k h]
    exact slotCohSet_congr_set A C₁ F d₀ D hTD hp (baseDrop_logs A C₁ F D ω k (p.1.1.1.1, p.2))
      (baseDrop_work A C₁ F D ω k (p.1.1.1.1, p.2)) rfl rfl
  · rw [bridgeDrop_apply_ge e A C₁ F d₂ E kq d₀ D ω k h]
    exact hp

/-- **The drops keep the initial supports `slotInitW` of the bridge's run**, for sets `T` that
writing the part keeps. -/
theorem bridgeDrop_slotInitW
    (hTD : ∀ n (x : (A.W × Req) × LogReg Req A.slots) v, x ∈ T n →
      ((D.Lw.set x.1.1 v, x.1.2), x.2) ∈ T n)
    (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    (hp : p.1 ∈ slotInitW e A C₁ F d₂ E kq d₀ T) :
    (bridgeDrop e A C₁ F d₂ E kq d₀ D ω k p).1 ∈ slotInitW e A C₁ F d₂ E kq d₀ T := by
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDrop_apply_lt e A C₁ F d₂ E kq d₀ D ω k h]
    have hlog := baseDrop_logs A C₁ F D ω k (p.1.1.1.1, p.2)
    obtain ⟨hb, hT0, h2, h3⟩ := (mem_slotCohInit A C₁ F d₀ (T := T) (c := p.1.1)).1 hp
    refine (mem_slotCohInit A C₁ F d₀ (T := T)).2 ⟨fun j => (congrFun hlog j).trans (hb j), ?_,
      h2, h3⟩
    exact mem_T_of_set A C₁ F d₀ D hTD hlog (baseDrop_work A C₁ F D ω k (p.1.1.1.1, p.2)) 0 hT0
  · rw [bridgeDrop_apply_ge e A C₁ F d₂ E kq d₀ D ω k h]
    exact hp

/-- **The slot form of the requests of the bridge with the drops** (`bridgeAlg_slotLogs`): for a
trace-preserving adversary, sets `T` carried by its steps (`hT`) that writing the part keeps
(`hTD`), and every reply family `a`, on every basis state of the compressed-oracle simulation of
the instance of the bridge with the drops, the workspace and the absorbed logs that the output
reads lie in `T (slots + post + 1)`, and every logged request is the dummy `d₂` or the outer
request of the output's log of the slot that its request point answers. -/
theorem bridgeAlgDrop_slotLogs (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (hTD : ∀ n (x : (A.W × Req) × LogReg Req A.slots) v, x ∈ T n →
      ((D.Lw.set x.1.1 v, x.1.2), x.2) ∈ T n)
    (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).inst a).W I J m (bT A C₁ F kq)}
    (hb : simState e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).inst a) b ≠ 0) :
    ((((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.work,
        ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.request),
        ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.logs) ∈
          T (A.slots + A.post + 1) ∧
      ∀ i q, b.1.1.2 i = some q → q = d₂ ∨ ∃ j r, answerSlot A C₁ i = some j ∧
        ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
        F.outer (A.reqCount
          ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.logs j) r =
          some q :=
  bridgeAlg_withPerm_slotLogs e A C₁ F d₂ E kq d₀ (bridgeDrop e A C₁ F d₂ E kq d₀ D ω)
    (fun r hr => bridgeDrop_slotInitW e A C₁ F d₂ E kq d₀ D ω T hTD _ r hr)
    (fun N k _ r hr => bridgeDrop_slotWSet e A C₁ F d₂ E kq d₀ D ω T hTD N k _ r hr) hA hT a hb

omit [Nonempty (Bits m)] in
/-- **The drops of additions keep the absorbed logs, the halting flag and the ancilla.** -/
theorem addsDrop_keeps (P : A.AddsW Y₁) (n : ℕ)
    (x : QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :
    (addsDrop C₁ F ω P (tab₀ A) n x).1.1.adv.workspace.1.1.logs =
      x.1.1.adv.workspace.1.1.logs ∧ (addsDrop C₁ F ω P (tab₀ A) n x).1.2 = x.1.2 ∧
      (addsDrop C₁ F ω P (tab₀ A) n x).2 = x.2 :=
  addsDrop_induct C₁ F ω P (tab₀ A) n (fun y => y.1.1.adv.workspace.1.1.logs =
      x.1.1.adv.workspace.1.1.logs ∧ y.1.2 = x.1.2 ∧ y.2 = x.2) (fun _ _ h => h) x
    ⟨rfl, rfl, rfl⟩

omit [Nonempty (Bits m)] [AddGroup Y₁] in
/-- **`slotCohSet` at the full sets** reads only the absorbed logs, the halting flag and the
ancilla. -/
theorem slotCohSet_univ_congr {N : Set (Option (Fin A.slots) × Req₂)} {k : ℕ} {c c'}
    (hc : c ∈ slotCohSet A C₁ F d₀ (fun _ => Set.univ) N k)
    (hl : cohLogs A C₁ F d₀ c' = cohLogs A C₁ F d₀ c) (hf : c'.1.2 = c.1.2) (ha : c'.2 = c.2) :
    c' ∈ slotCohSet A C₁ F d₀ (fun _ => Set.univ) N k := by
  have hE : ∀ q ∈ N, ∃ j r, q.1 = some j ∧ cohLogs A C₁ F d₀ c' j = some r ∧
      F.outer (A.reqCount (cohLogs A C₁ F d₀ c') j) r = some q.2 := fun q hq => by
    obtain ⟨j, r, h1, h2, h3⟩ := slotCohSet_outer A C₁ F d₀ (fun _ => Set.univ) hc q hq
    exact ⟨j, r, h1, (congrFun hl j).trans h2,
      (congrArg (fun l => F.outer (A.reqCount l j) r) hl).trans h3⟩
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, by rw [hf]; exact h2, by rw [ha]; exact h3⟩
  unfold ReprogrammedCircuit.segOut KindAlg.wsG at h1 ⊢
  split_ifs at h1 ⊢ <;>
    exact ⟨fun j hj => (congrFun hl j).trans (h1.1 j hj), hE, trivial⟩

omit [Nonempty (Bits m)] [AddGroup Y₁] in
/-- **`slotWSet` at the full sets** reads only the absorbed logs, the halting flag and the
ancilla. -/
theorem slotWSet_univ_congr {N : Set (Option (Fin A.slots) × Req₂)} {k : ℕ}
    {w w' : (bridgeAlg e A C₁ F d₂ E kq d₀).W}
    (hw : w ∈ slotWSet e A C₁ F d₂ E kq d₀ (fun _ => Set.univ) N k)
    (hl : cohLogs A C₁ F d₀ w'.1 = cohLogs A C₁ F d₀ w.1) (hf : w'.1.1.2 = w.1.1.2)
    (ha : w'.1.2 = w.1.2) : w' ∈ slotWSet e A C₁ F d₂ E kq d₀ (fun _ => Set.univ) N k :=
  slotCohSet_univ_congr A C₁ F d₀ (c := w.1) hw hl hf ha

/-- **The drops of additions on the bridge's registers keep the absorbed logs, the halting flag
and the ancilla.** -/
theorem bridgeDropAdds_keeps (P : A.AddsW Y₁) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    cohLogs A C₁ F d₀ (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1.1 =
        cohLogs A C₁ F d₀ p.1.1 ∧
      (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1.1.1.2 = p.1.1.1.2 ∧
      (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1.1.2 = p.1.1.2 := by
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ P ω k h]
    exact ⟨(addsDrop_keeps A C₁ F ω P k (p.1.1.1.1, p.2)).1, rfl, rfl⟩
  · rw [bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ P ω k h]
    exact ⟨rfl, rfl, rfl⟩

omit [AddGroup Y₁] in
/-- **`slotInitW` at the full sets** reads only the absorbed logs, the halting flag and the
ancilla. -/
theorem slotInitW_univ_congr {w w' : (bridgeAlg e A C₁ F d₂ E kq d₀).W}
    (hw : w ∈ slotInitW e A C₁ F d₂ E kq d₀ (fun _ => Set.univ))
    (hl : cohLogs A C₁ F d₀ w'.1 = cohLogs A C₁ F d₀ w.1) (hf : w'.1.1.2 = w.1.1.2)
    (ha : w'.1.2 = w.1.2) : w' ∈ slotInitW e A C₁ F d₂ E kq d₀ (fun _ => Set.univ) := by
  obtain ⟨hb, -, h2, h3⟩ := (mem_slotCohInit A C₁ F d₀ (T := fun _ => Set.univ) (c := w.1)).1 hw
  refine (mem_slotCohInit A C₁ F d₀ (T := fun _ => Set.univ) (c := w'.1)).2
    ⟨fun j => (congrFun hl j).trans (hb j), trivial, hf.trans h2, ?_⟩
  rw [ha]
  exact h3

/-- **The drops of additions keep the supports `slotWSet` of the bridge's run** at the full
sets. -/
theorem bridgeDropAdds_slotWSet_univ (P : A.AddsW Y₁) (N : Set (Option (Fin A.slots) × Req₂))
    (n : ℕ) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    (hp : p.1 ∈ slotWSet e A C₁ F d₂ E kq d₀ (fun _ => Set.univ) N n) :
    (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1 ∈
      slotWSet e A C₁ F d₂ E kq d₀ (fun _ => Set.univ) N n :=
  by
  have h1 := slotWSet_univ_congr e A C₁ F d₂ E kq d₀ (N := N) (k := n) (w := p.1)
    (w' := (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1) hp
  have hk := bridgeDropAdds_keeps e A C₁ F d₂ E kq d₀ ω P k p
  exact h1 hk.1 hk.2.1 hk.2.2

/-- **The drops of additions keep the initial supports `slotInitW` of the bridge's run** at the
full sets. -/
theorem bridgeDropAdds_slotInitW_univ (P : A.AddsW Y₁) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    (hp : p.1 ∈ slotInitW e A C₁ F d₂ E kq d₀ (fun _ => Set.univ)) :
    (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1 ∈
      slotInitW e A C₁ F d₂ E kq d₀ (fun _ => Set.univ) :=
  slotInitW_univ_congr e A C₁ F d₂ E kq d₀ hp
    (bridgeDropAdds_keeps e A C₁ F d₂ E kq d₀ ω P k p).1
    (bridgeDropAdds_keeps e A C₁ F d₂ E kq d₀ ω P k p).2.1
    (bridgeDropAdds_keeps e A C₁ F d₂ E kq d₀ ω P k p).2.2

/-- **The logs statement for the bridge with the drops of additions** (`bridgeAlg_logs`): on
every basis state of nonzero amplitude of the compressed-oracle simulation of its instance with
the replies `a`, every logged request is the dummy `d₂` or the outer request of a request in the
absorbed copy of the logs that the output reads, for a trace-preserving adversary. -/
theorem bridgeAlgAdds_logs (P : A.AddsW Y₁) (hA : A.TracePreserving)
    (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).inst a).W I J m (bT A C₁ F kq)}
    (hb : simState e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).inst a) b ≠ 0)
    {i : Fin (bT A C₁ F kq + 1)} {q : Req₂} (hq : b.1.1.2 i = some q) :
    q = d₂ ∨ ∃ j r,
      ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
      F.outer (A.reqCount
        ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).out b.1.1.1).out.adv.1.1.1.logs j) r =
        some q := by
  have hs := bridgeAlg_withPerm_slotLogs e A C₁ F d₂ E kq d₀
    (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω)
    (fun r hr => bridgeDropAdds_slotInitW_univ e A C₁ F d₂ E kq d₀ ω P _ r hr)
    (fun N k _ r hr => bridgeDropAdds_slotWSet_univ e A C₁ F d₂ E kq d₀ ω P N k _ r hr)
    hA (AdaptiveIAlg.LogInv.univ A F (tab₀ A)) a hb
  rcases hs.2 i q hq with h | ⟨j, r, -, hr, hq'⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, r, hr, hq'⟩

/-- **The logs statement for the bridge with any drops** (`bridgeAlg_logs`): for drops `β` of the
composition's registers that keep the absorbed logs, the halting flag and the ancilla (`hβ`), on
every basis state of nonzero amplitude of the compressed-oracle simulation of the instance with
the replies `a` of the bridge read after `β` (`bridgeAlgDrops`), every logged request is the dummy
`d₂` or the outer request of a request in the absorbed copy of the logs that the output reads, for
a trace-preserving adversary. -/
theorem bridgeAlgDrops_logs
    (β : ℕ → Equiv.Perm (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁)
      (Bits m) (BitStr I J)))
    (hβ : ∀ n x, (β n x).1.1.adv.workspace.1.1.logs = x.1.1.adv.workspace.1.1.logs ∧
      (β n x).1.2 = x.1.2 ∧ (β n x).2 = x.2)
    (hA : A.TracePreserving) (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).inst a).W I J m (bT A C₁ F kq)}
    (hb : simState e ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).inst a) b ≠ 0)
    {i : Fin (bT A C₁ F kq + 1)} {q : Req₂} (hq : b.1.1.2 i = some q) :
    q = d₂ ∨ ∃ j r,
      ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
      F.outer (A.reqCount
        ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).out b.1.1.1).out.adv.1.1.1.logs j) r =
        some q := by
  have hk : ∀ (k : Fin (bT A C₁ F kq + 1))
      (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)),
      cohLogs A C₁ F d₀ (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p).1.1 =
          cohLogs A C₁ F d₀ p.1.1 ∧
        (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p).1.1.1.2 = p.1.1.1.2 ∧
        (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p).1.1.2 = p.1.1.2 := fun k p => by
    by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
    · rw [bridgeDropPerms_apply_lt e A C₁ F d₂ E kq d₀ β k h]
      exact ⟨(hβ k (p.1.1.1.1, p.2)).1, rfl, rfl⟩
    · rw [bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ β k h]
      exact ⟨rfl, rfl, rfl⟩
  have hs := bridgeAlg_withPerm_slotLogs e A C₁ F d₂ E kq d₀
    (bridgeDropPerms e A C₁ F d₂ E kq d₀ β)
    (fun r hr => slotInitW_univ_congr e A C₁ F d₂ E kq d₀ hr (hk _ r).1 (hk _ r).2.1 (hk _ r).2.2)
    (fun N k _ r hr => slotWSet_univ_congr e A C₁ F d₂ E kq d₀ hr (hk _ r).1 (hk _ r).2.1
      (hk _ r).2.2)
    hA (AdaptiveIAlg.LogInv.univ A F (tab₀ A)) a hb
  rcases hs.2 i q hq with h | ⟨j, r, -, hr, hq'⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, r, hr, hq'⟩

/-- **The logs statement for the bridge with the drops** (`bridgeAlg_logs`): on every basis state
of nonzero amplitude of the compressed-oracle simulation of its instance with the replies `a`,
every logged request is the dummy `d₂` or the outer request of a request in the absorbed copy of
the logs that the output reads, for a trace-preserving adversary. -/
theorem bridgeAlgDrop_logs (hA : A.TracePreserving) (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).inst a).W I J m (bT A C₁ F kq)}
    (hb : simState e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).inst a) b ≠ 0)
    {i : Fin (bT A C₁ F kq + 1)} {q : Req₂} (hq : b.1.1.2 i = some q) :
    q = d₂ ∨ ∃ j r,
      ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
      F.outer (A.reqCount
        ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1).out.adv.1.1.1.logs j) r =
        some q := by
  rcases (bridgeAlgDrop_slotLogs e A C₁ F d₂ E kq d₀ D ω (fun _ => Set.univ) hA
    (AdaptiveIAlg.LogInv.univ A F (tab₀ A)) (fun _ _ _ _ => trivial) a hb).2 i q hq with
    h | ⟨j, r, -, hr, hq'⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, r, hr, hq'⟩

end Slots

end GordieHowe.Quantum
