-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ComposeBlock
public import GordieHowe.Model.Quantum.Interactive.AbsorbTabBlock
public import GordieHowe.Model.Quantum.Interactive.SimChallenger

@[expose] public section

/-!
# The composition with a challenger along a witness swap of the logs

A challenger that does not see a permutation `σ₁` of its requests (`Challenger.SwapInv`: its reply
programs agree on histories and requests related entrywise by `σ₁` or the identity) reads the same
states from logs whose entries are permuted by `σ₁` or the identity (`regStateOf_logFam`), so its
query inputs, assignments and replies in the composition do not see such a permutation of the logs
(`KindAlg.chalInput_chalSw` and the like); the simulation challenger does not see a swap its
simulator does not see (`QROM.simExtChallenger_swapInv`).

- `KindAlg.cwPerm`: the swap of the composed registers, a permutation of the adversary's
  workspace, request and response with the log of the slot recorded by `Jc` swapped by `σ₁`;
  `KindAlg.cwSet`: the composed registers well-formed at an index (the logs blank after it).
- `KindAlg.SwapHyps`: the hypotheses on the adversary's registers (the block hypotheses of each
  step along the permutations `σ`, the recorded slot set only at its step, the request swapped by
  `σ₁` exactly at the recorded slot, the requests away from it fixed by `σ₁` on the block).
- `KindAlg.twin_fullCircBoth_cw`, `KindAlg.composeBothOut_block_cw`: the composition with a
  challenger that does not see `σ₁`, against the composition with other Kraus maps, satisfies
  `Alg.BlockNone` and `Alg.BlockRel` along the swap, the request measurement's outcomes relabelled
  by `σ₁`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-- **Two requests related by `σ₁`**: equal, or the second is `σ₁` of the first. -/
def SwRel {Req : Type} (σ₁ : Equiv.Perm Req) (a b : Req) : Prop := b = a ∨ b = σ₁ a

/-- Two history entries with requests related by `σ₁` and the same response. -/
def HistSw {Req Resp : Type} (σ₁ : Equiv.Perm Req) (e e' : HistoryEntry Req Resp) : Prop :=
  SwRel σ₁ e.request e'.request ∧ e'.response = e.response

/-- **The swap of the log at the recorded slot, before and after a step that may set the slot to
`k`**, on logs blank from slot `k` on. -/
theorem logFam_swIf_eq_of_blank {Req : Type} {m : ℕ} (σ₁ : Equiv.Perm Req) {k : ℕ}
    {jx jy : Option ℕ} (hj : jx = jy ∨ (jy = none ∧ jx = some k)) (lg : LogReg Req m)
    (hl : ∀ i : Fin m, k ≤ i → lg i = none) :
    logFam (fun i : Fin m => swIf (jx = some (i : ℕ)) σ₁) lg =
      logFam (fun i : Fin m => swIf (jy = some (i : ℕ)) σ₁) lg := by
  rcases hj with rfl | ⟨rfl, rfl⟩
  · rfl
  funext i
  rw [logFam_apply, logFam_apply]
  by_cases hi : (i : ℕ) = k
  · rw [hl i hi.ge]
    rfl
  · rw [swIf_congr (p := some k = some (i : ℕ)) (p' := False) σ₁ (by simp [Ne.symm hi]),
      swIf_congr (p := none = some (i : ℕ)) (p' := False) σ₁ (by simp)]

namespace Challenger

variable {X Y Req Resp : Type}

/-- **A challenger that does not see `σ₁`**: its reply programs agree on histories related
entrywise by `HistSw σ₁` and requests related by `σ₁`. -/
def SwapInv (C : Challenger X Y Req Resp) (σ₁ : Equiv.Perm Req) : Prop :=
  ∀ ω hist hist' r r', List.Forall₂ (HistSw σ₁) hist hist' → SwRel σ₁ r r' →
    C.respond ω hist r = C.respond ω hist' r'

/-- **A permutation of each log entry by `σ₁` or the identity.** -/
def SwFam {Req : Type} {m : ℕ} (σ₁ : Equiv.Perm Req) (e : Fin m → Equiv.Perm Req) : Prop :=
  ∀ i, e i = Equiv.refl Req ∨ e i = σ₁

theorem SwFam.swRel {Req : Type} {m : ℕ} {σ₁ : Equiv.Perm Req} {e : Fin m → Equiv.Perm Req}
    (h : SwFam σ₁ e) (i : Fin m) (r : Req) : SwRel σ₁ r (e i r) := by
  rcases h i with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]

/-- **The state read from logs permuted entrywise by `σ₁` or the identity**: histories related by
`HistSw σ₁` and the same assignments, for reply programs that do not see `σ₁`. -/
theorem regStateOf_logFam {Coins : Type} (Q : ℕ)
    (respond : Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Reply X Y Resp))
    {σ₁ : Equiv.Perm Req}
    (hC : ∀ ω hist hist' r r', List.Forall₂ (HistSw σ₁) hist hist' → SwRel σ₁ r r' →
      respond ω hist r = respond ω hist' r')
    {m : ℕ} {e : Fin m → Equiv.Perm Req} (he : SwFam σ₁ e) (ω : Coins) (lg : LogReg Req m)
    (ans : Fin m → List Y) :
    ∀ j, List.Forall₂ (HistSw σ₁) (regStateOf Q respond ω lg ans j).history
        (regStateOf Q respond ω (logFam e lg) ans j).history ∧
      (regStateOf Q respond ω (logFam e lg) ans j).assignments =
        (regStateOf Q respond ω lg ans j).assignments
  | 0 => ⟨List.Forall₂.nil, rfl⟩
  | j + 1 => by
    obtain ⟨ih1, ih2⟩ := regStateOf_logFam Q respond hC he ω lg ans j
    by_cases hj : j < m
    · simp only [regStateOf, dif_pos hj, logFam_apply]
      rcases lg ⟨j, hj⟩ with _ | r
      · exact ⟨ih1, ih2⟩
      · have hlen := ih1.length_eq
        have ho : outWithOf respond ω (regStateOf Q respond ω (logFam e lg) ans j).history
            (e ⟨j, hj⟩ r) (ans ⟨j, hj⟩) =
            outWithOf respond ω (regStateOf Q respond ω lg ans j).history r (ans ⟨j, hj⟩) := by
          unfold outWithOf
          rw [hC ω _ _ r (e ⟨j, hj⟩ r) ih1 (he.swRel _ r)]
        simp only [Option.map_some, ← hlen, ho]
        split_ifs
        · exact ⟨List.rel_append ih1 (List.Forall₂.cons ⟨he.swRel _ r, rfl⟩ List.Forall₂.nil),
            by rw [ih2]⟩
        · exact ⟨ih1, ih2⟩
    · simp only [regStateOf, dif_neg hj]
      exact ⟨ih1, ih2⟩

end Challenger

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (C : Challenger X Y Req Resp)

/-- The challenger's registers with the logs permuted entrywise by `e`. -/
def chalSw (e : Fin B.slots → Equiv.Perm Req) (u : B.CCl C) : B.CCl C :=
  { u with logs := logFam e u.logs }

variable {B C} {σ₁ : Equiv.Perm Req} (hC : C.SwapInv σ₁) {e : Fin B.slots → Equiv.Perm Req}
  (he : Challenger.SwFam σ₁ e)

include hC he

theorem stateAt_chalSw (u : B.CCl C) (j : ℕ) :
    List.Forall₂ (HistSw σ₁) (B.stateAt C u j).history (B.stateAt C (B.chalSw C e u) j).history ∧
      (B.stateAt C (B.chalSw C e u) j).assignments = (B.stateAt C u j).assignments :=
  Challenger.regStateOf_logFam C.Q C.respond hC he u.coins u.logs _ j

theorem chalInput_chalSw [Nonempty X] [AddGroup Y] (j : Fin B.slots) (i : Fin C.q)
    (u : B.CCl C) : B.chalInput C j i (B.chalSw C e u) = B.chalInput C j i u := by
  obtain ⟨h1, -⟩ := stateAt_chalSw hC he u j
  unfold chalInput
  change (match (u.logs j).map (e j) with
    | none => x₀
    | some r => if (B.stateAt C (B.chalSw C e u) j).history.length < C.Q then
        (C.respond u.coins (B.stateAt C (B.chalSw C e u) j).history r).next x₀
          ((B.ansOf C u j).take i) else x₀) = _
  rcases u.logs j with _ | r
  · rfl
  · simp only [Option.map_some, ← h1.length_eq]
    rw [← hC u.coins _ _ r (e j r) h1 (he.swRel j r)]

theorem chalAss_chalSw [Nonempty X] [AddGroup Y] (j : Fin B.slots) (i : Fin C.q)
    (u : B.CCl C) : B.chalAss C j i (B.chalSw C e u) = B.chalAss C j i u := by
  obtain ⟨h1, h2⟩ := stateAt_chalSw hC he u j
  unfold chalAss
  change (match (u.logs j).map (e j) with
    | none => paddingAssignments X Y
    | some r => if (B.stateAt C (B.chalSw C e u) j).history.length < C.Q ∧
        OracleProgAns.wants (C.respond u.coins (B.stateAt C (B.chalSw C e u) j).history r)
          ((B.ansOf C u j).take i)
      then (B.stateAt C (B.chalSw C e u) j).assignments else paddingAssignments X Y) = _
  rcases u.logs j with _ | r
  · rfl
  · simp only [Option.map_some, ← h1.length_eq, h2]
    rw [← hC u.coins _ _ r (e j r) h1 (he.swRel j r)]

theorem reply_chalSw (j : Fin B.slots) (u : B.CCl C) :
    B.reply C j (B.chalSw C e u) = B.reply C j u := by
  obtain ⟨h1, -⟩ := stateAt_chalSw hC he u j
  unfold reply
  change (match (u.logs j).map (e j) with
    | none => none
    | some r => if (B.stateAt C (B.chalSw C e u) j).history.length < C.Q then
        (C.outWith u.coins (B.stateAt C (B.chalSw C e u) j).history r (B.ansOf C u j)).response
      else none) = _
  rcases u.logs j with _ | r
  · rfl
  · simp only [Option.map_some, ← h1.length_eq]
    unfold Challenger.outWith Challenger.outWithOf
    rw [← hC u.coins _ _ r (e j r) h1 (he.swRel j r)]

theorem advAss_chalSw [Nonempty X] [AddGroup Y] (j : Fin B.slots) (u : B.CCl C) :
    B.advAss C j (B.chalSw C e u) = B.advAss C j u := by
  obtain ⟨-, h2⟩ := stateAt_chalSw hC he u (j + 1)
  unfold advAss
  change (match (u.logs j).map (e j) with
    | none => (B.stateAt C (B.chalSw C e u) (j + 1)).assignments
    | some _ => paddingAssignments X Y) = _
  rcases u.logs j with _ | r
  · exact h2
  · rfl

theorem postAss_chalSw (u : B.CCl C) : B.postAss C (B.chalSw C e u) = B.postAss C u :=
  (stateAt_chalSw hC he u B.slots).2

omit hC he

variable (B C σ₁) in
/-- The witness swap of the logs at the slot recorded `jw`: `σ₁` on log `i` when `jw = some i`. -/
abbrev slotSw (jw : Option ℕ) : Fin B.slots → Equiv.Perm Req :=
  fun i => swIf (jw = some (i : ℕ)) σ₁

theorem swFam_slotSw (jw : Option ℕ) : Challenger.SwFam σ₁ (slotSw B σ₁ jw) := fun i => by
  unfold slotSw swIf
  split_ifs
  · right; rfl
  · left; rfl

variable (B C σ₁) in
/-- **The witness swap of the composed registers** at the permutation `σn` of the adversary's
workspace, request and response: `σn` on those, the logs by `slotSw` at the slot `Jc` reads in the
adversary's workspace. -/
def cwPerm (Jc : B.W → Option ℕ) (σn : Equiv.Perm (B.W × Req × Option Resp)) :
    Equiv.Perm (B.CW C) where
  toFun v := ⟨(σn v.adv.1, v.adv.2), B.chalSw C (slotSw B σ₁ (Jc v.adv.1.1)) v.chal⟩
  invFun v := ⟨(σn.symm v.adv.1, v.adv.2),
    { v.chal with logs := (logFam (slotSw B σ₁ (Jc (σn.symm v.adv.1).1))).symm v.chal.logs }⟩
  left_inv v := by
    obtain ⟨⟨x, p⟩, ⟨lg, qs, ω⟩⟩ := v
    simp [chalSw]
  right_inv v := by
    obtain ⟨⟨x, p⟩, ⟨lg, qs, ω⟩⟩ := v
    simp [chalSw]

theorem cwPerm_apply (Jc : B.W → Option ℕ) (σn : Equiv.Perm (B.W × Req × Option Resp))
    (v : B.CW C) : cwPerm B C σ₁ Jc σn v =
      ⟨(σn v.adv.1, v.adv.2), B.chalSw C (slotSw B σ₁ (Jc v.adv.1.1)) v.chal⟩ :=
  rfl

section Gates

variable {Jc : B.W → Option ℕ} {σn : Equiv.Perm (B.W × Req × Option Resp)}

include hC in
theorem prepChal_cwPerm [Nonempty X] [AddGroup Y] (j : Fin B.slots) (i : Fin C.q)
    (p : QueryReg (B.CW C) 1 X Y) :
    B.prepChal C j i (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) =
      WorkRel.wq (cwPerm B C σ₁ Jc σn) (B.prepChal C j i p) := by
  change ((cwPerm B C σ₁ Jc σn p.1, fun _ => (Equiv.swap x₀
      (B.chalInput C j i (B.chalSw C (slotSw B σ₁ (Jc p.1.adv.1.1)) p.1.chal)) (p.2 0).1,
      (p.2 0).2)) : QueryReg (B.CW C) 1 X Y) = (cwPerm B C σ₁ Jc σn p.1, _)
  rw [chalInput_chalSw hC (swFam_slotSw _)]
  rfl

theorem garSwap_cwPerm [Nonempty X] [AddGroup Y] (j : Fin B.slots) (i : Fin C.q)
    (p : QueryReg (B.CW C) 1 X Y) :
    B.garSwap C j i (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) =
      WorkRel.wq (cwPerm B C σ₁ Jc σn) (B.garSwap C j i p) :=
  rfl

theorem advSwap_cwPerm (k : Fin B.width) (p : QueryReg (B.CW C) 1 X Y) :
    B.advSwap C k (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) =
      WorkRel.wq (cwPerm B C σ₁ Jc σn) (B.advSwap C k p) :=
  rfl

include hC in
theorem writeReply_cwPerm
    (hσa : ∀ w q a a', σn (w, q, a') = ((σn (w, q, a)).1, (σn (w, q, a)).2.1, a'))
    (j : Fin B.slots) (p : QueryReg (B.CW C) 1 X Y) :
    B.writeReply C j (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) =
      WorkRel.wq (cwPerm B C σ₁ Jc σn) (B.writeReply C j p) := by
  obtain ⟨⟨⟨⟨w, q, a⟩, qs⟩, u⟩, x⟩ := p
  have hs : ((B.chalSw C (slotSw B σ₁ (Jc w)) u).logs j).isSome = (u.logs j).isSome := by
    change ((u.logs j).map _).isSome = _
    cases u.logs j <;> rfl
  unfold writeReply
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, WorkRel.wq, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id, cwPerm_apply]
  change (if ((B.chalSw C (slotSw B σ₁ (Jc w)) u).logs j).isSome then _ else _) = _
  rw [hs, reply_chalSw hC (swFam_slotSw _)]
  split_ifs
  · have h3 : (σn (w, q, a)).2.2 = a := congrArg (fun z => z.2.2) (hσa w q a a)
    simp only [DReg.workspace, DReg.request, DReg.response]
    rw [h3, hσa w q a (Equiv.swap none (B.reply C j u) a)]
  · rfl

theorem copyReq_cwPerm (j : Fin B.slots) (hk : ∀ x, B.kind (σn x).1 = B.kind x.1)
    (hq : ∀ x, (σn x).2.1 = swIf (Jc x.1 = some (j : ℕ)) σ₁ x.2.1)
    (p : QueryReg (B.CW C) 1 X Y) :
    B.copyReq C j (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) =
      WorkRel.wq (cwPerm B C σ₁ Jc σn) (B.copyReq C j p) := by
  obtain ⟨⟨⟨x, qs⟩, u⟩, y⟩ := p
  unfold copyReq
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, WorkRel.wq, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id, cwPerm_apply]
  change (if B.kind (σn x).1 then _ else _) = _
  rw [hk]
  split_ifs
  · change ((⟨((σn x), qs), (B.chalSw C (slotSw B σ₁ (Jc x.1)) u).swapLog j (σn x).2.1⟩ :
      B.CW C), y) = (⟨((σn x), qs), B.chalSw C (slotSw B σ₁ (Jc x.1)) (u.swapLog j x.2.1)⟩, y)
    congr 2
    simp only [ChallengerRegs.swapLog, chalSw]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, logFam_apply, hq]
      exact swap_apply_perm (Equiv.optionCongr (swIf (Jc x.1 = some (i : ℕ)) σ₁)) none
        (some x.2.1) (u.logs i)
    · simp only [Function.update_of_ne hi, logFam_apply]
  · rfl

end Gates

/-! ### The states along the swap -/

section States

open AdaptiveIAlg (idxSet AfterIdx prevIdx)

variable (B C σ₁) in
/-- **The composed registers well-formed at an index**: the adversary's workspace, request and
response in the set of the index, the logs blank after it. -/
def cwSet (G : ℕ → Set (B.W × Req × Option Resp)) (G₀ : Set (B.W × Req × Option Resp))
    (idx : Option ℕ) : Set (B.CW C) :=
  {v | v.adv.1 ∈ idxSet G G₀ idx ∧ ∀ i : Fin B.slots, AfterIdx idx i → v.chal.logs i = none}

/-- The permutation of the adversary's registers at an index. -/
def idxPerm {T : Type*} (σ : ℕ → Equiv.Perm T) (σ₀ : Equiv.Perm T) : Option ℕ → Equiv.Perm T
  | none => σ₀
  | some n => σ n

variable {L : Type} {ℓB : B.W → Option L} {r : L} {Jc : B.W → Option ℕ}
  {σ : ℕ → Equiv.Perm (B.W × Req × Option Resp)} {σ₀ : Equiv.Perm (B.W × Req × Option Resp)}
  {G G' : ℕ → Set (B.W × Req × Option Resp)} {G₀ G₀' : Set (B.W × Req × Option Resp)}

theorem logFam_slotSw_eq_none (jw : Option ℕ) (lg : LogReg Req B.slots) (i : Fin B.slots) :
    logFam (slotSw B σ₁ jw) lg i = none ↔ lg i = none := by
  rw [logFam_apply]
  cases lg i <;> simp

/-- **The states along the swap are states of twin circuits**, from the block hypotheses on the
sets and permutations of the adversary's registers. -/
theorem twinState_cwSet [DecidableEq L]
    (hNE : ∀ idx x, ℓB x.1 = none → (x ∈ idxSet G' G₀' idx ↔ x ∈ idxSet G G₀ idx))
    (hSE : ∀ idx x, InBlock ℓB r x.1 →
      (idxPerm σ σ₀ idx x ∈ idxSet G' G₀' idx ↔ x ∈ idxSet G G₀ idx))
    (hLE : ∀ idx x, ℓB (idxPerm σ σ₀ idx x).1 = ℓB x.1) (idx : Option ℕ) :
    ReprogrammedCircuit.TwinState (fun v : B.CW C => ℓB v.adv.1.1) r (B.cwSet C G G₀ idx)
      (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc (idxPerm σ σ₀ idx)) where
  none_eq v hv := and_congr (hNE idx v.adv.1 hv) Iff.rfl
  set_eq v hv := and_congr (hSE idx v.adv.1 hv) (forall_congr' fun i => imp_congr_right fun _ =>
    logFam_slotSw_eq_none _ _ i)
  label_eq v := hLE idx v.adv.1

theorem setIso_ofPerm_cw {π : Equiv.Perm (QueryReg (B.CW C) 1 X Y)}
    (h1 : ∀ q, (π q).1.adv.1 = q.1.adv.1) (h2 : ∀ q, (π q).1.chal.logs = q.1.chal.logs)
    (G : ℕ → Set (B.W × Req × Option Resp)) (G₀ : Set (B.W × Req × Option Resp))
    (idx : Option ℕ) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.cwSet C G G₀ idx} (KrausMap.ofPerm π) :=
  SetIso.ofPerm fun q => by
    change ((π q).1.adv.1 ∈ _ ∧ ∀ i, _ → (π q).1.chal.logs i = none) ↔ (q.1.adv.1 ∈ _ ∧ _)
    rw [h1, h2]

theorem setIso_writeReply_cw (j : Fin B.slots) (G : ℕ → Set (B.W × Req × Option Resp))
    (G₀ : Set (B.W × Req × Option Resp)) (idx : Option ℕ)
    (hG : ∀ w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.cwSet C G G₀ idx}
      (KrausMap.ofPerm (B.writeReply C j)) :=
  SetIso.ofPerm fun q => by
    change ((if (q.1.chal.logs j).isSome then _ else q).1.adv.1 ∈ _ ∧
      ∀ i, _ → (if (q.1.chal.logs j).isSome then _ else q).1.chal.logs i = none) ↔ _
    split_ifs
    · exact and_congr ⟨hG _ _ _ _, hG _ _ _ _⟩ Iff.rfl
    · exact Iff.rfl

theorem setIso_copyReq_cw (j : Fin B.slots) (G : ℕ → Set (B.W × Req × Option Resp))
    (G₀ : Set (B.W × Req × Option Resp)) (idx : Option ℕ) (hj : ¬ AfterIdx idx j) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.cwSet C G G₀ idx}
      (KrausMap.ofPerm (B.copyReq C j)) :=
  SetIso.ofPerm fun q => by
    change ((if B.kind q.1.adv.workspace then _ else q).1.adv.1 ∈ _ ∧
      ∀ i, _ → (if B.kind q.1.adv.workspace then _ else q).1.chal.logs i = none) ↔ _
    split_ifs
    · refine and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun hi => ?_)
      change Function.update q.1.chal.logs j _ i = none ↔ _
      rw [Function.update_of_ne (fun e => hj (by rw [← e]; exact hi))]
    · exact Iff.rfl

theorem setIso_measReq_cw (j : Fin B.slots) (G : ℕ → Set (B.W × Req × Option Resp))
    (G₀ : Set (B.W × Req × Option Resp)) (idx : Option ℕ) (hj : ¬ AfterIdx idx j) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.cwSet C G G₀ idx} (B.measReq C j) :=
  (setIso_copyReq_cw j G G₀ idx hj).comp (SetIso.measureFn _ _)

end States

section Hyps

open AdaptiveIAlg (idxSet AfterIdx prevIdx)

variable (B C) in
/-- **The hypotheses of the composition along the swap**, on the adversary's registers: at each
step, the block hypotheses of the step and the other Kraus map along `σ` with the sets `G`, `G'`,
and the recorded slot `Jc` changing only to `k` at step `k`; the permutations keep the kinds,
swap the request by `σ₁` exactly at the recorded slot and leave the response; away from the
recorded slot the requests on the block are fixed by `σ₁`; the sets are closed under changes of
the response and are states of twin circuits. -/
structure SwapHyps (σ₁ : Equiv.Perm Req)
    (st'' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp)) {L : Type} [DecidableEq L] (ℓB : B.W → Option L) (r : L)
    (Jc : B.W → Option ℕ)
    (σ : ℕ → Equiv.Perm (B.W × Req × Option Resp)) (σ₀ : Equiv.Perm (B.W × Req × Option Resp))
    (G G' : ℕ → Set (B.W × Req × Option Resp)) (G₀ G₀' : Set (B.W × Req × Option Resp)) :
    Prop where
  /-- The step hypotheses on the `none` block. -/
  pairNone : ∀ k : StepIdx B.slots B.post,
    PairNone (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace)
      {d | d.1 ∈ prevSeq G G₀ k} {d | d.1 ∈ G k} {d | d.1 ∈ prevSeq G' G₀' k}
      {d | d.1 ∈ G' k} (B.step k) (st'' k)
  /-- The step hypotheses on the block `r` along the permutations. -/
  pairOn : ∀ k : StepIdx B.slots B.post,
    PairOn (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) r (Equiv.refl _)
      (AdaptiveIAlg.tripPerm (σ k)) (AdaptiveIAlg.tripPerm (prevSeq σ σ₀ k)) {d | d.1 ∈ G k}
      {d | d.1 ∈ prevSeq G G₀ k} (B.step k) (st'' k)
  /-- The recorded slot changes only to `k` at step `k`. -/
  slot : ∀ (k : StepIdx B.slots B.post) i (a b : DReg B.W B.width X Y Req Resp),
    b.1 ∈ prevSeq G G₀ k → (B.step k).op i a b ≠ 0 →
      Jc a.workspace = Jc b.workspace ∨ (Jc b.workspace = none ∧ Jc a.workspace = some k)
  /-- The permutations keep the kinds. -/
  kind : ∀ n x, B.kind (σ n x).1 = B.kind x.1
  /-- They swap the request by `σ₁` exactly at the recorded slot. -/
  req : ∀ n x, (σ n x).2.1 = swIf (Jc x.1 = some n) σ₁ x.2.1
  /-- They leave the response. -/
  resp : ∀ n w q a a', σ n (w, q, a') = ((σ n (w, q, a)).1, (σ n (w, q, a)).2.1, a')
  /-- Away from the recorded slot the requests on the block are fixed by `σ₁`. -/
  fix : ∀ (j : Fin B.slots), ∀ x ∈ G j, InBlock ℓB r x.1 → B.kind x.1 → Jc x.1 ≠ some (j : ℕ) →
    σ₁ x.2.1 = x.2.1
  /-- The sets are closed under changes of the response. -/
  closed : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx
  /-- The second family's sets are closed under changes of the response. -/
  closed' : ∀ idx w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx
  /-- The two families' sets have the same registers of label `none`. -/
  none_eq : ∀ idx x, ℓB x.1 = none → (x ∈ idxSet G' G₀' idx ↔ x ∈ idxSet G G₀ idx)
  /-- The permutations carry the sets on the block. -/
  set_eq : ∀ idx x, InBlock ℓB r x.1 →
    (idxPerm σ σ₀ idx x ∈ idxSet G' G₀' idx ↔ x ∈ idxSet G G₀ idx)
  /-- The permutations keep the label. -/
  label_eq : ∀ idx x, ℓB (idxPerm σ σ₀ idx x).1 = ℓB x.1

end Hyps

/-! ### Twin pieces along the swap -/

section Twins

open AdaptiveIAlg (idxSet AfterIdx prevIdx)

variable {L : Type} [DecidableEq L] {ℓB : B.W → Option L} {r : L} {Jc : B.W → Option ℕ}
  {G G' : ℕ → Set (B.W × Req × Option Resp)} {G₀ G₀' : Set (B.W × Req × Option Resp)}
  {Q : Set (B.CW C) → Set (B.CW C) → Equiv.Perm (B.CW C) → Prop}

variable [Nonempty X] [AddGroup Y]

/-- **A gate permuting the composed registers, keeping the adversary's registers and the logs and
commuting with the swap**, twin with itself at a state. -/
theorem twin_ofPerm_cw {π : Equiv.Perm (QueryReg (B.CW C) 1 X Y)}
    (h1 : ∀ q, (π q).1.adv.1 = q.1.adv.1) (h2 : ∀ q, (π q).1.chal.logs = q.1.chal.logs)
    {σn : Equiv.Perm (B.W × Req × Option Resp)}
    (hπ : ∀ p, π (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) = WorkRel.wq (cwPerm B C σ₁ Jc σn) (π p))
    {idx : Option ℕ} {c c' : ReprogrammedCircuit (B.CW C) X Y} {b be : Bool} {Se Se' : Set (B.CW C)}
    {τe : Equiv.Perm (B.CW C)}
    (h : ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q c c'
      (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn) b Se Se' τe be) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q (.kraus (KrausMap.ofPerm π) c)
      (.kraus (KrausMap.ofPerm π) c') (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx)
      (cwPerm B C σ₁ Jc σn) b Se Se' τe be :=
  .same (blockIso_ofPerm_adv h1) (setIso_ofPerm_cw h1 h2 G G₀ idx)
    (setIso_ofPerm_cw h1 h2 G' G₀' idx) ⟨_, pairOn_ofPerm hπ r _ _⟩ h

include hC in
theorem twin_chalQueries_cw (j : Fin B.slots) {σn : Equiv.Perm (B.W × Req × Option Resp)}
    (idx : Option ℕ) (b : Bool) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q (B.chalQueries C j)
      (B.chalQueries C j) (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn) b
      (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn)
      (if C.q = 0 then b else false) := by
  have h := ReprogrammedCircuit.BTwin.concat_same (ℓ := fun v : B.CW C => ℓB v.adv.1.1) (r := r)
    (Q := Q) (S := B.cwSet C G G₀ idx) (S' := B.cwSet C G' G₀' idx)
    (τ := cwPerm B C σ₁ Jc σn) ((List.finRange C.q).map fun i =>
      .kraus (KrausMap.ofPerm (B.prepChal C j i))
        (.rquery (fun v => B.chalAss C j i v.chal)
          (.kraus (KrausMap.ofPerm (B.garSwap C j i)) .nil)))
    (fun x hx b' => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact twin_ofPerm_cw (fun _ => rfl) (fun _ => rfl) (prepChal_cwPerm hC j i)
        (.rquery (fun v => chalAss_chalSw hC (swFam_slotSw _) j i v.chal)
          (twin_ofPerm_cw (fun _ => rfl) (fun _ => rfl) (garSwap_cwPerm j i) .nil))) b
  have e : ((List.finRange C.q).map fun i =>
      (ReprogrammedCircuit.kraus (KrausMap.ofPerm (B.prepChal C j i))
        (.rquery (fun v => B.chalAss C j i v.chal) (.kraus (KrausMap.ofPerm (B.garSwap C j i))
          .nil)) : ReprogrammedCircuit (B.CW C) X Y)) = [] ↔ C.q = 0 := by
    simp
  simp only [e] at h
  exact h

theorem twin_advQueries_cw (ass : B.CW C → List (Assignment X Y))
    {σn : Equiv.Perm (B.W × Req × Option Resp)}
    (hass : ∀ v, ass (cwPerm B C σ₁ Jc σn v) = ass v) (idx : Option ℕ) (b : Bool) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q (B.advQueries C ass)
      (B.advQueries C ass) (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn) b
      (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn) false := by
  have h := ReprogrammedCircuit.BTwin.concat_same (ℓ := fun v : B.CW C => ℓB v.adv.1.1) (r := r)
    (Q := Q) (S := B.cwSet C G G₀ idx) (S' := B.cwSet C G' G₀' idx)
    (τ := cwPerm B C σ₁ Jc σn) ((List.finRange B.width).map fun k =>
      .kraus (KrausMap.ofPerm (B.advSwap C k))
        (.rquery ass (.kraus (KrausMap.ofPerm (B.advSwap C k)) .nil)))
    (fun x hx b' => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact twin_ofPerm_cw (fun _ => rfl) (fun _ => rfl) (advSwap_cwPerm i)
        (.rquery hass (twin_ofPerm_cw (fun _ => rfl) (fun _ => rfl) (advSwap_cwPerm i) .nil))) b
  have e : ((List.finRange B.width).map fun k =>
      (ReprogrammedCircuit.kraus (KrausMap.ofPerm (B.advSwap C k))
        (.rquery ass (.kraus (KrausMap.ofPerm (B.advSwap C k)) .nil)) :
          ReprogrammedCircuit (B.CW C) X Y)) = [] ↔ False := by
    simp [B.width_pos.ne']
  simp only [e, if_false] at h
  exact h

theorem reqOutcome_cwPerm {σn : Equiv.Perm (B.W × Req × Option Resp)} (j : Fin B.slots)
    (hk : ∀ x, B.kind (σn x).1 = B.kind x.1)
    (hq : ∀ x, (σn x).2.1 = swIf (Jc x.1 = some (j : ℕ)) σ₁ x.2.1)
    (p : QueryReg (B.CW C) 1 X Y)
    (hfix : B.kind p.1.adv.1.1 → Jc p.1.adv.1.1 ≠ some (j : ℕ) → σ₁ p.1.adv.1.2.1 = p.1.adv.1.2.1) :
    B.reqOutcome C (WorkRel.wq (cwPerm B C σ₁ Jc σn) p) =
      Equiv.optionCongr σ₁ (B.reqOutcome C p) := by
  unfold reqOutcome
  change (if B.kind (σn p.1.adv.1).1 then some (σn p.1.adv.1).2.1 else none) = _
  rw [hk, hq]
  by_cases hkd : B.kind p.1.adv.1.1
  · change _ = Equiv.optionCongr σ₁ (if B.kind p.1.adv.1.1 then _ else _)
    rw [if_pos hkd, if_pos hkd]
    by_cases hJ : Jc p.1.adv.1.1 = some (j : ℕ)
    · rw [swIf_apply_of _ hJ]
      rfl
    · rw [swIf_apply_of_not _ hJ]
      exact congrArg some (hfix hkd hJ).symm
  · change _ = Equiv.optionCongr σ₁ (if B.kind p.1.adv.1.1 then _ else _)
    rw [if_neg hkd, if_neg hkd]
    rfl

/-- **The request measurement of slot `j` at the state after step `j`**, twin with itself along
the swap, its outcomes relabelled by `σ₁`, when the requests away from the recorded slot are fixed
by `σ₁` on the well-formed registers of the block. -/
theorem twin_measReq_cw (j : Fin B.slots) {σn : Equiv.Perm (B.W × Req × Option Resp)}
    (hk : ∀ x, B.kind (σn x).1 = B.kind x.1)
    (hq : ∀ x, (σn x).2.1 = swIf (Jc x.1 = some (j : ℕ)) σ₁ x.2.1)
    (hst : ReprogrammedCircuit.TwinState (fun v : B.CW C => ℓB v.adv.1.1) r
      (B.cwSet C G G₀ (some j)) (B.cwSet C G' G₀' (some j)) (cwPerm B C σ₁ Jc σn))
    (hfix : ∀ x ∈ G j, InBlock ℓB r x.1 → B.kind x.1 → Jc x.1 ≠ some (j : ℕ) → σ₁ x.2.1 = x.2.1)
    {c c' : ReprogrammedCircuit (B.CW C) X Y} {b be : Bool} {Se Se' : Set (B.CW C)}
    {τe : Equiv.Perm (B.CW C)}
    (h : ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q c c'
      (B.cwSet C G G₀ (some j)) (B.cwSet C G' G₀' (some j)) (cwPerm B C σ₁ Jc σn) b Se Se' τe be) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q (.kraus (B.measReq C j) c)
      (.kraus (B.measReq C j) c') (B.cwSet C G G₀ (some j)) (B.cwSet C G' G₀' (some j))
      (cwPerm B C σ₁ Jc σn) b Se Se' τe be := by
  have hj : ¬ AfterIdx (some (j : ℕ)) j := lt_irrefl _
  refine .same (blockIso_measReq j) (setIso_measReq_cw j G G₀ (some j) hj)
    (setIso_measReq_cw j G' G₀' (some j) hj)
    ⟨(Equiv.optionCongr σ₁).prodCongr (Equiv.refl Unit), ?_⟩ h
  have h₂ := pairOn_ofPerm (ℓ := fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1)
    (copyReq_cwPerm (C := C) (σ₁ := σ₁) j hk hq) r {q | q.1 ∈ B.cwSet C G G₀ (some j)}
    {q | q.1 ∈ B.cwSet C G G₀ (some j)}
  have h₁ := pairOn_measureFn_on (ℓ := fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1)
    (π := WorkRel.wq (cwPerm B C σ₁ Jc σn)) (φ := Equiv.optionCongr σ₁) (f := B.reqOutcome C) r
    {q | q.1 ∈ B.cwSet C G G₀ (some j)} {q | q.1 ∈ B.cwSet C G G₀ (some j)}
    (fun p hp hps => reqOutcome_cwPerm j hk hq p (hfix _ hps.1 hp))
  exact PairOn.comp (S₀' := {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.cwSet C G' G₀' (some j)})
    (S₁' := {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.cwSet C G' G₀' (some j)}) h₂ h₁
    (SetIso.measureFn _ _).keepsSet
    (SetIso.measureFn _ _).keepsSet
    (fun i => ((blockIso_ofPerm_adv (copyReq_adv j)).keeps i).on _)
    (fun i => ((blockIso_ofPerm_adv (copyReq_adv j)).keeps i).on _)
    (fun x hb hx => (hst.set_eq x.1 hb).2 hx) (fun x hb hx => (hst.set_eq x.1 hb).1 hx)
    (fun x => hst.label_eq x.1) (fun x => hst.label_eq x.1)

include hC in
theorem twin_writeReply_cw (j : Fin B.slots) {σn : Equiv.Perm (B.W × Req × Option Resp)}
    (hσa : ∀ w q a a', σn (w, q, a') = ((σn (w, q, a)).1, (σn (w, q, a)).2.1, a'))
    (idx : Option ℕ)
    (hG : ∀ w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hG' : ∀ w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx)
    {c c' : ReprogrammedCircuit (B.CW C) X Y} {b be : Bool} {Se Se' : Set (B.CW C)}
    {τe : Equiv.Perm (B.CW C)}
    (h : ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q c c'
      (B.cwSet C G G₀ idx) (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn) b Se Se' τe be) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r Q
      (.kraus (KrausMap.ofPerm (B.writeReply C j)) c)
      (.kraus (KrausMap.ofPerm (B.writeReply C j)) c') (B.cwSet C G G₀ idx)
      (B.cwSet C G' G₀' idx) (cwPerm B C σ₁ Jc σn) b Se Se' τe be :=
  .same (blockIso_writeReply j) (setIso_writeReply_cw j G G₀ idx hG)
    (setIso_writeReply_cw j G' G₀' idx hG') ⟨_, pairOn_ofPerm (writeReply_cwPerm hC hσa j) r _ _⟩ h

variable (st'' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
  (DReg B.W B.width X Y Req Resp))

omit [DecidableEq L] [Nonempty X] [AddGroup Y] in
theorem afterIdx_prev {k i : ℕ} (h : AfterIdx (some k) i) : AfterIdx (prevIdx k) i := by
  unfold prevIdx
  split_ifs
  · trivial
  · change k - 1 < i
    change k < i at h
    omega

omit [DecidableEq L] [Nonempty X] [AddGroup Y] in
theorem le_of_afterIdx_prev {k : ℕ} (i : ℕ) (hi : k ≤ i) : AfterIdx (prevIdx k) i := by
  unfold prevIdx
  split_ifs
  · trivial
  · change k - 1 < i
    omega

omit [DecidableEq L] in
theorem advKraus_op_apply (K : StepIdx B.slots B.post → KrausMap B.R
      (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) (i : B.R) (y x : QueryReg (B.CW C) 1 X Y) :
    (({ B with step := K } : KindAlg _ O).advKraus C k).op i y x =
      (K k).op i y.1.adv x.1.adv *
        (1 : Matrix (CRest X Y Req B.slots C.q C.Coins) _ ℂ) (y.1.chal, y.2) (x.1.chal, x.2) :=
  onFst_advKraus (B := ({ B with step := K } : KindAlg _ O)) k i y x

/-- **The adversary's step `k` and the other Kraus map along the swap** on the composed registers:
from the block hypotheses of the step on the adversary's registers, and a recorded slot that
changes only to `k` at step `k`. -/
theorem pair_advKraus_cw {σ : ℕ → Equiv.Perm (B.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (B.W × Req × Option Resp)} (k : StepIdx B.slots B.post)
    (hn : PairNone (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace)
      {d | d.1 ∈ prevSeq G G₀ k} {d | d.1 ∈ G k} {d | d.1 ∈ prevSeq G' G₀' k}
      {d | d.1 ∈ G' k} (B.step k) (st'' k))
    (ho : PairOn (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) r (Equiv.refl _)
      (AdaptiveIAlg.tripPerm (σ k)) (AdaptiveIAlg.tripPerm (prevSeq σ σ₀ k)) {d | d.1 ∈ G k}
      {d | d.1 ∈ prevSeq G G₀ k} (B.step k) (st'' k))
    (hJ : ∀ i (a b : DReg B.W B.width X Y Req Resp), b.1 ∈ prevSeq G G₀ k →
      (B.step k).op i a b ≠ 0 →
        Jc a.workspace = Jc b.workspace ∨ (Jc b.workspace = none ∧ Jc a.workspace = some k)) :
    PairNone (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1)
        {q | q.1 ∈ B.cwSet C G G₀ (prevIdx k)} {q | q.1 ∈ B.cwSet C G G₀ (some k)}
        {q | q.1 ∈ B.cwSet C G' G₀' (prevIdx k)} {q | q.1 ∈ B.cwSet C G' G₀' (some k)}
        (B.advKraus C k) (({ B with step := st'' } : KindAlg _ O).advKraus C k) ∧
      PairOn (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1) r (Equiv.refl _)
        (WorkRel.wq (cwPerm B C σ₁ Jc (σ k)))
        (WorkRel.wq (cwPerm B C σ₁ Jc (idxPerm σ σ₀ (prevIdx k))))
        {q | q.1 ∈ B.cwSet C G G₀ (some k)} {q | q.1 ∈ B.cwSet C G G₀ (prevIdx k)}
        (B.advKraus C k) (({ B with step := st'' } : KindAlg _ O).advKraus C k) := by
  have e := advKraus_op_apply (C := C) B.step k
  have e' := advKraus_op_apply (C := C) st'' k
  have hprev : ∀ x : B.W × Req × Option Resp, x ∈ idxSet G G₀ (prevIdx k) → x ∈ prevSeq G G₀ k :=
    fun x hx => by rwa [AdaptiveIAlg.prevSeq_eq_idxSet]
  have hprev' : ∀ x : B.W × Req × Option Resp,
      x ∈ idxSet G' G₀' (prevIdx k) → x ∈ prevSeq G' G₀' k :=
    fun x hx => by rwa [AdaptiveIAlg.prevSeq_eq_idxSet]
  have hrest : ∀ {K : KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp)} {i : B.R} {y x : QueryReg (B.CW C) 1 X Y},
      K.op i y.1.adv x.1.adv * (1 : Matrix (CRest X Y Req B.slots C.q C.Coins) _ ℂ)
        (y.1.chal, y.2) (x.1.chal, x.2) ≠ 0 →
        K.op i y.1.adv x.1.adv ≠ 0 ∧ y.1.chal = x.1.chal := fun hne => by
    refine ⟨left_ne_zero_of_mul hne, ?_⟩
    by_contra h
    exact hne (by rw [Matrix.one_apply_ne (fun e => h (congrArg Prod.fst e)), mul_zero])
  refine ⟨⟨fun i y x hx hne => ?_, fun i y x hx hne => ?_, fun i r' y x hx hl hne => ?_,
    fun i r' y x hx hl hne => ?_, fun i y x hy hx hyl hxl => ?_, fun r' c d hc hd hcl hdl => ?_⟩,
    fun i y x hy hys hx hxs => ?_⟩
  · rw [e] at hne
    obtain ⟨h1, h2⟩ := hrest hne
    refine ⟨hn.keepsSet i _ _ (hprev _ hx.1) h1, fun j hj => ?_⟩
    rw [h2]
    exact hx.2 j (afterIdx_prev hj)
  · rw [e'] at hne
    obtain ⟨h1, h2⟩ := hrest hne
    refine ⟨hn.keepsSet' i _ _ (hprev' _ hx.1) h1, fun j hj => ?_⟩
    rw [h2]
    exact hx.2 j (afterIdx_prev hj)
  · rw [e] at hne
    exact hn.keeps i r' _ _ (hprev _ hx.1) hl (hrest hne).1
  · rw [e'] at hne
    exact hn.keeps' i r' _ _ (hprev' _ hx.1) hl (hrest hne).1
  · rw [e, e', hn.row_none_eq i _ _ hy.1 (hprev _ hx.1) hyl hxl]
  · have g1 := (onFst_advKraus (B := ({ B with step := st'' } : KindAlg _ O)) (C := C)
      k).rowGram (ℓκ := fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) r' c d
    have g2 := (onFst_advKraus (C := C) k).rowGram
      (ℓκ := fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) r' c d
    refine g1.trans (Eq.trans ?_ g2.symm)
    congr 1
    exact hn.gram_eq r' _ _ (hprev _ hc.1) (hprev _ hd.1) hcl hdl
  · rw [e, e']
    have hop := ho i y.1.adv x.1.adv hy hys.1 hx (hprev _ hxs.1)
    change (st'' k).op i (AdaptiveIAlg.tripPerm (σ k) y.1.adv)
        (AdaptiveIAlg.tripPerm (idxPerm σ σ₀ (prevIdx k)) x.1.adv) * _ = _
    have hpe : idxPerm σ σ₀ (prevIdx k) = prevSeq σ σ₀ k :=
      (AdaptiveIAlg.prevSeq_eq_idx (idxPerm σ σ₀) k).symm
    have hop' : (st'' k).op i (AdaptiveIAlg.tripPerm (σ k) y.1.adv)
        (AdaptiveIAlg.tripPerm (prevSeq σ σ₀ k) x.1.adv) = (B.step k).op i y.1.adv x.1.adv := hop
    rw [hpe, hop']
    by_cases hz : (B.step k).op i y.1.adv x.1.adv = 0
    · rw [hz, zero_mul, zero_mul]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    refine if_congr ?_ rfl rfl
    have hj := hJ i _ _ (hprev _ hxs.1) hz
    have hb : ∀ j : Fin B.slots, (k : ℕ) ≤ j → x.1.chal.logs j = none := fun j hj' =>
      hxs.2 j (le_of_afterIdx_prev (k := k) j hj')
    have hlx := logFam_swIf_eq_of_blank σ₁ hj x.1.chal.logs hb
    obtain ⟨⟨ay, ⟨ly, qy, cy⟩⟩, zy⟩ := y
    obtain ⟨⟨ax, ⟨lx, qx, cx⟩⟩, zx⟩ := x
    change logFam (fun i : Fin B.slots => swIf (Jc ay.1.1 = some (i : ℕ)) σ₁) lx =
      logFam (fun i : Fin B.slots => swIf (Jc ax.1.1 = some (i : ℕ)) σ₁) lx at hlx
    change ((⟨logFam (slotSw B σ₁ (Jc ay.1.1)) ly, qy, cy⟩ : B.CCl C), zy) =
        ((⟨logFam (slotSw B σ₁ (Jc ax.1.1)) lx, qx, cx⟩ : B.CCl C), zx) ↔
      ((⟨ly, qy, cy⟩ : B.CCl C), zy) = ((⟨lx, qx, cx⟩ : B.CCl C), zx)
    simp only [slotSw, ← hlx, Prod.mk.injEq, ChallengerRegs.mk.injEq,
      (logFam (fun i : Fin B.slots => swIf (Jc ay.1.1 = some (i : ℕ)) σ₁)).injective.eq_iff]

omit [DecidableEq L] [Nonempty X] [AddGroup Y] in
theorem prevIdx_succ (n : ℕ) : prevIdx (n + 1) = some n := by
  simp [prevIdx]

include hC in
/-- **The composition with the challenger, with the other Kraus maps, along the swap**: twin with
the composition along the well-formed composed registers and the swap of the composed
registers. -/
theorem twin_fullCircBoth_cw {Jc : B.W → Option ℕ} {σ : ℕ → Equiv.Perm (B.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (B.W × Req × Option Resp)} (h : B.SwapHyps σ₁ st'' ℓB r Jc σ σ₀ G G' G₀ G₀') :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r
      (ReprogrammedCircuit.TwinState (fun v : B.CW C => ℓB v.adv.1.1) r) (B.fullCircBoth C)
      (({ B with step := st'' } : KindAlg _ O).fullCircBoth C) (B.cwSet C G G₀ none)
      (B.cwSet C G' G₀' none) (cwPerm B C σ₁ Jc σ₀) false
      (B.cwSet C G G₀ (some (B.slots + B.post))) (B.cwSet C G' G₀' (some (B.slots + B.post)))
      (cwPerm B C σ₁ Jc (σ (B.slots + B.post))) true := by
  have hst := fun idx => twinState_cwSet (C := C) (Jc := Jc) (σ₁ := σ₁) h.none_eq h.set_eq
    h.label_eq idx
  have hslot := ReprogrammedCircuit.BTwin.concat_finRange (ℓ := fun v : B.CW C => ℓB v.adv.1.1)
    (r := r) (Q := ReprogrammedCircuit.TwinState (fun v : B.CW C => ℓB v.adv.1.1) r) B.slots
    (fun j => B.slotCircBoth C j)
    (fun j => ({ B with step := st'' } : KindAlg _ O).slotCircBoth C j)
    (fun n => B.cwSet C G G₀ (prevIdx n)) (fun n => B.cwSet C G' G₀' (prevIdx n))
    (fun n => cwPerm B C σ₁ Jc (idxPerm σ σ₀ (prevIdx n))) fun j => by
      obtain ⟨hn, ho⟩ := pair_advKraus_cw (C := C) (σ₁ := σ₁) (Jc := Jc) st'' (slotStep j)
        (h.pairNone _) (h.pairOn _) (h.slot _)
      simp only [prevIdx_succ]
      exact .diff hn ⟨_, ho⟩ (hst (some j)) (twin_measReq_cw j (h.kind j) (h.req j) (hst (some j))
        (h.fix j) ((twin_chalQueries_cw hC j (some j) true).append
          (twin_writeReply_cw hC j (h.resp j) (some j) (h.closed _) (h.closed' _)
            (twin_advQueries_cw _ (fun v => advAss_chalSw hC (swFam_slotSw _) j v.chal)
              (some j) _))))
  have hpost := ReprogrammedCircuit.BTwin.concat_finRange (ℓ := fun v : B.CW C => ℓB v.adv.1.1)
    (r := r) (Q := ReprogrammedCircuit.TwinState (fun v : B.CW C => ℓB v.adv.1.1) r) B.post
    (fun b => B.postCirc C b)
    (fun b => ({ B with step := st'' } : KindAlg _ O).postCirc C b)
    (fun n => B.cwSet C G G₀ (prevIdx (B.slots + n)))
    (fun n => B.cwSet C G' G₀' (prevIdx (B.slots + n)))
    (fun n => cwPerm B C σ₁ Jc (idxPerm σ σ₀ (prevIdx (B.slots + n)))) fun b => by
      obtain ⟨hn, ho⟩ := pair_advKraus_cw (C := C) (σ₁ := σ₁) (Jc := Jc) st'' (postStep b)
        (h.pairNone _) (h.pairOn _) (h.slot _)
      simp only [show B.slots + (b + 1) = (B.slots + b) + 1 by omega, prevIdx_succ]
      exact .diff hn ⟨_, ho⟩ (hst (some (B.slots + b)))
        (twin_advQueries_cw _ (fun v => postAss_chalSw hC (swFam_slotSw _) v.chal) _ true)
  obtain ⟨hn, ho⟩ := pair_advKraus_cw (C := C) (σ₁ := σ₁) (Jc := Jc) st'' lastStep
    (h.pairNone _) (h.pairOn _) (h.slot _)
  have hlast : ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r
      (ReprogrammedCircuit.TwinState (fun v : B.CW C => ℓB v.adv.1.1) r)
      (.kraus (B.advKraus C lastStep) .nil)
      (.kraus (({ B with step := st'' } : KindAlg _ O).advKraus C lastStep) .nil)
      (B.cwSet C G G₀ (prevIdx (B.slots + B.post))) (B.cwSet C G' G₀' (prevIdx (B.slots + B.post)))
      (cwPerm B C σ₁ Jc (idxPerm σ σ₀ (prevIdx (B.slots + B.post)))) false
      (B.cwSet C G G₀ (some (B.slots + B.post))) (B.cwSet C G' G₀' (some (B.slots + B.post)))
      (cwPerm B C σ₁ Jc (σ (B.slots + B.post))) true :=
    .diff hn ⟨_, ho⟩ (hst (some (B.slots + B.post))) .nil
  simp only [Nat.add_zero] at hpost
  exact (hslot.append hpost).append hlast

end Twins

/-! ### The initial state along the swap -/

section Init

open AdaptiveIAlg (idxSet AfterIdx prevIdx)

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

theorem chalSw_of_blank (jw : Option ℕ) (u : B.CCl C) (hu : ∀ i, u.logs i = none) :
    B.chalSw C (slotSw B σ₁ jw) u = u := by
  obtain ⟨lg, qs, ω⟩ := u
  have hu' : ∀ i, lg i = none := hu
  have hl : logFam (slotSw B σ₁ jw) lg = lg := funext fun i => by
    rw [logFam_apply, hu' i]
    rfl
  simp only [chalSw, hl]

theorem initSys_mat_apply (a b : QueryReg (B.CW C) 1 X Y) :
    (B.initSys C).mat a b = ∑ ω, ((C.coins ω).toReal : ℂ) * (B.init.mat a.1.adv b.1.adv *
      Matrix.single (((⟨fun _ => none, fun _ _ => (x₀, 0), ω⟩ : B.CCl C),
        (fun _ => (x₀, 0) : Fin 1 → X × Y))) ((⟨fun _ => none, fun _ _ => (x₀, 0), ω⟩, fun _ =>
          (x₀, 0))) (1 : ℂ) (a.1.chal, a.2) (b.1.chal, b.2)) := by
  simp only [KindAlg.initSys, MState.mix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    MState.reindex, MState.tensorKet_mat, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  rfl

/-- **The initial state of the composition is supported on the well-formed composed registers
at the start** of the adversary's initial support. -/
theorem initSys_supp_cw {G : ℕ → Set (B.W × Req × Option Resp)}
    {G₀ : Set (B.W × Req × Option Resp)}
    (hinit : ∀ a b, B.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (a b : ReprogrammedQueryReg (B.CW C) X Y)
    (h : (MState.withAnc KindAlg.x₀ (B.initSys C)).mat a b ≠ 0) :
    a.1.1 ∈ B.cwSet C G G₀ none ∧ b.1.1 ∈ B.cwSet C G G₀ none := by
  change (B.initSys C).mat (a.1.1, a.2) (b.1.1, b.2) * _ ≠ 0 at h
  have h1 := left_ne_zero_of_mul h
  rw [initSys_mat_apply] at h1
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have h2 := right_ne_zero_of_mul hω
  have h3 := hinit _ _ (left_ne_zero_of_mul h2)
  have h4 := right_ne_zero_of_mul h2
  rw [Matrix.single_apply] at h4
  split_ifs at h4 with he
  · obtain ⟨he1, he2⟩ := he
    have la := congrArg (fun x => x.1.logs) he1
    have lb := congrArg (fun x => x.1.logs) he2
    exact ⟨⟨h3.1, fun i _ => (congrFun la i).symm⟩, ⟨h3.2, fun i _ => (congrFun lb i).symm⟩⟩
  · exact absurd rfl h4

theorem initSys_eq_cw {L : Type} {ℓB : B.W → Option L} {r : L} {Jc : B.W → Option ℕ}
    {σ₀ : Equiv.Perm (B.W × Req × Option Resp)} {G : ℕ → Set (B.W × Req × Option Resp)}
    {G₀ : Set (B.W × Req × Option Resp)}
    (hinit_eq : ∀ a b : DReg B.W B.width X Y Req Resp, a.1 ∈ G₀ → b.1 ∈ G₀ →
      InBlock ℓB r a.workspace → InBlock ℓB r b.workspace →
      B.init.mat (AdaptiveIAlg.tripPerm σ₀ a) (AdaptiveIAlg.tripPerm σ₀ b) = B.init.mat a b)
    (a b : ReprogrammedQueryReg (B.CW C) X Y) (ha : a.1.1 ∈ B.cwSet C G G₀ none)
    (hb : b.1.1 ∈ B.cwSet C G G₀ none) (hla : InBlock ℓB r a.1.1.adv.1.1)
    (hlb : InBlock ℓB r b.1.1.adv.1.1) :
    (MState.withAnc KindAlg.x₀ (B.initSys C)).mat
      (WorkRel.wq (WorkRel.wa (cwPerm B C σ₁ Jc σ₀)) a)
      (WorkRel.wq (WorkRel.wa (cwPerm B C σ₁ Jc σ₀)) b) =
    (MState.withAnc KindAlg.x₀ (B.initSys C)).mat a b := by
  change (B.initSys C).mat (cwPerm B C σ₁ Jc σ₀ a.1.1, a.2) (cwPerm B C σ₁ Jc σ₀ b.1.1, b.2) * _ =
    (B.initSys C).mat (a.1.1, a.2) (b.1.1, b.2) * _
  congr 1
  rw [initSys_mat_apply, initSys_mat_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hca := chalSw_of_blank (σ₁ := σ₁) (Jc a.1.1.adv.1.1) a.1.1.chal (fun i => ha.2 i trivial)
  have hcb := chalSw_of_blank (σ₁ := σ₁) (Jc b.1.1.adv.1.1) b.1.1.chal (fun i => hb.2 i trivial)
  change _ * (B.init.mat (AdaptiveIAlg.tripPerm σ₀ a.1.1.adv) (AdaptiveIAlg.tripPerm σ₀ b.1.1.adv) *
    Matrix.single _ _ (1 : ℂ) (B.chalSw C (slotSw B σ₁ (Jc a.1.1.adv.1.1)) a.1.1.chal, a.2)
      (B.chalSw C (slotSw B σ₁ (Jc b.1.1.adv.1.1)) b.1.1.chal, b.2)) = _
  rw [hca, hcb, hinit_eq _ _ ha.1 hb.1 hla hlb]

end Init

section ComposeBits

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape (Bits m) (BitStr I J) Req Resp} {B : KindAlg ksB O} {C : Challenger (Bits m) (BitStr I J) Req Resp}
  {σ₁ : Equiv.Perm Req} {L : Type} [DecidableEq L] {ℓB : B.W → Option L} {r : L}
  {Jc : B.W → Option ℕ} {σ : ℕ → Equiv.Perm (B.W × Req × Option Resp)}
  {σ₀ : Equiv.Perm (B.W × Req × Option Resp)} {G G' : ℕ → Set (B.W × Req × Option Resp)}
  {G₀ G₀' : Set (B.W × Req × Option Resp)}
  {st'' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width (Bits m) (BitStr I J) Req Resp)
    (DReg B.W B.width (Bits m) (BitStr I J) Req Resp)}

/-- **The block hypotheses of the composition with a challenger along the witness swap**: for a
challenger that does not see `σ₁` and the hypotheses `SwapHyps` on the adversary's registers, with
the initial state supported on `G₀` and `G₀'` and invariant along `σ₀` on the block, the
composition with the other Kraus maps is the composition with other Kraus maps `K'`, and the two
satisfy `Alg.BlockNone` and `Alg.BlockRel` along sets `T (i + 1)`, `T' (i + 1)` and permutations
`P (i + 1)` after segment `i` (the well-formed registers and the swap at the start before the
first, at the last step from the last segment on), the operators relabelled by `ρ`, the label read
on the adversary's workspace. -/
theorem composeBothOut_block_cw (hC : C.SwapInv σ₁)
    (h : B.SwapHyps σ₁ st'' ℓB r Jc σ σ₀ G G' G₀ G₀')
    (hinit : ∀ a b, B.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hinit' : ∀ a b, B.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (hinit_eq : ∀ a b : DReg B.W B.width (Bits m) (BitStr I J) Req Resp, a.1 ∈ G₀ → b.1 ∈ G₀ →
      InBlock ℓB r a.workspace → InBlock ℓB r b.workspace →
      B.init.mat (AdaptiveIAlg.tripPerm σ₀ a) (AdaptiveIAlg.tripPerm σ₀ b) = B.init.mat a b)
    {O' : Type} (f : B.CW C → O') :
    ∃ (K' : Fin ((B.composeBothOut C f).depth + 1) → KrausMap (B.composeBothOut C f).R
        (QueryReg (B.composeBothOut C f).V 1 (Bits m) (BitStr I J))
        (QueryReg (B.composeBothOut C f).V 1 (Bits m) (BitStr I J)))
      (ρ : Equiv.Perm (B.composeBothOut C f).R) (T T' : ℕ → Set (B.CW C))
      (P : ℕ → Equiv.Perm (B.CW C)),
      T 0 = B.cwSet C G G₀ none ∧ T' 0 = B.cwSet C G' G₀' none ∧ P 0 = cwPerm B C σ₁ Jc σ₀ ∧
      (∀ j, (B.fullCircBoth C).queries < j →
        T j = B.cwSet C G G₀ (some (B.slots + B.post)) ∧
        T' j = B.cwSet C G' G₀' (some (B.slots + B.post)) ∧
        P j = cwPerm B C σ₁ Jc (σ (B.slots + B.post))) ∧
      ({ B with step := st'' } : KindAlg _ O).composeBothOut C f =
        { B.composeBothOut C f with step := K' } ∧
      (B.composeBothOut C f).BlockNone K' (fun v => ℓB v.1.adv.1.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T' (i + 1)})
        {v | v.1 ∈ B.cwSet C G G₀ none} {v | v.1 ∈ B.cwSet C G' G₀' none} ∧
      (B.composeBothOut C f).BlockRel K' (fun v => ℓB v.1.adv.1.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T' (i + 1)})
        {v | v.1 ∈ B.cwSet C G G₀ none} {v | v.1 ∈ B.cwSet C G' G₀' none}
        (fun i => WorkRel.wa (P (i + 1))) (WorkRel.wa (cwPerm B C σ₁ Jc σ₀)) (fun _ => ρ) r := by
  obtain ⟨K', ρ, T, T', P, hT0, hT0', hP0, -, hTe, heq, hn, hr⟩ :=
    (twin_fullCircBoth_cw hC st'' h).alg_block (fun _ _ _ h => h)
      (twinState_cwSet (C := C) (Jc := Jc) (σ₁ := σ₁) h.none_eq h.set_eq h.label_eq none)
      (MState.withAnc KindAlg.x₀ (B.initSys C)) (fun v => f v.1) (initSys_supp_cw hinit)
      (initSys_supp_cw hinit') (fun a b ha hb hla hlb => initSys_eq_cw hinit_eq a b ha hb hla hlb)
  exact ⟨K', ρ, T, T', P, hT0, hT0', hP0, hTe, heq, hn, hr⟩

end ComposeBits

end KindAlg

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum

/-- **The simulation challenger does not see a swap of the statements** that the simulator's
programs do not see. -/
theorem simExtChallenger_swapInv {X Y Stmt Proof SimCoins : Type} [Fintype SimCoins]
    [DecidableEq SimCoins] (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ)
    {σ₁ : Equiv.Perm Stmt} (hS : ∀ x c, S.prog (σ₁ x) c = S.prog x c) :
    (simExtChallenger S Q).SwapInv σ₁ := by
  intro ω hist hist' r r' hh hr
  have hl := hh.length_eq
  change simExtRespond S Q ω hist r = simExtRespond S Q ω hist' r'
  unfold simExtRespond
  have hp : ∀ c, S.prog r' c = S.prog r c := fun c => by
    rcases hr with rfl | rfl
    · rfl
    · exact hS r c
  simp only [← hl, hp]

end GordieHowe.QROM
