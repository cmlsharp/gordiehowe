-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeProof

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The supports of the bridge's run with the request points of a table

Three hypotheses of `ReqQueryAlg.simLaw_withSteps_eq_instLog`
(`GordieHowe/Model/Quantum/Interactive/ReqBridgeCore.lean`) at the bridge algorithm `bridgeAlg`
with the steps `bridgeSteps tab` and the supports `goodS`, for a trace-preserving adversary.

- `bridge_h0`: the simulated run starts on `goodS 0`.
- `bridge_hG`: a step with the request point of the table, then the simulated query, carries
  `goodS k` to `goodS (k + 1)`.
- `bridge_hP`: on `goodS k`, after the write of the request point `k`, the bridge's step `k` keeps
  the requests of the request points `0, …, k`.

The proof of `bridge_hP` carries records through the compiled circuit.
- `ReprogrammedCircuit.KeepsAt`: every Kraus map of a circuit keeps the records of the earlier
  queries; `ReprogrammedCircuit.stepAt_compiled_keepsAt`: a step of the pure algorithm of the
  compiled circuit then keeps them, with a certificate of the supports at the trivial records.
- `KindAlg.keepsAt_fullCircBoth`: records of the workspace kept by the adversary's Kraus maps are
  kept by the composition; `AdaptiveIAlg.keepsAt_logRec`: the records `logRec`, the absorbed logs
  of the slots before a query, for the adversary absorbed with a table.
- `reqL_congr`: the request of the request point `j` reads only the absorbed logs of the slots
  `l` with `(l + 1) · (q + width) ≤ j`.
- `cohStep_hist`, `bridge_step_hist`: step `k` of the run of the composition, and of the bridge,
  keeps the requests of the request points `0, …, k`; `ExpandAdvSupp.expandAdv_stepAt_supp`: one
  step of the expanded adversary.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Records kept by the Kraus maps of a circuit -/

namespace ReprogrammedCircuit

section Keeps

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **Every Kraus map of the circuit keeps the records `C i` of the earlier queries**, read with
`k` reprogrammed queries before the circuit (the records part of `Valid`, without its padding
condition). -/
def KeepsAt (C : ℕ → Set V) : ReprogrammedCircuit V X Y → ℕ → Prop
  | nil, _ => True
  | kraus K c, k => (∀ i < k, ∀ r p' p, K.op r p' p ≠ 0 → (p'.1 ∈ C i ↔ p.1 ∈ C i)) ∧
      KeepsAt C c k
  | rquery _ c, k => KeepsAt C c (k + 1)

/-- **Records kept by a concatenation**, the second circuit read after the first one's queries. -/
theorem KeepsAt.append {C : ℕ → Set V} : ∀ {c d : ReprogrammedCircuit V X Y} {k : ℕ},
    KeepsAt C c k → KeepsAt C d (k + c.queries) → KeepsAt C (c ++ d) k
  | nil, _, _, _, hd => hd
  | kraus _ c, _, _, ⟨hk, hc⟩, hd => ⟨hk, KeepsAt.append (c := c) hc hd⟩
  | rquery _ c, d, k, hc, hd => by
    refine KeepsAt.append (c := c) hc ?_
    rw [show k + 1 + c.queries = k + (rquery _ c).queries by simp [queries]; omega]
    exact hd

/-- **Records kept by a concatenation of circuits with `L` queries each**, piece `i` read from
query `k₀ + i * L`. -/
theorem KeepsAt.concat_of {C : ℕ → Set V} {L : ℕ} :
    ∀ {cs : List (ReprogrammedCircuit V X Y)} {k₀ : ℕ}, (∀ c ∈ cs, c.queries = L) →
      (∀ i (hi : i < cs.length), KeepsAt C cs[i] (k₀ + i * L)) → KeepsAt C (concat cs) k₀
  | [], _, _, _ => trivial
  | c :: cs, k₀, hq, h => by
    refine KeepsAt.append (by have := h 0 (by simp); simpa using this) ?_
    rw [hq c (List.mem_cons_self ..)]
    exact KeepsAt.concat_of (cs := cs) (k₀ := k₀ + L)
      (fun d hd => hq d (List.mem_cons_of_mem _ hd)) fun i hi => by
        have h' := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h'
        have e : k₀ + L + i * L = k₀ + (i + 1) * L := by ring
        rw [e]
        exact h'

/-- `KeepsAt.concat_of` for the circuits of a function on `Fin n`. -/
theorem KeepsAt.concat_finRange {C : ℕ → Set V} {n L k₀ : ℕ}
    {f : Fin n → ReprogrammedCircuit V X Y} (hq : ∀ i, (f i).queries = L)
    (h : ∀ i : Fin n, KeepsAt C (f i) (k₀ + i * L)) :
    KeepsAt C (concat ((List.finRange n).map f)) k₀ :=
  KeepsAt.concat_of (L := L) (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
      exact hq i)
    fun i hi => by
      simp only [List.getElem_map, List.getElem_finRange]
      exact h _

variable [AddCommGroup Y]

/-- **Every segment of the compiled circuit keeps the records** that the circuit's Kraus maps
keep, for a circuit with a certificate of its supports at the trivial records (which gives trace
preservation). -/
theorem segOK_seg_keepsAt {C G : ℕ → Set V} : ∀ (c : ReprogrammedCircuit V X Y) {k : ℕ}
    {P Q : Set V}, Valid (fun _ => Set.univ) G c k P Q → KeepsAt C c k → ∀ j ≤ c.queries,
      SegOK ((toCircuit c).seg j).K C (k + j) Set.univ Set.univ
  | nil, k, P, Q, _, _, j, hj => by
    obtain rfl : j = 0 := by simpa [queries] using hj
    rw [toCircuit, Circuit.seg_nil]
    exact segOK_identity C _ subset_rfl
  | kraus K c, k, P, Q, ⟨htp, _, P', _, hv⟩, ⟨hk, hc⟩, 0, _ =>
    (segOK_liftAnc htp hk fun _ _ _ _ _ => Set.mem_univ _).comp
      (segOK_seg_keepsAt c hv hc 0 (Nat.zero_le _))
  | kraus K c, k, P, Q, ⟨_, _, P', _, hv⟩, ⟨_, hc⟩, j + 1, hj =>
    segOK_seg_keepsAt c hv hc (j + 1) hj
  | rquery a c, k, P, Q, _, _, 0, _ =>
    (segOK_reprogSwap a C _ subset_rfl).comp (segOK_identity C _ subset_rfl)
  | rquery a c, k, P, Q, ⟨_, _, hv⟩, hc, 1, hj =>
    ((segOK_reprogSwap a C _ subset_rfl).comp (segOK_reprogAdd a C _ subset_rfl)).comp
      (segOK_seg_keepsAt c hv hc 0 (Nat.zero_le _))
  | rquery a c, k, P, Q, ⟨_, _, hv⟩, hc, j + 2, hj => by
    have h := segOK_seg_keepsAt c hv hc (j + 1) (by simp [queries] at hj; omega)
    rw [show k + 1 + (j + 1) = k + (j + 2) by omega] at h
    exact h

variable [Nonempty Y] {O' O : Type}
  (c : ReprogrammedCircuit V X Y) (x₀ : X) (ρ : MState (QueryReg V 1 X Y))
  (out : V × (X × Y × Bool) → O') (g : Option O' → O)

/-- The compiled algorithm's map `k` keeps the records as segment `k` of the circuit. -/
theorem segOK_step_keepsAt {C G : ℕ → Set V} {P Q : Set V}
    (hv : Valid (fun _ => Set.univ) G c 0 P Q) (hc : KeepsAt C c 0) {k : ℕ} (hk : k ≤ c.queries)
    (hkd : k < (compiledAlg c x₀ ρ out).depth + 1) :
    SegOK ((compiledAlg c x₀ ρ out).step ⟨k, hkd⟩) C k Set.univ Set.univ := by
  have h := segOK_sigmaEmbed (G := fun j : Fin ((toCircuit c).queries + 1) => (toCircuit c).seg j)
    (k := ⟨k, hkd⟩) (segOK_seg_keepsAt c hv hc k hk)
  rwa [zero_add] at h

/-- **One step of the dilation of the compiled circuit keeps the records of the earlier queries**
that the circuit's Kraus maps keep (as `dilStep_compiled_keeps`). -/
theorem dilStep_compiled_keepsAt {C G : ℕ → Set V} {P Q : Set V}
    (hv : Valid (fun _ => Set.univ) G c 0 P Q) (hc : KeepsAt C c 0) {k i : ℕ} (hk : k ≤ c.queries)
    (hi : i < k) [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    (T : Set V) (hT : T = C i ∨ T = (C i)ᶜ)
    {ψ : QState ((QueryReg (V × (X × Y × Bool)) 1 X Y × Bool) ×
      (compiledAlg c x₀ ρ out).HaltAnc)}
    (hclean : MixedAlg.CleanVec k ψ)
    (hS : ∀ i a, ¬ (i.1.1.1 ∈ T ∧ i.2 = false) → ψ (i, a) = 0) :
    ∀ i a, ¬ (i.1.1.1 ∈ T ∧ i.2 = false) →
      (compiledAlg c x₀ ρ out).halting.dilStep () k ψ (i, a) = 0 := by
  set A := compiledAlg c x₀ ρ out
  obtain ⟨hkd, hstep⟩ := dilStep_compiled_eq c x₀ ρ out hk hclean
  have hseg := segOK_step_keepsAt c x₀ ρ out hv hc hk hkd
  intro i' a hi'
  rw [hstep]
  refine krausAct_supported _
    (S := {p : QueryReg A.V 1 X Y × Bool | p.1.1.1 ∈ T ∧ p.2 = false})
    (S' := {p : QueryReg A.V 1 X Y × Bool | p.1.1.1 ∈ T ∧ p.2 = false})
    (KrausMap.complete_supp_of hseg.tp (S := {p | p.1.1 ∈ T}) (S' := {p | p.1.1 ∈ T})
      fun r j' j hj hne => ?_) (fun i a hi => hS i a hi) i' a hi'
  have hkeep := hseg.keeps i hi r j' j hne
  rcases hT with rfl | rfl
  · exact hkeep.2 hj
  · exact fun h => hj (hkeep.1 h)

/-- **A step of the pure algorithm of the compiled circuit keeps the records of earlier queries**
that the circuit's Kraus maps keep (as `stepAt_compiled_keeps`, the records apart from the
certificate of the supports). -/
theorem stepAt_compiled_keepsAt [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {C G : ℕ → Set V} {P Q : Set V} (hv : Valid (fun _ => Set.univ) G c 0 P Q)
    (hc : KeepsAt C c 0) {k i : ℕ} (hk : k ≤ c.queries) (hi : i < k) (T : Set V)
    (hT : T = C i ∨ T = (C i)ᶜ)
    {v : QState (QueryReg (((compiledAlg c x₀ ρ out).V × Bool) × (compiledAlg c x₀ ρ out).HaltAnc)
      1 X Y)}
    (hS : Supported {r | r.1.1.1.1 ∈ T ∧ r.1.1.2 = false ∧ MixedAlg.Clean k r.1.2} v) :
    Supported {r | r.1.1.1.1 ∈ T}
      ((((compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v) := by
  set A := compiledAlg c x₀ ρ out
  set σ := Alg.haltRelabel A.V A.HaltAnc X Y
  set ψ := relabel σ.symm v
  have hψ : ∀ i a, ψ (i, a) = v (σ (i, a)) := fun i a => rfl
  have hclean : MixedAlg.CleanVec k ψ := fun i a ha => by
    rw [hψ]
    exact hS _ fun h => ha h.2.2
  have hS' : ∀ i a, ¬ (i.1.1.1 ∈ T ∧ i.2 = false) → ψ (i, a) = 0 := fun i a hi => by
    rw [hψ]
    exact hS _ fun h => hi ⟨h.1, h.2.1⟩
  have hsupp := dilStep_compiled_keepsAt c x₀ ρ out hv hc hk hi T hT hclean hS'
  have hkd : k ≤ A.depth := by rw [depth_compiledAlg]; exact hk
  rw [Alg.stepAt_toQueryAlgCoh_mapOut, Alg.stepAt_dilateCoh A hkd]
  intro r hr
  exact hsupp _ _ fun h => hr h.1

end Keeps

end ReprogrammedCircuit

/-! ### Records of the workspace in the composition -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape X Y Req Resp} {B : KindAlg ksB O} {Ch : Challenger X Y Req Resp} [Nonempty X] [AddCommGroup Y]
  (Cw : ℕ → Set B.W)

open ReprogrammedCircuit

/-- A basis permutation that keeps the workspace keeps the records of the workspace. -/
theorem keepsAt_ofPerm_ws {π : Equiv.Perm (QueryReg (B.CW Ch) 1 X Y)}
    (hπ : ∀ p, (π p).1.adv.workspace = p.1.adv.workspace) {c : ReprogrammedCircuit (B.CW Ch) X Y}
    {k : ℕ} (hc : KeepsAt (fun i => B.advIn Ch (Cw i)) c k) :
    KeepsAt (fun i => B.advIn Ch (Cw i)) (.kraus (KrausMap.ofPerm π) c) k :=
  ⟨fun i _ r p' p h => by
    rw [ofPerm_eq_of_ne_zero h]
    change (π p).1.adv.workspace ∈ Cw i ↔ p.1.adv.workspace ∈ Cw i
    rw [hπ], hc⟩

/-- The adversary's queries keep the records of the workspace. -/
theorem keepsAt_advQueries_ws (ass : B.CW Ch → List (Assignment X Y)) (k₀ : ℕ) :
    KeepsAt (fun i => B.advIn Ch (Cw i)) (B.advQueries Ch ass) k₀ :=
  KeepsAt.concat_finRange (L := 1) (fun _ => rfl) fun _ =>
    keepsAt_ofPerm_ws Cw (fun _ => rfl) (keepsAt_ofPerm_ws Cw (fun _ => rfl) trivial)

/-- The challenger's queries keep the records of the workspace. -/
theorem keepsAt_chalQueries_ws (j : Fin B.slots) (k₀ : ℕ) :
    KeepsAt (fun i => B.advIn Ch (Cw i)) (B.chalQueries Ch j) k₀ :=
  KeepsAt.concat_finRange (L := 1) (fun _ => rfl) fun _ =>
    keepsAt_ofPerm_ws Cw (fun _ => rfl) (keepsAt_ofPerm_ws Cw (fun _ => rfl) trivial)

/-- **Slot `j` keeps the records of the workspace** when the adversary's Kraus map before slot
`j` keeps those of the earlier queries (`hslot`). -/
theorem keepsAt_slotCircBoth_ws (j : Fin B.slots)
    (hslot : ∀ z (y x : DReg B.W B.width X Y Req Resp), (B.step (slotStep j)).op z y x ≠ 0 →
      ∀ i < (j : ℕ) * (Ch.q + B.width), (y.workspace ∈ Cw i ↔ x.workspace ∈ Cw i)) :
    KeepsAt (fun i => B.advIn Ch (Cw i)) (B.slotCircBoth Ch j) ((j : ℕ) * (Ch.q + B.width)) := by
  refine ⟨fun i hi z p' p h => hslot z _ _ (advKraus_ne_zero' h) i hi, ?_⟩
  refine ⟨fun i _ o p' p h => ?_, ?_⟩
  · rw [AdaptiveIAlg.measReq_op_apply Ch j o p' p] at h
    have hy : p' = B.copyReq Ch j p := by
      by_contra h'
      exact h (mul_eq_zero_of_left (ite_eq_right h') _)
    subst hy
    change (B.copyReq Ch j p).1.adv.workspace ∈ Cw i ↔ p.1.adv.workspace ∈ Cw i
    rw [copyReq_workspace]
  refine KeepsAt.append (keepsAt_chalQueries_ws Cw j _) ?_
  exact keepsAt_ofPerm_ws Cw (writeReply_workspace j) (keepsAt_advQueries_ws Cw _ _)

/-- **Post batch `b` keeps the records of the workspace** when the adversary's Kraus map does. -/
theorem keepsAt_postCirc_ws (b : Fin B.post) (k₀ : ℕ)
    (hpost : ∀ z (y x : DReg B.W B.width X Y Req Resp), (B.step (postStep b)).op z y x ≠ 0 →
      ∀ i, (y.workspace ∈ Cw i ↔ x.workspace ∈ Cw i)) :
    KeepsAt (fun i => B.advIn Ch (Cw i)) (B.postCirc Ch b) k₀ :=
  ⟨fun i _ z _ _ h => hpost z _ _ (advKraus_ne_zero' h) i, keepsAt_advQueries_ws Cw _ _⟩

/-- **The composition keeps the records of the workspace** when the adversary's Kraus map before
slot `j` keeps those of the queries before slot `j` (`hslot`) and the later ones keep all
(`hpost`). -/
theorem keepsAt_fullCircBoth
    (hslot : ∀ (j : Fin B.slots) z (y x : DReg B.W B.width X Y Req Resp),
      (B.step (slotStep j)).op z y x ≠ 0 →
      ∀ i < (j : ℕ) * (Ch.q + B.width), (y.workspace ∈ Cw i ↔ x.workspace ∈ Cw i))
    (hpost : ∀ (k : StepIdx B.slots B.post), B.slots ≤ (k : ℕ) →
      ∀ z (y x : DReg B.W B.width X Y Req Resp), (B.step k).op z y x ≠ 0 →
      ∀ i, (y.workspace ∈ Cw i ↔ x.workspace ∈ Cw i)) :
    KeepsAt (fun i => B.advIn Ch (Cw i)) (B.fullCircBoth Ch) 0 := by
  unfold KindAlg.fullCircBoth
  refine KeepsAt.append (KeepsAt.append ?_ ?_) ?_
  · exact KeepsAt.concat_finRange (L := Ch.q + B.width) (fun j => B.queries_slotCircBoth Ch j)
      fun j => by simpa using keepsAt_slotCircBoth_ws Cw j (hslot j)
  · exact KeepsAt.concat_finRange (L := B.width) (fun b => B.queries_postCirc Ch b)
      fun b => keepsAt_postCirc_ws Cw b _ (hpost (postStep b) (by simp))
  · exact ⟨fun i _ z p' p h =>
      hpost lastStep (by simp) z _ _ (advKraus_ne_zero' h) i, trivial⟩

end KindAlg

/-! ### The records of the absorbed logs -/

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (tab : A.OuterTab Req₂ Resp₂)

/-- **The records of the absorbed logs before query `n`** (proof-internal), for slots of `L`
queries: the workspaces whose absorbed logs of the slots `l` with `l · L ≤ n` are those of a log
register in `Z`. -/
def logRec (Z : Set (LogReg Req A.slots)) (L n : ℕ) : Set (A.absorbTab F tab).toTPKindAlg.W :=
  {w | ∃ lg ∈ Z, ∀ l : Fin A.slots, (l : ℕ) * L ≤ n → w.1.1.logs l = lg l}

variable {A F tab}

/-- **`logRec` reads only the absorbed logs it records.** -/
theorem logRec_iff {Z : Set (LogReg Req A.slots)} {L n : ℕ}
    {y x : (A.absorbTab F tab).toTPKindAlg.W}
    (h : ∀ l : Fin A.slots, (l : ℕ) * L ≤ n → y.1.1.logs l = x.1.1.logs l) :
    y ∈ A.logRec F tab Z L n ↔ x ∈ A.logRec F tab Z L n := by
  constructor
  · rintro ⟨lg, hlg, hy⟩
    exact ⟨lg, hlg, fun l hl => (h l hl).symm.trans (hy l hl)⟩
  · rintro ⟨lg, hlg, hx⟩
    exact ⟨lg, hlg, fun l hl => (h l hl).trans (hx l hl)⟩

variable [Nonempty X] [AddCommGroup Y]

/-- **The composition of the adversary absorbed with a table keeps the records `logRec`** of the
slots of `q + width` queries, for a trace-preserving adversary: the adversary's step of slot `j`
changes only the log of slot `j`, which no record of an earlier query reads. -/
theorem keepsAt_logRec (hA : A.TracePreserving) (Z : Set (LogReg Req A.slots))
    (C₁ : Challenger X Y Req₁ Resp₁) :
    ReprogrammedCircuit.KeepsAt
      (fun i => (A.absorbTab F tab).toTPKindAlg.advIn C₁
        (A.logRec F tab Z (C₁.q + (A.absorbTab F tab).toTPKindAlg.width) i))
      ((A.absorbTab F tab).toTPKindAlg.fullCircBoth C₁) 0 := by
  refine KindAlg.keepsAt_fullCircBoth _ (fun j z y x h i hi => ?_) fun k hk z y x h i => ?_
  · refine logRec_iff fun l hl => tp_absorbTab_logs hA h l fun he => ?_
    have h1 : (l : ℕ) * (C₁.q + (A.absorbTab F tab).toTPKindAlg.width) <
        (j : ℕ) * (C₁.q + (A.absorbTab F tab).toTPKindAlg.width) := lt_of_le_of_lt hl hi
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    change (l : ℕ) = (j : ℕ) at he
    omega
  · refine logRec_iff fun l _ => tp_absorbTab_logs hA h l fun he => ?_
    have := l.isLt
    change (A.absorbTab F tab).toTPKindAlg.slots ≤ (k : ℕ) at hk
    change A.slots ≤ (k : ℕ) at hk
    omega

end AdaptiveIAlg

/-! ### The permutations of a query algorithm with request points -/

namespace ReqQueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)

/-- The controlled write on the simulation register, on the work register. -/
theorem simPerm_ctrlWrite_fst (k : Fin (t + 1)) (rep : G.W → Option Resp)
    (hrep : ∀ x w, rep (G.write k x w) = rep w) (s : SimRegister G.W I J m t) :
    (G.simPerm (G.ctrlWrite k rep hrep) s).1.1 = G.write k (rep s.1.1) s.1.1 :=
  rfl

end ReqQueryAlg

/-! ### One step of the expanded adversary -/

namespace ExpandAdvSupp

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (e : Y ≃ B) (E : Expansion X B C) (k : ℕ)

/-- **Step `i` of the expanded adversary carries a support of `𝒜`'s work register** that `𝒜`'s
step `i` carries (`h`, for `i ≤ t`), and keeps a support otherwise (`hm`). -/
theorem expandAdv_stepAt_supp {t : ℕ} (𝒜 : QueryAlg X Y t C) {S S' : Set 𝒜.W}
    (i : Fin (t + k + 1))
    (h : (i : ℕ) ≤ t → ∀ u, Supported {r | r.1 ∈ S} u →
      Supported {r | r.1 ∈ S'} ((𝒜.toOracleAlg ∅).stepAt () i u))
    (hm : t < (i : ℕ) → S ⊆ S') {v : QState (ExpBasis (X := X) (Y := Y) k 𝒜.W)}
    (hv : Supported {b : ExpBasis (X := X) (Y := Y) k 𝒜.W | b.1.1 ∈ S} v) :
    Supported {b : ExpBasis (X := X) (Y := Y) k 𝒜.W | b.1.1 ∈ S'}
      ((expandAdv e E k 𝒜).step i v) := by
  change Supported _ (expStep e E k 𝒜 𝒜.out i v)
  unfold expStep
  split_ifs with h1 h2
  · exact supported_lift k (h (by omega)) hv
  · have e1 : (𝒜.toOracleAlg ∅).stepAt () t = (𝒜.toOracleAlg ∅).stepAt () i := by
      rw [h2]
    rw [LinearIsometryEquiv.trans_apply, e1]
    exact supported_permOp_expPerm e E k _ 0 (supported_lift k (h (by omega)) hv)
  · exact supported_permOp_expPerm e E k _ _ (hv.mono fun b hb => hm (by omega) hb)

end ExpandAdvSupp

/-! ### The supports of the bridge with the request points of a table -/

section Bridge

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- **The request of the request point `j` read from absorbed logs** `lg`: the outer request of
slot `j'`'s logged request at its request number, for the slot `j'` whose reply step `j` reads
(`answerSlot`); the dummy `d₂` otherwise. -/
def reqL (j : ℕ) (lg : LogReg Req A.slots) : Req₂ :=
  match answerSlot A C₁ j with
  | none => d₂
  | some j' => match lg j' with
    | none => d₂
    | some r => (F.outer (A.reqCount lg j') r).getD d₂

/-- The request of the request point `j` of the composition, from its absorbed logs. -/
theorem reqV_eq_reqL (j : ℕ) (c : (bridgeCompose A C₁ F).V) :
    reqV A C₁ F d₂ j c = reqL A C₁ F d₂ j (absV A C₁ F c).1.1.1.logs :=
  rfl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂]
  [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁] in
/-- **The request of the request point `j` reads only the absorbed logs of the slots `l` with
`(l + 1) · (q + width) ≤ j`**, the slots whose reply comes no later than step `j`. -/
theorem reqL_congr (j : ℕ) {lg lg' : LogReg Req A.slots}
    (h : ∀ l : Fin A.slots, ((l : ℕ) + 1) * (C₁.q + A.width) ≤ j → lg l = lg' l) :
    reqL A C₁ F d₂ j lg = reqL A C₁ F d₂ j lg' := by
  unfold reqL answerSlot
  split_ifs with hj
  · dsimp only
    have hle : ∀ l : Fin A.slots, (l : ℕ) ≤ j / (C₁.q + A.width) - 1 →
        ((l : ℕ) + 1) * (C₁.q + A.width) ≤ j := fun l hl => by
      have h0 := hj.2.1
      calc ((l : ℕ) + 1) * (C₁.q + A.width) ≤ (j / (C₁.q + A.width)) * (C₁.q + A.width) :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ j := Nat.div_mul_le_self j _
    have hc : A.reqCount lg ⟨j / (C₁.q + A.width) - 1, hj.2.2⟩ =
        A.reqCount lg' ⟨j / (C₁.q + A.width) - 1, hj.2.2⟩ :=
      congrArg List.length (requestsBefore_congr fun i hi => h i (hle i (by
        change (i : ℕ) < j / (C₁.q + A.width) - 1 at hi
        omega)))
    rw [hc, h _ (hle _ le_rfl)]
  · rfl

/-- **The requests of the request points before `k` read from absorbed logs.** -/
def histL (k : ℕ) (lg : LogReg Req A.slots) : LogReg Req₂ (bT A C₁ F kq + 1) :=
  fun j => if (j : ℕ) < k then some (reqL A C₁ F d₂ j lg) else none

/-- **The requests before `k + 1` read only the absorbed logs of the slots `l` with
`(l + 1) · (q + width) ≤ k`.** -/
theorem histL_congr (k : ℕ) {lg lg' : LogReg Req A.slots}
    (h : ∀ l : Fin A.slots, ((l : ℕ) + 1) * (C₁.q + A.width) ≤ k → lg l = lg' l) :
    histL A C₁ F d₂ kq (k + 1) lg = histL A C₁ F d₂ kq (k + 1) lg' := by
  funext j
  unfold histL
  split_ifs with hj
  · rw [reqL_congr A C₁ F d₂ j fun l hl => h l (by omega)]
  · rfl

/-- **The requests of the bridge's request points before `k`**, read from its work register (the
logs `ReqQueryAlg.hist`). -/
noncomputable def histW (k : ℕ) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) : LogReg Req₂ (bT A C₁ F kq + 1) :=
  fun j => if (j : ℕ) < k then some ((bridgeAlg e A C₁ F d₂ E kq d₀).req j w) else none

/-- `ReqQueryAlg.hist` of the bridge is `histW` of the work register. -/
theorem hist_eq_histW (k : ℕ)
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq)) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).hist k s = histW e A C₁ F d₂ E kq d₀ k s.1.1 :=
  rfl

/-- `histW` from the absorbed logs of the run of the composition. -/
theorem histW_eq_histL (k : ℕ) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    histW e A C₁ F d₂ E kq d₀ k w = histL A C₁ F d₂ kq k (cohLogs A C₁ F d₀ w.1) :=
  rfl

/-- **Writing a reply of the bridge keeps `goodW`.** -/
theorem bridge_write_goodW (k : Fin (bT A C₁ F kq + 1)) (x : Option Resp₂)
    (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) (hw : w ∈ goodW e A C₁ F d₂ E kq d₀ k) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).write k x w ∈ goodW e A C₁ F d₂ E kq d₀ k := by
  obtain ⟨hl, hf, ha⟩ := bridgeAlg_write_spec e A C₁ F d₂ E kq d₀ k x w
  obtain ⟨_ | k', hk⟩ := k
  · have hb := (mem_cohInit A C₁ F d₀).1 hw
    refine (mem_cohInit A C₁ F d₀).2 ⟨fun j => (congrFun hl j).trans (hb.1 j), hf.trans hb.2.1, ?_⟩
    rw [ha]
    exact hb.2.2
  · exact cohSet_congr A C₁ F d₀ hw hl hf ha fun x hx => absurd hx (Set.notMem_empty x)

variable [Nonempty (Bits m)]

/-- **Step `k` of the bridge carries `goodW k` to `goodW (k + 1)`.** -/
theorem bridge_step_goodW (hA : A.TracePreserving) (k : Fin (bT A C₁ F kq + 1))
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ goodW e A C₁ F d₂ E kq d₀ k} v) :
    Supported {r | r.1 ∈ goodW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1)}
      ((bridgeAlg e A C₁ F d₂ E kq d₀).step k v) := by
  obtain ⟨_ | k', hk⟩ := k
  · exact bridge_hstep0 e A C₁ F d₂ E kq d₀ hA v hv
  · exact bridgeStep_supp e A C₁ F d₂ E kq d₀ hA ∅ hk v hv

omit [Nonempty (Bits m)] in
/-- **The simulated run of the bridge's steps with the request points of the table `tab` starts on
`goodS 0`.** -/
theorem bridge_h0 (tab : A.OuterTab Req₂ Resp₂) :
    Supported (goodS e A C₁ F d₂ E kq d₀ 0)
      (ReqQueryAlg.preQ e (bridgeAlg e A C₁ F d₂ E kq d₀)
        (bridgeSteps e A C₁ F d₂ E kq d₀ tab) 0) := by
  intro s hs
  change (bridgeAlg e A C₁ F d₂ E kq d₀).init s.1 * _ = 0
  rw [bridge_init_supp e A C₁ F d₂ E kq d₀ s.1 hs, zero_mul]

omit [Nonempty (Bits m)] in
/-- The bridge's write with the reply of the table, on the work register. -/
theorem bridgeWrite_fst (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (r : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    (bridgeWrite e A C₁ F d₂ E kq d₀ tab k r).1 =
      (bridgeAlg e A C₁ F d₂ E kq d₀).write k (bridgeRep e A C₁ F d₂ E kq d₀ tab k r.1) r.1 :=
  rfl

/-- **A step of the bridge with the request point of the table `tab`, then the simulated query,
carries `goodS k` to `goodS (k + 1)`.** -/
theorem bridge_hG (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    ∀ (k : Fin (bT A C₁ F kq + 1)) q, (k : ℕ) < bT A C₁ F kq →
      Supported (goodS e A C₁ F d₂ E kq d₀ k) q →
      Supported (goodS e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1))
        (simQuery e (bridgeAlg e A C₁ F d₂ E kq d₀).W (bT A C₁ F kq)
          (controlled (fun _ => bridgeSteps e A C₁ F d₂ E kq d₀ tab k) q)) := by
  intro k q _ hq
  refine ReqQueryAlg.supported_simQuery_work
    (P := goodW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1)) ?_ e
  refine supported_controlled_workSet (S := goodW e A C₁ F d₂ E kq d₀ k) (fun v hv => ?_) hq
  rw [bridgeSteps, LinearIsometryEquiv.trans_apply]
  refine bridge_step_goodW e A C₁ F d₂ E kq d₀ hA k _ (hv.permOp fun r hr => ?_)
  change r.1 ∈ goodW e A C₁ F d₂ E kq d₀ k at hr
  rw [Set.mem_ofPred_eq, bridgeWrite_fst]
  exact bridge_write_goodW e A C₁ F d₂ E kq d₀ k _ r.1 hr

/-- **The supports of the run of the composition before step `k + 1` with the requests `l` of
the request points `0, …, k + 1`** (proof-internal): `cohSet ∅ k`, the requests read from the
absorbed logs. -/
def cohHist (k : ℕ) (l : LogReg Req₂ (bT A C₁ F kq + 1)) :
    Set ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) :=
  {c | c ∈ cohSet A C₁ F d₀ ∅ k ∧ histL A C₁ F d₂ kq (k + 2) (cohLogs A C₁ F d₀ c) = l}

/-- The registers of the run of the composition with the requests `l` of the request points
`0, …, k + 1` (proof-internal). -/
def histSet (k : ℕ) (l : LogReg Req₂ (bT A C₁ F kq + 1)) :
    Set ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) :=
  {c | histL A C₁ F d₂ kq (k + 2) (cohLogs A C₁ F d₀ c) = l}

/-- **Step `k + 1` of the run of the composition keeps the requests of the request points
`0, …, k + 1`** on `cohSet ∅ k`: the records `logRec` of query `k` hold those requests
(`histL_congr`), and the step keeps them (`stepAt_compiled_keepsAt`). -/
theorem cohStep_hist (hA : A.TracePreserving) {k : ℕ}
    (hk : k + 1 ≤ ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries)
    (l : LogReg Req₂ (bT A C₁ F kq + 1))
    (u : QState (QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ cohHist A C₁ F d₂ kq d₀ k l} u) :
    Supported {r | r.1 ∈ histSet A C₁ F d₂ kq d₀ k l}
      (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
        (extOut A C₁ F d₀ (tab₀ A))).toOracleAlg ∅).stepAt () (k + 1) u) := by
  have hv := A.valid_logS (F := F) (tab := tab₀ A) hA ∅ C₁
  have hc := A.keepsAt_logRec (F := F) (tab := tab₀ A) hA
    {lg | histL A C₁ F d₂ kq (k + 2) lg = l} C₁
  have hs := ReprogrammedCircuit.stepAt_compiled_keepsAt _ _ _ _ (extOut A C₁ F d₀ (tab₀ A)) hv hc
    (k := k + 1) (i := k) hk (Nat.lt_succ_self k) _ (Or.inl rfl) (v := u) (fun r hr => hu r fun h =>
      hr ⟨⟨cohLogs A C₁ F d₀ r.1, h.2, fun _ _ => rfl⟩, h.1.2.1, h.1.2.2 (by omega)⟩)
  refine hs.mono fun r hr => ?_
  obtain ⟨lg, hlg, hag⟩ := hr
  change histL A C₁ F d₂ kq (k + 1 + 1) (cohLogs A C₁ F d₀ r.1) = l
  rw [histL_congr A C₁ F d₂ kq (k + 1) fun l' hl' => hag l' ?_]
  · exact hlg
  · have hL : 0 < C₁.q + A.width := by
      have := A.width_pos
      omega
    change (l' : ℕ) * (C₁.q + A.width) ≤ k
    rw [add_mul, one_mul] at hl'
    omega

omit [Nonempty (Bits m)] in
/-- `cohHist` on the bridge's work register (proof-internal). -/
def cohHistW (k : ℕ) (l : LogReg Req₂ (bT A C₁ F kq + 1)) : Set (bridgeAlg e A C₁ F d₂ E kq d₀).W :=
  {w | w.1 ∈ cohHist A C₁ F d₂ kq d₀ k l}

omit [Nonempty (Bits m)] in
/-- `histSet` on the bridge's work register (proof-internal). -/
def histWSet (k : ℕ) (l : LogReg Req₂ (bT A C₁ F kq + 1)) : Set (bridgeAlg e A C₁ F d₂ E kq d₀).W :=
  {w | w.1 ∈ histSet A C₁ F d₂ kq d₀ k l}

/-- **Step `k + 1` of the bridge keeps the requests of the request points `0, …, k + 1`** on
`wSet ∅ k`: the run of the composition, lifted, then the classical steps of the expansion. -/
theorem bridge_step_hist_succ (hA : A.TracePreserving) {k : ℕ}
    (hk : k + 1 < (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth + kq) + 1)
    (l : LogReg Req₂ (bT A C₁ F kq + 1))
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ cohHistW e A C₁ F d₂ E kq d₀ k l} v) :
    Supported {r | r.1 ∈ histWSet e A C₁ F d₂ E kq d₀ k l}
      ((bridgeAlg e A C₁ F d₂ E kq d₀).step ⟨k + 1, hk⟩ v) := by
  have hD : ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth =
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries :=
    ReprogrammedCircuit.depth_compiledAlg _ _ _ _
  exact ExpandAdvSupp.expandAdv_stepAt_supp e E kq
    ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))))
    (S := cohHist A C₁ F d₂ kq d₀ k l) (S' := histSet A C₁ F d₂ kq d₀ k l) ⟨k + 1, hk⟩
    (fun hi u hu => cohStep_hist A C₁ F d₂ kq d₀ hA (by change k + 1 ≤ _ at hi; omega) l u hu)
    (fun _ _ hc => hc.2) hv

/-- **Step `k` of the bridge keeps the requests of the request points `0, …, k`** on `goodW k`. -/
theorem bridge_step_hist (hA : A.TracePreserving) (k : Fin (bT A C₁ F kq + 1))
    (l : LogReg Req₂ (bT A C₁ F kq + 1))
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ goodW e A C₁ F d₂ E kq d₀ k ∧
      histW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1) r.1 = l} v) :
    Supported {r | histW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1) r.1 = l}
      ((bridgeAlg e A C₁ F d₂ E kq d₀).step k v) := by
  obtain ⟨_ | k', hk⟩ := k
  · have hL : 0 < C₁.q + A.width := by
      have := A.width_pos
      omega
    have hc : ∀ w w', histW e A C₁ F d₂ E kq d₀ 1 w = histW e A C₁ F d₂ E kq d₀ 1 w' :=
      fun w w' => histL_congr A C₁ F d₂ kq 0 fun l' hl' => by
        have := Nat.mul_pos (show 0 < (l' : ℕ) + 1 by omega) hL
        omega
    by_cases hl : ∃ w, histW e A C₁ F d₂ E kq d₀ 1 w = l
    · obtain ⟨w₀, hw₀⟩ := hl
      intro r hr
      exact absurd ((hc r.1 w₀).trans hw₀) hr
    · have h0 : v = 0 := by
        ext r
        rw [hv r fun h => hl ⟨r.1, h.2⟩]
        rfl
      rw [h0, map_zero]
      exact fun _ _ => rfl
  · have hv' : Supported {r | r.1 ∈ cohHistW e A C₁ F d₂ E kq d₀ k' l} v :=
      fun r hr => hv r fun h => hr ⟨h.1, by
        have h2 := h.2
        rw [histW_eq_histL] at h2
        exact h2⟩
    refine (bridge_step_hist_succ e A C₁ F d₂ E kq d₀ hA hk l v hv').mono fun r hr => ?_
    change histW e A C₁ F d₂ E kq d₀ (k' + 1 + 1) r.1 = l
    rw [histW_eq_histL]
    exact hr

omit [Nonempty (Bits m)] in
/-- `goodS` reads the work register. -/
theorem mem_goodS (k : ℕ)
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq)) :
    s ∈ goodS e A C₁ F d₂ E kq d₀ k ↔ s.1.1 ∈ goodW e A C₁ F d₂ E kq d₀ k :=
  Iff.rfl

/-- **On `goodS k`, after the write of the request point `k` with the reply of the table `tab`,
the bridge's step `k` keeps the requests of the request points `0, …, k`** (`ReqQueryAlg.hist`),
for a trace-preserving adversary. -/
theorem bridge_hP (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    ∀ (k : Fin (bT A C₁ F kq + 1)) q, Supported (goodS e A C₁ F d₂ E kq d₀ k) q → ∀ l,
      Supported {s | (bridgeAlg e A C₁ F d₂ E kq d₀).hist ((k : ℕ) + 1) s = l}
        (ReqQueryAlg.stepSim (bridgeAlg e A C₁ F d₂ E kq d₀) k
          (mask {s | (bridgeAlg e A C₁ F d₂ E kq d₀).hist ((k : ℕ) + 1) s = l}
            (permOp ((bridgeAlg e A C₁ F d₂ E kq d₀).simPerm
              ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k (bridgeRep e A C₁ F d₂ E kq d₀ tab k)
                (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k))) q))) := by
  intro k q hq l
  have h1 : Supported (goodS e A C₁ F d₂ E kq d₀ k)
      (permOp ((bridgeAlg e A C₁ F d₂ E kq d₀).simPerm
        ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k (bridgeRep e A C₁ F d₂ E kq d₀ tab k)
          (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k))) q) := by
    refine hq.permOp fun s hs => ?_
    rw [mem_goodS] at hs ⊢
    rw [ReqQueryAlg.simPerm_ctrlWrite_fst]
    exact bridge_write_goodW e A C₁ F d₂ E kq d₀ k _ s.1.1 hs
  have h2 : Supported (workSet (bridgeAlg e A C₁ F d₂ E kq d₀).W (bT A C₁ F kq)
      {w | w ∈ goodW e A C₁ F d₂ E kq d₀ k ∧ histW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1) w = l})
      (mask {s | (bridgeAlg e A C₁ F d₂ E kq d₀).hist ((k : ℕ) + 1) s = l}
        (permOp ((bridgeAlg e A C₁ F d₂ E kq d₀).simPerm
          ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k (bridgeRep e A C₁ F d₂ E kq d₀ tab k)
            (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k))) q)) := by
    intro s hs
    rw [mask_apply]
    by_cases h : (bridgeAlg e A C₁ F d₂ E kq d₀).hist ((k : ℕ) + 1) s = l
    · rw [Set.indicator_of_mem (show s ∈ {s | (bridgeAlg e A C₁ F d₂ E kq d₀).hist ((k : ℕ) + 1) s = l} from h)]
      refine h1 s fun h' => hs ⟨(mem_goodS e A C₁ F d₂ E kq d₀ _ s).1 h', ?_⟩
      rw [← hist_eq_histW]
      exact h
    · exact Set.indicator_of_notMem
        (show s ∉ {s | (bridgeAlg e A C₁ F d₂ E kq d₀).hist ((k : ℕ) + 1) s = l} from h) _
  have h3 := supported_controlled_workSet
    (S := {w | w ∈ goodW e A C₁ F d₂ E kq d₀ k ∧ histW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1) w = l})
    (S' := {w | histW e A C₁ F d₂ E kq d₀ ((k : ℕ) + 1) w = l})
    (U := (bridgeAlg e A C₁ F d₂ E kq d₀).step k)
    (fun v hv => bridge_step_hist e A C₁ F d₂ E kq d₀ hA k l v hv) h2
  rw [ReqQueryAlg.stepSim]
  refine h3.mono fun s hs => ?_
  rw [Set.mem_ofPred_eq, hist_eq_histW]
  exact hs

end Bridge

end GordieHowe.Quantum
