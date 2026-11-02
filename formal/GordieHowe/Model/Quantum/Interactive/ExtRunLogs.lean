-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeSlots
public import GordieHowe.Model.Quantum.Interactive.LogInvRaw
public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Model.QROM.Lifting

@[expose] public section

/-!
# The workspaces of the expanded coherent extraction run

For an adversary `Z` and sets `S` of the workspaces of its trace-preserving form carried by its
steps (`AdaptiveIAlg.WsInv`), on every basis state of nonzero amplitude of the compressed-oracle
simulation of the expanded coherent run of its composition with a challenger (the form of the
simulation-extraction run `extAdv`, `GordieHowe/SPBCS/SimExtract.lean`), the composed registers'
workspace lies in `S (slots + post + 1)` and the halting flag is down. This is the support argument
of `bridgeAlg_slotLogs` (`GordieHowe/Model/Quantum/Interactive/ReqBridgeSlots.lean`) for any
adversary and output map, without the bridge's request points.

- `ExpandAdvSupp.expandAdv_stepAt_succ_supp`: a step of the expanded adversary in the form of
  `QueryAlg.supported_simStage_of`.
- `AdaptiveIAlg.WsInv`; `AdaptiveIAlg.extCohSet`, `AdaptiveIAlg.extCohInit` (proof-internal).
- `AdaptiveIAlg.expandAdv_wsInv`: the statement; `AdaptiveIAlg.simProb_expandAdv_wsInv`: its
  probability form.
- `MultiRelay.idle_or_canAsk_of_act`, `MultiRelay.AsksAt.idle_or_canAsk`,
  `AdaptiveIAlg.LogInvRaw.mapOut`, `AdaptiveIAlg.LogsAsk`, `AdaptiveIAlg.logsAsk_of_relayFull`,
  `AdaptiveIAlg.relayAdv_logInvRaw_ask`: every logged request of the relayed adversary satisfying a
  test is one the program of a request in the relay's record can make, on every step's support.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace ExpandAdvSupp

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (e : Y ≃ B) (E : Expansion X B C) (k : ℕ)

/-- **Step `i + 1` of the expanded adversary carries `S i` to `S (i + 1)`**
(`expandAdv_step_supp` in the form of `QueryAlg.supported_simStage_of`). -/
theorem expandAdv_stepAt_succ_supp {t : ℕ} (𝒜 : QueryAlg X Y t C) (S : ℕ → Set 𝒜.W)
    (hstep : ∀ i, i + 1 ≤ t → ∀ u, Supported {r | r.1 ∈ S i} u →
      Supported {r | r.1 ∈ S (i + 1)} ((𝒜.toOracleAlg ∅).stepAt () (i + 1) u))
    (hmono : ∀ i, t ≤ i → S i ⊆ S (i + 1)) {i : ℕ} (hi : i < t + k)
    {v : QState (QueryReg (expandAdv e E k 𝒜).W 1 X Y)}
    (hv : Supported {r | r.1 ∈ {w : (expandAdv e E k 𝒜).W | w.1 ∈ S i}} v) :
    Supported {r | r.1 ∈ {w : (expandAdv e E k 𝒜).W | w.1 ∈ S (i + 1)}}
      (((expandAdv e E k 𝒜).toOracleAlg ∅).stepAt () (i + 1) v) := by
  rw [OracleAlg.stepAt_of_lt _ (by omega)]
  exact expandAdv_step_supp e E k 𝒜 S hstep hmono (by omega) hv

end ExpandAdvSupp

namespace AdaptiveIAlg

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {m : ℕ} {I J B C : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (e : BitStr I J ≃ B) {shZ : AlgShape (Bits m) (BitStr I J) Req Resp} (Z : AdaptiveIAlg shZ O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req Resp)
  (E : Expansion (Bits m) B C) (kq : ℕ) (g : Option (Z.toTPKindAlg.CW C₁) → C)
  (S : ℕ → Set Z.toTPKindAlg.W)

set_option quotPrecheck false in
/-- The coherent run of the composition with `C₁`, its output read through `g`. -/
local notation "cohR" => ((Z.toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut g)

/-- **Sets of the workspaces of the trace-preserving form carried by the steps**: the initial
workspaces lie in `S 0`, the step of slot `j` carries `S j` into `S (j + 1)`, and each step `k`
after the slots carries `S k` into `S (k + 1)`. -/
structure WsInv : Prop where
  /-- The initial workspaces lie in `S 0`. -/
  init : ∀ d d', (Z.toTPKindAlg.init).mat d d' ≠ 0 → d.workspace ∈ S 0
  /-- The step of slot `j` carries `S j` into `S (j + 1)`. -/
  slot : ∀ (j : Fin Z.slots) z (y x : DReg Z.toTPKindAlg.W Z.width (Bits m) (BitStr I J) Req Resp),
    (Z.toTPKindAlg.step (slotStep j)).op z y x ≠ 0 → x.workspace ∈ S j →
      y.workspace ∈ S (j + 1)
  /-- The step `k` after the slots carries `S k` into `S (k + 1)`. The sets are indexed by the
  step: re-applying a step need not keep a set (re-applying the relay's last step can wrap its
  clock), so a set kept by every step after the slots would lose what the last step gives. -/
  post : ∀ (k : StepIdx Z.slots Z.post), Z.slots ≤ (k : ℕ) →
    ∀ z (y x : DReg Z.toTPKindAlg.W Z.width (Bits m) (BitStr I J) Req Resp),
    (Z.toTPKindAlg.step k).op z y x ≠ 0 → x.workspace ∈ S k → y.workspace ∈ S (k + 1)

/-- **The supports of the run of the composition after step `k`** (proof-internal). -/
def extCohSet (k : ℕ) : Set (cohR).W :=
  {c | c.1.1.1 ∈ ReprogrammedCircuit.segOut (Z.toTPKindAlg.wsG C₁ S)
      (Z.toTPKindAlg.advIn C₁ (S (Z.slots + Z.post + 1))) 0
      (Z.toTPKindAlg.fullCircBoth C₁).queries k ∧
    c.1.2 = false ∧
    (k < (Z.toTPKindAlg.fullCircBoth C₁).queries → MixedAlg.Clean (k + 1) c.2)}

/-- **The supports of the run of the composition at the start** (proof-internal). -/
def extCohInit : Set (cohR).W :=
  {c | c.1.1.1 ∈ Z.toTPKindAlg.advIn C₁ (S 0) ∧ c.1.2 = false ∧ MixedAlg.Clean 0 c.2}

variable {Z C₁ S}

/-- The certificate of the composition through the sets `S` (proof-internal). -/
theorem valid_wsInv (hS : Z.WsInv S) :
    ReprogrammedCircuit.Valid (fun _ => Set.univ) (Z.toTPKindAlg.wsG C₁ S)
      (Z.toTPKindAlg.fullCircBoth C₁) 0 (Z.toTPKindAlg.advIn C₁ (S 0))
      (Z.toTPKindAlg.advIn C₁ (S (Z.slots + Z.post + 1))) :=
  KindAlg.valid_fullCircBoth_ws S Z.stepsTP_toTPKindAlg hS.slot hS.post

/-- **A step of the run of the composition carries `extCohSet k` to `extCohSet (k + 1)`**
(proof-internal). -/
theorem extCohStep_supp (hS : Z.WsInv S) {k : ℕ}
    (hk : k + 1 ≤ (Z.toTPKindAlg.fullCircBoth C₁).queries)
    (u : QState (QueryReg (cohR).W 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ Z.extCohSet C₁ g S k} u) :
    Supported {r | r.1 ∈ Z.extCohSet C₁ g S (k + 1)}
      (((cohR).toOracleAlg ∅).stepAt () (k + 1) u) := by
  refine stepAt_composeBothOut_supp _ _ _ (valid_wsInv hS) hk ?_
  refine fun r hr => hu r fun h => hr ?_
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3 (by omega)⟩
  have e1 : ReprogrammedCircuit.segOut (Z.toTPKindAlg.wsG C₁ S)
      (Z.toTPKindAlg.advIn C₁ (S (Z.slots + Z.post + 1))) 0
      (Z.toTPKindAlg.fullCircBoth C₁).queries k =
      Z.toTPKindAlg.wsG C₁ S (0 + k) := by
    unfold ReprogrammedCircuit.segOut
    rw [ite_eq_left (by omega)]
  rw [e1] at h1
  exact h1

/-- After the composition's last query, `extCohSet` only grows (proof-internal). -/
theorem extCohSet_mono_of_le {k : ℕ} (hk : (Z.toTPKindAlg.fullCircBoth C₁).queries ≤ k) :
    Z.extCohSet C₁ g S k ⊆ Z.extCohSet C₁ g S (k + 1) := by
  rintro c ⟨h1, h2, -⟩
  refine ⟨?_, h2, fun h => absurd h (by omega)⟩
  unfold ReprogrammedCircuit.segOut at h1 ⊢
  rw [ite_eq_right (by omega)] at h1
  rw [ite_eq_right (by omega)]
  exact h1

/-- **The initial state of the composition has its workspace in `S 0`** (proof-internal). -/
theorem initSys_wsInv (hS : Z.WsInv S) (p : QueryReg (Z.toTPKindAlg.CW C₁) 1 (Bits m) (BitStr I J))
    (hp : (Z.toTPKindAlg.initSys C₁).mat p p ≠ 0) : p.1 ∈ Z.toTPKindAlg.advIn C₁ (S 0) := by
  change (∑ ω, (_ : ℂ) • (MState.reindex (Z.toTPKindAlg.advSplit C₁)
    ((Z.toTPKindAlg.init).tensorKet _)).mat) p p ≠ 0 at hp
  rw [Matrix.sum_apply] at hp
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  rw [Matrix.smul_apply, smul_eq_mul] at hω
  have h2 := right_ne_zero_of_mul hω
  rw [MState.reindex_tensorKet_mat] at h2
  obtain ⟨d, d', hd, -, hdd⟩ := embed_ne_zero_exists h2
  subst hd
  exact hS.init d d' hdd

/-- **The initial state of the run of the composition lies on `extCohInit`** (proof-internal). -/
theorem extCohInit_supp (hS : Z.WsInv S) :
    Supported {r : QueryReg (cohR).W 1 (Bits m) (BitStr I J) | r.1 ∈ Z.extCohInit C₁ g S}
      (cohR).init :=
  (GordieHowe.QROM.compiled_init_props (initSys_wsInv hS)).1.mono
      fun _ hr => ⟨hr.2.2.2, hr.2.1, hr.2.2.1⟩

/-- **The first step of the run of the composition carries `extCohInit` into `extCohSet 0`**
(proof-internal). -/
theorem extCohInit_step0 (hS : Z.WsInv S) (u : QState (QueryReg (cohR).W 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ Z.extCohInit C₁ g S} u) :
    Supported {r | r.1 ∈ Z.extCohSet C₁ g S 0} (((cohR).toOracleAlg ∅).stepAt () 0 u) := by
  refine stepAt_composeBothOut_supp _ _ _ (valid_wsInv hS) (Nat.zero_le _) ?_
  refine fun r hr => hu r fun h => hr ?_
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩


/-- **The workspaces of the expanded coherent run** (module docstring): for sets `S` of the
workspaces of the trace-preserving form carried by its steps (`hS`), on every basis state of
nonzero amplitude of the compressed-oracle simulation of the expanded coherent run of the
composition with `C₁`, the composed registers' workspace lies in `S (slots + post + 1)` and the
halting flag is down. -/
theorem expandAdv_wsInv (hS : Z.WsInv S)
    {b : SimRegister (expandAdv e E kq (cohR)).W I J m
      ((Z.toTPKindAlg.composeBothOut C₁ id).depth + kq)}
    (hb : simState e (expandAdv e E kq (cohR)) b ≠ 0) :
    b.1.1.1.1.1.1.adv.workspace ∈ S (Z.slots + Z.post + 1) ∧ b.1.1.1.1.2 = false := by
  have hD : (Z.toTPKindAlg.composeBothOut C₁ id).depth = (Z.toTPKindAlg.fullCircBoth C₁).queries :=
    ReprogrammedCircuit.depth_compiledAlg _ _ _ _
  have hs := QueryAlg.supported_simStage_of e (expandAdv e E kq (cohR))
    (fun k => {w | w.1 ∈ Z.extCohSet C₁ g S k}) ?_ ?_ le_rfl
  · have hmem : b.1.1.1 ∈ Z.extCohSet C₁ g S ((Z.toTPKindAlg.composeBothOut C₁ id).depth + kq) := by
      by_contra h
      exact hb (hs b h)
    obtain ⟨h1, hflag, -⟩ := hmem
    unfold ReprogrammedCircuit.segOut at h1
    rw [ite_eq_right (by omega)] at h1
    exact ⟨h1, hflag⟩
  · rw [OracleAlg.stepAt_of_lt _ (by omega)]
    exact ExpandAdvSupp.expandAdv_step0_supp e E kq _ (extCohInit_step0 g hS)
      (ExpandAdvSupp.supported_embed kq (extCohInit_supp g hS))
  · intro k hk v hv
    exact ExpandAdvSupp.expandAdv_stepAt_succ_supp e E kq _ (Z.extCohSet C₁ g S)
      (fun i hi u hu => extCohStep_supp g hS (hD ▸ hi) u hu)
      (fun i hi => extCohSet_mono_of_le g (hD ▸ hi)) hk hv

/-- **The events of the expanded coherent run hold with a workspace in `S (slots + post + 1)`**:
for sets `S` carried by the steps (`hS`), every event `W` of the output has at most the
probability of `W` together with the output being `g (some v)` for composed registers `v` whose
workspace lies in `S (slots + post + 1)` (`expandAdv_wsInv`). -/
theorem simProb_expandAdv_wsInv [Fintype B] [DecidableEq B] (hS : Z.WsInv S)
    (W : C → DB (Bits m) B → Prop) :
    simProb e (expandAdv e E kq (cohR)) W ≤
      simProb e (expandAdv e E kq (cohR)) fun o D => W o D ∧
        ∃ v : Z.toTPKindAlg.CW C₁, v.adv.workspace ∈ S (Z.slots + Z.post + 1) ∧ g (some v) = o := by
  unfold simProb simLaw
  rw [MeasureTheory.OuterMeasure.map_apply, MeasureTheory.OuterMeasure.map_apply,
    bornWeight_apply_eq_sum, bornWeight_apply_eq_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hv : simState e (expandAdv e E kq (cohR)) b = 0
  · simp [Set.indicator, hv]
  · by_cases hb : b ∈ (fun b => ((expandAdv e E kq (cohR)).out b.1.1, slotsDB e b.2)) ⁻¹'
        {p | W p.1.out p.2}
    · obtain ⟨h1, h2⟩ := expandAdv_wsInv e E kq g hS hv
      have hb' : b ∈ (fun b => ((expandAdv e E kq (cohR)).out b.1.1, slotsDB e b.2)) ⁻¹'
          {p | W p.1.out p.2 ∧ ∃ v : Z.toTPKindAlg.CW C₁,
            v.adv.workspace ∈ S (Z.slots + Z.post + 1) ∧
            g (some v) = p.1.out} := by
        refine ⟨hb, b.1.1.1.1.1.1, h1, ?_⟩
        change g (some b.1.1.1.1.1.1) = g (Alg.haltOutCoh _ b.1.1.1)
        simp only [Alg.haltOutCoh, h2]
        rfl
      rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb']
    · rw [Set.indicator_of_notMem hb]
      exact bot_le

/-- Reading the output through a map keeps the Kraus operators of the trace-preserving form. -/
theorem mapOut_toTPKindAlg_op {O' : Type} (f : O → O')
    (k : StepIdx (Z.mapOut f).slots (Z.mapOut f).post) :
    ((Z.mapOut f).toTPKindAlg.step k).op = (Z.toTPKindAlg.step k).op := by
  funext x
  rcases x with r | r | c <;> rfl

/-- **Sets carried by the absorbed steps are carried by the steps of the absorbed adversary with its
output read through a map**, as sets of its workspaces. -/
theorem LogInv.wsInv [Inhabited Req] {Req₁ Resp₁ Req₂ Resp₂ O' : Type} [Fintype Req₁]
    [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] [Fintype Req₂]
    [DecidableEq Req₂]
    [Fintype Resp₂] [DecidableEq Resp₂] {shA : AlgShape (Bits m) (BitStr I J) Req₁ Resp₁} {A : AdaptiveIAlg shA O}
    {F : TwoRelay Req₁ Resp₁ Req Resp Req₂ Resp₂} {tab : A.OuterTab Req₂ Resp₂}
    {T : ℕ → Set ((A.W × Req₁) × LogReg Req₁ A.slots)} (hT : A.LogInv F tab T) (f : O → O') :
    ((A.absorbTab F tab).mapOut f).WsInv fun n =>
      {w | ((w.1.1.work, w.1.1.request), w.1.1.logs) ∈ T n} :=
  ⟨hT.init, fun j z y x h₀ hx => hT.slot j z y x (fun h => h₀
      ((congrFun (congrFun (congrFun (mapOut_toTPKindAlg_op (Z := A.absorbTab F tab) f
        (slotStep j)) z) y) x).trans h)) hx,
    fun k hk z y x h₀ hx => hT.post k hk z y x (fun h => h₀
      ((congrFun (congrFun (congrFun (mapOut_toTPKindAlg_op (Z := A.absorbTab F tab) f k) z) y)
        x).trans h)) hx⟩

end AdaptiveIAlg


/-! ### The logged asks of the relayed adversary -/

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys]

omit [Zero Y] [Zero Ys] in
/-- **A main request of the action of a sub-slot** is the idle request or one the program can
make. -/
theorem idle_or_canAsk_of_act {r : Req} {st : RelaySt Y Resp' Ys} {r' : Req'}
    (hfit : OracleProg.AnsFit F.side (F.prog r) st.ans)
    (h : F.act r st = .inr r') : r' = F.idle ∨ F.CanAsk r r' := by
  unfold act at h
  rcases hp : F.progAct r st with _ | ((x | x) | r'')
  · rw [hp] at h
    simp only at h
    split_ifs at h
    · exact .inl (Sum.inr.inj h).symm
  · rw [hp] at h
    simp at h
  · rw [hp] at h
    simp only at h
    split_ifs at h
    · exact .inl (Sum.inr.inj h).symm
  · rw [hp] at h
    simp only [Sum.inr.injEq] at h
    subst h
    exact .inr (F.canAsk_of_progAct hfit hp)

/-- **An ask of a relayed request is the idle request or one the program of a started request can
make**, the started request read at an index `i` of the record, for a side store read from the
record (`MultiRelay.consSide`) at a clock `T ≥ t`. -/
theorem AsksAt.idle_or_canAsk [Inhabited Req'] {n b Q : ℕ} {m S : ℕ}
    {rec : Fin m → Option (Option Req)} {store : Fin S → Option Resp' × (X × Y)} {t T : ℕ}
    {r' : Req'} (h : F.AsksAt n b Q (recList rec) store (F.consSide n b Q rec store T) t r')
    (ht : t ≤ T) :
    ∃ i r, (recList rec).getD i none = some r ∧ (r' = F.idle ∨ F.CanAsk r r') := by
  obtain ⟨i, r, hi, hr, hb, h1, h2, ha⟩ := h
  rw [F.stAt_vecSa_consSide n b Q store T (lt_of_getD_eq_some hr) hb hr
    (le_min (by omega) (by omega))] at ha
  exact ⟨i, r, hr, F.idle_or_canAsk_of_act (F.ansFit_stAt r _ _) ha⟩

end MultiRelay

namespace AdaptiveIAlg

section Asks

open Classical

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {Req' Resp' : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']

/-- **Sets carried by the adversary's steps are carried by the adversary with its output read
through a map.** -/
theorem LogInvRaw.mapOut {O' : Type} {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O}
    {T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)} (hT : A.LogInvRaw T) (g : O → O') :
    (A.mapOut g).LogInvRaw T :=
  ⟨hT.init, hT.slot, hT.post⟩

variable {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y] {O' : Type} [Inhabited X]
  [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ) (out' : A.RelayWS F → O')
  (p : Req' → Bool)

/-- **Every logged request satisfying `p` is one the program of a recorded request can make**
(proof-internal): for every logged `r'` with `p r'`, some entry `r` of the relay's record with
`F.CanAsk r r'`. -/
def LogsAsk (x : ((A.relayAdv F Q out').W × Req') × LogReg Req' (A.relayAdv F Q out').slots) :
    Prop :=
  ∀ j r', x.2 j = some r' → p r' = true →
    ∃ i r, (MultiRelay.recList x.1.1.1.record).getD i none = some r ∧ F.CanAsk r r'

/-- **The bookkeeping gives `LogsAsk`**, when the idle request fails `p`. -/
theorem logsAsk_of_relayFull (hpi : p F.idle = false) {t : ℕ} {x}
    (hx : x ∈ A.RelayFull F Q out' p t) : A.LogsAsk F Q out' p x := by
  rcases t with _ | t
  · obtain ⟨-, -, -, hl, -⟩ := hx
    intro j r' hj
    rw [hl j] at hj
    exact absurd hj (by simp)
  · obtain ⟨es, ht, hrec, -, hbl, hask, hs⟩ := hx
    intro j' r' hj hp
    have hl : MultiRelay.recList x.1.1.1.record = es := by
      rw [hrec.2.1]
      exact MultiRelay.recList_getElem? es hrec.1
    have hle : (j' : ℕ) ≤ x.1.1.1.time := by
      rw [ht]
      by_contra hlt
      rw [hbl j' (by omega)] at hj
      exact absurd hj (by simp)
    have hA := hask j' r' hj hp
    rw [← hl, hs] at hA
    obtain ⟨i, r₀, hi, hr₀⟩ := MultiRelay.AsksAt.idle_or_canAsk F hA hle
    rcases hr₀ with he | hc
    · rw [he, hpi] at hp
      exact absurd hp Bool.false_ne_true
    · exact ⟨i, r₀, hi, hc⟩

/-- **The relayed adversary's own steps carry `RelayFull` together with `LogsAsk`**, when the blank
and the idle requests fail `p`: every logged request satisfying `p` is one the program of a
request recorded by the relay can make, on every step's support. -/
theorem relayAdv_logInvRaw_ask (hpd : p default = false) (hpi : p F.idle = false) :
    (A.relayAdv F Q out').LogInvRaw fun t =>
      {x | x ∈ A.RelayFull F Q out' p t ∧ A.LogsAsk F Q out' p x} := by
  have hR := A.relayAdv_logInvRaw F Q out' p hpd hpi
  refine ⟨fun c c' h => ?_, fun j r a b lx ly h hlog hx => ?_, fun k hk r a b lx h hx => ?_⟩
  · have h' := hR.init c c' h
    exact ⟨h', A.logsAsk_of_relayFull F Q out' p hpi h'⟩
  · have h' := hR.slot j r a b lx ly h hlog hx.1
    exact ⟨h', A.logsAsk_of_relayFull F Q out' p hpi h'⟩
  · have h' := hR.post k hk r a b lx h hx.1
    exact ⟨h', A.logsAsk_of_relayFull F Q out' p hpi h'⟩

end Asks

end AdaptiveIAlg

end GordieHowe.Quantum
