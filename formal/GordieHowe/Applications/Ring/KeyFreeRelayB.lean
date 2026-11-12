-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeRelayOmega
public import GordieHowe.Model.Quantum.Interactive.AbsorbAssignSwap

@[expose] public section

/-!
# The key-free relay in side-read mode

For a key-free signer factoring through the base component and a public part (`KFSignFactors`),
whose public part and signature `F.out` are the run of a program `outB` over the base component
(`KFSignFactors.outB`), and a statement program over the base component (`KFStmt`), the key-free
relay over base reads (`kfRelayOn`, `GordieHowe/Applications/Ring/KeyFreeRelay.lean`) in
side-read mode (`KFReads.viaSide`) at the base component `ω`, `kfRelaySide ω`, makes those reads
as side reads of `ω`, the table in force read by the side reads themselves; its programs do not
depend on `ω`. It agrees with the key-free relay `kfRelay` at every oracle of base component `ω`
(`agreeAt_kfRelaySide`, `AssignRelay.AgreeAt`).

- `baseOf`, `prfOf`, `baseL`, `run_baseL`, `trace_baseL`, `ωT_eq`, `ωT_overT`: the plumbing.
- `sgnB`, `stpB`: the signer and the statement program over full and base reads. On refusal the
  signer makes the same reads as on acceptance, discarding them.
- `noTrailingSides_kfRelaySide`: its relay makes no trailing side reads.
- `sgnB_reads`, `sigK_sgnB_reads`, `xK_stpB_reads`, `kfProgK_viaSide_reads`, `kfRelaySide`: the
  relay (one oracle read, `qOut + qSt` side reads, one pad sub-slot, one main request).
- `run_sigK_sgnB`, `run_xK_stpB`, `agreeAt_kfRelaySide`, `run_elimProg_kfRelaySide`,
  `mainOf_kfRelaySide`, `elimSide_lift_xK_stpB`: the runs and the agreement.
- `kfAsg`, `KFEntryFrom`, `KFTableFacts`, `kfEntryFrom_of_tableFrom`, `kfTableFacts_of_explains`,
  `reqOf_of_explains`: the origin of the absorbed tables and main requests in `F.out`.
-/

namespace GordieHowe

open Quantum Signature QROM OracleProg RingSignature.OracleSplit

namespace RingSignature.KeyFree

open RingSignature.Insider

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : OracleSplit Y Y₁ Y₂)

/-! ### Plumbing -/

/-- The base component of an answer to a full read or a base read. -/
def baseOf : Y ⊕ Y₁ → Y₁
  | .inl y => (sp y).1
  | .inr y₁ => y₁

/-- The second component of an answer to a full read (`0` for a base read). -/
def prfOf : Y ⊕ Y₁ → Y₂
  | .inl y => (sp y).2
  | .inr _ => 0

/-- **A program over the base component as base reads.** -/
def baseL {α : Type} (p : OracleProg X Y₁ α) : OracleProg (X ⊕ X) (Y ⊕ Y₁) α :=
  translate Sum.inr (fun _ b => baseOf sp b) p

/-- `baseL p` runs as `p` at the base component answering its base reads. -/
theorem run_baseL {α : Type} (p : OracleProg X Y₁ α) (o : X ⊕ X → Y ⊕ Y₁) :
    (baseL sp p).run o = p.run fun x => baseOf sp (o (.inr x)) := by
  rw [baseL, run_translate]

/-- The reads of `baseL p` are `p`'s, as base reads. -/
theorem trace_baseL {α : Type} (p : OracleProg X Y₁ α) (o : X ⊕ X → Y ⊕ Y₁) :
    (baseL sp p).trace o = (p.trace fun x => baseOf sp (o (.inr x))).map Sum.inr := by
  rw [baseL, trace_translate]

/-- **The base component read through the table in force** is `ωT ω T`. -/
theorem ωT_eq (ω : X → Y₁) (T : X → Option Y) :
    (fun x => ((T x).map fun y => (sp y).1).getD (ω x)) = ωT sp ω T :=
  funext fun x => by cases hT : T x <;> simp [ωT, hT]

/-- **The base component read through a table and then through assignments `L`** is the base
component read through the table overridden by `L`. -/
theorem ωT_overT (ω : X → Y₁) (T L : X → Option Y) :
    (fun x => ((L x).map fun y => (sp y).1).getD (ωT sp ω T x)) = ωT sp ω (overT T L) :=
  funext fun x => by cases hL : L x <;> simp [ωT, overT, hL]

/-! ### The program -/

variable [DecidableEq X] {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
  (B : BaseSigner X Y N TS RMsg)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {SC X₀ R Pb : Type}
  (pks : Fin n → B.PK)
  {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))}
  (F : KFSignFactors sp Pb ksign) {stmtPω : (X → Y₁) → RingStmt B → X₀}
  (S : KFStmt stmtPω)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ}
  (sc : Fin Q → SC) [Inhabited X] [Inhabited B.Pub]

/-- **The key-free signer over base reads**: the public part, the signature, the kept point, the
published value and the assignments by `outB` over base reads; on a public part, a full read at
the kept point, and the assignments from its second component. On refusal the signer makes the
same reads as on acceptance, discarding them, so its control flow does not depend on its coins: a
full read at `default`, then the statement program over base reads at the statement
`⟨Rg, m, default⟩`. -/
def sgnB (pk : B.PK) (Rg : KeyRing B.PK N) (c : ℕ) (m : B.Msg) (s : SC) :
    OracleProg (X ⊕ X) (Y ⊕ Y₁) (Option (B.Pub × B.BSig × List (Assignment X Y))) :=
  (baseL sp (F.outB pk Rg c m s)).bind fun o =>
    match o with
    | none => .query (.inl default) fun _ =>
        (baseL sp (S.stmtPB ⟨Rg, m, default⟩)).mapOutput fun _ => none
    | some (q, kp) => .query (.inl kp.1) fun y => .pure (some (kp.2.1, q.2, kp.2.2 (prfOf sp y)))

/-- **The statement program over base reads.** -/
def stpB (x : RingStmt B) : OracleProg (X ⊕ X) (Y ⊕ Y₁) X₀ :=
  baseL sp (S.stmtPB x)

variable {sp B F S}

omit [DecidableEq X] [DecidableEq TS.PK] in
/-- The full and base reads of the signer: one full read, `qOut` base reads, and `qSt` more on
refusal. -/
theorem sgnB_reads (pk : B.PK) (Rg : KeyRing B.PK N) (c : ℕ) (msg : B.Msg) (s : SC)
    (o : X ⊕ X → Y ⊕ Y₁) :
    (((sgnB sp B F S pk Rg c msg s).trace o).filter Sum.isLeft).length ≤ 1 ∧
      (((sgnB sp B F S pk Rg c msg s).trace o).filter Sum.isRight).length ≤
        F.qOut + if (sgnB sp B F S pk Rg c msg s).run o = none then S.qSt else 0 := by
  rw [sgnB, trace_bind, run_bind, trace_baseL, run_baseL]
  have h1 := F.outB_queries pk Rg c msg s (fun x => baseOf sp (o (.inr x)))
  generalize (F.outB pk Rg c msg s).run (fun x => baseOf sp (o (.inr x))) = r
  rcases r with _ | ⟨q, kp⟩
  · have h2 := S.stmtPB_queries ⟨Rg, msg, default⟩
      (fun x => baseOf sp (o (.inr x)))
    simp only [trace_query, mapOutput, trace_bind, trace_baseL, trace_pure, run_query, run_bind,
      run_pure, List.append_nil, List.filter_append, List.filter_map, List.length_append,
      List.length_map, List.filter_cons, Function.comp_def, Sum.isLeft_inl, Sum.isRight_inl,
      Sum.isLeft_inr, Sum.isRight_inr, ↓reduceIte, Bool.false_eq_true, List.filter_false,
      List.filter_true, List.length_nil, List.length_cons, reduceCtorEq]
    simp [Function.comp_def, trace, mapOutput, trace_bind, trace_baseL, run_bind, List.filter_cons]
    omega
  · simp only [trace_query, trace_pure, run_query, run_pure, List.filter_append, List.filter_map,
      List.length_append, List.length_map]
    simp [Function.comp_def, List.filter_cons]
    omega

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- The signature over base reads: one full read, `qOut` base reads, and `qSt` more on refusal. -/
theorem sigK_sgnB_reads (c : ℕ) (r : Req B PS adm n) (o : X ⊕ X → Y ⊕ Y₁) :
    (((sigK B pks sc (sgnB sp B F S) c r).trace o).filter Sum.isLeft).length ≤ 1 ∧
      (((sigK B pks sc (sgnB sp B F S) c r).trace o).filter Sum.isRight).length ≤
        F.qOut + if (sigK B pks sc (sgnB sp B F S) c r).run o = none then S.qSt else 0 := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · simp [sigK]
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigK, dite_eq_left_of_eq_true (eq_true hc)]
      exact sgnB_reads _ _ _ _ _ o
    · rw [sigK, dite_eq_right_of_eq_false (eq_false hc)]
      simp [trace]
  · simp [sigK]

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- The statement program over base reads makes no full read and at most `qSt` base reads. -/
theorem xK_stpB_reads (r : Req B PS adm n) (o' : Option (B.Pub × B.BSig × List (Assignment X Y)))
    (o : X ⊕ X → Y ⊕ Y₁) :
    (((xK B (stpB sp B S) r o').trace o).filter Sum.isLeft).length = 0 ∧
      (((xK B (stpB sp B S) r o').trace o).filter Sum.isRight).length ≤ S.qSt := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o' with _ | p
  all_goals try (simp [xK]; done)
  simp only [xK, stpB, trace_mapOutput, trace_baseL, List.filter_map, List.length_map,
    Function.comp_def, Sum.isLeft_inr, Sum.isRight_inr, List.filter_false, List.filter_true,
    List.length_nil, true_and]
  exact S.stmtPB_queries _ _

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The reads of the key-free relay program in side-read mode**: one oracle read, `qOut + qSt`
side reads. -/
theorem kfProgK_viaSide_reads (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (h : X → Y) (m : MURequest (SignOracle.none B.core) n ⊕ R → Option (MUResponse B.core ⊕ Pf)) :
    (((kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r).trace
        (combineAns (MultiRelay.sideOracle h (KFReads.viaSide (fun y => (sp y).1) ω).side)
          m)).filter isRead).length ≤ 1 ∧
      (((kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r).trace
        (combineAns (MultiRelay.sideOracle h (KFReads.viaSide (fun y => (sp y).1) ω).side)
          m)).filter isSideRead).length ≤ F.qOut + S.qSt := by
  simp only [kfProgK, trace_bind, trace_lift_viaSide, run_lift_viaSide, List.filter_append,
    List.length_append, length_filter_isRead_map_viaSide, length_filter_isSideRead_map_viaSide]
  have h1 := sigK_sgnB_reads (sp := sp) (F := F) (S := S) (PS := PS) (adm := adm) pks sc c r
    (viaSideAns (fun y => (sp y).1) ω h (fun _ => none)
      ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none))
  generalize (sigK B pks sc (sgnB sp B F S) c r).run (viaSideAns (fun y => (sp y).1) ω h
    (fun _ => none) ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none)) = o at h1 ⊢
  have h2 := xK_stpB_reads (sp := sp) (S := S) (PS := PS) (adm := adm) r o
    (viaSideAns (fun y => (sp y).1) ω h (lastAssign (asgOf B o))
      ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T (lastAssign (asgOf B o))))
  have hT : overT T (fun _ => none) = T := funext fun x => by simp [overT]
  simp only [KFReads.tabB_viaSide, hT] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hnone : ∀ (r : Req B PS adm n), xK B (stpB sp B S) r none = .pure none := by
    intro r; rcases r <;> rfl
  rcases o with _ | o
  · rw [hnone] at h2a h2b ⊢
    simp only [↓reduceIte] at h1b
    simp [trace, isRead, isSideRead, List.filter_cons, hT]
    omega
  · simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero] at h1b
    simp [trace, isRead, isSideRead, List.filter_cons, hT]
    omega

variable (sp B F S) in
/-- **The key-free relay in side-read mode at the base component `ω`** (module docstring): the
key-free relay over base reads (`kfRelayOn`) of the signer `sgnB` and the statement program `stpB`,
its base reads the side reads of `ω` (`KFReads.viaSide`); one oracle read, `qOut + qSt` side
reads, a pad sub-slot, exactly one main request. -/
noncomputable def kfRelaySide (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
      (MUResponse B.core ⊕ Pf) X Y₁ :=
  kfRelayOn B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
    (KFReads.viaSide (fun y => (sp y).1) ω) 1 (F.qOut + S.qSt) 1 le_rfl (Or.inr ⟨default⟩)
    (fun _ _ _ _ => le_rfl)
    (fun T c r h m => (kfProgK_viaSide_reads pks toR dummyR sc ω T c r h m).1)
    (fun T c r h m => (kfProgK_viaSide_reads pks toR dummyR sc ω T c r h m).2) idle

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The key-free relay in side-read mode has no trailing side reads** (`kfProgK_noSideAfterAsk`):
its programs' base reads come before their one main request. -/
theorem noTrailingSides_kfRelaySide (ω : X → Y₁) (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (Q' : ℕ) :
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q').NoTrailingSides :=
  AssignRelay.noTrailingSides_relayOf _ _ fun T c r =>
    kfProgK_noSideAfterAsk B pks toR dummyR sc _ _ _ T c r


/-! ### The agreement with the key-free relay -/

variable {pks toR dummyR sc}

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The signature over base reads in side-read mode is the signature at the base component**
`ω`, its full reads answered by `h` and its base reads by `ω` through the table `T`. -/
theorem run_sigK_sgnB (ω : X → Y₁) (h : X → Y) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    (sigK B pks sc (sgnB sp B F S) c r).run
        (viaSideAns (fun y => (sp y).1) ω h (fun _ => none) (overT T fun _ => none)) =
      (sigPω sp B pks F sc ω T c r).run h := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · rfl
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigK, sigPω, dite_eq_left_of_eq_true (eq_true hc),
        dite_eq_left_of_eq_true (eq_true hc)]
      unfold sgnB
      rw [run_bind, run_baseL]
      have hb : (fun x => baseOf sp (viaSideAns (fun y => (sp y).1) ω h (fun _ => none)
          (overT T fun _ => none) (.inr x))) = ωT sp ω T := ωT_eq sp ω T
      rw [hb]
      erw [F.run_outB]
      rcases F.out (ωT sp ω T) (pks s) Rg c msg (sc ⟨c, hc.1⟩) with _ | q
      · simp [mapOutput, run_bind]
      · rfl
    · rw [sigK, sigPω, dite_eq_right_of_eq_false (eq_false hc),
        dite_eq_right_of_eq_false (eq_false hc)]
      rfl
  · rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The statement over base reads in side-read mode is the statement at the base component**
`ω`, its base reads answered by `ω` through the table `T` overridden by the signature's
assignments. -/
theorem run_xK_stpB (ω : X → Y₁) (h : X → Y) (T : X → Option Y) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    (xK B (stpB sp B S) r o).run (viaSideAns (fun y => (sp y).1) ω h (lastAssign (asgOf B o))
        (overT T (lastAssign (asgOf B o)))) = xPω sp B stmtPω ω T r o := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
  all_goals try rfl
  simp only [xK, xPω, stpB, run_mapOutput, run_baseL, asgOf, Option.elim]
  rw [← S.run_stmtPB, ← ωT_eq sp ω]
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The key-free relay in side-read mode agrees with the key-free relay** at every oracle `H`
of base component `ω` (`AssignRelay.AgreeAt`), for a signer factoring through the base component
(`F`, with its program `F.outB`) and a statement program reading only the base component (`hst`, with
its program `S`). -/
theorem agreeAt_kfRelaySide {stmtP : RingStmt B → OracleProg X Y X₀} {qk qs : ℕ}
    (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk) (hs : ∀ x, (stmtP x).QueriesLE qs)
    (hst : ∀ x (G : X → Y), (stmtP x).run G = stmtPω (base sp G) x)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (H : X → Y) :
    (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).AgreeAt H
      (kfRelaySide sp B pks F S toR dummyR sc (base sp H) idle) := by
  have hsig := fun T c r => (run_sigK_sgnB (F := F) (S := S) (pks := pks) (sc := sc) (adm := adm)
    (PS := PS) (base sp H) (reprogT T H) T c r).trans
      (run_sigPω (base sp H) T c r (reprogT T H) (base_reprogT sp H T))
  refine ⟨fun T c r m => ?_, fun T c r m => ?_, rfl⟩
  · rw [elimProg_kfRelay, AssignRelay.elimProg, run_elimSide, run_kfProg]
    change _ = (kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
      (KFReads.viaSide (fun y => (sp y).1) (base sp H)) T c r).run (combineAns
        (MultiRelay.sideOracle (reprogT T H)
          (KFReads.viaSide (fun y => (sp y).1) (base sp H)).side) m)
    simp only [kfProgK, run_bind, run_lift_viaSide, KFReads.tabB_viaSide]
    rw [hsig T c r, run_xK_stpB, xPω_eq hst]
    rfl
  · rw [elimProg_kfRelay, AssignRelay.elimProg, trace_elimSide,
      filterMap_getRight_filterMap_dropSide, trace_kfProg]
    change _ = ((kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
      (KFReads.viaSide (fun y => (sp y).1) (base sp H)) T c r).trace (combineAns
        (MultiRelay.sideOracle (reprogT T H)
          (KFReads.viaSide (fun y => (sp y).1) (base sp H)).side) m)).filterMap Sum.getRight?
    rw [filterMap_trace_kfProgK]
    simp only [run_lift_viaSide, KFReads.tabB_viaSide]
    rw [hsig T c r, run_xK_stpB, xPω_eq hst]
    simp [List.filterMap_append, List.filterMap_map, Function.comp_def]

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The run of the key-free relay in side-read mode, its side reads answered**: the outer reply
of the signature `sigPω` at `ω` read through `T` and the main reply to its main request. -/
theorem run_elimProg_kfRelaySide (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (h : X → Y) (m : MURequest (SignOracle.none B.core) n ⊕ R → Option (MUResponse B.core ⊕ Pf)) :
    ((kfRelaySide sp B pks F S toR dummyR sc ω idle).elimProg T c r).run (combineAns h m) =
      replyOf B r ((sigPω sp B pks F sc ω T c r).run h)
        (m (reqOf B toR dummyR c r ((sigPω sp B pks F sc ω T c r).run h)
          (xPω sp B stmtPω ω T r ((sigPω sp B pks F sc ω T c r).run h)))) := by
  rw [AssignRelay.elimProg, run_elimSide]
  change (kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
    (KFReads.viaSide (fun y => (sp y).1) ω) T c r).run (combineAns
      (MultiRelay.sideOracle h (KFReads.viaSide (fun y => (sp y).1) ω).side) m) = _
  simp only [kfProgK, run_bind, run_lift_viaSide, KFReads.tabB_viaSide]
  rw [run_sigK_sgnB, run_xK_stpB]
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The main request of the key-free relay in side-read mode**: the `reqOf` of the signature
`sigPω` at `ω` read through `T`. -/
theorem mainOf_kfRelaySide (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (T : X → Option Y) (H : X → Y)
    (m : MURequest (SignOracle.none B.core) n ⊕ R → Option (MUResponse B.core ⊕ Pf)) (c : ℕ)
    (r : Req B PS adm n) :
    (kfRelaySide sp B pks F S toR dummyR sc ω idle).mainOf T H m c r =
      reqOf B toR dummyR c r ((sigPω sp B pks F sc ω T c r).run (reprogT T H))
        (xPω sp B stmtPω ω T r ((sigPω sp B pks F sc ω T c r).run (reprogT T H))) := by
  unfold AssignRelay.mainOf AssignRelay.mainOfT
  rw [AssignRelay.elimProg, trace_elimSide, filterMap_getRight_filterMap_dropSide]
  change (((kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
    (KFReads.viaSide (fun y => (sp y).1) ω) T c r).trace (combineAns
      (MultiRelay.sideOracle (reprogT T H) (KFReads.viaSide (fun y => (sp y).1) ω).side)
        m)).filterMap Sum.getRight?).headD _ = _
  rw [filterMap_trace_kfProgK]
  simp only [run_lift_viaSide, KFReads.tabB_viaSide]
  rw [run_sigK_sgnB, run_xK_stpB]
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The statement over base reads in side-read mode, its side reads answered**, is the
statement at the base component `ω` read through the table `T` overridden by the signature's
assignments. -/
theorem elimSide_lift_xK_stpB (ω : X → Y₁) (T : X → Option Y) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    elimSide (KFReads.viaSide (fun y => (sp y).1) ω).side
        ((KFReads.viaSide (fun y => (sp y).1) ω).lift
          (Req' := MURequest (SignOracle.none B.core) n ⊕ R) (Resp' := MUResponse B.core ⊕ Pf)
          (lastAssign (asgOf B o)) (overT T (lastAssign (asgOf B o))) (xK B (stpB sp B S) r o)) =
      .pure (xPω sp B stmtPω ω T r o) := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
  all_goals try rfl
  rw [xK, stpB, baseL, mapOutput, KFReads.lift, translate_bind, elimSide_bind, translate_translate,
    elimSide_translate_side (KFReads.viaSide (fun y => (sp y).1) ω).side
    ((fun a => Sum.inl (Sum.elim Sum.inl (KFReads.viaSide (fun y => (sp y).1) ω).pt a)) ∘ Sum.inr)
    id (fun _ => rfl)]
  change OracleProg.pure (some _) = _
  rw [xPω, ← S.run_stmtPB, ← ωT_eq sp ω]
  rfl

variable (sp B pks F) in
/-- **The assignments of a public part at the base component** `ω` read through the table `T`,
from the second component of the oracle `H` read through `T` at the kept point. -/
def kfAsg (ω : X → Y₁) (T : X → Option Y) (H : X → Y) (s : Fin n) (Rg : KeyRing B.PK N)
    (msg : B.Msg) (q : Pb) : List (Assignment X Y) :=
  F.asg (ωT sp ω T) (pks s) Rg msg q (prf sp (reprogT T H) (F.xk (ωT sp ω T) (pks s) Rg msg q))

variable (sp B pks F stmtPω toR sc) in
/-- **The origin of a table entry through the key-free relay in side-read mode**
(`KFEntryFrom`): at the base component `ω` and the oracle `H`, the entry `(x, y)` is assigned by
`kfAsg` of the public part `q` of `F.out` at `ω` read through the table `p.tab` of a signing
request `sign s Rg msg` of `hP`, whose signature is `σ`, and the request's main request
`inr (toR x₀ r σ)`, `x₀` the statement `stmtPω` after those assignments, is a request of
`hist'`. -/
def KFEntryFrom (ω : X → Y₁) (H : X → Y) (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)))
    (x : X) (y : Y) : Prop :=
  ∃ p ∈ hP, ∃ s Rg msg q σ, ∃ hc : (p.num : ℕ) < Q ∧ pks s ∈ Rg.1 ∧ adm Rg,
    p.req = .sign s Rg msg ∧
    F.out (ωT sp ω p.tab) (pks s) Rg p.num msg (sc ⟨p.num, hc.1⟩) = some (q, σ) ∧
    lastAssign (kfAsg sp B pks F ω p.tab H s Rg msg q) x = some y ∧
    ∃ e' ∈ hist', e'.request = .inr (toR (stmtPω (ωT sp ω (overT p.tab
      (lastAssign (kfAsg sp B pks F ω p.tab H s Rg msg q)))) ⟨Rg, msg,
        F.pub (ωT sp ω p.tab) (pks s) Rg msg q⟩) (p.req, (p.num : ℕ)) σ)

variable (sp B pks F stmtPω toR sc) in
/-- **The origin of the absorbed tables through the key-free relay in side-read mode**
(`KFTableFacts`): every entry of the final table `T` and of the table of each tagged request of
`hP` has its origin in a signing request of `hP` (`KFEntryFrom`). -/
def KFTableFacts (ω : X → Y₁) (H : X → Y) (T : X → Option Y)
    (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf))) :
    Prop :=
  (∀ x y, T x = some y → KFEntryFrom sp B pks F stmtPω toR sc ω H hP hist' x y) ∧
    ∀ q ∈ hP, ∀ x y, q.tab x = some y → KFEntryFrom sp B pks F stmtPω toR sc ω H hP hist' x y

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **`KFEntryFrom` from the table origin** (`AssignRelay.TableFrom`) of the key-free relay in
side-read mode. -/
theorem kfEntryFrom_of_tableFrom (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (H : X → Y)
    (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)))
    (x : X) (y : Y) (h : (kfRelaySide sp B pks F S toR dummyR sc ω idle).TableFrom H hP hist' x y) :
    KFEntryFrom sp B pks F stmtPω toR sc ω H hP hist' x y := by
  obtain ⟨p, hp, m, ha, e', he', hreq⟩ := h
  rw [run_elimProg_kfRelaySide] at ha
  rw [mainOf_kfRelaySide] at hreq
  have key : ∀ (r : Req B PS adm n) (o : Option (B.Pub × B.BSig × List (Assignment X Y)))
      (a : Option (MUResponse B.core ⊕ Pf)), lastAssign (replyOf B r o a).assignments x = some y →
      ∃ s Rg msg p', r = .sign s Rg msg ∧ o = some p' ∧ lastAssign p'.2.2 x = some y := by
    intro r o a h
    unfold replyOf at h
    split at h
    · simp [lastAssign] at h
    · exact ⟨_, _, _, _, rfl, rfl, h⟩
    · simp [lastAssign] at h
  obtain ⟨s, Rg, msg, o, hr, ho, hl⟩ := key _ _ _ ha
  rw [hr] at ho hreq
  by_cases hc : (p.num : ℕ) < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
  · rw [sigPω, dite_eq_left_of_eq_true (eq_true hc)] at ho hreq
    rcases hout : F.out (ωT sp ω p.tab) (pks s) Rg p.num msg (sc ⟨p.num, hc.1⟩) with _ | ⟨q, σ⟩
    · rw [hout] at ho
      cases ho
    · rw [hout] at ho hreq
      simp only [run, Option.some.injEq] at ho
      subst ho
      refine ⟨p, hp, s, Rg, msg, q, σ, hc, hr, hout, hl, e', he', ?_⟩
      rw [hreq, hr]
      rfl
  · rw [sigPω, dite_eq_right_of_eq_false (eq_false hc)] at ho
    cases ho

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **`KFTableFacts` from the explanation** (`AssignRelay.Explains`) of the key-free relay in
side-read mode. -/
theorem kfTableFacts_of_explains (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (H : X → Y) (T : X → Option Y)
    (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)))
    (h : (kfRelaySide sp B pks F S toR dummyR sc ω idle).Explains Q H T hP hist') :
    KFTableFacts sp B pks F stmtPω toR sc ω H T hP hist' :=
  ⟨fun x y hx => kfEntryFrom_of_tableFrom ω idle H hP hist' x y (h.2.1 x y hx),
    fun q hq x y hx => kfEntryFrom_of_tableFrom ω idle H hP hist' x y (h.2.2 q hq x y hx)⟩

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The main requests explained through the key-free relay in side-read mode**: each request
of `hist'` is the padding request or a `reqOf` of a tagged request of `hP`. -/
theorem reqOf_of_explains (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (H : X → Y) (T : X → Option Y)
    (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)))
    (h : (kfRelaySide sp B pks F S toR dummyR sc ω idle).Explains Q H T hP hist')
    {e' : HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)}
    (he' : e' ∈ hist') :
    e'.request = idle ∨ ∃ p ∈ hP, ∃ o x, e'.request = reqOf B toR dummyR p.num p.req o x := by
  rcases h.1 e' he' with h' | ⟨p', hp', hc⟩
  · exact .inl h'
  · exact .inr ⟨p', hp', MultiRelay.canAsk_of_asksIn _
      (P := fun r' => ∃ o x, r' = reqOf B toR dummyR p'.num p'.req o x)
      (((asksIn_kfProgK_reqOf B pks toR dummyR sc _ _ _ p'.tab p'.num p'.req).recMain
        _).mapOutput _) hc⟩

end RingSignature.KeyFree

end GordieHowe
