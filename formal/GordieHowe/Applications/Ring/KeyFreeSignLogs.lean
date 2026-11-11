-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeRelayB
public import GordieHowe.Applications.Ring.KeyFreeChain
public import GordieHowe.Model.Quantum.Interactive.ExtRunLogs
public import GordieHowe.Model.Quantum.Interactive.RelayGoodLogs
public import GordieHowe.Model.Quantum.Interactive.RelayBlockInner

@[expose] public section

/-!
# The logged signing requests of the key-free extraction run

In the simulation-extraction run of the key-free route (`extAdv` of `seAlgKF`,
`GordieHowe/Applications/Ring/KeyFreeSE.lean`) for an adversary with an assigning relay absorbed
(`AdaptiveIAlg.absorbAssign`) at a fixed base component (`restrictAt`), every logged main request
satisfying a test `p` that the blank and the idle requests fail is one the relay's program of some
request can make (`AdaptiveIAlg.relayAdv_logInvRaw_ask`, carried to the extraction run by
`AdaptiveIAlg.simProb_expandAdv_wsInv`).

- `simProb_seAlgKF_asks` (**the generic statement**): with a property `P` that every main request
  of the relay's programs has (`AsksIn`), an event of the run has at most the probability of the event
  with every logged request satisfying `p` in `P`.
- `firstJ_eq_of_allEq`, `slotRequest`, `simProb_seAlgKF_slotRequest`: the request of slot `j`, the
  first recorded request of number `j`, is every recorded request of number `j`.
- `simProb_seAlgKF_slotAsks`: every logged request satisfying a test is asked by the request of a
  slot `j < Q`, numbered `j`, when only requests of number below `Q` other than the blank ask it.
- `KFSignedOf`, `KFSignedAsk`, `asksIn_kfRelaySide_signed`: the main request of the key-free relay in side-read
  mode, its side reads answered by `ω`, is a dummy or a corruption of its request, or the signed
  request of a signing request:
  `toR` of the statement `stmtPω` at the base component read through the table overridden by the
  signature's assignments, the ring request and the signature `F.out`.
- `simProb_seAlgKF_kfSigned` (**the key-free statement**): through `kfRelaySide`, for a test failing
  the dummies and the corruptions, every logged request satisfying it is a signed request.
-/

open scoped ENNReal

namespace GordieHowe

open Quantum Signature QROM OracleProg RingSignature.OracleSplit

namespace RingSignature.KeyFree

open RingSignature.Insider

/-! ### The main requests of the relay program at the base component -/

section Asks

variable {X Y Y₁ Y₂ : Type} [DecidableEq X] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : OracleSplit Y Y₁ Y₂) {N n : ℕ} {TB : BaseTypes} [DecidableEq TB.PK]
  (B : BaseSigner X Y N TB)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {SC X₀ R Pb : Type} (pks : Fin n → B.PK)
  {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))}
  (F : KFSignFactors sp Pb ksign) (stmtPω : (X → Y₁) → RingStmt B → X₀)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) {Q : ℕ} (sc : Fin Q → SC)

/-- **The signed request of the relay's program of a request at the base component `ω`**: for the
signing request `r = sign s Rg m` of a member `s` of a supported ring `Rg`, with request number
`c < Q` and table `T`, and an answer `y` at the kept point, with the public part and signature
`q = F.out (ωT ω T) …`, the request `toR x (sign s Rg m, c) q.2` at the statement `x = stmtPω` at
the base component read through `T` overridden by the signature's assignments
`F.asg … (sp y).2`. -/
def KFSignedOf (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (r' : MURequest (SignOracle.none B.core) n ⊕ R) : Prop :=
  ∃ (s : Fin n) (Rg : KeyRing B.PK N) (m : B.Msg) (hc : c < Q) (q : Pb × B.BSig) (y : Y),
    r = .sign s Rg m ∧ pks s ∈ Rg.1 ∧ adm Rg ∧
    F.out (ωT sp ω T) (pks s) Rg c m (sc ⟨c, hc⟩) = some q ∧
    r' = .inr (toR (stmtPω (ωT sp ω (overT T (lastAssign
      (F.asg (ωT sp ω T) (pks s) Rg m q.1 (sp y).2)))) ⟨Rg, m, F.pub (ωT sp ω T) (pks s) Rg m q.1⟩)
      (.sign s Rg m, c) q.2)

/-- **A signed request of the relay at the base component `ω`**: the signed request
(`KFSignedOf`) of the program of some request, request number and table. -/
def KFSignedAsk (ω : X → Y₁) (r' : MURequest (SignOracle.none B.core) n ⊕ R) : Prop :=
  ∃ T c r, KFSignedOf sp B pks F stmtPω toR sc ω T c r r'

variable (dummyR : Req B PS adm n × ℕ → R)

/-- **The output of the signature at the base component** (proof-internal): none, or for a
signing request by a member of a supported ring below `Q` whose `F.out` is `q`, the published
value, the signature and the assignments at some answer `y` at the kept point. -/
def KFSigOut (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) : Prop :=
  o = none ∨ ∃ (s : Fin n) (Rg : KeyRing B.PK N) (m : B.Msg) (hc : c < Q) (q : Pb × B.BSig)
    (y : Y), r = .sign s Rg m ∧ pks s ∈ Rg.1 ∧ adm Rg ∧
    F.out (ωT sp ω T) (pks s) Rg c m (sc ⟨c, hc⟩) = some q ∧
    o = some (F.pub (ωT sp ω T) (pks s) Rg m q.1, q.2,
      F.asg (ωT sp ω T) (pks s) Rg m q.1 (sp y).2)

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The outputs of the signature at the base component** on every path are `KFSigOut`. -/
theorem allOut_sigPω (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    (sigPω sp B pks F sc ω T c r).AllOut (KFSigOut sp B pks F sc ω T c r) := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · exact .inl rfl
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigPω, dite_eq_left_of_eq_true (eq_true hc)]
      rcases hq : F.out (ωT sp ω T) (pks s) Rg c msg (sc ⟨c, hc.1⟩) with _ | q
      · exact .inl rfl
      · exact fun y => .inr ⟨s, Rg, msg, hc.1, q, y, rfl, hc.2.1, hc.2.2, hq, rfl⟩
    · rw [sigPω, dite_eq_right_of_eq_false (eq_false hc)]
      exact .inl rfl
  · exact .inl rfl

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The outputs of the signature over base reads in side-read mode**, its side reads answered by
`ω`, on every path are `KFSigOut`. -/
theorem allOut_elimSide_sigK_sgnB [Inhabited X] [Inhabited B.Pub]
    {stmtPω : (X → Y₁) → RingStmt B → X₀}
    (S : KFStmt stmtPω) (ω : X → Y₁) (T : X → Option Y) (c : ℕ)
    (r : Req B PS adm n) :
    (elimSide (KFReads.viaSide (fun y => (sp y).1) ω).side
        ((KFReads.viaSide (fun y => (sp y).1) ω).lift
          (Req' := MURequest (SignOracle.none B.core) n ⊕ R) (Resp' := MUResponse B.core ⊕ Pf)
          (fun _ => none) (overT T fun _ => none) (sigK B pks sc (sgnB sp B F S) c r))).AllOut
      (KFSigOut sp B pks F sc ω T c r) := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · exact .inl rfl
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigK, dite_eq_left_of_eq_true (eq_true hc)]
      unfold sgnB
      rw [KFReads.lift, translate_bind, elimSide_bind, baseL, translate_translate,
        elimSide_translate_side (KFReads.viaSide (fun y => (sp y).1) ω).side
          ((fun a => Sum.inl (Sum.elim Sum.inl (KFReads.viaSide (fun y => (sp y).1) ω).pt a)) ∘
            Sum.inr) id (fun _ => rfl)]
      change OracleProg.AllOut (elimSide _ (translate _ _ _)) _
      have hb : (fun x => baseOf sp ((KFReads.viaSide (fun y => (sp y).1) ω).readAns
          (Resp' := MUResponse B.core ⊕ Pf) (fun _ => none) (overT T fun _ => none) (.inr x)
          (.inl (.inr ((KFReads.viaSide (fun y => (sp y).1) ω).side (id x)))))) = ωT sp ω T :=
        ωT_eq sp ω T
      simp only [Function.comp_def] at hb ⊢
      erw [hb, F.run_outB]
      rcases hq : F.out (ωT sp ω T) (pks s) Rg c msg (sc ⟨c, hc.1⟩) with _ | q
      · intro b
        change OracleProg.AllOut (elimSide _ (translate _ _ (mapOutput _ (baseL sp _)))) _
        rw [mapOutput, translate_bind, elimSide_bind, baseL, translate_translate,
          elimSide_translate_side (KFReads.viaSide (fun y => (sp y).1) ω).side
            ((fun a => Sum.inl (Sum.elim Sum.inl (KFReads.viaSide (fun y => (sp y).1) ω).pt a)) ∘
              Sum.inr) id (fun _ => rfl)]
        exact .inl rfl
      · intro b
        exact .inr ⟨s, Rg, msg, hc.1, q, _, rfl, hc.2.1, hc.2.2, hq, rfl⟩
    · rw [sigK, dite_eq_right_of_eq_false (eq_false hc)]
      exact .inl rfl
  · exact .inl rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **Every main request of the key-free relay in side-read mode, its side reads answered by `ω`,
is a dummy or a corruption of its request, or its signed request** (`KFSignedOf`). -/
theorem asksIn_kfRelaySide_signed [Inhabited X] [Inhabited B.Pub]
    {stmtPω : (X → Y₁) → RingStmt B → X₀}
    (S : KFStmt stmtPω) (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf)
      (elimSide (kfRelaySide sp B pks F S toR dummyR sc ω idle).side
        ((kfRelaySide sp B pks F S toR dummyR sc ω idle).prog T c r))
      fun r' => r' = reqOf B toR dummyR c r none none ∨
        KFSignedOf sp B pks F stmtPω toR sc ω T c r r' := by
  change MultiRelay.AsksIn _ (elimSide (KFReads.viaSide (fun y => (sp y).1) ω).side
    (kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
      (KFReads.viaSide (fun y => (sp y).1) ω) T c r)) _
  unfold kfProgK
  rw [elimSide_bind, KFReads.tabB_viaSide]
  refine MultiRelay.AsksIn.bind_allOut
    (MultiRelay.AsksIn.elimSide _ (asksIn_lift B _ _ _ _ _))
    (allOut_elimSide_sigK_sgnB sp B pks F sc S ω T c r) fun o ho => ?_
  rw [elimSide_bind, KFReads.tabB_viaSide, elimSide_lift_xK_stpB]
  change MultiRelay.AsksIn _ (elimSide _ (OracleProg.bind (OracleProg.query _ _) _)) _
  refine MultiRelay.AsksIn.query (fun r' h => ?_) fun b => ?_
  · cases h
    rcases ho with rfl | ⟨s, Rg, m, hc, q, y, rfl, hs, ha, hq, rfl⟩
    · left
      rcases r with i | ⟨s, Rg, m⟩ | ⟨i, bm⟩ <;> rfl
    · exact .inr ⟨s, Rg, m, hc, q, y, rfl, hs, ha, hq, rfl⟩
  · exact MultiRelay.AsksIn.pure _ _

end Asks

/-! ### The extraction run -/

section SPBCS

open GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

variable {k kN kS L e N n t : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  {B : BaseSigner Xb Yb N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x} (hb : M.FormatBounds Qs b b)
  {Stmt Wit SC R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R] [Fintype SC] [DecidableEq SC]
  {rel : Stmt → Wit → Prop} [DecidableRel rel]
  {enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit} {dummyS : Stmt}
  {isDummy : X₀ → Bool} [Inhabited M.NIProof]

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n

variable {Y Y₁ Req₀ Resp₀ : Type} [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁]
  [Fintype Req₀] [DecidableEq Req₀] [Fintype Resp₀] [DecidableEq Resp₀] [Inhabited Req₀]
  [AddGroup Y] [AddGroup Y₁] [Nonempty Y]

/-- **The relay's record at the end of the key-free extraction run**: the started slots' entries
(`MultiRelay.recList`) of the record of the relay in the workspace of the composed registers `c`
of the simulation-extraction run of `seAlgKF` for `A₀` with the assigning relay `G` absorbed at
the base component `ω`. -/
noncomputable def kfRecord {SC' : Type} [Fintype SC'] [DecidableEq SC'] [DecidableEq X₀]
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA₀ : AlgShape Xq Y Req₀ Resp₀} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay Xq Y Req₀ Resp₀ (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xs Ys)
    (sp : Y ≃+ Y₁ × XOut k e) (ω : Xq → Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q) :=
  MultiRelay.recList (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
    prf keys Q (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).toTPKindAlg Psim Q
      c).1.1.work.1.1.record

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The logged requests of the key-free extraction run** (module docstring): for an adversary
`A₀` with the assigning relay `G` absorbed (`absorbAssign`) at the base component `ω` of the split
`sp`, its output's first part kept, every main request of whose programs has the property `P`
(`hP`), and a test `p` that the blank and the idle requests fail (`hpd`, `hpi`), an event `Ev`
of the simulation-extraction run of `seAlgKF` has at most the probability of `Ev` with every
logged request `r'` satisfying `p` in `P` and one the relay's program of an entry `r` of the final
record (`kfRecord`) can make. -/
theorem simProb_seAlgKF_asks {SC' : Type} [Fintype SC'] [DecidableEq SC'] [DecidableEq X₀]
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA₀ : AlgShape Xq Y Req₀ Resp₀} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay Xq Y Req₀ Resp₀ (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xs Ys)
    (sp : Y ≃+ Y₁ × XOut k e) (ω : Xq → Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (kq : ℕ)
    (Ev : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q → DB Xq (Out k e) → Prop)
    (Pa : MUR ⊕ R → Prop)
    (hP : ∀ T c r, MultiRelay.AsksIn (MUResponse B.core ⊕ M.Response b)
      (elimSide G.side (G.prog T c r)) Pa)
    (p : MUR ⊕ R → Bool) (hpd : p default = false) (hpi : p G.idle = false) :
    simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        Ev ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        fun c D => Ev c D ∧
          ∀ r' ∈ Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
            (dummyS := dummyS) prf keys Q
            (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).toTPKindAlg Psim Q
              c).1.1.logs, p r' = true → Pa r' ∧
            ∃ i r, (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω
              Psim c).getD i none = some r ∧ (G.relayOf Q).CanAsk r r' := by
  have hR := (((A₀.absorbAssignP _ _ Q).relayAdv_logInvRaw_ask (G.relayOf Q) Q
    ((A₀.absorbAssignP _ _ Q).relayOut (G.relayOf Q)) p hpd hpi).restrictAt sp ω).mapOut Prod.fst
  have hT := hR.logInv (F := seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
    (AdaptiveIAlg.mapOut_tracePreserving (AdaptiveIAlg.tracePreserving_restrictAt sp ω _
      (AdaptiveIAlg.absorbAssign_tracePreserving A₀ G Q)) _) (fun _ => keyReplyNone B keys)
  -- TODO(unbundle-M4): `set` abstracting `Z` in `hR`/`hT` unfolds the composed shapes; `let`
  let Z := (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
    prf keys Q (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst))
  have hS : Z.WsInv _ :=
    hT.wsInv (claimOfOutX prf)
  refine (AdaptiveIAlg.simProb_expandAdv_wsInv (Z := Z)
    (C₁ := simExtChallenger Psim Q) (outEquiv k e)
    (simExtractionExpansion Z.toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    (·.getD (Z.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut) hS
    _).trans
    (simProb_mono _ _ fun c D h => ⟨h.1, fun r' hr' hp => ?_⟩)
  obtain ⟨v, hv, rfl⟩ := h.2
  obtain ⟨j, hj⟩ := (mem_requests_iff _ r').1 hr'
  obtain ⟨i, rr, hi, hc⟩ := hv.2 j r' hj hp
  exact ⟨MultiRelay.canAsk_of_asksIn_elimSide _
    (AssignRelay.asksIn_relayOf_elimSide G Q (P := fun _ _ _ => Pa) hP rr) hc, i, rr, hi, hc⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The relay's final record is tagged in the key-free extraction run**: for a trace-preserving
adversary `A₀` with the assigning relay `G` absorbed at the base component `ω`, and a relayed
request number `j < Q`, an event `Ev` of the simulation-extraction run of `seAlgKF` has at most
the probability of `Ev` with the requests of the final record (`kfRecord`) of number `j`
(`jTest Q j`) all equal. -/
theorem simProb_seAlgKF_jTagged {SC' : Type} [Fintype SC'] [DecidableEq SC'] [DecidableEq X₀]
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA₀ : AlgShape Xq Y Req₀ Resp₀} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀)) (hA : A₀.TracePreserving)
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay Xq Y Req₀ Resp₀ (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xs Ys)
    (sp : Y ≃+ Y₁ × XOut k e) (ω : Xq → Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (kq : ℕ)
    (Ev : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q → DB Xq (Out k e) → Prop)
    {j : ℕ} (hj : j < Q) :
    simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        Ev ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        fun c D => Ev c D ∧
          ∀ (i i' : ℕ) r r',
            (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim
              c)[i]? = some (some r) →
            (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim
              c)[i']? = some (some r') →
            AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := Req₀) Q j r = true →
            AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := Req₀) Q j r' = true → r = r' := by
  have hsupp := A₀.innerSupp_pureD (Req' := MUR ⊕ R) (Resp' := MUResponse B.core ⊕ M.Response b) Q j
    hA hj
  have hR := (((A₀.absorbAssignP _ _ Q).relayAdv_logInvRaw_good (G.relayOf Q) Q
    ((A₀.absorbAssignP _ _ Q).relayOut (G.relayOf Q)) (AdaptiveIAlg.jTest Q j)
    (A₀.innerGin _ _ Q j) (by convert hsupp)).restrictAt sp ω).mapOut
    Prod.fst
  have hT := hR.logInv (F := seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
    (AdaptiveIAlg.mapOut_tracePreserving (AdaptiveIAlg.tracePreserving_restrictAt sp ω _
      (AdaptiveIAlg.absorbAssign_tracePreserving A₀ G Q)) _) (fun _ => keyReplyNone B keys)
  -- TODO(unbundle-M4): `set` abstracting `Z` in `hR`/`hT` unfolds the composed shapes; `let`
  let Z := (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
    prf keys Q (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst))
  have hS : Z.WsInv _ :=
    hT.wsInv (claimOfOutX prf)
  refine (AdaptiveIAlg.simProb_expandAdv_wsInv (Z := Z)
    (C₁ := simExtChallenger Psim Q) (outEquiv k e)
    (simExtractionExpansion Z.toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    (·.getD (Z.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut) hS
    _).trans
    (simProb_mono _ _ fun c D h => ⟨h.1, ?_⟩)
  obtain ⟨v, hv, rfl⟩ := h.2
  exact fun _ _ _ _ h1 h2 h3 h4 => (AdaptiveIAlg.jTagged_of_relayGood hv).eq h1 h2 h3 h4

/-- **The first request satisfying `J` of a list whose such requests are all equal** is each of
them. -/
theorem firstJ_eq_of_allEq {Req : Type} {J : Req → Bool} {es : List (Option Req)}
    (hall : ∀ (i i' : ℕ) r r', es[i]? = some (some r) → es[i']? = some (some r') → J r = true →
      J r' = true → r = r')
    {i : ℕ} {r : Req} (hi : es[i]? = some (some r)) (hr : J r = true) :
    MultiRelay.firstJ J es = some r := by
  unfold MultiRelay.firstJ
  rcases hf : es.find? (fun e => e.any J) with _ | e
  · have hn := List.find?_eq_none.1 hf (some r) (List.mem_of_getElem? hi)
    simp [hr] at hn
  obtain ⟨-, i₀, hi₀, he, -⟩ := List.find?_eq_some_iff_getElem.1 hf
  have hJ := List.find?_some hf
  rcases e with _ | r₀
  · simp at hJ
  have hi₀' : es[i₀]? = some (some r₀) := by rw [List.getElem?_eq_getElem hi₀, he]
  simp only [Option.any_some] at hJ
  rw [hf]
  exact congrArg some (hall _ _ _ _ hi₀' hi hJ hr)

/-- **The request of slot `j`** of a register of the key-free extraction run: the first request of
number `j` (`jTest Q j`) of the relay's final record (`kfRecord`). -/
noncomputable def slotRequest {SC' : Type} [Fintype SC'] [DecidableEq SC'] [DecidableEq X₀]
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA₀ : AlgShape Xq Y Req₀ Resp₀} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay Xq Y Req₀ Resp₀ (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xs Ys)
    (sp : Y ≃+ Y₁ × XOut k e) (ω : Xq → Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (j : ℕ)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q) :
    Option ((Req₀ × Fin (Q + 1)) × (Xq → Option Y)) :=
  MultiRelay.firstJ (AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := Req₀) Q j)
    (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim c)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **Every recorded request of number `j` is the request of slot `j`** in the key-free extraction
run (`simProb_seAlgKF_jTagged`): an event `Ev` of the run has at most the probability of `Ev`
with every request of number `j` of the final record equal to `slotRequest j`. -/
theorem simProb_seAlgKF_slotRequest {SC' : Type} [Fintype SC'] [DecidableEq SC']
    [DecidableEq X₀] (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) {shA₀ : AlgShape Xq Y Req₀ Resp₀} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀)) (hA : A₀.TracePreserving)
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay Xq Y Req₀ Resp₀ (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xs Ys)
    (sp : Y ≃+ Y₁ × XOut k e) (ω : Xq → Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (kq : ℕ)
    (Ev : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q → DB Xq (Out k e) → Prop)
    {j : ℕ} (hj : j < Q) :
    simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        Ev ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        fun c D => Ev c D ∧
          ∀ (i : ℕ) r,
            (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim
              c)[i]? = some (some r) →
            AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := Req₀) Q j r = true →
            slotRequest (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim j
              c = some r :=
  (simProb_seAlgKF_jTagged (Qs := Qs) prf keys Q A₀ hA G sp ω Psim kq Ev hj).trans
    (simProb_mono _ _ fun _ _ h => ⟨h.1, fun _ _ hi hr => firstJ_eq_of_allEq h.2 hi hr⟩)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **Every logged request satisfying `p` is asked by the request of a slot** in the key-free
extraction run (`simProb_seAlgKF_asks` with `simProb_seAlgKF_slotRequest` at every slot): for a
trace-preserving adversary `A₀` and a test `p` that the blank and the idle requests fail (`hpd`,
`hpi`), whose requests are asked only by requests of number below `Q` other than the blank one
(`hp`), an event `Ev` of the run has at most the probability of `Ev` with every logged request
satisfying `p` asked by the request of a slot `j`, numbered `j`. -/
theorem simProb_seAlgKF_slotAsks {SC' : Type} [Fintype SC'] [DecidableEq SC']
    [DecidableEq X₀] (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) {shA₀ : AlgShape Xq Y Req₀ Resp₀} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀)) (hA : A₀.TracePreserving)
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay Xq Y Req₀ Resp₀ (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xs Ys)
    (sp : Y ≃+ Y₁ × XOut k e) (ω : Xq → Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (kq : ℕ)
    (Ev : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q → DB Xq (Out k e) → Prop)
    (p : MUR ⊕ R → Bool) (hpd : p default = false) (hpi : p G.idle = false)
    (hp : ∀ r r', (G.relayOf Q).CanAsk r r' → p r' = true → (r.1.2 : ℕ) < Q ∧ r ≠ default) :
    simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        Ev ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        fun c D => Ev c D ∧
          ∀ r' ∈ Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
            (dummyS := dummyS) prf keys Q
            (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).toTPKindAlg Psim Q
              c).1.1.logs, p r' = true →
            ∃ j : Fin Q, ∃ r, slotRequest (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
              A₀ G sp ω Psim j c = some r ∧ (r.1.2 : ℕ) = j ∧ (G.relayOf Q).CanAsk r r' := by
  -- the slot lemma at every slot below `m`, by induction on `m`
  have hall : ∀ m (Ev' : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
      keys Q (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q →
        DB Xq (Out k e) → Prop), simProb (outEquiv k e)
      (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
        (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq) Ev' ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        fun c D => Ev' c D ∧ ∀ j < min m Q, ∀ (i : ℕ) r,
          (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim
            c)[i]? = some (some r) →
          AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := Req₀) Q j r = true →
          slotRequest (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim j
            c = some r := by
    intro m Ev'
    induction m with
    | zero => exact simProb_mono _ _ fun _ _ h => ⟨h, fun j hj => absurd hj (by omega)⟩
    | succ m ih =>
      by_cases hm : m < Q
      · refine ih.trans ((simProb_seAlgKF_slotRequest (Qs := Qs) prf keys Q A₀ hA G sp ω Psim kq
          _ hm).trans (simProb_mono _ _ fun _ _ h => ⟨h.1.1, fun j hj => ?_⟩))
        rcases Nat.lt_or_ge j (min m Q) with hj' | hj'
        · exact h.1.2 j hj'
        · have : j = m := by omega
          subst this
          exact h.2
      · exact ih.trans (simProb_mono _ _ fun _ _ h => ⟨h.1, fun j hj => h.2 j (by omega)⟩)
  refine (simProb_seAlgKF_asks (Qs := Qs) prf keys Q A₀ G sp ω Psim kq _ (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) p hpd hpi).trans ((hall Q _).trans
      (simProb_mono _ _ fun c D h => ⟨h.1.1, fun r' hr' hpr => ?_⟩))
  obtain ⟨-, i, r, hi, hc⟩ := h.1.2 r' hr' hpr
  obtain ⟨hlt, hne⟩ := hp r r' hc hpr
  have hi' : (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim
      c)[i]? = some (some r) := by
    rw [List.getD_eq_getElem?_getD] at hi
    rcases h' : (kfRecord (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A₀ G sp ω Psim
      c)[i]? with _ | x
    · simp [h'] at hi
    · simp only [h', Option.getD_some] at hi
      rw [hi]
  have hJ : AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := Req₀) Q (r.1.2 : ℕ) r = true := by
    simp [AdaptiveIAlg.jTest, hne]
  exact ⟨⟨r.1.2, hlt⟩, r, h.2 _ (by simpa using hlt) i r hi' hJ, rfl, hc⟩

end SPBCS

/-! ### Through the key-free relay at the base component -/

section Chain

open GordieHowe.SPBCS IOP SPTerm

variable {k kN kS L e N n : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins]
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {R : Type} [Fintype R] [DecidableEq R] [Nonempty R] {honest : Wit₀ → R → CausalProver P τ X₀}
  {Stmt Wit Rq Frg : Type} {rel : Stmt → Wit → Prop}
  {enc : MURequest (SignOracle.none B.core) n ⊕ Rq → ProofQuery Stmt Wit}
  [DecidableEq X₀] [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype Rq] [DecidableEq Rq] [Inhabited Rq]
  [DecidableRel rel] [Inhabited M.NIProof] {dummyS : Stmt}

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The logged requests of the key-free extraction run through the relay at the base
component** (`simProb_seAlgKF_asks` with `asksIn_kfRelaySide_signed`): for an adversary with
the key-free relay in side-read mode `kfRelaySide ω` absorbed at the base component `ω`, its
output's first part kept, and a test `p` that
the blank and idle requests, the dummies `dummyR` and the corruptions fail, an event `Ev` of
the simulation-extraction run of `seAlgKF` has at most the probability of `Ev` with every
logged request satisfying `p` a signed request (`KFSignedAsk`). -/
theorem simProb_seAlgKF_kfSigned (hb : M.FormatBounds Qs b b)
    (stmtProg : RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y₁ X₀) (qS : ℕ)
    (hS : ∀ x, (stmtProg x).QueriesLE qS) (check : RingStmt B → Bool)
    (input : RingStmt B → RingWit B → Option Wit₀) {adm : KeyRing B.PK N → Prop}
    [DecidablePred adm]
    [Fintype
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)]
    [DecidableEq
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)]
    [Fintype
      (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)]
    [DecidableEq
      (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)]
    [Inhabited
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)]
    {SC Pb : Type} (pks : Fin n → B.PK)
    {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (Bits (queryBits k kN kS L)) Y
        (Option (B.Pub × B.BSig × List (Assignment (Bits (queryBits k kN kS L)) Y)))}
    (F : KFSignFactors sp Pb ksign) (stmtPω : (Bits (queryBits k kN kS L) → Y₁) → RingStmt B → X₀)
    [Inhabited B.Pub] (S : KFStmt stmtPω)
    (toR : X₀ →
      Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n × ℕ →
      B.BSig → Rq)
    (dummyR :
      Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n × ℕ →
      Rq)
    {Q : ℕ} (sc : Fin Q → SC)
    (idle : MURequest (SignOracle.none B.core) n ⊕ Rq) (ω : Bits (queryBits k kN kS L) → Y₁)
    {SC' : Type} [Fintype SC'] [DecidableEq SC'] (prf : Frg → Option M.NIProof)
    (keys : Fin n → B.KeyCoins)
    {shA₀ : AlgShape (Bits (queryBits k kN kS L)) Y (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n) (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (Stmt × (MURequest (SignOracle.none B.core) n ⊕ Rq)) (M.Response b) SC')
    (kq : ℕ)
    (Ev : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      (((A₀.absorbAssign (Resp' := MUResponse B.core ⊕ M.Response b)
        (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst))
      Psim Q → DB (Bits (queryBits k kN kS L)) (Out k e) → Prop)
    (p : MURequest (SignOracle.none B.core) n ⊕ Rq → Bool) (hpd : p default = false)
    (hpi : p idle = false) (hpdum : ∀ r, p (.inr (dummyR r)) = false)
    (hpc : ∀ i, p (.inl (.corrupt i)) = false) :
    simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign (Resp' := MUResponse B.core ⊕ M.Response b)
            (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).restrictAt
            sp ω).mapOut Prod.fst)) Psim Q kq)
        Ev ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          (((A₀.absorbAssign (Resp' := MUResponse B.core ⊕ M.Response b)
            (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).restrictAt
            sp ω).mapOut Prod.fst)) Psim Q kq)
        fun c D => Ev c D ∧
          ∀ r' ∈ Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
            (dummyS := dummyS) prf keys Q
            (((A₀.absorbAssign (Resp' := MUResponse B.core ⊕ M.Response b)
            (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).restrictAt
              sp ω).mapOut Prod.fst)).toTPKindAlg Psim Q c).1.1.logs, p r' = true →
            KFSignedAsk sp B pks F stmtPω toR sc ω r' := by
  have hP : ∀ T c r, MultiRelay.AsksIn (MUResponse B.core ⊕ M.Response b)
      (elimSide (kfRelaySide sp B pks F S toR dummyR sc ω idle).side
        ((kfRelaySide sp B pks F S toR dummyR sc ω idle).prog T c r))
      fun r' => p r' = true → KFSignedAsk sp B pks F stmtPω toR sc ω r' := by
    intro T c r
    refine fun ans r' h hp => ?_
    rcases asksIn_kfRelaySide_signed sp B pks F toR sc dummyR S ω idle T c r ans r' h
      with h' | h'
    · subst h'
      rcases r <;> simp [reqOf, hpc, hpdum] at hp
    · exact ⟨T, c, r, h'⟩
  have h1 := simProb_seAlgKF_asks (Qs := Qs) (rel := rel) (enc := enc) (dummyS := dummyS)
    (prf := prf) (keys := keys) (Q := Q) (A₀ := A₀)
    (G := kfRelaySide sp B pks F S toR dummyR sc ω idle)
    (sp := sp) (ω := ω) (Psim := Psim) (kq := kq) (Ev := Ev)
    (hP := hP) (p := p) (hpd := hpd) (hpi := hpi)
  exact h1.trans (simProb_mono _ _ fun c D h => ⟨h.1, fun r' hr' hp => (h.2 r' hr' hp).1 hp⟩)

end Chain

end RingSignature.KeyFree

end GordieHowe
