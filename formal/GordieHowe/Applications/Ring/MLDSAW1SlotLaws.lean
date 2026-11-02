-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseSGuess
public import GordieHowe.Applications.Ring.MLDSAW1CaseSplitRun
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeRelaySwap
public import GordieHowe.Applications.Ring.MLDSAW1RegShape
public import GordieHowe.Applications.Ring.AbsorbAssignSlot
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeChainW1

@[expose] public section

/-!
# The slot laws of the extraction run of the ML-DSA ring publishing `w₁`

The slot hypotheses `h1`, `h2` of `tsum_w1Guess_le`
(`GordieHowe/Applications/Ring/MLDSAW1CaseSGuess.lean`) for the extraction run of `seAlgKF` at
an adversary `A₀` with the side-mode key-free relay `kfRelaySide` at side coins `sc` absorbed at
the base component `ω`. The outcomes of the runs at all side coins share the type `W1Outcome`,
written through the shape term of `reg_seAlgKF_kfRelaySide`; the law at `sc` is the extraction
law cast to it along `natOutcome_eq_w1Outcome`. Changing slot `j`'s coin changes the relay's
programs only at slot `j` (`relayOf_kfRelaySide_prog_congr`): the law of slot `j`'s request is
unchanged (`toOuterMeasure_extLaw_withStep_label_of_blockNone`), and with equal public parts the
two coins' signatures differ by the swap `w1SlotSw` (`coinSwapAt_w1Slot`), so the joint law of
the request and the readout is unchanged (`toOuterMeasure_extLaw_withStep_label_and`).

- `RingSignature.KeyFree.relayOf_kfRelaySide_prog_congr`: the relay's program of a request
  reads only its own side coins.
- `w1ShapeS`, `W1Outcome`, `kfOutcome_eq_w1Outcome`, `natOutcome_eq_w1Outcome`: the shape of the
  simulation-extraction adversary and the shared outcome type.
- `w1SlotReq`, `w1SlotReq_eq_kfLabel`, `w1SlotReq_eq_slotRequest`: the request of slot `j`.
- `w1OutS`, `w1OutS_eq`, `w1CanonSig`, `w1CanonSig_eq`: the adversary's output and the readout
  (the canonical witness's signature).
- `firstJ_spec`, `w1MainSw_one`, `w1SlotSw`, `w1SlotSw_of_not_sign`, `coinSwapAt_w1Slot`: the
  swap of the signatures at a slot's request.
- `OracleProg.AllOut.bind_congr`, `OracleProg.allOut_of_forall`,
  `RingSignature.KeyFree.allOut_resolve_lift`, `KFOutOfSig`, `resolve_sigK_allOut`,
  `resolve_xK_stpB`, `resolve_kfProgK_swap_side`, `progSwap_kfRelaySide_side`: the relay's swap
  with the main requests moved only at the signer's results.
- `w1ProofSwG`, `w1MainSwG`, `w1MainSwG_one`, `w1MainSwG_reqOf_of_ne`, `w1SlotGate`: the swap
  gated to the slot's statements.
- `w1Enc_stmt_proofSwG`, `prog_comap_w1MainSwG`, `w1Rel_proofSwG_iff`: the hypotheses `hstmt`,
  `hsim`, `hrel` of `w1SlotLaw_h2` at `w1Enc`, a simulator reading only the program statement, and
  `w1Rel` (`w1Rel_iff_of_w1SlotPub_eq`).
- `readsClaimDB_w1CanonSig`: the readout reads only the claim, the database and the corruptions.
- `cast_natOutcome`, `toOuterMeasure_simPMF_congr`: the casts to the shared outcome type.
- `w1SlotLaw_h1_of_eqOn`, **`w1SlotLaw_h1`**: the law of slot `j`'s request does not depend on
  its coin.
- `w1CanonSigR`, `w1SlotGuess`, `w1SlotLaw_hG`: the readout at the registers, the guess event,
  and its bound by a slot's signature guess.
- **`slotLaws_kfExtractionLaw`**: `tsum_w1Guess_le` at the slot laws.
- `w1SlotLaw_h2_of_eqOn`, **`w1SlotLaw_h2`**: the joint law of the request and the readout
  depends on the coin only through the public part.
-/

namespace GordieHowe.OracleProg

variable {A B R S : Type*}

/-- **Continuations agreeing on the results satisfying `P`** give the same program after a
program whose results all satisfy `P`. -/
theorem AllOut.bind_congr {P : R → Prop} {f g : R → OracleProg A B S} (hfg : ∀ r, P r → f r = g r) :
    ∀ {p : OracleProg A B R}, p.AllOut P → p.bind f = p.bind g
  | .pure r, h => hfg r h
  | .query a k, h => by
    change OracleProg.query a (fun b => (k b).bind f) = OracleProg.query a fun b => (k b).bind g
    exact congrArg _ (funext fun b => AllOut.bind_congr hfg (h b))

/-- **A property of every value holds of every result.** -/
theorem allOut_of_forall {P : R → Prop} (h : ∀ r, P r) : ∀ p : OracleProg A B R, p.AllOut P
  | .pure r => h r
  | .query _ k => fun b => allOut_of_forall h (k b)

end GordieHowe.OracleProg

namespace GordieHowe.RingSignature.KeyFree

open Quantum Signature QROM OracleProg RingSignature.OracleSplit RingSignature.Insider

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  [DecidableEq X] {N n : ℕ} {TB : BaseTypes} (B : BaseSigner X Y N TB)
  {Pf PC : Type} {iFP : Fintype Pf} {iDP : DecidableEq Pf} {iFC : Fintype PC}
  {iDC : DecidableEq PC} {iNC : Nonempty PC}
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {SC X₀ R Pb : Type}
  (pks : Fin n → B.PK)
  {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))}
  (F : KFSignFactors sp Pb ksign) {stmtPω : (X → Y₁) → RingStmt B → X₀}
  (S : KFStmt stmtPω)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ}
  [Inhabited X] [Inhabited B.Pub]

/-- **The side-mode key-free relay's program of a request reads only its own side coins**: at
side coins `sc'` agreeing with `sc` at the request's number when it is a signing request, the
programs of the request are equal (`kfProgK_congr`). -/
theorem relayOf_kfRelaySide_prog_congr (sc sc' : Fin Q → SC) (ω : X → Y₁)
    (idle : MURequest (SignOracle.none B) n ⊕ R)
    (r : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y))
    (h : ∀ s Rg m (hc : (r.1.2 : ℕ) < Q), r.1.1 = .sign s Rg m →
      sc' ⟨r.1.2, hc⟩ = sc ⟨r.1.2, hc⟩) :
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q).prog r =
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).prog r := by
  change (recMain _ (kfProgK B pks toR dummyR sc' _ _ _ _ _ _)).mapOutput _ =
    (recMain _ (kfProgK B pks toR dummyR sc _ _ _ _ _ _)).mapOutput _
  rw [kfProgK_congr B pks toR dummyR _ _ _ _ _ _ h]
  rfl

/-- **The results of a lifted program, its side reads resolved**, are those of the program. -/
theorem allOut_resolve_lift {Yb Xs Ys α Req' Resp' : Type} (Rd : KFReads X Y Yb Xs Ys)
    (Tf Tb : X → Option Y) {P : α → Prop} :
    ∀ p : OracleProg (X ⊕ X) (Y ⊕ Yb) α, p.AllOut P →
      (resolve Rd.side (Rd.lift (Req' := Req') (Resp' := Resp') Tf Tb p)).AllOut P
  | .pure _, h => h
  | .query a k, h => by
    rw [KFReads.lift_query]
    rcases ha : a.elim Sum.inl Rd.pt with x | x
    · exact fun b => allOut_resolve_lift Rd Tf Tb _ (h _)
    · exact allOut_resolve_lift Rd Tf Tb _ (h _)

variable (sc : Fin Q → SC) in
/-- **The signatures the side-mode signer of request number `c` can return**: none, or, at a
signing request whose base-component program at `ω` read through `T` returns `(q, kp)`, the
published value and assignments of `kp` at a second component, with the signature of `q`. -/
def KFOutOfSig (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) : Prop :=
  o = none ∨ ∃ s Rg m, ∃ h : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg, ∃ q kp, ∃ y : Y ⊕ Y₁,
    r = .sign s Rg m ∧ (F.outB (pks s) Rg c m (sc ⟨c, h.1⟩)).run (ωT sp ω T) = some (q, kp) ∧
      o = some (kp.2.1, q.2, kp.2.2 (prfOf sp y))

/-- **The resolved side-mode signature returns only `KFOutOfSig`.** -/
theorem resolve_sigK_allOut (sc : Fin Q → SC) (ω : X → Y₁) (T : X → Option Y) (c : ℕ)
    (r : Req B PS adm n) :
    (resolve ω ((KFReads.viaSide (fun y => (sp y).1) ω).lift
        (Req' := MURequest (SignOracle.none B) n ⊕ R) (Resp' := MUResponse B ⊕ Pf)
        (fun _ => none) ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none)
        (sigK B pks sc (sgnB sp B F S) c r))).AllOut
      (KFOutOfSig sp B pks F sc ω T c r) := by
  rcases r with _ | ⟨s, Rg, m⟩ | _
  · exact Or.inl rfl
  · dsimp only [sigK]
    split_ifs with hc
    · unfold sgnB
      rw [KFReads.lift_bind, resolve_bind, resolve_lift_baseL_viaSide]
      have hω : (fun x => (((KFReads.viaSide (fun y => (sp y).1) ω).tabB T fun _ => none) x).map
          (fun y => (sp y).1) |>.getD (ω x)) = ωT sp ω T := ωT_eq sp ω T
      simp only [OracleProg.bind]
      rw [hω]
      rcases hrun : (F.outB (pks s) Rg c m (sc ⟨c, hc.1⟩)).run (ωT sp ω T) with _ | ⟨q, kp⟩
      · dsimp only
        refine allOut_resolve_lift (KFReads.viaSide (fun y => (sp y).1) ω) _ _ _ ?_
        intro _
        exact AllOut.mapOutput _ (allOut_of_forall (fun _ => Or.inl rfl) _)
      · dsimp only
        refine allOut_resolve_lift (KFReads.viaSide (fun y => (sp y).1) ω) _ _ _ ?_
        intro y
        exact Or.inr ⟨s, Rg, m, hc, q, kp, y, rfl, hrun, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **The resolved side-mode statement** is the statement at the base component (`xPω`). -/
theorem resolve_xK_stpB (ω : X → Y₁) (T : X → Option Y) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    resolve ω ((KFReads.viaSide (fun y => (sp y).1) ω).lift
        (Req' := MURequest (SignOracle.none B) n ⊕ R) (Resp' := MUResponse B ⊕ Pf)
        (lastAssign (asgOf B o))
        ((KFReads.viaSide (fun y => (sp y).1) ω).tabB T (lastAssign (asgOf B o)))
        (xK B (stpB sp B S) r o)) = .pure (xPω sp B stmtPω ω T r o) := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
  all_goals try rfl
  rw [xK, stpB, KFReads.lift_mapOutput, resolve_mapOutput, resolve_lift_baseL_viaSide]
  change OracleProg.pure (some _) = _
  rw [xPω, ← S.run_stmtPB, ← ωT_eq sp ω]
  rfl

/-- **The resolved side-mode key-free relay program with one request's signature moved**
(`resolve_kfProgK_swap` with `sw` moving the main requests alike only at the signatures the
signer can return, `KFOutOfSig`, and at the statements it then asks, `xPω`). -/
theorem resolve_kfProgK_swap_side (sc sc' : Fin Q → SC) (ω : X → Y₁) (T : X → Option Y) (c : ℕ)
    (r : Req B PS adm n) (swσ : B.BSig → B.BSig)
    (sw : MURequest (SignOracle.none B) n ⊕ R → MURequest (SignOracle.none B) n ⊕ R)
    (hφ : CoinSwapAt sp B pks F sc sc' ω T c r swσ)
    (hsw : ∀ o, KFOutOfSig sp B pks F sc ω T c r o →
      sw (reqOf B toR dummyR c r o (xPω sp B stmtPω ω T r o)) =
        reqOf B toR dummyR c r (mapSig B swσ o) (xPω sp B stmtPω ω T r o)) :
    resolve ω (kfProgK B pks toR dummyR sc' (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r) =
      (resolve ω (kfProgK B pks toR dummyR sc (sgnB sp B F S) (stpB sp B S)
        (KFReads.viaSide (fun y => (sp y).1) ω) T c r)).translate (Sum.map id sw)
        fun _ b => b := by
  unfold kfProgK
  rw [resolve_bind, resolve_sigK_sgnB_swap sp B pks F S sc sc' ω T c r swσ hφ, mapOutput_bind,
    resolve_bind, translate_bind, ← resolve_translate_main, translate_main_lift]
  refine AllOut.bind_congr (fun o ho => ?_) (resolve_sigK_allOut sp B pks F S sc ω T c r)
  simp only [Function.comp_def]
  rw [← resolve_translate_main, translate_bind, translate_main_lift, asgOf_mapSig, xK_mapSig,
    resolve_bind, resolve_bind, resolve_xK_stpB]
  simp only [OracleProg.bind, translate, translate_bind, Sum.map_inr, hsw o ho, replyOf_mapSig]

/-- **(ii-c) with the main requests moved only where the signer can return**
(`progSwap_kfRelaySide` with `resolve_kfProgK_swap_side`): `sw` needs to move the main request of
`r₀` alike only at the signatures `KFOutOfSig` and the statements `xPω` asked at them. -/
theorem progSwap_kfRelaySide_side
    (houtB : ∀ pk Rg c m s s', Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (F.outB pk Rg c m s) (F.outB pk Rg c m s'))
    (hstmt : ∀ (Rg : KeyRing B.PK N) (m : B.Msg) (y y' : B.Pub), Lockstep (fun _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) (S.stmtPB ⟨Rg, m, y⟩) (S.stmtPB ⟨Rg, m, y'⟩))
    (hcO : ∀ pk Rg c m s, CountsLE (fun _ => true) F.qOut (F.outB pk Rg c m s))
    (hcS : ∀ x, CountsLE (fun _ => true) S.qSt (S.stmtPB x))
    (sc sc' : Fin Q → SC) (ω : X → Y₁) (idle : MURequest (SignOracle.none B) n ⊕ R)
    (J : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y) → Bool)
    (r₀ : (Req B PS adm n × Fin (Q + 1)) × (X → Option Y)) (swσ : B.BSig → B.BSig)
    (sw : Equiv.Perm (MURequest (SignOracle.none B) n ⊕ R))
    (hoff : ∀ r, J r = false → ∀ s Rg m (hc : (r.1.2 : ℕ) < Q), r.1.1 = .sign s Rg m →
      sc' ⟨r.1.2, hc⟩ = sc ⟨r.1.2, hc⟩)
    (hφ : CoinSwapAt sp B pks F sc sc' ω r₀.2 r₀.1.2 r₀.1.1 swσ)
    (hsw : ∀ o, KFOutOfSig sp B pks F sc ω r₀.2 r₀.1.2 r₀.1.1 o →
      sw (reqOf B toR dummyR r₀.1.2 r₀.1.1 o (xPω sp B stmtPω ω r₀.2 r₀.1.1 o)) =
        reqOf B toR dummyR r₀.1.2 r₀.1.1 (mapSig B swσ o) (xPω sp B stmtPω ω r₀.2 r₀.1.1 o))
    (hidle : sw idle = idle) :
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q).ProgSwap
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc' ω idle) Q).prog J (· = r₀) sw
      (AssignRelay.recordSw sw) := by
  have hc : ∀ sc₁ : Fin Q → SC, SidesLE (F.qOut + S.qSt)
      (AssignRelay.relayOfProg (kfRelaySide sp B pks F S toR dummyR sc₁ ω idle) Q r₀) := fun sc₁ =>
    sidesLE_of_countsLE (CountsLE.recMain (fun _ => rfl) _
      (countsLE_kfProgK_sgnB sp B pks F S toR dummyR hcO hcS sc₁ ω r₀.2 r₀.1.2 r₀.1.1)).mapOutput
  refine AssignRelay.progSwap_relayOf _ _ J r₀ sw (fun r hr => ?_) (hc sc) (hc sc')
    (lockstep_relayOfProg_kfRelaySide sp B pks F S toR dummyR houtB hstmt sc sc' ω idle
      r₀).startsSide
    (resolve_kfProgK_swap_side sp B pks F S toR dummyR sc sc' ω r₀.2 r₀.1.2 r₀.1.1 swσ sw hφ hsw)
    rfl hidle
  change (recMain _ (kfProgK B pks toR dummyR sc' _ _ _ _ _ _)).mapOutput _ =
    (recMain _ (kfProgK B pks toR dummyR sc _ _ _ _ _ _)).mapOutput _
  rw [kfProgK_congr B pks toR dummyR _ _ _ _ _ _ (hoff r hr)]
  rfl

end GordieHowe.RingSignature.KeyFree

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree GordieHowe.QROM
open GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}
  (sp : OracleSplit Y Y₁ (XOut kh e))

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "X₀f" => W1ExpStmt prims RMsg N
local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "PSh" => w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk
local notation "PSf" => (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb
  honest chk)
local notation "Rq" => W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q

attribute [local instance] admDecF

variable {Frg : Type}

section SlotLaws

variable [NeZero n] {Stmt Wit : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt} [Inhabited Mc.NIProof]
  {SC' : Type} [Fintype SC'] [DecidableEq SC']


/-- **The shape of the simulation-extraction adversary at the ML-DSA ring publishing `w₁`**:
`seAlgKFS` at the restricted shape of `absorbAssign_kfRelaySide_toShape`, for every side coin
(`reg_seAlgKF_kfRelaySide`). -/
noncomputable abbrev w1ShapeS
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)] (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f)) :
    AlgShape Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq)) (Mc.Response b) :=
  seAlgKFS (Stmt := Stmt) (M := Mc) (B := Bf)
    ((A₀.toShape.absorbAssignS (Req' := MURequest (SignOracle.none Bf) n ⊕ Rq)
      (Resp' := MUResponse Bf ⊕ Mc.Response b) Y₁ Q 1 1
      ((w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO).qOut +
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp).qSt)).restrictAtS Y₁ (XOut kh e))

/-- **The outcomes of the extraction run at the ML-DSA ring publishing `w₁`**, written through the
shape term of `reg_seAlgKF_kfRelaySide`: `KFOutcome` with the workspace, width and slots of
`seAlgKFS` at the restricted shape of the absorbed adversary. They do not mention the side
coins. -/
abbrev W1Outcome
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)] (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) : Type :=
  BaseGame.Tuple Xq (Out kh e)
    (CWork (w1ShapeS sp hO A₀ (Stmt := Stmt) (Q := Q)).CntW
      (w1ShapeS sp hO A₀ (Stmt := Stmt) (Q := Q)).width Xq (XOut kh e)
      (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq)) (Mc.Response b)
      (w1ShapeS sp hO A₀ (Stmt := Stmt) (Q := Q)).slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins)
    (kq + Q * Psim.q) × DB Xq (Out kh e)

/-- **The extraction outcomes at any side coins are `W1Outcome`** (rfl, against the shape term
only). -/
theorem kfOutcome_eq_w1Outcome
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp) (ξ :
        Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) :
    KFOutcome (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q
              kq = W1Outcome sp hO A₀ Psim kq :=
  rfl

/-- **The extraction outcomes at any side coins, typed through `SPBCS.Reg`, are `W1Outcome`**
(rfl, against the shape term only). -/
theorem natOutcome_eq_w1Outcome
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp) (ξ :
        Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) :
    (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS :=
        dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q)
              (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = W1Outcome sp hO A₀ Psim kq :=
  rfl

/-- **The request of slot `j` of an outcome**: the first entry of number `j` (`jTest Q j`) of the
relay's final record, read from the outcome's composed registers. -/
noncomputable def w1SlotReq
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)] (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (j : Fin Q) (o : W1Outcome sp hO A₀ Psim kq) :
    Option (AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q) :=
  MultiRelay.firstJ (AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := (RingSignature.Insider.Req Bf
      PSf adm n)) Q j)
    (MultiRelay.recList o.1.out.adv.workspace.1.1.work.1.1.record)

/-- **The request of slot `j` is the label `kfLabel`** of the relay's test of number `j`, at any
side coins (rfl). -/
theorem w1SlotReq_eq_kfLabel
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp) (ξ :
        Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (j : Fin Q)
    (o : W1Outcome sp hO A₀ Psim kq) :
    w1SlotReq sp hO A₀ Psim kq j o = kfLabel (rel := rel) (enc := penc) (dummyS := dummyS)
      (prf := prf) (keys := ξ) (Q := Q) (A := (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕
          Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) (Psim
              := Psim) (kq := kq)
      (fun w => Distinguisher.jLabel (AssignRelay.relayOf (kfRelaySide sp Bf (fun j => (Bf).pk (ξ
          j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q) (AdaptiveIAlg.jTest Q j) w.1.1) o :=
  rfl

/-- **The request of slot `j` is `slotRequest`** at any side coins (rfl). -/
theorem w1SlotReq_eq_slotRequest
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp) (ξ :
        Fin n → (Bf).KeyCoins)
    (ω : Xq → Y₁) (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (j : Fin Q)
    (o : W1Outcome sp hO A₀ Psim kq) :
    w1SlotReq sp hO A₀ Psim kq j o = slotRequest (rel := rel) (enc := penc) (dummyS := dummyS)
      prf ξ Q A₀ (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) sp ω Psim j o.1.out :=
  rfl

/-- **The output of the adversary in an outcome**: `A₀`'s output at its workspace, read through
the registers of the shape term. -/
noncomputable def w1OutS
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (o : W1Outcome sp hO A₀ Psim kq) : Frg × X₀f :=
  A₀.out o.1.out.adv.workspace.1.1.work.1.1.inner.1.1.1.1.1.1.work

/-- **The output of an outcome is the absorbed adversary's output** at any side coins (rfl). -/
theorem w1OutS_eq
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁) (idle : MURequest (SignOracle.none Bf) n ⊕ Rq)
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (prf : Frg → Option Mc.NIProof)
    (o : W1Outcome sp hO A₀ Psim kq) :
    w1OutS sp hO A₀ Psim kq o = (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst).out
      (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut
              Prod.fst)).toTPKindAlg Psim Q o.1.out).1.1.work :=
  rfl

/-- **The readout of the registers and the database**: the canonical witness's signature. -/
noncomputable def w1CanonSigR
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (pks : Fin n → PubKey p prims)
    (c : CWork (w1ShapeS sp hO A₀ (Stmt := Stmt) (Q := Q)).CntW
      (w1ShapeS sp hO A₀ (Stmt := Stmt) (Q := Q)).width Xq (XOut kh e)
      (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq)) (Mc.Response b)
      (w1ShapeS sp hO A₀ (Stmt := Stmt) (Q := Q)).slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins)
    (D₀ : DB Xq (Out kh e)) : Option (FIPSSignature p prims) :=
  (kfCanon Mc Ext (fun _ w => w)
    (w1Ok prims O Mo βmin tol enc k D bmsg adm pks
      (A₀.out c.adv.workspace.1.1.work.1.1.inner.1.1.1.1.1.1.work)
      ((Quantum.requests c.adv.workspace.1.1.logs).take Q))
    (A₀.out c.adv.workspace.1.1.work.1.1.inner.1.1.1.1.1.1.work).2 D₀).map fun w => w.sig

/-- **The readout of an outcome**: the signature of the canonical witness (`kfCanon`) at the test
`w1Ok` of the output `w1OutS` and the first `Q` logged requests, for the users' keys `pks`
(`w1CanonSigR` at the outcome's registers and database). -/
noncomputable def w1CanonSig
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (pks : Fin n → PubKey p prims) (o : W1Outcome sp hO A₀ Psim kq) :
    Option (FIPSSignature p prims) :=
  w1CanonSigR sp hO A₀ Psim Ext pks o.1.out o.2

/-- **The readout is the canonical witness's signature of `kfCanonOut`** at any side coins
(rfl). -/
theorem w1CanonSig_eq
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁) (idle : MURequest (SignOracle.none Bf) n ⊕ Rq)
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (prf : Frg → Option Mc.NIProof)
    (o : W1Outcome sp hO A₀ Psim kq) :
    w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o =
      (kfCanonOut (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign (Resp'
          := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst) Psim Ext
        (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
        o.1.out o.2).1.map fun w => w.sig :=
  rfl

/-- **The first request satisfying `J` satisfies `J`.** -/
theorem firstJ_spec {Req : Type} {J : Req → Bool} {es : List (Option Req)} {r : Req}
    (h : MultiRelay.firstJ J es = some r) : J r = true := by
  unfold MultiRelay.firstJ at h
  rcases hf : es.find? (fun e => e.any J) with _ | e
  · rw [hf] at h
    simp at h
  · rw [hf] at h
    have hJ := List.find?_some hf
    rcases e with _ | e
    · simp at h
    · simp only [Option.bind_some, id, Option.some.injEq] at h
      subst h
      simpa using hJ

/-- **The moved main requests at the identity move of the signatures** are the main requests. -/
theorem w1MainSw_one (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (x : MURequest (SignOracle.none Bf) n ⊕ Rq) : w1MainSw t₀ 1 x = x := by
  rcases x with _ | (⟨a, t, σ⟩ | d)
  · rfl
  · simp [w1MainSw, w1ProofSw]
  · rfl

open Classical in
/-- **The move of the signatures at a slot's request between two coins**: the transposition of
the two coins' signatures (`w1SlotSig`) when both sign, the identity otherwise. -/
noncomputable def w1SlotSw (pks : Fin n → PubKey p prims) (ω : Xq → Y₁)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (c c' : KFCoins (p := p) (T := T) k D Y₁) : Equiv.Perm (FIPSSignature p prims) :=
  match w1SlotSig sp pks ω r c, w1SlotSig sp pks ω r c' with
  | some σ, some σ' => Equiv.swap σ σ'
  | _, _ => 1

/-- **The move at a request that is not a signing request is the identity.** -/
theorem w1SlotSw_of_not_sign (pks : Fin n → PubKey p prims) (ω : Xq → Y₁)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (c c' : KFCoins (p := p) (T := T) k D Y₁) (hr : ∀ s Rg m, r.1.1 ≠ .sign s Rg m) :
    w1SlotSw sp pks ω r c c' = 1 := by
  have hn : ∀ c'' : KFCoins (p := p) (T := T) k D Y₁, w1SlotSig sp pks ω r c'' = none := by
    intro c''
    unfold w1SlotSig w1SlotOut
    rcases h : r.1.1 with _ | ⟨s, Rg, m⟩ | _
    · rfl
    · exact absurd h (hr s Rg m)
    · rfl
  unfold w1SlotSw
  rw [hn c, hn c']

open Classical in
/-- **The signature of the proof requests tagged `t₀` with a statement in `G` moved by `swσ`**;
other proof requests kept. -/
noncomputable def w1ProofSwG (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (G : W1BStmt prims RMsg N → Prop) (swσ : Equiv.Perm (FIPSSignature p
        prims)) :
    Equiv.Perm (W1BStmt prims RMsg N × (RingSignature.Insider.Req Bf PSf adm n
        × Fin (Q + 1)) ×
      FIPSSignature p prims) where
  toFun q := (q.1, q.2.1, if q.2.1 = t₀ ∧ G q.1 then swσ q.2.2 else q.2.2)
  invFun q := (q.1, q.2.1, if q.2.1 = t₀ ∧ G q.1 then swσ.symm q.2.2 else q.2.2)
  left_inv q := by
    rcases q with ⟨a, t, σ⟩
    by_cases h : t = t₀ ∧ G a <;> simp [h]
  right_inv q := by
    rcases q with ⟨a, t, σ⟩
    by_cases h : t = t₀ ∧ G a <;> simp [h]

/-- **The main requests with the signature of the proof requests tagged `t₀` with a statement in
`G` moved by `swσ`.** -/
noncomputable def w1MainSwG (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (G : W1BStmt prims RMsg N → Prop) (swσ : Equiv.Perm (FIPSSignature p
        prims)) :
    Equiv.Perm (MURequest (SignOracle.none Bf) n ⊕ Rq) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (w1ProofSwG sp t₀ G swσ) (Equiv.refl _))

/-- **The gated move at the identity move of the signatures** is the identity. -/
theorem w1MainSwG_one (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (G : W1BStmt prims RMsg N → Prop) (x : MURequest (SignOracle.none Bf) n ⊕
        Rq) :
    w1MainSwG sp t₀ G 1 x = x := by
  rcases x with _ | (⟨a, t, σ⟩ | d)
  · rfl
  · simp [w1MainSwG, w1ProofSwG]
  · rfl

/-- **The gated move fixes the main request of a request with another tag.** -/
theorem w1MainSwG_reqOf_of_ne (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (G : W1BStmt prims RMsg N → Prop) (swσ : Equiv.Perm (FIPSSignature p prims))
    (r : RingSignature.Insider.Req Bf PSf adm n) (c : Fin (Q + 1)) (ht : (r, w1Num Q c) ≠ t₀)
    (o : Option (BucketVec p × FIPSSignature p prims × List (Assignment Xq Y)))
    (x₀ : Option X₀f) :
    w1MainSwG sp t₀ G swσ (reqOf Bf (w1ToR (PS := PSh) (Q := Q)) w1DummyR c r o x₀) =
      reqOf Bf (w1ToR (PS := PSh) (Q := Q)) w1DummyR c r o x₀ := by
  rcases r with _ | _ | _ <;> rcases o with _ | ⟨y, σ, a⟩ <;> rcases x₀ with _ | x <;>
    first
    | rfl
    | (simp [reqOf, w1MainSwG, w1ProofSwG, w1ToR, ht])

/-- **The gate of the swap at a slot's request**: the bounded statements the side-mode signer of
the request asks at the side coins `sc` (`xPω` at `KFOutOfSig`). -/
def w1SlotGate [Inhabited Xq] (hO : O.ReadsFst sp) (pks : Fin n → PubKey p prims)
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (xb : W1BStmt prims RMsg N) : Prop :=
  ∃ o, KFOutOfSig sp Bf pks (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO) sc ω r.2
      r.1.2 r.1.1 o ∧
    ∃ x₀, xPω sp Bf (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) ω r.2 r.1.1 o = some x₀ ∧
      w1Bnd x₀ = xb

/-- **Equal public parts give a swap of the signatures** (`CoinSwapAt`): at side coins `sc₁`,
`sc₂` whose coins at the request's number `j` have equal public parts (`w1SlotPub`), the
key-free signer's base-component program at `sc₂` runs as at `sc₁` with the signature moved by
`w1SlotSw`. -/
theorem coinSwapAt_w1Slot [Inhabited Xq] (hO : O.ReadsFst sp) (pks : Fin n → PubKey p prims)
    (sc₁ sc₂ : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q) (j : Fin Q)
    (hj : (r.1.2 : ℕ) = j)
    (hpub : w1SlotPub sp pks ω r (sc₁ j) = w1SlotPub sp pks ω r (sc₂ j)) :
    CoinSwapAt sp Bf pks (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO) sc₁ sc₂ ω
      r.2 r.1.2 r.1.1 (w1SlotSw sp pks ω r (sc₁ j) (sc₂ j)) := by
  intro s Rg m h hr
  have hcj : (⟨r.1.2, h.1⟩ : Fin Q) = j := Fin.ext hj
  rw [hcj]
  change (w1KFOutB prims O sp βmin tol enc k D bmsg (pks s) Rg r.1.2 m (sc₂ j)).run
      (ωT sp ω r.2) =
    ((w1KFOutB prims O sp βmin tol enc k D bmsg (pks s) Rg r.1.2 m (sc₁ j)).run
      (ωT sp ω r.2)).map _
  erw [run_w1KFOutB, run_w1KFOutB]
  have hp := hpub
  simp only [w1SlotPub, w1SlotOut, hr] at hp
  unfold w1SlotSw w1SlotSig w1SlotOut
  simp only [hr]
  rcases h1 : w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω r.2) (pks s) Rg r.1.2 m
      (sc₁ j) with _ | ⟨q, σ⟩ <;>
    rcases h2 : w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω r.2) (pks s) Rg r.1.2 m
      (sc₂ j) with _ | ⟨q', σ'⟩ <;> rw [h1, h2] at hp <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hp
  all_goals first
    | rfl
    | (subst hp
       exact congrArg some (Prod.ext (Prod.ext rfl (Equiv.swap_apply_left σ σ').symm) rfl))

/-- **The readout of two outcomes agrees** when their claims' statements, their databases and their
corruptions among the first `Q` main requests agree (the content of `readsClaimDB_w1CanonSig`,
stated on `W1Outcome`). -/
theorem w1CanonSig_congr
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)] (hO : O.ReadsFst sp)
    (ξ : Fin n → (Bf).KeyCoins)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) (o o' : W1Outcome sp hO A₀ Psim kq)
    (hx : (w1OutS sp hO A₀ Psim kq o).2 = (w1OutS sp hO A₀ Psim kq o').2) (hD : o.2 = o'.2)
    (hcor : ∀ i, (Sum.inl (MURequest.corrupt i) : MURequest (SignOracle.none Bf) n ⊕ Rq) ∈
        (Quantum.requests o.1.out.adv.workspace.1.1.logs).take Q ↔
      (Sum.inl (MURequest.corrupt i) : MURequest (SignOracle.none Bf) n ⊕ Rq) ∈
        (Quantum.requests o'.1.out.adv.workspace.1.1.logs).take Q) :
    w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o =
      w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o' := by
  have hok : w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j))
        (w1OutS sp hO A₀ Psim kq o) ((Quantum.requests o.1.out.adv.workspace.1.1.logs).take Q) =
      w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j))
        (w1OutS sp hO A₀ Psim kq o') ((Quantum.requests o'.1.out.adv.workspace.1.1.logs).take Q) :=
    funext fun w => propext (by
      unfold w1Ok w1Honest
      rw [hx]
      exact and_congr_right fun _ => exists_congr fun i => and_congr_right fun _ =>
        not_congr (hcor i))
  unfold w1CanonSig w1CanonSigR
  congr 2 <;> first | exact hok | exact hx | exact hD

/-- **The readout reads only the claim, the database and the corruptions** among the first `Q`
main requests (`ReadsClaimDB`): the canonical witness reads the claim's statement and the
database, and `w1Ok` reads the logged requests only through the corruptions (`w1Honest`). -/
theorem readsClaimDB_w1CanonSig
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) (z : FIPSSignature p prims) :
    ReadsClaimDB (rel := rel) (enc := penc) (dummyS := dummyS) (prf := prf) (keys := ξ) (Q := Q)
      (A := (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) (Psim
              := Psim) (kq := kq)
      (fun o => w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z) := by
  intro o o' hc hD hcor
  exact iff_of_eq (congrArg (· = some z) (w1CanonSig_congr sp hO ξ A₀ Psim kq Ext o o'
    (congrArg SPBCS.Claim.stmt hc) hD hcor))

/-- **The cast of the outcomes along `natOutcome_eq_w1Outcome` is the identity.** -/
theorem cast_natOutcome
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hO : O.ReadsFst sp)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (o : W1Outcome sp hO A₀ Psim kq) :
    @Eq (W1Outcome sp hO A₀ Psim kq)
      (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
        idle prf A₀ Psim kq sc) o) o :=
  @cast_eq (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS :=
      dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q)
              (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) _ o

/-- **The extraction laws of equal adversaries on an event of a shared outcome type**: at
`Ag₂ = Ag'`, the laws give the same probability to the preimages of `S` under the casts of their
outcome types (`SPBCS.Reg`) to `Ω`. -/
theorem toOuterMeasure_simPMF_congr
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {shAg₂ : AlgShape Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq)) (Mc.Response b)} {Ag₂ Ag' : AdaptiveIAlg shAg₂ (Claim X₀f Mc.NIProof)} (h : Ag₂ = Ag')
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) {Ω : Type}
    (h₂ : (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg Ag₂ Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = Ω)
    (h' : (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg Ag' Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = Ω) (S : Set Ω) :
    (simPMF (outEquiv kh e) (extAdv Qs Ag₂ Psim Q kq)).toOuterMeasure (cast h₂ ⁻¹' S) =
      (simPMF (outEquiv kh e) (extAdv Qs Ag' Psim Q kq)).toOuterMeasure (cast h' ⁻¹' S) := by
  subst h
  rfl

/-- **`toOuterMeasure_simPMF_congr` at named preimages**: at `Ag₂ = Ag'`, sets `S₂` and `S'` that
are the preimages of `S` under the casts of the outcome types get the same probability. -/
theorem toOuterMeasure_simPMF_congr_of_preimage
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {shAg₂ : AlgShape Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq)) (Mc.Response b)} {Ag₂ Ag' : AdaptiveIAlg shAg₂ (Claim X₀f Mc.NIProof)} (h : Ag₂ = Ag')
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) {Ω : Type}
    (h₂ : (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg Ag₂ Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = Ω)
    (h' : (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg Ag' Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = Ω) (S : Set Ω)
    {S₂ : Set (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg Ag₂ Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e))}
    {S' : Set (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg Ag' Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e))}
    (hS₂ : cast h₂ ⁻¹' S = S₂) (hS' : cast h' ⁻¹' S = S') :
    (simPMF (outEquiv kh e) (extAdv Qs Ag₂ Psim Q kq)).toOuterMeasure S₂ =
      (simPMF (outEquiv kh e) (extAdv Qs Ag' Psim Q kq)).toOuterMeasure S' := by
  subst hS₂ hS'
  exact toOuterMeasure_simPMF_congr (Qs := Qs) (Λ := Λ) (E := E) (hb := hb) (honest := honest)
    (chk := chk) sp h Psim kq h₂ h' S


/-- **Heterogeneously equal laws give an event of a shared outcome type the same probability**,
read through casts of their outcome types to `Ω`. -/
theorem _root_.PMF.toOuterMeasure_cast_preimage_heq {α β Ω : Type} {μ : PMF α} {ν : PMF β}
    (h : μ ≍ ν) (h₂ : α = Ω) (h' : β = Ω) (S : Set Ω) :
    μ.toOuterMeasure (cast h₂ ⁻¹' S) = ν.toOuterMeasure (cast h' ⁻¹' S) := by
  subst h₂ h'
  cases h
  rfl

-- TODO(unbundle-M4): at the concrete relays, combining the `HEq` of
-- `seAlgKF_absorbAssign_eq_withStep` with its shape equation unfolds the concrete `Fintype`
-- instances of the two shapes; at free relays it does not
/-- **The outcome types of the absorbed adversaries with `G'` and with `G` and `p'`'s steps are
equal**, for relays of `G'` that are `G`'s with the programs `p'` of the same shape. -/
theorem tuple_absorbAssign_withStep_eq
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit}
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    {G G' : AssignRelay Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm) (MURequest (SignOracle.none Bf) n ⊕ Rq)
      (MUResponse Bf ⊕ Mc.Response b) Xs Ys}
    {p' : (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × (Xq → Option Y) →
      OracleProg ((Xq ⊕ Xs) ⊕ (MURequest (SignOracle.none Bf) n ⊕ Rq))
        ((Y ⊕ Ys) ⊕ Option (MUResponse Bf ⊕ Mc.Response b))
        (Option (AssignRelay.RespD Xq Y (RingSignature.Insider.Resp Bf PSf adm)
          (MURequest (SignOracle.none Bf) n ⊕ Rq) (MUResponse Bf ⊕ Mc.Response b)))}
    (hG : G'.relayOf Q = (G.relayOf Q).withProg p')
    (hS : (G.relayOf Q).SameShape p')
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) :
    (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
        prf ξ Q
        (((A₀.absorbAssign G' Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) =
      (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg ((seAlgKF (rel := rel) (enc := penc) (dummyS :=
          dummyS) prf ξ Q
        (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).withStep
        (AdaptiveIAlg.absorbTabStep (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)
          (seTwoKF (Proof := Mc.Response b) Bf rel penc dummyS ((Bf).pk ∘ ξ) Q)
          ((A₀.absorbAssign G Q).restrictStep
            ((A₀.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
              ((A₀.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp ω))) Psim Q) (kq + Q * Psim.q) ×
        DB Xq (Out kh e)) := by
  have hs := seAlgKF_absorbAssign_toShape_eq (rel := rel) (enc := penc) (dummyS := dummyS)
    (Stmt := Stmt) prf ξ Q (A := A₀) (sp := sp) (H₁ := ω) (f := Prod.fst) hG
  have h := seAlgKF_absorbAssign_eq_withStep (rel := rel) (enc := penc) (dummyS := dummyS)
    (Stmt := Stmt) prf ξ Q (A := A₀) (sp := sp) (H₁ := ω) (f := Prod.fst) hG hS
  congr 3

/-- **The extraction laws of the absorbed adversaries with `G'` and with `G` and `p'`'s steps agree
on an event of a shared outcome type**, at named preimages
    (`toOuterMeasure_simPMF_congr_of_preimage`). -/
theorem toOuterMeasure_simPMF_absorbAssign_withStep
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit}
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    {G G' : AssignRelay Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm) (MURequest (SignOracle.none Bf) n ⊕ Rq)
      (MUResponse Bf ⊕ Mc.Response b) Xs Ys}
    {p' : (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × (Xq → Option Y) →
      OracleProg ((Xq ⊕ Xs) ⊕ (MURequest (SignOracle.none Bf) n ⊕ Rq))
        ((Y ⊕ Ys) ⊕ Option (MUResponse Bf ⊕ Mc.Response b))
        (Option (AssignRelay.RespD Xq Y (RingSignature.Insider.Resp Bf PSf adm)
          (MURequest (SignOracle.none Bf) n ⊕ Rq) (MUResponse Bf ⊕ Mc.Response b)))}
    (hG : G'.relayOf Q = (G.relayOf Q).withProg p')
    (hS : (G.relayOf Q).SameShape p')
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) {Ω : Type}
    (h₂ : (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS :=
        dummyS) prf ξ Q
        (((A₀.absorbAssign G' Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = Ω)
    (h' : (BaseGame.Tuple Xq (Out kh e) (SPBCS.Reg ((seAlgKF (rel := rel) (enc := penc) (dummyS :=
        dummyS) prf ξ Q
        (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).withStep
        (AdaptiveIAlg.absorbTabStep (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)
          (seTwoKF (Proof := Mc.Response b) Bf rel penc dummyS ((Bf).pk ∘ ξ) Q)
          ((A₀.absorbAssign G Q).restrictStep
            ((A₀.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
              ((A₀.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp ω))) Psim Q) (kq + Q * Psim.q) ×
      DB Xq (Out kh e)) = Ω) (S : Set Ω) {S₂ S' : Set _} (hS₂ : cast h₂ ⁻¹' S = S₂)
    (hS' : cast h' ⁻¹' S = S') :
    (simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ
        Q
        (((A₀.absorbAssign G' Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).toOuterMeasure S₂ =
      (simPMF (outEquiv kh e) (extAdv Qs ((seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q
        (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).withStep
        (AdaptiveIAlg.absorbTabStep (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)
          (seTwoKF (Proof := Mc.Response b) Bf rel penc dummyS ((Bf).pk ∘ ξ) Q)
          ((A₀.absorbAssign G Q).restrictStep
            ((A₀.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
              ((A₀.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp ω))) Psim Q kq)).toOuterMeasure
                  S' := by
  subst hS₂ hS'
  have hs := seAlgKF_absorbAssign_toShape_eq (rel := rel) (enc := penc) (dummyS := dummyS)
    (Stmt := Stmt) prf ξ Q (A := A₀) (sp := sp) (H₁ := ω) (f := Prod.fst) hG
  have h := seAlgKF_absorbAssign_eq_withStep (rel := rel) (enc := penc) (dummyS := dummyS)
    (Stmt := Stmt) prf ξ Q (A := A₀) (sp := sp) (H₁ := ω) (f := Prod.fst) hG hS
  have hμ : simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS :=
      dummyS) prf ξ Q
        (((A₀.absorbAssign G' Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq) ≍
      simPMF (outEquiv kh e) (extAdv Qs ((seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf
          ξ Q
        (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)).withStep
        (AdaptiveIAlg.absorbTabStep (((A₀.absorbAssign G Q).restrictAt sp ω).mapOut Prod.fst)
          (seTwoKF (Proof := Mc.Response b) Bf rel penc dummyS ((Bf).pk ∘ ξ) Q)
          ((A₀.absorbAssign G Q).restrictStep
            ((A₀.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
              ((A₀.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp ω))) Psim Q kq) := by
    congr
  exact PMF.toOuterMeasure_cast_preimage_heq hμ h₂ h' S


omit nttOps in
/-- **The law of a cast along `h` at a set whose preimage is named**: the image law of `μ` under
`cast h` gives `S` the probability that `μ` gives the preimage `S'`. -/
theorem toOuterMeasure_map_cast_of_preimage {α β : Type} (μ : PMF α) (h : α = β) (S : Set β)
    {S' : Set α} (hS : cast h ⁻¹' S = S') :
    (μ.map (cast h)).toOuterMeasure S = μ.toOuterMeasure S' := by
  rw [PMF.toOuterMeasure_map_apply, hS]

/-- **(h1) at two side coins agreeing off slot `j`**: at side coins `sc`
updated at `j` to `c` or `c'`, the extraction runs give the event `w1SlotReq j = some r` the same
probability (`toOuterMeasure_extLaw_withStep_label_of_blockNone` with
`blockNone_absorbAssign`: the relay's programs at the two coins agree off slot `j`). The default
request is no signing request (`hdef`), and `A₀` is trace preserving. -/
theorem w1SlotLaw_h1_of_eqOn {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt}
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hdef : ∀ s Rg m,
        (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (hA : A₀.TracePreserving)
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (j : Fin Q) (sc₁ sc₂ : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (hsc : ∀ i, i ≠ j → sc₂ i = sc₁ i)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q) :
    ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf
        ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim
                Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω idle
          prf A₀ Psim kq sc₁))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r} =
      ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim
                Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω idle
          prf A₀ Psim kq sc₂))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r} := by
  -- TODO(unbundle-M4): `obtain ⟨Ev, hEv⟩ … := ⟨_, rfl⟩; rw [← hEv]` times out in the rewrite's
  -- motive check; state the goal at a free event instead
  suffices H : ∀ Ev : Set (W1Outcome sp hO A₀ Psim kq), Ev = {o | w1SlotReq sp hO A₀ Psim kq j o =
      some r} →
        ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
            prf
            ξ Q
              (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
              (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
                (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
                (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
                (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω idle) Q).restrictAt sp ω).mapOut Prod.fst))
                    Psim
                    Q kq)).map
            (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
                idle
              prf A₀ Psim kq sc₁))).toOuterMeasure
              Ev =
          ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
              prf ξ Q
              (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
              (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
                (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
                (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
                (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω idle) Q).restrictAt sp ω).mapOut Prod.fst))
                    Psim
                    Q kq)).map
            (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
                idle
              prf A₀ Psim kq sc₂))).toOuterMeasure
              Ev from H _ rfl
  intro Ev hEv
  have hS := sameShape_kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
    (w1DummyR (PS := PSh) (Q := Q))
    (fun pk Rg c m s s' => lockstep_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s s')
    (fun Rg m y y' => (lockstep_hashesProg sp prims O _ _ _ _ Rg.1).mapOutput
      fun _ _ _ => trivial) sc₁ sc₂ ω idle
  have hG := relayOf_kfRelaySide_eq_withProg sp Bf (fun j => (Bf).pk (ξ j))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
    (w1DummyR (PS := PSh) (Q := Q)) sc₁ sc₂ ω idle
  have a₁ := natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    idle prf A₀ Psim kq sc₁
  have a₂ := natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    idle prf A₀ Psim kq sc₂
  -- TODO(unbundle-M4): the two absorbed adversaries have shapes indexed by each relay's numbers;
  -- their outcome types and laws are compared at a free relay (`tuple_absorbAssign_withStep_eq`)
  have a₁' := (tuple_absorbAssign_withStep_eq (Qs := Qs) (Λ := Λ) (E := E)
    (hb := hb) (honest := honest) (chk := chk) (rel := rel) (penc := penc) (dummyS := dummyS)
    (G := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω idle))
    (G' := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω idle))
    sp ξ ω prf A₀ hG hS Psim kq).symm.trans a₂
  have hc₂ := cast_natOutcome (Qs := Qs) (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    idle prf A₀ Psim kq sc₂
  have hc₁ : ∀ o : W1Outcome sp hO A₀ Psim kq, @Eq (W1Outcome sp hO A₀ Psim kq) (cast a₁' o) o :=
    fun o => cast_eq a₁' o
  have hE₂ : Set.preimage (cast a₂) Ev = Ev :=
    Set.ext fun o => iff_of_eq (congrArg (· ∈ Ev) (hc₂ o))
  have hE₁ : Set.preimage (cast a₁') Ev = Ev :=
    Set.ext fun o => iff_of_eq (congrArg (· ∈ Ev) (hc₁ o))
  have hR := toOuterMeasure_simPMF_absorbAssign_withStep (Qs := Qs) (Λ := Λ) (E := E)
    (hb := hb) (honest := honest) (chk := chk) (rel := rel) (penc := penc) (dummyS := dummyS)
    (G := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω idle))
    (G' := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω idle))
    (Ω := W1Outcome sp hO A₀ Psim kq) sp ξ ω prf A₀ hG hS Psim kq a₂ a₁' Ev hE₂ hE₁
  have hN := AdaptiveIAlg.blockNone_absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b) A₀ sp ω
      Prod.fst hA j.isLt hS (by
      intro r' hr
      refine relayOf_kfRelaySide_prog_congr sp Bf _ _ _ _ _ _ _ ω idle r' fun s Rg m hc hs => ?_
      have hne : (⟨r'.1.2, hc⟩ : Fin Q) ≠ j := by
        intro hj'
        have hd : r' = default := by
          by_contra hd
          have ht : AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := (RingSignature.Insider.Req Bf
              PSf adm n)) Q (j : ℕ) r' = true := by
            simp only [AdaptiveIAlg.jTest, decide_eq_true_eq]
            exact ⟨congrArg Fin.val hj', hd⟩
          rw [ht] at hr
          exact Bool.noConfusion hr
        subst hd
        exact hdef s Rg m hs
      exact hsc _ hne)
  have hM := toOuterMeasure_extLaw_withStep_label_of_blockNone (Qs := Qs) (Psim := Psim)
    (prf := prf) (keys := ξ) (rel := rel) (enc := penc) (dummyS := dummyS) hN
    (fun idx _ _ _ _ hx => by rcases idx with _ | m <;> exact hx)
    (fun idx _ _ _ _ hx => by rcases idx with _ | m <;> exact hx)
    (AdaptiveIAlg.mapOut_tracePreserving ((A₀.absorbAssign _ Q).tracePreserving_restrictAt sp ω
      (AdaptiveIAlg.absorbAssign_tracePreserving _ _ _)) Prod.fst)
    (AdaptiveIAlg.tracePreserving_absorbAssign_withStep hS) kq
    Ev r fun o => by rw [hEv]; exact Iff.rfl
  have hc₁₁ := cast_natOutcome (Qs := Qs) (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
      idle prf
      A₀ Psim kq sc₁
  have hE₁₁ : Set.preimage (cast a₁) Ev = Ev :=
    Set.ext fun o => iff_of_eq (congrArg (· ∈ Ev) (hc₁₁ o))
  refine (toOuterMeasure_map_cast_of_preimage _ a₁ Ev hE₁₁).trans ?_
  refine Eq.trans ?_ (toOuterMeasure_map_cast_of_preimage _ a₂ Ev hE₂).symm
  exact Eq.symm (hR.trans hM)

/-- **The swap of the proof queries keeps the statements** of `w1Enc`. -/
theorem w1Enc_stmt_proofSwG [Nonempty RMsg] [Nonempty (FIPSSignature p
    prims)] (pks : Fin n → PubKey p prims)
    (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (G : W1BStmt prims RMsg N → Prop) (swσ : Equiv.Perm (FIPSSignature p prims))
    (q : Rq) :
    ((w1Enc (PS := PSh) (adm := adm) (Q := Q) pks) (.inr (Equiv.sumCongr (w1ProofSwG sp t₀ G swσ)
        (Equiv.refl _) q))).stmt =
      ((w1Enc (PS := PSh) (adm := adm) (Q := Q) pks) (.inr q)).stmt := by
  rcases q with ⟨a, t, σ⟩ | d <;> rfl

/-- **A simulator reading only the program statement does not see the swap** of the tagged
statements. -/
theorem prog_comap_w1MainSwG {SC' : Type} [Fintype SC'] [DecidableEq SC']
    (Psim₀ : NARG.Simulator Xq (XOut kh e) X₀f (Mc.Response b) SC')
    (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (G : W1BStmt prims RMsg N → Prop) (swσ : Equiv.Perm (FIPSSignature p prims))
    (x : W1Stmt prims O Mo βmin tol enc k D bmsg PSh adm n Q × (MURequest (SignOracle.none Bf) n ⊕
        Rq))
    (c : SC') :
    (Psim₀.comap (w1StmtX ∘ Prod.fst)).prog
        (((Equiv.refl _).prodCongr (w1MainSwG sp t₀ G swσ)) x) c =
      (Psim₀.comap (w1StmtX ∘ Prod.fst)).prog x c :=
  rfl

/-- **The gated swap keeps the relation `w1Rel`** at the slot `j`'s request `r` with equal
public parts at the two coins (`w1Rel_iff_of_w1SlotPub_eq` at the gated statements). -/
theorem w1Rel_proofSwG_iff [Inhabited Xq] [Nonempty RMsg] [Nonempty
    (FIPSSignature p prims)]
    (hO : O.ReadsFst sp)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (pks : Fin n → PubKey p prims)
    (sc₁ sc₂ : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q) (j : Fin Q)
    (hj : (r.1.2 : ℕ) = j) (hpub : w1SlotPub sp pks ω r (sc₁ j) = w1SlotPub sp pks ω r (sc₂ j))
    (q : Rq) :
    w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q ((w1Enc (PS := PSh) (adm := adm) (Q := Q)
        pks) (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO pks sc₁
            ω r) (w1SlotSw sp pks ω r (sc₁ j) (sc₂ j))) (Equiv.refl _) q))).stmt
        ((w1Enc (PS := PSh) (adm := adm) (Q := Q) pks) (.inr (Equiv.sumCongr (w1ProofSwG sp
            (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO pks sc₁ ω r) (w1SlotSw sp pks ω r (sc₁ j)
                (sc₂ j))) (Equiv.refl _) q))).wit ↔
      w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q ((w1Enc (PS := PSh) (adm := adm) (Q := Q)
          pks) (.inr q)).stmt ((w1Enc (PS := PSh) (adm := adm) (Q := Q) pks) (.inr q)).wit := by
  rcases q with ⟨a, t, σ⟩ | d
  swap
  · exact Iff.rfl
  by_cases hcond : t = (r.1.1, w1Num Q r.1.2) ∧ (w1SlotGate sp hO pks sc₁ ω r) a
  swap
  · simp [w1ProofSwG, hcond]
  have hcond' := hcond
  obtain ⟨rfl, o, ho, x₀, hx, rfl⟩ := hcond'
  rcases ho with rfl | ⟨s, Rg, m, hc, q, kp, y, hr, hrun, rfl⟩
  · exfalso
    revert hx
    rcases r.1.1 with _ | _ | _ <;> simp [xPω]
  have hrun' := hrun
  erw [run_w1KFOutB] at hrun'
  obtain ⟨q', hq', hqk⟩ := Option.map_eq_some_iff.1 hrun'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqk
  have hcj : (⟨r.1.2, hc.1⟩ : Fin Q) = j := Fin.ext hj
  rw [hcj] at hq'
  have h1 : w1SlotOut sp pks ω r (sc₁ j) = some (q'.1, q'.2) := by
    simp only [w1SlotOut, hr]
    rw [hq']
  obtain ⟨σ', h2⟩ : ∃ σ', w1SlotOut sp pks ω r (sc₂ j) = some (q'.1, σ') := by
    unfold w1SlotPub at hpub
    rw [h1] at hpub
    rcases h : w1SlotOut sp pks ω r (sc₂ j) with _ | ⟨φ', σ''⟩
    · rw [h] at hpub
      simp at hpub
    · rw [h] at hpub
      simp only [Option.map_some, Option.some.injEq] at hpub
      exact ⟨σ'', by rw [← hpub]⟩
  have hsw : (w1SlotSw sp pks ω r (sc₁ j) (sc₂ j)) = Equiv.swap q'.2 σ' := by
    unfold w1SlotSw w1SlotSig
    rw [h1, h2]
    rfl
  have hx0 : x₀ = w1StmtPω prims O Mo βmin tol enc k D bmsg sp
      (ωT sp ω (overT r.2 (lastAssign
        [⟨w1KFKept prims O sp bmsg (ωT sp ω r.2) (pks s) Rg m q'.1, sp.symm (q'.1.2, prfOf sp
            y)⟩])))
      ⟨Rg, m, q'.1.1⟩ := by
    rw [hr] at hx
    simp only [xPω, Option.some.injEq] at hx
    exact hx.symm
  have key := w1Rel_iff_of_w1SlotPub_eq (PS := PSh) (adm := adm) sp pks ω hO hdisj r hr h1 h2
    (prfOf sp y) (.inr (.inl (r.1.1, w1Num Q r.1.2)))
  rw [← hx0] at key
  simp only [Equiv.sumCongr_apply, Sum.map_inl, w1ProofSwG, Equiv.coe_fn_mk, if_pos hcond]
  rw [hsw]
  change w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q (w1Bnd x₀, .inr (.inl (r.1.1, w1Num Q
      r.1.2))) (w1Idx pks (r.1.1, w1Num Q r.1.2).1, Equiv.swap q'.2 σ' σ) ↔
    w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q (w1Bnd x₀, .inr (.inl (r.1.1, w1Num Q
        r.1.2))) (w1Idx pks (r.1.1, w1Num Q r.1.2).1, σ)
  by_cases e1 : σ = q'.2
  · subst e1
    rw [Equiv.swap_apply_left]
    exact key.symm
  by_cases e2 : σ = σ'
  · subst e2
    rw [Equiv.swap_apply_right]
    exact key
  rw [Equiv.swap_apply_of_ne_of_ne e1 e2]

/-- **(h2) at two side coins agreeing off slot `j`**: at side coins agreeing off `j` whose coins
at `j` give the request `r` equal public parts (`hpub`), the extraction runs give the event that
slot `j`'s request is `r` and the readout is `z` the same probability
(`toOuterMeasure_extLaw_withStep_label_and` with `kfSwapBlock_absorbAssign` along the swap
`w1SlotSw` of the two coins' signatures). The swap of the proof queries keeps their statements
and relation (`hstmt`, `hrel`) and the simulator does not see it (`hsim`). -/
theorem w1SlotLaw_h2_of_eqOn {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt}
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hdef : ∀ s Rg m,
        (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (i : MURequest (SignOracle.none Bf) n) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (hA : A₀.TracePreserving)
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (j : Fin Q) (sc₁ sc₂ : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (hsc : ∀ i, i ≠ j → sc₂ i = sc₁ i)
    (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) (z : FIPSSignature p prims)
    (hpub : w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) =
      w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r (sc₂ j))
    (hstmt : ∀ (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) G swσ q,
      (penc (.inr (Equiv.sumCongr (w1ProofSwG sp t₀ G swσ) (Equiv.refl _) q))).stmt =
        (penc (.inr q)).stmt)
    (hrel : (r.1.2 : ℕ) = j → ∀ q,
      rel (penc (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun
          j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂ j)))
              (Equiv.refl _) q))).stmt
          (penc (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun
              j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂
                  j))) (Equiv.refl _) q))).wit ↔
        rel (penc (.inr q)).stmt (penc (.inr q)).wit)
    (hsim : ∀ (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) G swσ x c,
      Psim.prog (((Equiv.refl Stmt).prodCongr (w1MainSwG sp t₀ G swσ)) x) c = Psim.prog x c) :
    ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf
        ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
            (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
          prf A₀ Psim kq sc₁))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r ∧
            w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} =
      ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
            (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
          prf A₀ Psim kq sc₂))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r ∧
            w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} := by
  -- TODO(unbundle-M4): `obtain ⟨Ev, hEv⟩ … := ⟨_, rfl⟩; rw [← hEv]` times out in the rewrite's
  -- motive check; state the goal at a free event instead
  suffices H : ∀ Ev : Set (W1Outcome sp hO A₀ Psim kq), Ev = {o | w1SlotReq sp hO A₀ Psim kq j o =
      some r ∧
            w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} →
        ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
            prf
            ξ Q
              (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
              (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
                (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
                (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
                (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω (Sum.inl i : MURequest (SignOracle.none Bf) n
                    ⊕
                    Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
            (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
                (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
              prf A₀ Psim kq sc₁))).toOuterMeasure
              Ev =
          ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
              prf ξ Q
              (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
              (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
                (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
                (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
                (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n
                    ⊕
                    Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
            (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
                (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
              prf A₀ Psim kq sc₂))).toOuterMeasure
              Ev from H _ rfl
  intro Ev hEv
  by_cases hJr : AdaptiveIAlg.jTest (X := Xq) (Y := Y)
      (Req := RingSignature.Insider.Req Bf PSf adm n) Q (j : ℕ) r = true
  swap
  · have he : Ev = ∅ := by
      rw [hEv]
      ext o
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h _
      exact hJr (firstJ_spec h)
    rw [he]
    simp
  have hj : (r.1.2 : ℕ) = j := by
    simp only [AdaptiveIAlg.jTest, decide_eq_true_eq] at hJr
    exact hJr.1
  have hS := sameShape_kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
    (w1DummyR (PS := PSh) (Q := Q))
    (fun pk Rg c m s s' => lockstep_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s s')
    (fun Rg m y y' => (lockstep_hashesProg sp prims O _ _ _ _ Rg.1).mapOutput
      fun _ _ _ => trivial) sc₁ sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
  have hG := relayOf_kfRelaySide_eq_withProg sp Bf (fun j => (Bf).pk (ξ j))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
    (w1DummyR (PS := PSh) (Q := Q)) sc₁ sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
  have a₁ := natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc₁
  have a₂ := natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc₂
  -- TODO(unbundle-M4): the two absorbed adversaries have shapes indexed by each relay's numbers;
  -- their outcome types and laws are compared at a free relay (`tuple_absorbAssign_withStep_eq`)
  have a₁' := (tuple_absorbAssign_withStep_eq (Qs := Qs) (Λ := Λ) (E := E)
    (hb := hb) (honest := honest) (chk := chk) (rel := rel) (penc := penc) (dummyS := dummyS)
    (G := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)))
    (G' := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)))
    sp ξ ω prf A₀ hG hS Psim kq).symm.trans a₂
  have hc₂ := cast_natOutcome (Qs := Qs) (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc₂
  have hc₁ : ∀ o : W1Outcome sp hO A₀ Psim kq, @Eq (W1Outcome sp hO A₀ Psim kq) (cast a₁' o) o :=
    fun o => cast_eq a₁' o
  have hE₂ : Set.preimage (cast a₂) Ev = Ev :=
    Set.ext fun o => iff_of_eq (congrArg (· ∈ Ev) (hc₂ o))
  have hE₁ : Set.preimage (cast a₁') Ev = Ev :=
    Set.ext fun o => iff_of_eq (congrArg (· ∈ Ev) (hc₁ o))
  have hR := toOuterMeasure_simPMF_absorbAssign_withStep (Qs := Qs) (Λ := Λ) (E := E)
    (hb := hb) (honest := honest) (chk := chk) (rel := rel) (penc := penc) (dummyS := dummyS)
    (G := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)))
    (G' := (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)))
    (Ω := W1Outcome sp hO A₀ Psim kq) sp ξ ω prf A₀ hG hS Psim kq a₂ a₁' Ev hE₂ hE₁
  have hφ := coinSwapAt_w1Slot (T := T) (Mo := Mo) (Λ := Λ) (E := E) (hb := hb)
    (honest := honest) (chk := chk) (adm := adm) sp hO (fun j => (Bf).pk (ξ j)) sc₁ sc₂ ω r j hj
        hpub
  have hP := progSwap_kfRelaySide_side sp Bf (fun j => (Bf).pk (ξ j))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
    (w1DummyR (PS := PSh) (Q := Q))
    (fun pk Rg c m s s' => lockstep_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s s')
    (fun Rg m y y' => (lockstep_hashesProg sp prims O _ _ _ _ Rg.1).mapOutput
      fun _ _ _ => trivial)
    (fun pk Rg c m s => countsLE_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s)
    (fun x => ((countsLE_hashesProg sp prims O _ _ x.ring.1).mapOutput).mono
      (Nat.mul_le_mul_left 2 x.ring.2))
    sc₁ sc₂ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
    (AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := RingSignature.Insider.Req Bf PSf adm n) Q j) r
    (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂ j)) (w1MainSwG sp (r.1.1, w1Num Q
        r.1.2) (w1SlotGate sp hO (fun j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk
            (ξ j)) ω r (sc₁ j) (sc₂ j)))
    (fun r' hr s Rg m hc hs => by
      have hne : (⟨r'.1.2, hc⟩ : Fin Q) ≠ j := by
        intro hj'
        have hd : r' = default := by
          by_contra hd
          have ht : AdaptiveIAlg.jTest (X := Xq) (Y := Y)
              (Req := (RingSignature.Insider.Req Bf PSf adm n)) Q (j : ℕ) r' = true := by
            simp only [AdaptiveIAlg.jTest, decide_eq_true_eq]
            exact ⟨congrArg Fin.val hj', hd⟩
          rw [ht] at hr
          exact Bool.noConfusion hr
        subst hd
        exact hdef s Rg m hs
      exact hsc _ hne) hφ
    (fun o ho => by
      have hG : ∀ x₀, xPω sp Bf (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) ω r.2 r.1.1 o =
          some x₀ → (w1SlotGate sp hO (fun j => (Bf).pk (ξ j)) sc₁ ω r) (w1Bnd x₀) := fun x₀ hx =>
              ⟨o, ho, x₀, hx, rfl⟩
      rcases ho with rfl | ⟨s, Rg, m, hc, q, kp, y, hr, hrun, rfl⟩
      · change w1MainSwG sp _ _ _ (reqOf _ _ _ _ r.1.1 none _) = reqOf _ _ _ _ r.1.1 none _
        rcases r.1.1 with _ | _ | _ <;> rfl
      · have hx := hG _ (by rw [hr]; rfl)
        revert hx
        generalize (w1SlotGate sp hO (fun j => (Bf).pk (ξ j)) sc₁ ω r) = G
        intro hx
        rw [hr]
        simp only [xPω, reqOf, mapSig, w1ToR, w1MainSwG, w1ProofSwG, Option.map_some,
          Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, Equiv.coe_fn_mk, Prod.map, id]
        simp [hx])
    rfl
  have hoffT := offTagFixed_kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
    (w1DummyR (PS := PSh) (Q := Q)) sc₁ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
    (AdaptiveIAlg.jTest (X := Xq) (Y := Y) (Req := RingSignature.Insider.Req Bf PSf adm n) Q j)
    (w1MainSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun j => (Bf).pk (ξ j)) sc₁ ω r)
        (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂ j)))
    (fun r' hr o x₀ => by
      by_cases ht : (r'.1.1, w1Num Q r'.1.2) = (r.1.1, w1Num Q r.1.2)
      · have h1 : r'.1.1 = r.1.1 := (Prod.mk.inj ht).1
        have h2 : (r'.1.2 : ℕ) = r.1.2 := w1Num_injOn (Nat.le_of_lt_succ r'.1.2.2)
          (Nat.le_of_lt_succ r.1.2.2) (Prod.mk.inj ht).2
        have hd : r' = default := by
          by_contra hd
          have htt : AdaptiveIAlg.jTest (X := Xq) (Y := Y)
              (Req := (RingSignature.Insider.Req Bf PSf adm n)) Q (j : ℕ) r' = true := by
            simp only [AdaptiveIAlg.jTest, decide_eq_true_eq]
            exact ⟨h2.trans hj, hd⟩
          rw [htt] at hr
          exact Bool.noConfusion hr
        have hns : ∀ s Rg m, r.1.1 ≠ .sign s Rg m := fun s Rg m h =>
          hdef s Rg m (by rw [← h, ← h1, hd]; rfl)
        have hsw1 := w1SlotSw_of_not_sign (Λ := Λ) (E := E) (hb := hb) (honest := honest)
          (chk := chk) sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂ j) hns
        erw [hsw1]
        exact w1MainSwG_one (Λ := Λ) (E := E) (hb := hb) (honest := honest) (chk := chk) sp _ _ _
      · exact w1MainSwG_reqOf_of_ne sp _ _ _ _ _ ht o x₀) rfl
  have h := kfSwapBlock_absorbAssign (rel := rel) (enc := penc) (A := A₀) (sp := sp) (H₁ := ω)
    (f := Prod.fst) (j := j) (r₀ := r) prf Psim hA j.isLt hS hP rfl
    rfl (fun _ => ⟨rfl, rfl⟩) hoffT (hstmt _ _ _) (hrel hj) rfl (hsim _ _ _)
  have hM := toOuterMeasure_extLaw_withStep_label_and (Qs := Qs) (Psim := Psim)
    (prf := prf) (keys := ξ) (rel := rel) (enc := penc) (dummyS := dummyS) h kq
    (fun o => w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z)
    (readsClaimDB_w1CanonSig (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω (Sum.inl i :
        MURequest (SignOracle.none Bf) n ⊕ Rq) prf
      A₀ Psim kq sc₁ Ext z)
    Ev fun o => by rw [hEv]; exact Iff.rfl
  have hc₁₁ := cast_natOutcome (Qs := Qs) (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
        (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
      prf A₀ Psim kq sc₁
  have hE₁₁ : Set.preimage (cast a₁) Ev = Ev :=
    Set.ext fun o => iff_of_eq (congrArg (· ∈ Ev) (hc₁₁ o))
  refine (toOuterMeasure_map_cast_of_preimage _ a₁ Ev hE₁₁).trans ?_
  refine Eq.trans ?_ (toOuterMeasure_map_cast_of_preimage _ a₂ Ev hE₂).symm
  exact Eq.symm (hR.trans hM)

/-- **The guess event at the side coins `sc`**: the readout is the signature `z` of a logged
signing entry among the first `Q` main requests that a signed request of the relay asks
(`KFSignedAsk`), the guess term of `tsum_simProb_w1Goal_le` read at the outcome. -/
def w1SlotGuess
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) (sc
          : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (o : W1Outcome sp hO A₀ Psim kq) : Prop :=
  ∃ z, w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z ∧
    ∃ e' ∈ (Quantum.requests o.1.out.adv.workspace.1.1.logs).take Q,
      (w1SignEntry e').isSome = true ∧ w1EntrySig e' = some z ∧
      KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e'

/-- **(hG) The guess event is a slot's signature guess**: its probability is at most that of the
readout being the signature `w1SlotSig` of some slot's request at its coin
(`simProb_seAlgKF_slotAsks` with `w1SlotAsks_hp` and `w1EntrySig_of_canAsk`). -/
theorem w1SlotLaw_hG {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt}
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit}
    (hdef : ∀ s Rg m, (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) (i
          : MURequest (SignOracle.none Bf) n) (prf : Frg → Option Mc.NIProof)
    (hA : A₀.TracePreserving) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) :
    ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
          (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc))).toOuterMeasure
              {o | w1SlotGuess sp hO ξ ω A₀ Psim kq Ext sc o} ≤
      ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
          (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc))).toOuterMeasure
              {o | ∃ j r z, w1SlotReq sp hO A₀ Psim kq j o = some r ∧
        w1SlotSig sp (fun j => (Bf).pk (ξ j)) ω r (sc j) = some z ∧
        w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} := by
  have hc := cast_natOutcome (Qs := Qs) (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
    (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc
  have h1 : Set.preimage (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc)
      (dummyS := dummyS) sp hO ξ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim
          kq sc))
      {o | w1SlotGuess sp hO ξ ω A₀ Psim kq Ext sc o} =
      {x | (fun c Db => ∃ z, w1CanonSigR sp hO A₀ Psim Ext (fun j => (Bf).pk (ξ j)) c Db = some z ∧
        ∃ e' ∈ (Quantum.requests c.adv.workspace.1.1.logs).take Q,
          (w1SignEntry e').isSome = true ∧ w1EntrySig e' = some z ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e')
        x.1.out x.2} :=
    -- TODO(unbundle-M4): `rw [hc x]` times out in its motive; transport the membership instead
    Set.ext fun x => (iff_of_eq (congrArg (· ∈ {o | w1SlotGuess sp hO ξ ω A₀ Psim kq Ext sc o})
      (hc x))).trans Iff.rfl
  have h2 : Set.preimage (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc)
      (dummyS := dummyS) sp hO ξ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim
          kq sc))
      {o | ∃ j r z, w1SlotReq sp hO A₀ Psim kq j o = some r ∧
        w1SlotSig sp (fun j => (Bf).pk (ξ j)) ω r (sc j) = some z ∧
        w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} =
      {x | (fun c Db => ∃ j : Fin Q, ∃ r z, slotRequest (rel := rel) (enc := penc) (dummyS :=
          dummyS) prf ξ Q
          A₀ (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) sp ω Psim j c = some r ∧
          w1SlotSig sp (fun j => (Bf).pk (ξ j)) ω r (sc j) = some z ∧
          w1CanonSigR sp hO A₀ Psim Ext (fun j => (Bf).pk (ξ j)) c Db = some z) x.1.out x.2} :=
              Set.ext fun x => (iff_of_eq (congrArg (· ∈ {o | ∃ j r z,
                w1SlotReq sp hO A₀ Psim kq j o = some r ∧
                w1SlotSig sp (fun j => (Bf).pk (ξ j)) ω r (sc j) = some z ∧
                w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z})
                (hc x))).trans Iff.rfl
  -- TODO(unbundle-M4): `rw [PMF.toOuterMeasure_map_apply, …, ← simLaw_eq_toOuterMeasure_simPMF]`
  -- times out on the goal; read both sides through the named preimages instead
  refine (toOuterMeasure_map_cast_of_preimage _ _ _ h1).trans_le
    (le_of_le_of_eq ?_ (toOuterMeasure_map_cast_of_preimage _ _ _ h2).symm)
  refine (simLaw_eq_toOuterMeasure_simPMF _ _ _).symm.trans_le
    (le_of_le_of_eq ?_ (simLaw_eq_toOuterMeasure_simPMF _ _ _))
  refine (simProb_seAlgKF_slotAsks (Qs := Qs) (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
    A₀ hA (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)) sp
          ω Psim kq (fun c Db => ∃ z, w1CanonSigR sp hO A₀ Psim Ext (fun j => (Bf).pk (ξ j)) c Db
              = some z ∧
        ∃ e' ∈ (Quantum.requests c.adv.workspace.1.1.logs).take Q,
          (w1SignEntry e').isSome = true ∧ w1EntrySig e' = some z ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e')
    (fun r => (w1SignEntry r).isSome) rfl rfl
    (w1SlotAsks_hp sp hdef hO ξ sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq))).trans
        (simProb_mono (R' := (fun c Db => ∃ j : Fin Q, ∃ r z, slotRequest (rel := rel) (enc :=
            penc) (dummyS := dummyS) prf ξ Q
          A₀ (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) sp ω Psim j c = some r ∧
          w1SlotSig sp (fun j => (Bf).pk (ξ j)) ω r (sc j) = some z ∧
          w1CanonSigR sp hO A₀ Psim Ext (fun j => (Bf).pk (ξ j)) c Db = some z)) _ _ fun c Db h =>
              ?_)
  obtain ⟨⟨z, hz, e', he', hs, hsig, -⟩, hall⟩ := h
  obtain ⟨j, r, hr, hj, hca⟩ := hall e' (List.mem_of_mem_take he') hs
  exact ⟨j, r, z, hr, (w1EntrySig_of_canAsk sp (fun j => (Bf).pk (ξ j)) ω hO (Sum.inl i :
      MURequest (SignOracle.none Bf) n ⊕ Rq) r j hj hca hs).symm.trans hsig,
    hz⟩

/-- **(h1) The law of slot `j`'s request does not depend on its side coin**: at side coins `sc`
updated at `j` to `c` or `c'`, the extraction runs give the event `w1SlotReq j = some r` the same
probability (`toOuterMeasure_extLaw_withStep_label_of_blockNone` with
`blockNone_absorbAssign`: the relay's programs at the two coins agree off slot `j`). The default
request is no signing request (`hdef`), and `A₀` is trace preserving. -/
theorem w1SlotLaw_h1 {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt}
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hdef : ∀ s Rg m,
        (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none Bf) n ⊕ Rq) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (hA : A₀.TracePreserving)
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ) :
    ∀ (j : Fin Q) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
      (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q)
      (c c' : KFCoins (p := p) (T := T) k D Y₁), ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel
          := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) (Function.update sc j c) ω idle) Q).restrictAt sp
                ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω idle
          prf A₀ Psim kq (Function.update sc j c)))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r} =
      ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) (Function.update sc j c') ω idle) Q).restrictAt sp
                ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω idle
          prf A₀ Psim kq (Function.update sc j c')))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r} :=
  fun j sc r c c' => w1SlotLaw_h1_of_eqOn (Qs := Qs) sp hdef hO ξ ω idle prf A₀ hA Psim kq j
    (Function.update sc j c) (Function.update sc j c')
    (fun i hi => by rw [Function.update_of_ne hi, Function.update_of_ne hi]) r


/-- **(h2) The joint law of slot `j`'s request and the readout depends on its side coin only
through the public part**: at side coins `sc` updated at `j` to coins `c`, `c'` with equal public
parts at the request `r` (`w1SlotPub`), the extraction runs give the event that slot `j`'s request
is `r` and the readout `w1CanonSig` is `z` the same probability (`w1SlotLaw_h2_of_eqOn`). -/
theorem w1SlotLaw_h2 {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt}
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hdef : ∀ s Rg m,
        (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (i : MURequest (SignOracle.none Bf) n) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (hA : A₀.TracePreserving)
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (hstmt : ∀ (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) G swσ q,
      (penc (.inr (Equiv.sumCongr (w1ProofSwG sp t₀ G swσ) (Equiv.refl _) q))).stmt =
        (penc (.inr q)).stmt)
    (hrel : ∀ (j : Fin Q) (sc₁ sc₂ : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
      (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q),
      (r.1.2 : ℕ) = j →
      w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) =
        w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r (sc₂ j) → ∀ q,
      rel (penc (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun
          j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂ j)))
              (Equiv.refl _) q))).stmt
          (penc (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun
              j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂
                  j))) (Equiv.refl _) q))).wit ↔
        rel (penc (.inr q)).stmt (penc (.inr q)).wit)
    (hsim : ∀ (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) G swσ x c,
      Psim.prog (((Equiv.refl Stmt).prodCongr (w1MainSwG sp t₀ G swσ)) x) c = Psim.prog x c) :
    ∀ (j : Fin Q) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
      (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q)
      (z : FIPSSignature p prims) (c c' : KFCoins (p := p) (T := T) k D Y₁),
      w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r c = w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r c' →
      ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) (Function.update sc j c) ω (Sum.inl i : MURequest
                (SignOracle.none Bf) n ⊕ Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
            (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
          prf A₀ Psim kq (Function.update sc j c)))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r ∧
            w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} =
      ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) (Function.update sc j c') ω (Sum.inl i : MURequest
                (SignOracle.none Bf) n ⊕ Rq)) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
            (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
          prf A₀ Psim kq (Function.update sc j c')))).toOuterMeasure
          {o | w1SlotReq sp hO A₀ Psim kq j o = some r ∧
            w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk (ξ j)) o = some z} :=
  fun j sc r z c c' hp => w1SlotLaw_h2_of_eqOn (Qs := Qs) sp hdef hO ξ ω i prf A₀ hA Psim kq j
    (Function.update sc j c) (Function.update sc j c')
    (fun i hi => by rw [Function.update_of_ne hi, Function.update_of_ne hi]) r Ext z
    (by simpa only [Function.update_self] using hp) hstmt
    (fun hj => hrel j _ _ r hj (by simpa only [Function.update_self] using hp)) hsim


/-- **The slot laws bound the guess of case S** (`tsum_w1Guess_le` at the laws `L sc` of the
extraction runs, the slot requests `w1SlotReq`, the readout `w1CanonSig`, `w1SlotLaw_h1`,
`w1SlotLaw_h2` and `w1SlotLaw_hG`): averaged over uniform side coins, the guess event
`w1SlotGuess` has probability at most `Q · k · T · |BucketVec| / |MaskBox|`. -/
theorem slotLaws_kfExtractionLaw {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt}
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {penc : MURequest (SignOracle.none Bf) n ⊕ Rq → ProofQuery Stmt Wit} (hdef : ∀ s Rg m,
        (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (i : MURequest (SignOracle.none Bf) n) (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp
        Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (hA : A₀.TracePreserving)
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none Bf) n ⊕ Rq))
      (Mc.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (hstmt : ∀ (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) G swσ q,
      (penc (.inr (Equiv.sumCongr (w1ProofSwG sp t₀ G swσ) (Equiv.refl _) q))).stmt =
        (penc (.inr q)).stmt)
    (hrel : ∀ (j : Fin Q) (sc₁ sc₂ : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
      (r : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q),
      (r.1.2 : ℕ) = j →
      w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) =
        w1SlotPub sp (fun j => (Bf).pk (ξ j)) ω r (sc₂ j) → ∀ q,
      rel (penc (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun
          j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂ j)))
              (Equiv.refl _) q))).stmt
          (penc (.inr (Equiv.sumCongr (w1ProofSwG sp (r.1.1, w1Num Q r.1.2) (w1SlotGate sp hO (fun
              j => (Bf).pk (ξ j)) sc₁ ω r) (w1SlotSw sp (fun j => (Bf).pk (ξ j)) ω r (sc₁ j) (sc₂
                  j))) (Equiv.refl _) q))).wit ↔
        rel (penc (.inr q)).stmt (penc (.inr q)).wit)
    (hsim : ∀ (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) G swσ x c,
      Psim.prog (((Equiv.refl Stmt).prodCongr (w1MainSwG sp t₀ G swσ)) x) c = Psim.prog x c) :
    ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
        ((simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) Q).restrictAt sp ω).mapOut Prod.fst))
          Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
          (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc))).toOuterMeasure
              {o | w1SlotGuess sp hO ξ ω A₀ Psim kq Ext sc o} ≤
      Q * (k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p)) :=
  tsum_w1Guess_le (PS := PSh) sp (fun j => (Bf).pk (ξ j)) ω (fun sc => ((simPMF (outEquiv kh e)
      (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
          prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
          (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
            (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
            (w1DummyR (PS := PSh) (Q := Q)) sc ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕
                Rq)) Q).restrictAt sp ω).mapOut Prod.fst))
          Psim Q kq)).map
        (cast (natOutcome_eq_w1Outcome (rel := rel) (penc := penc) (dummyS := dummyS) sp hO ξ ω
          (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀ Psim kq sc))))
    (fun j o => w1SlotReq sp hO A₀ Psim kq j o) (w1CanonSig sp hO A₀ Psim kq Ext (fun j => (Bf).pk
        (ξ j)))
    (w1SlotLaw_h1 (Qs := Qs) sp hdef hO ξ ω (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)
        prf A₀ hA Psim kq)
    (w1SlotLaw_h2 (Qs := Qs) sp hdef hO ξ ω i prf A₀ hA Psim kq Ext hstmt hrel hsim)
    (fun sc o => w1SlotGuess sp hO ξ ω A₀ Psim kq Ext sc o)
    (w1SlotLaw_hG (Qs := Qs) sp hdef hO ξ ω A₀ Psim kq Ext i prf hA)

end SlotLaws

end GordieHowe.Ring.MLDSAW1
