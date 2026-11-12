-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeForger
public import GordieHowe.Applications.Ring.KeyFreeCanon
public import GordieHowe.Applications.Ring.KeyFreeSideSteps

@[expose] public section

/-!
# The canonical witness's goal in key-free extraction runs with side reads, as MU-EUF-NMA^corr

`kfExtSide_le_muEufNmaProb` at a family of relayed adversaries `X pks p` with a table in their
output, read through `Prod.fst`, and the canonical witness's goal (`forgerCanonKF`) as the event.
The forger reads the canonical witness through `rd`; it verifies when the goal holds (`hver`) and
its key is an uncorrupted user's (`hhon`). The run is written as the restriction at `ω` of the
adversary with its Kraus maps at `ω`, the form in which an absorbed relay at `ω` is the relay at
zero with the Kraus maps at `ω` (`absorbAssign_kfRelaySide_eq_withStep`).

- `kfCanonReadout`: the forger's readout of the canonical witness.
- `kfCanonSide_le_muEufNmaProb`.
-/

namespace GordieHowe

open Quantum Signature QROM RingSignature RingSignature.OracleSplit
open scoped ENNReal

namespace RingSignature.KeyFree

open GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

variable {k kN kS L e N n : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.PK]
  [DecidableEq T.PK]
  [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.KeyCoins]
  [DecidableEq T.KeyCoins]
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N T RMsg} [NeZero n]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} [DecidableEq X₀] {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : X₀ → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries Vr x)
  {Stmt Wit R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R]
  (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (enc : (Fin n → B.PK) → MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)
  (dummyS : Stmt)
  [Inhabited M.NIProof] {SC' : Type} [Fintype SC'] [DecidableEq SC']

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n


omit [Nonempty Y] [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq X₀]
  [Inhabited M.NIProof] in
/-- **The request bound of the bridge of a restricted adversary of width one without post
batches**: `slots · (q + 1) + kq`. -/
theorem bT_mapOut_restrictAt_eq {Rq Rs O O' Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype Rq]
    [DecidableEq Rq] [Fintype Rs] [DecidableEq Rs] [Fintype Req₁] [DecidableEq Req₁]
    [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] [Fintype Req₂] [DecidableEq Req₂]
    [Fintype Resp₂] [DecidableEq Resp₂]
    {shX : AlgShape Xq Y Rq Rs} (X : AdaptiveIAlg shX O) (f : O → O')
    (C₁ : Challenger Xq (XOut k e) Req₁ Resp₁) (F' : TwoRelay Rq Rs Req₁ Resp₁ Req₂ Resp₂)
    (kq' : ℕ)
    (hw : X.width = 1) (hp : X.post = 0) :
    bT ((X.mapOut f).restrictAt sp 0) C₁ F' kq' = X.slots * (C₁.q + 1) + kq' := by
  rw [bT_eq]
  change X.slots * (C₁.q + X.width) + X.width * X.post + kq' = _
  rw [hw, hp, Nat.mul_zero, Nat.add_zero]

/-- **The forger's readout of the canonical witness**: `rd` at the output of the extraction run's
registers and the canonical witness (`kfCanon`) at the test `ok pks`, at those registers and the
measured database. -/
def kfCanonReadout {WitK Wt : Type} {shA₁ : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} {A₁ : AdaptiveIAlg shA₁ (Frg × X₀)} {C₁ : Challenger Xq (XOut k e) (Stmt × (MUR ⊕ R))
      (M.Response b)} {t₀ : ℕ}
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok : Frg × X₀ → List (MUR ⊕ R) → Wt → Prop) [∀ f rs, DecidablePred (ok f rs)]
    (rd : Frg × X₀ → Option Wt → B.PK × B.BMsg × B.BSig)
    (Q : ℕ) (x : BaseGame.Tuple Xq (Out k e) (ExtReg A₁ C₁ MUR (MUResponse B.core)) t₀ ×
      DB Xq (Out k e)) : B.PK × B.BMsg × B.BSig :=
  rd (extForgery x.1.out) (kfCanon M Ext wit (ok (extForgery x.1.out)
    ((Quantum.requests (extLogs x.1.out)).take Q)) (extForgery x.1.out).2 x.2)

/-- **The forger of `kfCanonSide_le_muEufNmaProb`**: `kfForgerAdds` at the relayed adversaries
with their output read through `Prod.fst`, the readout `kfCanonReadout` at `rd`, the side reads
`kfSidePb` of `hside`, and the query budget `t'`.

Running time: that of `kfForgerAdds` (its paragraph) at these arguments, with one evaluation of
`rd` and of the list extractor (`kfCanon`) for the readout. This running time is argued here, not
proved in Lean. -/
noncomputable abbrev kfCanonSideForger {Tb WitK Wt : Type}
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shX : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)}
    (X : ∀ pks (p : Aux pks), AdaptiveIAlg (shX pks p) ((Frg × X₀) × Tb))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (X pks p).slots (X pks p).post →
      KrausMap (X pks p).R (DReg (X pks p).W (X pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (X pks p).W (X pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (hside : ∀ pks p, (X pks p).SideSteps (stω pks p))
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok : (Fin n → B.PK) → Frg × X₀ → List (MUR ⊕ R) → Wt → Prop)
    [∀ pks f rs, DecidablePred (ok pks f rs)]
    (rd : Frg × X₀ → Option Wt → B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, bT (((X pks p).mapOut Prod.fst).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 +
        ∑ j, ((hside pks p).mapOut Prod.fst).S.nb j ≤ t') :=
  kfForgerAdds sp Qs rel enc dummyS Aux aux
    (fun pks p => (X pks p).mapOut Prod.fst) prf Psim Q kq
    (fun pks _ => kfCanonReadout Ext wit (ok pks) rd Q)
    (kfSidePb sp Qs rel enc dummyS Aux (fun pks p => (X pks p).mapOut Prod.fst) prf Psim Q kq
      stω fun pks p => (hside pks p).mapOut Prod.fst) t' fun pks p =>
      (slotQ_kfSidePb_le sp Qs rel enc dummyS Aux (fun pks p => (X pks p).mapOut Prod.fst) prf
        Psim Q kq stω (fun pks p => (hside pks p).mapOut Prod.fst) pks p).trans (ht pks p)

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The canonical witness's goal in the run of a restriction with other Kraus maps** is that of
the restriction at `0` with the Kraus maps of the restriction at `ω`
(`AdaptiveIAlg.withStep_restrictAt_eq`), stated at a free adversary. -/
theorem simProb_withStep_restrictAt_eq {WitK Wt : Type}
    {shA : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (st : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width Xq Y (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg A.W A.width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok G : Frg × X₀ → List (MUR ⊕ R) → Wt → Prop) [∀ f rs, DecidablePred (ok f rs)] (ω : Xq → Y₁) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS) prf keys Q ((A.withStep st).restrictAt sp ω)) Psim Q kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys
        Q ((A.withStep st).restrictAt sp ω) Psim Ext wit ok G) =
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS) prf keys Q
          ((A.restrictAt sp 0).withStep ((A.withStep st).restrictAt sp ω).step)) Psim Q kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys
        Q ((A.restrictAt sp 0).withStep ((A.withStep st).restrictAt sp ω).step) Psim Ext wit ok G) := by
  -- TODO(unbundle-M4): `withStep`/`restrictAt` rebuild the shape as literals, so a plain `rfl`
  -- compares the two sides' synthesized `DecidableEq`/`Fintype` instances by evaluation; unfolding
  -- both first makes the check structural.
  unfold AdaptiveIAlg.restrictAt AdaptiveIAlg.withStep
  rfl

variable [Nonempty T.KeyCoins]

/-- **The canonical witness's goal in the key-free extraction runs with side reads as
MU-EUF-NMA^corr** (`kfExtSide_le_muEufNmaProb` at the event `forgerCanonKF`): for relayed
adversaries `X pks p` with a table in their output and Kraus maps `stω pks p ω` at the base
component `ω`, read after side reads (`hside`), averaged over the users' key coins, the auxiliary
input and a uniform `ω`, the probability that the canonical witness at the test `ok` satisfies the
goal `G ω` in the extraction run of the restriction at `ω` of `X pks p`, its output read through
`Prod.fst` and its Kraus maps those at `ω`, is at most the success probability of `kfForgerAdds`
with the readout `kfCanonReadout` at `rd`, in MU-EUF-NMA^corr with `Q'` requests. The readout of a
canonical witness meeting the goal verifies at every oracle with base component `ω` (`hver`) and
has an uncorrupted user's key (`hhon`). -/
theorem kfCanonSide_le_muEufNmaProb {Tb WitK Wt : Type}
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shX : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)}
    (X : ∀ pks (p : Aux pks), AdaptiveIAlg (shX pks p) ((Frg × X₀) × Tb))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (hTP : ∀ pks p, (X pks p).TracePreserving)
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (X pks p).slots (X pks p).post →
      KrausMap (X pks p).R (DReg (X pks p).W (X pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (X pks p).W (X pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (hside : ∀ pks p, (X pks p).SideSteps (stω pks p))
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok : (Fin n → B.PK) → Frg × X₀ → List (MUR ⊕ R) → Wt → Prop)
    [∀ pks f rs, DecidablePred (ok pks f rs)]
    (G : (Xq → Y₁) → Frg × X₀ → List (MUR ⊕ R) → Wt → Prop)
    (rd : Frg × X₀ → Option Wt → B.PK × B.BMsg × B.BSig)
    (hver : ∀ pks (ω : Xq → Y₁) (h : Xq → XOut k e) f rs w, ok pks f rs w → G ω f rs w →
      B.bverify (join sp ω h) (rd f (some w)).1 (rd f (some w)).2.1 (rd f (some w)).2.2 = true)
    (hhon : ∀ pks f rs w, ok pks f rs w →
      ∃ i, pks i = (rd f (some w)).1 ∧ (.inl (.corrupt i) : MUR ⊕ R) ∉ rs)
    (t' : ℕ)
    (ht : ∀ pks p, bT (((X pks p).mapOut Prod.fst).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 +
        ∑ j, ((hside pks p).mapOut Prod.fst).S.nb j ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT (((X pks p).mapOut Prod.fst).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (kq + Q * Psim.q) + 1 ≤ Q') :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel)
            (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys Q
              ((((X _ p).mapOut Prod.fst).withStep (stω _ p ω)).restrictAt sp ω)) Psim Q kq)
            (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS)
              prf keys Q ((((X _ p).mapOut Prod.fst).withStep (stω _ p ω)).restrictAt sp ω) Psim
              Ext wit (ok fun i => B.pk (keys i)) (G ω)) ≤
      muEufNmaProb (kfCanonSideForger sp Qs rel enc dummyS Aux aux X prf Psim Q kq stω hside Ext
        wit ok rd t' ht) Q' := by
  refine le_of_eq_of_le ?_ (kfExtSide_le_muEufNmaProb sp Qs rel enc dummyS Aux aux
    (fun pks p => (X pks p).mapOut Prod.fst) prf Psim Q kq
    (fun pks p => AdaptiveIAlg.mapOut_tracePreserving (hTP pks p) Prod.fst) stω
    (fun pks p => (hside pks p).mapOut Prod.fst)
    (fun pks _ => kfCanonReadout Ext wit (ok pks) rd Q) t' ht hQ
    (fun keys p ω => forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
      (dummyS := dummyS) prf keys Q _ Psim Ext wit (ok fun i => B.pk (keys i)) (G ω))
    (fun _ _ _ _ _ => Iff.rfl) ?_ ?_)
  · -- TODO(unbundle-M4): the two sides carry different (defeq) inline shape literals of
    -- `restrictAt`/`withStep`; `congr 1` times out, so go through the lemma at a free adversary.
    refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg _
      (tsum_congr fun ω => congrArg _ ?_))
    exact simProb_withStep_restrictAt_eq (A := (X _ p).mapOut Prod.fst) (st := stω _ p ω) (prf := prf)
      (keys := keys) (Q := Q) (Psim := Psim) (kq := kq) (Ext := Ext) (wit := wit) (ω := ω) ..
  · intro keys p ω h c v _ hW
    obtain ⟨w, hw, hg⟩ := hW
    have hok := (kfCanon_spec M Ext wit _ _ _ hw).2
    exact (congrArg (fun o => B.bverify (join sp ω h) (rd _ o).1 (rd _ o).2.1 (rd _ o).2.2)
      hw).trans
      (hver _ ω h _ _ w hok hg)
  · intro keys p ω c v _ hW
    obtain ⟨w, hw, -⟩ := hW
    have hok := (kfCanon_spec M Ext wit _ _ _ hw).2
    -- TODO(unbundle-M4): `obtain ⟨i, hi, hc⟩ := hhon …` costs about 2 s of elaboration here
    -- (inside `rcases`); `Exists.imp` keeps the declaration under the heartbeat budget.
    exact (hhon _ _ _ w hok).imp fun _ h =>
      ⟨h.1.trans (congrArg (fun o => (rd _ o).1) hw).symm, h.2⟩

/-- **Two averages commute**, each factor kept with its sum. -/
theorem _root_.GordieHowe.ENNReal.tsum_mul_tsum_comm {α β : Type} (u : α → ℝ≥0∞)
    (v : β → ℝ≥0∞) (F : α → β → ℝ≥0∞) :
    ∑' x, u x * ∑' y, v y * F x y = ∑' y, v y * ∑' x, u x * F x y := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => tsum_congr fun x => ?_
  ring

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [Nonempty T.KeyCoins] in
/-- **The canonical witness's goal in the run of a relayed adversary is read past the order of
restricting and dropping the table.** -/
theorem simProb_restrictAt_mapOut_comm {Tb WitK Wt : Type}
    {shX : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (X : AdaptiveIAlg shX ((Frg × X₀) × Tb))
    (st : StepIdx X.slots X.post → KrausMap X.R (DReg X.W X.width Xq Y (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)) (DReg X.W X.width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok G : Frg × X₀ → List (MUR ⊕ R) → Wt → Prop) [∀ f rs, DecidablePred (ok f rs)] (ω : Xq → Y₁) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS) prf keys Q (((X.withStep st).restrictAt sp ω).mapOut Prod.fst)) Psim Q
            kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys
          Q
        (((X.withStep st).restrictAt sp ω).mapOut Prod.fst) Psim Ext wit ok G) =
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS) prf keys Q (((X.mapOut Prod.fst).withStep st).restrictAt sp ω)) Psim Q
            kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys
          Q
        (((X.mapOut Prod.fst).withStep st).restrictAt sp ω) Psim Ext wit ok G) :=
  congrArg (fun A => simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel)
      (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys Q A) Psim Q kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys
          Q
        A Psim Ext wit ok G))
    -- TODO(unbundle-M4): `restrictAt`/`withStep` return inline shape literals, so a `congrArg`
    -- through `restrictAt` cannot be elaborated; both rewrites are `rfl`.
    ((mapOut_restrictAt_eq sp (X.withStep st) Prod.fst ω).symm.trans rfl)

/-- **The forger's request bound for absorbed relays**: `q + 1` per slot of the relayed adversary,
with at most `(S + P) · max w 3` slots, the `kq` extraction queries, and one. -/
def kfAbsorbSideRequests (S P w q kq : ℕ) : ℕ :=
  (S + P) * max w 3 * (q + 1) + kq + 1

/-- **The forger's query budget for absorbed relays**: its requests and `qS` side reads before each
of the at most `(S + P) · max w 3 + 1` Kraus maps of the relayed adversary. -/
def kfAbsorbSideBudget (S P w q kq qS : ℕ) : ℕ :=
  kfAbsorbSideRequests S P w q kq + ((S + P) * max w 3 + 1) * qS

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq X₀]
  [Inhabited M.NIProof] [Nonempty T.KeyCoins] in
/-- The numbers of `assignSideBase` for base adversaries with at most `S` slots, `P` post batches
and
width `w`, through relays with one oracle read and one pad sub-slot: the requests. -/
theorem bT_assignSideBase_le {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Inhabited Rq]
    [Fintype Rs] [DecidableEq Rs] {shA₀ : AlgShape Xq Y Rq Rs} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (G : (Xq → Y₁) → AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xq Y₁)
    (Q : ℕ) (C₁ : Challenger Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b))
    (F' : TwoRelay (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) (Stmt × (MUR ⊕ R)) (M.Response b)
      MUR (MUResponse B.core)) (kq' : ℕ) {S P w : ℕ} (hsl : A₀.slots ≤ S) (hpo : A₀.post ≤ P)
    (hwd : A₀.width ≤ w) (hG1 : (G 0).qG = 1 ∧ (G 0).qP = 1) :
    bT (((AdaptiveIAlg.assignSideBase A₀ G Q).mapOut Prod.fst).restrictAt sp 0) C₁ F' kq' ≤
      (S + P) * max w 3 * (C₁.q + 1) + kq' := by
  obtain ⟨h1, h2, h3⟩ := AdaptiveIAlg.relayAdv_numbers (A := A₀.absorbAssignP (MUR ⊕ R)
    (MUResponse B.core ⊕ M.Response b) Q) (Q := Q) (((G 0).relayOf Q).withSide 0)
    ((A₀.absorbAssignP (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Q).relayOut ((G 0).relayOf Q))
  rw [bT_mapOut_restrictAt_eq sp _ _ _ _ _ h1 h2, h3]
  change (A₀.slots + A₀.post) * max A₀.width (1 + (G 0).qG + (G 0).qP) * (C₁.q + 1) + kq' ≤ _
  rw [hG1.1, hG1.2]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.add_le_add hsl hpo)
    (max_le_max hwd le_rfl))) _

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq X₀]
  [Inhabited M.NIProof] [Nonempty T.KeyCoins] in
/-- The side reads of `assignSideBase` in all, for base adversaries with at most `S` slots, `P` post
batches and width `w`, through relays with one oracle read, one pad sub-slot and `qS` side reads. -/
theorem sum_sideSteps_assignSideBase_le {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq]
    [Inhabited Rq] [Fintype Rs] [DecidableEq Rs] 
    {shA₀ : AlgShape Xq Y Rq Rs} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (G : (Xq → Y₁) → AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xq Y₁)
    (Q : ℕ) {S P w qS : ℕ} (hsl : A₀.slots ≤ S) (hpo : A₀.post ≤ P) (hwd : A₀.width ≤ w)
    (hG1 : (G 0).qG = 1 ∧ (G 0).qP = 1 ∧ (G 0).qS = qS) :
    ∑ j, ((AdaptiveIAlg.sideSteps_assignSideBase A₀ G Q).mapOut Prod.fst).S.nb j ≤
      ((S + P) * max w 3 + 1) * qS := by
  refine (AdaptiveIAlg.sum_sideSteps_relayAdv_nb_le
    (A₀.absorbAssignP (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Q) ((G 0).relayOf Q) Q
    ((A₀.absorbAssignP (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Q).relayOut
      ((G 0).relayOf Q))).trans ?_
  obtain ⟨-, -, h3⟩ := AdaptiveIAlg.relayAdv_numbers (A := A₀.absorbAssignP (MUR ⊕ R)
    (MUResponse B.core ⊕ M.Response b) Q) (Q := Q) (((G 0).relayOf Q).withSide 0)
    ((A₀.absorbAssignP (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Q).relayOut ((G 0).relayOf Q))
  rw [h3]
  change ((A₀.slots + A₀.post) * max A₀.width (1 + (G 0).qG + (G 0).qP) + 1) * (G 0).qS ≤ _
  rw [hG1.1, hG1.2.1, hG1.2.2]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add hsl hpo)
    (max_le_max hwd le_rfl)) _)

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq X₀]
  [Inhabited M.NIProof] [Nonempty T.KeyCoins] in
/-- **The forger's request bound for absorbed relays** (`hQ` of `kfCanonSide_le_muEufNmaProb`). -/
theorem hQ_assignSideBase {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Inhabited Rq]
    [Fintype Rs] [DecidableEq Rs] {shA₀ : AlgShape Xq Y Rq Rs} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (G : (Xq → Y₁) → AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xq Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (pks : Fin n → B.PK) {S P w : ℕ} (hsl : A₀.slots ≤ S) (hpo : A₀.post ≤ P)
    (hwd : A₀.width ≤ w) (hG1 : (G 0).qG = 1 ∧ (G 0).qP = 1) :
    bT (((AdaptiveIAlg.assignSideBase A₀ G Q).mapOut Prod.fst).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (kq + Q * Psim.q) + 1 ≤ kfAbsorbSideRequests S P w Psim.q (kq + Q * Psim.q) :=
  Nat.add_le_add_right (bT_assignSideBase_le sp A₀ G Q (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) hsl hpo hwd
      hG1) 1

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq X₀]
  [Inhabited M.NIProof] [Nonempty T.KeyCoins] in
/-- **The forger's query budget for absorbed relays** (`ht` of `kfCanonSide_le_muEufNmaProb`). -/
theorem ht_assignSideBase {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Inhabited Rq]
    [Fintype Rs] [DecidableEq Rs] {shA₀ : AlgShape Xq Y Rq Rs} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (G : (Xq → Y₁) → AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xq Y₁)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (pks : Fin n → B.PK) {S P w qS : ℕ} (hsl : A₀.slots ≤ S) (hpo : A₀.post ≤ P)
    (hwd : A₀.width ≤ w) (hG1 : (G 0).qG = 1 ∧ (G 0).qP = 1 ∧ (G 0).qS = qS) :
    bT (((AdaptiveIAlg.assignSideBase A₀ G Q).mapOut Prod.fst).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (kq + Q * Psim.q) + 1 +
        ∑ j, ((AdaptiveIAlg.sideSteps_assignSideBase A₀ G Q).mapOut Prod.fst).S.nb j ≤
      kfAbsorbSideBudget S P w Psim.q (kq + Q * Psim.q) qS :=
  Nat.add_le_add (hQ_assignSideBase sp rel enc dummyS A₀ G Psim Q kq pks hsl hpo hwd
    ⟨hG1.1, hG1.2.1⟩) (sum_sideSteps_assignSideBase_le A₀ G Q hsl hpo hwd hG1)

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [Nonempty T.KeyCoins] in
/-- **The canonical witness's goal in the run of an adversary with the relay at `ω` absorbed** is
that in the run of the relayed adversary at zero with the Kraus maps at `ω`
(`AdaptiveIAlg.absorbAssign_apply_eq_assignSideBase`), its output read through `Prod.fst` after
the restriction at `ω`, when the relay at `ω` is the relay at zero with side `ω` (`hG`). -/
theorem simProb_absorbAssign_eq_assignSideBase {Rq Rs WitK Wt : Type} [Fintype Rq]
    [DecidableEq Rq] [Inhabited Rq] [Fintype Rs] [DecidableEq Rs]
    {shA₀ : AlgShape Xq Y Rq Rs} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (G : (Xq → Y₁) → AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xq Y₁)
    (Q : ℕ) (ω : Xq → Y₁) (hG : (G ω).relayOf Q = ((G 0).relayOf Q).withSide ω)
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok Gl : Frg × X₀ → List (MUR ⊕ R) → Wt → Prop) [∀ f rs, DecidablePred (ok f rs)] :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS) prf keys Q (((A₀.absorbAssign (G ω) Q).restrictAt sp ω).mapOut
          Prod.fst)) Psim Q kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
        keys Q (((A₀.absorbAssign (G ω) Q).restrictAt sp ω).mapOut Prod.fst) Psim Ext wit ok Gl) =
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS) prf keys Q ((((AdaptiveIAlg.assignSideBase A₀ G Q).mapOut
          Prod.fst).withStep (AdaptiveIAlg.assignSideSteps A₀ G Q ω)).restrictAt sp ω)) Psim Q kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
        keys Q ((((AdaptiveIAlg.assignSideBase A₀ G Q).mapOut Prod.fst).withStep
          (AdaptiveIAlg.assignSideSteps A₀ G Q ω)).restrictAt sp ω) Psim Ext wit ok Gl) :=
  (AdaptiveIAlg.absorbAssign_apply_eq_assignSideBase A₀ G Q
    (fun X => simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel)
        (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys Q
          ((X.restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
        keys Q ((X.restrictAt sp ω).mapOut Prod.fst) Psim Ext wit ok Gl)) ω hG).trans
    (simProb_restrictAt_mapOut_comm sp Qs rel enc dummyS _ _ prf keys Q Psim kq Ext wit ok Gl ω)

/-- **The canonical witness's goal for adversaries with a family of assigning relays absorbed, as
MU-EUF-NMA^corr** (`kfCanonSide_le_muEufNmaProb` at `AdaptiveIAlg.assignSideBase`): for
`t`-query adversaries `𝒜 pks` with at most `S` slots, `P` post batches and width `w`, and relays
`G pks sc ω` with one oracle read, one pad sub-slot and `qS` side reads whose relay at `ω` is the
relay at zero with side `ω` (`hG`), the average over the users' key coins, the side coins, a
uniform base component `ω` and the auxiliary input of the canonical witness's goal `Gl ω` in the
extraction run of `𝒜` with `G` absorbed and restricted at `ω` is at most the success probability
of `kfCanonSideForger` in MU-EUF-NMA^corr with `kfAbsorbSideRequests` requests and the query
budget `kfAbsorbSideBudget`. -/
theorem kfAbsorbSide_le_muEufNmaProb {Rq Rs SC WitK Wt : Type} [Fintype Rq] [DecidableEq Rq]
    [Inhabited Rq] [Fintype Rs] [DecidableEq Rs] [Fintype SC] [Nonempty SC] {t Q : ℕ}
    -- TODO(binder-pass): the key coins' law reads the instances of `Fin n → B.KeyCoins` as binders,
    -- so concrete statements supply their own (`instFintypeVector`), not the types record's.
    [iKF : Fintype (Fin n → B.KeyCoins)] [iKN : Nonempty (Fin n → B.KeyCoins)]
    (𝒜 : (Fin n → B.PK) → QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t)
    (G : (Fin n → B.PK) → (Fin Q → SC) → (Xq → Y₁) →
      AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) Xq Y₁)
    (hG : ∀ pks sc ω, (G pks sc ω).relayOf Q = ((G pks sc 0).relayOf Q).withSide ω)
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → Wt)
    (ok : (Fin n → B.PK) → Frg × X₀ → List (MUR ⊕ R) → Wt → Prop)
    [∀ pks f rs, DecidablePred (ok pks f rs)]
    (Gl : (Xq → Y₁) → Frg × X₀ → List (MUR ⊕ R) → Wt → Prop)
    (rd : Frg × X₀ → Option Wt → B.PK × B.BMsg × B.BSig)
    (hver : ∀ pks (ω : Xq → Y₁) (h : Xq → XOut k e) f rs w, ok pks f rs w → Gl ω f rs w →
      B.bverify (join sp ω h) (rd f (some w)).1 (rd f (some w)).2.1 (rd f (some w)).2.2 = true)
    (hhon : ∀ pks f rs w, ok pks f rs w →
      ∃ i, pks i = (rd f (some w)).1 ∧ (.inl (.corrupt i) : MUR ⊕ R) ∉ rs)
    {S P w qS : ℕ} (hsl : ∀ pks a, ((𝒜 pks).alg a).slots ≤ S)
    (hpo : ∀ pks a, ((𝒜 pks).alg a).post ≤ P) (hwd : ∀ pks a, ((𝒜 pks).alg a).width ≤ w)
    (hG1 : ∀ pks sc, (G pks sc 0).qG = 1 ∧ (G pks sc 0).qP = 1 ∧ (G pks sc 0).qS = qS) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' sc, PMF.uniformOfFintype (Fin Q → SC) sc *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          ∑' a, ((𝒜 fun i => B.pk (keys i)).aux.bind fun a => (PMF.pure ()).map fun s => (a, s)) a *
            simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel)
              (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys Q
              (((((𝒜 _).alg a.1).absorbAssign (G (fun i => B.pk (keys i)) sc ω) Q).restrictAt sp
                ω).mapOut Prod.fst)) Psim Q kq)
            (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS)
              prf keys Q (((((𝒜 _).alg a.1).absorbAssign (G (fun i => B.pk (keys i)) sc ω)
                Q).restrictAt sp ω).mapOut Prod.fst) Psim
              Ext wit (ok fun i => B.pk (keys i)) (Gl ω)) ≤
      muEufNmaProb (kfCanonSideForger sp Qs rel enc dummyS (fun pks => kfAbsAux (𝒜 pks) SC Q)
        (fun pks => kfAbsAuxLaw (𝒜 pks) (PMF.uniformOfFintype (Fin Q → SC)))
        (fun pks p => AdaptiveIAlg.assignSideBase ((𝒜 pks).alg (kfAbsAux.fst p).1)
          (G pks (kfAbsAux.coins p)) Q) prf Psim Q kq
        (fun pks p => AdaptiveIAlg.assignSideSteps ((𝒜 pks).alg (kfAbsAux.fst p).1)
          (G pks (kfAbsAux.coins p)) Q)
        (fun pks p => AdaptiveIAlg.sideSteps_assignSideBase ((𝒜 pks).alg (kfAbsAux.fst p).1)
          (G pks (kfAbsAux.coins p)) Q)
        Ext wit ok rd (kfAbsorbSideBudget S P w Psim.q (kq + Q * Psim.q) qS) fun pks p =>
          ht_assignSideBase sp rel enc dummyS ((𝒜 pks).alg (kfAbsAux.fst p).1)
            (G pks (kfAbsAux.coins p)) Psim Q kq pks (hsl pks _) (hpo pks _) (hwd pks _)
              (hG1 pks (kfAbsAux.coins p)))
        (kfAbsorbSideRequests S P w Psim.q (kq + Q * Psim.q)) := by
  obtain rfl : iKF = Pi.instFintype := Subsingleton.elim _ _
  have key := kfCanonSide_le_muEufNmaProb sp Qs rel enc dummyS
    (fun pks => kfAbsAux (𝒜 pks) SC Q)
    (fun pks => kfAbsAuxLaw (𝒜 pks) (PMF.uniformOfFintype (Fin Q → SC)))
    (fun pks p => AdaptiveIAlg.assignSideBase ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Q) prf Psim Q kq
    (fun _ _ => AdaptiveIAlg.tracePreserving_abortAlg _)
    (fun pks p => AdaptiveIAlg.assignSideSteps ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Q)
    (fun pks p => AdaptiveIAlg.sideSteps_assignSideBase ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Q) Ext wit ok Gl rd hver hhon _
    (fun pks p => ht_assignSideBase sp rel enc dummyS ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Psim Q kq pks (hsl pks _) (hpo pks _) (hwd pks _)
        (hG1 pks (kfAbsAux.coins p)))
    (fun pks p => hQ_assignSideBase sp rel enc dummyS ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Psim Q kq pks (hsl pks _) (hpo pks _) (hwd pks _)
        ⟨(hG1 pks (kfAbsAux.coins p)).1, (hG1 pks (kfAbsAux.coins p)).2.1⟩)
  refine le_of_eq_of_le ?_ key
  refine tsum_congr fun keys => congrArg _ ?_
  refine (tsum_kfAbsAuxLaw_avg (𝒜 _) _ _ _).trans ?_
  refine tsum_congr fun p => congrArg _ (tsum_congr fun ω => congrArg _ ?_)
  exact simProb_absorbAssign_eq_assignSideBase sp Qs rel enc dummyS _ _ Q ω (hG _ _ ω) prf keys
    Psim kq Ext wit _ _

end RingSignature.KeyFree

end GordieHowe
