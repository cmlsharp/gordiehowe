-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1H3Run
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeH3Chain
public import GordieHowe.Applications.Ring.MLDSAW1HedgedPS
public import GordieHowe.Applications.Ring.SPBCSSplitVerifies
public import GordieHowe.Applications.Ring.MLDSAW1H3Cases

@[expose] public section

/-!
# The unforgeability bound of the converted ML-DSA ring signature publishing `w₁`, by case

The forgery probability (BKM06 Definition 7) of the converted scheme `w1ConvConcrete` at the
concrete primitives, through the empty-ring step (`w1Concrete.insiderForgeProb_le_nonempty`), the
backbone of the key-free chain at the proof system `w1HPS` checking a nonempty ring
(`insiderForgeProb_le_w1KFChain`) and the split of the forger's win into its cases
(`tsum_simProb_w1Goal_le`).

- `w1ConvAdv`: the adversary against the converted scheme relabelled to the verifier rejecting the
  empty ring, read against the hedged scheme of `w1HPS`.
- `QueryBoundedAdversary.tsum_absorbAssign_restrictAt_mapOut`, `ENNReal.tsum3_add_const`: averages
  of absorbed adversaries and of constants.
- `tsum_simProb_w1Goal_le_chain`, `WbbC_eq`, `tsum_WbbC_eq`, `w1KFChainAvg_le_cases`: the backbone's
  average split into the cases.
- `insiderForgeProb_w1ConvAdv_le_backbone`, `w1ConvConcrete.insiderForgeProb_le_w1ConvAdv`,
  `w1ConvConcrete.insiderForgeProb_le_backbone`: the empty-ring step and the backbone.
- `w1ConvConcrete.insiderForgeProb_le_cases_aux` (private): the bound by case.
- `w1ChainAdv_width_le`: a schedule bound of the adversary bounds the width of the chain's
  adversary.
- `w1H3HopError`, `w1H3CaseError`: the hops to the key-free relay challenger and
  the cases of the forger's win.
- `w1SimExtF_eq`, `w1ZkF_eq`, `ENNReal.add_regroup7`: the errors of `Sc` and a regrouping.
- `w1ConvConcrete.insiderForgeProb_le` (**the bound by case**), at the hedged program
  statements and a schedule bound of the adversary.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree RingSignature.Insider
open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP GordieHowe.MLDSA.Regularity
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {I J Y₁ : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {sp : OracleSplit (BitStr I J) Y₁ (XOut kh e)}
  [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) (BitStr I J) p (concretePrimitivesKeyGen p) Msg N
    reps}
  {MO : MaskOracle (Bits (queryBits kh kN kS L)) (BitStr I J) p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {kr D : ℕ} [NeZero D] [Nonempty Msg]
  [Nonempty (FIPSSignature p (concretePrimitivesKeyGen p))]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen p) Msg N) kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt (concretePrimitivesKeyGen p) Msg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Pc" => concretePrimitivesKeyGen p
local notation "bmc" => (fun (_ : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N) (m : Msg) => m)
local notation "Lh" => hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D
local notation "Lf" => freshLoop (concretePrimitivesKeyGen p) O MO βmin kr D
local notation "Bc" => w1ConcreteBase p O MO βmin tol kr D (RMsg := Msg) bmc
local notation "Bf" => freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen p) Msg N
local notation "PSc" => w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) Lh bmc Sc Λ
  E hb honest
local notation "PSn" => w1PSNonempty sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) Lh
  bmc Sc Λ E hb honest
local notation "chkN" => fun (x : RingSignature.RingStmt (freshBase (concretePrimitivesKeyGen p) O
  MO βmin tol (concreteEnc p) kr D bmc)) =>
  decide (Subtype.val (RingSignature.RingStmtOf.ring x) ≠ [])
attribute [local instance] admDecF

/-- **The absorbed adversary restricted and relabelled, value by value**: the average over the
auxiliary inputs of a function of the algorithm of `((𝒜.absorbAssign (pure ()) G …).restrictAt sp ω)
.mapOut f` is the average over `𝒜.aux` (paired with `()`) of the function at
`(((𝒜.alg a).absorbAssign G Q).restrictAt sp ω).mapOut f`. -/
theorem _root_.GordieHowe.Quantum.QueryBoundedAdversary.tsum_absorbAssign_restrictAt_mapOut
    {X Y Y₁ Y₂ Req Resp O O' Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [AddGroup Ys]
    [Fintype Ys] [DecidableEq Ys] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
    [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y] [AddGroup Y₁]
    [AddGroup Y₂] [Nonempty Y] [Nonempty Y₂] {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (qG : ℕ) (hG : G.qG ≤ qG) (qP : ℕ)
    (hP : G.qP ≤ qP) (Q : ℕ) (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) (f : O × (X → Option Y) → O')
    -- TODO(unbundle-M4): the shape of the algorithm varies with the auxiliary input, so `F` is
    -- shape-polymorphic.
    (F : ∀ {sh : AlgShape X Y₂ Req' Resp'}, AdaptiveIAlg sh O' → ℝ≥0∞) :
    ∑' a, (((𝒜.absorbAssign (PMF.pure ()) (fun _ => G) qG (fun _ => hG) qP (fun _ => hP)
        Q).restrictAt sp ω).mapOut f).aux a *
      F ((((𝒜.absorbAssign (PMF.pure ()) (fun _ => G) qG (fun _ => hG) qP (fun _ => hP)
        Q).restrictAt sp ω).mapOut f).alg a) =
    ∑' a, (𝒜.aux.bind fun a => (PMF.pure ()).map fun s => (a, s)) a *
      F (((((𝒜.alg a.1).absorbAssign G Q).restrictAt sp ω).mapOut f)) := by
  dsimp only [QueryBoundedAdversary.mapOut, QueryBoundedAdversary.restrictAt,
    QueryBoundedAdversary.absorbAssign]
  rfl

/-- **`tsum_absorbAssign_restrictAt_mapOut` across a change of the response type**: the same
identity, read on the right at a relay `G₂` and a function `F₂` that agree with `G₁` and `F₁` up to
the equal response types `Resp₁ = Resp₂`. -/
theorem _root_.GordieHowe.Quantum.QueryBoundedAdversary.tsum_absorbAssign_restrictAt_mapOut_congr
    {X Y Y₁ Y₂ Req Resp O O' Req' Resp₁ Resp₂ Xs Ys : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
    [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [fR₁ : Fintype Resp₁]
    [dR₁ : DecidableEq Resp₁] [fR₂ : Fintype Resp₂] [dR₂ : DecidableEq Resp₂]
    [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y] [AddGroup Y₁]
    [AddGroup Y₂] [Nonempty Y] [Nonempty Y₂] {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (G₁ : AssignRelay X Y Req Resp Req' Resp₁ Xs Ys) (G₂ : AssignRelay X Y Req Resp Req' Resp₂ Xs Ys)
    (qG : ℕ) (hG : G₁.qG ≤ qG) (qP : ℕ) (hP : G₁.qP ≤ qP) (Q : ℕ) (sp : Y ≃+ Y₁ × Y₂)
    (ω : X → Y₁) (f : O × (X → Option Y) → O')
    (F₁ : ∀ {sh : AlgShape X Y₂ Req' Resp₁}, AdaptiveIAlg sh O' → ℝ≥0∞)
    (F₂ : ∀ {sh : AlgShape X Y₂ Req' Resp₂}, AdaptiveIAlg sh O' → ℝ≥0∞)
    (hR : Resp₁ = Resp₂) (hf : fR₁ ≍ fR₂) (hd : dR₁ ≍ dR₂) (hGG : G₁ ≍ G₂)
    (hF : @F₁ ≍ @F₂) :
    ∑' a, (((𝒜.absorbAssign (PMF.pure ()) (fun _ => G₁) qG (fun _ => hG) qP (fun _ => hP)
        Q).restrictAt sp ω).mapOut f).aux a *
      F₁ ((((𝒜.absorbAssign (PMF.pure ()) (fun _ => G₁) qG (fun _ => hG) qP (fun _ => hP)
        Q).restrictAt sp ω).mapOut f).alg a) =
    ∑' a, (𝒜.aux.bind fun a => (PMF.pure ()).map fun s => (a, s)) a *
      F₂ (((((𝒜.alg a.1).absorbAssign G₂ Q).restrictAt sp ω).mapOut f)) := by
  subst hR
  cases hf
  cases hd
  cases hGG
  cases hF
  exact QueryBoundedAdversary.tsum_absorbAssign_restrictAt_mapOut 𝒜 G₁ qG hG qP hP Q sp ω f F₁

/-- **An average of a sum with constants**: for distributions `u`, `v`, `r`, the triple average of
`W x y z + c + d` is the triple average of `W` plus `c + d`. -/
theorem _root_.GordieHowe.ENNReal.tsum3_add_const {α β γ : Type} (u : PMF α) (v : PMF β)
    (r : PMF γ) (W : α → β → γ → ℝ≥0∞) (c d : ℝ≥0∞) :
    ∑' x, u x * ∑' y, v y * ∑' z, r z * (W x y z + c + d) =
      (∑' x, u x * ∑' y, v y * ∑' z, r z * W x y z) + c + d := by
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
    add_assoc]

local notation "PSh" => w1HPS sp (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
  (Sc) Λ E (hb) (honest) chkN
local notation "PSf" => (PSh)
local notation "Sh" => hedgedScheme (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D
  bmc PSh adm
local notation "Sf" => freshScheme (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D
  bmc PSh adm

variable (O MO βmin tol kr D Sc Λ E hb honest adm) in
/-- **The adversary against the converted scheme, its verifier rejecting the empty ring**: `A`
relabelled to the scheme of `w1PSNonempty` (`UnforgeAdversary.withVerify`), read as an adversary
against the hedged scheme of `w1HPS` at the check of a nonempty ring (`w1HPS_eq_w1PSNonempty`). -/
noncomputable abbrev w1ConvAdv {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) :
    InsiderAdversary (Sh) n (OracleView.queriesOnly Xq (BitStr I J)) t :=
  UnforgeAdversary.withVerify (S := ofBase Bc PSc adm) (ofBase Bc PSn adm).verify
    (SideOracle.none _) A
variable [Inhabited Sc.NIProof]

/-- The proofs of `Sc` at the fresh program statements are inhabited, by the instance at the
hedged ones. -/
@[reducible] noncomputable local instance : Inhabited (SPBCS.NIProof (X := W1ExpStmt (concretePrimitivesKeyGen p) Msg N) Sc) :=
  ‹Inhabited Sc.NIProof›

omit [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Nonempty Msg]
  [Nonempty (FIPSSignature p (concretePrimitivesKeyGen p))] [Inhabited Sc.NIProof]
  [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The width bound of the chain's adversary, scaled by the statement program's `2N` reads**: the
bound passed to `thenProgOut`. A named proof whose arguments are variables, so definitions keep it
as it is and statements and definitions spell the same term. -/
theorem w1WidthMul {t : ℕ} {A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t} {w : ℕ}
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc Sc Λ E hb
        honest adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A) pks).alg a).width ≤ w)
    (pks : Fin n → (Bf).PK) :
    ∀ a, ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc Sc Λ E hb
        honest adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A) pks).alg a).width *
          (2 * N) ≤ w * (2 * N) :=
  fun a => Nat.mul_le_mul_right _ (hw pks a)

set_option hygiene false
set_option quotPrecheck false

/-- The adversary of the chain at `keys`, followed by the program statement of its forgery. -/
local notation "TPA" keys:max => (QueryBoundedAdversary.thenProgOut (w1ChainAdv
  (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc (Sc) Λ E
      (hb)
  (honest) adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A)
    (fun i => (Bf).pk (keys i)))
  (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O bmc (Sc))
  (2 * N) (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O bmc (Sc)) (w * (2 * N))
  (w1WidthMul hw (fun i => (Bf).pk (keys i))))

/-- The auxiliary input of the absorbed adversary at `keys`. -/
local notation "auxC" keys:max => ((TPA keys).aux.bind fun a => (PMF.pure ()).map fun s => (a, s))

/-- The encoding of the main requests at `keys`. -/
local notation "pencC" => fun (keys : Fin n → (Bf).KeyCoins) => w1Enc (PS := PSh) (adm := adm)
  (Q := Q) fun i => (Bf).pk (keys i)

/-- The simulator of the main proofs. -/
local notation "PsimC" => ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
  VE.toViewRead b pub Sim Tp) p₀).comap (w1StmtX ∘ Prod.fst))

/-- The run's adversary at `keys`, `sc`, `ω` and the auxiliary input `a`. -/
local notation "AdvRc" keys:max sc:max ω:max a:max =>
  (((((TPA keys).alg a.1).absorbAssign
    (Resp' := MUResponse (freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D
      bmc).core ⊕ (Sc).Response b)
    (kfRelaySide sp (freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc)
      (fun j => (freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc).pk
        (keys j))
      (w1KFFactors (T := T) (concretePrimitivesKeyGen p) O sp βmin tol (concreteEnc p) kr D bmc
        h.hO)
      (w1KFStmt (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc sp)
      (w1ToR (PS := PSh) (Q := Q)) (w1DummyR (PS := PSh) (Q := Q)) sc ω w1Idle) Q).restrictAt sp
    ω).mapOut Prod.fst)

/-- The run's adversary, its responses read at the proofs of `PSf`. -/
local notation "AdvRcP" keys:max sc:max ω:max a:max =>
  (((((TPA keys).alg a.1).absorbAssign
    (Resp' := MUResponse (freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D
      bmc).core ⊕ Sc.Response b)
    (w1SideRelay sp (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
        (Sc) Λ
      E (hb) (honest) adm chkN h keys sc ω) Q).restrictAt sp
          ω).mapOut Prod.fst)

/-- The forger's win at `w1Goal` in the run of `AdvRc keys sc ω a`. -/
local notation "WinRc" keys:max sc:max ω:max a:max =>
  simProb (outEquiv kh e) (extAdv (Qs) (seAlgKF (rel := w1Rel
      (concretePrimitivesKeyGen
    p) O
      MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm) (Q
        := Q)
      fun i => (Bf).pk (keys i))
      (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q (AdvRc keys sc ω a)) PsimC Q
      (kqOf Mg nr b b))
    (forgerWinsKF (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
      PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q)
      fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q
      (AdvRc keys sc ω a) PsimC Ext (fun _ w => w) (w1Goal (concretePrimitivesKeyGen p) O MO βmin
        tol (concreteEnc p) kr D bmc adm sp (fun j => (Bf).pk (keys j)) ω))

/-- The canonical witness's goal `Gl` in the run of `AdvRc keys sc ω a`. -/
local notation "CanRc" keys:max sc:max ω:max a:max Gl:max =>
  simProb (outEquiv kh e) (extAdv (Qs) (seAlgKF (rel := w1Rel
      (concretePrimitivesKeyGen
    p) O
      MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm) (Q
        := Q)
      fun i => (Bf).pk (keys i))
      (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q (AdvRc keys sc ω a)) PsimC Q
      (kqOf Mg nr b b))
    (forgerCanonKF (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
      PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q)
      fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q
      (AdvRc keys sc ω a) PsimC Ext (fun _ w => w) (w1Ok (concretePrimitivesKeyGen p) O MO βmin tol
        (concreteEnc p) kr D bmc adm (fun j => (Bf).pk (keys j))) Gl)

/-- The forger's win at `w1Goal` for an algorithm `B` at `keys` and `ω`. -/
local notation "WinFc" keys:max ω:max => fun {shB : AlgShape Xq (XOut kh e) (MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq (concretePrimitivesKeyGen p) O MO βmin tol
      (concreteEnc p) kr D bmc PSh adm n Q) (MUResponse (Bf).core ⊕ (Sc).Response b)} (B : AdaptiveIAlg shB ((KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × Msg × (BucketVec p × (Sc).Response
      b))
      × X₀f)) =>
  simProb (outEquiv kh e) (extAdv (Qs) (seAlgKF (rel := w1Rel
      (concretePrimitivesKeyGen
    p) O
      MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm)
      (Q := Q) fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q B) PsimC Q
      (kqOf Mg nr b b))
    (forgerWinsKF (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
      PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun i => (Bf).pk (keys i))
      (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q B PsimC Ext (fun _ w => w)
      (w1Goal (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc adm sp
        (fun j => (Bf).pk (keys j)) ω))

/-- The forger's win at `w1Goal` for an algorithm with the responses of `PSf`. -/
local notation "WinFcP" keys:max ω:max => fun {shB : AlgShape Xq (XOut kh e) (MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq (concretePrimitivesKeyGen p) O MO βmin tol
      (concreteEnc p) kr D bmc PSh adm n Q) (MUResponse (Bf).core ⊕ Sc.Response b)} (B : AdaptiveIAlg shB ((KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × Msg × (BucketVec p × (Sc).Response
      b))
      × X₀f)) =>
  simProb (outEquiv kh e) (extAdv (Qs) (seAlgKF (rel := w1Rel
      (concretePrimitivesKeyGen
    p) O
      MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm)
      (Q := Q) fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q B) PsimC Q
      (kqOf Mg nr b b))
    (forgerWinsKF (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
      PSh adm n Q) (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun i => (Bf).pk (keys i))
      (dummyS := w1DummyS PSh adm n Q) w1PrfOf keys Q B PsimC Ext (fun _ w => w)
      (w1Goal (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc adm sp
        (fun j => (Bf).pk (keys j)) ω))

/-- The forger's win at `w1Goal` in the absorbed run at `keys`, `sc` and `ω`, averaged over the
auxiliary input (the summand of the backbone). -/
local notation "WbbC" keys:max sc:max ω:max => (∑' a, ((((QueryBoundedAdversary.thenProgOut
  (w1ChainAdv Pc O MO βmin tol (concreteEnc p) kr D
                bmc (Sc) Λ E (hb) (honest) adm
                    chkN (w1ConvAdv O MO βmin tol
                  kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                      (w1ForgeStmtProg_queries sp Pc O bmc (Sc))
                        (w * (2 * N))
                      (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                    (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                        (Sc)
                      Λ E (hb) (honest) adm
                      chkN h
                      keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                    Prod.fst).aux a *
                simProb (outEquiv kh e)
                  (extAdv (Qs) (seAlgKF (rel := w1Rel Pc O MO βmin tol
                      (concreteEnc p) kr
                    D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a))
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
                  (forgerWinsKF (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a)
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
                    (w1Goal Pc O MO βmin tol (concreteEnc p) kr D bmc adm sp (fun i => (Bf).pk
                      (keys i))
                      ω)))

set_option quotPrecheck true
set_option hygiene true

open Classical in
omit [DecidableEq R] in
omit [DecidableEq R] in
/-- **`tsum_simProb_w1Goal_le` at the adversary of the chain.** -/
theorem tsum_simProb_w1Goal_le_chain
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (hp : p.isApproved) (_hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (_hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (_c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (_hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (_hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b) :
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * WinRc ξ sc ω a) ≤
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun f _ w
            => w1CaseU (bmsg := bmc) O sp ω f w)) +
      (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun _ rs w
            => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧
          w1EntrySig e' = some w.sig ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) kr D bmc h.hO)
            (w1StmtPω Pc O MO βmin tol (concreteEnc p) kr D bmc sp) (w1ToR (Q := Q)) sc ω e')) +
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
            (w1SecondRunLaw (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
              (dummyS := w1DummyS PSh adm n Q) (Qs) (kqOf Mg nr b b) pencC
                  w1PrfOf
              (fun ξ _ _ => auxC ξ)
              (fun ξ sc ω a => AdvRc ξ sc ω a) PsimC Ext
              (fun ξ => w1Ok Pc O MO βmin tol (concreteEnc p) kr D bmc adm
                (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
          (w1MsisReadout sp h.hO ξ)) +
      trCollAt Pc n := by
  have hR := tsum_simProb_w1Goal_le (Mc := Sc) (Qs := Qs) (hb :=
      hb)
    (honest := honest) (chk := chkN) (Q := Q)
    (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
    (dummyS := w1DummyS PSh adm n Q) sp hp h.hO h.hdisj h.uniformSplit.muPt_injective
    (kqOf Mg nr b b) pencC w1PrfOf w1Idle rfl (fun ξ _ _ => auxC ξ)
    (fun ξ _ _ a => (TPA ξ).alg a.1) PsimC Ext
  exact hR

omit [Nonempty Y₁] [DecidableEq R] in
open Classical in
/-- **The backbone's summand at `keys`, `sc` and `ω` is the summand of
`tsum_simProb_w1Goal_le`** (`QueryBoundedAdversary.tsum_absorbAssign_restrictAt_mapOut`). -/
theorem WbbC_eq
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (_hp : p.isApproved) (_hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (_hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (_c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (_hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (_hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (sc : Fin Q → KFCoins (p := p) (T := T) kr D Y₁)
    (ω : Xq → Y₁) :
    WbbC keys sc ω = ∑' a, (auxC keys) a * WinRc keys sc ω a := by
  -- TODO(unbundle-M4): read the right side at the relay and win of `AdvRc` through one equality of
  -- response types (comparing the two algorithm shapes inside the win times out).
  have hR := QueryBoundedAdversary.tsum_absorbAssign_restrictAt_mapOut_congr
    (Resp₂ := MUResponse (Bf).core ⊕ (Sc).Response b) (TPA keys)
    (w1SideRelay sp (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
        (Sc) Λ
      E (hb) (honest) adm chkN h keys sc ω)
    (kfRelaySide sp (freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc)
      (fun j => (freshBase (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc).pk
        (keys j))
      (w1KFFactors (T := T) (concretePrimitivesKeyGen p) O sp βmin tol (concreteEnc p) kr D bmc
        h.hO)
      (w1KFStmt (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc sp)
      (w1ToR (PS := PSh) (Q := Q)) (w1DummyR (PS := PSh) (Q := Q)) sc ω w1Idle)
    1 le_rfl 1 le_rfl Q sp ω Prod.fst (WinFcP keys ω) (WinFc keys ω) rfl HEq.rfl HEq.rfl HEq.rfl
    HEq.rfl
  exact hR.trans (tsum_congr fun a => congrArg (_ * ·) rfl)

open Classical in
omit [DecidableEq R] in
/-- **The backbone's average is the average of `tsum_simProb_w1Goal_le`** at the adversary of the
chain. -/
theorem tsum_WbbC_eq
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (hp : p.isApproved) (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b) :
    ∑' keys, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) keys *
      ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * WbbC keys sc ω =
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * WinRc ξ sc ω a) := by
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun sc => congrArg _
    (tsum_congr fun ω => congrArg _ ?_))
  exact WbbC_eq (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) hp hk h hQm c₀ A hw VE
    pub Sim Tp hvzk hrbr p₀ keys sc ω

open Classical in
omit [DecidableEq R] in
/-- **The backbone's average splits into the three cases** (`tsum_simProb_w1Goal_le` at the
adversary of the chain): the average over the key coins, the side coins and the base components of
the forger's win at `w1Goal` plus the simulation-extraction and zero-knowledge errors is at most the
averages of case U and of the guess, the Module-SIS term, `trCollAt` and the two errors. -/
theorem w1KFChainAvg_le_cases
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (hp : p.isApproved) (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b) :
        ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
          ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
            ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
              (∑' a, ((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                (concreteEnc p) kr D
                bmc (Sc) Λ E (hb) (honest) adm
                    chkN (w1ConvAdv O MO βmin tol
                  kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                      (w1ForgeStmtProg_queries sp Pc O bmc (Sc))
                        (w * (2 * N))
                      (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                    (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                        (Sc)
                      Λ E (hb) (honest) adm
                      chkN h
                      keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                    Prod.fst).aux a *
                simProb (outEquiv kh e)
                  (extAdv (Qs) (seAlgKF (rel := w1Rel Pc O MO βmin tol
                      (concreteEnc p) kr
                    D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a))
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
                  (forgerWinsKF (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a)
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
                    (w1Goal Pc O MO βmin tol (concreteEnc p) kr D bmc adm sp (fun i => (Bf).pk
                      (keys i))
                      ω)) +
                (Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
                  ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
                  (t + w * (2 * N) + Q * 1 + Q * 1) Q +
                ENNReal.ofReal ((Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q))
                    ≤
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun f _ w
            => w1CaseU (bmsg := bmc) O sp ω f w)) +
      (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun _ rs w
            => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧
          w1EntrySig e' = some w.sig ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) kr D bmc h.hO)
            (w1StmtPω Pc O MO βmin tol (concreteEnc p) kr D bmc sp) (w1ToR (Q := Q)) sc ω e')) +
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
            (w1SecondRunLaw (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
              (dummyS := w1DummyS PSh adm n Q) (Qs) (kqOf Mg nr b b) pencC
                  w1PrfOf
              (fun ξ _ _ => auxC ξ)
              (fun ξ sc ω a => AdvRc ξ sc ω a) PsimC Ext
              (fun ξ => w1Ok Pc O MO βmin tol (concreteEnc p) kr D bmc adm
                (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
          (w1MsisReadout sp h.hO ξ)) +
      trCollAt Pc n +
      (Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
        ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
        (t + w * (2 * N) + Q * 1 + Q * 1) Q +
      ENNReal.ofReal ((Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q) := by
  refine le_of_eq_of_le (ENNReal.tsum3_add_const (PMF.uniformOfFintype _)
    (PMF.uniformOfFintype _) (PMF.uniformOfFintype _)
    (fun (keys : Fin n → (Bf).KeyCoins) (sc : Fin Q → KFCoins (p := p) (T := T) kr D Y₁)
      (ω : Xq → Y₁) => WbbC keys sc ω)
    ((Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
      ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
      (t + w * (2 * N) + Q * 1 + Q * 1) Q)
    (ENNReal.ofReal ((Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q)))
        (add_le_add
      (add_le_add ?_ le_rfl) le_rfl)
  exact (le_of_eq (tsum_WbbC_eq (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) hp hk h
    hQm c₀ A hw VE pub Sim Tp hvzk hrbr p₀)).trans
    (tsum_simProb_w1Goal_le_chain (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) hp hk h
      hQm c₀ A hw VE pub Sim Tp hvzk hrbr p₀)

open Classical in
/-- **The converted scheme's forgery probability, through the empty-ring step and the backbone**
(`insiderForgeProb_le_w1KFChain` at the check of a nonempty ring). -/
theorem insiderForgeProb_w1ConvAdv_le_backbone
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (hp : p.isApproved) (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (_c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b) :
    insiderForgeProb (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A) Q ≤
      (ENNReal.ofReal (((Q * kr).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * kr : ℕ) * (2 ^ 256 :
        ℝ)⁻¹)) +
      Q * (√((kr * T : ℝ) * (n * commitPointAt Pc) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
        (kr * T : ℝ) * (n * commitPointAt Pc) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
      2 * √(t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
          ℝ) + Q : ℝ) *
        √((t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
            ℝ) + (1 + kr * T +
          max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * (2 * kr * T * (n * commitPointAt Pc)))) +
      Q * (((kr * T).choose 2 : ℝ) * (n * commitPointAt Pc))) +
      ((12 * ((t + Q * (w1KFq N reps kr T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
                (honest) n Q
              chkN).q) + (N + Q) : ℕ) :
            ℝ≥0∞) ^ 2 *
          ((t + Q * (w1KFq N reps kr T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
                (honest) n Q
              chkN).q) + (N + Q) - 1 : ℕ) :
            ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
          2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
        ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
          ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
            ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
              (∑' a, ((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                (concreteEnc p) kr D
                bmc (Sc) Λ E (hb) (honest) adm
                    chkN (w1ConvAdv O MO βmin tol
                  kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                      (w1ForgeStmtProg_queries sp Pc O bmc (Sc))
                        (w * (2 * N))
                      (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                    (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                        (Sc)
                      Λ E (hb) (honest) adm
                      chkN h
                      keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                    Prod.fst).aux a *
                simProb (outEquiv kh e)
                  (extAdv (Qs) (seAlgKF (rel := w1Rel Pc O MO βmin tol
                      (concreteEnc p) kr
                    D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a))
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
                  (forgerWinsKF (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a)
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
                    (w1Goal Pc O MO βmin tol (concreteEnc p) kr D bmc adm sp (fun i => (Bf).pk
                      (keys i))
                      ω)) +
                (Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
                  ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
                  (t + w * (2 * N) + Q * 1 + Q * 1) Q +
                ENNReal.ofReal ((Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1)
                    Q)))) := by
  have hV := (verifiesBy_spbcsSplitProofSystem sp (Sc) Λ E (Qs)
      (hb)
    (honest)
    (w1StmtProg sp (concretePrimitivesKeyGen p) O bmc) (2 * N)
    (w1StmtProg_queries sp (concretePrimitivesKeyGen p) O bmc) chkN
    (fun _ w => some w))
  have hB := insiderForgeProb_le_w1KFChain (prims := concretePrimitivesKeyGen p)
    (enc := concreteEnc p) (Mo := MO) (bmsg := bmc) (Mc := Sc) (Vr :=
        Vr)
    (Qs := Qs) (hb := hb) (honest := honest)
        (chk := chkN) (Q := Q) hk
    (fun _ hx => of_decide_eq_true hx) h hQm (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp)
    (fun s => keyGenFromSeed_s1_bounded hp s) (fun s => keyGenFromSeed_s2_bounded hp s) hV
    (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A) hw VE pub Sim Tp hvzk hrbr p₀
  convert hB using 1

omit [Inhabited Sc.NIProof] [Nonempty Msg]
  [Nonempty (FIPSSignature p (concretePrimitivesKeyGen p))] in
/-- **The empty-ring step for the converted scheme** (`w1Concrete.insiderForgeProb_le_nonempty`):
the forgery probability of `A` is at most that of `w1ConvAdv A` plus the spBCS knowledge error. -/
theorem w1ConvConcrete.insiderForgeProb_le_w1ConvAdv (h : W1OracleFacts O MO sp)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    {Ext : CausalExtractor P τ (W1ExpStmt (concretePrimitivesKeyGen p) Msg N) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))}
    {St : CausalStateFn P τ (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)} {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) Vr Ext St ε) :
    insiderForgeProb A Q ≤
      insiderForgeProb (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A) Q +
        knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) := by
  convert w1Concrete.insiderForgeProb_le_nonempty (bmsg := bmc) sp h.hO h.hM hrbr c₀ A Q using 2

open Classical in
/-- **The converted scheme's forgery probability, through the empty-ring step and the backbone**
(`w1Concrete.insiderForgeProb_le_nonempty`, `insiderForgeProb_le_w1KFChain` at the check of a
nonempty ring). -/
theorem w1ConvConcrete.insiderForgeProb_le_backbone
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (hp : p.isApproved) (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (((Q * kr).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * kr : ℕ) * (2 ^ 256 :
        ℝ)⁻¹)) +
      Q * (√((kr * T : ℝ) * (n * commitPointAt Pc) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
        (kr * T : ℝ) * (n * commitPointAt Pc) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
      2 * √(t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
          ℝ) + Q : ℝ) *
        √((t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
            ℝ) + (1 + kr * T +
          max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * (2 * kr * T * (n * commitPointAt Pc)))) +
      Q * (((kr * T).choose 2 : ℝ) * (n * commitPointAt Pc))) +
      ((12 * ((t + Q * (w1KFq N reps kr T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
                (honest) n Q
              chkN).q) + (N + Q) : ℕ) :
            ℝ≥0∞) ^ 2 *
          ((t + Q * (w1KFq N reps kr T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
                (honest) n Q
              chkN).q) + (N + Q) - 1 : ℕ) :
            ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
          2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
        ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
          ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
            ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
              (∑' a, ((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                (concreteEnc p) kr D
                bmc (Sc) Λ E (hb) (honest) adm
                    chkN (w1ConvAdv O MO βmin tol
                  kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                      (w1ForgeStmtProg_queries sp Pc O bmc (Sc))
                        (w * (2 * N))
                      (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                    (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                        (Sc)
                      Λ E (hb) (honest) adm
                      chkN h
                      keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                    Prod.fst).aux a *
                simProb (outEquiv kh e)
                  (extAdv (Qs) (seAlgKF (rel := w1Rel Pc O MO βmin tol
                      (concreteEnc p) kr
                    D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a))
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
                  (forgerWinsKF (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv Pc O MO βmin tol
                        (concreteEnc p)
                        kr D bmc (Sc) Λ E (hb) (honest) adm chkN (w1ConvAdv
                          O MO βmin tol kr D Sc Λ E hb honest adm A) (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp Pc O bmc (Sc))
                          (2 * N)
                        (w1ForgeStmtProg_queries sp Pc O bmc (Sc)) (w * (2 * N))
                        (w1WidthMul hw (fun i => (Bf).pk (keys i)))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp Pc O MO βmin tol (concreteEnc p) kr D bmc
                          (Sc) Λ E (hb) (honest)
                        adm chkN
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a)
                    ((inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ
                        VE.toViewRead b
                      pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
                    (w1Goal Pc O MO βmin tol (concreteEnc p) kr D bmc adm sp (fun i => (Bf).pk
                      (keys i))
                      ω)) +
                (Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
                  ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
                  (t + w * (2 * N) + Q * 1 + Q * 1) Q +
                ENNReal.ofReal ((Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1)
                    Q)))) := by
  exact (w1ConvConcrete.insiderForgeProb_le_w1ConvAdv h c₀ A hrbr).trans
    ((add_le_add (insiderForgeProb_w1ConvAdv_le_backbone (Λ := Λ) (E := E) (hb := hb)
      (honest := honest) (Q := Q) hp hk h hQm c₀ A hw VE pub Sim Tp hvzk hrbr p₀) le_rfl).trans_eq
      (add_comm _ _))

omit [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Nonempty Msg]
  [Nonempty (FIPSSignature p (concretePrimitivesKeyGen p))]
  [Inhabited Sc.NIProof]
  [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The width of the chain's adversary is the adversary's**: a schedule bound of `A` with width
`w` bounds the query width of `w1ChainAdv (w1ConvAdv A) pks` by `w`. -/
theorem w1ChainAdv_width_le {t : ℕ}
    {A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t} {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (pks : Fin n → (Bf).PK) a :
    ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
        (Sc) Λ
      E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D Sc
          Λ E hb honest
        adm A) pks).alg a).width ≤ w :=
  hS.width_le _ a

/-- **A four-fold average bounded through its second average**: if for every outer value `x`, third
value `z` and fourth value `d` the average over `v` is at most `B`, so is the whole average (the
averages over `v`, `r` and `μ x` commute, `ENNReal.tsum_mul_tsum_comm`). -/
theorem _root_.GordieHowe.ENNReal.tsum4_le_of_second {α β γ : Type} {δ : α → Type} (u : PMF α)
    (v : PMF β) (r : PMF γ) (μ : (x : α) → PMF (δ x)) (X : (x : α) → β → γ → δ x → ℝ≥0∞)
    (B : ℝ≥0∞)
    (h : ∀ x z d, ∑' y, v y * X x y z d ≤ B) :
    ∑' x, u x * ∑' y, v y * ∑' z, r z * ∑' d, μ x d * X x y z d ≤ B := by
  calc _ = ∑' x, u x * ∑' z, r z * ∑' d, μ x d * ∑' y, v y * X x y z d := by
        refine tsum_congr fun x => congrArg _ ?_
        rw [ENNReal.tsum_mul_tsum_comm]
        exact tsum_congr fun z => congrArg _ (ENNReal.tsum_mul_tsum_comm _ _ _)
    _ ≤ ∑' x, u x * ∑' z, r z * ∑' d, μ x d * B := by
        gcongr with x z d
        exact h x z d
    _ = B := by simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The cases of the forger's win -/

set_option hygiene false
set_option quotPrecheck false

/-- **The chain's adversaries at the users' public keys**, followed by the program statement of
their forgery: the adversary of the chain at the key coins `keys` (`TPA keys`) is this family at
the public keys of `keys`, with the width bound `hw`. -/
local notation "UAdvC" => fun (pks : Fin n → (Bf).PK) => QueryBoundedAdversary.thenProgOut
  (w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc (Sc) Λ E (hb)
    (honest) adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A) pks)
  (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O bmc (Sc)) (2 * N)
  (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O bmc (Sc)) (w * (2 * N))
  (w1WidthMul hw pks)

/-- The key-free relays in side-read mode at the public keys `pks`, the side coins `sc` and the
base component `ω`. -/
local notation "Gkf" => fun (pks : Fin n → (Bf).PK) (sc : Fin Q → KFCoins (p := p) (T := T) kr D Y₁)
  (ω : Xq → Y₁) => kfRelaySide sp Bf pks
    (w1KFFactors (T := T) (concretePrimitivesKeyGen p) O sp βmin tol (concreteEnc p) kr D bmc h.hO)
    (w1KFStmt (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc sp)
    (w1ToR (PS := PSh) (Q := Q)) (w1DummyR (PS := PSh) (Q := Q)) sc ω w1Idle

/-- The queries of the simulator of the main proofs. -/
local notation "PsimQ" => (PsimC : NARG.Simulator Xq (XOut kh e)
  (W1Stmt (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q ×
    (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q))
  ((Sc).Response b) _).q

/-- The side reads of the key-free relay before each Kraus map. -/
local notation "qSkf" => (w1KFFactors (T := T) (concretePrimitivesKeyGen p) O sp βmin tol
  (concreteEnc p) kr D bmc h.hO).qOut +
    (w1KFStmt (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc sp).qSt

/-- **The MU-EUF-NMA^corr forger of case U at the chain** (`w1UForger` at `UAdvC`, the key-free
relays `Gkf`, the simulator of the main proofs and the extractor `Ext`), with the numbers of a
schedule bound `hS`: at most `S` slots, `P' + 2N` post batches and width `w`. -/
local notation "UForgerC" => w1UForger (PS := PSh) (adm := adm) sp (Qs) UAdvC Gkf PsimC
  (kqOf Mg nr b b) Ext f₀
  (S := S) (P' := P' + 2 * N) (w := w) (qS := qSkf) (fun _ a => hS.slots_le _ a)
  (fun _ a => Nat.add_le_add_right (hS.post_le _ a) _) (fun _ a => hS.width_le _ a)
  (fun _ _ => ⟨rfl, rfl, rfl⟩)

open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **Case U of the chain as MU-EUF-NMA^corr** (`w1UAvg_le` at the chain's adversaries at the public keys, the key-free relays
`Gkf`, whose relay at `ω` is the relay at zero with side `ω` by `relayOf_kfRelaySide`): the
average of case U at the canonical witness over the users' key coins, the side coins, the base
component and the auxiliary input is at most the success probability of `w1UForger` in
MU-EUF-NMA^corr with `kfAbsorbSideRequests` requests. -/
theorem w1CaseUAvgC_le (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P')
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc (Sc) Λ E
          (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A)
            pks).alg a).width ≤ w)
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) (p₀ : Sc.Response b)
    (Ext : CausalExtractor P τ X₀f
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) :
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
      ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun f _
          (w : RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) =>
            w1CaseU (bmsg := bmc) O sp ω f w)) ≤
      muEufNmaProb UForgerC
        (kfAbsorbSideRequests S (P' + 2 * N) w PsimQ (kqOf Mg nr b b + Q * PsimQ)) := by
  have key := w1UAvg_le (PS := PSh) (adm := adm) sp (Qs) h.hO UAdvC Gkf
    (fun pks sc ω => relayOf_kfRelaySide sp Bf pks _ _ _ _ sc ω w1Idle Q) PsimC (kqOf Mg nr b b)
    Ext f₀ (S := S) (P' := P' + 2 * N) (w := w) (qS := qSkf) (fun _ a => hS.slots_le _ a)
    (fun _ a => Nat.add_le_add_right (hS.post_le _ a) _) (fun _ a => hS.width_le _ a)
    (fun _ _ => ⟨rfl, rfl, rfl⟩)
  refine le_of_eq_of_le ?_ key
  refine tsum_congr fun ξ => congrArg _ (tsum_congr fun sc => congrArg _
    (tsum_congr fun ω => congrArg _ ?_))
  -- The two sides differ only in the names `w1ExtAdvF`, `w1AbsAdv` (abbreviations): unfolding them
  -- at reducible transparency compares the regular definitions below argument by argument.
  with_reducible rfl

/-- The guess event of case S at the canonical witness: a logged signing entry with the witness's
signature, asked by a signed request of the key-free relay. -/
local notation "GlS" ξ:max sc:max ω:max => fun (_ : (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N ×
    Msg × (BucketVec p × (Sc).Response b)) × X₀f) (rs : List (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q))
    (w : RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) =>
  ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧ w1EntrySig e' = some w.sig ∧
    KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) kr D bmc h.hO)
      (w1StmtPω Pc O MO βmin tol (concreteEnc p) kr D bmc sp) (w1ToR (Q := Q)) sc ω e'

open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The guess event at the canonical witness is the slot guess of the run's outcome**
(`simProb_forgerCanonKF_eq`, `w1CanonSig_eq`, `cast_natOutcome`): the canonical witness satisfies
the guess event `GlS` only if the outcome's readout is the signature of a logged signing entry
asked by a signed request (`w1SlotGuess`). -/
theorem w1CanS_le_slotGuess (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {w : ℕ}
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc (Sc) Λ E
          (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A)
            pks).alg a).width ≤ w)
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) (p₀ : Sc.Response b)
    (Ext : CausalExtractor P τ X₀f
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (ξ : Fin n → (Bf).KeyCoins) (sc : Fin Q → KFCoins (p := p) (T := T) kr D Y₁) (ω : Xq → Y₁)
    (a : (TPA ξ).Aux × Unit) :
    CanRc ξ sc ω a (GlS ξ sc ω) ≤
      ((simPMF (outEquiv kh e) (extAdv (Qs) (seAlgKF (rel := w1Rel (concretePrimitivesKeyGen p) O
          MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
          (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun i => (Bf).pk (ξ i))
          (dummyS := w1DummyS PSh adm n Q) w1PrfOf ξ Q (AdvRc ξ sc ω a)) PsimC Q
          (kqOf Mg nr b b))).map
        (cast (natOutcome_eq_w1Outcome
          (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
          (penc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun i => (Bf).pk (ξ i))
          (dummyS := w1DummyS PSh adm n Q) sp h.hO ξ ω w1Idle w1PrfOf ((TPA ξ).alg a.1) PsimC
          (kqOf Mg nr b b) sc))).toOuterMeasure
        {o | w1SlotGuess sp h.hO ξ ω ((TPA ξ).alg a.1) PsimC (kqOf Mg nr b b) Ext sc o} := by
  refine le_of_eq_of_le (simProb_forgerCanonKF_eq
    (rel := w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
    (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun i => (Bf).pk (ξ i))
    (dummyS := w1DummyS PSh adm n Q) (Qs) w1PrfOf ξ Q (kqOf Mg nr b b) (AdvRc ξ sc ω a) PsimC Ext
    (fun _ w => w) (w1Ok (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc adm
      (fun j => (Bf).pk (ξ j))) (GlS ξ sc ω)) ?_
  refine (PMF.toOuterMeasure_map_apply _ _ _).trans_le
    ((MeasureTheory.measure_mono fun x hx => ?_).trans_eq (PMF.toOuterMeasure_map_apply _ _ _).symm)
  obtain ⟨wt, hwt, e', he', hs, hsig, hask⟩ := hx
  exact ⟨wt.sig, congrArg (Option.map fun (w : RingSignature.RingWitOf (FIPSSignature p
    (concretePrimitivesKeyGen p))) => w.sig) hwt, e', he', hs, hsig, hask⟩

open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The guess of case S at the chain** (`w1GuessAvg_le` through `w1CanS_le_slotGuess`, the
averages over the side coins innermost, `ENNReal.tsum4_le_of_second`): the average of the guess
event at the canonical witness is at most `Q · kr · T · |BucketVec| / |MaskBox|`. -/
theorem w1GuessAvgC_le (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {w : ℕ}
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc (Sc) Λ E
          (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D Sc Λ E hb honest adm A)
            pks).alg a).width ≤ w)
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) (p₀ : Sc.Response b)
    (Ext : CausalExtractor P τ X₀f
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))) :
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
      ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (GlS ξ sc ω)) ≤
      Q * (kr * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p)) := by
  refine ENNReal.tsum4_le_of_second (PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32))
    (PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁))
    (PMF.uniformOfFintype (Xq → Y₁)) (fun (ξ : Fin n → (Bf).KeyCoins) => auxC ξ)
    (fun (ξ : Fin n → (Bf).KeyCoins) (sc : Fin Q → KFCoins (p := p) (T := T) kr D Y₁)
      (ω : Xq → Y₁) (a : (TPA ξ).Aux × Unit) => CanRc ξ sc ω a (GlS ξ sc ω)) _ fun ξ ω a => ?_
  refine (ENNReal.tsum_le_tsum fun sc =>
    mul_le_mul' le_rfl (w1CanS_le_slotGuess h A hw VE pub Sim Tp p₀ Ext ξ sc ω a)).trans ?_
  exact w1GuessAvg_le (Qs) (chk := chkN) sp h.hO h.hdisj ξ ω (.publicKey 0) w1PrfOf
    ((TPA ξ).alg a.1) ((TPA ξ).tracePreserving a.1)
    (inertOnDummy w1IsDummy ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp) p₀)
    (kqOf Mg nr b b) Ext


open Classical in
/-- **The union bound over the cases of the forger's win**, for an adversary `A` with a schedule
bound `hS`, at the view encoder `VE`, the simulator `Sim`, the preimages `Tp`, the response `p₀`
and the extractor `Ext` of `Sc`, and the default forgery `f₀` of the readout. It is the sum of one
term per case:
* collision: two queries collide on a message representative (`runLawIn_le_add_collision`);
* case U: the extracted signature is a fresh base signature, bounded by the success probability
  of the MU-EUF-NMA^corr forger `w1UForger` with `kfAbsorbSideRequests` requests
  (`w1CaseUAvgC_le`);
* case S≠: the extracted signature is a second signature at an honest commitment, bounded by the
  key-generation-form Module-SIS term `Lattice.keyGenMsisMultiWinProb` of the second run
  (`tsum_simProb_w1Goal_le`);
* case S=: the extracted signature repeats an honest signature, bounded by the guess term
  `Q · kr · T · |BucketVec| / |MaskBox|` (`w1GuessAvgC_le`).
`w1H3CaseError_eq` states the sum. -/
noncomputable def w1H3CaseError (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) :
    ℝ≥0∞ :=
  have hw := w1ChainAdv_width_le hS
  (12 * ((t + Q * (w1KFq N reps kr T + 2 * N +
      max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
          (honest) n Q
        chkN).q) + (N + Q) : ℕ) :
      ℝ≥0∞) ^ 2 *
    ((t + Q * (w1KFq N reps kr T + 2 * N +
      max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
          (honest) n Q
        chkN).q) + (N + Q) - 1 : ℕ) :
      ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
    2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
  ((muEufNmaProb UForgerC
        (kfAbsorbSideRequests S (P' + 2 * N) w PsimQ (kqOf Mg nr b b + Q * PsimQ)) +
      Q * (kr * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p))) +
    Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
      (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁)).bind fun sc =>
        (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
          (w1SecondRunLaw (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
            (dummyS := w1DummyS PSh adm n Q) (Qs) (kqOf Mg nr b b) pencC w1PrfOf
            (fun ξ _ _ => auxC ξ)
            (fun ξ sc ω a => AdvRc ξ sc ω a) PsimC Ext
            (fun ξ => w1Ok Pc O MO βmin tol (concreteEnc p) kr D bmc adm
              (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
        (w1MsisReadout sp h.hO ξ)))

open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- The terms of `w1H3CaseError`: collision + ((case U + case S=) + case S≠). -/
@[simp] theorem w1H3CaseError_eq (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) :
    w1H3CaseError (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim Tp p₀ Ext f₀ =
    have hw := w1ChainAdv_width_le hS
    (12 * ((t + Q * (w1KFq N reps kr T + 2 * N +
        max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
            (honest) n Q
          chkN).q) + (N + Q) : ℕ) :
        ℝ≥0∞) ^ 2 *
      ((t + Q * (w1KFq N reps kr T + 2 * N +
        max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
            (honest) n Q
          chkN).q) + (N + Q) - 1 : ℕ) :
        ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
      2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
    ((muEufNmaProb UForgerC
          (kfAbsorbSideRequests S (P' + 2 * N) w PsimQ (kqOf Mg nr b b + Q * PsimQ)) +
        Q * (kr * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p))) +
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
            (w1SecondRunLaw (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
              (dummyS := w1DummyS PSh adm n Q) (Qs) (kqOf Mg nr b b) pencC w1PrfOf
              (fun ξ _ _ => auxC ξ)
              (fun ξ sc ω a => AdvRc ξ sc ω a) PsimC Ext
              (fun ξ => w1Ok Pc O MO βmin tol (concreteEnc p) kr D bmc adm
                (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
          (w1MsisReadout sp h.hO ξ))) :=
  rfl

open Classical in
/-- **`w1H3CaseError` with the case-U term `u`** in place of the success probability of the
MU-EUF-NMA^corr forger `w1UForger` (`w1H3CaseError_eq_with`), so that a bound on that game can
replace it (`Applications/Ring/MLDSAW1NamedAssumptions.lean`). It sits here because the terms
are written with this file's local notations. -/
noncomputable def w1H3CaseErrorWith (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (_f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p))
    (u : ℝ≥0∞) : ℝ≥0∞ :=
  have hw := w1ChainAdv_width_le hS
  (12 * ((t + Q * (w1KFq N reps kr T + 2 * N +
      max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
          (honest) n Q
        chkN).q) + (N + Q) : ℕ) :
      ℝ≥0∞) ^ 2 *
    ((t + Q * (w1KFq N reps kr T + 2 * N +
      max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
          (honest) n Q
        chkN).q) + (N + Q) - 1 : ℕ) :
      ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
    2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
  ((u +
      Q * (kr * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p))) +
    Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
      (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁)).bind fun sc =>
        (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
          (w1SecondRunLaw (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
            (dummyS := w1DummyS PSh adm n Q) (Qs) (kqOf Mg nr b b) pencC w1PrfOf
            (fun ξ _ _ => auxC ξ)
            (fun ξ sc ω a => AdvRc ξ sc ω a) PsimC Ext
            (fun ξ => w1Ok Pc O MO βmin tol (concreteEnc p) kr D bmc adm
              (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
        (w1MsisReadout sp h.hO ξ)))

open Classical in
/-- **The case-U forger of `w1H3CaseError`**: the MU-EUF-NMA^corr forger `w1UForger` against the
signer with fresh masks. -/
noncomputable def w1H3UForger (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) :=
  have hw := w1ChainAdv_width_le hS
  UForgerC

open Classical in
/-- **The requests of the case-U game of `w1H3CaseError`.** -/
noncomputable def w1H3URequests (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) : ℕ :=
  kfAbsorbSideRequests S (P' + 2 * N) w PsimQ (kqOf Mg nr b b + Q * PsimQ)

open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **`w1H3CaseError` at its case-U term** (`w1H3CaseErrorWith`). -/
theorem w1H3CaseError_eq_with (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) :
    w1H3CaseError (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
        Tp p₀ Ext f₀ =
      w1H3CaseErrorWith (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
        Tp p₀ Ext f₀
        (muEufNmaProb (w1H3UForger (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
          Tp p₀ Ext f₀)
          (w1H3URequests (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
            Tp p₀ Ext f₀)) :=
  rfl

set_option quotPrecheck true
set_option hygiene true

open Classical in
/-- **The bound by case at the fresh program statements** (BKM06 Definition 7, at the concrete
primitives): for an adversary `A` against the converted
scheme `w1ConvConcrete` with the proof system `w1PS` of an spBCS argument `Sc`, the forgery
probability is at most the spBCS knowledge error of the empty ring
(`w1Concrete.insiderForgeProb_le_nonempty`), plus the hops to the key-free relay challenger
(`insiderForgeProb_le_w1C2`), plus the collision of message representatives
(`runLawIn_le_add_collision`), plus the averages of case U and of the guess, the Module-SIS term
and `trCollAt` (`tsum_simProb_w1Goal_le`), plus the simulation-extraction and zero-knowledge
errors. -/
private theorem w1ConvConcrete.insiderForgeProb_le_cases_aux
    [DecidableRel (w1Rel (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc PSh adm
      n Q)]
    (hp : p.isApproved) (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) Msg N)
      Sc.NIProof)
    {t w : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv (concretePrimitivesKeyGen p) O MO βmin tol (concreteEnc p) kr D bmc
          (Sc) Λ
        E (hb) (honest) adm chkN (w1ConvAdv O MO βmin tol kr D
            Sc Λ E hb honest
          adm A) pks).alg a).width ≤
        w)
    (VE : (Sc).ViewEncoder E (Qs)) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : (Sc).Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (honest) pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) (Vr) Ext St ε)
    (p₀ : (Sc).Response b) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (((Q * kr).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * kr : ℕ) * (2 ^ 256 :
        ℝ)⁻¹)) +
      Q * (√((kr * T : ℝ) * (n * commitPointAt Pc) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
        (kr * T : ℝ) * (n * commitPointAt Pc) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
      2 * √(t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
          ℝ) + Q : ℝ) *
        √((t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
            ℝ) + (1 + kr * T +
          max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * (2 * kr * T * (n * commitPointAt Pc)))) +
      Q * (((kr * T).choose 2 : ℝ) * (n * commitPointAt Pc))) +
      ((12 * ((t + Q * (w1KFq N reps kr T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
                (honest) n Q
              chkN).q) + (N + Q) : ℕ) :
            ℝ≥0∞) ^ 2 *
          ((t + Q * (w1KFq N reps kr T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp (Sc) Λ E (hb)
                (honest) n Q
              chkN).q) + (N + Q) - 1 : ℕ) :
            ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
          2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
(    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun f _ w
            => w1CaseU (bmsg := bmc) O sp ω f w)) +
      (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, (auxC ξ) a * CanRc ξ sc ω a (fun _ rs w
            => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧
          w1EntrySig e' = some w.sig ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) kr D bmc h.hO)
            (w1StmtPω Pc O MO βmin tol (concreteEnc p) kr D bmc sp) (w1ToR (Q := Q)) sc ω e')) +
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) kr D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
            (w1SecondRunLaw (rel := w1Rel Pc O MO βmin tol (concreteEnc p) kr D bmc PSh adm n Q)
              (dummyS := w1DummyS PSh adm n Q) (Qs) (kqOf Mg nr b b) pencC
                  w1PrfOf
              (fun ξ _ _ => auxC ξ)
              (fun ξ sc ω a => AdvRc ξ sc ω a) PsimC Ext
              (fun ξ => w1Ok Pc O MO βmin tol (concreteEnc p) kr D bmc adm
                (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
          (w1MsisReadout sp h.hO ξ)) +
      trCollAt Pc n +
      (Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
        ((Sc).niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
        (t + w * (2 * N) + Q * 1 + Q * 1) Q +
      ENNReal.ofReal ((Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q)))) := by
  exact (w1ConvConcrete.insiderForgeProb_le_backbone (Λ := Λ) (E := E) (hb := hb)
    (honest := honest) (Q := Q) hp hk h hQm c₀ A hw VE pub Sim Tp hvzk hrbr p₀).trans
    (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
      (w1KFChainAvg_le_cases (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) hp hk h hQm
        c₀ A hw VE pub Sim Tp hvzk hrbr p₀))))


/-! ### The bound at the hedged program statements -/

/-- **The hops to the key-free relay challenger** (`insiderForgeProb_le_w1C2`), for an adversary
with `t` queries and query width `w`. -/
noncomputable def w1H3HopError (t w : ℕ) : ℝ :=
  (((Q * kr).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * kr : ℕ) * (2 ^ 256 :
      ℝ)⁻¹)) +
    Q * (√((kr * T : ℝ) * (n * commitPointAt Pc) *
          (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
      (kr * T : ℝ) * (n * commitPointAt Pc) *
          (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
    2 * √(t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) :
        ℝ) + Q : ℝ) *
      √((t + w * ((2 * N + ((Sc).qVerifier (Qs) b b).kq : ℕ) : ℝ)
          + (1 + kr * T +
        max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
        (Q * (2 * kr * T * (n * commitPointAt Pc)))) +
    Q * (((kr * T).choose 2 : ℝ) * (n * commitPointAt Pc)))

omit [Nonempty Msg]
  [Nonempty (FIPSSignature p (concretePrimitivesKeyGen p))] [∀ j i, Nonempty ((P j).Challenge i)]
  [∀ j i, Fintype ((Sc.comp j).MessageWrite i)] [Inhabited Sc.NIProof] in
/-- The simulation-extraction error at the fresh program statements is that of `Sc`. -/
theorem w1SimExtF_eq {VE : Sc.ViewEncoder E Qs} {Pub : Type} {pub : X₀f → Pub}
    {Sim : CausalJointSimulator VE.MV Pub} {Tp : Sc.Preimages} {ε : ChIdx P τ → NNReal}
    {t w : ℕ} :
    (Sc).simExtractionError (kqOf Mg nr b b) (maxError ε)
        ((Sc).niJointSimulatorProg Λ (VE).toViewRead b
            (pub)
          (Sim) (Tp)).q
        (t + w * (2 * N) + Q * 1 + Q * 1) Q =
      Sc.simExtractionError (kqOf Mg nr b b) (maxError ε)
        (Sc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q (t + w * (2 * N) + 2 * Q) Q := by
  rw [show t + w * (2 * N) + Q * 1 + Q * 1 = t + w * (2 * N) + 2 * Q by ring]

omit [Nonempty Msg]
  [Nonempty (FIPSSignature p (concretePrimitivesKeyGen p))] [∀ j i, Nonempty ((P j).Challenge i)]
  [∀ j i, Fintype ((Sc.comp j).MessageWrite i)] [Inhabited Sc.NIProof] in
/-- The zero-knowledge error at the fresh program statements is that of `Sc`. -/
theorem w1ZkF_eq {δ : NNReal} {t w : ℕ} :
    (Sc).zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q =
      Sc.zkError δ (t + w * (2 * N) + 2 * Q) Q := by
  rw [show t + w * (2 * N) + Q * 1 + Q * 1 = t + w * (2 * N) + 2 * Q by ring]

/-- Regrouping the terms of the bound. -/
theorem _root_.GordieHowe.ENNReal.add_regroup7 (k h g x c s z : ℝ≥0∞) :
    k + (h + (g + (x + c + s + z))) = k + (h + (g + x + c + s + z)) := by
  simp only [add_assoc]

open Classical in
/-- **The unforgeability bound of the converted ML-DSA ring signature publishing `w₁`, by case**
(BKM06 Definition 7, at the concrete primitives): for an adversary `A` against the converted
scheme `w1ConvConcrete` with the proof system `w1PS` of an spBCS argument `Sc`, with a schedule
bound of width `w`, the forgery probability is at most the spBCS knowledge error of the empty ring
(`w1Concrete.insiderForgeProb_le_nonempty`), plus the hops to the key-free relay challenger
(`w1H3HopError`), plus the cases of the forger's win at their explicit terms (`w1H3CaseError`:
the collision term, case U as MU-EUF-NMA^corr of `w1UForger`, the guess of case S, case S≠ as
Module-SIS), plus `trCollAt` and the simulation-extraction and zero-knowledge errors of `Sc`. -/
@[headline]
theorem w1ConvConcrete.insiderForgeProb_le
    (hp : p.isApproved) (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim X₀f Sc.NIProof)
    {t : ℕ} (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P')
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmc adm) Vr Ext St ε)
    (p₀ : Sc.Response b)
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p)) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (w1H3HopError (O := O) (MO := MO) (βmin := βmin) (tol := tol) (kr := kr) (D := D)
          (sp := sp) (Sc := Sc) (Λ := Λ) (E := E) (hb := hb)
          (honest := honest) (adm := adm) (Qs := Qs) (n := n) (Q := Q) t w) +
        (w1H3CaseError (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
            Tp p₀ Ext f₀ +
          trCollAt (concretePrimitivesKeyGen p) n +
          Sc.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (Sc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q (t + w * (2 * N) + 2 * Q) Q +
          ENNReal.ofReal (Sc.zkError δ (t + w * (2 * N) + 2 * Q) Q))) := by
  have hc := w1ConvConcrete.insiderForgeProb_le_cases_aux (Λ := Λ) (E := E) (hb := hb)
    (honest := honest) (Q := Q) hp hk h hQm c₀ A (w1ChainAdv_width_le hS) VE pub Sim Tp hvzk hrbr
    p₀
  have hU := w1CaseUAvgC_le (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS
    (w1ChainAdv_width_le hS) VE pub Sim Tp p₀ Ext f₀
  have hG := w1GuessAvgC_le (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A
    (w1ChainAdv_width_le hS) VE pub Sim Tp p₀ Ext
  refine hc.trans (le_trans (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hU hG) le_rfl) le_rfl) le_rfl)
      le_rfl)))) (le_of_eq ?_))
  rw [ENNReal.add_regroup7]
  refine congrArg₂ (· + ·) rfl (congrArg₂ (· + ·) rfl (congrArg₂ (· + ·)
    (congrArg₂ (· + ·) ?_ (w1SimExtF_eq (Sc := Sc)))
    (congrArg ENNReal.ofReal (w1ZkF_eq (Sc := Sc)))))
  rw [w1H3CaseError_eq]


end GordieHowe.Ring.MLDSAW1
