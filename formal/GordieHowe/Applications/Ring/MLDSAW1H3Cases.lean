-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeCanonSide
public import GordieHowe.Applications.Ring.MLDSAW1CaseU
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeRoute2
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeChainW1
public import GordieHowe.Applications.Ring.MLDSAW1SlotLaws

@[expose] public section

/-!
# The cases of a key-free forgery of the ML-DSA ring publishing `w₁`, bounded

The case bounds of the key-free chain at the ML-DSA ring publishing `w₁`, for the assembly of the
unforgeability bound (`GordieHowe/Applications/Ring/MLDSAW1H3Assembly.lean`).

- `w1UAvg_le`: case U, a forgery whose member's listed hash is the hash at the base component, at
  most the success probability of the key-free forger in MU-EUF-NMA^corr
  (`RingSignature.KeyFree.kfAbsorbSide_le_muEufNmaProb` at the relation `w1Rel`, the test `w1Ok`,
  the goal `w1CaseU` and the readout `w1Readout`).
- `w1GuessAvg_le`: the guess of case S, averaged over the side coins, at most
  `Q · k · T · |BucketVec| / |MaskBox|` (`slotLaws_kfExtractionLaw` at the relation `w1Rel`, the
  encoding `w1Enc`, the dummy statement `w1DummyS` and a simulator reading only the program
  statement).
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree RingSignature.Insider
open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

section CaseU

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  (sp : OracleSplit Y Y₁ (XOut kh e)) {prims : Primitives p}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  [Nonempty RMsg] [Nonempty (BucketVec p)] [Nonempty (FIPSSignature p prims)]
  {TPS : PSTypes}
  {PS : ProofSystem (Bits (queryBits kh kN kS L)) Y
    (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg))
    (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N) kh kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool} (Qs : ∀ x, Mc.IOPQueries Vr x)
  [Inhabited Mc.NIProof] {SC' : Type} [Fintype SC'] [DecidableEq SC']

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt prims RMsg N
local notation "Rq" => W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q
local notation "MUR" => MURequest (SignOracle.none Bf) n
local notation "Frg" => KeyRing (PubKey p prims) N × RMsg × (BucketVec p × Mc.Response b)

attribute [local instance] admDecF

/-- **The adversary of case U's extraction run** at the key coins `keys`, the side coins `sc`, the
base component `ω` and the auxiliary input `a`: `𝒜` at `a` with the relay `G … sc ω` absorbed,
restricted at `ω`, its output's table of assignments dropped.

Running time: that of `AdaptiveIAlg.absorbAssign` (its paragraph) at `𝒜` and `G`, with the
restriction (`AdaptiveIAlg.restrictAt`) at `ω`. This running time is argued here, not proved in
Lean. -/
noncomputable abbrev w1AbsAdv {SC : Type} {t : ℕ}
    -- TODO(binder-pass): the queries' `Nonempty` instance as a binder, so the body keeps it as a
    -- variable (inline, it is abstracted into an auxiliary lemma of the definition).
    [iXq : Nonempty Xq]
    (𝒜 : (Fin n → (Bf).PK) → QueryBoundedAdversary Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm)
      (Frg × X₀f) t)
    (G : (Fin n → (Bf).PK) → (Fin Q → SC) → (Xq → Y₁) →
      AssignRelay Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm) (MUR ⊕ Rq)
        (MUResponse Bf ⊕ Mc.Response b) Xq Y₁)
    (keys : Fin n → (Bf).KeyCoins) (sc : Fin Q → SC) (ω : Xq → Y₁)
    (a : (𝒜 fun i => (Bf).pk (keys i)).Aux × Unit) :=
  ((((𝒜 _).alg a.1).absorbAssign (G (fun i => (Bf).pk (keys i)) sc ω) Q).restrictAt sp
    ω).mapOut Prod.fst

open Classical in
/-- **The simulation-extraction adversary of case U's extraction run** (`seAlgKF` at the relation
`w1Rel`, the encoding `w1Enc` of the public keys of `keys`, the dummy statement `w1DummyS` and the
proofs `w1PrfOf`) of `w1AbsAdv`. Statements pass this name to `extAdv`, so the run's depth index
holds one constant, not the adversary's term.

Running time: that of `seAlgKF` (its paragraph) at `w1AbsAdv`. This running time is argued here,
not proved in Lean. -/
noncomputable abbrev w1ExtAdvF {SC : Type} {t : ℕ}
    -- TODO(binder-pass): the queries' `Nonempty` instance as a binder, so the body keeps it as a
    -- variable (inline, it is abstracted into an auxiliary lemma of the definition).
    [iXq : Nonempty Xq]
    (𝒜 : (Fin n → (Bf).PK) → QueryBoundedAdversary Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm)
      (Frg × X₀f) t)
    (G : (Fin n → (Bf).PK) → (Fin Q → SC) → (Xq → Y₁) →
      AssignRelay Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm) (MUR ⊕ Rq)
        (MUResponse Bf ⊕ Mc.Response b) Xq Y₁)
    (keys : Fin n → (Bf).KeyCoins) (sc : Fin Q → SC) (ω : Xq → Y₁)
    (a : (𝒜 fun i => (Bf).pk (keys i)).Aux × Unit) :=
  seAlgKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (enc := w1Enc (PS := PS) (adm := adm) (Q := Q) fun i => (Bf).pk (keys i))
    (dummyS := w1DummyS PS adm n Q) w1PrfOf keys Q (w1AbsAdv sp 𝒜 G keys sc ω a)

open Classical in
/-- **The MU-EUF-NMA^corr forger of case U** (`kfCanonSideForger` at the relation `w1Rel`, the
encoding `w1Enc`, the dummy statement `w1DummyS` and the proofs `w1PrfOf`): it runs the relayed
adversaries at zero (`AdaptiveIAlg.assignSideBase`) of the adversaries `𝒜 pks` at the auxiliary
input `kfAbsAux.fst p` and the relays `G pks (kfAbsAux.coins p)`, with their Kraus maps at each
base component and their side reads, and reads out the canonical witness passing `w1Ok` through
`w1Readout` at the default forgery `f₀`, within the query budget `kfAbsorbSideBudget`.

Running time: that of `kfCanonSideForger` (its paragraph) at these arguments: the adversary `𝒜`,
the relays `G`, the simulator `Psim`, the extractor `Ext`, one evaluation of `w1Ok`'s test for the
canonical witness and one of `w1Readout`. This running time is argued here, not proved in Lean. -/
noncomputable def w1UForger {SC : Type} [Fintype SC] [Nonempty SC] {t : ℕ}
    -- TODO(binder-pass): the queries' `Nonempty` instance as a binder, so the body keeps it as a
    -- variable (inline, it is abstracted into an auxiliary lemma of the definition).
    [iXq : Nonempty Xq]
    (𝒜 : (Fin n → (Bf).PK) → QueryBoundedAdversary Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm)
      (Frg × X₀f) t)
    (G : (Fin n → (Bf).PK) → (Fin Q → SC) → (Xq → Y₁) →
      AssignRelay Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm) (MUR ⊕ Rq)
        (MUResponse Bf ⊕ Mc.Response b) Xq Y₁)
    (Psim : NARG.Simulator Xq (XOut kh e)
      (W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q × (MUR ⊕ Rq)) (Mc.Response b) SC')
    (kq : ℕ) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (f₀ : PubKey p prims × Msg × FIPSSignature p prims)
    {S P' w qS : ℕ} (hsl : ∀ pks a, ((𝒜 pks).alg a).slots ≤ S)
    (hpo : ∀ pks a, ((𝒜 pks).alg a).post ≤ P') (hwd : ∀ pks a, ((𝒜 pks).alg a).width ≤ w)
    (hG1 : ∀ pks sc, (G pks sc 0).qG = 1 ∧ (G pks sc 0).qP = 1 ∧ (G pks sc 0).qS = qS) :=
  kfCanonSideForger sp Qs (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (fun pks => w1Enc (PS := PS) (adm := adm) (Q := Q) pks) (w1DummyS PS adm n Q)
    (fun pks => kfAbsAux (𝒜 pks) SC Q)
    (fun pks => kfAbsAuxLaw (𝒜 pks) (PMF.uniformOfFintype (Fin Q → SC)))
    (fun pks p => AdaptiveIAlg.assignSideBase ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Q) w1PrfOf Psim Q kq
    (fun pks p => AdaptiveIAlg.assignSideSteps ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Q)
    (fun pks p => AdaptiveIAlg.sideSteps_assignSideBase ((𝒜 pks).alg (kfAbsAux.fst p).1)
      (G pks (kfAbsAux.coins p)) Q)
    Ext (fun _ w => w) (fun pks => w1Ok prims O Mo βmin tol enc k D bmsg adm pks)
    (w1Readout bmsg f₀) (kfAbsorbSideBudget S P' w Psim.q (kq + Q * Psim.q) qS) fun pks p =>
      ht_assignSideBase sp (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
        (fun pks => w1Enc (PS := PS) (adm := adm) (Q := Q) pks) (w1DummyS PS adm n Q)
        ((𝒜 pks).alg (kfAbsAux.fst p).1) (G pks (kfAbsAux.coins p)) Psim Q kq pks
        (hsl pks _) (hpo pks _) (hwd pks _) (hG1 pks (kfAbsAux.coins p))

open Classical in
/-- **Case U as MU-EUF-NMA^corr** (`kfAbsorbSide_le_muEufNmaProb` at the relation `w1Rel`, the
encoding `w1Enc`, the dummy statement `w1DummyS`, the proofs `w1PrfOf`, the test `w1Ok`, the goal
`w1CaseU` and the readout `w1Readout` at the default forgery `f₀`): for `t`-query adversaries `𝒜
pks` of the insider game with at most `S` slots, `P'` post batches and width `w`, and relays `G pks
sc ω` with one oracle read, one pad sub-slot and `qS` side reads whose relay at `ω` is the relay at
zero with side `ω` (`hG`), the average over the users' key coins, the side coins, a uniform base
component `ω` and the auxiliary input of case U at the canonical witness in the extraction run of
`𝒜` with `G` absorbed and restricted at `ω` is at most the success probability of the key-free
forger `w1UForger` in MU-EUF-NMA^corr with `kfAbsorbSideRequests` requests. A canonical
witness in case U reads out to a forgery that verifies at every oracle with base component `ω`
(`bverify_w1Readout`, the oracles reading only the base component, `hO`) under an uncorrupted user's
key (`honest_w1Readout`). -/
theorem w1UAvg_le (hO : O.ReadsFst sp) {SC : Type} [Fintype SC] [Nonempty SC] {t : ℕ}
    (𝒜 : (Fin n → (Bf).PK) → QueryBoundedAdversary Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm)
      (Frg × X₀f) t)
    (G : (Fin n → (Bf).PK) → (Fin Q → SC) → (Xq → Y₁) →
      AssignRelay Xq Y (Req Bf PSf adm n) (Resp Bf PSf adm) (MUR ⊕ Rq)
        (MUResponse Bf ⊕ Mc.Response b) Xq Y₁)
    (hG : ∀ pks sc ω, (G pks sc ω).relayOf Q = ((G pks sc 0).relayOf Q).withSide ω)
    (Psim : NARG.Simulator Xq (XOut kh e)
      (W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q × (MUR ⊕ Rq)) (Mc.Response b) SC')
    (kq : ℕ) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims)))
    (f₀ : PubKey p prims × Msg × FIPSSignature p prims)
    {S P' w qS : ℕ} (hsl : ∀ pks a, ((𝒜 pks).alg a).slots ≤ S)
    (hpo : ∀ pks a, ((𝒜 pks).alg a).post ≤ P') (hwd : ∀ pks a, ((𝒜 pks).alg a).width ≤ w)
    (hG1 : ∀ pks sc, (G pks sc 0).qG = 1 ∧ (G pks sc 0).qP = 1 ∧ (G pks sc 0).qS = qS) :
    ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
      ∑' sc, PMF.uniformOfFintype (Fin Q → SC) sc *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          ∑' a, ((𝒜 fun i => (Bf).pk (keys i)).aux.bind
              fun a => (PMF.pure ()).map fun s => (a, s)) a *
            simProb (outEquiv kh e) (extAdv Qs (w1ExtAdvF sp 𝒜 G keys sc ω a) Psim Q kq)
              (forgerCanonKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
                (enc := w1Enc (PS := PS) (adm := adm) (Q := Q) fun i => (Bf).pk (keys i))
                (dummyS := w1DummyS PS adm n Q) w1PrfOf keys Q
                (w1AbsAdv sp 𝒜 G keys sc ω a) Psim Ext (fun _ w => w)
                (w1Ok prims O Mo βmin tol enc k D bmsg adm fun j => (Bf).pk (keys j))
                (fun f _ w => w1CaseU (bmsg := bmsg) O sp ω f w)) ≤
      muEufNmaProb (w1UForger sp Qs 𝒜 G Psim kq Ext f₀ hsl hpo hwd hG1)
        (kfAbsorbSideRequests S P' w Psim.q (kq + Q * Psim.q)) := by
  delta w1UForger w1ExtAdvF w1AbsAdv
  exact kfAbsorbSide_le_muEufNmaProb sp Qs (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (fun pks => w1Enc (PS := PS) (adm := adm) (Q := Q) pks) (w1DummyS PS adm n Q) 𝒜 G hG
    w1PrfOf Psim kq Ext (fun _ w => w)
    (fun pks => w1Ok prims O Mo βmin tol enc k D bmsg adm pks)
    (fun ω f _ w => w1CaseU (bmsg := bmsg) O sp ω f w) (w1Readout bmsg f₀)
    (fun pks ω h f rs w hok hU => bverify_w1Readout sp hO ω h f₀ pks f rs w hok hU)
    (fun pks f rs w hok => honest_w1Readout f₀ pks f rs w hok) hsl hpo hwd hG1

end CaseU

section Guess

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
  [Nonempty RMsg] [Nonempty (BucketVec p)] [Nonempty (FIPSSignature p prims)]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N) kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  (Qs : ∀ x, Mc.IOPQueries Vr x) {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}
  (sp : OracleSplit Y Y₁ (XOut kh e)) [Inhabited Mc.NIProof]

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "X₀f" => W1ExpStmt prims RMsg N
local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "PSh" => w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk
local notation "PSf" => (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb
  honest chk)
local notation "Rq" => W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q

attribute [local instance] admDecF

open Classical in
/-- **The guess of case S, averaged over the side coins** (`slotLaws_kfExtractionLaw` at the
relation `w1Rel`, the encoding `w1Enc` of the public keys of `ξ`, the dummy statement `w1DummyS`
and the simulator `Psim₀` read through the program statement, `w1StmtX ∘ Prod.fst`): for a
trace-preserving adversary `A₀` with the key-free relay at the side coins `sc` absorbed at the base
component `ω`, the guess event `w1SlotGuess` of its extraction run has probability at most
`Q · k · T · |BucketVec| / |MaskBox|` on average over uniform side coins. The swap of a slot's
signatures keeps the statements of `w1Enc` (`w1Enc_stmt_proofSwG`) and the relation
(`w1Rel_proofSwG_iff`, the message-representative and challenge points disjoint, `hdisj`), and the
simulator does not see it (`prog_comap_w1MainSwG`). -/
theorem w1GuessAvg_le (hO : O.ReadsFst sp) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁) (i : MURequest (SignOracle.none Bf) n) {Frg : Type}
    (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (hA : A₀.TracePreserving) {SC' : Type} [Fintype SC'] [DecidableEq SC']
    (Psim₀ : NARG.Simulator Xq (XOut kh e) X₀f (Mc.Response b) SC') (kq : ℕ)
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) :
    ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
        ((simPMF (outEquiv kh e) (extAdv Qs
          (seAlgKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
            (enc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun j => (Bf).pk (ξ j))
            (dummyS := w1DummyS PSh adm n Q) prf ξ Q
            (((A₀.absorbAssign (Resp' := MUResponse Bf ⊕ Mc.Response b)
              (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
                (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
                (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
                (w1DummyR (PS := PSh) (Q := Q)) sc ω
                (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq)) Q).restrictAt sp
                  ω).mapOut Prod.fst))
          (Psim₀.comap (w1StmtX ∘ Prod.fst)) Q kq)).map
        (cast (natOutcome_eq_w1Outcome
          (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
          (penc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun j => (Bf).pk (ξ j))
          (dummyS := w1DummyS PSh adm n Q) sp hO ξ ω
          (Sum.inl i : MURequest (SignOracle.none Bf) n ⊕ Rq) prf A₀
          (Psim₀.comap (w1StmtX ∘ Prod.fst)) kq sc))).toOuterMeasure
            {o | w1SlotGuess sp hO ξ ω A₀ (Psim₀.comap (w1StmtX ∘ Prod.fst)) kq Ext sc o} ≤
      Q * (k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p)) :=
  -- The default request is the corruption of user `0` (`UnforgeRequest.instInhabitedOfNeZero`).
  slotLaws_kfExtractionLaw (Qs := Qs)
    (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
    (penc := w1Enc (PS := PSh) (adm := adm) (Q := Q) fun j => (Bf).pk (ξ j))
    (dummyS := w1DummyS PSh adm n Q) sp (fun _ _ _ h => by cases h) hO ξ ω i prf A₀ hA
    (Psim₀.comap (w1StmtX ∘ Prod.fst)) kq Ext
    (fun t₀ G swσ q => w1Enc_stmt_proofSwG sp _ t₀ G swσ q)
    (fun j sc₁ sc₂ r hj hpub q => w1Rel_proofSwG_iff sp hO hdisj _ sc₁ sc₂ ω r j hj hpub q)
    (fun t₀ G swσ x c => prog_comap_w1MainSwG sp Psim₀ t₀ G swσ x c)

end Guess

end GordieHowe.Ring.MLDSAW1
