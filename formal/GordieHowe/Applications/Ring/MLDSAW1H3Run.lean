-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseSplitRun
public import GordieHowe.Applications.Ring.MLDSAW1CaseSRun
public import GordieHowe.Applications.Ring.MLDSAW1TrColl

@[expose] public section

/-!
# The key-free goal averaged over the runs, split into its three cases

The forger's win at the goal `w1Goal` of the key-free chain at the ML-DSA ring publishing `w₁`
(`simProb_w1Goal_le`, `GordieHowe/Applications/Ring/MLDSAW1CaseSplitRun.lean`), averaged over
uniform users' seeds, side coins and base components and the adversaries' auxiliary inputs: the
seeds with a key-hash collision cost `trCollAt` (`tsum_le_add_trCollAt`), the second-signature
case is bounded by Module-SIS (`tsum_simProb_w1SecondSig_le`), and the canonical witness's case U
and the guess of a logged signing entry's signature remain as averages.

- `simProb_le_one`: a probability of the simulation of an adversary is at most one.
- `indicator_w1Goal_le`: at one seed tuple without a key-hash collision, the split into case U,
  the guess and the second signature.
- `tsum_simProb_w1Goal_le`: the bound.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Signature Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open RingSignature.KeyFree RingSignature.Insider
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

/-- **A probability of the simulation of an adversary is at most one** (`simLaw` is the outer
measure of `simPMF`). -/
theorem simProb_le_one {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] {B C : Type} (eq : BitStr I J ≃ B) {k t : ℕ}
    (A : Adv (Bits m) (BitStr I J) B C k t) (R : C → DB (Bits m) B → Prop) :
    simProb eq A R ≤ 1 := by
  rw [simProb, simLaw_eq_toOuterMeasure_simPMF]
  exact PMF.toOuterMeasure_apply_le_one _ _

attribute [local instance] concreteNTTRingOps

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ} {kh kN kS L e : ℕ}
  [NeZero (bucketCount p)] [Fintype Msg] [DecidableEq Msg] {Y Y₁ : Type} [AddGroup Y]
  [AddGroup Y₁] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁]
  [Nonempty Y₁] [Nonempty (MaskBox p)]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p (concretePrimitivesKeyGen p) Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg}
  {βmin : ℚ≥0} {tol : ℕ} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt (concretePrimitivesKeyGen p) RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase (concretePrimitivesKeyGen p) O Mo βmin tol
      (concreteEnc p) k D bmsg) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]
  {chk : RingSignature.RingStmt (freshBase (concretePrimitivesKeyGen p) O Mo βmin tol
    (concreteEnc p) k D bmsg) → Bool}
  {Frg : Type}
  {Stmt Wit : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt} [Inhabited Mc.NIProof]
  (sp : OracleSplit Y Y₁ (XOut kh e))

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Pc" => concretePrimitivesKeyGen p
local notation "Bf" => freshBase (concretePrimitivesKeyGen p) O Mo βmin tol (concreteEnc p) k D bmsg
local notation "Lf" => freshLoop (concretePrimitivesKeyGen p) O Mo βmin k D
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen p) RMsg N
local notation "PSh" => w1HPS sp Pc O Mo βmin tol (concreteEnc p) k D bmsg Mc Λ E hb honest chk
local notation "PSf" => (w1HPS sp Pc O Mo βmin tol (concreteEnc p) k D bmsg Mc Λ
  E hb honest chk)
local notation "Rq" => W1Rq Pc O Mo βmin tol (concreteEnc p) k D bmsg PSh adm n Q
local notation "MUR" => MURequest (SignOracle.none (RingSignature.BaseSigner.core Bf)) n

attribute [local instance] admDecF

set_option hygiene false
set_option quotPrecheck false

/-- The adversary of a run: `A₀ ξ sc ω a` with the side-mode key-free relay at the side coins
`sc` absorbed at the base component `ω`, its output's first part kept. -/
local notation "AdvR" ξ:max sc:max ω:max a:max =>
  ((((A₀ ξ sc ω a).absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
    (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) k D bmsg hO)
      (w1KFStmt Pc O Mo βmin tol (concreteEnc p) k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)

set_option quotPrecheck true
set_option hygiene true

set_option hygiene false
set_option quotPrecheck false

/-- The forger's win at the goal in the run of `AdvR ξ sc ω a`. -/
local notation "WinR" ξ:max sc:max ω:max a:max =>
  simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc ξ) (dummyS := dummyS) prf
      ξ Q (AdvR ξ sc ω a)) Psim Q kq)
    (forgerWinsKF (rel := rel) (enc := penc ξ) (dummyS := dummyS) prf ξ Q (AdvR ξ sc ω a) Psim Ext
      (fun _ w => w) (w1Goal Pc O Mo βmin tol (concreteEnc p) k D bmsg adm sp
        (fun j => (Bf).pk (ξ j)) ω))

/-- The canonical witness's goal `Gl` in the run of `AdvR ξ sc ω a`. -/
local notation "CanR" ξ:max sc:max ω:max a:max Gl:max =>
  simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc ξ) (dummyS := dummyS) prf
      ξ Q (AdvR ξ sc ω a)) Psim Q kq)
    (forgerCanonKF (rel := rel) (enc := penc ξ) (dummyS := dummyS) prf ξ Q (AdvR ξ sc ω a) Psim
      Ext (fun _ w => w) (w1Ok Pc O Mo βmin tol (concreteEnc p) k D bmsg adm
        (fun j => (Bf).pk (ξ j))) Gl)

set_option quotPrecheck true
set_option hygiene true

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The key-free goal at one seed tuple splits into its three cases**: without a key-hash
collision, the average of the forger's win is at most the averages of case U and of the guess,
plus the average of the second signature on the seeds with injective key hashes. -/
theorem indicator_w1Goal_le (hO : O.ReadsFst sp)
    {SC' : Type} [Fintype SC'] [DecidableEq SC'] (kq : ℕ)
    (penc : (Fin n → _root_.MLDSA.Bytes 32) → MUR ⊕ Rq → ProofQuery Stmt Wit)
    (prf : Frg → Option Mc.NIProof) (idle : MUR ⊕ Rq) (hidle : w1SignEntry idle = none)
    {Aux : (Fin n → _root_.MLDSA.Bytes 32) → (Fin Q → KFCoins (p := p) (T := T) k D Y₁) →
      (Xq → Y₁) → Type}
    (aux : ∀ ξ sc ω, PMF (Aux ξ sc ω))
    {shA₀ : ∀ ξ sc ω, Aux ξ sc ω → AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)}
    (A₀ : ∀ ξ sc ω (a : Aux ξ sc ω), AdaptiveIAlg (shA₀ ξ sc ω a) (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MUR ⊕ Rq)) (Mc.Response b) SC')
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))) (ξ : Fin n → _root_.MLDSA.Bytes 32) :
    {seeds : Fin n → _root_.MLDSA.Bytes 32 | ∃ i j, i ≠ j ∧
      pubTr Pc (keyGen Pc (seeds i)).1 = pubTr Pc (keyGen Pc (seeds j)).1 ∧
      (keyGen Pc (seeds i)).1 ≠ (keyGen Pc (seeds j)).1}ᶜ.indicator (fun ξ =>
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * WinR ξ sc ω a) ξ ≤
      (∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * CanR ξ sc ω a (fun f _ w
            => w1CaseU (bmsg := bmsg) O sp ω f w)) + (∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins
              (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * CanR ξ sc ω a (fun _ rs w
            => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧
          w1EntrySig e' = some w.sig ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) k D bmsg hO)
            (w1StmtPω Pc O Mo βmin tol (concreteEnc p) k D bmsg sp) (w1ToR (Q := Q)) sc ω e')) +
      {ξ : Fin n → _root_.MLDSA.Bytes 32 | ∀ i j,
        pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) → (Bf).pk (ξ i) = (Bf).pk (ξ
          j)}.indicator
        (fun ξ => (∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * CanR ξ sc ω a (fun f rs w
            => ∃ i σe, W1SecondSig sp hO ξ sc ω f rs w i σe))) ξ := by
  have key : ∀ ξ sc ω a, WinR ξ sc ω a ≤
      CanR ξ sc ω a (fun f _ w => w1CaseU (bmsg := bmsg) O sp ω f w) +
      CanR ξ sc ω a (fun _ rs w => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧
          w1EntrySig e' = some w.sig ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) k D bmsg hO)
            (w1StmtPω Pc O Mo βmin tol (concreteEnc p) k D bmsg sp) (w1ToR (Q := Q)) sc ω e') +
      CanR ξ sc ω a (fun f rs w => ∃ i σe, W1SecondSig sp hO ξ sc ω f rs w i σe) :=
    fun ξ sc ω a => simProb_w1Goal_le (Qs := Qs) (rel := rel) (penc := penc ξ)
      (dummyS := dummyS) sp hO ξ sc ω idle hidle prf (A₀ ξ sc ω a) Psim Ext kq
  by_cases hξ : ξ ∈ {seeds : Fin n → _root_.MLDSA.Bytes 32 | ∃ i j, i ≠ j ∧
      pubTr Pc (keyGen Pc (seeds i)).1 = pubTr Pc (keyGen Pc (seeds j)).1 ∧
      (keyGen Pc (seeds i)).1 ≠ (keyGen Pc (seeds j)).1}ᶜ
  · have hξ' : ξ ∈ {ξ : Fin n → _root_.MLDSA.Bytes 32 | ∀ i j,
        pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) → (Bf).pk (ξ i) = (Bf).pk (ξ j)} :=
      fun i j h => eq_of_pubTr_eq Pc hξ h
    -- TODO(unbundle-M4): `rw` times out here (presumably its closing `rfl` attempt comparing the
    -- two different `simProb` sums); `simp only` closes only reducible `rfl`s.
    -- `-proj`: keep `(w1BaseT …).core` folded, as `key` states it; reducing it to its structure
    -- literal makes `key`'s use below unfold `simProb` to match the two spellings.
    simp -proj only [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ']
    refine le_trans (ENNReal.tsum_le_tsum fun sc => mul_le_mul_of_nonneg_left
      (ENNReal.tsum_le_tsum fun ω => mul_le_mul_of_nonneg_left
        (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
          (key ξ sc ω a) zero_le) zero_le) zero_le) (le_of_eq ?_)
    simp -proj only [mul_add, ENNReal.tsum_add]
  · -- TODO(unbundle-M4): as above, `rw` times out here.
    exact le_of_eq_of_le (Set.indicator_of_notMem hξ _) zero_le

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The key-free goal averaged over the runs splits into its three cases**: for adversaries
`A₀ ξ sc ω a` with the side-mode key-free relay at the side coins `sc` absorbed at the base
component `ω` (an idle request that is not a signing entry, `hidle`), the average over uniform
seeds `ξ`, side coins and base components and the auxiliary inputs `a ∼ aux ξ sc ω` of the
forger's win at `w1Goal` in the extraction run of `seAlgKF` is at most the same average of the
canonical witness in case U, plus that of a logged signing entry's signature equal to the
canonical witness's, plus the Module-SIS win probability of the reduction `B₂` reading out the
second signatures (`tsum_simProb_w1SecondSig_le`), plus the key-hash collision probability
`trCollAt` of the `n` seeds, at an approved parameter set. -/
theorem tsum_simProb_w1Goal_le (hp : p.isApproved) (hO : O.ReadsFst sp)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (hmu : Function.Injective O.muPt)
    {SC' : Type} [Fintype SC'] [DecidableEq SC'] (kq : ℕ)
    (penc : (Fin n → _root_.MLDSA.Bytes 32) → MUR ⊕ Rq → ProofQuery Stmt Wit)
    (prf : Frg → Option Mc.NIProof) (idle : MUR ⊕ Rq) (hidle : w1SignEntry idle = none)
    {Aux : (Fin n → _root_.MLDSA.Bytes 32) → (Fin Q → KFCoins (p := p) (T := T) k D Y₁) →
      (Xq → Y₁) → Type}
    (aux : ∀ ξ sc ω, PMF (Aux ξ sc ω))
    {shA₀ : ∀ ξ sc ω, Aux ξ sc ω → AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)}
    (A₀ : ∀ ξ sc ω (a : Aux ξ sc ω), AdaptiveIAlg (shA₀ ξ sc ω a) (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MUR ⊕ Rq)) (Mc.Response b) SC')
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))) :
    (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * WinR ξ sc ω a) ≤
      (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * CanR ξ sc ω a (fun f _ w
            => w1CaseU (bmsg := bmsg) O sp ω f w)) +
      (∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * CanR ξ sc ω a (fun _ rs w
            => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧
          w1EntrySig e' = some w.sig ∧
          KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
            (w1KFFactors (T := T) Pc O sp βmin tol (concreteEnc p) k D bmsg hO)
            (w1StmtPω Pc O Mo βmin tol (concreteEnc p) k D bmsg sp) (w1ToR (Q := Q)) sc ω e')) +
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        (fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
            (w1SecondRunLaw (rel := rel) (dummyS := dummyS) Qs kq penc prf aux
              (fun ξ sc ω a => AdvR ξ sc ω a) Psim Ext
              (fun ξ => w1Ok Pc O Mo βmin tol (concreteEnc p) k D bmsg adm
                (fun j => (Bf).pk (ξ j))) ξ sc ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
          (w1MsisReadout sp hO ξ)) +
      trCollAt Pc n := by
  have hsplit := indicator_w1Goal_le (Qs := Qs) (rel := rel) (dummyS := dummyS) sp hO kq penc prf
    idle hidle aux A₀ Psim Ext
  have hf1 : ∀ ξ, (∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
      ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω * ∑' a, aux ξ sc ω a * WinR ξ sc ω a) ≤ 1 := by
    intro ξ
    refine le_trans (ENNReal.tsum_le_tsum fun sc => mul_le_mul_of_nonneg_left
      (ENNReal.tsum_le_tsum fun ω => mul_le_mul_of_nonneg_left
        (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
          (simProb_le_one _ _ _) zero_le) zero_le) zero_le) (le_of_eq ?_)
    simp -proj only [mul_one, PMF.tsum_coe]
  refine (tsum_le_add_trCollAt Pc n _ hf1).trans (add_le_add ?_ le_rfl)
  have hS := tsum_simProb_w1SecondSig_le (rel := rel) (dummyS := dummyS) sp hO hp hdisj hmu Qs
    kq penc prf aux (fun ξ sc ω a => AdvR ξ sc ω a) Psim Ext
    (fun ξ => w1Ok Pc O Mo βmin tol (concreteEnc p) k D bmsg adm (fun j => (Bf).pk (ξ j)))
  refine (ENNReal.tsum_le_tsum fun ξ => mul_le_mul_of_nonneg_left (hsplit ξ) zero_le).trans ?_
  simp -proj only [mul_add, ENNReal.tsum_add]
  exact add_le_add le_rfl hS
end GordieHowe.Ring.MLDSAW1
