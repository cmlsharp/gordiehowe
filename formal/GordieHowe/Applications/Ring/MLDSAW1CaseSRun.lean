-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseS
public import GordieHowe.Applications.Ring.KeyFreeCanon

@[expose] public section

/-!
# Case S with a second signature in the extraction runs, bounded by Module-SIS

The second-signature term of the key-free route at the ML-DSA ring publishing `w₁`
(`W1SecondSig`, `GordieHowe/Applications/Ring/MLDSAW1CaseS.lean`) at the canonical witness of
the extraction runs of `seAlgKF` (`forgerCanonKF`), averaged over the users' seeds without
key-hash collisions, the side coins, the base component and the adversaries' auxiliary inputs, is
at most the Module-SIS win probability of the reduction `B₂`
(`tsum_w1SecondSig_le_keyGenMsisMultiWinProb`, at the runs' readouts `kfCanonOut`).

- `w1SecondRunLaw`: the law of the readout of the extraction runs, the auxiliary input drawn.
- `tsum_simProb_w1SecondSig_le`: the bound.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Signature Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open RingSignature.KeyFree RingSignature.Insider
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ} {kh kN kS L e : ℕ}
  [NeZero (bucketCount p)] [Fintype Msg] [DecidableEq Msg] {Y : Type} [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Nonempty (MaskBox p)]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p (concretePrimitivesKeyGen p) Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg}
  {βmin : ℚ≥0} {tol : ℕ} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits (queryBits kh kN kS L)) Y (RingSignature.RingStmt (hedgedBase (concretePrimitivesKeyGen p) O Mo βmin
      tol (concreteEnc p) k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] {Frg : Type}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) kh kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : W1ExpStmt (concretePrimitivesKeyGen p) RMsg N → FullTr P τ → Bool}
  {Stmt Wit : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  {rel : Stmt → Wit → Prop} [DecidableRel rel] {dummyS : Stmt} [Inhabited M.NIProof]

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Pc" => concretePrimitivesKeyGen p
local notation "Bf" => freshBase (concretePrimitivesKeyGen p) O Mo βmin tol (concreteEnc p) k D bmsg
local notation "Lf" => freshLoop (concretePrimitivesKeyGen p) O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen p) RMsg N
local notation "Rq" => W1Rq Pc O Mo βmin tol (concreteEnc p) k D bmsg PS adm n Q
local notation "MUR" => MURequest (SignOracle.none (RingSignature.BaseSigner.core Bf)) n

attribute [local instance] admDecF

/-- **The law of the readout of the extraction runs**, at the users' seeds `ξ`, the side coins
`sc` and the base component `ω`: the auxiliary input `a ∼ aux ξ sc ω` drawn, the canonical
witness at the test `ok ξ`, the output and the first `Q` logged requests (`kfCanonOut`) of the
extraction run of `seAlgKF` for the adversary `A ξ sc ω a` (`simPMF`). -/
noncomputable def w1SecondRunLaw {SC' : Type} [Fintype SC'] [DecidableEq SC']
    (Qs : ∀ x, M.IOPQueries Vr x) (kq : ℕ) (penc : (Fin n → _root_.MLDSA.Bytes 32) → MUR ⊕ Rq →
      ProofQuery Stmt Wit) (prf : Frg → Option M.NIProof)
    {Aux : (Fin n → _root_.MLDSA.Bytes 32) → (Fin Q → KFCoins (p := p) (T := T) k D Y₁) → (Xq → Y₁) → Type}
    (aux : ∀ ξ sc ω, PMF (Aux ξ sc ω))
    {shA : ∀ ξ sc ω, Aux ξ sc ω → AlgShape Xq (XOut kh e) (MUR ⊕ Rq)
      (MUResponse (Bf).core ⊕ M.Response b)}
    (A : ∀ ξ sc ω (a : Aux ξ sc ω), AdaptiveIAlg (shA ξ sc ω a) (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MUR ⊕ Rq)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (ok : (Fin n → _root_.MLDSA.Bytes 32) → Frg × X₀f → List (MUR ⊕ Rq) → RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)) → Prop)
    (ξ : Fin n → _root_.MLDSA.Bytes 32) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁) :
    PMF (Option (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) × (Frg × X₀f) × List (MUR ⊕ Rq)) :=
  (aux ξ sc ω).bind fun a =>
    (simPMF (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc ξ) (dummyS := dummyS)
        prf ξ Q (A ξ sc ω a)) Psim Q kq)).map fun x =>
      kfCanonOut (rel := rel) (enc := penc ξ) (dummyS := dummyS) prf ξ Q (A ξ sc ω a) Psim Ext
        (fun _ w => w) (ok ξ) x.1.out x.2

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Case S with a second signature in the extraction runs is bounded by Module-SIS**: the
average over uniform seeds `ξ` with the keys of equal key hashes equal, uniform side coins `sc`,
uniform base components `ω` and auxiliary inputs `a ∼ aux ξ sc ω`, of the probability that the
canonical witness of the extraction run for `A ξ sc ω a` is in case S with a second signature
(`W1SecondSig`), is at most the Module-SIS win probability of the reduction reading out
`w1MsisReadout` from the joint law of the runs' readouts (`w1SecondRunLaw`), at an approved
parameter set. -/
theorem tsum_simProb_w1SecondSig_le (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hp : p.isApproved) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (hmu : Function.Injective O.muPt)
    {SC' : Type} [Fintype SC'] [DecidableEq SC']
    (Qs : ∀ x, M.IOPQueries Vr x) (kq : ℕ) (penc : (Fin n → _root_.MLDSA.Bytes 32) → MUR ⊕ Rq →
      ProofQuery Stmt Wit) (prf : Frg → Option M.NIProof)
    {Aux : (Fin n → _root_.MLDSA.Bytes 32) → (Fin Q → KFCoins (p := p) (T := T) k D Y₁) → (Xq → Y₁) → Type}
    (aux : ∀ ξ sc ω, PMF (Aux ξ sc ω))
    {shA : ∀ ξ sc ω, Aux ξ sc ω → AlgShape Xq (XOut kh e) (MUR ⊕ Rq)
      (MUResponse (Bf).core ⊕ M.Response b)}
    (A : ∀ ξ sc ω (a : Aux ξ sc ω), AdaptiveIAlg (shA ξ sc ω a) (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MUR ⊕ Rq)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (ok : (Fin n → _root_.MLDSA.Bytes 32) → Frg × X₀f → List (MUR ⊕ Rq) → RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)) → Prop) :
    ∑' ξ, PMF.uniformOfFintype (Fin n → _root_.MLDSA.Bytes 32) ξ *
        {ξ : Fin n → _root_.MLDSA.Bytes 32 | ∀ i j, pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) →
          (Bf).pk (ξ i) = (Bf).pk (ξ j)}.indicator (fun ξ =>
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
            ∑' a, aux ξ sc ω a *
              simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc ξ)
                  (dummyS := dummyS) prf ξ Q (A ξ sc ω a)) Psim Q kq)
                (forgerCanonKF (rel := rel) (enc := penc ξ) (dummyS := dummyS) prf ξ Q
                  (A ξ sc ω a) Psim Ext (fun _ w => w) (ok ξ)
                  (fun f rs w => ∃ i σe, W1SecondSig sp hO ξ sc ω f rs w i σe))) ξ ≤
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (Xq → Y₁)).bind fun ω =>
            (w1SecondRunLaw (rel := rel) (dummyS := dummyS) Qs kq penc prf aux A Psim Ext ok ξ sc
              ω).map fun o => (o.1, sc, ω, o.2.1, o.2.2)).map
          (w1MsisReadout sp hO ξ) := by
  have h := tsum_w1SecondSig_le_keyGenMsisMultiWinProb (X := Xq) sp hO hp hdisj hmu
    (aux := fun _ _ _ => PMF.pure ())
    (fun ξ sc ω _ => w1SecondRunLaw (rel := rel) (dummyS := dummyS) Qs kq penc prf aux A Psim Ext
      ok ξ sc ω) id
  simp only [PMF.pure_bind, id] at h
  refine le_trans (le_of_eq ?_) h
  refine tsum_congr fun ξ => congrArg _ ?_
  unfold Set.indicator
  split_ifs
  · refine tsum_congr fun sc => congrArg _ (tsum_congr fun ω => congrArg _ ?_)
    rw [tsum_eq_single () fun a ha => absurd (Subsingleton.elim a ()) ha, PMF.pure_apply_self,
      one_mul, w1SecondRunLaw, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun a => congrArg _ ?_
    refine (simProb_forgerCanonKF_eq (rel := rel) (enc := penc ξ) (dummyS := dummyS) Qs prf ξ Q
      kq (A ξ sc ω a) Psim Ext (fun _ w => w) (ok ξ) _).trans ?_
    congr 1
    ext o
    exact ⟨fun ⟨w, hw, i, σe, h⟩ => ⟨w, i, σe, hw, h⟩, fun ⟨w, i, σe, hw, h⟩ => ⟨w, hw, i, σe, h⟩⟩
  · rfl

end GordieHowe.Ring.MLDSAW1
