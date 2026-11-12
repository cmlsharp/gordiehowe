-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1RingBindingHeadline
public import GordieHowe.Applications.Ring.MLDSAW1H3Assembly
public import GordieHowe.Applications.Ring.BaseSigners
public import GordieHowe.Applications.MLDSA.Assumptions

@[expose] public section

/-!
# The ML-DSA ring unforgeability results under the named assumptions with `t₀` published

The two unforgeability results of the ML-DSA ring publishing `w₁` bound the forgery probability by
a base game of ML-DSA with `t₀` published. Under the named assumptions of
`GordieHowe/Applications/MLDSA/Assumptions.lean` (section "`t₀` published") that game is
at most `ε'`:

* `w1BindConcrete.insiderForgeProb_le_of_t0`: the ring-binding theorem
  (`w1BindConcrete.insiderForgeProb_le`) with the standard call game bounded by
  `MLDSAT0MUEufCmaWithin`;
* `w1ConvConcrete.insiderForgeProb_le_of_t0`: the converted scheme's theorem
  (`w1ConvConcrete.insiderForgeProb_le`) with its case-U term, MU-EUF-NMA^corr of the forger
  `w1H3UForger`, bounded by `MLDSAT0MUEufNma` (`w1H3CaseError_eq_with`, `w1H3CaseErrorWith_mono`).

The headline statements themselves are unchanged.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree RingSignature.Insider
open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP GordieHowe.MLDSA.Regularity
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec
open scoped ENNReal

attribute [local instance] concreteNTTRingOps

section RingBinding

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {T N reps : ℕ} {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg]
  {O : W1Oracles (Bits (queryBits k kN kS L)) Y p (concretePrimitivesKeyGen p)
    (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg) N reps}
  {MO : MaskOracle (Bits (queryBits k kN kS L)) Y p T
    (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg)}
  {βmin : ℚ≥0} {tol kr D : ℕ} [NeZero D]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) k kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt (concretePrimitivesKeyGen p) RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWit (w1ConcreteBase p O MO βmin tol kr D Prod.mk) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm]
  {n t : ℕ} [NeZero n]

/-- **Unforgeability of the ML-DSA ring signature publishing `w₁` under the named assumption with
`t₀` published**: `w1BindConcrete.insiderForgeProb_le` with the standard call game bounded by
`MLDSAT0MUEufCmaWithin` for a class `𝒜` containing the relayed forger. -/
theorem w1BindConcrete.insiderForgeProb_le_of_t0 (sp : OracleSplit Y Y₁ (XOut k e))
    (hp : p.isApproved)
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))}
    {St : CausalStateFn P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase p O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase p O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase p O MO βmin tol kr D Prod.mk).BSig)
    (A : InsiderAdversary (w1BindConcrete p O MO βmin tol kr D
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ)
    {𝒜 : Set (MUAdversary (w1ConcreteRejection p O MO βmin tol kr D Prod.mk).stdOracle (max n 2)
      (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) _)} {ε' : ℝ≥0∞}
    (hε' : MLDSAT0MUEufCmaWithin 𝒜 (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P')
      (kr * Q) ε')
    (hmem : relayMUAdversary (w1ConcreteRejection p O MO βmin tol kr D Prod.mk) kr
      (max n 2) hk
      0 (w1RingForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
      (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') ∈ 𝒜) :
    insiderForgeProb A Q ≤
      ε' +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase p O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  (w1BindConcrete.insiderForgeProb_le sp hp hk hO hM ⟨Ext, St, ε, hrbr⟩ c₀ f₀ A hS Q).trans
    (add_le_add (hε'.le_muEufProbWithin hmem) le_rfl)

end RingBinding

section Converted

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
attribute [local instance] admDecF

variable [Inhabited Sc.NIProof]

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **`w1H3CaseErrorWith` is monotone in the case-U term.** -/
theorem w1H3CaseErrorWith_mono (h : W1OracleFacts O MO sp) {t : ℕ}
    (A : InsiderAdversary (w1ConvConcrete p O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P') (VE : Sc.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀f → Pub) (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages)
    (p₀ : Sc.Response b) (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p))
    {u u' : ℝ≥0∞} (huu : u ≤ u') :
    w1H3CaseErrorWith (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
        Tp p₀ Ext f₀ u ≤
      w1H3CaseErrorWith (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
        Tp p₀ Ext f₀ u' := by
  dsimp only [w1H3CaseErrorWith]
  exact add_le_add le_rfl (add_le_add (add_le_add huu le_rfl) le_rfl)

/-- **The unforgeability bound of the converted ML-DSA ring signature publishing `w₁` under the
named assumption with `t₀` published**: `w1ConvConcrete.insiderForgeProb_le` with the case-U term,
MU-EUF-NMA^corr of the forger `w1H3UForger` against the signer with fresh masks, bounded by
`MLDSAT0MUEufNma` for a class `𝒜` containing that forger (`w1H3CaseError_eq_with`,
`w1H3CaseErrorWith_mono`). -/
theorem w1ConvConcrete.insiderForgeProb_le_of_t0
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
    (f₀ : PubKey p (concretePrimitivesKeyGen p) × Msg × FIPSSignature p (concretePrimitivesKeyGen p))
    {𝒜 : Set (MUAdversary (SignOracle.none (Bf).core) n (OracleView.queriesOnly Xq (BitStr I J)) _)}
    {ε' : ℝ≥0∞}
    (hε' : MLDSAT0MUEufNma 𝒜 (w1H3URequests (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub
        Sim Tp p₀ Ext f₀) ε')
    (hmem : w1H3UForger (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub
        Sim Tp p₀ Ext f₀ ∈ 𝒜) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (w1H3HopError (O := O) (MO := MO) (βmin := βmin) (tol := tol) (kr := kr) (D := D)
          (sp := sp) (Sc := Sc) (Λ := Λ) (E := E) (hb := hb)
          (honest := honest) (adm := adm) (Qs := Qs) (n := n) (Q := Q) t w) +
        (w1H3CaseErrorWith (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub
            Sim Tp p₀ Ext f₀ ε' +
          trCollAt (concretePrimitivesKeyGen p) n +
          Sc.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (Sc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q (t + w * (2 * N) + 2 * Q) Q +
          ENNReal.ofReal (Sc.zkError δ (t + w * (2 * N) + 2 * Q) Q))) := by
  refine (w1ConvConcrete.insiderForgeProb_le hp hk h ⟨hQm⟩ c₀ A hS pub ⟨VE, Sim, Tp, hvzk⟩
    ⟨Ext, St, ε, hrbr⟩ p₀ f₀).trans ?_
  rw [w1H3CaseError_eq_with]
  exact add_le_add le_rfl (add_le_add le_rfl (add_le_add (add_le_add (add_le_add
    (w1H3CaseErrorWith_mono h A hS VE pub Sim Tp p₀ Ext f₀ (hε'.le_muEufNmaProb hmem)) le_rfl)
    le_rfl) le_rfl))

end Converted

end GordieHowe.Ring.MLDSAW1
