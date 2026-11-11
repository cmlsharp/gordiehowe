-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1H3Assembly

@[expose] public section

/-!
# Unforgeability of the converted ML-DSA ring signatures publishing `w₁`

The insider unforgeability bounds (BKM06 Definition 7) of `w1ConvScheme44`, `w1ConvScheme65` and
`w1ConvScheme87`: `w1ConvConcrete.insiderForgeProb_le` at the parameter sets ML-DSA-44,
-65 and -87 (approved, `isApproved_mldsa44` …). The bound is the spBCS knowledge error of the
empty ring, the hops to the key-free relay challenger (`w1H3HopError`), the cases of the forger's
win (`w1H3CaseError`: the collision of message representatives, case U as the MU-EUF-NMA^corr
success probability of `w1UForger`, the guess of case S and case S≠ as Module-SIS), `trCollAt`,
and the simulation-extraction and zero-knowledge errors of the spBCS argument.

- `w1ConvScheme44.insiderForgeProb_le`, `w1ConvScheme65.insiderForgeProb_le`,
  `w1ConvScheme87.insiderForgeProb_le`.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree RingSignature.Insider
open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP GordieHowe.MLDSA.Regularity
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

section Conv44

local notation "Pm" => _root_.MLDSA.mldsa44

variable {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {I J Y₁ : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {sp : OracleSplit (BitStr I J) Y₁ (XOut kh e)}
  [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) (BitStr I J) Pm (concretePrimitivesKeyGen Pm) Msg N
    reps}
  {MO : MaskOracle (Bits (queryBits kh kN kS L)) (BitStr I J) Pm T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {kr D : ℕ} [NeZero D] [Nonempty Msg]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N) kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N)}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Pc" => concretePrimitivesKeyGen Pm
local notation "bmc" => (fun (_ : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N) (m : Msg) => m)
local notation "Lh" => hedgedLoop (concretePrimitivesKeyGen Pm) O MO βmin kr D
local notation "Lf" => freshLoop (concretePrimitivesKeyGen Pm) O MO βmin kr D
local notation "Bc" => w1ConcreteBase Pm O MO βmin tol kr D (RMsg := Msg) bmc
local notation "Bf" => freshBase (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D bmc
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N
local notation "PSc" => w1PS sp (concretePrimitivesKeyGen Pm) O βmin tol (concreteEnc Pm) Lh bmc Sc Λ
  E hb honest
local notation "PSn" => w1PSNonempty sp (concretePrimitivesKeyGen Pm) O βmin tol (concreteEnc Pm) Lh
  bmc Sc Λ E hb honest
local notation "chkN" => fun (x : RingSignature.RingStmt (freshBase (concretePrimitivesKeyGen Pm) O
  MO βmin tol (concreteEnc Pm) kr D bmc)) =>
  decide (Subtype.val (RingSignature.RingStmtOf.ring x) ≠ [])
local notation "PSh" => w1HPS sp (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D bmc
  (Sc) Λ E (hb) (honest) chkN
local notation "Sf" => freshScheme (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D
  bmc PSh adm
attribute [local instance] admDecF

variable [Inhabited Sc.NIProof]

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
ML-DSA-44 ring signature publishing `w₁`** (`w1ConvScheme44`;
`w1ConvConcrete.insiderForgeProb_le` at ML-DSA-44, `isApproved_mldsa44`): for an adversary
`A` with `t` queries, `Q` requests and a schedule bound of `S` slots, width `w` and `P'` post
batches, against the converted scheme with the proof system `w1PS` of an spBCS argument `Sc`, the
forgery probability is at most the spBCS knowledge error of the empty ring, plus the hops to the
key-free relay challenger (`w1H3HopError`), plus the cases of the forger's win (`w1H3CaseError`: the
collision of message representatives, case U as the MU-EUF-NMA^corr success probability of
`w1UForger`, the guess of case S, `Q · kr · T · |BucketVec| / |MaskBox|`, and case S≠ as the
Module-SIS term), plus `trCollAt` and the simulation-extraction and zero-knowledge errors of `Sc`.
-/
@[headline]
theorem w1ConvScheme44.insiderForgeProb_le
    (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim X₀f Sc.NIProof)
    {t : ℕ} (A : InsiderAdversary (w1ConvScheme44 (X := Xq) (Y := BitStr I J) (T := T) (Msg := Msg) (N := N)
        (reps := reps) O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P')
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen Pm) (concreteEnc Pm) bmc adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen Pm) (concreteEnc Pm) bmc adm) Vr Ext St ε)
    (p₀ : Sc.Response b)
    (f₀ : PubKey Pm (concretePrimitivesKeyGen Pm) × Msg × FIPSSignature Pm (concretePrimitivesKeyGen Pm)) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (w1H3HopError (O := O) (MO := MO) (βmin := βmin) (tol := tol) (kr := kr) (D := D)
          (sp := sp) (Sc := Sc) (Λ := Λ) (E := E) (hb := hb)
          (honest := honest) (adm := adm) (Qs := Qs) (n := n) (Q := Q) t w) +
        (w1H3CaseError (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
            Tp p₀ Ext f₀ +
          trCollAt (concretePrimitivesKeyGen Pm) n +
          Sc.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (Sc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q (t + w * (2 * N) + 2 * Q) Q +
          ENNReal.ofReal (Sc.zkError δ (t + w * (2 * N) + 2 * Q) Q))) :=
  w1ConvConcrete.insiderForgeProb_le isApproved_mldsa44 hk h hQm c₀ A hS VE pub Sim Tp hvzk hrbr p₀
    f₀

end Conv44

section Conv65

local notation "Pm" => _root_.MLDSA.mldsa65

variable {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {I J Y₁ : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {sp : OracleSplit (BitStr I J) Y₁ (XOut kh e)}
  [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) (BitStr I J) Pm (concretePrimitivesKeyGen Pm) Msg N
    reps}
  {MO : MaskOracle (Bits (queryBits kh kN kS L)) (BitStr I J) Pm T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {kr D : ℕ} [NeZero D] [Nonempty Msg]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N) kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N)}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Pc" => concretePrimitivesKeyGen Pm
local notation "bmc" => (fun (_ : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N) (m : Msg) => m)
local notation "Lh" => hedgedLoop (concretePrimitivesKeyGen Pm) O MO βmin kr D
local notation "Lf" => freshLoop (concretePrimitivesKeyGen Pm) O MO βmin kr D
local notation "Bc" => w1ConcreteBase Pm O MO βmin tol kr D (RMsg := Msg) bmc
local notation "Bf" => freshBase (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D bmc
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N
local notation "PSc" => w1PS sp (concretePrimitivesKeyGen Pm) O βmin tol (concreteEnc Pm) Lh bmc Sc Λ
  E hb honest
local notation "PSn" => w1PSNonempty sp (concretePrimitivesKeyGen Pm) O βmin tol (concreteEnc Pm) Lh
  bmc Sc Λ E hb honest
local notation "chkN" => fun (x : RingSignature.RingStmt (freshBase (concretePrimitivesKeyGen Pm) O
  MO βmin tol (concreteEnc Pm) kr D bmc)) =>
  decide (Subtype.val (RingSignature.RingStmtOf.ring x) ≠ [])
local notation "PSh" => w1HPS sp (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D bmc
  (Sc) Λ E (hb) (honest) chkN
local notation "Sf" => freshScheme (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D
  bmc PSh adm
attribute [local instance] admDecF

variable [Inhabited Sc.NIProof]

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
ML-DSA-65 ring signature publishing `w₁`** (`w1ConvScheme65`;
`w1ConvConcrete.insiderForgeProb_le` at ML-DSA-65, `isApproved_mldsa65`): for an adversary
`A` with `t` queries, `Q` requests and a schedule bound of `S` slots, width `w` and `P'` post
batches, against the converted scheme with the proof system `w1PS` of an spBCS argument `Sc`, the
forgery probability is at most the spBCS knowledge error of the empty ring, plus the hops to the
key-free relay challenger (`w1H3HopError`), plus the cases of the forger's win (`w1H3CaseError`: the
collision of message representatives, case U as the MU-EUF-NMA^corr success probability of
`w1UForger`, the guess of case S, `Q · kr · T · |BucketVec| / |MaskBox|`, and case S≠ as the
Module-SIS term), plus `trCollAt` and the simulation-extraction and zero-knowledge errors of `Sc`.
-/
@[headline]
theorem w1ConvScheme65.insiderForgeProb_le
    (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim X₀f Sc.NIProof)
    {t : ℕ} (A : InsiderAdversary (w1ConvScheme65 (X := Xq) (Y := BitStr I J) (T := T) (Msg := Msg) (N := N)
        (reps := reps) O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P')
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen Pm) (concreteEnc Pm) bmc adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen Pm) (concreteEnc Pm) bmc adm) Vr Ext St ε)
    (p₀ : Sc.Response b)
    (f₀ : PubKey Pm (concretePrimitivesKeyGen Pm) × Msg × FIPSSignature Pm (concretePrimitivesKeyGen Pm)) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (w1H3HopError (O := O) (MO := MO) (βmin := βmin) (tol := tol) (kr := kr) (D := D)
          (sp := sp) (Sc := Sc) (Λ := Λ) (E := E) (hb := hb)
          (honest := honest) (adm := adm) (Qs := Qs) (n := n) (Q := Q) t w) +
        (w1H3CaseError (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
            Tp p₀ Ext f₀ +
          trCollAt (concretePrimitivesKeyGen Pm) n +
          Sc.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (Sc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q (t + w * (2 * N) + 2 * Q) Q +
          ENNReal.ofReal (Sc.zkError δ (t + w * (2 * N) + 2 * Q) Q))) :=
  w1ConvConcrete.insiderForgeProb_le isApproved_mldsa65 hk h hQm c₀ A hS VE pub Sim Tp hvzk hrbr p₀
    f₀

end Conv65

section Conv87

local notation "Pm" => _root_.MLDSA.mldsa87

variable {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {I J Y₁ : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {sp : OracleSplit (BitStr I J) Y₁ (XOut kh e)}
  [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) (BitStr I J) Pm (concretePrimitivesKeyGen Pm) Msg N
    reps}
  {MO : MaskOracle (Bits (queryBits kh kN kS L)) (BitStr I J) Pm T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {kr D : ℕ} [NeZero D] [Nonempty Msg]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N) kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N)}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Pc" => concretePrimitivesKeyGen Pm
local notation "bmc" => (fun (_ : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N) (m : Msg) => m)
local notation "Lh" => hedgedLoop (concretePrimitivesKeyGen Pm) O MO βmin kr D
local notation "Lf" => freshLoop (concretePrimitivesKeyGen Pm) O MO βmin kr D
local notation "Bc" => w1ConcreteBase Pm O MO βmin tol kr D (RMsg := Msg) bmc
local notation "Bf" => freshBase (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D bmc
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen Pm) Msg N
local notation "PSc" => w1PS sp (concretePrimitivesKeyGen Pm) O βmin tol (concreteEnc Pm) Lh bmc Sc Λ
  E hb honest
local notation "PSn" => w1PSNonempty sp (concretePrimitivesKeyGen Pm) O βmin tol (concreteEnc Pm) Lh
  bmc Sc Λ E hb honest
local notation "chkN" => fun (x : RingSignature.RingStmt (freshBase (concretePrimitivesKeyGen Pm) O
  MO βmin tol (concreteEnc Pm) kr D bmc)) =>
  decide (Subtype.val (RingSignature.RingStmtOf.ring x) ≠ [])
local notation "PSh" => w1HPS sp (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D bmc
  (Sc) Λ E (hb) (honest) chkN
local notation "Sf" => freshScheme (concretePrimitivesKeyGen Pm) O MO βmin tol (concreteEnc Pm) kr D
  bmc PSh adm
attribute [local instance] admDecF

variable [Inhabited Sc.NIProof]

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
ML-DSA-87 ring signature publishing `w₁`** (`w1ConvScheme87`;
`w1ConvConcrete.insiderForgeProb_le` at ML-DSA-87, `isApproved_mldsa87`): for an adversary
`A` with `t` queries, `Q` requests and a schedule bound of `S` slots, width `w` and `P'` post
batches, against the converted scheme with the proof system `w1PS` of an spBCS argument `Sc`, the
forgery probability is at most the spBCS knowledge error of the empty ring, plus the hops to the
key-free relay challenger (`w1H3HopError`), plus the cases of the forger's win (`w1H3CaseError`: the
collision of message representatives, case U as the MU-EUF-NMA^corr success probability of
`w1UForger`, the guess of case S, `Q · kr · T · |BucketVec| / |MaskBox|`, and case S≠ as the
Module-SIS term), plus `trCollAt` and the simulation-extraction and zero-knowledge errors of `Sc`.
-/
@[headline]
theorem w1ConvScheme87.insiderForgeProb_le
    (hk : 0 < kh) (h : W1OracleFacts O MO sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt)
    (c₀ : Claim X₀f Sc.NIProof)
    {t : ℕ} (A : InsiderAdversary (w1ConvScheme87 (X := Xq) (Y := BitStr I J) (T := T) (Msg := Msg) (N := N)
        (reps := reps) O MO βmin tol kr D PSc adm) n
      (OracleView.queriesOnly Xq (BitStr I J)) t) {S w P' : ℕ}
    (hS : GameAdversary.ScheduleLE A S w P')
    (VE : Sc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Sc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel (concretePrimitivesKeyGen Pm) (concreteEnc Pm) bmc adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen Pm) (concreteEnc Pm) bmc adm) Vr Ext St ε)
    (p₀ : Sc.Response b)
    (f₀ : PubKey Pm (concretePrimitivesKeyGen Pm) × Msg × FIPSSignature Pm (concretePrimitivesKeyGen Pm)) :
    insiderForgeProb A Q ≤
      knowledgeError kh e (kqOf Mg nr b b)
          (t + Q * ((Bc).qPub + (PSc).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) +
      (ENNReal.ofReal (w1H3HopError (O := O) (MO := MO) (βmin := βmin) (tol := tol) (kr := kr) (D := D)
          (sp := sp) (Sc := Sc) (Λ := Λ) (E := E) (hb := hb)
          (honest := honest) (adm := adm) (Qs := Qs) (n := n) (Q := Q) t w) +
        (w1H3CaseError (Λ := Λ) (E := E) (hb := hb) (honest := honest) (Q := Q) h A hS VE pub Sim
            Tp p₀ Ext f₀ +
          trCollAt (concretePrimitivesKeyGen Pm) n +
          Sc.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (Sc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q (t + w * (2 * N) + 2 * Q) Q +
          ENNReal.ofReal (Sc.zkError δ (t + w * (2 * N) + 2 * Q) Q))) :=
  w1ConvConcrete.insiderForgeProb_le isApproved_mldsa87 hk h hQm c₀ A hS VE pub Sim Tp hvzk hrbr p₀
    f₀

end Conv87

end GordieHowe.Ring.MLDSAW1
