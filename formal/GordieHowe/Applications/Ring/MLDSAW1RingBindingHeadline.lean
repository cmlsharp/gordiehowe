-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplitHeadline
public import GordieHowe.Applications.Ring.RingForgerSplitKeyReuseHeadline
public import GordieHowe.Applications.Ring.MLDSAW1Forge
public import GordieHowe.Applications.Ring.MLDSAW1Lift
public import GordieHowe.Applications.Ring.MLDSAW1ReadsBase

@[expose] public section

/-!
# Unforgeability of the ML-DSA ring signature publishing `w₁` from the standard call game

The split reduction (`insiderForgeProb_le_muEufProbWithin_split`,
`GordieHowe/Applications/Ring/RingForgerSplitHeadline.lean`, and its key-reuse form
`keyReuseForgeProb_le_muEufProbWithin_split`) at the ML-DSA ring publishing `w₁`: the concrete base
signer with the base message `(R, m)` (`bindsRing_w1BaseSigner_pair`), which reads only the base
component of the split oracle (`readsOnly_w1Base`, `readsStdOnly_w1Base`), the proof system `w1PS`
compiled at each base component (`compiledBySplit_spbcsSplitProofSystem`, `claim_w1PS`), the
knowledge bound of the spBCS argument for the fixed relation `w1ExpRel` (`SPBCS.knowledgeBound`),
whose witnesses are witnesses of the ring relation (`ringRel_of_w1PS`), and the program statement of
a forgery (`w1ForgeStmtProg`). Then the multi-user game of the ring-aware (or key-reuse) signing
oracle is bounded by that of the standard FIPS 204 call oracle
(`muEufProbWithin_w1ConcreteBase_le_relay`,
`GordieHowe/Applications/Ring/MLDSAW1Lift.lean`).

- `w1RingPS`, `w1RingQ'`, `w1RingForger`, `w1RingStdForger`: the proof system, the number of
  requests and queries, and the multi-user forgers.
- `w1BindConcrete.insiderForgeProb_le`, `w1BindConcrete.keyReuseForgeProb_le`: the bounds at an approved
  parameter set; `w1BindScheme44.insiderForgeProb_le`, `…65_le`, `…87_le` and the key-reuse forms:
  at ML-DSA-44, ML-DSA-65 and ML-DSA-87.

The multi-user forger plays the adversary embedded into `max n 2` users (`splitMUForger`, see
`insiderForgeProb_le_muEufProbWithin_split`), and the multi-user game runs at the whole oracle
`Y`, not at the base component `Y₁`.

The standard call game is the multi-user game (MU-EUF-CMA^corr) of FIPS 204 with public keys that
include `t₀` (FIPS 204 §6.1: `t₀` "need not be regarded as secret") and the signing oracle hedged
Algorithm 7 with its loop capped at `T` attempts (FIPS 204 §6.2 and Appendix C).

The hypotheses `hrbr` (causal round-by-round knowledge soundness for `w1ExpRel`) and `hb` (the
format bounds of the spBCS compilation) are obligations of the proof system: the tree has no
compiled IOP for `w1ExpRel`, and the theorems hold for every IOP meeting them. `hrbr` is met by an
IOP that accepts honest witnesses: the one-message IOP in which the prover sends the witness and
the verifier decides `w1ExpRel` (`causalRBRKnowledgeSound_oneMsg` with error `0`,
`oneMsgVerifier_oneMsgTr`, at the decidability instance `instDecidablePredMemW1ExpRel`); it is
also met by the verifier rejecting every transcript (`causalRBRKnowledgeSound_reject`). The other
hypotheses are satisfiable: decodings reading only the base component
(`W1Oracles.readsFst_viaBase`, `MaskOracle.readsFst_viaBase`) and the schedule bound
(`RingSignature.GameAdversary.exists_scheduleLE`).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Signature Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec
open scoped ENNReal

attribute [local instance] concreteNTTRingOps

section Concrete

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
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (w1ConcreteBase p O MO βmin tol kr D Prod.mk) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm]
  {n t : ℕ} [NeZero n]

variable (O MO βmin tol kr D Sc Λ E hb honest) in
/-- **The proof system of the ring at the concrete primitives** (`w1PS` at the hedged loop of the
concrete base signer and the base message `(R, m)`). -/
noncomputable abbrev w1RingPS (sp : OracleSplit Y Y₁ (XOut k e)) :
    ProofSystem (Bits (queryBits k kN kS L)) Y (RingSignature.RingStmt (w1ConcreteBase p O MO βmin tol kr D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))
      (spbcsPST Sc b R) :=
  w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
    (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) Prod.mk Sc Λ E hb honest

variable (O MO βmin tol kr D Sc Λ E hb honest) in
/-- **The requests and queries of the ring's multi-user forger** (`splitQ'` at the compiled
verifier `Sc.qVerifier Qs b b`, the program statement's `2N` queries and relays of length
`1 + qPub + PS.q`), for an adversary with `Q` requests and the schedule bound `S`, `w`, `P'`. -/
noncomputable abbrev w1RingQ' (sp : OracleSplit Y Y₁ (XOut k e)) (Q S w P' : ℕ) : ℕ :=
  splitQ' (Sc.qVerifier Qs b b) Q (2 * N) S w P'
    (1 + ((w1ConcreteBase p O MO βmin tol kr D Prod.mk).qPub +
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q))

variable (O MO βmin tol kr D Sc Λ E hb honest adm) in
/-- **The multi-user forger of the ring** (`splitForger` at the base signer, the proof system
`w1RingPS`, the program statement of a forgery `w1ForgeStmtProg`, the claims `w1Claim`, the
relation `w1ExpRel` and the database extractor of the knowledge bound), with `w1RingQ'` requests
and queries. -/
noncomputable abbrev w1RingForger (sp : OracleSplit Y Y₁ (XOut k e))
    (Ext : CausalExtractor P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase p O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase p O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase p O MO βmin tol kr D Prod.mk).BSig)
    (A : InsiderAdversary (ofBase (w1ConcreteBase p O MO βmin tol kr D Prod.mk)
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    MUAdversary (SignOracle.ring (w1ConcreteBase p O MO βmin tol kr D Prod.mk)) (max n 2)
      (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y)
      (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') :=
  splitMUForger sp (w1ConcreteBase p O MO βmin tol kr D Prod.mk)
    (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm (V := Sc.qVerifier Qs b b)
    (rel := w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) Prod.mk adm)
    (ext := Sc.dbExtractBits Ext)
    (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O Prod.mk Sc) (2 * N)
    (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O Prod.mk Sc) A hS Q
    (w1Claim (concretePrimitivesKeyGen p) Sc) c₀ f₀

/-- **Unforgeability of the ML-DSA ring signature publishing `w₁` (BKM06 Definition 7) from the
standard call game** at an approved parameter set (`insiderForgeProb_le_muEufProbWithin_split`
at the base signer `w1ConcreteBase` with the base message `(R, m)` and the proof system
`w1RingPS`, then `muEufProbWithin_w1ConcreteBase_le_relay`): for decodings of the base signer's
oracles reading only the base component of the split `sp` (`hO`, `hM`), at most `kr` calls of
the FIPS 204 signer per signature (`hk`), a causal round-by-round knowledge-sound IOP for the
fixed relation `w1ExpRel` (`hrbr`), and an adversary with `n` users, `t` queries, `Q` requests and
the schedule bound `S`, `w`, `P'` (`hS`), the forgery probability is at most the probability that
the relayed multi-user forger wins the game of the standard call oracle with `kr · Q'` calls,
at most `kr · Q` of them signing or corruption requests (`Q' = w1RingQ'`), plus the spBCS
knowledge error at `t + Q · (qPub + PS.q) + 2N + kq` queries. -/
@[headline]
theorem w1BindConcrete.insiderForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e)) (hp : p.isApproved)
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
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (relayMUAdversary (w1ConcreteRejection p O MO βmin tol kr D Prod.mk) kr
          (max n 2) hk
          0 (w1RingForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase p O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have h := insiderForgeProb_le_muEufProbWithin_split (V := Sc.qVerifier Qs b b)
    (rel := w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) Prod.mk adm)
    (ext := Sc.dbExtractBits Ext)
    (bindsRing_w1BaseSigner_pair _ O βmin tol (concreteEnc p) _)
    (readsOnly_w1Base (prims := concretePrimitivesKeyGen p) (concreteEnc p) βmin tol kr D Prod.mk hO
      hM)
    (compiledBySplit_spbcsSplitProofSystem sp Sc Λ E hb honest _ (2 * N) _ (fun _ => true)
      fun _ w => some w)
    (claim_w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) _ Prod.mk Sc)
    (Sc.knowledgeBound _ Ext St hrbr Qs _ fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
    (fun ω h x w hw => ringRel_of_w1PS hO ω x w hw (join sp ω h) (base_join sp ω h))
    c₀ f₀ (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O Prod.mk Sc)
    (2 * N) (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O Prod.mk Sc)
    (run_w1ForgeStmtProg_join sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) _ Prod.mk
      Sc Λ E hb honest) A hS Q
  refine h.trans (add_le_add ?_ (le_of_eq (Sc.knowledgeError_toQVerifier Qs _ _)))
  refine le_trans (le_of_eq ?_) (muEufProbWithin_w1ConcreteBase_le_relay O MO βmin tol kr D Prod.mk
    hp hk 0 (w1RingForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q) _ Q)
  with_reducible rfl

variable (O MO βmin tol kr D Sc Λ E hb honest adm) in
/-- **The multi-user forger of the key-reuse game of the ring** (`splitStdForger` at the base
signer, the proof system
`w1RingPS`, the program statement of a forgery `w1ForgeStmtProg`, the claims `w1Claim`, the
relation `w1ExpRel` and the database extractor of the knowledge bound), with `w1RingQ'` requests
and queries. -/
noncomputable abbrev w1RingStdForger (sp : OracleSplit Y Y₁ (XOut k e))
    (Ext : CausalExtractor P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))))
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase p O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase p O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase p O MO βmin tol kr D Prod.mk).BSig)
    (A : KeyReuseAdversary (w1ConcreteBase p O MO βmin tol kr D Prod.mk)
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    MUAdversary (SignOracle.ringStd (w1ConcreteBase p O MO βmin tol kr D Prod.mk)) (max n 2)
      (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y)
      (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') :=
  splitStdMUForger sp (w1ConcreteBase p O MO βmin tol kr D Prod.mk)
    (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm (V := Sc.qVerifier Qs b b)
    (rel := w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) Prod.mk adm)
    (ext := Sc.dbExtractBits Ext)
    (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O Prod.mk Sc) (2 * N)
    (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O Prod.mk Sc) A hS Q
    (w1Claim (concretePrimitivesKeyGen p) Sc) c₀ f₀

/-- **Unforgeability of the key-reuse game of the ML-DSA ring signature publishing `w₁` from the
standard call game** (the form of `w1BindConcrete.insiderForgeProb_le` for the key-reuse game, through
`keyReuseForgeProb_le_muEufProbWithin_split` and `muEufProbWithin_w1ConcreteBase_le_relay_ringStd`,
the ordinary signer reading only the base component by `readsStdOnly_w1Base`). -/
theorem w1BindConcrete.keyReuseForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e)) (hp : p.isApproved)
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
    (A : KeyReuseAdversary (w1ConcreteBase p O MO βmin tol kr D Prod.mk)
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (relayMUAdversaryStd (w1ConcreteRejection p O MO βmin tol kr D Prod.mk) kr
        (max n 2) hk
          0 (w1RingStdForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase p O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have h := keyReuseForgeProb_le_muEufProbWithin_split (V := Sc.qVerifier Qs b b)
    (rel := w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) Prod.mk adm)
    (ext := Sc.dbExtractBits Ext)
    (bindsRing_w1BaseSigner_pair _ O βmin tol (concreteEnc p) _)
    (readsOnly_w1Base (prims := concretePrimitivesKeyGen p) (concreteEnc p) βmin tol kr D Prod.mk hO
      hM)
    (readsStdOnly_w1Base (prims := concretePrimitivesKeyGen p) (concreteEnc p) βmin tol kr D Prod.mk
      hO hM)
    (compiledBySplit_spbcsSplitProofSystem sp Sc Λ E hb honest _ (2 * N) _ (fun _ => true)
      fun _ w => some w)
    (claim_w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) _ Prod.mk Sc)
    (Sc.knowledgeBound _ Ext St hrbr Qs _ fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
    (fun ω h x w hw => ringRel_of_w1PS hO ω x w hw (join sp ω h) (base_join sp ω h))
    c₀ f₀ (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O Prod.mk Sc)
    (2 * N) (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O Prod.mk Sc)
    (run_w1ForgeStmtProg_join sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) _ Prod.mk
      Sc Λ E hb honest) A hS Q
  refine h.trans (add_le_add ?_ (le_of_eq (Sc.knowledgeError_toQVerifier Qs _ _)))
  refine le_trans (le_of_eq ?_) (muEufProbWithin_w1ConcreteBase_le_relay_ringStd O MO βmin tol kr
    D Prod.mk
    hp hk 0 (w1RingStdForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q) _
      Q)
  with_reducible rfl

end Concrete

/-! ### ML-DSA-44, ML-DSA-65 and ML-DSA-87 -/

section P44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  [NeZero (bucketCount Pm)] [Nonempty (MaskBox Pm)] {T N reps : ℕ} {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg]
  {O : W1Oracles (Bits (queryBits k kN kS L)) Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {MO : MaskOracle (Bits (queryBits k kN kS L)) Y Pm T
    (KeyRing (PubKey Pm Kg) N × RMsg)}
  {βmin : ℚ≥0} {tol kr D : ℕ} [NeZero D]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt Kg RMsg N) k kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt Kg RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk) → R →
    CausalProver P τ (W1ExpStmt Kg RMsg N)}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]
  {n t : ℕ} [NeZero n]

/-- **Unforgeability of the ML-DSA-44 ring signature publishing `w₁` from the standard call game**
(`w1BindConcrete.insiderForgeProb_le` at ML-DSA-44). -/
@[headline]
theorem w1BindScheme44.insiderForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e))
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt Kg RMsg N)
      (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))}
    {St : CausalStateFn P τ (W1ExpStmt Kg RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel Kg (concreteEnc Pm) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt Kg RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BSig)
    (A : InsiderAdversary (w1BindScheme44 O MO βmin tol kr D
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (relayMUAdversary (w1ConcreteRejection Pm O MO βmin tol kr D Prod.mk) kr
          (max n 2) hk
          0 (w1RingForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  w1BindConcrete.insiderForgeProb_le sp (Or.inl rfl) hk hO hM hrbr c₀ f₀ A hS Q

/-- **Unforgeability of the key-reuse game of the ML-DSA-44 ring signature publishing `w₁` from
the standard call game** (`w1BindConcrete.keyReuseForgeProb_le` at ML-DSA-44). -/
@[headline]
theorem w1BindScheme44.keyReuseForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e))
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt Kg RMsg N)
      (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))}
    {St : CausalStateFn P τ (W1ExpStmt Kg RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel Kg (concreteEnc Pm) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt Kg RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BSig)
    (A : KeyReuseAdversary (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk)
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (relayMUAdversaryStd (w1ConcreteRejection Pm O MO βmin tol kr D Prod.mk) kr
        (max n 2) hk
          0 (w1RingStdForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  w1BindConcrete.keyReuseForgeProb_le sp (Or.inl rfl) hk hO hM hrbr c₀ f₀ A hS Q

end P44

section P65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  [NeZero (bucketCount Pm)] [Nonempty (MaskBox Pm)] {T N reps : ℕ} {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg]
  {O : W1Oracles (Bits (queryBits k kN kS L)) Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {MO : MaskOracle (Bits (queryBits k kN kS L)) Y Pm T
    (KeyRing (PubKey Pm Kg) N × RMsg)}
  {βmin : ℚ≥0} {tol kr D : ℕ} [NeZero D]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt Kg RMsg N) k kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt Kg RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk) → R →
    CausalProver P τ (W1ExpStmt Kg RMsg N)}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]
  {n t : ℕ} [NeZero n]

/-- **Unforgeability of the ML-DSA-65 ring signature publishing `w₁` from the standard call game**
(`w1BindConcrete.insiderForgeProb_le` at ML-DSA-65). -/
@[headline]
theorem w1BindScheme65.insiderForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e))
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt Kg RMsg N)
      (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))}
    {St : CausalStateFn P τ (W1ExpStmt Kg RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel Kg (concreteEnc Pm) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt Kg RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BSig)
    (A : InsiderAdversary (w1BindScheme65 O MO βmin tol kr D
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (relayMUAdversary (w1ConcreteRejection Pm O MO βmin tol kr D Prod.mk) kr
          (max n 2) hk
          0 (w1RingForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  w1BindConcrete.insiderForgeProb_le sp (Or.inr (Or.inl rfl)) hk hO hM hrbr c₀ f₀ A hS Q

/-- **Unforgeability of the key-reuse game of the ML-DSA-65 ring signature publishing `w₁` from
the standard call game** (`w1BindConcrete.keyReuseForgeProb_le` at ML-DSA-65). -/
@[headline]
theorem w1BindScheme65.keyReuseForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e))
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt Kg RMsg N)
      (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))}
    {St : CausalStateFn P τ (W1ExpStmt Kg RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel Kg (concreteEnc Pm) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt Kg RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BSig)
    (A : KeyReuseAdversary (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk)
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (relayMUAdversaryStd (w1ConcreteRejection Pm O MO βmin tol kr D Prod.mk) kr
        (max n 2) hk
          0 (w1RingStdForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  w1BindConcrete.keyReuseForgeProb_le sp (Or.inr (Or.inl rfl)) hk hO hM hrbr c₀ f₀ A hS Q

end P65

section P87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  [NeZero (bucketCount Pm)] [Nonempty (MaskBox Pm)] {T N reps : ℕ} {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg]
  {O : W1Oracles (Bits (queryBits k kN kS L)) Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {MO : MaskOracle (Bits (queryBits k kN kS L)) Y Pm T
    (KeyRing (PubKey Pm Kg) N × RMsg)}
  {βmin : ℚ≥0} {tol kr D : ℕ} [NeZero D]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Sc : SPBCS Mg P (W1ExpStmt Kg RMsg N) k kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  {E : (j : ι) → (Sc.comp j).Encoder}
  {Vr : W1ExpStmt Kg RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} {hb : Sc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk) → R →
    CausalProver P τ (W1ExpStmt Kg RMsg N)}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]
  {n t : ℕ} [NeZero n]

/-- **Unforgeability of the ML-DSA-87 ring signature publishing `w₁` from the standard call game**
(`w1BindConcrete.insiderForgeProb_le` at ML-DSA-87). -/
@[headline]
theorem w1BindScheme87.insiderForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e))
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt Kg RMsg N)
      (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))}
    {St : CausalStateFn P τ (W1ExpStmt Kg RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel Kg (concreteEnc Pm) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt Kg RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BSig)
    (A : InsiderAdversary (w1BindScheme87 O MO βmin tol kr D
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (relayMUAdversary (w1ConcreteRejection Pm O MO βmin tol kr D Prod.mk) kr
          (max n 2) hk
          0 (w1RingForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  w1BindConcrete.insiderForgeProb_le sp (Or.inr (Or.inr rfl)) hk hO hM hrbr c₀ f₀ A hS Q

/-- **Unforgeability of the key-reuse game of the ML-DSA-87 ring signature publishing `w₁` from
the standard call game** (`w1BindConcrete.keyReuseForgeProb_le` at ML-DSA-87). -/
@[headline]
theorem w1BindScheme87.keyReuseForgeProb_le (sp : OracleSplit Y Y₁ (XOut k e))
    (hk : 0 < kr) (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt Kg RMsg N)
      (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm)))}
    {St : CausalStateFn P τ (W1ExpStmt Kg RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel Kg (concreteEnc Pm) Prod.mk adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt Kg RMsg N) Sc.NIProof)
    (f₀ : (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).PK ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BMsg ×
      (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).BSig)
    (A : KeyReuseAdversary (w1ConcreteBase Pm O MO βmin tol kr D Prod.mk)
      (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp) adm
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (relayMUAdversaryStd (w1ConcreteRejection Pm O MO βmin tol kr D Prod.mk) kr
        (max n 2) hk
          0 (w1RingStdForger O MO βmin tol kr D Sc Λ E hb honest adm sp Ext c₀ f₀ A hS Q)
          (w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P'))
        (kr * w1RingQ' O MO βmin tol kr D Sc Λ E hb honest sp Q S w P') (kr * Q) +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase Pm O MO βmin tol kr D Prod.mk).qPub +
            (w1RingPS O MO βmin tol kr D Sc Λ E hb honest sp).q) + 2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  w1BindConcrete.keyReuseForgeProb_le sp (Or.inr (Or.inr rfl)) hk hO hM hrbr c₀ f₀ A hS Q

end P87

end GordieHowe.Ring.MLDSAW1
