-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1RingBindingHeadline
public import GordieHowe.Applications.Ring.RingForgerSplitOn
public import GordieHowe.Applications.Ring.SPBCSSplitNonempty

@[expose] public section

/-!
# Forgeries of the ML-DSA ring publishing `w₁` on the empty ring

The proof system `w1PS` checks every ring statement, so a forgery on the empty ring verifies only
through a failure of knowledge soundness: the fixed relation `w1ExpRel` has no witness on the
empty ring (`ringRel_of_w1PS`, `RingRel.idx_lt`). The proof system `w1PSNonempty` is `w1PS` with
the empty ring rejected; its ring scheme has the signer, the keys and the signatures of the scheme
of `w1PS`.

- `w1PSNonempty`: `w1PS` checking that the ring is nonempty.
- `w1Concrete.forgeProbOn_nil_le`: at the concrete primitives and any base message `bmsg`, the
  probability of a forgery on the empty ring (BKM06 Definition 7) is at most the spBCS knowledge
  error of the headline `w1BindConcrete.insiderForgeProb_le`.
- `w1Concrete.insiderForgeProb_le_nonempty`: the forgery probability against the scheme of `w1PS`
  is at most that of the relabelled adversary (`UnforgeAdversary.withVerify`) against the scheme of
  `w1PSNonempty`, plus that knowledge error.

The hypotheses are those of `w1BindConcrete.insiderForgeProb_le` without the ring-binding base message.
As there, `hrbr` (causal round-by-round knowledge soundness for `w1ExpRel`) and `hb` are
obligations of the proof system, met by the one-message IOP deciding `w1ExpRel`
(`causalRBRKnowledgeSound_oneMsg`); the other hypotheses are satisfiable as stated there.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Signature Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open scoped ENNReal

section PS

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {p : Params} (prims : Primitives p) {Msg : Type} {N reps : ℕ}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] (O : W1Oracles (Bits (queryBits k kN kS L)) Y p prims Msg N reps)
  (βmin : ℚ≥0) (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p)
  {CLp : Type} [Fintype CLp] [DecidableEq CLp] [Nonempty CLp] (Lp : W1Loop (Bits (queryBits k kN kS L)) Y p prims Msg N CLp) {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (W1ExpStmt prims RMsg N) k kN kS L e) (Λ : SiteLayout Mg)
  {b : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : RingSignature.RingWit (w1BaseSigner prims O βmin tol enc Lp bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N))

/-- **The proof system of the ML-DSA ring publishing `w₁` with the empty ring rejected**: `w1PS`
with the check that the ring is nonempty. -/
noncomputable abbrev w1PSNonempty :
    ProofSystem (Bits (queryBits k kN kS L)) Y (RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc Lp bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims))
      (spbcsPST M b R) :=
  spbcsSplitProofSystem sp M Λ E hb honest (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg) (fun x => decide (x.ring.1 ≠ []))
    fun _ w => some w

end PS

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

section Concrete

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {T N reps : ℕ} {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {O : W1Oracles (Bits (queryBits k kN kS L)) Y p (concretePrimitivesKeyGen p) Msg N reps}
  {MO : MaskOracle (Bits (queryBits k kN kS L)) Y p T Msg}
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
  {honest : RingSignature.RingWit (w1ConcreteBase p O MO βmin tol kr D bmsg) → R →
    CausalProver P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm]
  {n t : ℕ} [NeZero n]

/-- **A forgery on the empty ring is a knowledge-soundness failure** (BKM06 Definition 7,
`forgeProbOn_nil_le_knowledgeError_split` at the base signer `w1ConcreteBase` with any base message
`bmsg`, the converted one `bmsg R m = m` included, and the proof system `w1PS`): for decodings of
the base signer's oracles reading only the base component of the split `sp` (`hO`, `hM`), a causal
round-by-round knowledge-sound IOP for the fixed relation `w1ExpRel` (`hrbr`), and an adversary with
`n` users, `t` queries and `Q` requests, the probability of a forgery on the empty ring is at most
the spBCS knowledge error at `t + Q · (qPub + PS.q) + 2N + kq` queries. -/
theorem w1Concrete.forgeProbOn_nil_le (sp : OracleSplit Y Y₁ (XOut k e)) (hO : O.ReadsFst sp)
    (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))}
    {St : CausalStateFn P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmsg adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) Sc.NIProof)
    (A : InsiderAdversary (ofBase (w1ConcreteBase p O MO βmin tol kr D bmsg)
      (w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
        (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t) (Q : ℕ) :
    forgeProbOn A Q (fun o => o.1.1 = []) ≤
      knowledgeError k e (kqOf Mg nr b b)
        (t + Q * ((w1ConcreteBase p O MO βmin tol kr D bmsg).qPub +
          (w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
        (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest).q) +
          2 * N + kqOf Mg nr b b)
        Sc.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have h := forgeProbOn_nil_le_knowledgeError_split (V := Sc.qVerifier Qs b b)
    (rel := w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmsg adm)
    (ext := Sc.dbExtractBits Ext)
    (readsOnly_w1Base (prims := concretePrimitivesKeyGen p) (concreteEnc p) βmin tol kr D bmsg hO
      hM)
    (compiledBySplit_spbcsSplitProofSystem sp Sc Λ E hb honest _ (2 * N) _ (fun _ => true)
      fun _ w => some w)
    (claim_w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) _ bmsg Sc)
    (Sc.knowledgeBound _ Ext St hrbr Qs _ fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
    (fun ω h x w hw => ringRel_of_w1PS hO ω x w hw (join sp ω h) (base_join sp ω h))
    c₀ (w1ForgeStmtProg sp (concretePrimitivesKeyGen p) O bmsg Sc)
    (2 * N) (w1ForgeStmtProg_queries sp (concretePrimitivesKeyGen p) O bmsg Sc)
    (run_w1ForgeStmtProg_join sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) _ bmsg
      Sc Λ E hb honest) A Q
  exact h.trans (le_of_eq (Sc.knowledgeError_toQVerifier Qs _ _))

/-- **BKM06 Definition 7 for the ML-DSA ring publishing `w₁` with the empty ring rejected**
(`insiderForgeProb_le_spbcsSplit_check`, then `w1Concrete.forgeProbOn_nil_le`): under the
hypotheses of `w1Concrete.forgeProbOn_nil_le`, the forgery probability of an adversary against the
scheme of `w1PS` is at most that of the relabelled adversary against the scheme of
`w1PSNonempty`, plus the spBCS knowledge error at `t + Q · (qPub + PS.q) + 2N + kq` queries. -/
theorem w1Concrete.insiderForgeProb_le_nonempty (sp : OracleSplit Y Y₁ (XOut k e))
    (hO : O.ReadsFst sp) (hM : MO.ReadsFst sp)
    {Ext : CausalExtractor P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)
      (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p)))}
    {St : CausalStateFn P τ (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N)}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel (concretePrimitivesKeyGen p) (concreteEnc p) bmsg adm)
      Vr Ext St ε)
    (c₀ : Claim (W1ExpStmt (concretePrimitivesKeyGen p) RMsg N) Sc.NIProof)
    (A : InsiderAdversary (ofBase (w1ConcreteBase p O MO βmin tol kr D bmsg)
      (w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
        (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest) adm)
      n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) Y) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      insiderForgeProb (S := ofBase (w1ConcreteBase p O MO βmin tol kr D bmsg)
          (w1PSNonempty sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
            (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest) adm)
        (UnforgeAdversary.withVerify (S := ofBase (w1ConcreteBase p O MO βmin tol kr D bmsg)
            (w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
        (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest) adm)
          (ofBase (w1ConcreteBase p O MO βmin tol kr D bmsg)
            (w1PSNonempty sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
              (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest)
            adm).verify (SideOracle.none _) A) Q +
        knowledgeError k e (kqOf Mg nr b b)
          (t + Q * ((w1ConcreteBase p O MO βmin tol kr D bmsg).qPub +
            (w1PS sp (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p)
        (hedgedLoop (concretePrimitivesKeyGen p) O MO βmin kr D) bmsg Sc Λ E hb honest).q) +
          2 * N + kqOf Mg nr b b)
          Sc.senc.digestsPerInput Mg.nJ (maxError ε) :=
  (insiderForgeProb_le_spbcsSplit_check sp Sc Λ E hb honest _ (2 * N) _ _ _
      (fun _ _ h => decide_eq_true h) A Q).trans
    (add_le_add le_rfl (w1Concrete.forgeProbOn_nil_le sp hO hM hrbr c₀ A Q))

end Concrete

end GordieHowe.Ring.MLDSAW1
