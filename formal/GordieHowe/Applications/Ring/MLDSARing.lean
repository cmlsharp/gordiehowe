-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSignerFacts
public import GordieHowe.Applications.Ring.MLDSALoopBound
public import GordieHowe.Applications.Ring.StmtBase
public import GordieHowe.Applications.Ring.StmtAnon
public import GordieHowe.Applications.Ring.RingForgerSPBCS
public import GordieHowe.Applications.Ring.RingForgerZKStmt
public import GordieHowe.Applications.Ring.RingSignsStdFacts

@[expose] public section

/-!
# The generic ML-DSA ring signature

The ring signature `ofBase (mldsaBaseSigner p prims maxAttempts bmsg) PS adm` (the
base signer of `GordieHowe/Applications/Ring/BaseSigners.lean`: the hedged FIPS 204 signer on the
base message `bmsg R m`, public value `Unit`) whose proof system `PS` is a compiled IOP over its
own statements that verify ML-DSA base signatures (`Ring.StmtVerifiesRing.proofSystem`). The
statements here are generic over the IOP `C`, its transcript `TD`, its honest prover `Hc` and the
map `V : StmtVerifiesRing …`, which the compiled ML-DSA-44 ring programs instantiate
(`GordieHowe.MLDSA44.Ring`); every headline is an instance of a generic theorem of
`GordieHowe/Applications/Ring/StmtBase.lean`, `GordieHowe/Applications/Ring/StmtAnon.lean`,
`GordieHowe/Applications/Ring/RingForgerSPBCS.lean` or
`GordieHowe/Applications/Ring/RingForgerZKStmt.lean`.

- `mldsaOn p prims maxAttempts TD kS bmsg`: the base signer on the compiled oracle of `TD`;
  `mldsaScheme p prims maxAttempts Hc hb hf V`: the scheme.
- Headlines: `mldsaScheme.completeWithin` (completeness at the per-message refusal term
  `mldsaRefuseMsg` of `GordieHowe/Applications/Ring/MLDSALoopBound.lean` and the correctness error
  `εc`; the per-key form `mldsaScheme.completeAtWithin` remains, its refusal hypothesis known at the
  FIPS primitives only at `ρ = 1`),
  `mldsaScheme.insiderForgeProb_le_of_bindsRing`,
  `mldsaScheme.keyReuseForgeProb_le_of_bindsRing` (BKM06 Definition 7 and key-reuse
  unforgeability for a ring-binding base message, by knowledge soundness, from the base scheme's
  standard MU-EUF-CMA^corr game `SignOracle.std` with at most `Q` signing and corruption requests;
  the ring-oracle forms `mldsaScheme.insiderForgeProb_le_muEufProbWithin`,
  `mldsaScheme.keyReuseForgeProb_le_muEufProbWithin` and the extraction-forger forms
  `mldsaScheme.insiderForgeProb_le_extractionSuccess`, `mldsaScheme.keyReuseForgeProb_le_extractionSuccess` remain),
  `mldsaScheme.insiderForgeProb_le` (BKM06 Definition 7 for every base
  message, from zero knowledge, simulation extraction and MU-EUF-CMA^corr, at the worst-message
  refusal term `mldsaRefuseAvg`; the form at a refusal bound `ρ`,
  `mldsaScheme.insiderForgeProb_le_refuseAvg`, remains),
  `mldsaScheme.anonAdvantage_le` (anonymity against full key exposure, `Pub = Unit`, at
  `mldsaRefuseAvg`).
- Satisfiability of the base-signer hypotheses: `RefuseWithin` at `1`
  (`BaseSigner.refuseWithin_one`); `CorrectWithin` at `0` under the signing and verification laws
  (`mldsaBaseSigner_correctWithin_zero`), at every approved parameter set at the concrete
  primitives with the FIPS 204 `ExpandS` and any `ExpandMask`
  (`mldsaBaseSigner_correctWithin_zero_concreteKeyGen`,
  `mldsaBaseSigner_correctWithin_zero_concrete`); and
  `exists_bindsRing_mldsaBaseSigner`: some base message binds the ring (the witness is a unary
  encoding of the index of the pair `(R, m)`).
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum Signature RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature _root_.MLDSA
open scoped NNReal ENNReal

variable (p : Params) (prims : Primitives p) [NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] (maxAttempts : ℕ)
  {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-! ### Satisfiability of the ring-binding hypothesis -/

/-- **Some base message binds the ring**: for some length `len` and base message `bmsg` of `len`
bytes, the ML-DSA base signer at `bmsg` binds the ring. The witness is `len = card (KeyRing PK N ×
RMsg)` and the unary encoding of the index of `(R, m)` (byte `j` is `1` exactly when `j` is below
the index). -/
theorem exists_bindsRing_mldsaBaseSigner {Xo Yo : Type} (N : ℕ) :
    ∃ (len : ℕ) (bmsg : KeyRing (PublicKey p prims) N → RMsg → _root_.MLDSA.Bytes len),
      (mldsaBaseSigner p prims maxAttempts bmsg : BaseSigner Xo Yo N (mldsaBaseT p prims len RMsg)).BindsRing := by
  classical
  let e := Fintype.equivFin (KeyRing (PublicKey p prims) N × RMsg)
  let n := Fintype.card (KeyRing (PublicKey p prims) N × RMsg)
  refine ⟨n, fun R m => Vector.ofFn fun j : Fin n => if j.1 < (e (R, m)).1 then 1 else 0, ?_⟩
  intro R R' m m' h
  dsimp only [mldsaBaseSigner] at h
  have hk : (e (R, m)).1 = (e (R', m')).1 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := Vector.ext_iff.mp h (e (R, m)).1 (hlt.trans (e (R', m')).2)
      simp [Vector.getElem_ofFn] at this
      exact absurd (Fin.le_def.1 this) (not_le.2 hlt)
    · have := Vector.ext_iff.mp h (e (R', m')).1 (hlt.trans (e (R, m)).2)
      simp [Vector.getElem_ofFn] at this
      exact absurd (Fin.le_def.1 this) (not_le.2 hlt)
  have := e.injective (Fin.ext hk)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-! ### The scheme over an IOP whose statements verify ML-DSA base signatures -/

/-- **The ML-DSA base signer on the compiled oracle of a transcript `TD`** at `kS`-byte salts:
`mldsaBaseSigner p prims maxAttempts bmsg` with the oracle `Bits (queryBits k (2k) kS 2^40) →
XOut k (fsExtraBytes + maxGrant)` of `TD`. -/
abbrev mldsaOn {X₀ W : Type} {rel₀ : Set (X₀ × W)} {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀}
    (TD : SPBCS.ProofSystemTranscript C) (kS : ℕ) {N : ℕ}
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → _root_.MLDSA.Bytes len) :
    BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N
      (mldsaBaseT p prims len RMsg) :=
  mldsaBaseSigner p prims maxAttempts bmsg

/-- **The generic ML-DSA ring signature** at the base message `bmsg`: `ofBase
(mldsaBaseSigner p prims maxAttempts bmsg) PS adm` with `PS` the compiled IOP `C` read at the base
signer's ring statements (`StmtVerifiesRing.proofSystem` of `V`, the honest prover `Hc`, proofs in
the format `pB`), on the supported rings `adm`. -/
noncomputable abbrev mldsaScheme {X₀ W : Type} {rel₀ : Set (X₀ × W)}
    {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀} {SD : C.SimData} {Inp : Type}
    {relI : Set (X₀ × Inp)} (Hc : C.Honest SD Inp relI) {TD : SPBCS.ProofSystemTranscript C}
    {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) {N : ℕ}
    {bmsg : KeyRing (PublicKey p prims) N → RMsg → _root_.MLDSA.Bytes len}
    {adm : KeyRing (mldsaOn p prims maxAttempts TD kS bmsg).PK N → Prop}
    (V : StmtVerifiesRing rel₀ relI (mldsaOn p prims maxAttempts TD kS bmsg) adm)
    [DecidablePred adm] :
    RingScheme (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N
      (ofBaseT (mldsaBaseT p prims len RMsg) (spbcsPST (TD.setting kS hb).model pB Hc.Coins)) :=
  ofBase (mldsaOn p prims maxAttempts TD kS bmsg) (V.proofSystem Hc hb hf) adm

variable {X₀ W : Type} {rel₀ : Set (X₀ × W)} {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀}
  {SD : C.SimData} {Inp : Type} {relI : Set (X₀ × Inp)} (Hc : C.Honest SD Inp relI)
  {TD : SPBCS.ProofSystemTranscript C} {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {bmsg : KeyRing (PublicKey p prims) N → RMsg → _root_.MLDSA.Bytes len}
  {adm : KeyRing (mldsaOn p prims maxAttempts TD kS bmsg).PK N → Prop} [DecidablePred adm]
  (V : StmtVerifiesRing rel₀ relI
    (mldsaOn p prims maxAttempts TD kS bmsg) adm)

/-- **Completeness of the generic ML-DSA ring signature** (`StmtVerifiesRing.completeWithin`):
for an honest prover with completeness error `errc` (`hE`) and a hedged signer with correctness
error `εc` (`hc`), `mldsaScheme` refuses with probability at most the per-message refusal term
`mldsaRefuseMsg p prims maxAttempts bmsg` (the refusal probability of an honest member at the base
message of its honest ring, averaged over the members' key seeds; `refuseWithin_mldsaRefuseMsg`)
and is rejected with probability at most `εc + errc` plus spBCS's overrun and key-collision terms
and `0 / 2^(8 kS)`. The refusal term is left symbolic; FIPS 204 Appendix C's heuristic puts it
near `2^-256` at `maxAttempts = 814`, a remark about its expected size, not a hypothesis here. -/
@[headline]
theorem mldsaScheme.completeWithin {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    {εc : ℝ≥0∞} (hc : (mldsaOn p prims maxAttempts TD kS bmsg).CorrectWithin εc) :
    (mldsaScheme p prims maxAttempts Hc hb hf V).CompleteWithin
      (mldsaRefuseMsg p prims maxAttempts bmsg)
      (εc + ((errc : ℝ≥0∞) + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision (C.term.size C.rounds) TD.k + ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * kS))) :=
  V.completeWithin Hc hb hf hE (refuseWithin_mldsaRefuseMsg p prims maxAttempts bmsg adm) hc

/-- **Completeness per key of the generic ML-DSA ring signature**
(`StmtVerifiesRing.completeAtWithin`): as `mldsaScheme.completeWithin`, with the per-key refusal
rate `ρ` (`RefuseAtWithin`), at every key and every supported ring holding it. At the FIPS
primitives the hypothesis `hρ` is known only at `ρ = 1` (`BaseSigner.refuseAtWithin_one`): a key
whose attempts all get one failing challenge refuses with probability `1`
(`GordieHowe/Applications/Ring/MLDSALoopBound.lean`), so the averaged `mldsaScheme.completeWithin`
is the completeness statement. -/
theorem mldsaScheme.completeAtWithin {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    {ρ εc : ℝ≥0∞} (hρ : (mldsaOn p prims maxAttempts TD kS bmsg).RefuseAtWithin adm ρ)
    (hc : (mldsaOn p prims maxAttempts TD kS bmsg).CorrectWithin εc) :
    (mldsaScheme p prims maxAttempts Hc hb hf V).CompleteAtWithin ρ
      (εc + ((errc : ℝ≥0∞) + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision (C.term.size C.rounds) TD.k + ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * kS))) :=
  V.completeAtWithin Hc hb hf hE hρ hc

variable [Inhabited W] [DecidableEq X₀]

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the generic ML-DSA
ring signature for a ring-binding base message** (`StmtVerifiesRing.insiderForgeProb_le`): for a
base message that binds the ring (`hbind`; satisfiable, `exists_bindsRing_mldsaBaseSigner`) and the
soundness data `Sd` of `C`, the forgery probability of an adversary of BKM06 Definition 7 against
`mldsaScheme` is at most the extraction forger's success in MU-EUF-CMA^corr with the ring-aware
signing oracle plus spBCS's knowledge error at the largest round error of `C` and
`t + Q · q + kq` queries. The headline form is
`mldsaScheme.insiderForgeProb_le_of_bindsRing`. -/
theorem mldsaScheme.insiderForgeProb_le_extractionSuccess
    (hbind : (mldsaOn p prims maxAttempts TD kS bmsg).BindsRing) (Sd : C.Sound) {n t : ℕ}
    (A : InsiderAdversary (mldsaScheme p prims maxAttempts Hc hb hf V) n
      (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      extractionSuccess (insiderRelay _ _ adm) A Q
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V.stmt V.check V.input)
          (StmtVerifiesRing.extractor hb V) +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (mldsaScheme p prims maxAttempts Hc hb hf V).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  V.insiderForgeProb_le Hc hb hf hbind Sd A Q

/-- **Key-reuse unforgeability of the generic ML-DSA ring signature for a ring-binding base
message** (`StmtVerifiesRing.keyReuseForgeProb_le`): the bound of `mldsaScheme.insiderForgeProb_le_extractionSuccess`
for the key-reuse game, the extraction forger in MU-EUF-CMA^corr with the ring-aware and the
ordinary signing oracle. The headline form is `mldsaScheme.keyReuseForgeProb_le_muEufProbWithin`. -/
theorem mldsaScheme.keyReuseForgeProb_le_extractionSuccess
    (hbind : (mldsaOn p prims maxAttempts TD kS bmsg).BindsRing) (Sd : C.Sound) {n t : ℕ}
    (A : KeyReuseAdversary _ (V.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      extractionSuccess (keyReuseRelay _ _ adm) A Q
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V.stmt V.check V.input)
          (StmtVerifiesRing.extractor hb V) +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (mldsaScheme p prims maxAttempts Hc hb hf V).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  V.keyReuseForgeProb_le Hc hb hf hbind Sd A Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the generic ML-DSA
ring signature for a ring-binding base message, from MU-EUF-CMA^corr**
(`StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin`; the base signer is oracle-free,
`mldsaBaseSigner_oracleFree`): for a base message that binds the ring (`hbind`; satisfiable,
`exists_bindsRing_mldsaBaseSigner`), the soundness data `Sd` of `C` and an adversary of BKM06
Definition 7 with the schedule bound `S`, `w`, `P` (`hS`), its forgery probability is at most the
success probability of the explicit multi-user forger `ringMUForger` with at most `Q` signing and
corruption requests (`Signature.muEufProbWithin`) plus spBCS's knowledge error at the largest round
error of `C` and `t + Q · q + kq` queries. -/
theorem mldsaScheme.insiderForgeProb_le_muEufProbWithin
    (hbind : (mldsaOn p prims maxAttempts TD kS bmsg).BindsRing) (Sd : C.Sound) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (mldsaOn p prims maxAttempts TD kS bmsg) ×
      Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : (mldsaOn p prims maxAttempts TD kS bmsg).PK ×
      (mldsaOn p prims maxAttempts TD kS bmsg).BMsg × (mldsaOn p prims maxAttempts TD kS bmsg).BSig)
    (A : InsiderAdversary (mldsaScheme p prims maxAttempts Hc hb hf V) n
      (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringMUForger _ (V.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V.stmt V.check V.input) c₀
          (StmtVerifiesRing.extractorList hb V) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam _ (V.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
            (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))))
        (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
          (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q) +
            kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  V.insiderForgeProb_le_muEufProbWithin Hc hb hf hbind
    (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg) Sd c₀ f₀ A hS Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the generic ML-DSA
ring signature for a ring-binding base message, from the standard MU-EUF-CMA^corr game**
(`StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin_std`; the ring-aware signer signs as the
ordinary signer on the base message, `mldsaBaseSigner_ringSignsStd`): the bound of
`mldsaScheme.insiderForgeProb_le_muEufProbWithin` with the multi-user forger relayed to the base
scheme's own game (`SignOracle.std`, `Signature.ringToStd`), with the same numbers of requests and
of signing and corruption requests. -/
@[headline]
theorem mldsaScheme.insiderForgeProb_le_of_bindsRing
    (hbind : (mldsaOn p prims maxAttempts TD kS bmsg).BindsRing) (Sd : C.Sound) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (mldsaOn p prims maxAttempts TD kS bmsg) ×
      Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : (mldsaOn p prims maxAttempts TD kS bmsg).PK ×
      (mldsaOn p prims maxAttempts TD kS bmsg).BMsg × (mldsaOn p prims maxAttempts TD kS bmsg).BSig)
    (A : InsiderAdversary (mldsaScheme p prims maxAttempts Hc hb hf V) n
      (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (Signature.ringToStd 0 (ringMUForger _ (V.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V.stmt V.check V.input) c₀
          (StmtVerifiesRing.extractorList hb V) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam _ (V.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
            (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))))
          (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
            (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))))
        (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
          (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q) +
            kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  V.insiderForgeProb_le_muEufProbWithin_std Hc hb hf hbind
    (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg)
    (mldsaBaseSigner_ringSignsStd p prims maxAttempts bmsg) Sd c₀ f₀ A hS Q

/-- **Key-reuse unforgeability of the generic ML-DSA ring signature for a ring-binding base
message, from MU-EUF-CMA^corr** (`StmtVerifiesRing.keyReuseForgeProb_le_muEufProbWithin`): the bound
of `mldsaScheme.insiderForgeProb_le_muEufProbWithin` for the key-reuse game, the multi-user forger
with the ring-aware and the ordinary signing oracle. The headline form is
`mldsaScheme.keyReuseForgeProb_le_of_bindsRing`. -/
theorem mldsaScheme.keyReuseForgeProb_le_muEufProbWithin
    (hbind : (mldsaOn p prims maxAttempts TD kS bmsg).BindsRing) (Sd : C.Sound) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (mldsaOn p prims maxAttempts TD kS bmsg) ×
      Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : (mldsaOn p prims maxAttempts TD kS bmsg).PK ×
      (mldsaOn p prims maxAttempts TD kS bmsg).BMsg × (mldsaOn p prims maxAttempts TD kS bmsg).BSig)
    (A : KeyReuseAdversary _ (V.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringMUForger _ (V.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V.stmt V.check V.input) c₀
          (StmtVerifiesRing.extractorList hb V) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam _ (V.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
            (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))))
        (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
          (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q) +
            kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  V.keyReuseForgeProb_le_muEufProbWithin Hc hb hf hbind
    (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg) Sd c₀ f₀ A hS Q

/-- **Key-reuse unforgeability of the generic ML-DSA ring signature for a ring-binding base
message, from the standard MU-EUF-CMA^corr game**
(`StmtVerifiesRing.keyReuseForgeProb_le_muEufProbWithin_std`; the ring-aware signer signs as the
ordinary signer on the base message, `mldsaBaseSigner_ringSignsStd`): the bound of
`mldsaScheme.keyReuseForgeProb_le_muEufProbWithin` with the multi-user forger relayed to the base
scheme's own game (`SignOracle.std`, `Signature.ringStdToStd`), with the same numbers of requests
and of signing and corruption requests. -/
@[headline]
theorem mldsaScheme.keyReuseForgeProb_le_of_bindsRing
    (hbind : (mldsaOn p prims maxAttempts TD kS bmsg).BindsRing) (Sd : C.Sound) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (mldsaOn p prims maxAttempts TD kS bmsg) ×
      Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : (mldsaOn p prims maxAttempts TD kS bmsg).PK ×
      (mldsaOn p prims maxAttempts TD kS bmsg).BMsg × (mldsaOn p prims maxAttempts TD kS bmsg).BSig)
    (A : KeyReuseAdversary _ (V.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (Signature.ringStdToStd 0 (ringMUForger _ (V.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V.stmt V.check V.input) c₀
          (StmtVerifiesRing.extractorList hb V) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam _ (V.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
            (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))))
          (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
            (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))))
        (ringQ' (StmtVerifiesRing.verifier hb (pB := pB) V) Q S w P
          (1 + ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * ((mldsaOn p prims maxAttempts TD kS bmsg).qPub + (V.proofSystem Hc hb hf).q) +
            kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  V.keyReuseForgeProb_le_muEufProbWithin_std Hc hb hf hbind
    (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg)
    (mldsaBaseSigner_ringSignsStd p prims maxAttempts bmsg) Sd c₀ f₀ A hS Q

omit [Inhabited W] [DecidableEq X₀] in
/-- **Anonymity against full key exposure (BKM06 Definition 4, `Q` adaptive challenges) of the
generic ML-DSA ring signature** (`StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins_avg`, the public
value `Unit`, `BaseSigner.pubOfCoins_unique`): for an honest prover with completeness error `errc`
(`hE`) and a hedged signer with correctness error `εc` (`hcorr`), every anonymity adversary (any
oracle view, at most `t` queries) against `n` users has advantage at most
`Q · wiError errc (Q · |AnonRequest|) + 2Q · εc + Q · n · mldsaRefuseAvg`, with `mldsaRefuseAvg`
the worst-message refusal term of the hedged signer (`refuseAvgWithin_mldsaRefuseAvg`), left
symbolic. It is larger than the per-message term of completeness, near which FIPS 204 Appendix C's
heuristic `2^-256` sits (`GordieHowe/Applications/Ring/MLDSALoopBound.lean`). -/
@[headline]
theorem mldsaScheme.anonAdvantage_le {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    {εc : ℝ≥0} (hcorr : (mldsaOn p prims maxAttempts TD kS bmsg).CorrectWithin εc) {n : ℕ}
    {Vw : OracleView (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
      (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))} {t : ℕ}
    (A : AnonAdversary (mldsaScheme p prims maxAttempts Hc hb hf V) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * (TD.setting kS hb).model.wiError errc
          (Q * Fintype.card (AnonRequest (mldsaScheme p prims maxAttempts Hc hb hf V) n)) +
        2 * Q * εc + Q * n * (mldsaRefuseAvg p prims maxAttempts).toReal := by
  have : Unique (mldsaOn p prims maxAttempts TD kS bmsg).Pub := inferInstanceAs (Unique Unit)
  have hρ : (mldsaOn p prims maxAttempts TD kS bmsg).RefuseAvgWithin adm
      ((mldsaRefuseAvg p prims maxAttempts).toNNReal : ℝ≥0∞) := by
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (mldsaRefuseAvg_le_one p prims maxAttempts))]
    exact refuseAvgWithin_mldsaRefuseAvg p prims maxAttempts bmsg adm
  have h := V.anonAdvantage_le_of_pubOfCoins_avg Hc hb hf hE
    (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg) (fun _ => Finset.card_filter_le _ _)
    (BaseSigner.pubOfCoins_unique _) hcorr hρ A Q
  rwa [ENNReal.coe_toNNReal_eq_toReal] at h

omit [Inhabited W] [DecidableEq X₀] in
/-- The ML-DSA base signer's public values `()` are inhabited. -/
instance mldsaOn_nonempty_pub : Nonempty (mldsaOn p prims maxAttempts TD kS bmsg).Pub :=
  inferInstanceAs (Nonempty Unit)

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the generic ML-DSA
ring signature for every base message (converted signatures included), from zero knowledge,
simulation extraction and MU-EUF-CMA^corr, at a refusal rate averaged over the keys**
(`StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb_refuseAvg`; the base signer is oracle-free,
`mldsaBaseSigner_oracleFree`, and its public value `()` is read off the coins,
`BaseSigner.pubOfCoins_unique`): for an honest prover with completeness error `errc` (`hE`), the
soundness data `Sd` of `C`, a signer refusing with probability at most `ρ` averaged over the honest
keys on the supported rings (`hρ`; at `mldsaRefuseAvg`,
`mldsaScheme.insiderForgeProb_le`), with correctness error `εc`
(`hcorr`; `mldsaBaseSigner_correctWithin_zero` at the FIPS primitives), an injective statement map
(`hinj`) and no honest statement of the empty ring (`hnil`), an adversary of BKM06 Definition 7
with the schedule bound `S`, `w`, `P'` (`hS`) forges with probability at most the success of the
multi-user forger `zkForger` with `zkQ'` requests, plus the zero-knowledge error, the
simulation-extraction error, spBCS's knowledge error, `2Q · εc` and `Q · n · ρ`. The statements
of the empty ring are tested by `RingSignature.EmptyRingTest V.stmt`. -/
theorem mldsaScheme.insiderForgeProb_le_refuseAvg [Fintype Inp] [DecidableEq Inp]
    [RingSignature.EmptyRingTest V.stmt]
    [Nonempty (mldsaOn p prims maxAttempts TD kS bmsg).Msg]
    [Nonempty (mldsaOn p prims maxAttempts TD kS bmsg).BSig]
    (hk : 0 < TD.k) {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound) {ρ : ℝ≥0∞}
    (hρ : (mldsaOn p prims maxAttempts TD kS bmsg).RefuseAvgWithin adm ρ) {εc : ℝ≥0∞}
    (hcorr : (mldsaOn p prims maxAttempts TD kS bmsg).CorrectWithin εc)
    (hinj : Function.Injective V.stmt)
    (hnil : ∀ x : RingSignature.RingStmt (mldsaOn p prims maxAttempts TD kS bmsg),
      x.ring.1 = [] → ∀ y, (V.stmt x, y) ∉ relI)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (mldsaScheme p prims maxAttempts Hc hb hf V) n
      (OracleView.queriesOnly _ _) t) [NeZero n]
    [Nonempty (SPBCS.NIProof (k := TD.k) (kN := 2 * TD.k) (kS := kS) (L := 2 ^ 40)
      (e := Configurations.fsExtraBytes + TD.maxGrant) (TD.setting kS hb).model)] (Q : ℕ)
    (f₀ : (mldsaOn p prims maxAttempts TD kS bmsg).PK ×
      (mldsaOn p prims maxAttempts TD kS bmsg).BMsg × (mldsaOn p prims maxAttempts TD kS bmsg).BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (RingSignature.Insider.zkForger A (wit := V.wit) (fun _ _ _ _ => False)
          (fun _ => ()) Q
          (RingSignature.Insider.zkPsim (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
            (TD.setting kS hb).layout hf
            (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
            V.check V.input adm (TD.setting kS hb).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T)
          C.extractor (kqOf C.merges C.rounds pB pB) f₀)
        (RingSignature.Insider.zkQ' (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
          (TD.setting kS hb).layout hf
          (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
          V.check V.input adm (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T Q S w P') +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (kqOf C.merges C.rounds pB pB)
          (maxError Sd.error)
          ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
            (TD.setting kS hb).viewEncoder.toViewRead pB id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T).q t Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (mldsaScheme p prims maxAttempts Hc hb hf V).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) +
        2 * Q * εc + Q * (n * ρ) :=
  haveI : Unique (mldsaOn p prims maxAttempts TD kS bmsg).Pub := inferInstanceAs (Unique Unit)
  V.insiderForgeProb_le_zk_muEufProb_refuseAvg Hc hb hf hk hE Sd
    (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg) (BaseSigner.pubOfCoins_unique _) hρ
    hcorr hinj hnil T A Q f₀ hS

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the generic ML-DSA
ring signature for every base message (converted signatures included), from zero knowledge,
simulation extraction and MU-EUF-CMA^corr**
(`mldsaScheme.insiderForgeProb_le_refuseAvg` at the worst-message refusal term
`mldsaRefuseAvg`, `refuseAvgWithin_mldsaRefuseAvg`): the bound with `Q · n · mldsaRefuseAvg` for the
refusals, `mldsaRefuseAvg` left symbolic. -/
@[headline]
theorem mldsaScheme.insiderForgeProb_le [Fintype Inp] [DecidableEq Inp]
    [RingSignature.EmptyRingTest V.stmt]
    [Nonempty (mldsaOn p prims maxAttempts TD kS bmsg).Msg]
    [Nonempty (mldsaOn p prims maxAttempts TD kS bmsg).BSig]
    (hk : 0 < TD.k) {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound) {εc : ℝ≥0∞}
    (hcorr : (mldsaOn p prims maxAttempts TD kS bmsg).CorrectWithin εc)
    (hinj : Function.Injective V.stmt)
    (hnil : ∀ x : RingSignature.RingStmt (mldsaOn p prims maxAttempts TD kS bmsg),
      x.ring.1 = [] → ∀ y, (V.stmt x, y) ∉ relI)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (mldsaScheme p prims maxAttempts Hc hb hf V) n
      (OracleView.queriesOnly _ _) t) [NeZero n]
    [Nonempty (SPBCS.NIProof (k := TD.k) (kN := 2 * TD.k) (kS := kS) (L := 2 ^ 40)
      (e := Configurations.fsExtraBytes + TD.maxGrant) (TD.setting kS hb).model)] (Q : ℕ)
    (f₀ : (mldsaOn p prims maxAttempts TD kS bmsg).PK ×
      (mldsaOn p prims maxAttempts TD kS bmsg).BMsg × (mldsaOn p prims maxAttempts TD kS bmsg).BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (RingSignature.Insider.zkForger A (wit := V.wit) (fun _ _ _ _ => False)
          (fun _ => ()) Q
          (RingSignature.Insider.zkPsim (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
            (TD.setting kS hb).layout hf
            (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
            V.check V.input adm (TD.setting kS hb).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T)
          C.extractor (kqOf C.merges C.rounds pB pB) f₀)
        (RingSignature.Insider.zkQ' (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
          (TD.setting kS hb).layout hf
          (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
          V.check V.input adm (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T Q S w P') +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (kqOf C.merges C.rounds pB pB)
          (maxError Sd.error)
          ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
            (TD.setting kS hb).viewEncoder.toViewRead pB id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T).q t Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (mldsaScheme p prims maxAttempts Hc hb hf V).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) +
        2 * Q * εc + Q * (n * mldsaRefuseAvg p prims maxAttempts) :=
  mldsaScheme.insiderForgeProb_le_refuseAvg p prims maxAttempts Hc hb hf V hk hE Sd
    (refuseAvgWithin_mldsaRefuseAvg p prims maxAttempts bmsg adm) hcorr hinj hnil T A Q f₀ hS

end GordieHowe.Ring
