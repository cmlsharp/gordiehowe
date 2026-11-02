-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerGames
public import GordieHowe.Applications.Ring.StmtBase

@[expose] public section

/-!
# The ring signatures compiled by spBCS from MU-EUF-CMA^corr

The bounds of `GordieHowe/Applications/Ring/RingForgerGames.lean` for the proof systems of
`GordieHowe/Applications/Ring/RingUnforgeability.lean` (spBCS, `insiderForgeProb_le_spbcs`) and of
`GordieHowe/Applications/Ring/StmtBase.lean` (an IOP whose statements verify base signatures,
`StmtVerifiesRing.insiderForgeProb_le`): the forgery probability of BKM06 Definition 7 and of the
key-reuse game against an oracle-free base signer is at most the success probability in
MU-EUF-CMA^corr of the explicit multi-user forger `ringMUForger`, plus the knowledge error.

- `insiderForgeProb_le_muEufProb_spbcs`, `keyReuseForgeProb_le_muEufProb_spbcs`.
- `keyReuseForgeProb_le_muEufProbWithin_std_spbcs`,
  `Ring.StmtVerifiesRing.keyReuseForgeProb_le_muEufProbWithin_std`: the key-reuse game from the
  standard multi-user game, for a ring-aware signer signing as the ordinary signer.
- `insiderForgeProb_le_muEufProbWithin_std_spbcs`,
  `Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin_std`: BKM06 Definition 7 from the
  standard multi-user game, for a ring-aware signer signing as the ordinary signer.
- `Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProb`,
  `Ring.StmtVerifiesRing.keyReuseForgeProb_le_muEufProb`.
- `insiderForgeProb_le_muEufProbWithin_spbcs`, `keyReuseForgeProb_le_muEufProbWithin_spbcs`,
  `Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin`,
  `Ring.StmtVerifiesRing.keyReuseForgeProb_le_muEufProbWithin`: the same bounds with the
  multi-user forger winning with at most `Q` signing and corruption requests
  (`Signature.muEufProbWithin`).
-/

namespace GordieHowe

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum Signature RingSignature
open scoped NNReal ENNReal

/-! ### The spBCS proof system -/

section SPBCS

open SPTerm GordieHowe.Ring

variable {k kN kS L e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (RingStmt B) k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : RingStmt B → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [Nonempty R]
  (honest : RingWit B → R → CausalProver P τ (RingStmt B))
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ}
  {rel : Set (RingStmt B × RingWit B)} {Ext : CausalExtractor P τ (RingStmt B) (RingWit B)}
  {St : CausalStateFn P τ (RingStmt B)} {ε : ChIdx P τ → ℝ≥0}

/-- **BKM06 Definition 7 for the ring signature compiled by spBCS from
MU-EUF-CMA^corr**: `insiderForgeProb_le_muEufProb` at spBCS's compiled verifier and
knowledge bound (`insiderForgeProb_le_spbcs`), for an oracle-free base signer (`hB`) and an
adversary with the schedule bound `S`, `w`, `P` (`hS`). -/
theorem insiderForgeProb_le_muEufProb_spbcs (hbind : B.BindsRing) (hB : B.OracleFree)
    (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Claim (RingStmt B) M.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B (spbcsProofSystem M Λ E hb honest) adm) n
      (OracleView.queriesOnly _ _) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProb (ringMUForger B (spbcsProofSystem M Λ E hb honest) adm
          (compiledBy_spbcsProofSystem M Λ E hb honest) c₀ (M.dbExtractBitsList Ext) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam B (spbcsProofSystem M Λ E hb honest) adm (max n 2)) 1 Q
          (ringQ' (M.qVerifier Qs b b) Q S w P'
            (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
        (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))) +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (B.qPub + (spbcsProofSystem M Λ E hb honest).q) + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have K := M.knowledgeBound rel Ext St hrbr Qs _ fun _ _ _ hv =>
    queries_length_le_of_formatBounds hb hv
  rw [← coe_comp_dbExtractBitsList] at K
  exact insiderForgeProb_le_muEufProb hbind hB
    (compiledBy_spbcsProofSystem M Λ E hb honest) K hrel c₀ f₀ A hS Q

/-- **The bound of `insiderForgeProb_le_muEufProb_spbcs` with at most `Q` signing and corruption
requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem insiderForgeProb_le_muEufProbWithin_spbcs (hbind : B.BindsRing) (hB : B.OracleFree)
    (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Claim (RingStmt B) M.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B (spbcsProofSystem M Λ E hb honest) adm) n
      (OracleView.queriesOnly _ _) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringMUForger B (spbcsProofSystem M Λ E hb honest) adm
          (compiledBy_spbcsProofSystem M Λ E hb honest) c₀ (M.dbExtractBitsList Ext) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam B (spbcsProofSystem M Λ E hb honest) adm (max n 2)) 1 Q
          (ringQ' (M.qVerifier Qs b b) Q S w P'
            (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
        (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))) Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (B.qPub + (spbcsProofSystem M Λ E hb honest).q) + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have K := M.knowledgeBound rel Ext St hrbr Qs _ fun _ _ _ hv =>
    queries_length_le_of_formatBounds hb hv
  rw [← coe_comp_dbExtractBitsList] at K
  exact insiderForgeProb_le_muEufProbWithin hbind hB
    (compiledBy_spbcsProofSystem M Λ E hb honest) K hrel c₀ f₀ A hS Q

/-- **The key-reuse game for the ring signature compiled by spBCS from MU-EUF-CMA^corr with the
ring-aware and the ordinary signing oracle**:
`keyReuseForgeProb_le_muEufProb` at spBCS's compiled verifier and knowledge bound. -/
theorem keyReuseForgeProb_le_muEufProb_spbcs (hbind : B.BindsRing) (hB : B.OracleFree)
    (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Claim (RingStmt B) M.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B (spbcsProofSystem M Λ E hb honest) adm n
      (OracleView.queriesOnly _ _) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProb (ringMUForger B (spbcsProofSystem M Λ E hb honest) adm
          (compiledBy_spbcsProofSystem M Λ E hb honest) c₀ (M.dbExtractBitsList Ext) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B (spbcsProofSystem M Λ E hb honest) adm (max n 2)) 1 Q
          (ringQ' (M.qVerifier Qs b b) Q S w P'
            (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
        (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))) +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (B.qPub + (spbcsProofSystem M Λ E hb honest).q) + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have K := M.knowledgeBound rel Ext St hrbr Qs _ fun _ _ _ hv =>
    queries_length_le_of_formatBounds hb hv
  rw [← coe_comp_dbExtractBitsList] at K
  exact keyReuseForgeProb_le_muEufProb hbind hB
    (compiledBy_spbcsProofSystem M Λ E hb honest) K hrel c₀ f₀ A hS Q

/-- **The bound of `keyReuseForgeProb_le_muEufProb_spbcs` with at most `Q` signing and corruption
requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem keyReuseForgeProb_le_muEufProbWithin_spbcs (hbind : B.BindsRing) (hB : B.OracleFree)
    (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Claim (RingStmt B) M.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B (spbcsProofSystem M Λ E hb honest) adm n
      (OracleView.queriesOnly _ _) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringMUForger B (spbcsProofSystem M Λ E hb honest) adm
          (compiledBy_spbcsProofSystem M Λ E hb honest) c₀ (M.dbExtractBitsList Ext) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B (spbcsProofSystem M Λ E hb honest) adm (max n 2)) 1 Q
          (ringQ' (M.qVerifier Qs b b) Q S w P'
            (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
        (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))) Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (B.qPub + (spbcsProofSystem M Λ E hb honest).q) + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have K := M.knowledgeBound rel Ext St hrbr Qs _ fun _ _ _ hv =>
    queries_length_le_of_formatBounds hb hv
  rw [← coe_comp_dbExtractBitsList] at K
  exact keyReuseForgeProb_le_muEufProbWithin hbind hB
    (compiledBy_spbcsProofSystem M Λ E hb honest) K hrel c₀ f₀ A hS Q


/-- **The key-reuse game for the ring signature compiled by spBCS from the standard MU-EUF-CMA^corr
game**: the bound of
`keyReuseForgeProb_le_muEufProbWithin_spbcs` with the combined oracle reduced to the ordinary one
(`muEufProbWithin_ringStd_le_std`), for a ring-aware signer signing as the ordinary signer on the
base message (`hstd`), with the same numbers of requests and of signing and corruption requests. -/
@[headline]
theorem keyReuseForgeProb_le_muEufProbWithin_std_spbcs (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Claim (RingStmt B) M.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B (spbcsProofSystem M Λ E hb honest) adm n
      (OracleView.queriesOnly _ _) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringStdToStd 0 (ringMUForger B (spbcsProofSystem M Λ E hb honest) adm
          (compiledBy_spbcsProofSystem M Λ E hb honest) c₀ (M.dbExtractBitsList Ext) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B (spbcsProofSystem M Λ E hb honest) adm (max n 2)) 1 Q
          (ringQ' (M.qVerifier Qs b b) Q S w P'
            (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
          (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
        (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))) Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (B.qPub + (spbcsProofSystem M Λ E hb honest).q) + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  (keyReuseForgeProb_le_muEufProbWithin_spbcs M Λ E hb honest hbind hB hrbr hrel c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ringStd_le_std hstd 0 _ _ _) le_rfl)

/-- **BKM06 Definition 7 for the ring signature compiled by spBCS from the standard MU-EUF-CMA^corr
game**: the bound of
`insiderForgeProb_le_muEufProbWithin_spbcs` with the ring-aware oracle reduced to the ordinary one
(`muEufProbWithin_ring_le_std`), for a ring-aware signer signing as the ordinary signer on the
base message (`hstd`), with the same numbers of requests and of signing and corruption requests. -/
@[headline]
theorem insiderForgeProb_le_muEufProbWithin_std_spbcs (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Claim (RingStmt B) M.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B (spbcsProofSystem M Λ E hb honest) adm) n
      (OracleView.queriesOnly _ _) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringToStd 0 (ringMUForger B (spbcsProofSystem M Λ E hb honest) adm
          (compiledBy_spbcsProofSystem M Λ E hb honest) c₀ (M.dbExtractBitsList Ext) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam B (spbcsProofSystem M Λ E hb honest) adm (max n 2)) 1 Q
          (ringQ' (M.qVerifier Qs b b) Q S w P'
            (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
          (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))))
        (ringQ' (M.qVerifier Qs b b) Q S w P'
          (1 + (B.qPub + (spbcsProofSystem M Λ E hb honest).q))) Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (B.qPub + (spbcsProofSystem M Λ E hb honest).q) + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  (insiderForgeProb_le_muEufProbWithin_spbcs M Λ E hb honest hbind hB hrbr hrel c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ring_le_std hstd 0 _ _ _) le_rfl)

end SPBCS

/-! ### An IOP whose statements verify base signatures -/

namespace Ring.StmtVerifiesRing

open RealizedProgram RealizedProgram.ProofSystem

variable {X₀ W : Type} {rel₀ : Set (X₀ × W)} {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀}
  {SD : C.SimData} {Inp : Type} {relI : Set (X₀ × Inp)} (Hc : C.Honest SD Inp relI)
  {TD : SPBCS.ProofSystemTranscript C} {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {TB : BaseTypes} {B : BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N TB}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] [Inhabited W] [DecidableEq X₀]
  (V₀ : StmtVerifiesRing rel₀ relI B adm)

/-- **BKM06 Definition 7 for the ring signature of an IOP whose statements verify base signatures of
`B`, from MU-EUF-CMA^corr**: `GordieHowe.insiderForgeProb_le_muEufProb`
at the read verifier and its knowledge bound (`StmtVerifiesRing.insiderForgeProb_le`), for an
oracle-free base signer (`hB`) and an adversary with the schedule bound `S`, `w`, `P` (`hS`). -/
theorem insiderForgeProb_le_muEufProb (hbind : B.BindsRing) (hB : B.OracleFree) (Sd : C.Sound)
    {n t : ℕ} (c₀ : RingSignature.RingStmt B × Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B (V₀.proofSystem Hc hb hf) adm) n
      (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProb (ringMUForger B (V₀.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input) c₀
          (extractorList hb V₀) f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam B (V₀.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
            (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
        (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))) +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (B.qPub + (V₀.proofSystem Hc hb hf).q) + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) := by
  have K := knowledgeBound hb hf V₀ Sd
  rw [← coe_comp_extractorList] at K
  exact GordieHowe.insiderForgeProb_le_muEufProb hbind hB _ K
    (fun _ _ h => h) c₀ f₀ A hS Q

/-- **The bound of `insiderForgeProb_le_muEufProb` with at most `Q` signing and corruption
requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem insiderForgeProb_le_muEufProbWithin (hbind : B.BindsRing) (hB : B.OracleFree)
    (Sd : C.Sound)
    {n t : ℕ} (c₀ : RingSignature.RingStmt B × Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B (V₀.proofSystem Hc hb hf) adm) n
      (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringMUForger B (V₀.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input) c₀
          (extractorList hb V₀) f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam B (V₀.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
            (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
        (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (B.qPub + (V₀.proofSystem Hc hb hf).q) + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) := by
  have K := knowledgeBound hb hf V₀ Sd
  rw [← coe_comp_extractorList] at K
  exact GordieHowe.insiderForgeProb_le_muEufProbWithin hbind hB _ K
    (fun _ _ h => h) c₀ f₀ A hS Q

/-- **The key-reuse game for the ring signature of an IOP whose statements verify base signatures
of `B`, from MU-EUF-CMA^corr with the ring-aware and the ordinary signing oracle**:
`GordieHowe.keyReuseForgeProb_le_muEufProb` at the read verifier and its knowledge
bound. -/
theorem keyReuseForgeProb_le_muEufProb (hbind : B.BindsRing) (hB : B.OracleFree) (Sd : C.Sound)
    {n t : ℕ} (c₀ : RingSignature.RingStmt B × Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B (V₀.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProb (ringMUForger B (V₀.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input) c₀
          (extractorList hb V₀) f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B (V₀.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
            (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
        (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))) +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (B.qPub + (V₀.proofSystem Hc hb hf).q) + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) := by
  have K := knowledgeBound hb hf V₀ Sd
  rw [← coe_comp_extractorList] at K
  exact GordieHowe.keyReuseForgeProb_le_muEufProb hbind hB _ K
    (fun _ _ h => h) c₀ f₀ A hS Q

/-- **The bound of `keyReuseForgeProb_le_muEufProb` with at most `Q` signing and corruption
requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem keyReuseForgeProb_le_muEufProbWithin (hbind : B.BindsRing) (hB : B.OracleFree)
    (Sd : C.Sound)
    {n t : ℕ} (c₀ : RingSignature.RingStmt B × Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B (V₀.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringMUForger B (V₀.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input) c₀
          (extractorList hb V₀) f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B (V₀.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
            (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
        (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (B.qPub + (V₀.proofSystem Hc hb hf).q) + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) := by
  have K := knowledgeBound hb hf V₀ Sd
  rw [← coe_comp_extractorList] at K
  exact GordieHowe.keyReuseForgeProb_le_muEufProbWithin hbind hB _ K
    (fun _ _ h => h) c₀ f₀ A hS Q


/-- **The key-reuse game for the ring signature of an IOP whose statements verify base signatures
from the standard MU-EUF-CMA^corr game**: the bound of
`keyReuseForgeProb_le_muEufProbWithin` with the combined oracle reduced to the ordinary one
(`muEufProbWithin_ringStd_le_std`), for a ring-aware signer signing as the ordinary signer on the
base message (`hstd`), with the same numbers of requests and of signing and corruption requests. -/
@[headline]
theorem keyReuseForgeProb_le_muEufProbWithin_std (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (Sd : C.Sound)
    {n t : ℕ} (c₀ : RingSignature.RingStmt B × Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B (V₀.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringStdToStd 0 (ringMUForger B (V₀.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input) c₀
          (extractorList hb V₀) f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B (V₀.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
            (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
        (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (B.qPub + (V₀.proofSystem Hc hb hf).q) + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  (keyReuseForgeProb_le_muEufProbWithin Hc hb hf V₀ hbind hB Sd c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ringStd_le_std hstd 0 _ _ _) le_rfl)

/-- **BKM06 Definition 7 for the ring signature of an IOP whose statements verify base signatures
from the standard MU-EUF-CMA^corr game**: the bound of
`insiderForgeProb_le_muEufProbWithin` with the ring-aware oracle reduced to the ordinary one
(`muEufProbWithin_ring_le_std`), for a ring-aware signer signing as the ordinary signer on the
base message (`hstd`), with the same numbers of requests and of signing and corruption requests. -/
@[headline]
theorem insiderForgeProb_le_muEufProbWithin_std (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (Sd : C.Sound)
    {n t : ℕ} (c₀ : RingSignature.RingStmt B × Claim X₀ (TD.setting kS hb).model.NIProof)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B (V₀.proofSystem Hc hb hf) adm) n
      (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringToStd 0 (ringMUForger B (V₀.proofSystem Hc hb hf) adm
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input) c₀
          (extractorList hb V₀) f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam B (V₀.proofSystem Hc hb hf) adm (max n 2)) 1 Q
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
            (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
          (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))))
        (ringQ' (verifier hb (pB := pB) V₀) Q S w P
          (1 + (B.qPub + (V₀.proofSystem Hc hb hf).q))) Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (B.qPub + (V₀.proofSystem Hc hb hf).q) + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  (insiderForgeProb_le_muEufProbWithin Hc hb hf V₀ hbind hB Sd c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ring_le_std hstd 0 _ _ _) le_rfl)

end Ring.StmtVerifiesRing

end GordieHowe
