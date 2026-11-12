-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.ProgramBase
public import GordieHowe.Applications.Ring.RingUnforgeability
public import GordieHowe.Model.NARG.VerifierComap

@[expose] public section

/-!
# Ring signatures from a compiled IOP over its own statements and a base signer

The program form (the paper's Theorem 5.2, `thm:backend`) of the ring signature
`ofBase B PS adm` (`GordieHowe/Model/RingSignature/Base.lean`) for a multi-circuit IOP with forked
domains `C` over statements `X₀` that do not depend on the oracle, at a transcript `TD` of `C`
(the transcript writes the statement `X₀`): ring statements of `B` are read as statements of `C`
and the proof system is spBCS at `TD` read at ring statements (`spbcsComapProofSystem`). The base
signer's oracle is the compiled oracle of `TD`, so `B` is chosen after `TD`.
`GordieHowe/Applications/Ring/ProgramBase.lean` is the case of the program's statements
(`BaseVerifiesRing`); a configuration whose transcript writes its own ring statements (the Falcon
rings') is the case `X₀` = those statements.

- `ringRelAll B adm`: the ring relation at every oracle; `ringRel_of_mem_ringRelAll`: its pairs
  are in the ring relation at every oracle; `StmtVerifiesRing.mem_ringRelAll`: a sound witness
  gives a pair of it.
- `StmtVerifiesRing rel relH B adm`: statements `X₀` with the relation `rel` verify base
  signatures of `B` for the ring relation `ringRel B adm H` at every oracle `H`: a statement map,
  a statement check, a witness map (soundness at every oracle), and a partial map of ring
  witnesses to honest inputs, defined on the ring relation (the honest direction).
  `StmtVerifiesRing.ofVerifiesWithoutOracle`: for a base signer whose verification and public value
  read no oracle, the conditions at one oracle suffice. `BaseVerifiesRing.toStmt`: a program
  verifying base signatures, at the IOP's relation `relOf rel` and the witness read at the
  statement.
- `StmtVerifiesRing.proofSystem V Hc hb hf`: the proof system (spBCS at the setting with merges of
  `TD`, the honest prover `Hc` of `C`, proofs in the format `pB`).
  `StmtVerifiesRing.proofSystem_completeWithin`: it is adaptively complete for the ring relation at
  the honest prover's completeness error `errc`.
- `compiledBy_spbcsComapProofSystem`: the comap proof system is given by its compiled verifier read
  at ring statements (`NARG.Verifier.comap`). `StmtVerifiesRing.verifier`,
  `StmtVerifiesRing.extractor`: that verifier and the extractor of ring witnesses.
  `StmtVerifiesRing.knowledgeBound`: the knowledge bound of that verifier for the ring relation at
  every oracle (`ringRelAll`), from causal round-by-round knowledge soundness of `C`
  (`IOP.Sound.causal_rbr`) and the soundness map.
- Headlines: `StmtVerifiesRing.completeWithin`, `StmtVerifiesRing.completeAtWithin` (completeness,
  refusal and rejection separate, for an honest prover with completeness error `errc`).
- `StmtVerifiesRing.insiderForgeProb_le`, `StmtVerifiesRing.jointForgeProb_le` (BKM06
  Definition 7 and joint-security unforgeability for a ring-binding base message, by knowledge
  soundness: the extraction forger's success plus spBCS's knowledge error at the largest round
  error of `C`). Their forms by MU-EUF-CMA^corr are the headlines
  (`StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin`,
  `StmtVerifiesRing.jointForgeProb_le_muEufProbWithin`).
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature
open scoped NNReal ENNReal

/-- **Statements `X₀` with the relation `rel` verify base signatures of `B` for the ring relation**
`RingSignature.ringRel B adm H` at every oracle `H` (BKM06 Definition 1, ePrint 2005/304, p. 3,
with `Vrfy_R(M, σ)` the verifier on the statement of `(R, M, y)`): for honest inputs `relH`, a map
`stmt` of ring statements to statements and a statement check `check`, with

* soundness: a witness of `rel` at the statement of a checked ring statement gives a ring witness
  (`wit`) at every oracle;
* the honest direction: at every oracle, the statements of the ring relation pass the check, and a
  ring witness has an honest input (`input`, defined on the ring relation) at the statement. -/
structure StmtVerifiesRing {X₀ W Inp : Type} (rel : Set (X₀ × W)) (relH : Set (X₀ × Inp))
    {Xo Yo : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
    (B : BaseSigner Xo Yo N T RMsg) (adm : KeyRing B.PK N → Prop) where
  /-- The statement of a ring statement. -/
  stmt : RingSignature.RingStmt B → X₀
  /-- The check of a ring statement. -/
  check : RingSignature.RingStmt B → Bool
  /-- The ring witness of a witness of the relation. -/
  wit : RingSignature.RingStmt B → W → RingSignature.RingWit B
  /-- A witness of the relation at a checked statement gives a ring witness. -/
  sound : ∀ (H : Xo → Yo) x w, check x = true → (stmt x, w) ∈ rel → (x, wit x w) ∈ RingSignature.ringRel B adm H
  /-- The honest input of a ring statement and a ring witness, if any. -/
  input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Inp
  /-- The statements of the ring relation pass the check. -/
  check_eq_true : ∀ (H : Xo → Yo) x w, (x, w) ∈ RingSignature.ringRel B adm H → check x = true
  /-- A ring witness has an honest input. -/
  input_mem : ∀ (H : Xo → Yo) x w, (x, w) ∈ RingSignature.ringRel B adm H → ∃ y ∈ input x w, (stmt x, y) ∈ relH

namespace StmtVerifiesRing

/-- **For a base signer verifying without the oracle, the conditions at one oracle suffice**: the
ring relation is the same at every oracle (`VerifiesWithoutOracle.ringRel_eq`). -/
def ofVerifiesWithoutOracle {X₀ W Inp : Type} {rel : Set (X₀ × W)} {relH : Set (X₀ × Inp)}
    {Xo Yo : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
    {B : BaseSigner Xo Yo N T RMsg} {adm : KeyRing B.PK N → Prop}
    (hB : B.VerifiesWithoutOracle) (H₀ : Xo → Yo) (stmt : RingSignature.RingStmt B → X₀)
    (check : RingSignature.RingStmt B → Bool) (wit : RingSignature.RingStmt B → W → RingSignature.RingWit B)
    (sound : ∀ x w, check x = true → (stmt x, w) ∈ rel → (x, wit x w) ∈ RingSignature.ringRel B adm H₀)
    (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Inp)
    (check_eq_true : ∀ x w, (x, w) ∈ RingSignature.ringRel B adm H₀ → check x = true)
    (input_mem : ∀ x w, (x, w) ∈ RingSignature.ringRel B adm H₀ → ∃ y ∈ input x w, (stmt x, y) ∈ relH) :
    StmtVerifiesRing rel relH B adm where
  stmt := stmt
  check := check
  wit := wit
  sound H x w hx hw := by
    rw [← hB.ringRel_eq adm H₀ H]
    exact sound x w hx hw
  input := input
  check_eq_true H x w h := check_eq_true x w (by rw [hB.ringRel_eq adm H₀ H]; exact h)
  input_mem H x w h := input_mem x w (by rw [hB.ringRel_eq adm H₀ H]; exact h)

/-- **A sound witness gives a ring witness at every oracle.** -/
theorem mem_ringRelAll {X₀ W Inp : Type} {rel : Set (X₀ × W)} {relH : Set (X₀ × Inp)}
    {Xo Yo : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
    {B : BaseSigner Xo Yo N T RMsg} {adm : KeyRing B.PK N → Prop}
    (V : StmtVerifiesRing rel relH B adm) (x : RingSignature.RingStmt B) (w : W) (hx : V.check x = true)
    (hw : (V.stmt x, w) ∈ rel) : (x, V.wit x w) ∈ ringRelAll B adm :=
  fun H => V.sound H x w hx hw

end StmtVerifiesRing

/-- **A program verifying base signatures, at the relation of its IOP**: statements the program's,
the relation `relOf rel` (a witness function read at the statement), the witness `V.wit x (f
(V.stmt x))`, and the honest input `V.input x w`. -/
def BaseVerifiesRing.toStmt {ir : RealizedProgram} {I : RealizedProgram.Interp} {W : Type}
    {rel : Set (ir.Valuation I × W)} {Inp : Type} {relH : Set (ir.Valuation I × Inp)} {Xo Yo : Type}
    {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
    {B : BaseSigner Xo Yo N T RMsg} {adm : KeyRing B.PK N → Prop}
    (V : BaseVerifiesRing ir I rel relH B adm) : StmtVerifiesRing (relOf rel) relH B adm where
  stmt := V.stmt
  check := V.check
  wit x f := V.wit x (f (V.stmt x))
  sound H x _ hx hf := V.sound H x _ hx hf
  input := V.input
  check_eq_true := V.check_eq_true
  input_mem := V.input_mem

/-! ### The comap proof system is given by its compiled verifier -/

section CompiledBy

open SPTerm

variable {k kN kS L e N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N T RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀) (stmt : RingSignature.RingStmt B → X₀) (check : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)

/-- **The spBCS proof system read at ring statements is given by its compiled verifier read at
ring statements** (`NARG.Verifier.comap` of `M.qVerifier Qs b b`), with the claims
`(x, c)` for `c` the claim `spbcsComapClaim M stmt x π`. -/
def compiledBy_spbcsComapProofSystem :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).CompiledBy
      (NARG.Verifier.comap (M.qVerifier Qs b b) stmt check) where
  claim x π := (spbcsComapClaim M stmt x π).map (Prod.mk x)
  stmt_eq x π c hc := by
    obtain ⟨c', -, rfl⟩ := Option.mem_map.1 hc
    rfl
  accepted_of_verify H x π h := by
    obtain ⟨hx, c, hc, hacc⟩ :=
      (verify_spbcsComapProofSystem_eq_true_iff M Λ E hb honest stmt check input H x π).1 h
    exact ⟨(x, c), Option.mem_map_of_mem _ hc,
      (NARG.Verifier.accepted_comap_iff _ stmt check _ x c).2
        ⟨hx, stmt_of_mem_spbcsComapClaim M stmt hc, hacc⟩⟩

end CompiledBy

/-! ### The proof system at a transcript of an IOP over its own statements -/

namespace StmtVerifiesRing

variable {X₀ W : Type} {rel₀ : Set (X₀ × W)} {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀}
  {SD : C.SimData} {Inp : Type} {relI : Set (X₀ × Inp)} (Hc : C.Honest SD Inp relI)
  {TD : SPBCS.ProofSystemTranscript C} {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
    (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N T RMsg}
  {adm : KeyRing B.PK N → Prop} {W' : Type} {rel : Set (X₀ × W')}
  (V : StmtVerifiesRing rel relI B adm)

/-- **The proof system of `C` for the ring relation**: spBCS at the setting with merges of the
transcript `TD` (`spbcsComapProofSystem`), the honest prover `Hc` of `C`
(`RealizedProgram.ProofSystem.IOP.honest`) on the honest input of a ring witness at the statement
`V.stmt x`, proofs in the format `pB`, verification after the check `V.check`. -/
noncomputable abbrev proofSystem :
    RingSignature.ProofSystem (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))
      (RingSignature.RingStmt B) (RingSignature.RingWit B)
      (transcriptPST TD kS hb pB Hc.Coins) :=
  spbcsComapProofSystem (TD.setting kS hb).model (TD.setting kS hb).layout
    (TD.setting kS hb).encoder hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt V.check
    V.input

/-- **The proof system is adaptively complete for the ring relation**, at the completeness error
`errc` of the honest prover (`hE`). -/
theorem proofSystem_completeWithin {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) :
    (V.proofSystem Hc hb hf).CompleteWithin (RingSignature.ringRel B adm) fun T =>
      (errc : ℝ≥0∞) + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision (C.term.size C.rounds) TD.k + T / 2 ^ (8 * kS) :=
  spbcsComapProofSystem_completeWithin _ _ _ hf _ _ _ _ adm (TD.setting kS hb).viewEncoder
    (rel₀ := fun x y => (x, y) ∈ relI)
    (fun H p hp => ⟨V.check_eq_true H p.1 p.2 hp, V.input_mem H p.1 p.2 hp⟩)
    fun x y hy => ROM.probUniform_prod_le fun c =>
      RealizedProgram.ProofSystem.IOP.completeness_of_errorBound Hc hE c x y hy

variable [DecidablePred adm]

variable [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [Nonempty T.Coins]

/-- **Completeness of the ring signature of an IOP whose statements verify base signatures of
`B`** (BKM06 Definition 1 with errors, averaged over honest rings): for an honest prover of `C`
with completeness error `errc` (`hE`), a base signer with refusal rate `ρ` on honest rings (`hρ`)
and correctness error `εc` (`hc`), the ring signature `ofBase B (V.proofSystem Hc hb hf) adm`
refuses an honest supported ring with probability at most `ρ` and is rejected with probability at
most `εc + errc` plus spBCS's overrun and key-collision terms and `(q + qPub) / 2^(8 kS)`. -/
@[headline]
theorem completeWithin {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) {ρ εc : ℝ≥0∞}
    (hρ : B.RefuseWithin adm ρ) (hc : B.CorrectWithin εc) :
    (ofBase B (V.proofSystem Hc hb hf) adm).CompleteWithin ρ
      (εc + (TD.setting kS hb).model.ringCompletenessError errc (B.q + B.qPub)) :=
  completeWithin_ofBase B _ adm hρ hc (V.proofSystem_completeWithin Hc hb hf hE)

omit [Fintype T.KeyCoins] [Nonempty T.KeyCoins] in
/-- **Completeness per key of the ring signature of an IOP whose statements verify base signatures
of `B`**: as `completeWithin`, with the per-key refusal rate `ρ` (`RefuseAtWithin`), at every key
and every supported ring holding it. -/
@[headline]
theorem completeAtWithin {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) {ρ εc : ℝ≥0∞}
    (hρ : B.RefuseAtWithin adm ρ) (hc : B.CorrectWithin εc) :
    (ofBase B (V.proofSystem Hc hb hf) adm).CompleteAtWithin ρ
      (εc + (TD.setting kS hb).model.ringCompletenessError errc (B.q + B.qPub)) :=
  completeAtWithin_ofBase B _ adm hρ hc (V.proofSystem_completeWithin Hc hb hf hE)

/-! ### Knowledge soundness -/

variable [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BMsg]
  [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub]
  [DecidableEq T.Pub] [DecidableEq T.KeyCoins] [DecidableEq T.Coins]

variable [Inhabited W] [DecidableEq X₀] (V₀ : StmtVerifiesRing rel₀ relI B adm)

omit [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [Nonempty T.Coins] in
/-- **The compiled verifier of the proof system, read at ring statements** (`NARG.Verifier.comap`
of spBCS's verifier at the setting with merges of `TD`, proofs in the format `pB`). -/
abbrev verifier :=
  NARG.Verifier.comap ((TD.setting kS hb).model.qVerifier (TD.setting kS hb).queries pB pB)
    V₀.stmt V₀.check

omit [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [Nonempty T.Coins] in
/-- **The extractor of ring witnesses**: spBCS's database extractor at the extractor of `C`
(`RealizedProgram.ProofSystem.IOP.extractor`) on the statement `V₀.stmt x`, its witnesses read by
`V₀.wit x`.

Running time: one run of `SPBCS.dbExtractBits` (its paragraph) and one application of `V₀.stmt`
and of `V₀.wit` per witness. This running time is argued here, not proved in Lean. -/
abbrev extractor (x : RingSignature.RingStmt B)
    (D : DB (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (Out TD.k (Configurations.fsExtraBytes + TD.maxGrant))) :
    Multiset (RingSignature.RingWit B) :=
  ((TD.setting kS hb).model.dbExtractBits C.extractor (V₀.stmt x) D).map (V₀.wit x)

omit [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [Nonempty T.Coins] in
/-- **The extractor of ring witnesses as a list**: `extractor` with the list extractor
`SPBCS.dbExtractBitsList` (the database's entries in the lexicographic order of their inputs).

Running time: one run of `SPBCS.dbExtractBitsList` (its paragraph) and one application of
`V₀.stmt` and of `V₀.wit` per witness. This running time is argued here, not proved in Lean. -/
abbrev extractorList (x : RingSignature.RingStmt B)
    (D : DB (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
      (Out TD.k (Configurations.fsExtraBytes + TD.maxGrant))) :
    List (RingSignature.RingWit B) :=
  ((TD.setting kS hb).model.dbExtractBitsList C.extractor (V₀.stmt x) D).map (V₀.wit x)

omit [DecidablePred adm] [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins]
  [Fintype T.Coins] [Nonempty T.Coins] [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg]
  [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub]
  [DecidableEq T.Pub] [DecidableEq T.KeyCoins] [DecidableEq T.Coins] in
/-- **The list extractor read as multisets is `extractor`.** -/
theorem coe_comp_extractorList :
    (fun x D => (extractorList hb V₀ x D : Multiset (RingSignature.RingWit B))) =
      extractor hb V₀ := by
  funext x D
  rw [extractorList, extractor, ← Multiset.map_coe]
  exact congrArg _ (SPBCS.coe_dbExtractBitsList _ _ _ _)

omit [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [Nonempty T.Coins] in
/-- **The knowledge bound of the read verifier for the ring relation at every oracle**
(`ringRelAll`): spBCS's knowledge bound (`SPBCS.knowledgeBound`, CMS19 Proposition 8.12 and Lemmas
5.9–5.10) from causal round-by-round knowledge soundness of `C` (`IOP.Sound.causal_rbr` of `Sd`),
read at ring statements (`KnowledgeBound.comap`) through the soundness map of `V₀`. -/
noncomputable def knowledgeBound (Sd : C.Sound) :
    NARG.QROM.Verifier.KnowledgeBound (verifier hb (pB := pB) V₀) (ringRelAll B adm)
      (extractor hb V₀) ((TD.setting kS hb).model.dbBound Sd.error) :=
  ((TD.setting kS hb).model.knowledgeBound rel₀ C.extractor Sd.stateFn Sd.causal_rbr
    (TD.setting kS hb).queries _ fun _ _ _ hv => queries_length_le_of_formatBounds hf hv).comap
      V₀.stmt V₀.check (ringRelAll B adm) V₀.wit V₀.mem_ringRelAll

omit [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
of an IOP whose statements verify base signatures of `B`, for a ring-binding base message**, by
knowledge soundness: for a base message that binds the ring (`hbind`) and the soundness data `Sd`
of `C` (causal round-by-round knowledge soundness, the paper's Theorem 5.2), the forgery
probability of an adversary of BKM06 Definition 7 against `ofBase B (V₀.proofSystem Hc hb hf) adm`
(start input the honest public keys, the oracle by at most `t` queries, `Q` requests) is at most
the success probability of the extraction forger in MU-EUF-CMA^corr with the ring-aware signing
oracle (`extractionSuccess` of `insiderRelay`, at the extractor `extractor`) plus spBCS's knowledge
error at the largest round error of `C` and `t + Q · q + kq` queries (`q` the ring signer's query
bound, `kq = kqOf C.merges C.rounds pB pB`). -/
theorem insiderForgeProb_le (hbind : B.BindsRing) (Sd : C.Sound) {n t : ℕ}
    (A : InsiderAdversary (ofBase B (V₀.proofSystem Hc hb hf) adm) n
      (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      extractionSuccess (insiderRelay B _ adm) A Q
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input)
          (extractor hb V₀) +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (ofBase B (V₀.proofSystem Hc hb hf) adm).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  insiderForgeProb_le_of_knowledgeBound hbind _ (knowledgeBound hb hf V₀ Sd)
    (fun _ _ h => h) A Q

/-- **Joint-security unforgeability of the ring signature of an IOP whose statements verify base
signatures of `B`, for a ring-binding base message**: the bound of `insiderForgeProb_le` for the
joint-security game, the extraction forger in MU-EUF-CMA^corr with the ring-aware and the ordinary
signing oracle (`jointRelay`). -/
theorem jointForgeProb_le (hbind : B.BindsRing) (Sd : C.Sound) {n t : ℕ}
    (A : JointAdversary B (V₀.proofSystem Hc hb hf) adm n (OracleView.queriesOnly _ _) t)
    (Q : ℕ) :
    jointForgeProb A Q ≤
      extractionSuccess (jointRelay B _ adm) A Q
          (compiledBy_spbcsComapProofSystem _ _ _ hf _ V₀.stmt V₀.check V₀.input)
          (extractor hb V₀) +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (ofBase B (V₀.proofSystem Hc hb hf) adm).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  jointForgeProb_le_of_knowledgeBound hbind _ (knowledgeBound hb hf V₀ Sd)
    (fun _ _ h => h) A Q

end StmtVerifiesRing

end GordieHowe.Ring
