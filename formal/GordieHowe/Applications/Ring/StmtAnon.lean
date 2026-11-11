-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.StmtBase
public import GordieHowe.Applications.Ring.SPBCSAnon
public import GordieHowe.Headline

@[expose] public section

/-!
# Anonymity of the ring signature of a compiled IOP over its own statements

The program form (the paper's Theorem 5.2) of the anonymity theorems of
`GordieHowe/Applications/Ring/RingAnonymity.lean`, for the proof system
`StmtVerifiesRing.proofSystem` of `GordieHowe/Applications/Ring/StmtBase.lean` (spBCS at a
transcript of a multi-circuit IOP `C`, read at ring statements).

- `proofLaw_spbcsComapProofSystem_of_input`: the law of a proof of the comap proof system with an
  honest input is the spBCS proof law at the statement `stmt x` and that input, each proof in the
  format.
- `pubWI_spbcsComapProofSystem`: its witness indistinguishability with public outputs at error
  `wiError δ`, for a relation whose pairs have honest inputs in a relation at which the composite has
  honest-verifier zero knowledge at error `δ` (`pubWI_proofLaw_comap`, `PubWI.congr_rel`).
- `StmtVerifiesRing.pubWI_proofSystem`: for the proof system of `C`, at the honest prover's
  completeness error `errc` (zero knowledge by `RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound`).
- Headlines `StmtVerifiesRing.anonAdvantage_le`, `StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins`,
  `StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins_avg` (at the averaged refusal rate
  `RefuseAvgWithin`): anonymity of `ofBase B (V.proofSystem Hc hb hf) adm` for an oracle-free base
  signer;
  `StmtVerifiesRing.anonAdvantage_le_split` (with `pubWI_spbcsComapProofSystem_split`): for a base
  signer reading only the oracle off the compiled proofs' queries.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature SPTerm
open scoped NNReal ENNReal BigOperators

/-! ### The comap proof system -/

section Comap

variable {k kN kS L e N : ℕ} {TB : BaseTypes}
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀) (stmt : RingSignature.RingStmt B → X₀)
  (check : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The law of a proof of the comap proof system with an honest input `y`** is the spBCS proof
law at `chainOracle H`, the statement `stmt x` and the input `y`, each proof in the format. -/
theorem proofLaw_spbcsComapProofSystem_of_input (VE : M.ViewEncoder E Qs)
    (H : Bits (queryBits k kN kS L) → XOut k e) (x : RingSignature.RingStmt B)
    (w : RingSignature.RingWit B) {y : Wit₀} (hy : input x w = some y) :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).proofLaw H x w =
      (proofLaw E Qs (chainOracle H) (stmt x) (honest y)).map (toResponse M) := by
  let φ : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) ≃
      FiatShamirSalt kS × R × (M.Pos → MerkleSalt kN) :=
    (SaltedCoins.equivProd _ _).trans (Equiv.prodCongr (Equiv.refl _) (ProverCoins.equivProd M R))
  rw [proofLaw, ← PMF.map_uniformOfFintype_equiv φ, PMF.map_comp, PMF.map_comp]
  change (PMF.uniformOfFintype (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))).map _ = _
  congr 1
  funext a
  obtain ⟨p, hp, hp1⟩ := run_prove_spbcsComapProofSystem M Λ E hb honest stmt check input VE H x w
    hy a
  change ((spbcsComapProofSystem M Λ E hb honest stmt check input).prove x w a).run H =
    toResponse M (prove (honest y a.coins.iop) (stmt x) a.salt E a.coins.merkleSalts
      (chainOracle H) (Qs (stmt x)))
  rw [hp, ← hp1, toResponse, dite_eq_left p.2]
  rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **Witness indistinguishability with public outputs of the comap proof system** at error
`wiError δ`: for a relation `rel` whose pairs have honest inputs in `rel₀` (`hrel`) at which the
composite's honest prover has honest-verifier zero knowledge at error `δ` (`hz`, what the proof
reveals read off the view by `VE`). -/
theorem pubWI_spbcsComapProofSystem (VE : M.ViewEncoder E Qs) {rel₀ : Set (X₀ × Wit₀)}
    {PubZ : Type} {pubZ : X₀ → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ} {δ : ℝ≥0}
    (hz : CausalHVZK VE.toReveal.MV rel₀ honest pubZ sim δ)
    {rel : Set (RingSignature.RingStmt B × RingSignature.RingWit B)}
    (hrel : ∀ x w, (x, w) ∈ rel → ∃ y ∈ input x w, (stmt x, y) ∈ rel₀) :
    PubWI (spbcsComapProofSystem M Λ E hb honest stmt check input).proofLaw
      RingSignature.RingStmtOf.pub rel (M.wiError δ) := by
  rcases isEmpty_or_nonempty Wit₀ with hW | ⟨⟨y₀⟩⟩
  · refine PubWI.of_forall_not_mem (fun p hp => ?_) fun c => SPBCS.wiError_nonneg δ c
    obtain ⟨y, -, -⟩ := hrel p.1 p.2 hp
    exact hW.false y
  let ι' : RingSignature.RingStmt B → RingSignature.RingWit B → Wit₀ := fun x w =>
    (input x w).getD y₀
  have hlaw : PubWI (fun H x w => (proofLaw E Qs (chainOracle H) (stmt x) (honest (ι' x w))).map
      (toResponse M (b := b))) RingSignature.RingStmtOf.pub rel (M.wiError δ) := by
    refine PubWI.of_split chainSplit
      (law₁ := fun h x w => (proofLaw E Qs h (stmt x) (honest (ι' x w))).map (toResponse M (b := b)))
      (fun ω₂ h₁ => by rw [← chainSplit_snd, Equiv.apply_symm_apply]) ?_
    refine PubWI.map_proof ?_ (toResponse M)
    exact pubWI_proofLaw_comap stmt ι' RingSignature.RingStmtOf.pub honest VE.toReveal hz
      fun x w hxw => by
        obtain ⟨y, hy, hy₀⟩ := hrel x w hxw
        simp only [ι', Option.mem_def] at hy ⊢
        rw [hy]
        exact hy₀
  refine hlaw.congr_rel fun H x w hxw => ?_
  obtain ⟨y, hy, -⟩ := hrel x w hxw
  rw [proofLaw_spbcsComapProofSystem_of_input M Λ E hb honest stmt check input VE H x w hy]
  simp only [ι', Option.mem_def] at hy ⊢
  rw [hy]
  rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **Witness indistinguishability of the comap proof system at the oracles with a fixed off-query
part** `ω₂`, under the hypotheses of `pubWI_spbcsComapProofSystem`. -/
theorem pubWI_spbcsComapProofSystem_split (VE : M.ViewEncoder E Qs) {rel₀ : Set (X₀ × Wit₀)}
    {PubZ : Type} {pubZ : X₀ → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ} {δ : ℝ≥0}
    (hz : CausalHVZK VE.toReveal.MV rel₀ honest pubZ sim δ)
    {rel : Set (RingSignature.RingStmt B × RingSignature.RingWit B)}
    (hrel : ∀ x w, (x, w) ∈ rel → ∃ y ∈ input x w, (stmt x, y) ∈ rel₀)
    (ω₂ : {x // x ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L))} → XOut k e) :
    PubWI (fun h => (spbcsComapProofSystem M Λ E hb honest stmt check input).proofLaw
      (chainSplit.symm (ω₂, h))) RingSignature.RingStmtOf.pub rel (M.wiError δ) := by
  rcases isEmpty_or_nonempty Wit₀ with hW | ⟨⟨y₀⟩⟩
  · refine PubWI.of_forall_not_mem (fun p hp => ?_) fun c => SPBCS.wiError_nonneg δ c
    obtain ⟨y, -, -⟩ := hrel p.1 p.2 hp
    exact hW.false y
  let ι' : RingSignature.RingStmt B → RingSignature.RingWit B → Wit₀ := fun x w =>
    (input x w).getD y₀
  have hlaw : PubWI (fun h x w => (proofLaw E Qs h (stmt x) (honest (ι' x w))).map
      (toResponse M (b := b))) RingSignature.RingStmtOf.pub rel (M.wiError δ) := by
    refine PubWI.map_proof ?_ (toResponse M)
    exact pubWI_proofLaw_comap stmt ι' RingSignature.RingStmtOf.pub honest VE.toReveal hz
      fun x w hxw => by
        obtain ⟨y, hy, hy₀⟩ := hrel x w hxw
        simp only [ι', Option.mem_def] at hy ⊢
        rw [hy]
        exact hy₀
  refine hlaw.congr_rel fun h x w hxw => ?_
  obtain ⟨y, hy, -⟩ := hrel x w hxw
  rw [proofLaw_spbcsComapProofSystem_of_input M Λ E hb honest stmt check input VE _ x w hy,
    ← chainSplit_snd, Equiv.apply_symm_apply]
  simp only [ι', Option.mem_def] at hy ⊢
  rw [hy]
  rfl

end Comap

/-! ### The proof system of a compiled IOP over its own statements -/

namespace StmtVerifiesRing

variable {X₀ W : Type} {rel₀ : Set (X₀ × W)} {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀}
  {SD : C.SimData} {Inp : Type} {relI : Set (X₀ × Inp)} (Hc : C.Honest SD Inp relI)
  {TD : SPBCS.ProofSystemTranscript C} {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {TB : BaseTypes}
  {B : BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N TB}
  {adm : KeyRing B.PK N → Prop} {W' : Type} {rel : Set (X₀ × W')}
  (V : StmtVerifiesRing rel relI B adm)

/-- **Witness indistinguishability with public outputs of the proof system of `C`** for the ring
relation at every oracle, at error `wiError errc` for an honest prover with completeness error
`errc` (`hE`; zero knowledge by `RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound`). -/
theorem pubWI_proofSystem {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    (H : Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)) →
      XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) :
    PubWI (V.proofSystem Hc hb hf).proofLaw RingSignature.RingStmtOf.pub
      (RingSignature.ringRel B adm H) ((TD.setting kS hb).model.wiError errc) :=
  pubWI_spbcsComapProofSystem _ _ _ hf _ _ _ _ (TD.setting kS hb).viewEncoder
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) fun x w h => V.input_mem H x w h

variable [DecidablePred adm] {n : ℕ}

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

/-- **Anonymity of the ring signature of a compiled IOP over its own statements** (the program
form, Theorem 5.2, of `anonAdvantage_ofBase_le`; BKM06 Definition 4 with `Q` adaptive challenges,
`GordieHowe/Model/RingSignature/Anonymity.lean`): for statements verifying base signatures of an
oracle-free base signer (`V`, `hB`), an honest prover with completeness error `errc` (`hE`), at
most `C'` valid challenges for every key vector (`hC`), an `ε keys` bounding at the good key vectors
the distance of the two users' refusal-or-public value laws (`hε`) and correctness error `εc`
(`hcorr`), every anonymity adversary with any oracle view and query bound has advantage at most
`Q · (𝔼 ε + 2εc) + Q · wiError errc (Q · C') + Pr[¬ Good]`. -/
@[headline]
theorem anonAdvantage_le {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (hB : B.OracleFree)
    {C' : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B (V.proofSystem Hc hb hf) adm) n =>
        c.Valid keys).card ≤ C')
    (Good : (Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins) → Prop) [DecidablePred Good]
    (ε : (Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins) → ℝ) (hε0 : ∀ keys, 0 ≤ ε keys)
    (hε : ∀ keys, Good keys →
      ∀ H (c : AnonRequest (ofBase B (V.proofSystem Hc hb hf) adm) n), c.Valid keys → adm c.ring →
        PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
          (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε keys)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc)
    {Vw : OracleView (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
      (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))} {t : ℕ}
    (A : AnonAdversary (ofBase B (V.proofSystem Hc hb hf) adm) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * ((𝔼 keys, ε keys) + 2 * εc) +
      Q * (TD.setting kS hb).model.wiError errc (Q * C') +
        𝔼 keys, (if Good keys then 0 else 1 : ℝ) :=
  anonAdvantage_ofBase_le hB (V.pubWI_proofSystem Hc hb hf hE) hC Good ε hε0 hε hcorr A Q

/-- **Anonymity of the ring signature of a compiled IOP over its own statements when the public
value is a function of the signing coins** (`hpub`: a salt read off the coins, or `Pub = Unit`; the
program form of `anonAdvantage_ofBase_le_of_pubOfCoins`): for statements verifying base signatures
of an oracle-free base signer (`V`, `hB`), an honest prover with completeness error `errc` (`hE`),
at most `C'` valid challenges for every key vector (`hC`), correctness error `εc` (`hcorr`) and a
bound `ρ` on the base signer's refusal probability at every key and every ring holding it (`hρ`),
every anonymity adversary with any oracle view and query bound has advantage at most
`Q · wiError errc (Q · C') + 2Q · εc + 2Q · ρ`. -/
@[headline]
theorem anonAdvantage_le_of_pubOfCoins {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    (hB : B.OracleFree) {C' : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B (V.proofSystem Hc hb hf) adm) n =>
        c.Valid keys).card ≤ C')
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {εc ρ : ℝ≥0} (hcorr : B.CorrectWithin εc)
    (hρ : ∀ H (kc : B.KeyCoins) (Rg : KeyRing B.PK N) (m : B.Msg), B.pk kc ∈ Rg.1 →
      Pr[cb ~ PMF.uniformOfFintype B.Coins :
        (B.bsign (B.sk kc) Rg (Rg.1.idxOf (B.pk kc)) m cb).run H = none] ≤ ρ)
    {Vw : OracleView (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
      (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))} {t : ℕ}
    (A : AnonAdversary (ofBase B (V.proofSystem Hc hb hf) adm) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * (TD.setting kS hb).model.wiError errc (Q * C') + 2 * Q * εc +
      2 * Q * ρ :=
  anonAdvantage_ofBase_le_of_pubOfCoins hB (V.pubWI_proofSystem Hc hb hf hE) hC hpub hcorr hρ A Q

/-- **Anonymity of the ring signature of a compiled IOP over its own statements when the public
value is a function of the signing coins, at the refusal rate averaged over the keys** (the program
form of `anonAdvantage_ofBase_le_of_pubOfCoins_avg`): as `anonAdvantage_le_of_pubOfCoins`, with an
averaged refusal rate at most `ρ` on the supported rings (`hρ`, `RefuseAvgWithin`) in place of the
per-key bound, every anonymity adversary has advantage at most
`Q · wiError errc (Q · C') + 2Q · εc + Q · n · ρ`. -/
@[headline]
theorem anonAdvantage_le_of_pubOfCoins_avg {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    (hB : B.OracleFree) {C' : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B (V.proofSystem Hc hb hf) adm) n =>
        c.Valid keys).card ≤ C')
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {εc ρ : ℝ≥0} (hcorr : B.CorrectWithin εc)
    (hρ : B.RefuseAvgWithin adm ρ)
    {Vw : OracleView (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
      (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))} {t : ℕ}
    (A : AnonAdversary (ofBase B (V.proofSystem Hc hb hf) adm) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * (TD.setting kS hb).model.wiError errc (Q * C') + 2 * Q * εc +
      Q * n * ρ :=
  anonAdvantage_ofBase_le_of_pubOfCoins_avg hB (V.pubWI_proofSystem Hc hb hf hE) hC hpub hcorr hρ
    A Q

/-- **Anonymity of the ring signature of a compiled IOP over its own statements for a base signer
reading only the oracle off the compiled proofs' queries** (`anonAdvantage_ofBase_split_le` at
`chainSplit`): for a base signer whose algorithms read the oracle only off the image of
`Query.toBits` (`hB`), the bound of `anonAdvantage_le`. -/
@[headline]
theorem anonAdvantage_le_split {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc)
    (hB : B.ReadsOnly fun H => (chainSplit H).1) {C' : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B (V.proofSystem Hc hb hf) adm) n =>
        c.Valid keys).card ≤ C')
    (Good : (Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins) → Prop) [DecidablePred Good]
    (ε : (Fin n → (ofBase B (V.proofSystem Hc hb hf) adm).KeyCoins) → ℝ) (hε0 : ∀ keys, 0 ≤ ε keys)
    (hε : ∀ keys, Good keys →
      ∀ H (c : AnonRequest (ofBase B (V.proofSystem Hc hb hf) adm) n), c.Valid keys → adm c.ring →
        PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
          (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε keys)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc)
    {Vw : OracleView (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
      (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))} {t : ℕ}
    (A : AnonAdversary (ofBase B (V.proofSystem Hc hb hf) adm) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * ((𝔼 keys, ε keys) + 2 * εc) +
      Q * (TD.setting kS hb).model.wiError errc (Q * C') +
        𝔼 keys, (if Good keys then 0 else 1 : ℝ) :=
  anonAdvantage_ofBase_split_le (PS := V.proofSystem Hc hb hf) (Good := Good) chainSplit hB
    (fun ω₂ _ => pubWI_spbcsComapProofSystem_split _ _ _ hf _ _ _ _ (TD.setting kS hb).viewEncoder
      (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE)
      (fun x w h => V.input_mem _ x w h) ω₂) hC ε hε0 hε hcorr A Q

end StmtVerifiesRing

end GordieHowe.Ring
