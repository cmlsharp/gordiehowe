-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.AnonCoupling
public import GordieHowe.Applications.Ring.SPBCSRing
public import GordieHowe.Applications.Ring.RingAnonymity
public import GordieHowe.Headline

@[expose] public section

/-!
# Witness indistinguishability of the spBCS proof system of a ring relation

The hypothesis `PubWI` of the anonymity theorems of
`GordieHowe/Applications/Ring/RingAnonymity.lean` for the spBCS proof system of
`GordieHowe/Applications/Ring/SPBCSRing.lean`, from the honest-verifier zero knowledge of the
compiled composite (`gameAdvantage_pubRun_le` of `GordieHowe/Applications/Ring/Anonymity.lean`, at
error `wiError δ`).

- `chainSplit`, `chainSplit_snd`: the quantum oracle `Bits (queryBits k kN kS L) → XOut k e` as its
  values off the image of `Query.toBits` and the oracle `chainOracle H` the compiled proofs read.
- `proofLaw_spbcsProofSystem`: the law of a proof of the proof system at `H` is the spBCS proof
  law at `chainOracle H`, each proof put in the format.
- `pubWI_spbcsProofSystem`: **witness indistinguishability with public outputs at error
  `wiError δ`**: relabelling the proofs (`PubWI.map_proof`) and splitting the oracle
  (`PubWI.of_split`).
- `anonAdvantage_ofBase_spbcs_le`, `anonAdvantage_ofBase_spbcs_le_of_pubOfCoins`: the anonymity
  bounds of `anonAdvantage_ofBase_le` and `anonAdvantage_ofBase_le_of_pubOfCoins` for the ring
  signature compiled by spBCS.
- `pubWI_spbcsProofSystem_split`, `anonAdvantage_ofBase_spbcs_split_le`: the same for a base
  signer reading only the oracle off the compiled proofs' queries (the first part of `chainSplit`).
- `replayVia`, `mapChoice`, `toWIAdversaryVia`, `map_wiRun_replayVia`, `pubWI_proofLaw_comap`:
  witness indistinguishability through a statement map (proofs of `σ x` with witnesses `ι' x w`,
  public values of the statements `x`), the replay argument of `gameAdvantage_pubRun_le` with the
  public values of the chosen statements; `toResponse`: a compiled proof in the format.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature
open scoped ENNReal NNReal BigOperators

/-! ### The oracle the compiled proofs read -/

section Split

variable {k kN kS L e : ℕ}

/-- **The quantum oracle split into the oracle of the compiled proofs and the rest**: an oracle `H`
is its values off the image of `Query.toBits` and the oracle `chainOracle H` on queries. -/
noncomputable def chainSplit :
    (Bits (queryBits k kN kS L) → XOut k e) ≃
      ({b // b ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L))} → XOut k e) ×
        (Query k kN kS L → Out k e) where
  toFun H := (fun c => H c.1, chainOracle H)
  invFun p b := if hb : b ∈ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) then
      (outEquiv k e).symm (p.2 (Classical.choose hb)) else p.1 ⟨b, hb⟩
  left_inv H := by
    funext b
    by_cases hb : b ∈ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L))
    · simp only [hb, dite_true, chainOracle, Equiv.symm_apply_apply]
      rw [Classical.choose_spec hb]
    · simp [hb]
  right_inv p := by
    refine Prod.ext (funext fun c => by simp [c.2]) (funext fun q => ?_)
    have hq : Query.toBits q ∈ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) :=
      ⟨q, rfl⟩
    simp only [chainOracle, hq, dite_true, Equiv.apply_symm_apply]
    rw [Query.toBits.injective (Classical.choose_spec hq)]

/-- **The second part of `chainSplit H` is `chainOracle H`.** -/
theorem chainSplit_snd (H : Bits (queryBits k kN kS L) → XOut k e) :
    (chainSplit H).2 = chainOracle H :=
  rfl

end Split

/-! ### The proof law -/

section Format

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e) {b : ℕ}

/-- **A compiled proof in the format `b`**, or none if it does not fit. -/
noncomputable def toResponse (π : M.NIProof) : M.Response b :=
  if h : M.Bounded b π then some ⟨π, h⟩ else none

end Format

section ProofLaw

variable {k kN kS L e N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N T RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (RingSignature.RingStmt B) k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : RingSignature.RingStmt B → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : RingSignature.RingWit B → R → CausalProver P τ (RingSignature.RingStmt B))

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The law of a proof of the spBCS proof system** at the oracle `H` is the spBCS proof law
(`SPBCS.proofLaw`) at `chainOracle H`, each proof in the format. -/
theorem proofLaw_spbcsProofSystem (VE : M.ViewEncoder E Qs)
    (H : Bits (queryBits k kN kS L) → XOut k e) (x : RingSignature.RingStmt B)
    (w : RingSignature.RingWit B) :
    (spbcsProofSystem M Λ E hb honest).proofLaw H x w =
      (proofLaw E Qs (chainOracle H) x (honest w)).map (toResponse M) := by
  let φ : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) ≃
      FiatShamirSalt kS × R × (M.Pos → MerkleSalt kN) :=
    (SaltedCoins.equivProd _ _).trans (Equiv.prodCongr (Equiv.refl _) (ProverCoins.equivProd M R))
  rw [proofLaw, ← PMF.map_uniformOfFintype_equiv φ, PMF.map_comp, PMF.map_comp]
  change (PMF.uniformOfFintype (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))).map _ = _
  congr 1
  funext a
  obtain ⟨p, hp, hp1⟩ := run_prove_spbcsProofSystem M Λ E hb honest VE H x w a
  change ((spbcsProofSystem M Λ E hb honest).prove x w a).run H = toResponse M
    (prove (honest w a.coins.iop) x a.salt E a.coins.merkleSalts (chainOracle H) (Qs x))
  rw [hp, ← hp1, toResponse, dite_eq_left p.2]
  rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **Witness indistinguishability of the spBCS proof system with public outputs** at error
`wiError δ`, for a relation `rel` at which the compiled composite's honest prover has
honest-verifier zero knowledge at error `δ` (`hz`, what the proof reveals read off the view by
`VE`): `gameAdvantage_pubRun_le` at the oracle the proofs read, through `PubWI.of_split` and
`PubWI.map_proof`. -/
theorem pubWI_spbcsProofSystem (VE : M.ViewEncoder E Qs)
    {rel : Set (RingSignature.RingStmt B × RingSignature.RingWit B)} {PubZ : Type}
    {pubZ : RingSignature.RingStmt B → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ}
    {δ : ℝ≥0} (hz : CausalHVZK VE.toReveal.MV rel honest pubZ sim δ) :
    PubWI (spbcsProofSystem M Λ E hb honest).proofLaw RingSignature.RingStmtOf.pub rel
      (M.wiError δ) := by
  refine PubWI.of_split chainSplit
    (law₁ := fun h x w => (proofLaw E Qs h x (honest w)).map (toResponse M (b := b)))
    (fun ω₂ h₁ => funext fun x => funext fun w => by
      rw [proofLaw_spbcsProofSystem M Λ E hb honest VE, ← chainSplit_snd,
        Equiv.apply_symm_apply]) ?_
  refine PubWI.map_proof ?_ (toResponse M)
  intro Q c F S hc hS hF U
  exact (gameAdvantage_pubRun_le (F := F) RingSignature.RingStmtOf.pub VE.toReveal hz S hS hF U).trans
    (mul_le_mul_of_nonneg_left (SPBCS.wiError_mono δ hc) (Nat.cast_nonneg _))

/-! ### Anonymity of the ring signature compiled by spBCS -/

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins]
  [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

variable (adm : KeyRing B.PK N → Prop) [DecidablePred adm] {n : ℕ}

/-- **Anonymity of the ring signature compiled by spBCS** (BKM06 Definition 4 with `Q` adaptive
challenges, `GordieHowe/Model/RingSignature/Anonymity.lean`; `anonAdvantage_ofBase_le` with
`pubWI_spbcsProofSystem`): for an oracle-free base signer (`hB`), a composite whose honest prover
has honest-verifier zero knowledge at error `δ` for the ring relation at every oracle (`hz`, what
the proof reveals read off the view by `VE`), at most `C` valid challenges for every key vector
(`hC`), a coupling `cpl` of the two users' refusal-or-public value laws
(`BaseSigner.AnonCoupling`) and correctness error `εc` (`hcorr`), every
anonymity adversary with any oracle view and query bound has advantage at most
`Q · (cpl.meanError + 2εc) + Q · wiError δ (Q · C) + cpl.badProb`. -/
theorem anonAdvantage_ofBase_spbcs_le (VE : M.ViewEncoder E Qs) {PubZ : Type}
    {pubZ : RingSignature.RingStmt B → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ}
    {δ : ℝ≥0}
    (hz : ∀ H, CausalHVZK VE.toReveal.MV (RingSignature.ringRel B adm H) honest pubZ sim δ)
    (hB : B.OracleFree) {C : ℕ}
    (hC : (ofBase B (spbcsProofSystem M Λ E hb honest) adm).validChallengeBound n ≤ C)
    (cpl : B.AnonCoupling adm n)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) {V : OracleView (Bits (queryBits k kN kS L)) (XOut k e)}
    {t : ℕ} (A : AnonAdversary (ofBase B (spbcsProofSystem M Λ E hb honest) adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * (cpl.meanError + 2 * εc) + Q * M.wiError δ (Q * C) +
      cpl.badProb :=
  anonAdvantage_ofBase_le hB (fun H => pubWI_spbcsProofSystem M Λ E hb honest VE (hz H)) hC cpl
    hcorr A Q

/-- **Anonymity of the ring signature compiled by spBCS when the public value is a function of the
signing coins** (a salt read off the coins; `Pub = Unit`, `pubOfCoins_unique`;
`anonAdvantage_ofBase_le_of_pubOfCoins` with `pubWI_spbcsProofSystem`): every anonymity adversary
has advantage at most `Q · wiError δ (Q · C) + 2Q · εc + 2Q · ρ`, with `ρ` a bound on the base
signer's refusal probability at every input (`hρ`). -/
theorem anonAdvantage_ofBase_spbcs_le_of_pubOfCoins (VE : M.ViewEncoder E Qs) {PubZ : Type}
    {pubZ : RingSignature.RingStmt B → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ}
    {δ : ℝ≥0}
    (hz : ∀ H, CausalHVZK VE.toReveal.MV (RingSignature.ringRel B adm H) honest pubZ sim δ)
    (hB : B.OracleFree) {C : ℕ}
    (hC : (ofBase B (spbcsProofSystem M Λ E hb honest) adm).validChallengeBound n ≤ C)
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {εc ρ : ℝ≥0} (hcorr : B.CorrectWithin εc)
    (hρ : B.RefuseKeyWithin ρ)
    {V : OracleView (Bits (queryBits k kN kS L)) (XOut k e)} {t : ℕ}
    (A : AnonAdversary (ofBase B (spbcsProofSystem M Λ E hb honest) adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * M.wiError δ (Q * C) + 2 * Q * εc + 2 * Q * ρ :=
  anonAdvantage_ofBase_le_of_pubOfCoins hB
    (fun H => pubWI_spbcsProofSystem M Λ E hb honest VE (hz H)) hC hpub hcorr hρ A Q

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] [Fintype T.PK]
  [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins] [Nonempty T.KeyCoins]
  [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins] in
/-- **Witness indistinguishability of the spBCS proof system at the oracles with a fixed off-query
part** `ω₂`, at error `wiError δ` under the hypothesis `hz` of `pubWI_spbcsProofSystem` (the proofs
read the oracle through `chainOracle`, the second part of `chainSplit`). -/
theorem pubWI_spbcsProofSystem_split (VE : M.ViewEncoder E Qs)
    {rel : Set (RingSignature.RingStmt B × RingSignature.RingWit B)} {PubZ : Type}
    {pubZ : RingSignature.RingStmt B → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ}
    {δ : ℝ≥0} (hz : CausalHVZK VE.toReveal.MV rel honest pubZ sim δ)
    (ω₂ : {x // x ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L))} → XOut k e) :
    PubWI (fun h => (spbcsProofSystem M Λ E hb honest).proofLaw (chainSplit.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub rel (M.wiError δ) := by
  have hlaw : (fun h => (spbcsProofSystem M Λ E hb honest).proofLaw (chainSplit.symm (ω₂, h))) =
      fun h x w => (proofLaw E Qs h x (honest w)).map (toResponse M (b := b)) := by
    funext h x w
    rw [proofLaw_spbcsProofSystem M Λ E hb honest VE, ← chainSplit_snd, Equiv.apply_symm_apply]
  rw [hlaw]
  refine PubWI.map_proof ?_ (toResponse M)
  intro Q c F S hc hS hF U
  exact (gameAdvantage_pubRun_le (F := F) RingSignature.RingStmtOf.pub VE.toReveal hz S hS hF U).trans
    (mul_le_mul_of_nonneg_left (SPBCS.wiError_mono δ hc) (Nat.cast_nonneg _))

/-- **Anonymity of the ring signature compiled by spBCS for a base signer reading only the oracle
off the compiled proofs' queries** (`anonAdvantage_ofBase_split_le` at `chainSplit`, with
`pubWI_spbcsProofSystem_split`): for a base signer whose algorithms read the oracle only off the
image of `Query.toBits` (`hB`), the bound of `anonAdvantage_ofBase_spbcs_le`. -/
theorem anonAdvantage_ofBase_spbcs_split_le (VE : M.ViewEncoder E Qs) {PubZ : Type}
    {pubZ : RingSignature.RingStmt B → PubZ} {sim : CausalJointSimulator VE.toReveal.MV PubZ}
    {δ : ℝ≥0}
    (hz : ∀ H, CausalHVZK VE.toReveal.MV (RingSignature.ringRel B adm H) honest pubZ sim δ)
    (hB : B.ReadsOnly fun H => (chainSplit H).1) {C : ℕ}
    (hC : (ofBase B (spbcsProofSystem M Λ E hb honest) adm).validChallengeBound n ≤ C)
    (cpl : B.AnonCoupling adm n)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) {V : OracleView (Bits (queryBits k kN kS L)) (XOut k e)}
    {t : ℕ} (A : AnonAdversary (ofBase B (spbcsProofSystem M Λ E hb honest) adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * (cpl.meanError + 2 * εc) + Q * M.wiError δ (Q * C) +
      cpl.badProb := by
  classical
  exact anonAdvantage_ofBase_split_le chainSplit hB
    (fun ω₂ h₁ => pubWI_spbcsProofSystem_split M Λ E hb honest VE (hz _) ω₂) hC cpl
    hcorr A Q

end ProofLaw

/-! ### Witness indistinguishability through a statement map -/

section Comap

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ W₀ : Type}
  {M : SPBCS Mg P X₀ k kN kS L e} {X W Pub : Type} (σ : X → X₀) (ι' : X → W → W₀)
  (pubOf : X → Pub) {Q : ℕ}

/-- **The history recomputed from the proofs**, for two-witness choices of statements `X` read
through `σ`, with the public values of the chosen statements. -/
def replayVia (F : (j : Fin Q) → (Query k kN kS L → Out k e) → PubHist Pub M.NIProof j →
    Option (SPBCS.WIChoice X W)) :
    (j : ℕ) → j ≤ Q → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) →
      PubHist Pub M.NIProof j
  | 0, _, _, _ => Fin.elim0
  | j + 1, hj, h, πs =>
    Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replayVia F j (by omega) h (Fin.init πs))
      ((F ⟨j, by omega⟩ h (replayVia F j (by omega) h (Fin.init πs))).map fun c =>
        (pubOf c.stmt, πs (Fin.last j)))

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The recomputed history after one more proof** extends the recomputed history by the round of
that proof. -/
theorem replayVia_succ_snoc (F : (j : Fin Q) → (Query k kN kS L → Out k e) →
    PubHist Pub M.NIProof j → Option (SPBCS.WIChoice X W)) (j : ℕ) (hj : j + 1 ≤ Q)
    (h : Query k kN kS L → Out k e) (πs : Fin j → M.NIProof) (π : M.NIProof) :
    replayVia pubOf F (j + 1) hj h (Fin.snoc (α := fun _ => M.NIProof) πs π) =
      Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replayVia pubOf F j (by omega) h πs)
        ((F ⟨j, by omega⟩ h (replayVia pubOf F j (by omega) h πs)).map fun c =>
          (pubOf c.stmt, π)) := by
  rw [replayVia, Fin.init_snoc, Fin.snoc_last]

/-- A two-witness choice read through `σ` and `ι'`. -/
def mapChoice (c : SPBCS.WIChoice X W) : SPBCS.WIChoice X₀ W₀ :=
  ⟨σ c.stmt, ι' c.stmt c.wit₀, ι' c.stmt c.wit₁⟩

open Classical in
/-- **The witness-indistinguishability adversary of the composite** from two-witness choices of
statements `X`: the choices read through `σ` and `ι'`, from the history recomputed from the proofs,
with the choice `c₀` for the refused rounds. -/
noncomputable def toWIAdversaryVia {rel₀ : Set (X₀ × W₀)}
    (F : (j : Fin Q) → (Query k kN kS L → Out k e) → PubHist Pub M.NIProof j →
      Option (SPBCS.WIChoice X W)) (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, ((mapChoice σ ι' c).stmt, (mapChoice σ ι' c).wit₀) ∈ rel₀ ∧
      ((mapChoice σ ι' c).stmt, (mapChoice σ ι' c).wit₁) ∈ rel₀)
    {c₀ : SPBCS.WIChoice X W} (hc₀ : c₀ ∈ S) (hF : ∀ j h hist c, F j h hist = some c → c ∈ S) :
    M.WIAdversary rel₀ Q where
  choices := S.image (mapChoice σ ι')
  admissible c hc := by
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
    exact hS c' hc'
  choose j h πs := mapChoice σ ι' ((F j h (replayVia pubOf F j j.2.le h πs)).getD c₀)
  choose_mem j h πs := by
    refine Finset.mem_image_of_mem _ ?_
    cases hc : F j h (replayVia pubOf F j j.2.le h πs) with
    | none => exact hc₀
    | some c => exact hF _ _ _ _ hc

variable {E : (j : ι) → (M.comp j).Encoder} {Vr : X₀ → FullTr P τ → Bool}
  {Qs : ∀ x, M.IOPQueries Vr x} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : W₀ → R → CausalProver P τ X₀)

omit [∀ j i, Nonempty ((P j).Challenge i)] [DecidableEq R] in
/-- **The witness-indistinguishability experiment with its history recomputed** is the experiment
with public outputs of the selector, the proofs of statements `σ x` with witnesses `ι' x w`. -/
theorem map_wiRun_replayVia {rel₀ : Set (X₀ × W₀)}
    {F : (j : Fin Q) → (Query k kN kS L → Out k e) → PubHist Pub M.NIProof j →
      Option (SPBCS.WIChoice X W)} {S : Finset (SPBCS.WIChoice X W)}
    {hS : ∀ c ∈ S, ((mapChoice σ ι' c).stmt, (mapChoice σ ι' c).wit₀) ∈ rel₀ ∧
      ((mapChoice σ ι' c).stmt, (mapChoice σ ι' c).wit₁) ∈ rel₀}
    {c₀ : SPBCS.WIChoice X W} {hc₀ : c₀ ∈ S} {hF : ∀ j h hist c, F j h hist = some c → c ∈ S}
    (bs : ℕ → Bool) :
    ∀ j (hj : j ≤ Q), (SPBCS.wiRun (fun h x w => proofLaw E Qs h x (honest w))
        (toWIAdversaryVia σ ι' pubOf F S hS hc₀ hF) bs j hj).map
        (fun s => (s.1, replayVia pubOf F j hj s.1 s.2)) =
      pubRun (fun h x w => proofLaw E Qs h (σ x) (honest (ι' x w))) pubOf (wiSelector F bs) j hj
  | 0, _ => by
    rw [SPBCS.wiRun, pubRun, PMF.map_comp]
    congr 1
  | j + 1, hj => by
    rw [SPBCS.wiRun, pubRun, ← map_wiRun_replayVia (hS := hS) (hc₀ := hc₀) (hF := hF) bs j
      (by omega), PMF.map_bind, PMF.bind_map]
    congr 1
    funext s
    simp only [Function.comp_apply, SPBCS.wiStep, pubStep, PMF.map_comp, wiSelector,
      toWIAdversaryVia]
    simp only [Function.comp_def, replayVia_succ_snoc]
    cases hc : F ⟨j, by omega⟩ s.1 (replayVia pubOf F j (by omega) s.1 s.2) with
    | none =>
      simp only [Option.map_none, Option.getD_none, roundLaw, PMF.pure_map]
      exact PMF.map_const _ _
    | some c =>
      simp only [Option.map_some, Option.getD_some, roundLaw, PMF.map_comp, Function.comp_def,
        mapChoice]
      congr 1
      · cases bs j <;> rfl

omit [DecidableEq R] in
/-- **Witness indistinguishability with public outputs through a statement map**: for the spBCS
compilation `M` whose honest prover has honest-verifier zero knowledge at error `δ` for `rel₀`
(`hz`), proofs of statements `σ x` with witnesses `ι' x w` have witness indistinguishability at
error `wiError δ` for every relation `rel` that `σ` and `ι'` map into `rel₀` (`hrel`), the public
values `pubOf` of the statements `x`. -/
theorem pubWI_proofLaw_comap (Rv : M.Reveal E Qs) {rel₀ : Set (X₀ × W₀)} {PubZ : Type}
    {pubZ : X₀ → PubZ} {sim : CausalJointSimulator Rv.MV PubZ} {δ : ℝ≥0}
    (hz : CausalHVZK Rv.MV rel₀ honest pubZ sim δ) {rel : Set (X × W)}
    (hrel : ∀ x w, (x, w) ∈ rel → (σ x, ι' x w) ∈ rel₀) :
    PubWI (fun h x w => proofLaw E Qs h (σ x) (honest (ι' x w))) pubOf rel (M.wiError δ) := by
  classical
  intro Q c F S hc hS hF U
  have hS' : ∀ c ∈ S, ((mapChoice σ ι' c).stmt, (mapChoice σ ι' c).wit₀) ∈ rel₀ ∧
      ((mapChoice σ ι' c).stmt, (mapChoice σ ι' c).wit₁) ∈ rel₀ := fun c hc =>
    ⟨hrel _ _ (hS c hc).1, hrel _ _ (hS c hc).2⟩
  rcases S.eq_empty_or_nonempty with hS0 | ⟨c₀, hc₀⟩
  · have hnone : ∀ j h hist, F j h hist = none := fun j h hist => by
      cases hcF : F j h hist with
      | none => rfl
      | some c => exact absurd (hF j h hist c hcF) (by simp [hS0])
    have hsel : wiSelector F (fun _ => false) = wiSelector F fun _ => true := by
      funext j h hist
      simp [wiSelector, hnone]
    rw [hsel]
    unfold GordieHowe.gameAdvantage GordieHowe.advantage
    rw [sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (SPBCS.wiError_nonneg δ _)
  rw [← map_wiRun_replayVia σ ι' pubOf honest (hS := hS') (hc₀ := hc₀) (hF := hF),
    ← map_wiRun_replayVia σ ι' pubOf honest (hS := hS') (hc₀ := hc₀) (hF := hF)]
  have hadv := SPBCS.witnessIndistinguishable Rv (SPBCS.obsClose_of_causalHVZK Rv hz) Q c
    (toWIAdversaryVia σ ι' pubOf F S hS' hc₀ hF) (Finset.card_image_le.trans hc)
    (fun h πs => U h (replayVia pubOf F Q le_rfl h πs))
  unfold SPBCS.wiAdvantage SPBCS.wiAdvantageWith SPBCS.wiGameWith at hadv
  unfold GordieHowe.gameAdvantage at hadv ⊢
  simp only [PMF.toOuterMeasure_map_apply] at ⊢
  exact hadv

end Comap

end GordieHowe.Ring
