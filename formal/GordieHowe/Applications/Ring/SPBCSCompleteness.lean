-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSRing
public import GordieHowe.Model.RingSignature.BaseCompleteness
public import GordieHowe.Model.ROM.AdaptiveCompletenessProg
public import GordieHowe.SPBCS.CompleteNARG
public import GordieHowe.SPBCS.Extraction.CompletenessAdaptive

@[expose] public section

/-!
# Completeness of the ring signature compiled by spBCS

The spBCS proof system of the ring relation (`spbcsProofSystem`,
`GordieHowe/Applications/Ring/SPBCSRing.lean`) is adaptively complete for the ring relation
(`ProofSystem.CompleteWithin`, `GordieHowe/Model/RingSignature/BaseCompleteness.lean`), and the
completeness headlines of `ofBase` instantiate with it.

- `spbcsProofSystem_completeWithin`: when every pair of the ring relation at every oracle is in the
  relation `rel₀` of the IOP (`hrel`) and the IOP has completeness error `εp` on `rel₀` (`hε`, the
  hypothesis of `SPBCS.completenessGuarantees`, paper `thm:bcs-complete`), the proof system is
  adaptively complete for `ringRel B adm` at error
  `εp + overrun + keyCollision (τ.size nr) k + T / 2^(8 kS)` against programs with `T` queries: the
  fresh-slice bound of spBCS (`prob_not_accepts_prove_proverCoins_replaceSlice_le`, moved to the
  quantum oracle's bit strings by `freshSlice_coins_comp_toBits`) and the salt-guessing term of
  `OracleProg.prob_bad_coins_le`.
- `completeWithin_ofBase_spbcs` (averaged over honest rings, refusal from
  `RefuseWithin`) and `completeAtWithin_ofBase_spbcs` (per key, refusal from `RefuseAtWithin`), with
  rejection error `εc + (εp + overrun + keyCollision (τ.size nr) k + (q + qPub) / 2^(8 kS))`.
- `completeWithin_ofBase_spbcs_of_verifiesWithoutOracle`,
  `completeAtWithin_ofBase_spbcs_of_verifiesWithoutOracle`: for a base signer whose verification and
  public value read no oracle (`BaseSigner.VerifiesWithoutOracle`), with `rel₀` the ring relation
  at any one oracle `H₀`.

The hypothesis `hrel` asks for one oracle-independent relation `rel₀` of the IOP containing the
ring relation at every oracle. For a base signer whose verification reads the oracle (the ML-DSA
ring publishing `w₁` verifies against the commitment hash `H`), `rel₀` must contain the ring
relation at every commitment hash; this file constructs no such relation.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature GordieHowe.IOP
open scoped ENNReal

variable {k kN kS L e N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N T RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (RingStmt B) k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : RingStmt B → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : RingWit B → R → CausalProver P τ (RingStmt B))
  (adm : KeyRing B.PK N → Prop)

variable {M} in
/-- **The completeness error of an honest causal prover is at most `εp`** on the relation `rel₀`:
for every pair of `rel₀`, the composite verifier rejects the run of the prover on the statement,
over uniform coins and challenges, with probability at most `εp`. -/
def _root_.GordieHowe.IOP.CausalProver.CompleteWithin {W : Type}
    (honest : W → R → CausalProver P τ (RingStmt B)) (Vr : RingStmt B → FullTr P τ → Bool)
    (rel₀ : RingStmt B → W → Prop) (εp : ℝ≥0∞) : Prop :=
  ∀ x w, rel₀ x w → Pr[q ← R × Chs P τ : Vr x ((honest w q.1).run x q.2) ≠ true] ≤ εp

/-- Every honest causal prover has completeness error at most `1`. -/
theorem _root_.GordieHowe.IOP.CausalProver.completeWithin_one {W : Type}
    (honest : W → R → CausalProver P τ (RingStmt B)) (Vr : RingStmt B → FullTr P τ → Bool)
    (rel₀ : RingStmt B → W → Prop) : CausalProver.CompleteWithin honest Vr rel₀ 1 :=
  fun _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The spBCS proof system is adaptively complete for the ring relation**: if every pair of the
ring relation at every oracle is in `rel₀` (`hrel`) and the composite verifier rejects the run of
the causal honest prover on a pair of `rel₀` with probability at most `εp` over uniform coins and
challenges (`hε`), then against every program with `T` queries the error is
`εp + overrun + keyCollision (τ.size nr) k + T / 2^(8 kS)`, for a query phase with view laws `VE`. -/
theorem spbcsProofSystem_completeWithin (VE : M.ViewEncoder E Qs)
    {rel₀ : RingStmt B → RingWit B → Prop}
    (hrel : ∀ (H : Bits (queryBits k kN kS L) → XOut k e) (p : RingStmt B × RingWit B),
      p ∈ ringRel B adm H → rel₀ p.1 p.2) {εp : ℝ≥0∞}
    (hε : ∀ x w, rel₀ x w → Pr[q ← R × Chs P τ : Vr x ((honest w q.1).run x q.2) ≠ true] ≤ εp) :
    (spbcsProofSystem M Λ E hb honest).CompleteWithin (ringRel B adm)
      fun T => εp + M.overrun + SPBCS.keyCollision (τ.size nr) k + T / 2 ^ (8 * kS) := by
  classical
  intro T C _ _ G hG
  have hcard : (Fintype.card (FiatShamirSalt kS) : ℝ≥0∞) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    rfl
  let Bad : M.ProverCoins R → FiatShamirSalt kS → (Bits (queryBits k kN kS L) → XOut k e) →
      Option (RingStmt B × RingWit B) → Prop := fun r σ H o =>
    ∃ p, o = some p ∧ rel₀ p.1 p.2 ∧ ¬ M.Accepts (chainOracle H) p.1
      (prove (honest p.2 r.iop) p.1 σ E r.merkleSalts (chainOracle H) (Qs p.1)) (Qs p.1)
  have hslice : ∀ σ g o, Pr[q ← M.ProverCoins R × (Bits (queryBits k kN kS L) → XOut k e) :
      Bad q.1 σ (replaceSlice M.saltOfBits σ g q.2) o] ≤
        εp + M.overrun + SPBCS.keyCollision (τ.size nr) k := by
    intro σ g o
    rcases o with _ | p
    · rw [QROM.probUniform_eq_zero fun q hq => by obtain ⟨p, hp, -⟩ := hq; exact absurd hp (by simp)]
      exact zero_le
    · refine (QROM.probUniform_mono fun q hq => ?_).trans
        (freshSlice_coins_comp_toBits (saltQ := M.querySalt) M.saltOfBits_toBits
          (Bad := fun (c : M.ProverCoins R) σ h (o : ProofQuery (RingStmt B) (RingWit B)) =>
            rel₀ o.stmt o.wit ∧ ¬ M.Accepts h o.stmt
              (prove (honest o.wit c.iop) o.stmt σ E c.merkleSalts h (Qs o.stmt)) (Qs o.stmt))
          (prob_not_accepts_prove_proverCoins_replaceSlice_le M honest E Qs hε) σ g ⟨p.1, p.2⟩)
      obtain ⟨p', hp', hr, hna⟩ := hq
      obtain rfl := Option.some.inj hp'
      exact ⟨hr, hna⟩
  let eqv : C × (M.ProverCoins R × (FiatShamirSalt kS × (Bits (queryBits k kN kS L) → XOut k e))) ≃
      (Bits (queryBits k kN kS L) → XOut k e) × C ×
        SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) :=
    { toFun := fun z => (z.2.2.2, z.1, ⟨z.2.2.1, z.2.1⟩)
      invFun := fun d => (d.2.1, d.2.2.coins, d.2.2.salt, d.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change probUniform _ (fun d : (Bits (queryBits k kN kS L) → XOut k e) × C ×
      SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) =>
    ∃ p, (G d.2.1).run d.1 = some p ∧ p ∈ ringRel B adm d.1 ∧
      (spbcsProofSystem M Λ E hb honest).verify d.1 p.1
        (((spbcsProofSystem M Λ E hb honest).prove p.1 p.2 d.2.2).run d.1) = false) ≤ _
  refine (QROM.probUniform_mono (E' := fun d => Bad d.2.2.coins d.2.2.salt d.1 ((G d.2.1).run d.1))
    fun d hd => ?_).trans ?_
  · obtain ⟨p, hp, hrel', hv⟩ := hd
    refine ⟨p, hp, hrel d.1 p hrel', fun hacc => ?_⟩
    rw [verify_spbcsProofSystem_of_accepts M Λ E hb honest VE d.1 p.1 p.2 d.2.2 hacc] at hv
    exact Bool.noConfusion hv
  · rw [← QROM.probUniform_equiv eqv]
    refine ROM.probUniform_prod_le fun c => ?_
    rw [ROM.probUniform_prod_eq_sum]
    refine ((G c).prob_bad_coins_le M.saltOfBits (hG c) hslice).trans_eq ?_
    rw [hcard]

/-! ### Completeness at spBCS -/

variable [DecidablePred adm]

variable [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [Nonempty T.Coins]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **Completeness of the ring signature compiled by spBCS** (BKM06 Definition 1 with errors,
averaged over honest rings): for a base signer with refusal rate `ρ` on honest rings and
correctness error `εc`, and an IOP with completeness error `εp` on a relation `rel₀` containing the
ring relation at every oracle, the ring signature `ofBase B (spbcsProofSystem …) adm` refuses an
honest supported ring with probability at most `ρ` and is rejected with probability at most
`εc + (εp + overrun + keyCollision (τ.size nr) k + (q + qPub) / 2^(8 kS))`. -/
theorem completeWithin_ofBase_spbcs (VE : M.ViewEncoder E Qs) {ρ εc : ℝ≥0∞}
    (hρ : B.RefuseWithin adm ρ) (hc : B.CorrectWithin εc) {rel₀ : RingStmt B → RingWit B → Prop}
    (hrel : ∀ H, ringRel B adm H ⊆ {p | rel₀ p.1 p.2}) {εp : ℝ≥0∞}
    (hε : CausalProver.CompleteWithin honest Vr rel₀ εp) :
    (ofBase B (spbcsProofSystem M Λ E hb honest) adm).CompleteWithin ρ
      (εc + M.ringCompletenessError εp (B.q + B.qPub)) :=
  completeWithin_ofBase B _ adm hρ hc (spbcsProofSystem_completeWithin M Λ E hb honest adm VE hrel hε)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] [Fintype T.KeyCoins]
  [Nonempty T.KeyCoins] in
/-- **Completeness of the ring signature compiled by spBCS, per key**: as
`completeWithin_ofBase_spbcs`, with the per-key refusal rate `ρ` (`RefuseAtWithin`), at every key
and every supported ring holding it. -/
theorem completeAtWithin_ofBase_spbcs (VE : M.ViewEncoder E Qs) {ρ εc : ℝ≥0∞}
    (hρ : B.RefuseAtWithin adm ρ) (hc : B.CorrectWithin εc) {rel₀ : RingStmt B → RingWit B → Prop}
    (hrel : ∀ H, ringRel B adm H ⊆ {p | rel₀ p.1 p.2}) {εp : ℝ≥0∞}
    (hε : CausalProver.CompleteWithin honest Vr rel₀ εp) :
    (ofBase B (spbcsProofSystem M Λ E hb honest) adm).CompleteAtWithin ρ
      (εc + M.ringCompletenessError εp (B.q + B.qPub)) :=
  completeAtWithin_ofBase B _ adm hρ hc
    (spbcsProofSystem_completeWithin M Λ E hb honest adm VE hrel hε)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **Completeness of the ring signature compiled by spBCS, base verification without the
oracle**: for a base signer whose verification and public value read no oracle, the IOP's relation
may be the ring relation at any one oracle `H₀` (`completeWithin_ofBase_spbcs` with
`VerifiesWithoutOracle.ringRel_eq`). -/
theorem completeWithin_ofBase_spbcs_of_verifiesWithoutOracle (VE : M.ViewEncoder E Qs)
    {ρ εc : ℝ≥0∞} (hρ : B.RefuseWithin adm ρ) (hc : B.CorrectWithin εc)
    (hB : B.VerifiesWithoutOracle) (H₀ : Bits (queryBits k kN kS L) → XOut k e) {εp : ℝ≥0∞}
    (hε : CausalProver.CompleteWithin honest Vr (fun x w => (x, w) ∈ ringRel B adm H₀) εp) :
    (ofBase B (spbcsProofSystem M Λ E hb honest) adm).CompleteWithin ρ
      (εc + M.ringCompletenessError εp (B.q + B.qPub)) :=
  completeWithin_ofBase_spbcs M Λ E hb honest adm VE hρ hc (rel₀ := fun x w => (x, w) ∈ ringRel B adm H₀)
    (fun H p hp => by rw [hB.ringRel_eq adm H₀ H]; exact hp) hε

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] [Fintype T.KeyCoins]
  [Nonempty T.KeyCoins] in
/-- **Completeness per key of the ring signature compiled by spBCS, base verification without
the oracle** (`completeAtWithin_ofBase_spbcs` with `VerifiesWithoutOracle.ringRel_eq`). -/
theorem completeAtWithin_ofBase_spbcs_of_verifiesWithoutOracle (VE : M.ViewEncoder E Qs)
    {ρ εc : ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ) (hc : B.CorrectWithin εc)
    (hB : B.VerifiesWithoutOracle) (H₀ : Bits (queryBits k kN kS L) → XOut k e) {εp : ℝ≥0∞}
    (hε : CausalProver.CompleteWithin honest Vr (fun x w => (x, w) ∈ ringRel B adm H₀) εp) :
    (ofBase B (spbcsProofSystem M Λ E hb honest) adm).CompleteAtWithin ρ
      (εc + M.ringCompletenessError εp (B.q + B.qPub)) :=
  completeAtWithin_ofBase_spbcs M Λ E hb honest adm VE hρ hc
    (rel₀ := fun x w => (x, w) ∈ ringRel B adm H₀)
    (fun H p hp => by rw [hB.ringRel_eq adm H₀ H]; exact hp) hε

end GordieHowe.Ring
