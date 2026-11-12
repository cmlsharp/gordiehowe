-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Headline
public import GordieHowe.Model.Signature.Properties
public import GordieHowe.Model.ROM.AdaptiveCompleteness

@[expose] public section

/-!
# Completeness of a ring signature from a base signer and a proof system

Completeness (`GordieHowe/Model/RingSignature/Completeness.lean`, BKM06 Definition 1) of
`ofBase B PS adm`, from the base signer's refusal rate and correctness error and the completeness
of the proof system, with refusal and rejection bounded separately.

- `ProofSystem.CompleteWithin PS rel ε`: **adaptive completeness** (Unruh 2017, ePrint 2017/398,
  Definition 5, p. 14) for a relation `rel H` that may depend on the oracle `H`: for every classical
  oracle program `G` with uniform coins and at most `T` queries that outputs a statement-witness
  pair (or nothing), the probability over a uniform oracle `H`, the coins of `G` and the prover's
  coins that `G` outputs a pair in `rel H` whose honest proof `PS` rejects at `H` is at most `ε T`.
  `CompleteWithin.mono`: it holds at every larger error. `ProofSystem.acceptAll`,
  `acceptAll_completeWithin`: a proof system with error `0` (the hypothesis is satisfiable).
- `RingScheme.refuseProbAt`, `RingScheme.rejectProbAt`, `RingScheme.CompleteAtWithin S εr εv`:
  **completeness per key**: for the key-generation coins `kc` of the signer, every supported ring
  holding its key and every message, refusal at most `εr` and rejection at most `εv` over the
  oracle and the signing coins. `CompleteAtWithin.completeWithin`: it gives `CompleteWithin`
  (averaged over honest rings); `refuseProb_le_of_refuseProbAt`, `rejectProb_le_of_rejectProbAt`:
  the two halves, through `prob_completenessDraw_le` (an event bounded at every value of the
  members' keys is bounded over the whole draw). `trivial_completeAtWithin`: satisfiable.
- `BaseSigner.RefuseAtWithin B adm ρ`: the per-key refusal rate of the ring-aware signer: at every
  oracle, for every key and every supported ring holding it, `bsign` at the key's first position
  refuses with probability at most `ρ` over its coins. `refuseAtWithin_one`,
  `uniformSig_refuseAtWithin`: satisfiable. `BaseSigner.RefuseAvgWithin B adm ρ`, the refusal rate
  averaged over the honest key coins, and `RefuseAtWithin.refuseAvgWithin`;
  `refuseAvgWithin_one`: satisfiable. `RefuseAtWithin.refuseWithin`,
  `RefuseAvgWithin.refuseWithin`: each gives the averaged `RefuseWithin`
  (`tsum_uniformOfFintype_pi_eval`: one member's key coins are uniform).
- `BaseSigner.VerifiesWithoutOracle`: base verification and the public value read no oracle;
  `VerifiesWithoutOracle.ringRel_eq`: then the ring relation is the same at every oracle.
  `OracleFree.verifiesWithoutOracle`: `BaseSigner.OracleFree` is the stronger hypothesis, since it
  implies `VerifiesWithoutOracle`. `uniformSig_verifiesWithoutOracle`: satisfiable.
- `BaseSigner.ringPairProg`: the statement and witness of an honest ring signature as an oracle
  program from the base signer's coins (`bsign`, then `pub`), with at most `q + qPub` queries
  (`ringPairProg_queries`): the adversary of adaptive completeness. `run_ringPairProg_of_bsign`:
  its output on a base signature.
- `refuseProbAt_ofBase_le`, `rejectProbAt_ofBase_le`: the per-key bounds for `ofBase B PS adm`;
  rejection at most `εc + εp (q + qPub)`.
- Headlines: `completeAtWithin_ofBase` (per key, refusal `ρ` from `RefuseAtWithin`) and
  `completeWithin_ofBase` (averaged, refusal `ρ` from `RefuseWithin`), both with rejection error
  `εc + εp (q + qPub)` for a base signer with correctness error `εc` (`BaseSigner.CorrectWithin`)
  and a proof system adaptively complete for `ringRel B adm` at error `εp`.
  `completeAtWithin_ofBase_satisfiable`: their hypotheses hold together (the uniform-signature
  base signer with the accepting proof system).

## Sources and deliberate differences

1. **Adaptive completeness for an oracle-dependent relation.** Unruh's Definition 5 draws the pair
   from an adversary after its oracle queries; here the adversary is a classical oracle program
   with uniform coins (the base signer is one), and the relation may read the oracle (the ring
   relation reads it through `bverify` and `pub`); the event requires the pair to be in the
   relation at the same oracle. Completeness at a fixed pair is the case of a program without
   queries. The error is a function of the program's query bound.
2. **The honest pair reads the oracle.** The base signer and the public value are oracle programs,
   so the witness of an honest ring signature depends on the oracle the proof system uses; the
   hypothesis on the proof system is therefore adaptive completeness, applied to the honest pair
   (`ringPairProg`) as the program.
-/

namespace GordieHowe.RingSignature

open scoped ENNReal
open GordieHowe.IOP

/-! ### Completeness of a proof system -/

namespace ProofSystem

variable {X Y Stmt Wit : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **Adaptive completeness of a proof system at error `ε`** for the oracle-dependent relation
`rel` (Unruh 2017 Definition 5): for every query bound `T`, every finite nonempty type of coins `C`
and every classical oracle program `G` on them with at most `T` queries outputting a pair or
nothing, over a uniform oracle `H`, uniform coins of `G` and uniform prover coins, the probability
that `G` outputs a pair `(x, w)` in `rel H` and the verifier rejects at `H` the honest proof of `x`
with the witness `w` is at most `ε T`. -/
def CompleteWithin {TPS : PSTypes} [Fintype TPS.Coins] [Nonempty TPS.Coins]
    (PS : ProofSystem X Y Stmt Wit TPS) (rel : (X → Y) → Set (Stmt × Wit))
    (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (T : ℕ) (C : Type) [Fintype C] [Nonempty C] (G : C → OracleProg X Y (Option (Stmt × Wit))),
    (∀ c, (G c).QueriesLE T) →
      Pr[d ~ PMF.uniformOfFintype ((X → Y) × C × PS.Coins) :
        ∃ p, (G d.2.1).run d.1 = some p ∧ p ∈ rel d.1 ∧
          PS.verify d.1 p.1 ((PS.prove p.1 p.2 d.2.2).run d.1) = false] ≤ ε T

/-- Adaptive completeness at an error gives it at every larger error. -/
theorem CompleteWithin.mono {TPS : PSTypes} [Fintype TPS.Coins] [Nonempty TPS.Coins]
    {PS : ProofSystem X Y Stmt Wit TPS} {rel : (X → Y) → Set (Stmt × Wit)}
    {ε ε' : ℕ → ℝ≥0∞} (h : PS.CompleteWithin rel ε) (hε : ∀ T, ε T ≤ ε' T) :
    PS.CompleteWithin rel ε' :=
  fun T C _ _ G hG => (h T C G hG).trans (hε T)

/-- The types of `acceptAll`: one proof, one coin. -/
abbrev acceptAllT : PSTypes where
  Proof := Unit
  Coins := Unit

variable (X Y Stmt Wit) in
/-- **The accepting proof system**: one proof, one coin, no queries; the verifier accepts
everything. It is adaptively complete at error `0` for every relation
(`acceptAll_completeWithin`). -/
def acceptAll : ProofSystem X Y Stmt Wit acceptAllT where
  q := 0
  prove _ _ _ := .pure ()
  prove_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  verify _ _ _ := true

/-- **The accepting proof system is adaptively complete at error `0`.** -/
theorem acceptAll_completeWithin (rel : (X → Y) → Set (Stmt × Wit)) :
    (acceptAll X Y Stmt Wit).CompleteWithin rel fun _ => 0 := by
  intro T C _ _ G _
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun d _ hd => ?_
  simp only [Set.mem_ofPred_eq] at hd
  obtain ⟨p, -, -, hv⟩ := hd
  exact Bool.noConfusion hv

end ProofSystem

/-! ### Completeness per key -/

namespace RingScheme

variable {X Y : Type} {N : ℕ} {TS : RingTypes} (S : RingScheme X Y N TS) [Fintype X] [DecidableEq X] [Fintype Y]
  [Nonempty Y] [Fintype TS.SignCoins] [Nonempty TS.SignCoins]

/-- **The refusal probability at a key**: over a uniform oracle and uniform signing coins, the
probability that the signer with the key-generation coins `kc` refuses to sign `m` on the ring
`R`. -/
noncomputable def refuseProbAt (kc : S.KeyCoins) (R : KeyRing S.PK N) (m : S.Msg) : ℝ≥0∞ :=
  Pr[d ~ PMF.uniformOfFintype ((X → Y) × S.SignCoins) :
    (S.sign (S.keyGen kc) R m d.2).run d.1 = none]

/-- **The rejection probability at a key**: the probability that the signer with the coins `kc`
signs `m` on `R` and verification rejects the signature. -/
noncomputable def rejectProbAt (kc : S.KeyCoins) (R : KeyRing S.PK N) (m : S.Msg) : ℝ≥0∞ :=
  Pr[d ~ PMF.uniformOfFintype ((X → Y) × S.SignCoins) :
    ∃ σ, (S.sign (S.keyGen kc) R m d.2).run d.1 = some σ ∧ S.verify d.1 R m σ = false]

/-- **The scheme is complete per key with refusal error `εr` and rejection error `εv`**: for every
key-generation coins, every supported ring holding their public key and every message, the
refusal probability at the key is at most `εr` and the rejection probability at most `εv`. -/
structure CompleteAtWithin (εr εv : ℝ≥0∞) : Prop where
  /-- The refusal probability at every key on every supported ring holding it is at most `εr`. -/
  refuseProbAt_le : ∀ (kc : S.KeyCoins) (R : KeyRing S.PK N) (m : S.Msg), S.pk kc ∈ R.1 →
    S.Supported R → S.refuseProbAt kc R m ≤ εr
  /-- The rejection probability at every key on every supported ring holding it is at most
  `εv`. -/
  rejectProbAt_le : ∀ (kc : S.KeyCoins) (R : KeyRing S.PK N) (m : S.Msg), S.pk kc ∈ R.1 →
    S.Supported R → S.rejectProbAt kc R m ≤ εv

variable [Fintype TS.KeyCoins] [Nonempty TS.KeyCoins]

/-- **An event of the completeness draw bounded at every value of the members' keys**: if, for
every key coins of the members, the event has probability at most `ε` over the oracle and the
signing coins, it has probability at most `ε` over the whole draw. -/
theorem prob_completenessDraw_le {r : ℕ} (E : (Fin r → S.KeyCoins) → (X → Y) × S.SignCoins → Prop)
    {ε : ℝ≥0∞} (h : ∀ keys, Pr[d ~ PMF.uniformOfFintype ((X → Y) × S.SignCoins) : E keys d] ≤ ε) :
    Pr[d ~ PMF.uniformOfFintype (S.CompletenessDraw r) : E d.2.1 (d.1, d.2.2)] ≤ ε := by
  let eqv : (Fin r → S.KeyCoins) × ((X → Y) × S.SignCoins) ≃ S.CompletenessDraw r :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun d => (d.2.1, d.1, d.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change probUniform _ (fun d : S.CompletenessDraw r => E d.2.1 (d.1, d.2.2)) ≤ ε
  rw [← QROM.probUniform_equiv eqv]
  exact ROM.probUniform_prod_le fun keys => h keys

/-- **Refusal per key bounds the averaged refusal.** -/
theorem refuseProb_le_of_refuseProbAt {ε : ℝ≥0∞}
    (h : ∀ (kc : S.KeyCoins) (R : KeyRing S.PK N) (m : S.Msg), S.pk kc ∈ R.1 → S.Supported R →
      S.refuseProbAt kc R m ≤ ε) {r : ℕ} (hr : r ≤ N) (s : Fin r) (m : S.Msg) :
    S.refuseProb hr s m ≤ ε := by
  unfold refuseProb
  refine S.prob_completenessDraw_le (fun keys d => S.Supported (S.honestRing hr keys) ∧
    (S.sign (S.keyGen (keys s)) (S.honestRing hr keys) m d.2).run d.1 = none) fun keys => ?_
  by_cases ha : S.Supported (S.honestRing hr keys)
  · refine (PMF.toOuterMeasure_mono _ fun d hd => ?_).trans
      (h (keys s) _ m (S.pk_mem_honestRing hr keys s) ha)
    exact hd.1.2
  · refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_) zero_le
    exact Set.disjoint_left.2 fun d _ hd => ha hd.1

/-- **Rejection per key bounds the averaged rejection.** -/
theorem rejectProb_le_of_rejectProbAt {ε : ℝ≥0∞}
    (h : ∀ (kc : S.KeyCoins) (R : KeyRing S.PK N) (m : S.Msg), S.pk kc ∈ R.1 → S.Supported R →
      S.rejectProbAt kc R m ≤ ε) {r : ℕ} (hr : r ≤ N) (s : Fin r) (m : S.Msg) :
    S.rejectProb hr s m ≤ ε := by
  unfold rejectProb
  refine S.prob_completenessDraw_le (fun keys d => S.Supported (S.honestRing hr keys) ∧
    ∃ σ, (S.sign (S.keyGen (keys s)) (S.honestRing hr keys) m d.2).run d.1 = some σ ∧
      S.verify d.1 (S.honestRing hr keys) m σ = false) fun keys => ?_
  by_cases ha : S.Supported (S.honestRing hr keys)
  · refine (PMF.toOuterMeasure_mono _ fun d hd => ?_).trans
      (h (keys s) _ m (S.pk_mem_honestRing hr keys s) ha)
    exact hd.1.2
  · refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_) zero_le
    exact Set.disjoint_left.2 fun d _ hd => ha hd.1

variable {S} in
/-- **Completeness per key gives completeness** averaged over honest rings
(`CompleteWithin`): the signer's key is in every honest ring of its user. -/
theorem CompleteAtWithin.completeWithin {εr εv : ℝ≥0∞} (h : S.CompleteAtWithin εr εv) :
    S.CompleteWithin εr εv :=
  ⟨fun _ hr s m => S.refuseProb_le_of_refuseProbAt h.refuseProbAt_le hr s m,
    fun _ hr s m => S.rejectProb_le_of_rejectProbAt h.rejectProbAt_le hr s m⟩

/-- **The trivial scheme is complete per key with errors `0` and `0`** (`CompleteAtWithin` is
satisfiable). -/
theorem trivial_completeAtWithin : (trivial X Y N).CompleteAtWithin 0 0 := by
  constructor
  · intro kc R m hR _
    refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
    refine Set.disjoint_left.2 fun d _ hd => ?_
    simp only [Set.mem_ofPred_eq] at hd
    change (if _ ∈ _ then some () else none) = none at hd
    split_ifs at hd
  · intro kc R m _ _
    refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
    refine Set.disjoint_left.2 fun d _ hd => ?_
    simp only [Set.mem_ofPred_eq] at hd
    obtain ⟨σ, -, hv⟩ := hd
    exact Bool.noConfusion hv

end RingScheme

/-! ### The base signer: refusal per key and the honest pair -/

namespace BaseSigner

variable {X Y : Type} {N : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  (B : BaseSigner X Y N TS RMsg)

variable [DecidableEq TS.PK] [Fintype TS.Coins] [Nonempty TS.Coins]

/-- **The per-key refusal rate of the ring-aware signer is at most `ρ`** on the supported rings
`adm`: at every oracle `H`, for every key-generation coins `kc`, every supported ring `R` holding
their public key and every message `m`, `bsign` at the key's first position refuses with
probability at most `ρ` over uniform signing coins. For signers whose refusal does not depend on the
other members' keys (the generic rings). -/
def RefuseAtWithin (adm : KeyRing B.PK N → Prop) (ρ : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N), B.pk kc ∈ R.1 → adm R → ∀ m : B.Msg,
    Pr[c ~ PMF.uniformOfFintype B.Coins :
      (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H = none] ≤ ρ

/-- **The per-key refusal rate of the ring-aware signer is at most `ρ` on every ring**: at every
oracle `H`, for every key-generation coins `kc`, every ring `R` holding their public key (supported
or not) and every message `m`, `bsign` at the key's first position refuses with probability at most
`ρ` over uniform signing coins. -/
def RefuseKeyWithin (ρ : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (m : B.Msg), B.pk kc ∈ R.1 →
    Pr[c ~ PMF.uniformOfFintype B.Coins :
      (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H = none] ≤ ρ

/-- Every ring-aware signer has per-key refusal rate at most `1` on every ring. -/
theorem refuseKeyWithin_one : B.RefuseKeyWithin 1 :=
  fun _ _ _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

variable [Fintype TS.KeyCoins] [Nonempty TS.KeyCoins]

/-- **The refusal rate of the ring-aware signer averaged over the honest key coins is at most `ρ`**
on the supported rings `adm`: the average, over uniform key-generation coins `kc`, of the largest
refusal probability over uniform signing coins of `bsign` at the key's first position, over the
oracles `H`, the supported rings `R` holding the key and the messages `m`, is at most `ρ`. A key
with a high refusal rate counts at its probability. -/
def RefuseAvgWithin (adm : KeyRing B.PK N → Prop) (ρ : ℝ≥0∞) : Prop :=
  ∑' kc, PMF.uniformOfFintype B.KeyCoins kc *
      ⨆ (H : X → Y) (R : KeyRing B.PK N) (_ : B.pk kc ∈ R.1) (_ : adm R) (m : B.Msg),
        Pr[c ~ PMF.uniformOfFintype B.Coins :
          (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H = none] ≤ ρ

/-- **A per-key refusal bound is an averaged one** at the same rate. -/
theorem RefuseAtWithin.refuseAvgWithin {adm : KeyRing B.PK N → Prop} {ρ : ℝ≥0∞}
    (h : B.RefuseAtWithin adm ρ) : B.RefuseAvgWithin adm ρ := by
  refine (ENNReal.tsum_le_tsum fun kc => mul_le_mul_of_nonneg_left
    (iSup_le fun H => iSup_le fun R => iSup_le fun hk => iSup_le fun ha => iSup_le fun m =>
      h H kc R hk ha m) zero_le).trans ?_
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype TS.KeyCoins] [Nonempty TS.KeyCoins] in
/-- Every ring-aware signer has per-key refusal rate at most `1`. -/
theorem refuseAtWithin_one (adm : KeyRing B.PK N → Prop) : B.RefuseAtWithin adm 1 :=
  fun _ _ _ _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

/-- Every ring-aware signer has averaged refusal rate at most `1`. -/
theorem refuseAvgWithin_one (adm : KeyRing B.PK N → Prop) : B.RefuseAvgWithin adm 1 :=
  (B.refuseAtWithin_one adm).refuseAvgWithin

/-- **The uniform-signature base signer never refuses** (`RefuseAtWithin` at `0`). -/
theorem uniformSig_refuseAtWithin (k : ℕ) (adm : KeyRing Unit N → Prop) :
    (uniformSig X Y N k).RefuseAtWithin adm 0 := by
  intro H kc R _ _ m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  have h : (some c : Option (Fin (k + 1))) = none := hc
  exact Option.some_ne_none _ h

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The per-key refusal rate bounds the averaged refusal rate**: `RefuseAtWithin` gives
`RefuseWithin` (the signer's key is in every honest ring of its user). -/
theorem RefuseAtWithin.refuseWithin {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
    [Fintype TS.KeyCoins]
    [Nonempty TS.KeyCoins] [Fintype TS.Coins] [Nonempty TS.Coins] {B : BaseSigner X Y N TS RMsg}
    {adm : KeyRing B.PK N → Prop}
    {ρ : ℝ≥0∞} (h : B.RefuseAtWithin adm ρ) : B.RefuseWithin adm ρ := by
  intro r hr s m
  let eqv : (Fin r → B.KeyCoins) × ((X → Y) × B.Coins) ≃ B.RefusalDraw r :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun d => (d.2.1, d.1, d.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold refuseProb
  change probUniform _ (fun d : B.RefusalDraw r => adm (B.honestRing hr d.2.1) ∧
    (B.bsign (B.sk (d.2.1 s)) (B.honestRing hr d.2.1)
      ((B.honestRing hr d.2.1).1.idxOf (B.pk (d.2.1 s))) m d.2.2).run d.1 = none) ≤ ρ
  rw [← QROM.probUniform_equiv eqv]
  refine ROM.probUniform_prod_le fun keys => ?_
  by_cases ha : adm (B.honestRing hr keys)
  · refine ROM.probUniform_prod_le fun H => ?_
    refine (QROM.probUniform_mono fun c hc => hc.2).trans ?_
    exact h H (keys s) (B.honestRing hr keys) (List.mem_ofFn.2 ⟨s, rfl⟩) ha m
  · rw [QROM.probUniform_eq_zero fun d hd => ha hd.1]
    exact zero_le

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- **The marginal of one coordinate of uniform key coins is uniform**: for `f` on the key coins,
`∑_{keys} u(keys) f(keys s) = ∑_{kc} u(kc) f(kc)` with `u` the uniform weights. -/
theorem tsum_uniformOfFintype_pi_eval {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {r : ℕ}
    (s : Fin r) (f : K → ℝ≥0∞) :
    ∑' keys : Fin r → K, PMF.uniformOfFintype (Fin r → K) keys * f (keys s) =
      ∑' kc : K, PMF.uniformOfFintype K kc * f kc := by
  classical
  let e := Equiv.piSplitAt s fun _ : Fin r => K
  have hcard : Fintype.card (Fin r → K) =
      Fintype.card K * Fintype.card ({j // j ≠ s} → K) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hR : (Fintype.card ({j // j ≠ s} → K) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hRt : (Fintype.card ({j // j ≠ s} → K) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hKt : (Fintype.card K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [tsum_fintype, PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    ← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [e, Equiv.piSplitAt_symm_apply, ↓reduceDIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [hcard, Nat.cast_mul, ENNReal.mul_inv (Or.inl hK) (Or.inl hKt), Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun kc _ => ?_
  rw [mul_assoc, ← mul_assoc _ (Fintype.card ({j // j ≠ s} → K) : ℝ≥0∞),
    ENNReal.inv_mul_cancel hR hRt, one_mul]

/-- **The averaged refusal rate bounds the refusal probability**: `RefuseAvgWithin` gives
`RefuseWithin` at the same rate. For every honest ring and position, the refusal probability
given the members' key coins is at most the largest refusal probability of the signer's key over
the oracles, supported rings holding it and messages; averaging it over the signer's own key coins
is the averaged rate (`tsum_uniformOfFintype_pi_eval`). -/
theorem RefuseAvgWithin.refuseWithin {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
    [Fintype TS.KeyCoins]
    [Nonempty TS.KeyCoins] [Fintype TS.Coins] [Nonempty TS.Coins] {B : BaseSigner X Y N TS RMsg}
    {adm : KeyRing B.PK N → Prop}
    {ρ : ℝ≥0∞} (h : B.RefuseAvgWithin adm ρ) : B.RefuseWithin adm ρ := by
  classical
  intro r hr s m
  let eqv : (Fin r → B.KeyCoins) × ((X → Y) × B.Coins) ≃ B.RefusalDraw r :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun d => (d.2.1, d.1, d.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold refuseProb
  change probUniform _ (fun d : B.RefusalDraw r => adm (B.honestRing hr d.2.1) ∧
    (B.bsign (B.sk (d.2.1 s)) (B.honestRing hr d.2.1)
      ((B.honestRing hr d.2.1).1.idxOf (B.pk (d.2.1 s))) m d.2.2).run d.1 = none) ≤ ρ
  rw [← QROM.probUniform_equiv eqv, probUniform_prod_eq_tsum]
  refine (ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le).trans
    ((tsum_uniformOfFintype_pi_eval s _).trans_le h)
  by_cases ha : adm (B.honestRing hr keys)
  · refine ROM.probUniform_prod_le fun H => ?_
    refine (QROM.probUniform_mono fun c hc => hc.2).trans ?_
    exact le_iSup_of_le H (le_iSup_of_le (B.honestRing hr keys)
      (le_iSup_of_le (List.mem_ofFn.2 ⟨s, rfl⟩) (le_iSup_of_le ha (le_iSup_of_le m le_rfl))))
  · rw [QROM.probUniform_eq_zero fun d hd => ha hd.1]
    exact zero_le

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq TS.PK] [Fintype TS.KeyCoins]
  [Nonempty TS.KeyCoins] [Fintype TS.Coins] [Nonempty TS.Coins]

/-- **Base verification and the public value read no oracle**: `bverify` is the same function at
every oracle, and so is the result of every public-value program. The Falcon-512 and ML-DSA base
signers satisfy it (`falconBaseSigner_verifiesWithoutOracle`,
`mldsaBaseSigner_verifiesWithoutOracle`, `GordieHowe/Applications/Ring/BaseSignerFacts.lean`). -/
structure VerifiesWithoutOracle : Prop where
  /-- Base verification does not depend on the oracle. -/
  bverify_eq : ∀ H H' : X → Y, B.bverify H = B.bverify H'
  /-- The public value does not depend on the oracle. -/
  run_pub_eq : ∀ (pk : B.PK) (σ : B.BSig) (H H' : X → Y), (B.pub pk σ).run H = (B.pub pk σ).run H'

variable {B} in
/-- **An oracle-free base signer verifies without the oracle**: `OracleFree` (its signers and
public value make no queries, and base verification is the same at every oracle) implies
`VerifiesWithoutOracle`, so `OracleFree` is the stronger hypothesis. -/
theorem OracleFree.verifiesWithoutOracle (h : B.OracleFree) : B.VerifiesWithoutOracle :=
  ⟨h.bverify_eq, h.run_pub_eq⟩

/-- The uniform-signature base signer verifies without the oracle. -/
theorem uniformSig_verifiesWithoutOracle (k : ℕ) : (uniformSig X Y N k).VerifiesWithoutOracle :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

variable {B} in
/-- **Without oracle reads in verification, the ring relation does not depend on the oracle.** -/
theorem VerifiesWithoutOracle.ringRel_eq (h : B.VerifiesWithoutOracle) (adm : KeyRing B.PK N → Prop)
    (H H' : X → Y) : ringRel B adm H = ringRel B adm H' := by
  have hsub : ∀ H H' : X → Y, ringRel B adm H ⊆ ringRel B adm H' := fun H H' p hp =>
    show RingRel B adm H' p.1 p.2 from
      ⟨hp.supported, hp.idx_lt, by rw [← h.bverify_eq H H']; exact hp.verify_eq,
        by rw [← h.run_pub_eq _ _ H H']; exact hp.pub_eq⟩
  exact Set.Subset.antisymm (hsub H H') (hsub H' H)

/-- **The statement and witness of an honest ring signature** as an oracle program from the base
signer's coins: run `bsign` of `sk` at position `i` of `R` on `m`; on a refusal output nothing;
on a base signature `σ` output the statement `(R, m, y)` with `y` the public value of `σ` under
`pk`, and the witness `(i, σ)`. -/
def ringPairProg (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (c : B.Coins) :
    OracleProg X Y (Option (RingStmt B × RingWit B)) :=
  (B.bsign sk R i m c).bind fun
    | none => .pure none
    | some σ => (B.pub pk σ).mapOutput fun y => some (⟨R, m, y⟩, ⟨i, σ⟩)

/-- The honest pair makes at most `q + qPub` queries. -/
theorem ringPairProg_queries (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : B.Coins) : (B.ringPairProg pk sk R i m c).QueriesLE (B.q + B.qPub) := by
  refine (B.bsign_queries sk R i m c).bind fun o => ?_
  rcases o with _ | σ
  · exact OracleProg.QueriesLE.pure _ _
  · exact (B.pub_queries pk σ).mapOutput _

/-- **The honest pair of a base signature**: when `bsign` outputs `σ`, the program outputs the
statement with the public value of `σ` and the witness `(i, σ)`. -/
theorem run_ringPairProg_of_bsign {H : X → Y} {pk : B.PK} {sk : B.SK} {R : KeyRing B.PK N} {i : ℕ}
    {m : B.Msg} {c : B.Coins} {σ : B.BSig} (hσ : (B.bsign sk R i m c).run H = some σ) :
    (B.ringPairProg pk sk R i m c).run H = some (⟨R, m, (B.pub pk σ).run H⟩, ⟨i, σ⟩) := by
  simp only [ringPairProg, OracleProg.run_bind, hσ, OracleProg.run_mapOutput]

end BaseSigner

/-! ### Completeness of `ofBase` -/

variable {X Y : Type} {N : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  (B : BaseSigner X Y N TS RMsg) {TPS : PSTypes} (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
  [Fintype TPS.Coins] [Nonempty TPS.Coins]
  (adm : KeyRing B.PK N → Prop) [DecidablePred adm] [Fintype X] [DecidableEq X] [Fintype Y]
  [Nonempty Y]

variable [DecidableEq TS.PK] [Fintype TS.Coins] [Nonempty TS.Coins]

/-- **The refusal of `ofBase` at a key is that of its base signer**: on a supported ring holding
the key, at most the per-key refusal rate `ρ`. -/
theorem refuseProbAt_ofBase_le {ρ : ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ) {kc : B.KeyCoins}
    {R : KeyRing B.PK N} (hR : B.pk kc ∈ R.1) (ha : adm R) (m : B.Msg) :
    (ofBase B PS adm).refuseProbAt kc R m ≤ ρ := by
  have hs : ∀ c, (ofBase B PS adm).sign ((ofBase B PS adm).keyGen kc) R m c =
      signAt B PS (B.pk kc) (B.sk kc) R (R.1.idxOf (B.pk kc)) m c :=
    fun c => sign_ofBase_of_mem B PS adm (kp := B.keyGen kc) hR ha m c
  unfold RingScheme.refuseProbAt
  change probUniform ((X → Y) × (B.Coins × PS.Coins))
    (fun d => ((ofBase B PS adm).sign ((ofBase B PS adm).keyGen kc) R m d.2).run d.1 = none) ≤ ρ
  refine ROM.probUniform_prod_le fun H => ?_
  refine (QROM.probUniform_mono (E' := fun c : B.Coins × PS.Coins =>
    (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c.1).run H = none) fun c hc => ?_).trans ?_
  · erw [hs c] at hc
    exact (BaseSigner.run_signAt_eq_none_iff B PS).1 hc
  · rw [ROM.probUniform_prod_fst
      (fun c₁ => (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c₁).run H = none)]
    exact hρ H kc R hR ha m

/-- **The rejection of `ofBase` at a key**: on a supported ring holding the key, at most the base
signer's correctness error `εc` plus the adaptive completeness error `εp` of the proof system for
the ring relation at the `q + qPub` queries of the honest pair (`ringPairProg`). An honest
signature is rejected only if its base signature fails base verification, or if it verifies, so
that the pair is in the ring relation at the oracle, and the proof is rejected. -/
theorem rejectProbAt_ofBase_le {εc : ℝ≥0∞} {εp : ℕ → ℝ≥0∞} (hc : B.CorrectWithin εc)
    (hp : PS.CompleteWithin (ringRel B adm) εp) {kc : B.KeyCoins} {R : KeyRing B.PK N}
    (hR : B.pk kc ∈ R.1) (ha : adm R) (m : B.Msg) :
    (ofBase B PS adm).rejectProbAt kc R m ≤ εc + εp (B.q + B.qPub) := by
  have hi : R.1.idxOf (B.pk kc) < R.1.length := List.idxOf_lt_length_iff.2 hR
  have hget : R.1[R.1.idxOf (B.pk kc)]'hi = B.pk kc := List.getElem_idxOf hi
  have hget' : R.1[R.1.idxOf (B.pk kc)]? = some (B.pk kc) := by
    rw [List.getElem?_eq_getElem hi, hget]
  have hs : ∀ c, (ofBase B PS adm).sign ((ofBase B PS adm).keyGen kc) R m c =
      signAt B PS (B.pk kc) (B.sk kc) R (R.1.idxOf (B.pk kc)) m c :=
    fun c => sign_ofBase_of_mem B PS adm (kp := B.keyGen kc) hR ha m c
  unfold RingScheme.rejectProbAt
  change probUniform ((X → Y) × (B.Coins × PS.Coins))
    (fun d => ∃ s, ((ofBase B PS adm).sign ((ofBase B PS adm).keyGen kc) R m d.2).run d.1 = some s ∧
      (ofBase B PS adm).verify d.1 R m s = false) ≤ _
  refine (QROM.probUniform_mono (E' := fun d : (X → Y) × (B.Coins × PS.Coins) =>
    (∃ σ, (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m d.2.1).run d.1 = some σ ∧
      B.bverify d.1 (B.pk kc) (B.bmsg R m) σ = false) ∨
    ∃ p, (B.ringPairProg (B.pk kc) (B.sk kc) R (R.1.idxOf (B.pk kc)) m d.2.1).run d.1 = some p ∧
      p ∈ ringRel B adm d.1 ∧ PS.verify d.1 p.1 ((PS.prove p.1 p.2 d.2.2).run d.1) = false)
    fun d hd => ?_).trans ((QROM.probUniform_or_le _ _).trans (add_le_add ?_ ?_))
  · obtain ⟨s, hsgn, hv⟩ := hd
    erw [hs d.2] at hsgn
    replace hsgn : (signAt B PS (B.pk kc) (B.sk kc) R (R.1.idxOf (B.pk kc)) m d.2).run d.1 =
        some (show B.Pub × PS.Proof from s) := hsgn
    rcases hσ : (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m d.2.1).run d.1 with _ | σ
    · rw [(BaseSigner.run_signAt_eq_none_iff B PS).2 hσ] at hsgn
      exact absurd hsgn (by simp)
    · rw [run_signAt_of_bsign B PS hσ] at hsgn
      obtain rfl := Option.some.inj hsgn
      cases hbv : B.bverify d.1 (B.pk kc) (B.bmsg R m) σ
      · exact Or.inl ⟨σ, rfl, hbv⟩
      · refine Or.inr ⟨_, B.run_ringPairProg_of_bsign hσ, ?_, hv⟩
        exact (show RingRel B adm d.1 _ _ from
          ⟨ha, hi, by rw [hget]; exact hbv, by rw [hget]⟩)
  · refine ROM.probUniform_prod_le fun H => ?_
    rw [ROM.probUniform_prod_fst (fun c₁ => ∃ σ,
      (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c₁).run H = some σ ∧
        B.bverify H (B.pk kc) (B.bmsg R m) σ = false)]
    exact hc H kc R _ hget' m
  · exact hp (B.q + B.qPub) B.Coins _ fun c => B.ringPairProg_queries _ _ _ _ _ c

/-- **Completeness of `ofBase` per key** (BKM06 Definition 1 with errors, per key): for a base
signer with per-key refusal rate `ρ` and correctness error `εc`, and a proof system adaptively
complete for the ring relation at error `εp`, at every key and every supported ring holding it the
ring signature refuses with probability at most `ρ` and is rejected with probability at most
`εc + εp (q + qPub)`. -/
@[headline]
theorem completeAtWithin_ofBase {ρ εc : ℝ≥0∞} {εp : ℕ → ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ)
    (hc : B.CorrectWithin εc) (hp : PS.CompleteWithin (ringRel B adm) εp) :
    (ofBase B PS adm).CompleteAtWithin ρ (εc + εp (B.q + B.qPub)) :=
  ⟨fun _ _ m hR ha => refuseProbAt_ofBase_le B PS adm hρ hR ha m,
    fun _ _ m hR ha => rejectProbAt_ofBase_le B PS adm hc hp hR ha m⟩

variable [Fintype TS.KeyCoins] [Nonempty TS.KeyCoins]

/-- **Completeness of `ofBase`** (BKM06 Definition 1 with errors, averaged over honest rings): for
a base signer with refusal rate `ρ` on honest rings (`RefuseWithin`) and correctness error `εc`,
and a proof system adaptively complete for the ring relation at error `εp`, the ring signature
refuses an honest supported ring with probability at most `ρ` and is rejected with probability at
most `εc + εp (q + qPub)`. -/
@[headline]
theorem completeWithin_ofBase {ρ εc : ℝ≥0∞} {εp : ℕ → ℝ≥0∞} (hρ : B.RefuseWithin adm ρ)
    (hc : B.CorrectWithin εc) (hp : PS.CompleteWithin (ringRel B adm) εp) :
    (ofBase B PS adm).CompleteWithin ρ (εc + εp (B.q + B.qPub)) :=
  ⟨fun r hr s m => (BaseSigner.refuseProb_ofBase_eq B PS adm hr s m).le.trans (hρ r hr s m),
    fun _ hr s m => (ofBase B PS adm).rejectProb_le_of_rejectProbAt (ε := εc + εp (B.q + B.qPub))
      (fun _ _ m hR ha => rejectProbAt_ofBase_le B PS adm hc hp hR ha m) hr s m⟩

omit [DecidablePred adm] in
/-- **The hypotheses of the completeness headlines hold together**: the uniform-signature base
signer (per-key refusal `0`, correctness error `0`) with the accepting proof system (adaptive
completeness error `0`) is complete per key with errors `0` and `0`. -/
theorem completeAtWithin_ofBase_satisfiable (k : ℕ)
    (adm₀ : KeyRing (BaseSigner.uniformSig X Y N k).PK N → Prop)
    [DecidablePred adm₀] :
    (ofBase (BaseSigner.uniformSig X Y N k) (ProofSystem.acceptAll X Y _ _) adm₀).CompleteAtWithin
      0 (0 + 0) :=
  completeAtWithin_ofBase _ _ adm₀ (BaseSigner.uniformSig_refuseAtWithin k adm₀)
    (BaseSigner.uniformSig_correctWithin k) (ProofSystem.acceptAll_completeWithin _)

end GordieHowe.RingSignature
