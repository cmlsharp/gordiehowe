-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeMain
public import GordieHowe.Applications.Ring.RingInsider

@[expose] public section

/-!
# The zero-knowledge hop of the key-free route

The zero-knowledge hop of the key-free unforgeability route, generic in the adversary: against the
main challenger `kfMain` (`GordieHowe/Applications/Ring/KeyFreeMain.lean`) with the real
challenger of the compiled spBCS prover, an adversary passes a classical test of its output and
its requests, run at the final oracle in force, with at most the probability against the
simulated main challenger `kfMainSim` with the spBCS joint simulator, plus `zkError δ t Q`
(`SPBCS.everlastingZeroKnowledge_qrom`, for a composite that is honest-verifier zero knowledge).
The multi-user requests are absorbed into dummy proof queries outside the relation (L1,
`outLaw_kfMain`, `outLaw_kfMainSim`), so the distinguisher is the adversary absorbed and followed
by the test.

- `kfAbsorbed`, `kfTest`, `kfDist`: the distinguisher at one auxiliary value.
  `outLaw_kfDist_real`, `outLaw_kfDist_sim`: its acceptance at each oracle is the test's against
  `kfMain` and `kfMainSim`. `acceptProb_kfDist`, `acceptProb_kfDist_le_one`.
- `acceptKAt`, `acceptK`: the probability that the test accepts, at one auxiliary value and
  averaged over the auxiliary input, the oracle uniform.
- `acceptKAt_kfMain_le`, `acceptK_kfMain_le` (**the hop**).
-/

namespace GordieHowe

open Quantum Signature
open scoped ENNReal

namespace RingSignature

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm

section SPBCS

variable {k kN kS L e N n t kq : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {TB : BaseTypes} {B : BaseSigner Xb Yb N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : Wit₀ → R → CausalProver P τ X₀}
  {Stmt Wit : Type} [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  [Inhabited (ProofQuery Stmt Wit)] {stmtX : Stmt → X₀} {fw : Wit → Wit₀}
  {relH : Set (X₀ × Wit₀)} {rel : Stmt → Wit → Prop} [DecidableRel rel]
  {Rq O : Type} [Fintype Rq] [DecidableEq Rq]
  {enc : MURequest (SignOracle.none B) n ⊕ Rq → ProofQuery Stmt Wit}

local notation "𝒫z" => Insider.encProver M Λ E hb honest

variable (A' : QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
    (MURequest (SignOracle.none B) n ⊕ Rq) (MUResponse B ⊕ M.Response b) O t)
  (test : O → List (MURequest (SignOracle.none B) n ⊕ Rq) →
    OracleProg (Bits (queryBits k kN kS L)) (XOut k e) Bool)

/-- **The adversary at the auxiliary value `a` with its multi-user requests absorbed** into dummy
proof queries (`SideRelay.dummyRelay` at the replies `keyReplyNone keys`). -/
noncomputable abbrev kfAbsorbed (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux) :=
  AdaptiveIAlg.absorb (A'.alg a) (SideRelay.dummyRelay (keyReplyNone B keys) enc Q)

/-- **The test on an absorbed workspace**: `test` at its output and its logged requests. -/
noncomputable abbrev kfTest (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux)
    (w : (kfAbsorbed A' (enc := enc) keys Q a).W) :
    OracleProg (Bits (queryBits k kN kS L)) (XOut k e) Bool :=
  test ((A'.alg a).out w.work) (Quantum.requests w.logs)

/-- **The distinguisher of the key-free route's zero-knowledge hop** at the auxiliary value `a`:
the adversary with its multi-user requests absorbed (`kfAbsorbed`), followed by the test
(`kfTest`). -/
noncomputable def kfDist (henc : Function.Injective enc)
    (htest : ∀ o rs, (test o rs).QueriesLE kq) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux) :
    QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e) (ProofQuery Stmt Wit)
      (M.Response b) Bool
      ((A'.alg a).width * ((A'.alg a).budget + (A'.alg a).post) + (A'.alg a).width * kq) where
  Aux := Unit
  aux := PMF.pure ()
  sh _ := (A'.sh a).absorbS.thenProgS kq
  alg _ := (kfAbsorbed A' (enc := enc) keys Q a).thenProg (kfTest A' test keys Q a) kq
    fun _ => htest _ _
  tracePreserving _ := AdaptiveIAlg.thenProg_tracePreserving (kfAbsorbed A' (enc := enc) keys Q a)
    (kfTest A' test keys Q a) kq (fun _ => htest _ _)
    (AdaptiveIAlg.absorb_tracePreserving (A'.alg a) _ (A'.tracePreserving a))
  withinBudget _ := AdaptiveIAlg.withinBudget_thenProg (kfAbsorbed A' (enc := enc) keys Q a)
    (kfTest A' test keys Q a) kq (fun _ => htest _ _)
    (AdaptiveIAlg.absorb_withinBudget (A'.alg a) _ (fun _ => henc) (A'.withinBudget a))
  queries_le _ := (AdaptiveIAlg.thenProg_queries (kfAbsorbed A' (enc := enc) keys Q a)
    (kfTest A' test keys Q a) kq (fun _ => htest _ _)).le

/-- **The probability that the test accepts at one auxiliary value**: the oracle uniform, the
test run on the output and the requests at the final oracle in force. -/
noncomputable def acceptKAt (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (MURequest (SignOracle.none B) n ⊕ Rq) (MUResponse B ⊕ M.Response b))
    (a : A'.Aux) : ℝ≥0∞ :=
  ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
    (((A'.alg a).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
      {o | ∃ v ∈ o, (test ((A'.alg a).out v.adv.workspace.1) (Quantum.requests v.chal.logs)).run
        (H.reprogram ((A'.alg a).toKindAlg.postAss C v.chal)) = true}

/-- **The probability that the test accepts**, averaged over the auxiliary input. -/
noncomputable def acceptK (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (MURequest (SignOracle.none B) n ⊕ Rq) (MUResponse B ⊕ M.Response b)) :
    ℝ≥0∞ :=
  ∑' a, A'.aux a * acceptKAt A' test C a

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The acceptance probability of the distinguisher** is the oracle average of its output law
at `true`. -/
theorem acceptProb_kfDist (henc : Function.Injective enc)
    (htest : ∀ o rs, (test o rs).QueriesLE kq) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (ProofQuery Stmt Wit)
      (M.Response b)) :
    (kfDist A' test henc htest keys Q a).acceptProb C =
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((kfDist A' test henc htest keys Q a).alg ()).compose C).outLaw H (some true) := by
  simp only [QueryBoundedAdversary.acceptProb, kfDist]
  rw [tsum_eq_single () fun u hu => absurd (Subsingleton.elim u ()) hu]
  erw [PMF.pure_apply_self, one_mul]
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  rw [PMF.toOuterMeasure_map_apply]
  have : (fun o => (⟨o, Equiv.refl _ ∘ H⟩ :
      Outcome (Option Bool) (Bits (queryBits k kN kS L)) (XOut k e))) ⁻¹'
      {p | p.out = some true} = {some true} := by
    ext o
    simp
  rw [this, PMF.toOuterMeasure_apply_singleton]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The acceptance probability of the distinguisher is at most `1`. -/
theorem acceptProb_kfDist_le_one (henc : Function.Injective enc)
    (htest : ∀ o rs, (test o rs).QueriesLE kq) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (ProofQuery Stmt Wit)
      (M.Response b)) :
    (kfDist A' test henc htest keys Q a).acceptProb C ≤ 1 := by
  rw [acceptProb_kfDist]
  calc _ ≤ ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H * 1 :=
        ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (PMF.coe_le_one _ _) zero_le
    _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open Classical in
/-- **The distinguisher against the real challenger is the test against `kfMain`** at every
oracle (L1, `outLaw_kfMain`). -/
theorem outLaw_kfDist_real (henc : Function.Injective enc)
    (htest : ∀ o rs, (test o rs).QueriesLE kq) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((kfDist A' test henc htest keys Q a).alg ()).compose
        (realChallenger rel ((𝒫z).comap stmtX fw) Q)).outLaw H (some true) =
      (((A'.alg a).toKindAlg.composeBothOut (kfMain B rel ((𝒫z).comap stmtX fw) enc keys Q)
          id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, (test ((A'.alg a).out v.adv.workspace.1) (Quantum.requests v.chal.logs)).run
          (H.reprogram ((A'.alg a).toKindAlg.postAss
            (kfMain B rel ((𝒫z).comap stmtX fw) enc keys Q) v.chal)) = true} := by
  have h := outLaw_kfMain B rel ((𝒫z).comap stmtX fw) enc henc keys Q (A'.alg a) H
    fun adv lg _ _ G => (test ((A'.alg a).out adv.workspace.1) (Quantum.requests lg)).run G = true
  refine Eq.trans ?_ h.symm
  change (((kfAbsorbed A' (enc := enc) keys Q a).thenProg (kfTest A' test keys Q a) kq
    fun _ => htest _ _).compose _).outLaw H (some true) = _
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The distinguisher against the simulated challenger is the test against `kfMainSim`** at
every oracle (L1, `outLaw_kfMainSim`), for dummy proof queries outside the relation (`hd`). -/
theorem outLaw_kfDist_sim (henc : Function.Injective enc)
    (hd : ∀ r, ¬ rel (enc (.inl r)).stmt (enc (.inl r)).wit)
    (htest : ∀ o rs, (test o rs).QueriesLE kq) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux)
    {SC : Type} [Fintype SC] [DecidableEq SC]
    (S : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) Stmt (M.Response b) SC)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((kfDist A' test henc htest keys Q a).alg ()).compose (simChallenger rel S Q)).outLaw H
        (some true) =
      (((A'.alg a).toKindAlg.composeBothOut (kfMainSim B rel S enc keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, (test ((A'.alg a).out v.adv.workspace.1) (Quantum.requests v.chal.logs)).run
          (H.reprogram ((A'.alg a).toKindAlg.postAss (kfMainSim B rel S enc keys Q) v.chal)) =
            true} := by
  have h := outLaw_kfMainSim B rel S enc henc hd keys Q (A'.alg a) H
    fun adv lg _ _ G => (test ((A'.alg a).out adv.workspace.1) (Quantum.requests lg)).run G = true
  refine Eq.trans ?_ h.symm
  change (((kfAbsorbed A' (enc := enc) keys Q a).thenProg (kfTest A' test keys Q a) kq
    fun _ => htest _ _).compose _).outLaw H (some true) = _
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2

open Classical in
/-- **The key-free route's zero-knowledge hop at one auxiliary value**: the test accepts against
`kfMain` (the real challenger of the compiled spBCS prover at the statements `stmtX` and the
decoded witnesses `fw`) with at most its probability against `kfMainSim` (the spBCS joint
simulator at `stmtX`) plus `zkError δ t Q`, for a relation `rel` that is `relH` read through
`stmtX` and `fw` (`hrel`), an injective `enc` with dummy proof queries outside `rel` (`hd`), a
test of at most `kq` queries (`htest`) and a composite that is honest-verifier zero knowledge for
`relH` (`hvzk`). -/
theorem acceptKAt_kfMain_le (hrel : ∀ x w, rel x w ↔ (stmtX x, fw w) ∈ relH)
    (henc : Function.Injective enc) (hd : ∀ r, ¬ rel (enc (.inl r)).stmt (enc (.inl r)).wit)
    (htest : ∀ o rs, (test o rs).QueriesLE kq)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) {δ : NNReal} (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux) :
    acceptKAt A' test (kfMain B rel ((𝒫z).comap stmtX fw) enc keys Q) a ≤
      acceptKAt A' test (kfMainSim B rel
        ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap stmtX) enc keys Q) a +
        ENNReal.ofReal (M.zkError δ t Q) := by
  have hzk := M.everlastingZeroKnowledge_qrom Λ honest E VE hb T stmtX fw hvzk
  unfold NARG.QROM.EverlastingZeroKnowledge at hzk
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    M.encode_niSimulator Λ E VE hb] at hzk
  have hD : (kfDist A' test henc htest keys Q a).QueriesBeforeLastProofQuery t := fun _ =>
    ⟨(A'.alg a).budget,
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (A'.queries_le a),
      AdaptiveIAlg.requestsAfterAtMost_thenProg (kfAbsorbed A' (enc := enc) keys Q a)
        (kfTest A' test keys Q a) _ fun _ => htest _ _⟩
  have key : ∀ x y : ℝ≥0∞, x ≤ 1 → y ≤ 1 →
      GordieHowe.advantage x.toReal y.toReal ≤ M.zkError δ t Q →
      x ≤ y + ENNReal.ofReal (M.zkError δ t Q) := fun x y hx hy h => by
    have h' : |x.toReal - y.toReal| ≤ M.zkError δ t Q := h
    have hz : 0 ≤ M.zkError δ t Q := (abs_nonneg _).trans h'
    have hr : x.toReal ≤ y.toReal + M.zkError δ t Q := by
      linarith [le_abs_self (x.toReal - y.toReal)]
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hy),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hz]
    exact ENNReal.ofReal_le_ofReal hr
  have h := hzk t Q _ (kfDist A' test henc htest keys Q a) hD
  have hle : (kfDist A' test henc htest keys Q a).acceptProb
      (realChallenger rel ((𝒫z).comap stmtX fw) Q) ≤
      (kfDist A' test henc htest keys Q a).acceptProb
        (simChallenger rel ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap stmtX) Q) +
        ENNReal.ofReal (M.zkError δ t Q) := by
    convert key _ _ (acceptProb_kfDist_le_one A' test henc htest keys Q a _)
      (acceptProb_kfDist_le_one A' test henc htest keys Q a _) h using 3
    · exact funext fun x => funext fun w => propext (hrel x w)
    · exact QROM.simChallenger_congr _ _ _ _ _ _ _ _ hrel _ Q
  rw [acceptProb_kfDist, acceptProb_kfDist] at hle
  simp only [outLaw_kfDist_real, outLaw_kfDist_sim A' test henc hd] at hle
  exact hle

open Classical in
/-- **The key-free route's zero-knowledge hop**: `acceptKAt_kfMain_le` averaged over the
auxiliary input. -/
theorem acceptK_kfMain_le (hrel : ∀ x w, rel x w ↔ (stmtX x, fw w) ∈ relH)
    (henc : Function.Injective enc) (hd : ∀ r, ¬ rel (enc (.inl r)).stmt (enc (.inl r)).wit)
    (htest : ∀ o rs, (test o rs).QueriesLE kq)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) {δ : NNReal} (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    acceptK A' test (kfMain B rel ((𝒫z).comap stmtX fw) enc keys Q) ≤
      acceptK A' test (kfMainSim B rel
        ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap stmtX) enc keys Q) +
        ENNReal.ofReal (M.zkError δ t Q) := by
  unfold acceptK
  calc _ ≤ ∑' a, (A'.aux a * acceptKAt A' test (kfMainSim B rel
          ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap stmtX) enc keys Q) a +
          A'.aux a * ENNReal.ofReal (M.zkError δ t Q)) :=
        ENNReal.tsum_le_tsum fun a => by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left
            (acceptKAt_kfMain_le A' test hrel henc hd htest VE pub Sim T hvzk keys Q a) zero_le
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end SPBCS

end RingSignature

end GordieHowe
