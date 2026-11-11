-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingStrongZKRelays
public import GordieHowe.Applications.Ring.RingInsider

@[expose] public section

/-!
# Zero knowledge in the insider game of `ofBase` whose public values read the key

The zero-knowledge steps of `GordieHowe/Applications/Ring/RingInsider.lean` (BKM06 Definition 7,
`insiderForgeProb`) for the ring signature `ofBase B (spbcsComapProofSystem …) adm` with an
oracle-free base signer (`BaseSigner.OracleFree`) whose public values and refusals need not be
functions of the signing coins. The relays read the users' key coins
(`GordieHowe/Applications/Ring/RingStrongZKRelays.lean`). At fixed keys and auxiliary value, the
game's ring signatures are replaced by checked ones (`Q · εc`), absorbed into proof queries of the
real zero-knowledge challenger, simulated (`zkError`), and unchecked (`Q · εc`); the chain ends at
the simulated game `simSplitK` with the test `True`.

- `zkAbsorbedK`, `zkTestK`, `distinguisherK`: the zero-knowledge distinguisher with the relay
  `zkRelayK`; `acceptProb_distinguisherK`, `acceptProb_distinguisherK_le_one`.
- `game_le_sum_realK`, `acceptProb_real_leK`, `sum_sim_eq_checkedK`: the game to the real
  challenger, zero knowledge, and back to the checked simulated game.
- `game_le_simK_at`: the chain at one key and one auxiliary value.
-/

namespace GordieHowe

open Quantum
open scoped ENNReal

namespace RingSignature.Insider

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm

section SPBCS

variable {k kN kS L e N n t : ℕ} {TB : BaseTypes} [DecidableEq TB.PK]
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : Wit₀ → R → CausalProver P τ X₀} {stmt : RingStmt B → X₀} {check : RingStmt B → Bool}
  {input : RingStmt B → RingWit B → Option Wit₀}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {W' : Type} [Fintype W'] [DecidableEq W']
  [Nonempty W'] {fw : W' → Wit₀} {enc : RingStmt B → RelayWit B → W'}
  {relH : Set (X₀ × Wit₀)}

local notation "𝒫" => Ring.spbcsComapProofSystem M Λ E hb honest stmt check input

local notation "𝒫z" => encProver M Λ E hb honest

variable [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig]

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins]

variable (A : InsiderAdversary
    (ofBase B (Ring.spbcsComapProofSystem M Λ E hb honest stmt check input) adm) n
    (OracleView.queriesOnly (Bits (queryBits k kN kS L)) (XOut k e)) t)

variable [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]

/-! ### The distinguisher of zero knowledge -/

/-- **The adversary with its requests absorbed into proof queries read from the keys**
(`zkRelayK`) at the key coins `keys`, the auxiliary value `a` and the signing coins `ds`. -/
noncomputable abbrev zkAbsorbedK [NeZero n] (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux) (ds : Fin Q → B.Coins) :
    AdaptiveIAlg (((A.at keys).sh a).absorbS (Req' := ProofQuery (RelayStmt B 𝒫 adm n) W')
      (Resp' := (𝒫).Proof)) (Output 𝒫 adm) :=
  AdaptiveIAlg.absorb (Req' := ProofQuery (RelayStmt B 𝒫 adm n) W') (Resp' := (𝒫).Proof)
    ((A.at keys).alg a) (zkRelayK B enc keys ds)

/-- **The forgery test on an absorbed workspace**: `forgeryTest` at its output and its logged
requests. -/
noncomputable abbrev zkTestK [NeZero n] (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux) (ds : Fin Q → B.Coins)
    (w : (zkAbsorbedK A enc keys Q a ds).W) :
    OracleProg (Bits (queryBits k kN kS L)) (XOut k e) Bool :=
  forgeryTest keys Q (((A.at keys).alg a).out w.work) (Quantum.requests w.logs)

/-- **The distinguisher of zero knowledge with the relay read from the keys** at the key coins
`keys`, the auxiliary value `a` and the signing coins `ds`: the adversary with its requests
absorbed (`zkAbsorbedK`: proof queries with the signers' witnesses), followed by the forgery test
(`zkTestK`).

Running time: that of the adversary, plus the relay of each request (at most one base signature
and its public value) and `forgeryTest`. This running time is argued here, not proved in Lean. -/
noncomputable def distinguisherK [NeZero n] (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux) (ds : Fin Q → B.Coins) :
    QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt B 𝒫 adm n) W') (𝒫).Proof Bool
      (((A.at keys).alg a).width * (((A.at keys).alg a).budget + ((A.at keys).alg a).post) +
        ((A.at keys).alg a).width * (M.qVerifier Qs b b).kq) where
  Aux := Unit
  aux := PMF.pure ()
  sh _ := (((A.at keys).sh a).absorbS (Req' := ProofQuery (RelayStmt B 𝒫 adm n) W')
    (Resp' := (𝒫).Proof)).thenProgS (M.qVerifier Qs b b).kq
  alg _ := (zkAbsorbedK A enc keys Q a ds).thenProg (zkTestK A enc keys Q a ds)
    (M.qVerifier Qs b b).kq fun _ => forgeryTest_queriesLE keys Q _ _
  tracePreserving _ := AdaptiveIAlg.thenProg_tracePreserving (zkAbsorbedK A enc keys Q a ds)
    (zkTestK A enc keys Q a ds) (M.qVerifier Qs b b).kq
    (fun _ => forgeryTest_queriesLE keys Q _ _)
    (AdaptiveIAlg.absorb_tracePreserving ((A.at keys).alg a) (zkRelayK B enc keys ds)
      ((A.at keys).tracePreserving a))
  withinBudget _ := AdaptiveIAlg.withinBudget_thenProg (zkAbsorbedK A enc keys Q a ds)
    (zkTestK A enc keys Q a ds) (M.qVerifier Qs b b).kq
    (fun _ => forgeryTest_queriesLE keys Q _ _)
    (AdaptiveIAlg.absorb_withinBudget ((A.at keys).alg a) (zkRelayK B enc keys ds)
      (zkRelayK_route_injective B enc keys ds) ((A.at keys).withinBudget a))
  queries_le _ := (AdaptiveIAlg.thenProg_queries (zkAbsorbedK A enc keys Q a ds)
    (zkTestK A enc keys Q a ds) (M.qVerifier Qs b b).kq
    (fun _ => forgeryTest_queriesLE keys Q _ _)).le

omit [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TB.BMsg] [DecidableEq TB.BMsg]
  [Fintype TB.BSig] [DecidableEq TB.BSig] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The acceptance probability of the distinguisher** is the oracle average of its output law at
`true`. -/
theorem acceptProb_distinguisherK [NeZero n] (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (a : (A.at keys).Aux) (ds : Fin Q → B.Coins)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt B 𝒫 adm n) W') (𝒫).Proof) :
    (distinguisherK A enc keys Q a ds).acceptProb C =
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((distinguisherK A enc keys Q a ds).alg ()).compose C).outLaw H (some true) := by
  simp only [QueryBoundedAdversary.acceptProb, distinguisherK]
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

omit [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TB.BMsg] [DecidableEq TB.BMsg]
  [Fintype TB.BSig] [DecidableEq TB.BSig] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- The acceptance probability of the distinguisher is at most `1`. -/
theorem acceptProb_distinguisherK_le_one [NeZero n] (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (a : (A.at keys).Aux) (ds : Fin Q → B.Coins)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt B 𝒫 adm n) W') (𝒫).Proof) :
    (distinguisherK A enc keys Q a ds).acceptProb C ≤ 1 := by
  rw [acceptProb_distinguisherK]
  calc _ ≤ ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H * 1 :=
        ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (PMF.coe_le_one _ _) zero_le
    _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### Real to simulated ring signatures -/

open Classical in
omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Nonempty TB.KeyCoins] in
/-- **The insider game at fixed keys is at most the average, over the signing coins, of the
distinguisher against the real challenger of the compiled prover at the program's statements, plus
`Q · εc`**, at each auxiliary value and each oracle, for an oracle-free base signer (`hB`) with
correctness error `εc` (`hcorr`), under the hypotheses `hz` on the program's statements and inputs:
the game's replies are replaced by the checked ones (`game_le_checked`), and the checked game
relays the real challenger (`relays_realK`, `AdaptiveIAlg.outLaw_absorb`). -/
theorem game_le_sum_realK [NeZero n] (hB : B.OracleFree)
    (hz : ZKRingHypsAt B adm stmt input fw enc relH) {εc : ℝ≥0∞} (hcorr : B.CorrectWithin εc)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    ((((A.at keys).alg a).toKindAlg.composeBothOut
        (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisherK A enc keys Q a ds).alg ()).compose
          (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _)
            Q)).outLaw H (some true) + Q * εc := by
  rw [toOuterMeasure_outLaw_unforge_eq_split (ofBase B 𝒫 adm) n (SideOracle.none _)
    ((A.at keys).alg a).toKindAlg keys Q H fun adv lg =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ H)]
  refine (game_le_checked hcorr ((A.at keys).alg a).toKindAlg keys Q H fun adv lg =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ H)).trans (add_le_add (le_of_eq ?_) le_rfl)
  have h := ((A.at keys).alg a).outLaw_absorb (σ := PMF.uniformOfFintype (Fin Q → B.Coins))
    (F' := fun ds => zkRelayK B enc keys ds) (C := (checkedSplit 𝒫 adm keys Q).toChallenger)
    (C' := realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)
    (e := coinSplit Q B.Coins (𝒫).Coins)
    (fun s c' => coins_checkedSplit (PS := 𝒫) (adm := adm) keys Q s c')
    (fun H s c' => (relays_realK (PS := 𝒫) (adm := adm) hB stmt fw enc hz.mem_relH
      hz.not_mem_relH_nil (𝒫z) (fun x w c h => prove_eq_of_hyps hz x w c h) keys s
        c').relays H _)
    (fun s c => zkRelayK_route_injective B enc keys s c) H
    (fun adv lg _ _ _ =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ H))
  refine h.trans (Finset.sum_congr rfl fun ds _ => ?_)
  congr 1
  change _ = (((zkAbsorbedK A enc keys Q a ds).thenProg (zkTestK A enc keys Q a ds)
    (M.qVerifier Qs b b).kq fun _ => forgeryTest_queriesLE keys Q _ _).compose _).outLaw H
      (some true)
  rw [AdaptiveIAlg.outLaw_thenProg]
  have hnil := KindAlg.postAss_eq_nil (zkAbsorbedK A enc keys Q a ds).toKindAlg
    (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)
    (QROM.outWith_realChallenger_assignments _ _ _ Q)
  congr 2
  ext o
  simp only [hnil, run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

open Classical in
omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **Zero knowledge at one key, one auxiliary value and one draw of signing coins**: the
distinguisher accepts against the real challenger with probability at most its acceptance against
the simulated challenger of the spBCS joint simulator plus `zkError δ t Q`
(`SPBCS.everlastingZeroKnowledge_qrom`), for a composite that is honest-verifier zero knowledge for
`relH` (`hvzk`). -/
theorem acceptProb_real_leK [NeZero n] (VE : M.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (a : (A.at keys).Aux) (ds : Fin Q → B.Coins) :
    (distinguisherK A enc keys Q a ds).acceptProb
        (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q) ≤
      (distinguisherK A enc keys Q a ds).acceptProb
          (simChallenger (relZ B 𝒫 adm stmt fw relH)
            ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap (stmt ∘ Prod.fst)) Q) +
        ENNReal.ofReal (M.zkError δ t Q) := by
  have hzk := M.everlastingZeroKnowledge_qrom Λ honest E VE hb T
    (stmt ∘ Prod.fst : RelayStmt B 𝒫 adm n → X₀) fw hvzk
  unfold NARG.QROM.EverlastingZeroKnowledge at hzk
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    M.encode_niSimulator Λ E VE hb] at hzk
  have hD : (distinguisherK A enc keys Q a ds).QueriesBeforeLastProofQuery t := fun _ =>
    ⟨((A.at keys).alg a).budget,
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans ((A.at keys).queries_le a),
      AdaptiveIAlg.requestsAfterAtMost_thenProg (zkAbsorbedK A enc keys Q a ds)
        (zkTestK A enc keys Q a ds) _ fun _ => forgeryTest_queriesLE keys Q _ _⟩
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
  have h := hzk t Q _ (distinguisherK A enc keys Q a ds) hD
  convert key _ _ (acceptProb_distinguisherK_le_one A keys Q a ds _)
    (acceptProb_distinguisherK_le_one A keys Q a ds _) h using 3
  · exact funext fun _ => funext fun _ => propext Iff.rfl
  · exact QROM.simChallenger_congr _ _ _ _ _ _ _ _ (fun _ _ => Iff.rfl) _ Q

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] in
open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] [Nonempty TB.KeyCoins] in
/-- **The side-coin average of the distinguisher against the simulated challenger is the checked
simulated game** (`simSplitK` with the test `drawOk`) at each key, auxiliary value and oracle, the
forgery read under the final oracle, for an oracle-free base signer (`hB`). -/
theorem sum_sim_eq_checkedK [NeZero n] (hB : B.OracleFree)
    (hz : ZKRingHypsAt B adm stmt input fw enc relH) {SC : Type} [Fintype SC] [DecidableEq SC]
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisherK A enc keys Q a ds).alg ()).compose
          (simChallenger (relZ B 𝒫 adm stmt fw relH) (Sim.comap (stmt ∘ Prod.fst)) Q)).outLaw H
          (some true) =
      ((((A.at keys).alg a).toKindAlg.composeBothOut
          (simSplitK 𝒫 adm keys (Sim.comap stmt) Q (drawOk B keys)).toChallenger
            id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H.reprogram
            (((A.at keys).alg a).toKindAlg.postAss
              (simSplitK 𝒫 adm keys (Sim.comap stmt) Q (drawOk B keys)).toChallenger
                v.chal))} := by
  have h := ((A.at keys).alg a).outLaw_absorb (σ := PMF.uniformOfFintype (Fin Q → B.Coins))
    (F' := fun ds => zkRelayK B enc keys ds)
    (C := (simSplitK 𝒫 adm keys (Sim.comap stmt) Q (drawOk B keys)).toChallenger)
    (C' := simChallenger (relZ B 𝒫 adm stmt fw relH) (Sim.comap (stmt ∘ Prod.fst)) Q)
    (e := coinSplit Q B.Coins SC) (fun s c' => coins_simSplitK keys (Sim.comap stmt) Q _ s c')
    (fun H s c' => (relays_sim_zkK (PS := 𝒫) (adm := adm) hB stmt fw enc hz.mem_relH
      hz.not_mem_relH_nil keys Sim s c').relays H _)
    (fun s c => zkRelayK_route_injective B enc keys s c) H
    (fun adv lg _ _ G =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ G))
  refine (Eq.trans (Finset.sum_congr rfl fun ds _ => ?_) h.symm)
  congr 1
  change ((((zkAbsorbedK A enc keys Q a ds).thenProg (zkTestK A enc keys Q a ds)
    (M.qVerifier Qs b b).kq fun _ => forgeryTest_queriesLE keys Q _ _).compose _).outLaw H
      (some true)) = _
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2
  ext o
  simp only [run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

/-! ### The chain -/

open Classical in
omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Nonempty TB.KeyCoins] in
/-- **The chain at one key and one auxiliary value**: the insider game with a nonempty ring,
averaged over the oracle, is at most the simulated game read from the keys (`simSplitK` with the
spBCS joint simulator read at `stmt`, without the test), averaged over the oracle and with the
forgery read under the final oracle, plus `zkError δ t Q` and `2 Q εc`, for an oracle-free base
signer (`hB`) with correctness error `εc` (`hcorr`), under the hypotheses `hz` with a total
encoding and the honest-verifier zero knowledge `hvzk` of the composite. -/
theorem game_le_simK_at [NeZero n] (hB : B.OracleFree) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (enc : RingStmt B → RelayWit B → W')
    (hz : ZKRingHypsAt B adm stmt input fw enc relH)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) (a : (A.at keys).Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (simSplitK 𝒫 adm keys ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap
            stmt) Q fun _ _ => True).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H.reprogram
            (((A.at keys).alg a).toKindAlg.postAss
              (simSplitK 𝒫 adm keys ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap
                stmt) Q fun _ _ => True).toChallenger v.chal))} +
        ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc := by
  set Simj := M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T
  have hσ : ∑ ds : Fin Q → B.Coins, PMF.uniformOfFintype (Fin Q → B.Coins) ds = 1 := by
    have h1 := (PMF.uniformOfFintype (Fin Q → B.Coins)).tsum_coe
    rwa [tsum_fintype] at h1
  have hreal := Ring.BKMAdversary.tsum_pmf_mul_le_add
    (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)) _ _ _ fun H =>
    game_le_sum_realK A hB hz hcorr keys Q a H
  have hzk : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisherK A enc keys Q a ds).alg ()).compose
          (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _)
            Q)).outLaw H (some true) ≤
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          (((distinguisherK A enc keys Q a ds).alg ()).compose
            (simChallenger (relZ B 𝒫 adm stmt fw relH) (Simj.comap (stmt ∘ Prod.fst))
              Q)).outLaw H (some true) +
        ENNReal.ofReal (M.zkError δ t Q) := by
    rw [Ring.tsum_mul_sum_comm, Ring.tsum_mul_sum_comm]
    simp_rw [← acceptProb_distinguisherK]
    calc _ ≤ ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          ((distinguisherK A enc keys Q a ds).acceptProb
            (simChallenger (relZ B 𝒫 adm stmt fw relH) (Simj.comap (stmt ∘ Prod.fst)) Q) +
            ENNReal.ofReal (M.zkError δ t Q)) :=
          Finset.sum_le_sum fun ds _ => mul_le_mul_of_nonneg_left
            (acceptProb_real_leK A VE pub Sim T hvzk keys Q a ds) zero_le
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ, one_mul]
  have hsim := Ring.BKMAdversary.tsum_pmf_mul_le_add
    (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)) _ _ _ fun H =>
    (le_of_eq (sum_sim_eq_checkedK A hB hz Simj keys Q a H)).trans
      (simChecked_leK hcorr ((A.at keys).alg a).toKindAlg keys (Simj.comap stmt) Q H
        fun adv lg G => Wins keys Q (((A.at keys).alg a).out adv.workspace.1)
          (Quantum.requests lg) (outEquiv k e ∘ G))
  calc _ ≤ _ := hreal
    _ ≤ _ := add_le_add (hzk.trans (add_le_add hsim le_rfl)) le_rfl
    _ = _ := by ring

end SPBCS

end RingSignature.Insider

end GordieHowe
