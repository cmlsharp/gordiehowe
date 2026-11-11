-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.InsiderRelays
public import GordieHowe.Applications.Ring.RelayForger
public import GordieHowe.SPBCS.KnowledgeTheorems

@[expose] public section

/-!
# Unforgeability with respect to insider corruption at every base-message map

BKM06 Definition 7 (Bender, Katz, Morselli, TCC 2006, LNCS p. 67; ePrint 2005/304, p. 7) for the
ring signature compiled by spBCS, at every base-message map `bind`, including converted
signatures (`bind R m = m`), from zero knowledge, simulation-sound extractability and knowledge
soundness of spBCS and the multi-user unforgeability of the base scheme.

The side requests of BKM06 (public keys and corruptions) are answered from values independent of
the random oracle: the users' key-generation coins, and for ring signatures a public value and
signing coins drawn per request. At fixed side coins, an adversary of BKM06 composed with the
challenger of BKM06 is an adversary of the zero-knowledge game composed with a main challenger
(`AdaptiveIAlg.absorb`, `AdaptiveIAlg.outLaw_absorb`): the side requests and their answers move
into its workspace, and each ring-signing request becomes a proof query on its statement with the
signer's witness. The reduction:

1. The forgery's ring is empty, or not. On the empty ring the ring relation has no witness, so the
   knowledge bound of spBCS (`ExtractionForger.winProb_le_of_knowledgeBound`) bounds acceptance
   by `knowledgeError`.
2. Real to simulated ring signatures, at each value of the auxiliary input and of the side coins:
   the absorbed adversary followed by the verifier and the freshness test (`thenProg`) is a
   distinguisher of everlasting zero knowledge (`SPBCS.everlastingZeroKnowledge_qrom`), with
   error `zkError δ t Q`.
3. The simulated ring signatures are the simulation-extraction game's: absorbed again, the
   adversary is an adversary of the simulation-extraction game whose proof queries are the
   statements of its ring-signing requests (`seRelay`). A fresh forgery of BKM06 on a nonempty
   ring is a fresh statement, and weak simulation-sound extractability
   (`SPBCS.weak_online_simulation_extractability_qrom`,
   `WeakOnlineSimulationExtractable.unruhSimExtraction_of_queryFreeTest`) bounds its acceptance by
   the extraction probability plus `simExtractionError`.
4. An extracted witness decodes to a forgery of the multi-user game at the users' keys
   (`BKMAdversary.simForgerSuccess`): the forger runs the adversary with public keys and
   corruptions answered by the base oracles, ring signatures simulated, no signing request.

- `InsiderFreshAt`: the freshness of BKM06 at given keys and requests.
- `BKMAdversary.distinguisher`, `BKMAdversary.seAdversary`: the absorbed adversaries.
- `BKMAdversary.simForgerSuccess`: the success of the forger in the multi-user game.
- `BKMAdversary.insiderWinProb_le_of_zeroKnowledge`: the headline.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm
open scoped ENNReal NNReal

/-- **An average of finite averages is a finite average of averages** (exchange of a sum over a
countable type with a finite sum in `ℝ≥0∞`). -/
theorem tsum_mul_sum_comm {α β : Type*} [Fintype β] (u : α → ℝ≥0∞) (σ : β → ℝ≥0∞)
    (f : β → α → ℝ≥0∞) : ∑' x, u x * ∑ s, σ s * f s x = ∑ s, σ s * ∑' x, u x * f s x := by
  have h : ∀ x, u x * ∑ s, σ s * f s x = ∑ s, σ s * (u x * f s x) := fun x => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [h]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  simp_rw [ENNReal.tsum_mul_left]

/-! ### Freshness at given keys and requests -/

section Fresh

variable {Sch : SigScheme} [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg]
  [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [Nonempty Sch.Pub] [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins]
  [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins]
  [Nonempty Sch.SignCoins] {n N : ℕ} {RMsg : Type}

/-- **The freshness of BKM06 Definition 7 at the users' coins `keys` and the answered requests
`reqs`**: every key of the ring is the key of a user without a corruption request, and no
ring-signing request was for the statement's ring and message. -/
structure InsiderFreshAt (keys : Fin n → Sch.KeyCoins) (x : RingStmt Sch RMsg N)
    (reqs : List (BKMRequest Sch n N RMsg)) : Prop where
  /-- Every key of the ring is the key of an uncorrupted user. -/
  honest_ring : ∀ pk ∈ x.ring.1, ∃ i, Sch.pk (keys i) = pk ∧ BKMRequest.corrupt i ∉ reqs
  /-- No ring signature on the ring and message was requested. -/
  no_ringSign : ∀ s (R : RingOf Sch.PK N) m, BKMRequest.ringSign s R m ∈ reqs →
    ¬ (R.1 = x.ring.1 ∧ m = x.msg)

end Fresh

section Game

variable {Sch : SigScheme} [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Sig]
  [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Fintype Sch.KeyCoins]
  [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] {n : ℕ} {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {N : ℕ}
  {m k e : ℕ} {Pf Resp Coins : Type} [Fintype Resp] [DecidableEq Resp] [Fintype Coins]
  [DecidableEq Coins]
  {V : NARG.QROM.Verifier m k e (Claim (RingStmt Sch RMsg N) Pf) (RingStmt Sch RMsg N)}
  (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
    (μ : PMF Coins)
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)
  {t Q : ℕ} (A : BKMAdversary V Resp n t Q)

namespace BKMAdversary

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Resp] [DecidableEq Resp] [Fintype Sch.PK]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] [DecidableEq Coins] in
/-- **A request of BKM06 calls the base corruption of user `i` exactly when it is the corruption
request of `i`**: public keys and ring signatures make no corruption call. -/
theorem bk_corrupt_mem_trace_bkmLayer {r : BKMRequest Sch n N RMsg} {c : Coins}
    {O : BaseRequest Sch n → BaseResponse Sch} {i : Fin n} :
    BaseRequest.corrupt i ∈ ((bkmLayer Pv μ bind adm).prog r c).trace O ↔ r = .corrupt i := by
  simp only [bkmLayer]
  rcases r with i' | i' | ⟨s, ring, mg⟩
  · simp [BKMRequest.Admissible, BKMRequest.toRingRequest, ringLayer, OracleProg.trace_query]
  · simp [BKMRequest.Admissible, BKMRequest.toRingRequest, ringLayer, OracleProg.trace_query,
      eq_comm]
  · simp only [reduceCtorEq, iff_false]
    split_ifs
    · simp only [BKMRequest.toRingRequest, ringLayer, OracleProg.trace_query, List.mem_cons,
        reduceCtorEq, false_or]
      rcases hO : O (.publicKey s) with pk | σ | kc
      · simp only [ringSignAfterKey]
        split_ifs
        · simp only [OracleProg.trace_query, List.mem_cons, reduceCtorEq, false_or]
          rcases hO2 : O (.sign s (bind ring.1 mg)) with _ | _ | _ <;> simp
        · simp
      · simp
      · simp
    · simp

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Resp] [DecidableEq Resp] [Fintype Sch.PK]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
/-- **The base calls of at most `Q` requests of BKM06 corrupt user `i` exactly when one of the
requests is the corruption of `i`.** -/
theorem bk_corrupted_iff {ω : (bkmLayer Pv μ bind adm).Draw Q}
    {reqs : List (BKMRequest Sch n N RMsg)} (hl : reqs.length ≤ Q) {i : Fin n} :
    (bkmLayer Pv μ bind adm).Corrupted Q ω reqs i ↔ BKMRequest.corrupt i ∈ reqs := by
  simp only [OracleLayer.Corrupted, OracleLayer.calls, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hc⟩
    by_cases hQ : p.2 < Q
    · simp only [OracleLayer.callsAt, hQ, ↓reduceDIte] at hc
      rw [← (bk_corrupt_mem_trace_bkmLayer Pv μ bind adm).1 hc]
      exact List.fst_mem_of_mem_zipIdx hp
    · simp [OracleLayer.callsAt, hQ] at hc
  · intro h
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem h
    refine ⟨(reqs[j], j), List.mem_zipIdx_iff_getElem?.2 (by simp), ?_⟩
    simp only [OracleLayer.callsAt, show j < Q by omega, ↓reduceDIte]
    exact (bk_corrupt_mem_trace_bkmLayer Pv μ bind adm).2 hji

/-- **The freshness of BKM06 on the composed registers is freshness at the users' coins and the
first `Q` logged requests.** -/
theorem insiderFresh_iff (a : A.Aux) (v : A.Register Pv μ bind adm a) :
    A.InsiderFresh Pv μ bind adm a v ↔
      InsiderFreshAt v.chal.coins.1 (A.claim Pv μ bind adm a v).stmt
        ((requests v.chal.logs).take Q) := by
  have hans : A.answered Pv μ bind adm a v = (requests v.chal.logs).take Q :=
    KindAlg.map_request_history_stateAt _ _ _ _
  have hc : ∀ i, (bkmLayer Pv μ bind adm).Corrupted Q v.chal.coins
      (A.answered Pv μ bind adm a v) i ↔
      BKMRequest.corrupt i ∈ (requests v.chal.logs).take Q := fun i => by
    rw [hans]
    exact bk_corrupted_iff Pv μ bind adm (List.length_take_le _ _)
  constructor
  · intro h
    refine ⟨fun pk hpk => ?_, fun s R mg hr => ?_⟩
    · obtain ⟨i, hi, hni⟩ := h.honest_ring pk hpk
      exact ⟨i, hi, fun hm => hni ((hc i).2 hm)⟩
    · exact h.no_ringSign s R mg (hans ▸ hr)
  · intro h
    refine ⟨fun pk hpk => ?_, fun s R mg hr => ?_⟩
    · obtain ⟨i, hi, hni⟩ := h.honest_ring pk hpk
      exact ⟨i, hi, fun hm => hni ((hc i).1 hm)⟩
    · exact h.no_ringSign s R mg (hans ▸ hr)

/-- **The adversary wins with a nonempty ring** at the auxiliary input `a`, the users' coins `keys`,
the workspace `w`, the logs `lg` and the final oracle `G`: the verifier accepts the claim of `w`
under `G` (read through `outEquiv`), the claim is fresh at `keys` and the first `Q` logged requests
(`InsiderFreshAt`), and its ring is nonempty. -/
def WinAt (a : A.Aux) (keys : Fin n → Sch.KeyCoins) (w : (A.alg a).W)
    (lg : LogReg (BKMRequest Sch n N RMsg) (A.alg a).slots) (G : Bits m → XOut k e) : Prop :=
  V.Accepted (outEquiv k e ∘ G) ((A.alg a).out w) ∧
    InsiderFreshAt keys ((A.alg a).out w).stmt ((requests lg).take Q) ∧
    ((A.alg a).out w).stmt.ring.1 ≠ []

/-- **The win probability of BKM06 splits by the ring of the forgery**: at most the oracle average
of the output law on `WinAt` (a nonempty ring) plus the probability of an accepted claim with the
empty ring. -/
theorem insiderWinProb_le_add :
    A.insiderWinProb Pv μ bind adm ≤
      ∑' a, A.aux a * ∑' H, PMF.uniformOfFintype (Bits m → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut (challenger Pv μ bind adm (Q := Q)) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} +
      ∑' a, A.aux a * (((A.alg a).toKindAlg.composeBothOut (challenger Pv μ bind adm (Q := Q))
        id).realLaw (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out,
          V.Accepted p.oracle (A.claim Pv μ bind adm a v) ∧
            (A.claim Pv μ bind adm a v).stmt.ring.1 = []} := by
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  set C := (A.alg a).toKindAlg.composeBothOut (challenger Pv μ bind adm (Q := Q)) id
  have hsplit : (C.realLaw (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out,
      V.Accepted p.oracle (A.claim Pv μ bind adm a v) ∧ A.InsiderFresh Pv μ bind adm a v} ≤
      (C.realLaw (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out,
        V.Accepted p.oracle (A.claim Pv μ bind adm a v) ∧ A.InsiderFresh Pv μ bind adm a v ∧
          (A.claim Pv μ bind adm a v).stmt.ring.1 ≠ []} +
      (C.realLaw (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out,
        V.Accepted p.oracle (A.claim Pv μ bind adm a v) ∧
          (A.claim Pv μ bind adm a v).stmt.ring.1 = []} := by
    refine le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_union_le _ _)
    rintro p ⟨v, hv, hacc, hf⟩
    by_cases hr : (A.claim Pv μ bind adm a v).stmt.ring.1 = []
    · exact Or.inr ⟨v, hv, hacc, hr⟩
    · exact Or.inl ⟨v, hv, hacc, hf, hr⟩
  refine hsplit.trans (add_le_add (le_of_eq ?_) le_rfl)
  rw [Alg.toOuterMeasure_realLaw_eq_tsum C (outEquiv k e) (fun v G =>
    V.Accepted G (A.claim Pv μ bind adm a v) ∧ A.InsiderFresh Pv μ bind adm a v ∧
      (A.claim Pv μ bind adm a v).stmt.ring.1 ≠ [])]
  refine tsum_congr fun H => ?_
  congr 2
  ext o
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [insiderFresh_iff]
  rfl

/-- **An accepted claim with the empty ring has at most the knowledge error**: the ring relation has
no witness for the empty ring, so the knowledge bound (`ExtractionForger.winProb_le_of_knowledgeBound`
at a forger that decodes nothing) bounds its probability by the knowledge error at
`t + Q · q + kq` queries. -/
theorem emptyRing_le_knowledgeError (hV : ∀ c, V.stmt c = c.stmt)
    {ext : RingStmt Sch RMsg N → DB (Bits m) (Out k e) → Multiset (RingWit Sch)} {β : ℕ → ℝ≥0∞}
    (K : V.KnowledgeBound (ringRel adm bind) ext β) :
    ∑' a, A.aux a * (((A.alg a).toKindAlg.composeBothOut (challenger Pv μ bind adm (Q := Q))
        id).realLaw (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out,
          V.Accepted p.oracle (A.claim Pv μ bind adm a v) ∧
            (A.claim Pv μ bind adm a v).stmt.ring.1 = []} ≤
      V.knowledgeError β (t + Q * Pv.q + V.kq) := by
  let F : ExtractionForger V Sch n (RingWit Sch) (BKMRequest Sch n N RMsg) (RingResponse Sch Resp)
  :=
    { A.forger Pv μ bind adm ext with decode := fun _ _ => none }
  have h := F.winProb_le_of_knowledgeBound hV K A.queries_le
    (fun a v => (F.claim a v).stmt.ring.1 = [])
    fun a v w hf hw => absurd hw.2.idx_lt (by rw [hf]; exact Nat.not_lt_zero _)
  have hs : F.success = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun a => ?_
    rw [simProb_eq_zero _ _ fun _ _ ⟨_, _, f, hf, _⟩ => by simp [F] at hf, mul_zero]
  rw [hs, zero_add] at h
  exact h

end BKMAdversary

end Game

/-! ### The spBCS compilation -/

section SPBCS

variable {Sch : SigScheme} [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg]
  [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [Nonempty Sch.Pub] [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins]
  [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins]
  [Nonempty Sch.SignCoins] {n : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {N : ℕ}
  {k e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {kN kS L : ℕ}
  {M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e} (Λ : SiteLayout Mg) {B : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : RingStmt Sch RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs B B) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
  (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : RingStmt Sch RMsg N → Pub)
  (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)
  (pubOf : Sch.SignCoins → Sch.Pub)
  {t Q : ℕ} (A : BKMAdversary (M.qVerifier Qs B B) (M.Response B) n t Q)

namespace BKMAdversary

variable [Nonempty RMsg] [NeZero n]

variable [Nonempty Sch.Sig]

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg]
  [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins]
  [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
variable (Sch n N RMsg) in
/-- A relayed proof query, the blank main request of the absorbed adversaries. -/
noncomputable instance instInhabitedRelayQuery :
    Inhabited (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) :=
  ⟨⟨default, (0, Classical.arbitrary _)⟩⟩

/-- **The test of a forgery on an absorbed workspace** at the side coins `s`: the verifier's
program on the adversary's claim (its `kq` queries, answers read through `outEquiv`), then
whether the claim is fresh at the users' coins and the first `Q` logged requests, with a nonempty
ring.

Running time: the verifier's `kq` queries and decision (`NARG.Verifier.prog`), and a scan of the
ring and of the logged requests. This running time is argued here, not proved in Lean. -/
noncomputable def forgeryTest (a : A.Aux) (s : SideCoins Sch n Q)
    (w : (A.alg a).AbsW (Resp' := M.Response B)) :
    OracleProg (Bits (queryBits k kN kS L)) (XOut k e) Bool :=
  open Classical in
  (((M.qVerifier Qs B B).prog ((A.alg a).out w.work)).mapQuery id (outEquiv k e)).bind fun b =>
    .pure (b && decide (InsiderFreshAt s.1 ((A.alg a).out w.work).stmt
      ((requests w.logs).take Q) ∧ ((A.alg a).out w.work).stmt.ring.1 ≠ []))

omit [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Nonempty Sch.Pub] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins]
  [Nonempty Sch.SignCoins] in
/-- The test makes the verifier's `kq` queries. -/
theorem forgeryTest_queriesLE (a : A.Aux) (s : SideCoins Sch n Q)
    (w : (A.alg a).AbsW (Resp' := M.Response B)) :
    (A.forgeryTest a s w).QueriesLE (M.qVerifier Qs B B).kq := by
  intro G
  simp only [forgeryTest, OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil,
    OracleProg.length_trace_mapQuery]
  exact NARG.Verifier.prog_queriesLE _ _ _

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins] in
/-- **The distinguisher of zero knowledge** at the auxiliary input `a` and the side coins `s`:
the adversary with its side requests absorbed (`zkRelay`, proof queries with the signers'
witnesses), followed by `forgeryTest`.

Running time: that of the adversary, plus the relay of each request (`zkRelay`, at most one base
signature) and `forgeryTest`. This running time is argued here, not proved in Lean. -/
noncomputable def distinguisher (a : A.Aux) (s : SideCoins Sch n Q) :
    QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) (M.Response B) Bool
      ((A.alg a).width * ((A.alg a).budget + (A.alg a).post) +
        (A.alg a).width * (M.qVerifier Qs B B).kq) where
  Aux := Unit
  aux := PMF.pure ()
  sh _ := (A.sh a).absorbS.thenProgS (M.qVerifier Qs B B).kq
  alg _ := ((A.alg a).absorb (zkRelay (N := N) (Resp := M.Response B) adm bind pubOf s)).thenProg
    (A.forgeryTest a s) (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)
  tracePreserving _ := AdaptiveIAlg.thenProg_tracePreserving
    ((A.alg a).absorb (zkRelay (N := N) (Resp := M.Response B) adm bind pubOf s)) (A.forgeryTest a s)
    (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)
    (AdaptiveIAlg.absorb_tracePreserving (A.alg a) (zkRelay adm bind pubOf s) (A.tracePreserving a))
  withinBudget _ := AdaptiveIAlg.withinBudget_thenProg
    ((A.alg a).absorb (zkRelay (N := N) (Resp := M.Response B) adm bind pubOf s)) (A.forgeryTest a s)
    (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)
    (AdaptiveIAlg.absorb_withinBudget (A.alg a) (zkRelay adm bind pubOf s)
      (zkRelay_route_injective adm bind pubOf s) (A.withinBudget a))
  queries_le _ := (AdaptiveIAlg.thenProg_queries
    ((A.alg a).absorb (zkRelay (N := N) (Resp := M.Response B) adm bind pubOf s)) (A.forgeryTest a s)
    (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)).le

omit [Nonempty Sch.Sig] [NeZero n] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] in
/-- The relay of BKM06's requests through the base oracles routes each request number
injectively. -/
theorem atKeys_bkmBaseRelay_route_injective (s : SideCoins Sch n Q) (c : ℕ) :
    Function.Injective (((bkmBaseRelay Sch n N RMsg (M.Response B) adm pubOf Q).atKeys s.1 s.2).route c) := by
  rw [atKeys_bkmBaseRelay]
  exact seRelay_route_injective _ _ _ _ c

/-- **The adversary of the simulation-extraction game** at the side coins `s`: the adversary with
its side requests absorbed through the base oracles at the users' coins `s.1`
(`bkmBaseRelay`, which is `seRelay`, `atKeys_bkmBaseRelay`), its proof queries the statements of
its ring-signing requests (with the request), public keys and corruptions answered by the base
oracles, the public values `pubOf` of the signing coins `s.2`.

Running time: that of the adversary, plus the relay of each request (`bkmBaseRelay`, one base call
and a lookup of the signer's key in the ring). This running time is argued here, not proved in
Lean. -/
noncomputable def seAdversary (s : SideCoins Sch n Q) :
    M.QBSimExtractionAdversary B (RelayStmt Sch n N RMsg) t where
  Aux := A.Aux
  aux := A.aux
  sh a := (A.sh a).absorbS
  alg a := (A.alg a).absorb ((bkmBaseRelay Sch n N RMsg (M.Response B) adm pubOf Q).atKeys s.1 s.2)
  tracePreserving a := AdaptiveIAlg.absorb_tracePreserving _ _ (A.tracePreserving a)
  withinBudget a := AdaptiveIAlg.absorb_withinBudget _ _
    (atKeys_bkmBaseRelay_route_injective adm pubOf s) (A.withinBudget a)
  queries_le a := A.queries_le a

omit [Nonempty Sch.Sig] in
/-- The shape of `seAdversary` at `a` is `A`'s shape absorbed (`AlgShape.absorbS`). -/
@[simp] theorem seAdversary_sh (s : SideCoins Sch n Q) (a : A.Aux) :
    (A.seAdversary adm pubOf s).sh a = (A.sh a).absorbS :=
  rfl

/-- **The simulator of the simulation-extraction game**: the spBCS simulator
(`niJointSimulatorProg`), inert on the empty ring (`inertOnEmpty`), where it answers `none`.

Running time: that of `niJointSimulatorProg`, plus a test of the ring. This running time is
argued here, not proved in Lean. -/
abbrev seSimulator :
    NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt Sch RMsg N) (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T)) :=
  inertOnEmpty (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) none

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] [DecidableEq Sch.SignCoins] in
/-- **The forger of the multi-user game built from the adversary of BKM06** (`RelayForger`): the
adversary's requests relayed through the base oracles (`bkmBaseRelay`: public keys and corruptions
forwarded, the signer's public key asked for a ring-signing request, no signing request, the
public values of the ring signatures `pubOf` of the forger's own signing coins), the ring
signatures simulated by `seSimulator` (which programs the oracle), the database extractor
`dbExtractBits Ext` and the decoding `decodeRing`. Reducible, so instance search reaches the coins
of its relay.

Running time: that of the extraction run of the absorbed adversary (`extAdv`: the adversary, one
simulator run per ring-signing request, the verifier's queries on its claim, the oracle simulated
by a compressed oracle), plus one base call per request and the extractor's and the decoding's
running times (their docstrings). This running time is argued here, not proved in Lean. -/
@[reducible] noncomputable def relayForger
    (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)) :
    RelayForger Sch n M B (BKMRequest Sch n N RMsg) (RingResponse Sch (M.Response B))
      (RelayStmt Sch n N RMsg) (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T)) where
  Aux := A.Aux
  aux := A.aux
  sh := A.sh
  alg := A.alg
  relay := bkmBaseRelay Sch n N RMsg (M.Response B) adm pubOf Q
  sim := (seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst
  extractor := M.dbExtractBits Ext
  decode := decodeRing bind

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] [DecidableEq Sch.SignCoins] in
/-- **The success probability of the forger of the multi-user game** built from the adversary of
BKM06 (`relayForger`; the multi-user game with adaptive corruption, Bader, Hofheinz, Jager, Kiltz,
Li, TCC 2015, ePrint 2014/797, Definition 2, p. 6, `RelayForger.success`): the forger reads the
keys only through the base oracles (public keys, and the key-generation coins of the users the
adversary corrupts); it makes no signing request. -/
noncomputable def simForgerSuccess (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)) :
    ℝ≥0∞ :=
  (A.relayForger Λ VE pub Sim T bind adm pubOf Ext).success Qs Q (kqOf Mg nr B B)

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] [DecidableEq Sch.SignCoins] in
/-- **The forger's success as an average of extraction runs** of the simulation-extraction
adversary `seAdversary s` over the auxiliary input and the side coins `s = (keys, draws)`: some
witness the database extractor returns for the forgery's statement decodes to a forgery of the
multi-user game at `keys`, the corrupted users read from the logged requests. -/
noncomputable def simExtractForgery {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)} :
    ℝ≥0∞ :=
  ∑' a, A.aux a * ∑ s : SideCoins Sch n Q, PMF.uniformOfFintype (SideCoins Sch n Q) s *
    simProb (outEquiv k e)
      (extAdv Qs ((A.seAdversary adm pubOf s).alg a) ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q
        (kqOf Mg nr B B))
      fun c D => ∃ w ∈ M.dbExtractBits Ext
          (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt D,
        ∃ f ∈ decodeRing bind (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt w,
          BaseForgery s.1 (fun i => BKMRequest.corrupt i ∈
              (requests (advWorkspace ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).1.logs).take Q)
            (fun _ _ => False) f

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig] in
/-- The uniform law on a product is the product of the uniform laws. -/
theorem uniformOfFintype_prod_apply {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (a : α) (b : β) :
    PMF.uniformOfFintype (α × β) (a, b) = PMF.uniformOfFintype α a * PMF.uniformOfFintype β b := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig]
  [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Fintype Sch.Sig]
  [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
/-- Forgeries for equivalent records of corruption and signing. -/
theorem baseForgery_congr {keys : Fin n → Sch.KeyCoins} {c c' : Fin n → Prop}
    {g g' : Fin n → Sch.Msg → Prop} (hc : ∀ i, c i ↔ c' i) (hg : ∀ i m, g i m ↔ g' i m)
    {f : Sch.PK × Sch.Msg × Sch.Sig} : BaseForgery keys c g f ↔ BaseForgery keys c' g' f :=
  ⟨fun h => ⟨h.verify_eq, by
      obtain ⟨i, h1, h2, h3⟩ := h.exists_user
      exact ⟨i, h1, (hc i).not.1 h2, (hg i _).not.1 h3⟩⟩,
    fun h => ⟨h.verify_eq, by
      obtain ⟨i, h1, h2, h3⟩ := h.exists_user
      exact ⟨i, h1, (hc i).not.2 h2, (hg i _).not.2 h3⟩⟩⟩

omit [Nonempty Sch.Sig] in
/-- **The average of the extraction runs is the success of the forger of the multi-user game**
(`relayForger`): the runs are the same (`seAdversary` absorbs through `bkmBaseRelay`), and the
forger's single output wins exactly when some candidate does (`exists_mem_iff_pickForgery`), the
corruptions of the relay's base calls being the logged corruption requests
(`corrupt_mem_calls_bkmBaseRelay`), with no signing call. -/
theorem simExtractForgery_eq {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)} :
    A.simExtractForgery Λ VE pub Sim T bind adm pubOf (Ext := Ext) =
      A.simForgerSuccess Λ VE pub Sim T bind adm pubOf Ext := by
  classical
  rw [simExtractForgery, tsum_mul_sum_comm, simForgerSuccess, RelayForger.success,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun keys _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [uniformOfFintype_prod_apply, mul_assoc]
  refine congrArg (_ * ·) (congrArg (_ * ·) (tsum_congr fun a => congrArg (_ * ·) ?_))
  simp only [RelayForger.run, RelayForger.made, RelayForger.output, relayForger, seAdversary]
  congr 1
  funext c D
  apply propext
  rw [← exists_mem_iff_pickForgery]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, f, hf, h⟩
    refine ⟨f, ⟨w, hw, hf⟩, (baseForgery_congr (fun i => ?_) (fun i m => ?_)).1 h⟩
    · exact (corrupt_mem_calls_bkmBaseRelay adm pubOf keys ω _ i).symm
    · exact iff_of_false id
        ((bkmBaseRelay Sch n N RMsg (M.Response B) adm pubOf Q).not_sign_mem_calls keys ω _ i m)
  · rintro ⟨f, ⟨w, hw, hf⟩, h⟩
    refine ⟨w, hw, f, hf, (baseForgery_congr (fun i => ?_) (fun i m => ?_)).2 h⟩
    · exact (corrupt_mem_calls_bkmBaseRelay adm pubOf keys ω _ i).symm
    · exact iff_of_false id
        ((bkmBaseRelay Sch n N RMsg (M.Response B) adm pubOf Q).not_sign_mem_calls keys ω _ i m)

/-- The relation of the relayed proof queries: the ring relation on their statements and
witnesses. -/
abbrev relayRel : RelayStmt Sch n N RMsg → RelayWit Sch N → Prop :=
  fun x w => (x.1, w.toWit) ∈ ringRel adm bind

/-- **The freshness test of the simulation-extraction game** at the side coins `s`: every key of the
claim's ring is the key of a user without a corruption request among the first `Q` logged
requests. -/
def okAt (s : SideCoins Sch n Q) (a : A.Aux) (w : (A.alg a).AbsW (Resp' := M.Response B)) : Prop :=
  ∀ pk ∈ ((A.alg a).out w.work).stmt.ring.1, ∃ i, Sch.pk (s.1 i) = pk ∧
    BKMRequest.corrupt i ∉ (requests w.logs).take Q

/-- **Feeding answers to a program followed by a pure map** gives the mapped result. -/
theorem hopRS_result_bind_pure {X Y R R' : Type} (g : R → R') :
    ∀ (p : OracleProg X Y R) (ans : List Y),
      OracleProgAns.result (p.bind fun r => .pure (g r)) ans = (OracleProgAns.result p ans).map g
  | .pure _, _ => rfl
  | .query _ _, [] => rfl
  | .query _ k, b :: ans => hopRS_result_bind_pure g (k b) ans

omit [NeZero n] [Nonempty Sch.Sig] [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg]
  [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [Nonempty Sch.Pub] in
/-- **The challenger of a layer assigns nothing.** -/
theorem hopRS_outWith_challenger_assignments {X Y Req Resp : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] (L : OracleLayer Sch n X Y Req Resp) [Fintype L.Coins] [DecidableEq L.Coins] (Q : ℕ)
    (ω : L.Draw Q)
    (hist : List (HistoryEntry Req Resp)) (req : Req) (ans : List Y) :
    ((L.challenger Q).outWith ω hist req ans).assignments = [] := by
  unfold Challenger.outWith Challenger.outWithOf
  simp only [OracleLayer.challenger]
  split_ifs
  · rw [hopRS_result_bind_pure (fun r => (⟨r, []⟩ : Reply X Y Resp))]
    cases OracleProgAns.result _ ans <;> rfl
  · rfl

omit [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Nonempty Sch.Pub] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins]
  [Nonempty Sch.SignCoins] in
/-- **The forgery test accepts exactly on a win** at the side coins `s`. -/
theorem hopRS_run_forgeryTest (a : A.Aux) (s : SideCoins Sch n Q)
    (w : (A.alg a).AbsW (Resp' := M.Response B)) (G : Bits (queryBits k kN kS L) → XOut k e) :
    (A.forgeryTest a s w).run G = true ↔ A.WinAt a s.1 w.work w.logs G := by
  classical
  unfold forgeryTest WinAt
  rw [OracleProg.run_bind, OracleProg.run_mapQuery]
  simp only [OracleProg.run, Bool.and_eq_true, decide_eq_true_eq, NARG.Verifier.run_prog]
  rfl

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] in
open Classical in
/-- **The game of BKM06 with the checked signer is the side-coin average of the distinguisher
against the real challenger**, at each value of the auxiliary input and each oracle
(`AdaptiveIAlg.outLaw_absorb` with `relays_bkm_real`, then `AdaptiveIAlg.outLaw_thenProg`), when
the public value of an honest signature is `pubOf` of its coins (`hpub`). -/
theorem outLaw_bkm_eq_sum_real (hpub : Sch.PubOfCoins pubOf) (a : A.Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((A.alg a).toKindAlg.composeBothOut
        ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind
          adm).challenger Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} =
      ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        (((A.distinguisher bind adm pubOf a s).alg ()).compose
          (realChallenger (relayRel bind adm)
            ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).comap Prod.fst
              RelayWit.toWit) (PMF.uniformOfFintype _) Q)).outLaw H (some true) := by
  have hnil := KindAlg.postAss_eq_nil (A.alg a).toKindAlg
    ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind
      adm).challenger Q) (hopRS_outWith_challenger_assignments _ Q)
  have h := (A.alg a).outLaw_absorb (σ := PMF.uniformOfFintype (SideCoins Sch n Q))
    (F' := zkRelay (N := N) (Resp := M.Response B) adm bind pubOf)
    (C := (checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind
      adm).challenger Q)
    (e := drawEquiv (checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode
      queryEncoding) (PMF.uniformOfFintype _) bind adm) Q)
    (C' := realChallenger (relayRel bind adm)
      ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).comap Prod.fst
        RelayWit.toWit) (PMF.uniformOfFintype _) Q)
    (fun s c => drawLaw_drawEquiv_symm
      (checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm)
        Q s c)
    (fun H s c => (relays_bkm_real
      (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding)
        (PMF.uniformOfFintype _) bind adm hpub Q s c).relays
        H _)
    (zkRelay_route_injective adm bind pubOf) H
    (fun adv lg _ c G => A.WinAt a c.1 adv.workspace.1 lg G)
  have hr : ∀ G : Bits (queryBits k kN kS L) → XOut k e,
      G.reprogram ([] : List (Assignment (Bits (queryBits k kN kS L)) (XOut k e))) = G :=
    fun _ => rfl
  simp only [hnil, hr] at h
  refine h.trans (Finset.sum_congr rfl fun s _ => ?_)
  congr 1
  change _ = ((((A.alg a).absorb (zkRelay (N := N) (Resp := M.Response B) adm bind pubOf s)).thenProg
    (A.forgeryTest a s) (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)).compose _).outLaw H
      (some true)
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2
  ext o
  simp only [hopRS_run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] in
open Classical in
/-- **The side-coin average of the distinguisher against the simulated challenger is the game of
BKM06 with checked simulated ring signatures** (`simBKMCheckedChallenger`), at each value of the
auxiliary input and each oracle, when the public value of an honest signature is `pubOf` of its
coins (`hpub`). -/
theorem sum_sim_eq_outLaw_simBKM (hpub : Sch.PubOfCoins pubOf) (a : A.Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        (((A.distinguisher bind adm pubOf a s).alg ()).compose
          (simChallenger (relayRel bind adm)
            ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q)).outLaw H
          (some true) =
      (((A.alg a).toKindAlg.composeBothOut
          (simBKMCheckedChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
            pubOf Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} := by
  have h := (A.alg a).outLaw_absorb (σ := PMF.uniformOfFintype (SideCoins Sch n Q))
    (F' := zkRelay (N := N) (Resp := M.Response B) adm bind pubOf)
    (C := simBKMCheckedChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
      pubOf Q)
    (C' := simChallenger (relayRel bind adm)
      ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q)
    (e := splitEquiv Q _)
    (fun s c => simCoinsLaw_splitEquiv_symm Q _ s c)
    (fun H s c => (relays_sim_zk bind adm hpub
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) Q s c).relays H _)
    (zkRelay_route_injective adm bind pubOf) H
    (fun adv lg _ c G => A.WinAt a c.1 adv.workspace.1 lg G)
  refine (Eq.trans (Finset.sum_congr rfl fun s _ => ?_) h.symm)
  congr 1
  change ((((A.alg a).absorb (zkRelay (N := N) (Resp := M.Response B) adm bind pubOf s)).thenProg
    (A.forgeryTest a s) (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)).compose _).outLaw H
      (some true) = _
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2
  ext o
  simp only [hopRS_run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

omit [Fintype RMsg] [DecidableEq RMsg] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Nonempty RMsg]
  [Nonempty Sch.Sig] [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
include hb in
/-- **The spBCS verifier at its query budget accepts only claims that the spBCS verifier accepts**
under the oracle read through `outEquiv` and `Query.toBits` (`chainOracle`), for format bounds
`B`. -/
theorem hopSE_accepts {G : Bits (queryBits k kN kS L) → XOut k e}
    {c : Claim (RingStmt Sch RMsg N) M.NIProof}
    (h : (M.qVerifier Qs B B).Accepted (outEquiv k e ∘ G) c) :
    M.Accepts (chainOracle G) c.stmt c.proof (Qs c.stmt) := by
  refine (NARG.Verifier.ofOracle_accepted_iff (fun h₁ h₂ c hag hv => ?_)).1 h
  refine M.accepts_of_agree Qs (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
    (fun i => ?_) hv
  have := hag i
  rwa [QROM.Expansion.queries_map] at this

omit [NeZero n] [Nonempty Sch.Sig] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub]
  [Nonempty Sch.KeyCoins] [Nonempty Sch.SignCoins] in
/-- **The relayed statements of the first `Q` requests differ from a fresh statement with a
nonempty ring**: each is `dummyStmt`, with the empty ring, or the statement of a ring-signing
request among the first `Q`, which freshness separates from it. -/
theorem hopSE_fresh {Resp : Type} (pkOf : Fin n → Sch.PK) (kcOf : Fin n → Sch.KeyCoins)
    {Q' : ℕ} (pubs : Fin Q' → Sch.Pub) {keys : Fin n → Sch.KeyCoins} {x : RingStmt Sch RMsg N}
    {rs : List (BKMRequest Sch n N RMsg)} (hf : InsiderFreshAt keys x (rs.take Q'))
    (hx : x.ring.1 ≠ []) :
    ∀ x' ∈ ((seRelay (Resp := Resp) pkOf kcOf adm pubs).relayList rs).take Q', x'.1 ≠ x := by
  intro x' hx' heq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
  simp only [List.length_take, SideRelay.length_relayList] at hj
  have hjQ : j < Q' := by omega
  have hjl : j < rs.length := by omega
  simp only [List.getElem_take, SideRelay.relayList, List.getElem_mapIdx, seRelay] at heq
  have hmem : rs[j] ∈ rs.take Q' :=
    List.mem_iff_getElem.2 ⟨j, by simp only [List.length_take]; omega, by simp⟩
  by_cases hs : j < Q' ∧ signerIn pkOf adm rs[j]
  · generalize rs[j] = r at heq hmem hs
    cases r with
    | publicKey i => exact hs.2.elim
    | corrupt i => exact hs.2.elim
    | ringSign s R m =>
      rw [stmtAt, dite_eq_left_of_eq_true (eq_true hs)] at heq
      subst heq
      exact hf.no_ringSign s R m hmem ⟨rfl, rfl⟩
  · exact hx (heq ▸ (stmtAt_ring_eq_nil_iff pkOf adm pubs j rs[j]).2 hs)

omit [Nonempty Sch.Sig] in
include hb in
/-- **`simBKM_le_sum_winTestProb` under format bounds `B`**: the absorbed event, with the freshness
of the relayed statements added, is contained in the win-and-test event of each side coin. -/
theorem hopSE_simBKM_le (a : A.Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (simBKMChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q) id).outLaw
        H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
      ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) := by
  classical
  have hstep := fun H => AdaptiveIAlg.outLaw_absorb (A := A.alg a)
    (C := simBKMChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q)
    (C' := simExtChallenger ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q)
    (PMF.uniformOfFintype (SideCoins Sch n Q))
    (fun s => (bkmBaseRelay Sch n N RMsg (M.Response B) adm pubOf Q).atKeys s.1 s.2)
    (splitEquiv Q _) (fun s c' => simCoinsLaw_splitEquiv_symm Q _ s c')
    (fun H s c' => by
      rw [atKeys_bkmBaseRelay]
      exact (relays_sim_se adm _ pubOf none Q s c').relays H _)
    (fun s c => atKeys_bkmBaseRelay_route_injective adm pubOf s c) H
    (fun adv lg mlg c G => A.WinAt a c.1 adv.workspace.1 lg G ∧
      ∀ x' ∈ (requests mlg).take Q, x'.1 ≠ ((A.alg a).out adv.workspace.1).stmt)
  refine (tsum_congr fun H => congrArg (_ * ·) (Eq.trans ?_ (hstep H))).trans_le ?_
  · congr 1
    ext o
    refine exists_congr fun v => and_congr_right fun _ => ⟨fun h => ⟨h, ?_⟩, And.left⟩
    rw [SideRelay.requests_logs, atKeys_bkmBaseRelay]
    exact hopSE_fresh adm _ _ _ h.2.1 h.2.2
  rw [tsum_mul_sum_comm]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ zero_le
  unfold winTestProb
  refine le_of_le_of_eq ?_ (Alg.toOuterMeasure_realLaw_eq_tsum _ (outEquiv k e)
    fun v G => Wins ((A.seAdversary adm pubOf s).alg a).toTPKindAlg
      ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Qs Prod.fst
      ((outEquiv k e).symm ∘ G) v ∧
      A.okAt s a (advWorkspace ((A.seAdversary adm pubOf s).alg a).toTPKindAlg
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q v).1).symm
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (MeasureTheory.measure_mono ?_) zero_le
  rintro o ⟨v, hv, hw, hf⟩
  refine ⟨v, hv, ?_⟩
  have hH : (outEquiv k e).symm ∘ (outEquiv k e) ∘ H = H := by
    funext x
    simp
  rw [hH]
  refine ⟨⟨fun x' hx' => ?_, hopSE_accepts hb hw.1⟩, fun pk hpk => hw.2.1.honest_ring pk hpk⟩
  have hq := KindAlg.map_request_history_stateAt ((A.seAdversary adm pubOf s).alg a).toTPKindAlg
    (simExtChallenger ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q) v.chal
    ((A.seAdversary adm pubOf s).alg a).toTPKindAlg.slots
  unfold SPBCS.queried at hx'
  rw [hq] at hx'
  exact hf x' hx'

omit [Nonempty Sch.Sig] in
include hb in
/-- **The game of BKM06 with simulated ring signatures is at most the side-coin average of the
simulation-extraction game with the freshness test**: a fresh forgery on a nonempty ring is a
fresh statement of the simulation-extraction game, accepted under the final oracle. -/
theorem simBKM_le_sum_winTestProb (a : A.Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (simBKMChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q) id).outLaw
        H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
      ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) :=
  A.hopSE_simBKM_le Λ hb VE pub Sim T adm pubOf a

omit [Nonempty Sch.Sig] in
/-- **A fresh extracted witness that passes the test decodes to a forgery of the multi-user
game.** -/
theorem extractFreshTestProb_le {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)}
    (s : SideCoins Sch n Q) (a : A.Aux) :
    extractFreshTestProb Qs ((A.seAdversary adm pubOf s).alg a)
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B) Prod.fst
        (ringRel adm bind) Ext (A.okAt s a) ≤
      simProb (outEquiv k e)
        (extAdv Qs ((A.seAdversary adm pubOf s).alg a) ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q
          (kqOf Mg nr B B))
        fun c D => ∃ w ∈ M.dbExtractBits Ext
            (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt D,
          ∃ f ∈ decodeRing bind (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt w,
            BaseForgery s.1 (fun i => BKMRequest.corrupt i ∈
                (requests (advWorkspace ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).1.logs).take Q)
              (fun _ _ => False) f := by
  refine simProb_mono _ _ fun c D ⟨hx, _, hok⟩ => ?_
  obtain ⟨w, hw, hrel⟩ := (extractsAt_dbExtractBits_iff M (ringRel adm bind) Ext).2 hx
  have hR := hrel.2
  refine ⟨w, hw, _, (by simp only [decodeRing, hR.idx_lt, ↓reduceDIte]; rfl), hR.verify_eq, ?_⟩
  obtain ⟨i, hi, hc⟩ := hok _ hR.mem_ring
  exact ⟨i, hi, hc, not_false⟩

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] in
/-- **The acceptance probability of a distinguisher with one auxiliary value** is the oracle
average of its output law at `true`. -/
theorem acceptProb_distinguisher (a : A.Aux) (s : SideCoins Sch n Q)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) (M.Response B)) :
    (A.distinguisher bind adm pubOf a s).acceptProb C =
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.distinguisher bind adm pubOf a s).alg ()).compose C).outLaw H (some true) := by
  simp only [QueryBoundedAdversary.acceptProb, distinguisher]
  rw [tsum_eq_single () fun u hu => absurd (Subsingleton.elim u ()) hu]
  erw [PMF.pure_apply_self, one_mul]
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  rw [PMF.toOuterMeasure_map_apply]
  have : (fun o => (⟨o, Equiv.refl _ ∘ H⟩ : Outcome (Option Bool) (Bits (queryBits k kN kS L)) (XOut k e))) ⁻¹'
      {p | p.out = some true} = {some true} := by
    ext o
    simp
  rw [this, PMF.toOuterMeasure_apply_singleton]

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig]
  [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Fintype Sch.Sig]
  [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
/-- **The simulator inert on the empty ring assigns only at the keys of its chain inputs** when
the spBCS simulator does (`simAssignsAtKeys_niJointSimulatorProg`, digests of at least one byte):
on the empty ring it assigns nothing. -/
theorem simAssignsAtKeys_seSimulator (hk : 0 < k) :
    M.SimAssignsAtKeys B (seSimulator (B := B) Λ VE pub Sim T) id := by
  intro r c G qa hqa
  have hS := simAssignsAtKeys_niJointSimulatorProg hk Λ VE B pub Sim T r c G qa
  simp only [seSimulator, inertOnEmpty] at hqa ⊢
  split_ifs at hqa ⊢ with h
  · simp at hqa
  · exact hS hqa

open Classical in
/-- **Zero knowledge at one auxiliary value and one value of the side coins**: the distinguisher
accepts against the real challenger with probability at most its acceptance against the
simulated challenger plus `zkError δ t Q` (`SPBCS.everlastingZeroKnowledge_qrom`). -/
theorem acceptProb_real_le {δ : ℝ≥0} (hvzk : CausalHVZK VE.MV (ringRel adm bind) honest pub Sim δ)
    (a : A.Aux) (s : SideCoins Sch n Q) :
    (A.distinguisher bind adm pubOf a s).acceptProb (realChallenger (relayRel bind adm)
        ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).comap Prod.fst
          RelayWit.toWit) (PMF.uniformOfFintype _) Q) ≤
      (A.distinguisher bind adm pubOf a s).acceptProb (simChallenger (relayRel bind adm)
        ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q) +
        ENNReal.ofReal (M.zkError δ t Q) := by
  have hzk := M.everlastingZeroKnowledge_qrom Λ honest E VE hb T
    (Prod.fst : RelayStmt Sch n N RMsg → RingStmt Sch RMsg N) (RelayWit.toWit (Sch := Sch) (N := N)) hvzk
  unfold NARG.QROM.EverlastingZeroKnowledge at hzk
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    M.encode_niSimulator Λ E VE hb] at hzk
  have hD : (A.distinguisher bind adm pubOf a s).QueriesBeforeLastProofQuery t := fun _ =>
    ⟨(A.alg a).budget, (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (A.queries_le a),
      AdaptiveIAlg.requestsAfterAtMost_thenProg ((A.alg a).absorb (zkRelay adm bind pubOf s))
        (A.forgeryTest a s) _ (A.forgeryTest_queriesLE a s)⟩
  have hle : ∀ C, (A.distinguisher bind adm pubOf a s).acceptProb C ≤ 1 := fun C => by
    rw [A.acceptProb_distinguisher]
    calc _ ≤ ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H * 1 :=
          ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (PMF.coe_le_one _ _) zero_le
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have key : ∀ x y : ℝ≥0∞, x ≤ 1 → y ≤ 1 → GordieHowe.advantage x.toReal y.toReal ≤ M.zkError δ t Q →
      x ≤ y + ENNReal.ofReal (M.zkError δ t Q) := fun x y hx hy h => by
    have h' : |x.toReal - y.toReal| ≤ M.zkError δ t Q := h
    have hz : 0 ≤ M.zkError δ t Q := (abs_nonneg _).trans h'
    have hr : x.toReal ≤ y.toReal + M.zkError δ t Q := by
      linarith [le_abs_self (x.toReal - y.toReal)]
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hy),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hz]
    exact ENNReal.ofReal_le_ofReal hr
  have h := hzk t Q _ (A.distinguisher bind adm pubOf a s) hD
  convert key _ _ (hle _) (hle _) h using 4

omit [Nonempty Sch.Sig] [NeZero n] in
/-- **An average of `f + c` is the average of `f` plus `c`.** -/
theorem tsum_pmf_mul_add {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' x, μ x * (f x + c) = ∑' x, μ x * f x + c := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Nonempty Sch.Sig] [NeZero n] in
/-- **An average of `f ≤ g + c` is at most the average of `g` plus `c`.** -/
theorem tsum_pmf_mul_le_add {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x, f x ≤ g x + c) : ∑' x, μ x * f x ≤ ∑' x, μ x * g x + c := by
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * (g x + c) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul_of_nonneg_left (h x) zero_le
    _ = ∑' x, μ x * g x + c := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Nonempty Sch.Sig] [NeZero n] [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Nonempty Sch.Pub] in
/-- **Replacing the honest signer of BKM06 by the checked one costs at most `Q · ε`** for a scheme
with correctness error `ε` (`hcorr`): the two layers disagree on a request only when its drawn
signature fails to verify (`draw_bkmLayer_ne_checked_le`), and the request is fixed before its
draw is read (`Quantum.SplitChallenger.toOuterMeasure_outLaw_le_add`). -/
theorem outLaw_bkm_le_checked {εc : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc) (a : A.Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((A.alg a).toKindAlg.composeBothOut ((bkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm).challenger Q) id).outLaw
        H).toOuterMeasure {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
      (((A.alg a).toKindAlg.composeBothOut ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm).challenger Q) id).outLaw
          H).toOuterMeasure {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} +
        Q * εc := by
  have h :=
      ((bkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm).split Q).toOuterMeasure_outLaw_le_add
    ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm).split Q).reply
    ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm).split Q).reply_queries
    (fun κ i r _ => draw_bkmLayer_ne_checked_le (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm hcorr Q κ i r) (A.alg a).toKindAlg H
    (fun adv lg κ _ => A.WinAt a κ adv.workspace.1 lg H)
  rw [← split_checkedBkmLayer] at h
  exact h

omit [Nonempty Sch.Sig] [NeZero n] [Fintype Sch.Msg] [DecidableEq Sch.Msg] in
/-- **Replacing the checked simulated signer by the simulated one costs at most `Q · ε`** for a
scheme with correctness error `ε` (`hcorr`): the two disagree on a request only when its drawn
signature fails to verify (`draw_simSplit_ne_le`). -/
theorem outLaw_simChecked_le {εc : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc) (a : A.Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((A.alg a).toKindAlg.composeBothOut
        (simBKMCheckedChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind pubOf Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
      (((A.alg a).toKindAlg.composeBothOut
          (simBKMChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
            (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} + Q * εc := by
  have hε := fun κ i r => draw_simSplit_ne_le (n := n) (bind := bind) (adm := adm) hcorr (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) pubOf Q κ i r
  have h := (simSplit (n := n) (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q (drawOk Sch N RMsg bind)).toOuterMeasure_outLaw_le_add
    (simSplit (n := n) (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q fun _ _ _ => True).reply
    (simSplit (n := n) (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm pubOf Q fun _ _ _ => True).reply_queries
    (fun κ i r _ => hε κ i r) (A.alg a).toKindAlg H
    (fun adv lg κ G => A.WinAt a κ adv.workspace.1 lg G)
  rw [← simSplit_withReply] at h
  exact h

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
compiled by spBCS, at every base-message map** (TCC 2006, LNCS p. 67; ePrint 2005/304, p. 7:
adversarially chosen rings, adaptive corruption, ring-signing queries, no ordinary signing
oracle), including converted signatures (`bind R m = m`). For a base scheme with correctness error
`εc` (`hcorr`) whose honest signatures have public values `pubOf` of their signing coins (`hpub`:
Falcon's salt, or `Pub = Unit`), the spBCS compilation `M` of a ring composite that is
honest-verifier zero knowledge with error `δ` at
the joint simulator `Sim` (`hvzk`) and round-by-round knowledge sound in the series–parallel
order at the extractor `Ext` with errors `ε` (`hrbr`), with the proof format bounded by `B`
(`hb`) and digests of at least one byte (`hk`): the probability that an adversary of BKM06 with
at most `Q` requests and `t` queries of its own wins (`insiderWinProb`, the ring signatures
produced by the compiled honest prover `niProver` at the site layout `Λ`, run through
`queryEncoding`) is at most the success probability of the explicit forger of the multi-user
signature game (`simForgerSuccess`: the forger reaches the keys only through public keys and
corruptions of the base oracles, makes no signing request, and outputs one candidate), plus the
zero-knowledge error `zkError δ t Q`, the simulation-extraction error at the simulator's `q`
queries, the knowledge error at `t + Q · q_P + kq` queries (the forgeries on the empty ring, which
has no witness), and `2 Q εc` (each of the `Q` ring signatures with a drawn signature that fails
to verify, once in the real game and once in the simulated one). Here `kq = kqOf Mg nr B B`
bounds the verifier's queries and `q_P` those of one honest prover run. The zero-knowledge error
counts all `Q` requests as proof queries: public-key and corruption requests are relayed as proof
queries of a statement with no witness, which both zero-knowledge challengers refuse. -/
theorem insiderWinProb_le_of_zeroKnowledge (hk : 0 < k) {εc : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc)
    (hpub : Sch.PubOfCoins pubOf) {δ : ℝ≥0}
    (hvzk : CausalHVZK VE.MV (ringRel adm bind) honest pub Sim δ)
    {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)}
    {St : CausalStateFn P τ (RingStmt Sch RMsg N)} {ε : ChIdx P τ → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) :
    A.insiderWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding)
        (PMF.uniformOfFintype _) bind adm ≤
      A.simForgerSuccess Λ VE pub Sim T bind adm pubOf Ext +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q +
            kqOf Mg nr B B) M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc := by
  classical
  have hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kqOf Mg nr B B :=
    fun _ _ _ hv => queries_length_le_of_formatBounds hb hv
  have h0 := A.emptyRing_le_knowledgeError (((M.niProver Λ honest E hb).mapOutput some).encode
    queryEncoding) (PMF.uniformOfFintype _) bind adm (fun _ => rfl)
    (M.knowledgeBound (ringRel adm bind) Ext St hrbr Qs _ hkq)
  have hse := (weak_online_simulation_extractability_qrom (B := B) Qs hkq hrbr
    (seSimulator (B := B) Λ VE pub Sim T)
    (simAssignsAtKeys_seSimulator Λ VE pub Sim T hk)).unruhSimExtraction_of_queryFreeTest hkq
  have hs : ∀ s : SideCoins Sch n Q, ∑' a, A.aux a * winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
      ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) ≤
      ∑' a, A.aux a * simProb (outEquiv k e)
        (extAdv Qs ((A.seAdversary adm pubOf s).alg a) ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q
          (kqOf Mg nr B B))
        (fun c D => ∃ w ∈ M.dbExtractBits Ext
            (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt D,
          ∃ f ∈ decodeRing bind (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt w,
            BaseForgery s.1 (fun i => BKMRequest.corrupt i ∈
                (requests (advWorkspace ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).1.logs).take Q)
              (fun _ _ => False) f) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q := fun s =>
    (hse (RelayStmt Sch n N RMsg) Prod.fst t Q (A.seAdversary adm pubOf s) fun a => A.okAt s a).trans
      (add_le_add (ENNReal.tsum_le_tsum fun a =>
        mul_le_mul_of_nonneg_left (A.extractFreshTestProb_le Λ VE pub Sim T bind adm pubOf s a)
          zero_le) le_rfl)
  have hσ : ∑ s : SideCoins Sch n Q, PMF.uniformOfFintype (SideCoins Sch n Q) s = 1 := by
    have h1 := (PMF.uniformOfFintype (SideCoins Sch n Q)).tsum_coe
    rwa [tsum_fintype] at h1
  have ha : ∀ a, ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
      (((A.alg a).toKindAlg.composeBothOut
        (challenger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm
          (Q := Q)) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
      ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) +
        ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc := by
    intro a
    have hsim : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (simBKMCheckedChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind pubOf Q) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
            (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
        ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
          winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
            ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) +
          Q * εc :=
      (tsum_pmf_mul_le_add _ _ _ _ fun H => A.outLaw_simChecked_le Λ VE pub Sim T bind adm pubOf
        hcorr a H).trans (add_le_add (A.simBKM_le_sum_winTestProb Λ hb VE pub Sim T adm pubOf a) le_rfl)
    have hreal : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm).challenger Q) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
        ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
          (((A.alg a).toKindAlg.composeBothOut
            (simBKMCheckedChallenger (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind pubOf Q) id).outLaw H).toOuterMeasure
            {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
              (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} +
          ENNReal.ofReal (M.zkError δ t Q) := by
      simp_rw [A.outLaw_bkm_eq_sum_real Λ hb honest bind adm pubOf hpub a]
      rw [tsum_mul_sum_comm]
      simp_rw [← A.acceptProb_distinguisher]
      calc _ ≤ ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
            ((A.distinguisher bind adm pubOf a s).acceptProb (simChallenger (relayRel bind adm)
              ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q) +
              ENNReal.ofReal (M.zkError δ t Q)) :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
              (A.acceptProb_real_le Λ hb honest VE pub Sim T bind adm pubOf hvzk a s) zero_le
        _ = ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
              (A.distinguisher bind adm pubOf a s).acceptProb (simChallenger (relayRel bind adm)
                ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q) +
              ENNReal.ofReal (M.zkError δ t Q) := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ, one_mul]
        _ = _ := by
            congr 1
            simp_rw [A.acceptProb_distinguisher]
            rw [← tsum_mul_sum_comm]
            simp_rw [A.sum_sim_eq_outLaw_simBKM Λ VE pub Sim T bind adm pubOf hpub a]
    calc _ ≤ _ := tsum_pmf_mul_le_add _ _ _ _ fun H => A.outLaw_bkm_le_checked Λ hb honest bind adm
            hcorr a H
      _ ≤ _ := add_le_add (hreal.trans (add_le_add hsim le_rfl)) le_rfl
      _ = _ := by ring
  refine (A.insiderWinProb_le_add _ _ bind adm).trans ?_
  have hmain : ∑' a, A.aux a * ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (challenger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (PMF.uniformOfFintype _) bind adm
            (Q := Q)) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
      A.simForgerSuccess Λ VE pub Sim T bind adm pubOf Ext + ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q + 2 * Q * εc := by
    calc _ ≤ ∑' a, A.aux a * (∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
          winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
            ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc)) :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ((ha a).trans_eq (add_assoc _ _ _))
            zero_le
      _ = ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s * ∑' a, A.aux a *
            winTestProb Qs ((A.seAdversary adm pubOf s).alg a)
              ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAt s a) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) := by
          rw [tsum_pmf_mul_add, tsum_mul_sum_comm]
      _ ≤ ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s * (∑' a, A.aux a * simProb (outEquiv k e)
            (extAdv Qs ((A.seAdversary adm pubOf s).alg a)
              ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
            (fun c D => ∃ w ∈ M.dbExtractBits Ext
                (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt D,
              ∃ f ∈ decodeRing bind (advOut ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).stmt w,
                BaseForgery s.1 (fun i => BKMRequest.corrupt i ∈
                    (requests (advWorkspace ((A.seAdversary adm pubOf s).alg a).toTPKindAlg _ Q c).1.logs).take Q)
                  (fun _ _ => False) f) +
            M.simExtractionError (kqOf Mg nr B B) (maxError ε)
              (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) :=
          add_le_add (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hs s) zero_le) le_rfl
      _ = _ := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ, one_mul]
          rw [← simExtractForgery_eq, simExtractForgery, tsum_mul_sum_comm]
          ring
  calc _ ≤ _ := add_le_add hmain h0
    _ = _ := add_right_comm _ _ _

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) at every base-message
map, for a perfectly correct base scheme** (`insiderWinProb_le_of_zeroKnowledge` at correctness
error `0`, `SigScheme.Correct.correctWithin`): the bound without the correctness term. -/
theorem insiderWinProb_le_of_correct (hk : 0 < k) (hcorr : Sch.Correct) (hpub : Sch.PubOfCoins pubOf)
    {δ : ℝ≥0} (hvzk : CausalHVZK VE.MV (ringRel adm bind) honest pub Sim δ)
    {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)}
    {St : CausalStateFn P τ (RingStmt Sch RMsg N)} {ε : ChIdx P τ → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) :
    A.insiderWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding)
        (PMF.uniformOfFintype _) bind adm ≤
      A.simForgerSuccess Λ VE pub Sim T bind adm pubOf Ext +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q +
            kqOf Mg nr B B) M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have h := A.insiderWinProb_le_of_zeroKnowledge Λ hb honest VE pub Sim T bind adm pubOf hk
    hcorr.correctWithin hpub hvzk hrbr
  rwa [mul_zero, add_zero] at h

end BKMAdversary

end SPBCS

end GordieHowe.Ring
