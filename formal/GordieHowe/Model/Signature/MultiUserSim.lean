-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUser
public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Model.Quantum.Interactive.CoSimQuery

@[expose] public section

/-!
# Multi-user forgers that hold a compressed-oracle simulation

An adversary of the multi-user games of `GordieHowe/Model/Signature/MultiUser.lean` that runs, in
its workspace, the compressed-oracle simulation `Sim*` (CMS19 section 3.6) of a query algorithm
with request points (`Quantum.ReqQueryAlg`) and sends the request points to the multi-user
challenger (`Quantum.ReqQueryAlg.coSimAdv`), its output read off the simulated algorithm's output
and the measured database. It makes no oracle query. When the signing oracle makes no query
(`SignOracle.NoQuery`; `noQuery_ring`, `noQuery_ringStd` for an oracle-free base signer), the
challenger answers every request point by a function of its coins, the step and the request
(`muReplyAfter`), and the forger's success in MU-EUF-CMA^corr is an average of Born weights of the
simulated states (`muEufProb_coSimMU`).

- `SignOracle.NoQuery`, `SignOracle.noQuery_ring`, `SignOracle.noQuery_ringStd`.
- `ForgesReq`, `forges_iff_forgesReq`: the winning condition read from the requests of the history
  (the replies do not enter it).
- `muReplyAfter`, `run_respond_muChallenger`: the challenger's reply after `k` requests.
- `coSimMU`: the forger, a `MUAdversary` with `0` queries, from a family of query algorithms with
  request points indexed by the public keys and an auxiliary input, and a readout of the forgery.
- `muEufProb_coSimMU`: its success probability with `Q'` requests, for `Q'` at least the number of
  request points.
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature GordieHowe.QROM
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB}

/-- **A signing oracle without queries**: its signer makes no oracle query. -/
def SignOracle.NoQuery (O : SignOracle B) : Prop :=
  ∀ kp sm c, (O.sign kp sm c).QueriesLE 0

/-- The ring-aware signing oracle of an oracle-free base signer makes no query. -/
theorem SignOracle.noQuery_ring (hB : B.OracleFree) : (SignOracle.ring B).NoQuery := by
  intro kp p c
  change (if kp.1 ∈ p.1.1 then B.bsign kp.2 p.1 (p.1.1.idxOf kp.1) p.2 c else .pure none).QueriesLE
    0
  split_ifs
  · exact hB.bsign_noQuery _ _ _ _ _
  · exact OracleProg.QueriesLE.pure _ _

/-- The ring-aware and ordinary signing oracles of an oracle-free base signer make no query. -/
theorem SignOracle.noQuery_ringStd (hB : B.OracleFree) : (SignOracle.ringStd B).NoQuery := by
  intro kp sm c
  rcases sm with p | bm
  · exact SignOracle.noQuery_ring hB kp p c
  · exact hB.ssign_noQuery _ _ _

variable {O : SignOracle B} {n : ℕ}

/-- The public key of user `0`, as the default request. -/
instance [NeZero n] : Inhabited (MURequest O n) := ⟨.publicKey 0⟩

/-- **A forgery of MU-EUF-CMA^corr read from the requests** `rs` of the history: `σ` verifies on
`bm` under `pk` at `H`, and `pk` is the key of a user that no request of `rs` corrupts or asks to
sign for `bm`. -/
def ForgesReq (keys : Fin n → B.KeyCoins) (H : X → Y) (f : B.PK × B.BMsg × B.BSig)
    (rs : List (MURequest O n)) : Prop :=
  B.bverify H f.1 f.2.1 f.2.2 = true ∧ ∃ i, B.pk (keys i) = f.1 ∧ MURequest.corrupt i ∉ rs ∧
    ∀ sm, MURequest.sign i sm ∈ rs → O.base sm ≠ f.2.1

/-- **The winning condition reads only the requests of the history.** -/
theorem forges_iff_forgesReq (keys : Fin n → B.KeyCoins) (H : X → Y) (f : B.PK × B.BMsg × B.BSig)
    (hist : MUHist O n) :
    Forges keys H f hist ↔ ForgesReq keys H f (hist.map HistoryEntry.request) := by
  constructor
  · rintro ⟨hv, i, hi, hc, hs⟩
    refine ⟨hv, i, hi, fun h => hc ?_, fun sm h hb => hs ?_⟩
    · obtain ⟨e, he, hr⟩ := List.mem_map.1 h
      exact ⟨e, he, hr⟩
    · obtain ⟨e', he', hr⟩ := List.mem_map.1 h
      exact ⟨e', he', sm, hr, hb⟩
  · rintro ⟨hv, i, hi, hc, hs⟩
    refine ⟨hv, i, hi, fun ⟨e, he, hr⟩ => hc (hr ▸ List.mem_map_of_mem he), ?_⟩
    rintro ⟨e, he, sm, hr, hb⟩
    exact hs sm (hr ▸ List.mem_map_of_mem he) hb

variable [AddGroup Y]

variable (O) in
/-- **The reply of the multi-user challenger after `k` requests** at the key coins `keys` and the
coins `c` (`muChallenger`), for a signing oracle without queries (its signer read at the zero
oracle): `none` from the `Q'`-th request on. -/
def muReplyAfter (keys : Fin n → B.KeyCoins) (Q' : ℕ) (c : Fin Q' → O.Coins) (k : ℕ)
    (r : MURequest O n) : Option (MUResponse B) :=
  if h : k < Q' then
    match r with
    | .publicKey i => some (.publicKey (B.pk (keys i)))
    | .sign i sm => ((O.sign (B.keyGen (keys i)) sm (c ⟨k, h⟩)).run fun _ => 0).map .signature
    | .corrupt i => some (.keyCoins (keys i))
  else none

/-- **The multi-user challenger answers by `muReplyAfter`** after a history of `k` requests, without
assignments, at every oracle, for a signing oracle without queries. -/
theorem run_respond_muChallenger (hO : O.NoQuery) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    (c : Fin Q' → O.Coins) (hist : MUHist O n) (r : MURequest O n) (H : X → Y) :
    ((muChallenger O n keys Q').respond c hist r).run H =
      ⟨muReplyAfter O keys Q' c hist.length r, []⟩ := by
  simp only [muChallenger, muReplyAfter]
  split_ifs with h
  · rcases r with i | ⟨i, sm⟩ | i
    · rfl
    · simp only [OracleProg.run_bind, OracleProg.run_pure]
      rw [OracleProg.run_eq_of_queriesLE_zero (hO _ _ _) H fun _ => 0]
    · rfl
  · rfl

/-! ### The forger -/

/-- **The composition of an adversary with its output read through `g`**, read as its output and
history, is the composition of the adversary read as `g` of its output and its history. -/
theorem _root_.GordieHowe.Quantum.AdaptiveIAlg.composeBothOut_mapOut {X Y Req Resp O O' : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
    [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
    {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (g : O → O') (C : Challenger X Y Req Resp) :
    ((A.mapOut g).toKindAlg.composeBothOut C fun v =>
        ((A.mapOut g).output C v, (A.mapOut g).history C v)) =
      A.toKindAlg.composeBothOut C fun v => (g (A.output C v), A.history C v) :=
  rfl

section Forger

variable {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {TB : BaseTypes} {B : BaseSigner (Bits m) (BitStr I J) N TB} (O : SignOracle B) [NeZero n]
  (e : BitStr I J ≃ Bd)

/-- **The forger holding a compressed-oracle simulation**: on the public keys `pks`, it draws the
auxiliary input `a` from `aux pks`, runs the compressed-oracle simulation of the query algorithm
with request points `G pks a` with its request points sent to the multi-user challenger
(`ReqQueryAlg.coSimAdv`), and outputs `g pks a` of the simulated algorithm's output and the measured
database. It makes no oracle query and does not read the table. -/
noncomputable def coSimMU (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    (t : ∀ pks, Aux pks → ℕ) (Ot : ∀ pks, Aux pks → Type)
    (G : ∀ pks a, ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B) (t pks a)
      (Ot pks a))
    (g : ∀ pks a, Ot pks a × DB (Bits m) Bd → B.PK × B.BMsg × B.BSig) :
    MUAdversary O n (OracleView.queriesOnly _ _) 0 := fun p =>
  { Aux := Aux p.1
    aux := aux p.1
    sh a := ((ReqQueryAlg.coSimAdv e (G p.1 a) (BitStr I J)).mapOut (g p.1 a)).toShape
    alg a := (ReqQueryAlg.coSimAdv e (G p.1 a) (BitStr I J)).mapOut (g p.1 a)
    tracePreserving a := ReqQueryAlg.coSimAdv_tracePreserving (G := G p.1 a) (Y := BitStr I J) e
    withinBudget a := AdaptiveIAlg.mapOut_withinBudget
      (ReqQueryAlg.coSimAdv_withinBudget (G := G p.1 a) (Y := BitStr I J) e) (g p.1 a)
    queries_le a := (ReqQueryAlg.coSimAdv_queries (G := G p.1 a) (Y := BitStr I J) e).le }

/-- **The success probability of the forger holding a compressed-oracle simulation** in
MU-EUF-CMA^corr with `Q'` requests, at least the number `t + 1` of request points (`hQ`), for a
signing oracle without queries (`hO`): averaged over the users' key coins, the oracle, the
auxiliary input and the challenger's coins `c`, the Born weight of `|Sim*⟩` of the instance with the
replies `muReplyAfter keys Q' c` on the outcomes whose readout `g` is a forgery (`ForgesReq`) for
the logged requests. The number `t pks a + 1` of request points may depend on the public keys and
the auxiliary value. -/
theorem muEufProb_coSimMU (hO : O.NoQuery) (Aux : (Fin n → B.PK) → Type)
    (aux : ∀ pks, PMF (Aux pks)) (t : ∀ pks, Aux pks → ℕ) (Ot : ∀ pks, Aux pks → Type)
    (G : ∀ pks a, ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B) (t pks a)
      (Ot pks a))
    (g : ∀ pks a, Ot pks a × DB (Bits m) Bd → B.PK × B.BMsg × B.BSig) (Q' : ℕ)
    (hQ : ∀ pks a, t pks a + 1 ≤ Q') :
    muEufProb (coSimMU O e Aux aux t Ot G g) Q' =
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
          ∑' a, aux (fun i => B.pk (keys i)) a *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              bornWeight
                (simState e ((G (fun i => B.pk (keys i)) a).inst (muReplyAfter O keys Q' c)))
                {b | ForgesReq keys H (g (fun i => B.pk (keys i)) a
                  ((G (fun i => B.pk (keys i)) a).out b.1.1.1, slotsDB e b.2))
                  (requests b.1.1.2)} := by
  classical
  simp only [muEufProb, muLaw, runLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    QueryBoundedAdversary.transcriptLaw]
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun H => congrArg _ (tsum_congr fun a => ?_))
  congr 1
  set G' := G (fun i => B.pk (keys i)) a
  set g' := g (fun i => B.pk (keys i)) a
  have hset : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (Bits m → BitStr I J) ×
      Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) | ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} =
      {o | ∃ p ∈ o, Forges keys H p.1 p.2} := rfl
  rw [hset]
  -- TODO(unbundle-M4): rewriting `alg` leaves the scheme's `sh a` in the shape argument; state
  -- `composeBothOut_mapOut` at the field shape and go back to `rw`
  change ((KindAlg.composeBothOut (muChallenger O n keys Q')
      (ReqQueryAlg.coSimAdv e G' (BitStr I J)).toKindAlg fun v =>
        (g' ((ReqQueryAlg.coSimAdv e G' (BitStr I J)).output (muChallenger O n keys Q') v),
          (ReqQueryAlg.coSimAdv e G' (BitStr I J)).history (muChallenger O n keys Q') v)).outLaw
        H).toOuterMeasure {o | ∃ p ∈ o, Forges keys H p.1 p.2} = _
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  simp only [forges_iff_forgesReq]
  rw [← KindAlg.toOuterMeasure_outLaw_composeBothOut (ReqQueryAlg.coSimAdv e G'
    (BitStr I J)).toKindAlg (muChallenger O n keys Q') (fun v =>
      ((ReqQueryAlg.coSimAdv e G' (BitStr I J)).output (muChallenger O n keys Q') v,
        (ReqQueryAlg.coSimAdv e G' (BitStr I J)).history (muChallenger O n keys Q') v)) H
    (fun p => ForgesReq keys H (g' p.1) (p.2.map HistoryEntry.request))]
  exact ReqQueryAlg.toOuterMeasure_outLaw_coSimAdv_history e (G := G') H
    (muChallenger O n keys Q') (muReplyAfter O keys Q') (hQ _ a)
    (fun c k hist w hl => (run_respond_muChallenger hO keys Q' c hist _ H).trans (by rw [hl]))
    (fun c hist r H' => by rw [run_respond_muChallenger hO keys Q' c hist r H'])
    (fun o rs => ForgesReq keys H (g' o) rs)

end Forger

end GordieHowe.Signature
