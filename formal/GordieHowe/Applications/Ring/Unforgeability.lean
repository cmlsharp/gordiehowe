-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Games
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.Headline

@[expose] public section

/-!
# Unforgeability of the ring signature from knowledge soundness and the base scheme

The reduction of the ring games of `GordieHowe/Applications/Ring/Games.lean` to the multi-user signature game with
adaptive corruption, by straight-line knowledge extraction
(`GordieHowe.SPBCS.QROM.acceptsTest_le_pure_of_queryCount`, CMS19 Theorem 8.6 (2) with a classical test),
generically for a compiled verifier with a knowledge bound (`GordieHowe.NARG.QROM.Verifier.KnowledgeBound`), and for the
spBCS compilation of a ring composite (`GordieHowe.SPBCS`, `GordieHowe.SPBCS.knowledgeBound` from
round-by-round knowledge soundness in the series–parallel order).

The ring adversary composed with the ring challenger is one algorithm of the model: the ring
challenger's honest prover runs are classical queries of the composed algorithm, so only knowledge
soundness of the BCS argument is used, no zero knowledge and no simulation. The composition is
dominated by that of the trace-preserving form of the adversary
(`AdaptiveIAlg.realLaw_composeBothOut_le`), whose branches make at most `t + Q · q` unpadded
queries (`AdaptiveIAlg.tpQueryCount`), whatever the number of slots. The test is the
freshness of the forgery (`ConvertedFresh`), a classical predicate of the composed registers. The
forger `RingAdversary.forger` runs the adversary through the ring layer over the base oracles,
simulates the oracle with a compressed oracle, extracts a witness `(i, σ)` for the statement of
the forgery and outputs `(R*_i, bind R* m*, σ)`. On a fresh forgery the extracted signature is a
base forgery: the key `R*_i` is that of an uncorrupted user who was never asked to sign
`bind R* m*`, in particular not by a ring-signing request on another ring (`ringLayer` asks the
base signature on `bind R m`).

- `convertedWinProb_le_of_knowledgeBound`, `bkmWinProb_le_of_knowledgeBound`: the bounds for a
  compiled verifier `V` with a knowledge bound, a database extractor and an honest prover program.
- `convertedWinProb_le` (spBCS): the converted-signature game. With `bind R m = m`: a
  valid ring signature on `(R*, m*)` whose members are honest and uncorrupted implies that some
  member was asked to sign `m*`, ordinarily or in a ring signature, except with the forger's success
  probability and the knowledge error.
- `bkmWinProb_le` (spBCS): BKM06 Definition 7 (insider corruption, adversarially
  chosen rings, with an additional ordinary signing oracle) when `bind` is injective (the base
  message binds the ring, as BKM06's generic construction signs `M ‖ PK_1 ‖ … ‖ PK_n`, Section 5,
  LNCS p. 68): the freshness of BKM06 implies `ConvertedFresh`
  (`RingAdversary.convertedFresh_of_bkmFresh`).
- `convertedWinProb_le_of_success_le`, `bkmWinProb_le_of_success_le`: the same with the base
  assumption `success ≤ ε` for the explicit forger as a hypothesis.

For `bind R m = m` (the converted-signature construction) BKM06 Definition 7 is not covered by
this reduction: a forgery on `(R*, m*)` after a ring-signing request on `(R', m*)`, `R' ≠ R*`, may
extract the base signature that request produced.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum GordieHowe.QROM
open scoped NNReal ENNReal

/-- An average of bounds `x a ≤ y a + c` over a distribution is a bound `∑ x ≤ ∑ y + c`. -/
theorem tsum_mul_le_tsum_mul_add {α : Type*} (μ : PMF α) {x y : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, x a ≤ y a + c) : ∑' a, μ a * x a ≤ ∑' a, μ a * y a + c := by
  calc ∑' a, μ a * x a ≤ ∑' a, (μ a * y a + μ a * c) :=
        ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; gcongr; exact h a
    _ = ∑' a, μ a * y a + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

variable {Sch : SigScheme} {n : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {N : ℕ} {adm : List Sch.PK → Prop} {m k e : ℕ} {Pf Resp Coins : Type} [Fintype Resp]
  [DecidableEq Resp] [Fintype Coins]
  {V : NARG.QROM.Verifier m k e (Claim (RingStmt Sch RMsg N) Pf) (RingStmt Sch RMsg N)}
  (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
  (bind : List Sch.PK → RMsg → Sch.Msg)

/-- **The decoding of an extracted ring witness**: the key at the witness's position, the base
message `bind R m`, and the base signature; `none` if the position is outside the ring. -/
def decodeRing (x : RingStmt Sch RMsg N) (w : RingWit Sch) : Option (Sch.PK × Sch.Msg × Sch.Sig) :=
  if h : w.idx < x.ring.1.length then some (x.ring.1[w.idx], bind x.ring.1 x.msg, w.sig) else none

namespace RingAdversary

variable {t Q : ℕ} (A : RingAdversary V Resp n t Q)

/-- **The forger built from a ring adversary** (`ExtractionForger`): the adversary run through the
ring layer over the base oracles (`ringLayer`, answering `Q` requests), the straight-line database
extractor `ext` at the statement of the forgery, and the decoding `decodeRing`.

Running time: the adversary's run composed with the ring challenger (each of its at most `Q`
requests answered by the ring layer: one base signature or corruption call and one run of the
honest prover program, at most `Pv.q` queries), then the verifier's `kq` queries on the forgery,
all answered by the compressed oracle with `T = t + Q · q + kq` slots (Zha19, ePrint 2018/276,
p. 7; DFMS22, ePrint 2021/280, App. B); the measurement of the database; `ext` on it (for
spBCS, `SPBCS.dbExtractBits`, polynomial by its Running time paragraph); one
base signature verification per candidate to select a witness; and `decodeRing`, linear in the ring
size. This running time is argued here, not proved in Lean. -/
noncomputable def forger (ext : RingStmt Sch RMsg N → DB (Bits m) (Out k e) → Multiset (RingWit Sch)) :
    ExtractionForger V Sch n (RingWit Sch) where
  Req := RingRequest Sch n N RMsg
  Resp := RingResponse Sch Resp
  layer := ringLayer Pv bind
  Q := Q
  Aux := A.Aux
  aux := A.aux
  alg := A.alg
  extractor := ext
  decode := decodeRing bind

variable {Pv bind}

/-- **A fresh forgery's extracted witness is a base forgery**: if the forgery is fresh
(`ConvertedFresh`) and `(i, σ)` is a witness of the ring relation for its statement, the decoded
candidate is a forgery of the multi-user game for the records of the run. -/
theorem baseForgery_decodeRing {a : A.Aux} {v : A.Register Pv bind a}
    (hf : A.ConvertedFresh Pv bind a v) {w : RingWit Sch}
    (hw : RingRel bind (A.claim Pv bind a v).stmt w) :
    ∃ f ∈ decodeRing bind (A.claim Pv bind a v).stmt w,
      BaseForgery v.chal.coins.1
        ((ringLayer Pv bind).Corrupted Q v.chal.coins (A.answered Pv bind a v))
        ((ringLayer Pv bind).Signed Q v.chal.coins (A.answered Pv bind a v)) f := by
  refine ⟨_, by rw [decodeRing, dite_eq_left_of_eq_true (eq_true hw.idx_lt)]; rfl, hw.verify_eq, ?_⟩
  obtain ⟨i, hi, hc⟩ := hf.honest_ring _ hw.mem_ring
  refine ⟨i, hi, hc, hf.unsigned i ?_⟩
  rw [hi]
  exact hw.mem_ring

/-- **The per-branch query count of the composition** (`AdaptiveIAlg.tpQueryCount`) is at most
`t + Q · q`, `q` the queries of one prover run: `width` per query slot, at most `budget` query
slots, `q` per answered request, at most `Q` answered requests, `width` per post batch. -/
theorem branchQueries_le (a : A.Aux) :
    (A.alg a).width * (A.alg a).budget + Q * Pv.q + (A.alg a).width * (A.alg a).post ≤
      t + Q * Pv.q := by
  have h2 := A.queries_le a
  nlinarith

variable (Pv bind)

/-- **Unforgeability in the converted-signature game for a compiled verifier with a knowledge
bound** (`GordieHowe/Applications/Ring/Games.lean`), at one ring adversary: for a compiled verifier `V` whose claims'
statements are read by `Claim.stmt` (`hV`), with a knowledge bound for the ring relation at the
database extractor `ext` and the database bound `β` (`K`, CMS19 Proposition 8.12 and Lemmas
5.9–5.10), the probability that a ring adversary with at most `Q` requests and `t` queries of its
own wins the converted-signature game (`convertedWinProb`) is at most the success probability of the
explicit forger `A.forger Pv bind ext` in the multi-user signature game with adaptive corruption,
plus the knowledge error at `t + Q · q + kq` queries (`q = Pv.q` the queries of one honest prover
run). -/
theorem convertedWinProb_le_of_knowledgeBound (hV : ∀ c, V.stmt c = c.stmt)
    {ext : RingStmt Sch RMsg N → DB (Bits m) (Out k e) → Multiset (RingWit Sch)} {β : ℕ → ℝ≥0∞}
    (K : V.KnowledgeBound (ringRel adm bind) ext β) :
    A.convertedWinProb Pv bind ≤ (A.forger Pv bind ext).success +
      V.knowledgeError β (t + Q * Pv.q + V.kq) := by
  refine tsum_mul_le_tsum_mul_add A.aux fun a => ?_
  set C := challenger Pv bind (Q := Q) (n := n) (N := N)
  set B := (A.alg a).toTPKindAlg.composeBothOut C id
  have hdom := (A.alg a).realLaw_composeBothOut_le C id (outEquiv k e)
    {p | ∃ v ∈ p.out, A.ConvertedWins Pv bind a v p.oracle}
    (fun p ⟨v, hv, _⟩ => by rw [Option.mem_def] at hv; rw [hv]; simp)
  have hle : (B.realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ v ∈ p.out, A.ConvertedWins Pv bind a v p.oracle} ≤
      (B.realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ v ∈ p.out, A.ConvertedFresh Pv bind a v ∧ V.Accepted p.oracle (A.claim Pv bind a v)} :=
    MeasureTheory.measure_mono fun p ⟨v, hv, hw⟩ => ⟨v, hv, hw.2, hw.1⟩
  have hpure := B.toOuterMeasure_realLaw_le_coh (outEquiv k e) B.defaultOut
    {p | A.ConvertedFresh Pv bind a p.out ∧ V.Accepted p.oracle (A.claim Pv bind a p.out)}
  have hacc := SPBCS.QROM.acceptsTest_le_pure_of_queryCount K (A.claim Pv bind a)
    (A.ConvertedFresh Pv bind a) (B.toQueryAlgCoh.mapOut (·.getD B.defaultOut))
    (AdaptiveIAlg.tpQueryCount (outEquiv k e) (A.alg a) C id (·.getD B.defaultOut))
  refine hdom.trans (hle.trans (hpure.trans (hacc.trans (add_le_add ?_ ?_))))
  · refine simProb_mono _ _ fun v D ⟨hf, w, hwE, hw⟩ => ?_
    rw [hV] at hw hwE
    obtain ⟨f, hf', hb⟩ := A.baseForgery_decodeRing hf hw.2
    exact ⟨w, hwE, f, hf', hb⟩
  · exact V.knowledgeError_mono K.mono
      (Nat.add_le_add_right (A.branchQueries_le (Pv := Pv) a) _)

/-! ### BKM06 Definition 7 for a ring-binding base message -/

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The base calls of the ring layer that sign**: a base signature by user `i` on `m'` is asked
only by an ordinary signing request `(i, m')`, or by a ring-signing request by `i` on a ring `R`
and message `m` with `bind R m = m'`. -/
theorem sign_mem_trace_ringLayer {req : RingRequest Sch n N RMsg} {c}
    {O : BaseRequest Sch n → BaseResponse Sch} {i : Fin n} {m' : Sch.Msg}
    (h : BaseRequest.sign i m' ∈ ((ringLayer Pv bind).prog req c).trace O) :
    req = .base (.sign i m') ∨ ∃ ring m, req = .ringSign i ring m ∧ bind ring.1 m = m' := by
  rcases req with r | ⟨s, ring, m⟩
  · simp only [ringLayer, OracleProg.trace_query, OracleProg.trace_pure, List.mem_singleton] at h
    exact Or.inl (by rw [h])
  · simp only [ringLayer, OracleProg.trace_query, List.mem_cons, reduceCtorEq, false_or] at h
    refine Or.inr ⟨ring, m, ?_⟩
    rcases hO : O (.publicKey s) with pk | σ | kc
    · rw [hO] at h
      simp only [ringSignAfterKey] at h
      split_ifs at h
      · simp only [OracleProg.trace_query, List.mem_cons, BaseRequest.sign.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | h
        · exact ⟨rfl, rfl⟩
        · rcases hO2 : O (.sign s (bind ring.1 m)) with _ | _ | _ <;> simp [hO2] at h
      · simp at h
    · rw [hO] at h
      simp at h
    · rw [hO] at h
      simp at h

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- A base call of the answered requests comes from one of them. -/
theorem exists_mem_of_signed {Q : ℕ} {ω : (ringLayer Pv bind).Draw Q}
    {reqs : List (RingRequest Sch n N RMsg)} {i : Fin n} {m' : Sch.Msg}
    (h : (ringLayer Pv bind).Signed Q ω reqs i m') :
    ∃ req ∈ reqs, req = .base (.sign i m') ∨
      ∃ ring m, req = .ringSign i ring m ∧ bind ring.1 m = m' := by
  obtain ⟨⟨req, c⟩, hp, hc⟩ := List.mem_flatMap.1 h
  have hreq : req ∈ reqs := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.1 hp)
  refine ⟨req, hreq, ?_⟩
  simp only [OracleLayer.callsAt] at hc
  split_ifs at hc
  · exact sign_mem_trace_ringLayer Pv bind hc
  · simp at hc

variable {t Q : ℕ} (A : RingAdversary V Resp n t Q)

/-- **BKM06 freshness implies the freshness of the converted game when `bind` is injective**:
a member asked to sign `bind R* m*` was asked by an ordinary signing request (excluded by
`no_sign`) or by a ring-signing request on `(R, m)` with `bind R m = bind R* m*`, hence on
`(R*, m*)` (excluded by `no_ringSign`). -/
theorem convertedFresh_of_bkmFresh
    (hbind : Function.Injective2 bind) {a : A.Aux}
    {v : A.Register Pv bind a} (h : A.BKMFresh Pv bind a v) :
    A.ConvertedFresh Pv bind a v where
  honest_ring := h.honest_ring
  unsigned i hi hs := by
    have hex := exists_mem_of_signed Pv bind hs
    obtain ⟨req, hreq, hor⟩ := hex
    rcases hor with hb | ⟨ring, m, hr, hm⟩
    · exact h.no_sign i hi (hb ▸ hreq)
    · exact h.no_ringSign i ring m (hr ▸ hreq) (hbind hm)

/-- **BKM06 Definition 7 for a compiled verifier with a knowledge bound**, for a base message that
binds the ring (`bind` injective, `hbind`), at one ring adversary: under the hypotheses of
`convertedWinProb_le_of_knowledgeBound`, the probability that the adversary wins the game of
BKM06 Definition 7 (`bkmWinProb`) is at most the success probability of the forger
`A.forger Pv bind ext` plus the knowledge error at `t + Q · q + kq` queries. -/
theorem bkmWinProb_le_of_knowledgeBound (hbind : Function.Injective2 bind)
    (hV : ∀ c, V.stmt c = c.stmt)
    {ext : RingStmt Sch RMsg N → DB (Bits m) (Out k e) → Multiset (RingWit Sch)} {β : ℕ → ℝ≥0∞}
    (K : V.KnowledgeBound (ringRel adm bind) ext β) :
    A.bkmWinProb Pv bind ≤ (A.forger Pv bind ext).success +
      V.knowledgeError β (t + Q * Pv.q + V.kq) := by
  refine le_trans ?_ (A.convertedWinProb_le_of_knowledgeBound Pv bind hV K)
  refine ENNReal.tsum_le_tsum fun a => ?_
  gcongr with p v hv
  intro hp
  exact ⟨hp.1, A.convertedFresh_of_bkmFresh Pv bind hbind hp.2⟩

end RingAdversary

/-! ### The spBCS compilation of a ring composite -/

namespace RingAdversary

open SPBCS GordieHowe.SPBCS SPTerm

variable {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ} {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {kN kS L : ℕ}
  {M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e} (Λ : SiteLayout Mg) {B : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : RingStmt Sch RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs B B) {R : Type} [Fintype R] [Nonempty R]
  (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
  {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)}
  {St : CausalStateFn P τ (RingStmt Sch RMsg N)} {ε : ChIdx P τ → ℝ≥0}
  {t Q : ℕ} (A : RingAdversary (M.qVerifier Qs B B) (M.Response B) n t Q)

include hb

/-- **Unforgeability of the ring signature compiled by spBCS in the converted-signature game**
(`GordieHowe/Applications/Ring/Games.lean`), at one ring adversary: for the spBCS compilation `M` of a ring composite
that is round-by-round knowledge sound in the series–parallel order at the extractor `Ext` for the ring relation
with errors `ε` (`hrbr`, the paper's Theorem 5.2, `thm:backend`, at the instance), with the proof
format bounded by `B` (`hb`), the probability that a ring adversary of `def:adversary` with at most
`Q` requests and `t` queries of its own wins the converted-signature game against the compiled
honest prover `niProver` at the site layout `Λ`, run through `queryEncoding`, is at most the success probability of
the explicit forger `A.forger … (M.dbExtractBits Ext)` in the multi-user signature game with
adaptive corruption, plus the knowledge error of spBCS at `t + Q · q + kq`
queries (`q` the queries of one honest prover run, `kq = kqOf Mg nr B B` the verifier's). -/
@[headline]
theorem convertedWinProb_le (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) :
    A.convertedWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind ≤
      (A.forger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind (M.dbExtractBits Ext)).success +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q + kqOf Mg nr B B) M.senc.digestsPerInput
          Mg.nJ (maxError ε) :=
  A.convertedWinProb_le_of_knowledgeBound _ bind (fun _ => rfl)
    (M.knowledgeBound (ringRel adm bind) Ext St hrbr Qs _
      fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)

/-- **Unforgeability of the ring signature compiled by spBCS with respect to insider corruption**
(BKM06 Definition 7, TCC 2006, LNCS p. 67; adversarially chosen rings, adaptive corruption, and an
additional ordinary signing oracle) for a base message that binds the ring (`bind` injective,
`hbind`), at one ring adversary: under the hypotheses of `convertedWinProb_le`, the probability that
the adversary wins the game of BKM06 Definition 7 (`bkmWinProb`) is at most the success probability
of the forger plus the knowledge error of spBCS at `t + Q · q + kq` queries. -/
@[headline]
theorem bkmWinProb_le (hbind : Function.Injective2 bind)
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) :
    A.bkmWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind ≤
      (A.forger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind (M.dbExtractBits Ext)).success +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q + kqOf Mg nr B B) M.senc.digestsPerInput
          Mg.nJ (maxError ε) :=
  A.bkmWinProb_le_of_knowledgeBound _ bind hbind (fun _ => rfl)
    (M.knowledgeBound (ringRel adm bind) Ext St hrbr Qs _
      fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)

/-! ### With the base assumption -/

/-- **Unforgeability of the ring signature compiled by spBCS in the converted-signature game
under the base assumption**: if the forger built from the adversary succeeds in the multi-user
signature game with adaptive corruption with probability at most `ε'` (`hSig`, the assumption on the
base scheme for this forger), the adversary wins with probability at most `ε'` plus the knowledge
error of spBCS. -/
@[headline]
theorem convertedWinProb_le_of_success_le
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) {ε' : ℝ≥0∞}
    (hSig : (A.forger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind (M.dbExtractBits Ext)).success ≤ ε') :
    A.convertedWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind ≤
      ε' + knowledgeError k e (kqOf Mg nr B B)
        (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q + kqOf Mg nr B B) M.senc.digestsPerInput
        Mg.nJ (maxError ε) :=
  (A.convertedWinProb_le bind Λ hb honest hrbr).trans (add_le_add hSig le_rfl)

/-- **BKM06 Definition 7 for the ring signature compiled by spBCS under the base assumption** for
a ring-binding base message: if the forger built from the adversary succeeds with probability at
most `ε'` (`hSig`), the adversary wins the game of BKM06 Definition 7 with probability at most `ε'`
plus the knowledge error of spBCS. -/
@[headline]
theorem bkmWinProb_le_of_success_le (hbind : Function.Injective2 bind)
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) {ε' : ℝ≥0∞}
    (hSig : (A.forger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind (M.dbExtractBits Ext)).success ≤ ε') :
    A.bkmWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind ≤
      ε' + knowledgeError k e (kqOf Mg nr B B)
        (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q + kqOf Mg nr B B) M.senc.digestsPerInput
        Mg.nJ (maxError ε) :=
  (A.bkmWinProb_le bind Λ hb honest hbind hrbr).trans (add_le_add hSig le_rfl)

end RingAdversary

end GordieHowe.Ring
