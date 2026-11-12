-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Joint
public import GordieHowe.Model.Signature.MultiUser
public import GordieHowe.Applications.Ring.SPBCSRing
public import GordieHowe.Applications.Ring.InsiderTools
public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.Model.Quantum.Interactive.SplitHybrid
public import GordieHowe.Model.RingSignature.BaseCompleteness
public import GordieHowe.SPBCS.Extraction.OnlineExtractTest
public import GordieHowe.SPBCS.SimExtract

@[expose] public section

/-!
# Unforgeability of `ofBase` for a ring-binding base message, by knowledge soundness

The unforgeability games of `GordieHowe/Model/RingSignature/Unforgeability.lean` (BKM06
Definition 7, `insiderForgeProb`) and `GordieHowe/Model/RingSignature/Joint.lean`
(`jointForgeProb`) for the ring signature `ofBase B PS adm` with a base message that binds the
ring, bounded by knowledge soundness of the proof system and the base scheme's multi-user game.
The honest prover runs inside the challenger, so only knowledge soundness is used, no zero
knowledge and no simulation. The adversaries reach the oracle by queries only
(`OracleView.queriesOnly`); their start input is the honest users' public keys.

- `Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound`: for an interactive algorithm composed
  with any challenger and any readout of the composed registers, an accepted claim passing a
  classical test is extracted in the simulated run, except with the knowledge error at
  `t + Q · q + kq` queries.
- `UnforgeAdversary.at`, `UnforgeAdversary.runAt`, `forgeProb_le_tsum_realLaw`: the forgery
  probability as an average, over the users' key coins and the auxiliary input, of model runs at
  fixed key coins (the oracle's draw moves inside, since the start input does not read it).
- `ProofSystem.CompiledBy PS V`: a proof system whose verifier is the acceptance of a compiled
  verifier `V` on claims of statements and proofs; `compiledBy_spbcsProofSystem` for spBCS.
- `BaseSigner.BindsRing`: `bmsg` injective in `(R, m)`.
- `MURelay`, `MURelay.request`, `MURelay.hist`: the relay of the game's requests to a multi-user game
  with a signing oracle `SO` (`Signature.SignOracle`), corruptions as corruptions;
  `MURelay.corrupted_of_hist`, `MURelay.signed_hist`; `MURelay.KeepsFresh`: no member of a fresh
  ring was asked, in the relayed history, to sign for its base message. `insiderRelay` (to the
  ring-aware oracle `SignOracle.ring`) and `jointRelay` (to `SignOracle.ringStd`, ring-aware and
  ordinary) keep freshness for a ring-binding base message (`keepsFresh_insiderRelay`,
  `keepsFresh_jointRelay`).
- `stmtOf`, `claimOf`, `decodeWit`, `extractionSuccessAt`, `extractionSuccess`: the extraction
  forger and its success probability: in the simulated run (a compressed oracle) of the adversary
  composed with the challenger at the key coins, followed by the compiled verifier's queries on the
  forgery's claim, some witness extracted from the measured database decodes to
  `(R*_i, bmsg R* m*, σ)`, a forgery of MU-EUF-CMA^corr (`Signature.Forges`) at every oracle for the
  relayed history.
- `forgeProb_le_extractProb`: a forgery passing any test is extracted, except with the knowledge
  error. `forgeProb_le_of_knowledgeBound`: the forgery probability is at most the extraction forger's
  success plus the knowledge error, for a relay keeping freshness and a relation all of whose
  witnesses are witnesses of the ring relation at every oracle.
- `insiderForgeProb_le_of_knowledgeBound`, `jointForgeProb_le_of_knowledgeBound` (any compiled
  verifier with a knowledge bound): the bounds by the extraction forger's success. Their forms by
  MU-EUF-CMA^corr are the headlines
  (`insiderForgeProb_le_muEufProbWithin`, `insiderForgeProb_le_muEufProbWithin_spbcs` and
  the joint-security forms).

## The base term

`extractionSuccess` is the success probability of a forger of another form than the adversaries of
`Signature.MUAdversary`: it runs the adversary against the ring challenger at the users' key coins
(the challenger signs with the secret keys) and extracts from the compressed oracle's database. Its
winning condition is that of MU-EUF-CMA^corr
(`Signature.Forges` for the signing oracle `SO`) at the relayed history, which holds one signing request
for each answered ring-signing or side request of the game and one corruption for each answered
corruption. The theorems here
do not bound it by `Signature.muEufProb` of a `GameAdversary`.

## Oracle-reading base signers

The bound needs a relation independent of the oracle: the knowledge bound is for a fixed set of
statement-witness pairs, and the extracted witness must verify at every oracle for the decoded
candidate to be a forgery whatever oracle the multi-user game draws (`hrel`). Signers that read the
oracle are allowed: their queries are classical queries of the composed algorithm.

## What the library does not prove

The library does not prove two statements: the reduction of BKM06 Definition 7 to multi-user
strong unforgeability with corruption for base schemes whose public value depends on the signer's
key, and its instances for the public-w₁ ML-DSA ring; the converted-signature bound from knowledge
soundness alone (without zero knowledge). Converted signatures are bounded through the
zero-knowledge route of `GordieHowe/Applications/Ring/RingInsider.lean`.
-/

namespace GordieHowe

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum
open scoped NNReal ENNReal

/-! ### Knowledge soundness of a composition with a challenger, with a test -/

namespace Quantum.AdaptiveIAlg

variable {m k e : ℕ} {Req Resp O O' Cl Stmt Wit : Type} [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [DecidableEq O']

/-- **An accepted claim passing a test is extracted, except with the knowledge error**, for an
interactive algorithm composed with any challenger: for a compiled verifier `V` with a knowledge
bound for `rel` at the database extractor `ext` and the database bound `β` (`K`), an algorithm `A`
with at most `t` queries of its own on every branch (`ht`), a challenger `C`, a readout `f` of the
composed registers, a claim `c y` and a classical test `ok y` of the readout, the probability that
the composition terminates with a readout passing `ok` whose claim the verifier accepts is at most
the probability that, in the simulated run of the composition of the trace-preserving form followed
by the verifier's queries (`SPBCS.QROM.extAdvVia`), the measured readout passes `ok` and `ext`
returns a witness for the claim's statement from the measured database, plus the knowledge error
at `t + Q · q + kq` queries (`Q`, `q` the challenger's request and per-reply query bounds), for any
challenger and readout. -/
theorem acceptsTest_le_of_knowledgeBound {V : NARG.QROM.Verifier m k e Cl Stmt}
    {rel : Set (Stmt × Wit)} {ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit} {β : ℕ → ℝ≥0∞}
    (K : V.KnowledgeBound rel ext β) {shA : AlgShape (Bits m) (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (C : Challenger (Bits m) (XOut k e) Req Resp) (f : A.toKindAlg.CW C → O') (c : O' → Cl)
    (ok : O' → Prop) {t : ℕ} (ht : A.width * (A.budget + A.post) ≤ t) :
    ((A.toKindAlg.composeBothOut C f).realLaw (outEquiv k e)).toOuterMeasure
        {p | ∃ y ∈ p.out, V.Accepted p.oracle (c y) ∧ ok y} ≤
      simProb (outEquiv k e) (SPBCS.QROM.extAdvVia V c (A.toTPKindAlg.composeBothOut C f))
          (fun y D => ok y ∧ NARG.ExtractsAt rel ext (V.stmt (c y)) D) +
        V.knowledgeError β (t + C.Q * C.q + V.kq) := by
  set B := A.toTPKindAlg.composeBothOut C f
  have hdom := A.realLaw_composeBothOut_le (freeze := false) C f (outEquiv k e)
    {p | ∃ y ∈ p.out, V.Accepted p.oracle (c y) ∧ ok y}
    (fun p ⟨y, hy, _⟩ => by rw [Option.mem_def] at hy; rw [hy]; simp)
  have hle : (B.realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ y ∈ p.out, V.Accepted p.oracle (c y) ∧ ok y} ≤
      (B.realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ y ∈ p.out, ok y ∧ V.Accepted p.oracle (c y)} :=
    MeasureTheory.measure_mono fun p ⟨y, hy, hw⟩ => ⟨y, hy, hw.2, hw.1⟩
  have hpure := B.toOuterMeasure_realLaw_le_coh (outEquiv k e) B.defaultOut
    {p | ok p.out ∧ V.Accepted p.oracle (c p.out)}
  have hacc := SPBCS.QROM.acceptsTest_le_pure_of_queryCount K c ok
    (B.toQueryAlgCoh.mapOut (·.getD B.defaultOut))
    (AdaptiveIAlg.tpQueryCount (outEquiv k e) A C f (·.getD B.defaultOut))
  refine hdom.trans (hle.trans (hpure.trans (hacc.trans (add_le_add le_rfl ?_))))
  refine V.knowledgeError_mono K.mono (Nat.add_le_add_right ?_ _)
  change A.width * A.budget + C.Q * C.q + A.width * A.post ≤ t + C.Q * C.q
  nlinarith

end Quantum.AdaptiveIAlg

namespace RingSignature

/-! ### The unforgeability game as an average of model runs -/

section Decompose

variable {m k e : ℕ} {N : ℕ} {TS : RingTypes} {S : RingScheme (Bits m) (XOut k e) N TS} {n : ℕ} {O : SideOracle S}
  {t : ℕ} [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.Msg] [DecidableEq TS.Msg]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Fintype TS.Sig] [DecidableEq TS.Sig]

variable [Fintype O.BMsg] [DecidableEq O.BMsg] [Fintype O.BSig] [DecidableEq O.BSig]

/-- **The adversary of the unforgeability game at the users' key coins**: its start input, the
users' public keys, with the empty table of `OracleView.queriesOnly`. -/
abbrev UnforgeAdversary.at (A : UnforgeAdversary S n O (OracleView.queriesOnly _ _) t)
    (keys : Fin n → S.KeyCoins) :
    QueryBoundedAdversary (Bits m) (XOut k e) (UnforgeRequest n O) (UnforgeResponse O)
      (KeyRing S.PK N × S.Msg × S.Sig) t :=
  A (fun i => S.pk (keys i), ())

variable [Fintype TS.SignCoins] [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]

/-- **The run of the unforgeability game at the users' key coins `keys` and the auxiliary value
`a`**: the adversary's algorithm at `a` composed with the challenger at `keys`, reading the output
and the answered requests (as `QueryBoundedAdversary.transcriptLaw` does). -/
noncomputable abbrev UnforgeAdversary.runAt (A : UnforgeAdversary S n O (OracleView.queriesOnly _ _) t)
    (Q : ℕ) (keys : Fin n → S.KeyCoins) (a : (A.at keys).Aux) :=
  ((A.at keys).alg a).toKindAlg.composeBothOut (unforgeChallenger S n O keys Q) fun v =>
    (((A.at keys).alg a).output _ v, ((A.at keys).alg a).history _ v)

variable [Nonempty TS.KeyCoins]

/-- **The forgery probability is an average of model runs** (the oracle uniform, read through
`outEquiv`): over the users' key coins and the adversary's auxiliary input, of the probability that
the run at the key coins terminates with an output on which the event `E` holds, for every event `E`
implied by a forgery at every oracle (`hE`). The adversary's start input does not read the oracle
(`OracleView.queriesOnly`), and its auxiliary input is drawn independently of the oracle, so the
oracle's draw moves inside. -/
theorem forgeProb_le_tsum_realLaw (A : UnforgeAdversary S n O (OracleView.queriesOnly _ _) t)
    (Q : ℕ) (E : (Fin n → S.KeyCoins) → (Bits m → Out k e) →
      (KeyRing S.PK N × S.Msg × S.Sig) × UnforgeHist n O → Prop)
    (hE : ∀ keys H y, Forges keys H y.1 y.2 → E keys (outEquiv k e ∘ H) y) :
    forgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → S.KeyCoins) keys *
      ∑' a, (A.at keys).aux a * ((A.runAt Q keys a).realLaw (outEquiv k e)).toOuterMeasure
        {p | ∃ y ∈ p.out, E keys p.oracle y} := by
  simp only [forgeProb, unforgeLaw, runLaw, OracleView.queriesOnly, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply, QueryBoundedAdversary.transcriptLaw, Alg.realLaw]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl ?_
  simp only [← ENNReal.tsum_mul_left]
  conv_lhs => rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun H => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl (mul_le_mul' le_rfl (PMF.toOuterMeasure_mono _ ?_))
  rintro o ⟨⟨y, hy, hf⟩, -⟩
  exact ⟨y, hy, hE keys H y hf⟩

end Decompose

/-! ### Proof systems given by a compiled verifier -/

/-- **A proof system whose verifier is the acceptance of a compiled verifier**: the claims of a
statement and a proof (`claim`, possibly none), whose statement is the statement (`stmt_eq`), and
on which the compiled verifier `V` accepts, against the oracle read through `outEquiv`, whenever the
proof system's verifier accepts (`accepted_of_verify`). The spBCS proof system of
`GordieHowe/Applications/Ring/SPBCSRing.lean` is one (`compiledBy_spbcsProofSystem`). -/
structure ProofSystem.CompiledBy {m k e : ℕ} {Stmt Wit Cl : Type}
    {TPS : PSTypes} (PS : ProofSystem (Bits m) (XOut k e) Stmt Wit TPS) (V : NARG.QROM.Verifier m k e Cl Stmt) where
  /-- The claim of a statement and a proof. -/
  claim : Stmt → PS.Proof → Option Cl
  /-- The claim's statement is the statement. -/
  stmt_eq : ∀ x π c, c ∈ claim x π → V.stmt c = x
  /-- An accepted proof has a claim that the compiled verifier accepts. -/
  accepted_of_verify : ∀ H x π, PS.verify H x π = true →
    ∃ c ∈ claim x π, V.Accepted (outEquiv k e ∘ H) c

/-! ### Ring-binding base messages -/

namespace BaseSigner

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.PK]
  [DecidableEq T.PK] [Fintype RMsg]
  [DecidableEq RMsg] [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins]
  [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins]
  [Nonempty T.Coins] (B : BaseSigner X Y N T RMsg)

end BaseSigner


/-! ### The relay of the ring game's requests to the multi-user game -/

section Relay

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N T RMsg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop} [DecidablePred adm]

variable [DecidableEq T.PK]

variable (B PS adm) in
/-- **A relay of the requests of the unforgeability game of `ofBase B PS adm`, with the side oracle
`O`, to the multi-user game with the signing oracle `SO`**: the message `SO` signs for a ring
signature on `(R, m)` (`ringMsg`) and for a side signature on `bm` (`sideMsg`). Corruptions are
relayed as corruptions. -/
structure MURelay (O : SideOracle (ofBase B PS adm)) (SO : Signature.SignOracle B.core) where
  /-- The message of a ring-signing request. -/
  ringMsg : KeyRing B.PK N → B.Msg → SO.SMsg
  /-- The message of a side-signing request. -/
  sideMsg : O.BMsg → SO.SMsg

namespace MURelay

variable {O : SideOracle (ofBase B PS adm)} {SO : Signature.SignOracle B.core} (r : MURelay B PS adm O SO)
  {n : ℕ}

/-- **The relayed request**: a corruption as a corruption, a ring-signing request by `s` as a signing
request by `s` on `ringMsg R m`, a side request by `i` as a signing request by `i` on `sideMsg bm`. -/
def request : UnforgeRequest n O → Signature.MURequest SO n
  | .corrupt i => .corrupt i
  | .sign s R m => .sign s (r.ringMsg R m)
  | .sideSign i bm => .sign i (r.sideMsg bm)

/-- **The relayed reply**: key coins as key coins; signatures are not relayed (`none`; the
existential winning condition reads only the requests). -/
def response : UnforgeResponse O → Option (Signature.MUResponse B.core)
  | .keyCoins kc => some (.keyCoins kc)
  | _ => none

/-- **The relayed history**: each answered request of the unforgeability game, relayed. -/
def hist (h : UnforgeHist n O) : Signature.MUHist SO n :=
  h.map fun x => ⟨r.request x.request, x.response.bind response⟩

/-- **A user corrupted in the relayed history was corrupted in the history.** -/
theorem corrupted_of_hist {h : UnforgeHist n O} {i : Fin n}
    (hc : Signature.Corrupted (r.hist h) i) : RingSignature.Corrupted h i := by
  obtain ⟨x, hx, hr⟩ := hc
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  refine ⟨y, hy, ?_⟩
  rcases hreq : y.request with j | ⟨s, R, m⟩ | ⟨j, bm⟩ <;>
    simp only [hreq, request, Signature.MURequest.corrupt.injEq, reduceCtorEq] at hr
  rw [hr]

/-- **A signing request of the relayed history is a relayed ring-signing or side request**: user
`j` asked to sign for `bm` in the relayed history was asked, in the history, for a ring signature on
some `(R, m)` with `SO.base (ringMsg R m) = bm`, or for a side signature on some `bm'` with
`SO.base (sideMsg bm') = bm`. -/
theorem signed_hist {h : UnforgeHist n O} {j : Fin n} {bm : B.BMsg}
    (hs : Signature.Signed (r.hist h) j bm) :
    (∃ x ∈ h, ∃ R m, x.request = .sign j R m ∧ SO.base (r.ringMsg R m) = bm) ∨
      ∃ x ∈ h, ∃ bm', x.request = .sideSign j bm' ∧ SO.base (r.sideMsg bm') = bm := by
  obtain ⟨x, hx, sm, hr, hb⟩ := hs
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rcases hreq : y.request with i | ⟨s, R, m⟩ | ⟨i, bm'⟩ <;>
    simp only [hreq, request, Signature.MURequest.sign.injEq, reduceCtorEq] at hr
  · obtain ⟨rfl, rfl⟩ := hr
    exact Or.inl ⟨y, hy, R, m, hreq, hb⟩
  · obtain ⟨rfl, rfl⟩ := hr
    exact Or.inr ⟨y, hy, bm', hreq, hb⟩

/-- **The relay keeps freshness**: for a fresh ring and message `(R, m)` of the unforgeability game,
no member of `R` was asked, in the relayed history, to sign for the base message `bmsg R m`. -/
def KeepsFresh : Prop :=
  ∀ (n : ℕ) (keys : Fin n → B.KeyCoins) (h : UnforgeHist n O) (R : KeyRing B.PK N) (m : B.Msg),
    Fresh (S := ofBase B PS adm) keys h R m → ∀ j, B.pk (keys j) ∈ R.1 →
      ¬ Signature.Signed (r.hist h) j (B.bmsg R m)

end MURelay

variable (B PS adm) in
/-- **The relay of BKM06 Definition 7 to MU-EUF-CMA^corr with the ring-aware signer**: a ring
signature on `(R, m)` is relayed as a signing request on `(R, m)` (`Signature.SignOracle.ring`);
there are no side requests. -/
def insiderRelay : MURelay B PS adm (SideOracle.none _) (Signature.SignOracle.ring B) where
  ringMsg R m := (R, m)
  sideMsg bm := bm.elim

variable (B PS adm) in
/-- **The relay of the joint-security game to MU-EUF-CMA^corr with both signers**: a ring signature on
`(R, m)` as a request `inl (R, m)`, an ordinary signature on `bm` as a request `inr bm`
(`Signature.SignOracle.ringStd`). -/
noncomputable def jointRelay :
    MURelay B PS adm (baseSide B PS adm) (Signature.SignOracle.ringStd B) where
  ringMsg R m := .inl (R, m)
  sideMsg bm := .inr bm

/-- **For a ring-binding base message the relay of BKM06 Definition 7 keeps freshness**: a member
asked for `bmsg R m` was asked for a ring signature on some `(R', m')` with the same base message,
hence on `(R, m)`, which freshness excludes. -/
theorem keepsFresh_insiderRelay (hbind : B.BindsRing) : (insiderRelay B PS adm).KeepsFresh := by
  intro n keys h R m hf j _ hs
  rcases (insiderRelay B PS adm).signed_hist hs with ⟨x, hx, R', m', hr, hb⟩ | ⟨x, hx, bm', -⟩
  · obtain ⟨rfl, rfl⟩ := hbind _ _ _ _ hb
    exact hf.not_signQueried ⟨x, hx, j, hr⟩
  · exact bm'.elim

/-- **For a ring-binding base message the relay of the joint-security game keeps freshness**: a member
asked for `bmsg R m` was asked for a ring signature with that base message, hence on `(R, m)`, or
for an ordinary signature on `bmsg R m`; freshness excludes both. -/
theorem keepsFresh_jointRelay (hbind : B.BindsRing) :
    (jointRelay B PS adm).KeepsFresh := by
  intro n keys h R m hf j hj hs
  rcases (jointRelay B PS adm).signed_hist hs with ⟨x, hx, R', m', hr, hb⟩ | ⟨x, hx, bm', hr, hb⟩
  · obtain ⟨rfl, rfl⟩ := hbind _ _ _ _ hb
    exact hf.not_signQueried ⟨x, hx, j, hr⟩
  · exact hf.not_sideCovered ⟨x, hx, j, bm', hr, hj, hb⟩

end Relay

/-! ### The extraction forger and the bound -/

section Forger

variable {m k e N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type} [DecidableEq T.PK]
  {B : BaseSigner (Bits m) (XOut k e) N T RMsg}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {O : SideOracle (ofBase B PS adm)} {n t : ℕ} {Cl : Type}
  {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}

/-- The output of the unforgeability game of `ofBase B PS adm` with the answered requests. -/
abbrev ForgeryReadout {T : Signature.SchemeTypes} {RMsg : Type} [DecidableEq T.PK]
    (B : BaseSigner (Bits m) (XOut k e) N T RMsg)
    {TPS : PSTypes} (PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS) (adm : KeyRing B.PK N → Prop)
    [DecidablePred adm] (O : SideOracle (ofBase B PS adm)) (n : ℕ) : Type :=
  (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) × UnforgeHist n O

/-- **The statement of a forgery** `(R, m, (y, π))`: `(R, m, y)`. -/
def stmtOf (y : ForgeryReadout B PS adm O n) : RingStmt B :=
  ⟨y.1.1, y.1.2.1, y.1.2.2.1⟩

/-- **The claim of a forgery** for the compiled verifier, `c₀` when the proof has none. -/
def claimOf (hC : PS.CompiledBy V) (c₀ : Cl) (y : ForgeryReadout B PS adm O n) : Cl :=
  (hC.claim (stmtOf y) y.1.2.2.2).getD c₀

/-- **The decoding of an extracted witness** `(i, σ)` for `(R, m, y)`: the key at position `i`,
the base message `bmsg R m` and `σ`; none if `i` is outside the ring. -/
def decodeWit (x : RingStmt B) (w : RingWit B) : Option (B.PK × B.BMsg × B.BSig) :=
  if h : w.idx < x.ring.1.length then some (x.ring.1[w.idx], B.bmsg x.ring x.msg, w.sig) else none

variable [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins]

variable [Fintype O.BMsg] [DecidableEq O.BMsg] [Fintype O.BSig] [DecidableEq O.BSig]

variable [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.Pub] [DecidableEq T.Pub]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [DecidableEq T.Coins] [Nonempty T.Coins]

/-- **The success probability of the extraction forger with the default claim `c₀`**: averaged over
the users' key coins and the adversary's auxiliary input, the probability that in the simulated
run (a compressed oracle) of the adversary composed with the challenger of the game at the key
coins, followed by the compiled verifier's queries on the forgery's claim, some witness that `ext`
returns from the measured database for the forgery's statement decodes to a candidate
`(pk, bm, σ)` that is a forgery of MU-EUF-CMA^corr with the signing oracle `SO`
(`Signature.Forges`) at every oracle, for the history relayed by `r`. -/
noncomputable def extractionSuccessAt {SO : Signature.SignOracle B.core} (r : MURelay B PS adm O SO)
    (A : UnforgeAdversary (ofBase B PS adm) n O (OracleView.queriesOnly _ _) t) (Q : ℕ)
    (hC : PS.CompiledBy V) (ext : RingStmt B → DB (Bits m) (Out k e) → Multiset (RingWit B))
    (c₀ : Cl) : ℝ≥0∞ :=
  ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
    ∑' a, (A.at keys).aux a *
      simProb (outEquiv k e) (SPBCS.QROM.extAdvVia V (claimOf hC c₀)
          (((A.at keys).alg a).toTPKindAlg.composeBothOut (unforgeChallenger _ n O keys Q) fun v =>
            (((A.at keys).alg a).output _ v, ((A.at keys).alg a).history _ v)))
        fun y D => ∃ w ∈ ext (stmtOf y) D, ∃ f ∈ decodeWit (stmtOf y) w,
          ∀ H, Signature.Forges keys H f (r.hist y.2)

/-- **The success probability of the extraction forger** (`extractionSuccessAt` at a default
claim when the claims are inhabited; `0` otherwise, when no proof is accepted). -/
noncomputable def extractionSuccess {SO : Signature.SignOracle B.core} (r : MURelay B PS adm O SO)
    (A : UnforgeAdversary (ofBase B PS adm) n O (OracleView.queriesOnly _ _) t) (Q : ℕ)
    (hC : PS.CompiledBy V) (ext : RingStmt B → DB (Bits m) (Out k e) → Multiset (RingWit B)) :
    ℝ≥0∞ :=
  open Classical in if h : Nonempty Cl then extractionSuccessAt r A Q hC ext (Classical.choice h) else 0

variable [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig]

variable {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → Multiset (RingWit B)} {β : ℕ → ℝ≥0∞}

omit [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] in
/-- **A forgery passing a test is extracted, except with the knowledge error**, in the
unforgeability game of `ofBase B PS adm` with any side oracle: for a proof system given by a
compiled verifier `V` (`hC`) with a knowledge bound for `rel` at `ext` and `β` (`K`), and a test `P`
of the key coins and the output that every forgery passes (`hP`), the forgery probability is at
most the probability, averaged over the key coins and the auxiliary input, that in the simulated
run the output passes `P` and `ext` returns a witness in `rel` for its statement, plus the knowledge
error at `t + Q · q + kq` queries (`q` the challenger's per-reply bound). -/
theorem forgeProb_le_extractProb (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel ext β) (c₀ : Cl)
    (A : UnforgeAdversary (ofBase B PS adm) n O (OracleView.queriesOnly _ _) t) (Q : ℕ)
    (P : (Fin n → B.KeyCoins) → ForgeryReadout B PS adm O n → Prop)
    (hP : ∀ keys H y, Forges keys H y.1 y.2 → P keys y) :
    forgeProb A Q ≤ (∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' a, (A.at keys).aux a *
        simProb (outEquiv k e) (SPBCS.QROM.extAdvVia V (claimOf hC c₀)
            (((A.at keys).alg a).toTPKindAlg.composeBothOut (unforgeChallenger _ n O keys Q)
              fun v => (((A.at keys).alg a).output _ v, ((A.at keys).alg a).history _ v)))
          fun y D => P keys y ∧ NARG.ExtractsAt rel ext (stmtOf y) D) +
      V.knowledgeError β (t + Q * max (ofBase B PS adm).q O.q + V.kq) := by
  classical
  have hE : ∀ keys H y, Forges keys H y.1 y.2 → V.Accepted (outEquiv k e ∘ H) (claimOf hC c₀ y) ∧
      (P keys y ∧ V.stmt (claimOf hC c₀ y) = stmtOf y) := by
    intro keys H y hf
    obtain ⟨c, hc, hacc⟩ := hC.accepted_of_verify H (stmtOf y) y.1.2.2.2 hf.verify_eq
    have hcl : claimOf hC c₀ y = c := by simp [claimOf, Option.mem_def.1 hc]
    exact ⟨hcl ▸ hacc, hP keys H y hf, hcl ▸ hC.stmt_eq _ _ _ hc⟩
  have hstep : ∀ keys a, ((A.runAt Q keys a).realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ y ∈ p.out, V.Accepted p.oracle (claimOf hC c₀ y) ∧
        (P keys y ∧ V.stmt (claimOf hC c₀ y) = stmtOf y)} ≤
      simProb (outEquiv k e) (SPBCS.QROM.extAdvVia V (claimOf hC c₀)
          (((A.at keys).alg a).toTPKindAlg.composeBothOut (unforgeChallenger _ n O keys Q)
            fun v => (((A.at keys).alg a).output _ v, ((A.at keys).alg a).history _ v)))
        (fun y D => P keys y ∧ NARG.ExtractsAt rel ext (stmtOf y) D) +
      V.knowledgeError β (t + Q * max (ofBase B PS adm).q O.q + V.kq) := by
    intro keys a
    refine (Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound K ((A.at keys).alg a)
      (unforgeChallenger _ n O keys Q)
      (fun v => (((A.at keys).alg a).output _ v, ((A.at keys).alg a).history _ v))
      (claimOf hC c₀) (fun y => P keys y ∧ V.stmt (claimOf hC c₀ y) = stmtOf y)
      ((A.at keys).queries_le a)).trans (add_le_add (simProb_mono _ _ ?_) le_rfl)
    rintro y D ⟨⟨hp, hs⟩, hx⟩
    rw [hs] at hx
    exact ⟨hp, hx⟩
  refine (forgeProb_le_tsum_realLaw A Q (fun keys h y => V.Accepted h (claimOf hC c₀ y) ∧
    (P keys y ∧ V.stmt (claimOf hC c₀ y) = stmtOf y)) hE).trans ?_
  refine (ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl
    (PMF.tsum_mul_le_tsum_mul_add _ (hstep keys))).trans ?_
  exact PMF.tsum_mul_le_tsum_mul_add _ fun _ => le_rfl

omit [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] in
/-- **Unforgeability of `ofBase B PS adm` from knowledge soundness and the multi-user game**, with
any side oracle `O` whose requests a relay `r` to the multi-user game with the signing oracle `SO`
passes on keeping freshness (`hr`): for a proof system given by a compiled verifier `V` (`hC`) with a
knowledge bound for a relation `rel` at the extractor `ext` and the database bound `β` (`K`, CMS19
Proposition 8.12 and Lemmas 5.9–5.10), every witness of `rel` being one of the ring relation at
every oracle (`hrel`), the forgery probability of an adversary with at most `t` queries and `Q`
requests is at most the success probability of the extraction forger (`extractionSuccess`), plus the
knowledge error at `t + Q · q + kq` queries. -/
theorem forgeProb_le_of_knowledgeBound {SO : Signature.SignOracle B.core} (r : MURelay B PS adm O SO)
    (hr : r.KeepsFresh) (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel ext β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w)
    (A : UnforgeAdversary (ofBase B PS adm) n O (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    forgeProb A Q ≤ extractionSuccess r A Q hC ext +
      V.knowledgeError β (t + Q * max (ofBase B PS adm).q O.q + V.kq) := by
  by_cases hCl : Nonempty Cl
  · rw [extractionSuccess, dite_eq_left_of_eq_true (eq_true hCl)]
    refine (forgeProb_le_extractProb hC K (Classical.choice hCl) A Q
      (fun keys y => Fresh keys y.2 y.1.1 y.1.2.1) fun _ _ _ hf => hf.fresh).trans
      (add_le_add ?_ le_rfl)
    refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl
      (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (simProb_mono _ _ ?_))
    rintro y D ⟨hf, w, hw, hrw⟩
    have hR := hrel _ _ hrw
    have hi : w.idx < (stmtOf y).ring.1.length := (hR 0).idx_lt
    refine ⟨w, hw, _, by rw [decodeWit, dite_eq_left_of_eq_true (eq_true hi)]; rfl, fun H => ⟨(hR H).verify_eq, ?_⟩⟩
    obtain ⟨j, hj, hc⟩ := hf.honest_ring _ (List.getElem_mem hi)
    have hmem : B.pk (keys j) ∈ y.1.1.1 := by
      rw [show B.pk (keys j) = _ from hj]
      exact List.getElem_mem hi
    exact ⟨j, hj, fun h => hc (r.corrupted_of_hist h), hr n keys y.2 _ _ hf j hmem⟩
  · rw [extractionSuccess, dite_eq_right_of_eq_false (eq_false hCl), zero_add]
    unfold forgeProb
    refine le_trans (le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
      (Set.disjoint_left.2 fun x _ hx => ?_))) zero_le
    obtain ⟨p, -, hf⟩ := hx
    obtain ⟨c, -, -⟩ := hC.accepted_of_verify _ _ _ hf.verify_eq
    exact hCl ⟨c⟩

omit [Fintype T.BMsg] [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of `ofBase B PS adm`
for a ring-binding base message**, by knowledge soundness: for a base message that binds the ring
(`hbind`), a proof system given by a compiled verifier `V` (`hC`) with a knowledge bound for `rel`
at `ext` and `β` (`K`), every witness of `rel` one of the ring relation at every oracle (`hrel`),
the forgery probability of an adversary of BKM06 Definition 7 (start input the honest public keys,
the oracle by at most `t` queries, `Q` requests) is at most the success probability of the
extraction forger in MU-EUF-CMA^corr with the ring-aware signing oracle (`extractionSuccess` of
`insiderRelay`) plus the knowledge error at `t + Q · q + kq` queries, `q` the ring signer's query
bound. -/
theorem insiderForgeProb_le_of_knowledgeBound (hbind : B.BindsRing) (hC : PS.CompiledBy V)
    (K : V.KnowledgeBound rel ext β) (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤ extractionSuccess (insiderRelay B PS adm) A Q hC ext +
      V.knowledgeError β (t + Q * (ofBase B PS adm).q + V.kq) := by
  have h := forgeProb_le_of_knowledgeBound (insiderRelay B PS adm)
    (keepsFresh_insiderRelay hbind) hC K hrel A Q
  rwa [show max (ofBase B PS adm).q (SideOracle.none (ofBase B PS adm)).q = (ofBase B PS adm).q
    from Nat.max_zero _] at h

/-- **Joint-security unforgeability of `ofBase B PS adm` for a ring-binding base message**, by
knowledge soundness: the bound of `insiderForgeProb_le_of_knowledgeBound` for the joint-security game
(the base scheme's ordinary signer as a side oracle), the extraction forger now in MU-EUF-CMA^corr
with both the ring-aware and the ordinary signing oracle (`jointRelay`,
`Signature.SignOracle.ringStd`). -/
theorem jointForgeProb_le_of_knowledgeBound (hbind : B.BindsRing) (hC : PS.CompiledBy V)
    (K : V.KnowledgeBound rel ext β) (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w)
    (A : JointAdversary B PS adm n (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    jointForgeProb A Q ≤ extractionSuccess (jointRelay B PS adm) A Q hC ext +
      V.knowledgeError β (t + Q * (ofBase B PS adm).q + V.kq) := by
  have h := forgeProb_le_of_knowledgeBound (jointRelay B PS adm)
    (keepsFresh_jointRelay hbind) hC K hrel A Q
  rwa [show max (ofBase B PS adm).q (baseSide B PS adm).q = (ofBase B PS adm).q
    from max_eq_left (Nat.le_add_right B.q _)] at h

end Forger


/-! ### The spBCS proof system -/

section SPBCS

open SPTerm GordieHowe.Ring

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

/-- **The spBCS proof system is given by its compiled verifier** `M.qVerifier Qs b b`, with the
claims `spbcsClaim`. -/
def compiledBy_spbcsProofSystem :
    (spbcsProofSystem M Λ E hb honest).CompiledBy (M.qVerifier Qs b b) where
  claim := spbcsClaim M
  stmt_eq _ _ _ hc := stmt_of_mem_spbcsClaim M hc
  accepted_of_verify H x π h := (verify_spbcsProofSystem_eq_true_iff M Λ E hb honest H x π).1 h

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BMsg]
  [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub]
  [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins]
  [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

variable {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ}
  {rel : Set (RingStmt B × RingWit B)} {Ext : CausalExtractor P τ (RingStmt B) (RingWit B)}
  {St : CausalStateFn P τ (RingStmt B)} {ε : ChIdx P τ → ℝ≥0}


end SPBCS

end RingSignature

end GordieHowe
