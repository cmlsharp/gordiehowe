-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.SPBCS.Extraction.OnlineExtractTest
public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Model.Quantum.Interactive.Output
public import GordieHowe.Model.QROM.AdaptiveCount
public import GordieHowe.Model.Quantum.Interactive.QueryBounded

@[expose] public section

/-!
# Unforgeability games of the ring signature, and the multi-user signature game

The games are stated in the interactive quantum model with run-time kinds (`Quantum.AdaptiveIAlg`,
`GordieHowe/Model/Quantum/Interactive/Adaptive.lean`): quantum queries to the random oracle, classical requests
to a classical challenger, the kind of each slot chosen by the adversary's workspace. The model's
composition with the challenger is `KindAlg.composeBothOut` of `AdaptiveIAlg.toKindAlg`; the
forger's simulated run uses the trace-preserving form `AdaptiveIAlg.toTPKindAlg`, which runs alike
on the branches that have not ended (`GordieHowe/Model/Quantum/Interactive/AdaptiveTP.lean`).

## The oracles of the multi-user game, through a classical layer

`OracleLayer`: a classical layer over the oracles of the multi-user signature game with
corruption (`BaseRequest`, `baseAnswer`): on each request of its own interface it runs a
classical program that queries those oracles adaptively and then returns an oracle program over
the random oracle computing the reply. `OracleLayer.challenger L Q` is the challenger of the
game played through the layer: the `n` users' key-generation coins uniform, and for each of the
first `Q` requests a uniform public value and signing coins for the base signing oracle and coins
of the layer. The base calls of the answered requests (`OracleLayer.calls`) define the records:
`Signed i m` (user `i` was asked to sign `m`) and `Corrupted i`. A layer only sees the answers of
the base oracles; it never reads the keys.

## The multi-user game with extraction forgers

`ExtractionForger`: a forger of the multi-user signature game with adaptive corruption
(MU-EUF-CMA^corr, Bader, Hofheinz, Jager, Kiltz, Li, TCC 2015, ePrint 2014/797, Definition 2,
p. 6), of the following form: it runs an interactive quantum algorithm against a classical layer
over the base oracles, simulates the random oracle with a compressed oracle, measures the
database, and applies the straight-line extractor `E` and a decoding to the statement the
algorithm outputs. `ExtractionForger.success`: the probability that some decoded candidate
`(pk, m, σ)` is a forgery: `σ` verifies on `m` under `pk`, and `pk` is the key of a user who was
neither corrupted nor asked to sign `m`. The forger identifies the user by public key; with
distinct honest keys this is the index form of Bader et al.

## The ring games

- `RingRequest`, `RingResponse`, `ringLayer`: the requests of the ring games: the base requests
  (public key, ordinary signature, corruption) and a ring-signing request `(s, R, m)`, answered by
  asking user `s`'s public key and, if it is in `R`, a base signature by `s` on `bind R m`, and
  proving the ring relation with a compiled honest prover program `Pv` (`GordieHowe.NARG.Prover`;
  for spBCS, `GordieHowe.SPBCS.niProver` run through `queryEncoding`).
- The games are generic in the compiled argument: its verifier `V : QVerifier` (acceptance, query
  expansion, statement of a claim) and its honest prover program `Pv`.
- `RingAdversary`: an interactive adversary with auxiliary input, at most `Q` requests and `t`
  queries of its own, outputting a ring statement and a proof.
- `ConvertedWins`: the forgery verifies; every key of its ring is the key of an uncorrupted honest
  user; no user whose key is in the ring was asked to sign the base message `bind R* m*`
  (ordinarily or inside a ring-signing request). With `bind R m = m` (converted signatures) this
  is: a valid ring signature on `(R*, m*)` implies that some member of `R*` signed `m*`.
- `BKMWins`: BKM06 Definition 7 (unforgeability with respect to insider corruption, TCC 2006,
  LNCS p. 67): the forgery verifies, its ring consists of uncorrupted honest keys, no
  ring-signing request on `(R*, m*)` was answered; and no ordinary signing request by a member
  on `bind R* m*` was answered (BKM06 has no ordinary signing oracle, so this condition is
  vacuous for its adversaries).
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {Sch : SigScheme} {n : ℕ}

/-! ### Classical layers over the base oracles -/

/-- **A classical layer over the oracles of the multi-user signature game**, with requests in `Req`
and replies in `Option Resp`, and oracle programs over the random oracle `X → Y`: on a request and
its coins (drawn from `coins`), a classical program that queries the base oracles (`BaseRequest`)
adaptively and returns an oracle program over the random oracle making at most `q` queries, whose
result is the reply. -/
structure OracleLayer (Sch : SigScheme) (n : ℕ) (X Y Req Resp : Type) where
  /-- The coins of the layer for one request. -/
  Coins : Type
  [instFintypeCoins : Fintype Coins]
  [instDecEqCoins : DecidableEq Coins]
  /-- Their distribution. -/
  coins : PMF Coins
  /-- The base calls, then the oracle program computing the reply. -/
  prog : Req → Coins →
    OracleProg (BaseRequest Sch n) (BaseResponse Sch) (OracleProg X Y (Option Resp))
  /-- The bound on the random-oracle queries of one reply. -/
  q : ℕ
  prog_queries : ∀ req c (O : BaseRequest Sch n → BaseResponse Sch) H,
    (((prog req c).run O).trace H).length ≤ q

attribute [instance] OracleLayer.instFintypeCoins OracleLayer.instDecEqCoins

namespace OracleLayer

variable {X Y Req Resp : Type} (L : OracleLayer Sch n X Y Req Resp) (Q : ℕ)

/-- **The draws of the game through a layer**: the `n` users' key-generation coins, and for each
of the first `Q` requests a public value and signing coins for the base signing oracle and the
layer's coins. -/
abbrev Draw : Type :=
  (Fin n → Sch.KeyCoins) × (Fin Q → (Sch.Pub × Sch.SignCoins) × L.Coins)

/-- The draws of one request: a uniform public value and signing coins, and the layer's coins. -/
noncomputable def requestLaw : PMF ((Sch.Pub × Sch.SignCoins) × L.Coins) :=
  (PMF.uniformOfFintype (Sch.Pub × Sch.SignCoins)).bind fun s => L.coins.map fun c => (s, c)

/-- The law of the draws: uniform key-generation coins, and independent draws per request. -/
noncomputable def drawLaw : PMF (L.Draw Q) :=
  (PMF.uniformOfFintype (Fin n → Sch.KeyCoins)).bind fun keys =>
    (PMF.pi fun _ : Fin Q => L.requestLaw).map fun r => (keys, r)

/-- The base oracles answering request number `c < Q` (`baseAnswer` at that request's signing
draw). -/
def oracleAt (ω : L.Draw Q) (c : Fin Q) : BaseRequest Sch n → BaseResponse Sch :=
  baseAnswer ω.1 (ω.2 c).1.1 (ω.2 c).1.2

/-- **The base calls of request number `c`** with the request `req`: the trace of the layer's
base program against the base oracles of that request; none for `c ≥ Q`. -/
def callsAt (ω : L.Draw Q) (req : Req) (c : ℕ) : List (BaseRequest Sch n) :=
  if h : c < Q then (L.prog req (ω.2 ⟨c, h⟩).2).trace (L.oracleAt Q ω ⟨c, h⟩) else []

/-- **The base calls of a list of requests**, numbered in order. -/
def calls (ω : L.Draw Q) (reqs : List Req) : List (BaseRequest Sch n) :=
  reqs.zipIdx.flatMap fun p => L.callsAt Q ω p.1 p.2

/-- **User `i` was asked to sign `m`** by one of the requests `reqs`. -/
def Signed (ω : L.Draw Q) (reqs : List Req) (i : Fin n) (m : Sch.Msg) : Prop :=
  BaseRequest.sign i m ∈ L.calls Q ω reqs

/-- **User `i` was corrupted** by one of the requests `reqs`. -/
def Corrupted (ω : L.Draw Q) (reqs : List Req) (i : Fin n) : Prop :=
  BaseRequest.corrupt i ∈ L.calls Q ω reqs

variable [Fintype X] [DecidableEq X] [Fintype Y]

/-- **The challenger of the game through a layer** answering `Q` requests: request number
`c < Q` runs the layer's base program against the base oracles of the draw of request `c`, then
the resulting program over the oracle in force; it assigns nothing. Later requests are answered by
`none`. -/
noncomputable def challenger : Challenger X Y Req Resp where
  Coins := L.Draw Q
  coins := L.drawLaw Q
  Q := Q
  q := L.q
  respond ω hist req :=
    if h : hist.length < Q then
      ((L.prog req (ω.2 ⟨hist.length, h⟩).2).run (L.oracleAt Q ω ⟨hist.length, h⟩)).bind
        fun r => .pure ⟨r, []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist req H := by
    split_ifs
    · simpa using L.prog_queries req _ _ H
    · simp

end OracleLayer

/-! ### The multi-user game against extraction forgers -/

/-- **A forgery of the multi-user game** for the candidate `(pk, m, σ)`, at the users' coins
`keys`, with the predicates `corrupted` and `signed` of the users: `σ` verifies on `m` under
`pk`, and `pk` is the key of a user neither corrupted nor asked to sign `m`. -/
structure BaseForgery (keys : Fin n → Sch.KeyCoins) (corrupted : Fin n → Prop)
    (signed : Fin n → Sch.Msg → Prop) (f : Sch.PK × Sch.Msg × Sch.Sig) : Prop where
  /-- The signature verifies. -/
  verify_eq : Sch.verify f.1 f.2.1 f.2.2 = true
  /-- The key is that of an uncorrupted user who did not sign the message. -/
  exists_user : ∃ i, Sch.pk (keys i) = f.1 ∧ ¬ corrupted i ∧ ¬ signed i f.2.1

section Forger

variable {m k e : ℕ} {Stmt Pf : Type}

/-- **A forger of the multi-user game with adaptive corruption that extracts** (the game is
MU-EUF-CMA^corr of Bader, Hofheinz, Jager, Kiltz, Li, TCC 2015, ePrint 2014/797, Definition 2, p. 6,
with the forger identifying the user by public key): auxiliary input, an interactive quantum
algorithm against a classical layer `layer` over the base oracles (the layer answers `Q` requests),
then, in the simulated run with a compressed oracle, the straight-line database extractor
`extractor` at the statement the algorithm outputs, and the decoding of the extracted witnesses into
candidates. The verifier `V` fixes the oracle and the claims. -/
structure ExtractionForger (_V : NARG.QROM.Verifier m k e (Claim Stmt Pf) Stmt) (Sch : SigScheme) (n : ℕ)
    (Wit : Type) where
  /-- The requests of the layer's interface. -/
  Req : Type
  /-- The replies of the layer's interface. -/
  Resp : Type
  [instFintypeReq : Fintype Req]
  [instDecEqReq : DecidableEq Req]
  [instFintypeResp : Fintype Resp]
  [instDecEqResp : DecidableEq Resp]
  /-- The layer over the base oracles. -/
  layer : OracleLayer Sch n (Bits m) (XOut k e) Req Resp
  /-- The number of requests the layer answers. -/
  Q : ℕ
  /-- The values of the auxiliary input. -/
  Aux : Type
  /-- The distribution of the auxiliary input. -/
  aux : PMF Aux
  /-- The interactive algorithm on each value. -/
  alg : Aux → AdaptiveIAlg (Bits m) (XOut k e) Req Resp (Claim Stmt Pf)
  /-- The straight-line database extractor. -/
  extractor : Stmt → DB (Bits m) (Out k e) → Multiset Wit
  /-- The decoding of a statement and an extracted witness into a candidate forgery. -/
  decode : Stmt → Wit → Option (Sch.PK × Sch.Msg × Sch.Sig)

attribute [instance] ExtractionForger.instFintypeReq ExtractionForger.instDecEqReq
  ExtractionForger.instFintypeResp ExtractionForger.instDecEqResp

namespace ExtractionForger

variable {V : NARG.QROM.Verifier m k e (Claim Stmt Pf) Stmt} {Wit : Type} (F : ExtractionForger V Sch n Wit)

/-- The composed registers of the forger's algorithm at `a` with the layer's challenger. -/
abbrev Register (a : F.Aux) : Type :=
  (F.alg a).toTPKindAlg.CW (F.layer.challenger F.Q)

/-- The claim the algorithm outputs, read from the composed registers. -/
noncomputable def claim (a : F.Aux) (v : F.Register a) : Claim Stmt Pf :=
  (F.alg a).out v.adv.workspace.1

/-- The requests answered in the run, read from the composed registers. -/
noncomputable def answered (a : F.Aux) (v : F.Register a) : List F.Req :=
  ((F.alg a).toTPKindAlg.stateAt (F.layer.challenger F.Q) v.chal
    (F.alg a).toTPKindAlg.slots).history.map HistoryEntry.request

/-- **The forger wins on the composed registers `v` and the database `D`**: some witness the
extractor returns from `D` for the output statement decodes to a forgery, for the users' coins
and the records of the answered requests in `v`. -/
def Wins (a : F.Aux) (v : F.Register a) (D : DB (Bits m) (Out k e)) : Prop :=
  ∃ w ∈ F.extractor (F.claim a v).stmt D,
    ∃ f ∈ F.decode (F.claim a v).stmt w,
    BaseForgery v.chal.coins.1 (F.layer.Corrupted F.Q v.chal.coins (F.answered a v))
      (F.layer.Signed F.Q v.chal.coins (F.answered a v)) f

/-- **The success probability of the forger** in the multi-user game with adaptive corruption:
averaged over the auxiliary input, the probability that in the simulated run of its algorithm
against the layer's challenger, expanded by the verifier's queries on the output claim
(`GordieHowe.SPBCS.QROM.extAdvVia`, of the composition of the trace-preserving form), the measured
registers and database give a forgery (`Wins`). The users' keys enter only through the base
oracles of the layer and the winning condition. -/
noncomputable def success : ℝ≥0∞ :=
  ∑' a, F.aux a * simProb (outEquiv k e)
    (SPBCS.QROM.extAdvVia V (F.claim a)
      ((F.alg a).toTPKindAlg.composeBothOut (F.layer.challenger F.Q) id))
    (fun v D => F.Wins a v D)

end ExtractionForger

end Forger

/-! ### The ring layer -/

variable (Sch n)

/-- **A request of the ring games**: a request to the base oracles (public key, ordinary
signature, corruption), or a ring signature by user `s` on the ring message `m` for the ring
`R` of at most `N` keys (BKM06 Definition 7, `OSign(s, M, R)`). -/
inductive RingRequest (N : ℕ) (RMsg : Type) where
  /-- A base request. -/
  | base (r : BaseRequest Sch n)
  /-- A ring signature by user `s` on `m` for the ring `R`. -/
  | ringSign (s : Fin n) (R : RingOf Sch.PK N) (m : RMsg)
deriving DecidableEq

/-- **A reply of the ring games**: a base answer or a ring signature. -/
inductive RingResponse (P : Type) where
  /-- A base answer. -/
  | base (r : BaseResponse Sch)
  /-- A ring signature. -/
  | ringSignature (π : P)
deriving DecidableEq

variable {Sch n}

/-- Ring requests as a sum type. -/
def RingRequest.equivSum (N : ℕ) (RMsg : Type) :
    RingRequest Sch n N RMsg ≃ BaseRequest Sch n ⊕ (Fin n × RingOf Sch.PK N × RMsg) where
  toFun
    | .base r => .inl r
    | .ringSign s R m => .inr (s, R, m)
  invFun
    | .inl r => .base r
    | .inr p => .ringSign p.1 p.2.1 p.2.2
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with _ | ⟨_, _, _⟩ <;> rfl

noncomputable instance (N : ℕ) (RMsg : Type) [Fintype RMsg] : Fintype (RingRequest Sch n N RMsg) :=
  Fintype.ofEquiv _ (RingRequest.equivSum N RMsg).symm

/-- Ring replies as a sum type. -/
def RingResponse.equivSum (P : Type) : RingResponse Sch P ≃ BaseResponse Sch ⊕ P where
  toFun
    | .base r => .inl r
    | .ringSignature π => .inr π
  invFun
    | .inl r => .base r
    | .inr π => .ringSignature π
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with _ | _ <;> rfl

noncomputable instance (P : Type) [Fintype P] : Fintype (RingResponse Sch P) :=
  Fintype.ofEquiv _ (RingResponse.equivSum P).symm

variable {RMsg : Type} {N : ℕ} {m k e : ℕ} {Resp Coins : Type} [Fintype Coins]

/-- **The ring-signing step after the signer's public key `pk`**: if `pk` is in the ring, at its
first position `p`, ask a base signature by `s` on `bind R mg` and prove the ring relation for
`(R, mg, pub σ)` with the witness `(p, σ)` by the compiled honest prover program `Pv`; otherwise
reply `none`. -/
noncomputable def ringSignAfterKey
    (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
    (bind : List Sch.PK → RMsg → Sch.Msg) (s : Fin n) (ring : RingOf Sch.PK N) (mg : RMsg)
    (c : Coins) (pk : Sch.PK) :
    OracleProg (BaseRequest Sch n) (BaseResponse Sch)
      (OracleProg (Bits m) (XOut k e) (Option (RingResponse Sch Resp))) :=
  if ring.1.idxOf pk < ring.1.length then
    .query (.sign s (bind ring.1 mg)) fun
      | .signature σ => .pure ((Pv.prog ⟨ring, mg, Sch.pub σ⟩
          ⟨ring.1.idxOf pk, σ⟩ c).bind fun π => .pure (some (.ringSignature π)))
      | _ => .pure (.pure none)
  else .pure (.pure none)

/-- **The ring layer** (the challenger of the ring games through `OracleLayer.challenger`): a
base request is forwarded and its answer returned; a ring-signing request `(s, R, mg)` asks user
`s`'s public key, then continues with `ringSignAfterKey`. The layer's coins are those of the
compiled honest prover program `Pv`. -/
noncomputable def ringLayer
    (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
    (bind : List Sch.PK → RMsg → Sch.Msg) :
    OracleLayer Sch n (Bits m) (XOut k e) (RingRequest Sch n N RMsg) (RingResponse Sch Resp) where
  Coins := Coins
  instDecEqCoins := Classical.decEq _
  coins := Pv.coins
  prog
    | .base r, _ => .query r fun a => .pure (.pure (some (.base a)))
    | .ringSign s ring mg, c => .query (.publicKey s) fun
        | .publicKey pk => ringSignAfterKey Pv bind s ring mg c pk
        | _ => .pure (.pure none)
  q := Pv.q
  prog_queries req c O H := by
    rcases req with r | ⟨s, ring, mg⟩
    · simp
    · simp only [OracleProg.run_query]
      rcases O (.publicKey s) with pk | σ | kc
      · simp only [ringSignAfterKey]
        split_ifs
        · simp only [OracleProg.run_query]
          rcases O (.sign s (bind ring.1 mg)) with pk' | σ | kc
          · simp
          · simp only [OracleProg.run_pure, OracleProg.trace_bind, OracleProg.trace_pure,
              List.append_nil]
            exact Pv.prog_queries _ _ _ H
          · simp
        · simp
      · simp
      · simp

/-! ### The ring adversaries and their wins -/

variable [Fintype RMsg] [DecidableEq RMsg]

/-- **An adversary of the ring unforgeability games** with `n` honest users, rings of at most
`N` keys, `Q` answered requests and at most `t` queries of its own: a query-bounded adversary
(`Quantum.QueryBoundedAdversary`, the paper's `(t, Q)`-adversary: auxiliary input drawn
independently of the oracle, the kind of each slot chosen at run time, channels between calls, at
most `t` queries on every branch over its query slots and its post phase) with ring requests and
replies (the ring signatures `Resp` of the compiled argument whose verifier is `_V`), outputting a
ring statement and a proof. The ring challenger answers the first `Q` requests. -/
abbrev RingAdversary {Pf : Type}
    (_V : NARG.QROM.Verifier m k e (Claim (RingStmt Sch RMsg N) Pf) (RingStmt Sch RMsg N)) (Resp : Type)
    [Fintype Resp] [DecidableEq Resp] (n t _Q : ℕ) : Type 1 :=
  QueryBoundedAdversary (Bits m) (XOut k e) (RingRequest Sch n N RMsg)
    (RingResponse Sch Resp) (Claim (RingStmt Sch RMsg N) Pf) t

variable {Pf : Type} {V : NARG.QROM.Verifier m k e (Claim (RingStmt Sch RMsg N) Pf) (RingStmt Sch RMsg N)}
  [Fintype Resp] [DecidableEq Resp]
  (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
  (bind : List Sch.PK → RMsg → Sch.Msg)
  {t Q : ℕ} (A : RingAdversary V Resp n t Q)

namespace RingAdversary

/-- The challenger of the ring games answering `Q` requests: the ring layer over the base
oracles. -/
noncomputable abbrev challenger : Challenger (Bits m) (XOut k e) (RingRequest Sch n N RMsg)
    (RingResponse Sch Resp) :=
  (ringLayer Pv bind).challenger Q

/-- The composed registers of the adversary at `a` with the ring challenger. -/
abbrev Register (a : A.Aux) : Type := (A.alg a).toTPKindAlg.CW (challenger Pv bind (Q := Q))

/-- The claim the adversary outputs, read from the composed registers. -/
noncomputable def claim (a : A.Aux) (v : A.Register Pv bind a) :
    Claim (RingStmt Sch RMsg N) Pf :=
  (A.alg a).out v.adv.workspace.1

/-- The requests answered in the run (the first `Q` requests), in order. -/
noncomputable def answered (a : A.Aux) (v : A.Register Pv bind a) :
    List (RingRequest Sch n N RMsg) :=
  ((A.alg a).toTPKindAlg.stateAt (challenger Pv bind (Q := Q)) v.chal
    (A.alg a).toTPKindAlg.slots).history.map
    HistoryEntry.request

/-- **The ring of the forgery consists of uncorrupted honest keys, and no member was asked to
sign its base message** (`ConvertedWins` without the verification): every key of the ring is the
key of an uncorrupted user, and no user whose key is in the ring was asked, ordinarily or in a
ring-signing request, to sign `bind R* m*`. -/
structure ConvertedFresh (a : A.Aux) (v : A.Register Pv bind a) : Prop where
  /-- Every key of the ring is the key of an uncorrupted user. -/
  honest_ring : ∀ pk ∈ (A.claim Pv bind a v).stmt.ring.1, ∃ i,
    Sch.pk (v.chal.coins.1 i) = pk ∧
      ¬ (ringLayer Pv bind).Corrupted Q v.chal.coins (A.answered Pv bind a v) i
  /-- No member was asked to sign the base message of the forgery. -/
  unsigned : ∀ i, Sch.pk (v.chal.coins.1 i) ∈ (A.claim Pv bind a v).stmt.ring.1 →
    ¬ (ringLayer Pv bind).Signed Q v.chal.coins (A.answered Pv bind a v) i
      (bind (A.claim Pv bind a v).stmt.ring.1 (A.claim Pv bind a v).stmt.msg)

/-- **The adversary wins the converted-signature game** on the composed registers `v` with the
oracle read as `h`: the compiled verifier accepts its claim, and the claim is fresh
(`ConvertedFresh`). -/
def ConvertedWins (a : A.Aux) (v : A.Register Pv bind a)
    (h : Bits m → Out k e) : Prop :=
  V.Accepted h (A.claim Pv bind a v) ∧ A.ConvertedFresh Pv bind a v

/-- **The probability that the adversary wins the converted-signature game**: averaged over its
auxiliary input, the oracle uniform, the probability that the composition with the ring
challenger terminates with registers on which it wins (`ConvertedWins`). -/
noncomputable def convertedWinProb : ℝ≥0∞ :=
  ∑' a, A.aux a * (((A.alg a).toKindAlg.composeBothOut (challenger Pv bind (Q := Q)) id).realLaw
    (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out, A.ConvertedWins Pv bind a v p.oracle}

/-- **The forgery is fresh in the sense of BKM06 Definition 7** (`BKMWins` without the
verification): every key of the ring is the key of an uncorrupted user; no answered ring-signing
request was for the forgery's ring and message; and no answered ordinary signing request was by a
member on the forgery's base message. -/
structure BKMFresh (a : A.Aux) (v : A.Register Pv bind a) : Prop where
  /-- Every key of the ring is the key of an uncorrupted user. -/
  honest_ring : ∀ pk ∈ (A.claim Pv bind a v).stmt.ring.1, ∃ i,
    Sch.pk (v.chal.coins.1 i) = pk ∧
      ¬ (ringLayer Pv bind).Corrupted Q v.chal.coins (A.answered Pv bind a v) i
  /-- No ring signature on the forgery's ring and message was requested. -/
  no_ringSign : ∀ s (ring : RingOf Sch.PK N) m,
    RingRequest.ringSign s ring m ∈ A.answered Pv bind a v →
    ¬ (ring.1 = (A.claim Pv bind a v).stmt.ring.1 ∧ m = (A.claim Pv bind a v).stmt.msg)
  /-- No member was asked an ordinary signature on the forgery's base message. -/
  no_sign : ∀ i, Sch.pk (v.chal.coins.1 i) ∈ (A.claim Pv bind a v).stmt.ring.1 →
    RingRequest.base (.sign i (bind (A.claim Pv bind a v).stmt.ring.1
      (A.claim Pv bind a v).stmt.msg)) ∉ A.answered Pv bind a v

/-- **The probability that the adversary wins the game of BKM06 Definition 7** (with the
ordinary signing oracle as an extra power): the compiled verifier accepts its claim and the claim
is fresh in the sense of BKM06 (`BKMFresh`). -/
noncomputable def bkmWinProb : ℝ≥0∞ :=
  ∑' a, A.aux a * (((A.alg a).toKindAlg.composeBothOut (challenger Pv bind (Q := Q)) id).realLaw
    (outEquiv k e)).toOuterMeasure {p | ∃ v ∈ p.out,
      V.Accepted p.oracle (A.claim Pv bind a v) ∧ A.BKMFresh Pv bind a v}

end RingAdversary

end GordieHowe.Ring
