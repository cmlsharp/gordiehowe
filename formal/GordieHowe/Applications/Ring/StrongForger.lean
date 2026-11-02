-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RelayForger

@[expose] public section

/-!
# Forgers of the multi-user strong-unforgeability game with corruption

The multi-user signature game with adaptive corruption (Bader, Hofheinz, Jager, Kiltz, Li,
TCC 2015, ePrint 2014/797, Definition 2, p. 6) with strong freshness: the challenger draws `n` key
pairs; the forger has oracles for the public keys, for signatures and for the corruption of users;
it outputs a candidate `(pk, m, σ)` and wins if `σ` verifies on `m` under the key `pk` of a user it
did not corrupt and `σ` is not a signature the signing oracle returned to that user. A forgery of
this game has `(m, σ)` distinct from every message-signature pair the oracle returned to the user
(`StrongForgery.not_returnedPair`), the freshness of strong unforgeability (SUF-CMA), so a forger
that wins this game wins the multi-user strong-unforgeability game on the same run.

- `SignTable`, `tableAnswer`: a signing table holds signing coins for every user and message; the
  base oracles at a table answer a signing request `(i, m)` with `signWith sk_i m (tab (i, m))`.
- `SignRelay`: a relay of an adversary's requests to a main challenger by one program per request
  over the base oracles (public keys, signatures, corruption), making at most one signing call
  (`prog_signs_le`). `SignRelay.atKeys F keys tabs` runs request number `c` against the base oracles
  at the users' coins `keys` and the signing table `tabs c` drawn for that request: each signing
  call reads one entry of a table drawn for its request alone, so its signature is that of uniform
  signing coins (`SignTable` entries are uniform). From request `Q` on, the base oracles return
  only public keys, so the forger obtains no signature or key outside the recorded requests. `SignRelay.calls`, `SignRelay.ReturnedPair`,
  `SignRelay.Returned`: the base calls of a list of requests and the signatures they returned.
- `StrongForgery`: a candidate that verifies under the key of a user neither corrupted nor holding
  the candidate's signature among those the oracle returned to it.
- `SignRelayForger`, `SignRelayForger.success`: a forger that runs an interactive quantum algorithm
  with its requests absorbed through a signing relay, the main requests answered by a simulator
  that programs the oracle (`simExtChallenger`), simulates the random oracle by a compressed oracle
  and extracts from the measured database (`extAdv`), and outputs one candidate (`pickForgery`);
  its success in the game above, averaged over the users' coins and the signing tables.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm
open scoped ENNReal

variable {Sch : SigScheme} {n : ℕ}

/-- **A signature is guessed from its public value with probability at most `γ`** (a property of
the scheme): for every key-generation coins `kc`, message `m`, public value `y` and signature `σ`,
over uniform signing coins, the probability that the signature `signWith sk_kc m c` is `σ` and
has public value `y` is at most `γ` times the probability that its public value is `y`. That is,
`γ` bounds the conditional probability of every signature given its public value: the
conditional min-entropy of an honest signature given its public value is at least `log₂ (1 / γ)`.
For `Pub = Unit` it is the min-entropy of the signature; for ML-DSA publishing `w₁` it is the
probability of guessing `(c̃, z, h)` from `w₁`. -/
def SigScheme.SigGivenPubLe (Sch : SigScheme) (γ : ℝ≥0∞) : Prop :=
  ∀ kc m y σ, (PMF.uniformOfFintype Sch.SignCoins).toOuterMeasure
      {c | Sch.signWith (Sch.sk kc) m c = σ ∧ Sch.pub (Sch.signWith (Sch.sk kc) m c) = y} ≤
    γ * (PMF.uniformOfFintype Sch.SignCoins).toOuterMeasure
      {c | Sch.pub (Sch.signWith (Sch.sk kc) m c) = y}

variable (Sch n) in
/-- **A signing table**: signing coins for every user and message. -/
abbrev SignTable : Type := Fin n × Sch.Msg → Sch.SignCoins

/-- **The base oracles at the users' coins `keys` and the signing table `tab`**: the public key of
user `i`, a signature `signWith sk_i m (tab (i, m))` on `m` by user `i`, and the key-generation
coins of a corrupted user (as `baseAnswer`, with the signing coins read from the table). -/
def tableAnswer (keys : Fin n → Sch.KeyCoins) (tab : SignTable Sch n) :
    BaseRequest Sch n → BaseResponse Sch
  | .publicKey i => .publicKey (Sch.pk (keys i))
  | .sign i m => .signature (Sch.signWith (Sch.sk (keys i)) m (tab (i, m)))
  | .corrupt i => .keyCoins (keys i)

/-- The base oracles at signing coins `c` are those at the constant table of `c`. -/
theorem baseAnswer_eq_tableAnswer (keys : Fin n → Sch.KeyCoins) (c : Sch.SignCoins) :
    baseAnswer keys c = tableAnswer keys fun _ => c := by
  funext r
  cases r <;> rfl

/-- **A relay of requests through the base oracles that may sign**: request number `c` with
request `r` runs the program `prog c r` over the base oracles (public keys, signatures and
corruption), whose result is the main request and the map from the main reply to the reply. Each
program makes at most one signing call. -/
structure SignRelay (Sch : SigScheme) (n : ℕ) (Req Resp Req' Resp' : Type) where
  /-- The program of request number `c` with request `r`. -/
  prog : ℕ → Req → BaseProg Sch n (Req' × (Option Resp' → Option Resp))
  /-- Each program makes at most one signing call. -/
  prog_signs_le : ∀ c r (O : BaseRequest Sch n → BaseResponse Sch),
    (((prog c r).trace O).filter BaseRequest.isSign).length ≤ 1

namespace SignRelay

variable {Req Resp Req' Resp' : Type} (F : SignRelay Sch n Req Resp Req' Resp') {Q : ℕ}

/-- **The signing table of request number `c`**: the table drawn for it, below `Q`, and a fixed
table from request `Q` on. -/
noncomputable def tableAt (tabs : Fin Q → SignTable Sch n) (c : ℕ) : SignTable Sch n :=
  if h : c < Q then tabs ⟨c, h⟩ else fun _ => Classical.arbitrary _

/-- **The base oracles of request number `c`** at the users' coins `keys` and the signing tables
`tabs`: below `Q`, the oracles at the request's table; from request `Q` on, every request is
answered by the user's public key, so no signature or key-generation coins are returned outside
the recorded requests. -/
noncomputable def oracleAt (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    (c : ℕ) : BaseRequest Sch n → BaseResponse Sch :=
  if c < Q then tableAnswer keys (tableAt tabs c)
  else fun
    | .publicKey i => .publicKey (Sch.pk (keys i))
    | .sign i _ => .publicKey (Sch.pk (keys i))
    | .corrupt i => .publicKey (Sch.pk (keys i))

/-- The base oracles of every request answer a public-key request with the user's key. -/
theorem oracleAt_publicKey (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    (c : ℕ) (i : Fin n) : oracleAt keys tabs c (.publicKey i) = .publicKey (Sch.pk (keys i)) := by
  unfold oracleAt
  split_ifs <;> rfl

/-- Below `Q`, the base oracles are those at the request's signing table. -/
theorem oracleAt_of_lt (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) {c : ℕ}
    (hc : c < Q) : oracleAt keys tabs c = tableAnswer keys (tabs ⟨c, hc⟩) := by
  simp only [oracleAt, tableAt, dif_pos hc, if_pos hc]

/-- **The relay at the users' coins `keys` and the signing tables `tabs`**: request number `c`
runs its program against the base oracles of that request. -/
noncomputable def atKeys (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) :
    SideRelay Req Resp Req' Resp' where
  route c r := ((F.prog c r).run (oracleAt keys tabs c)).1
  answer c r := ((F.prog c r).run (oracleAt keys tabs c)).2

/-- **The base calls of request number `c`** with request `r`. -/
noncomputable def callsAt (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (c : ℕ)
    (r : Req) : List (BaseRequest Sch n) :=
  (F.prog c r).trace (oracleAt keys tabs c)

/-- **The base calls of the requests `reqs`**, numbered in order. -/
noncomputable def calls (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    (reqs : List Req) : List (BaseRequest Sch n) :=
  reqs.zipIdx.flatMap fun p => F.callsAt keys tabs p.2 p.1

/-- **The signing oracle returned `σ` on `m` to user `i`** for one of the requests `reqs`: some
request asked user `i` to sign `m`, and `σ` is the signature at its table's entry `(i, m)`. -/
def ReturnedPair (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (reqs : List Req)
    (i : Fin n) (m : Sch.Msg) (σ : Sch.Sig) : Prop :=
  ∃ p ∈ reqs.zipIdx, BaseRequest.sign i m ∈ F.callsAt keys tabs p.2 p.1 ∧
    σ = Sch.signWith (Sch.sk (keys i)) m (tableAt tabs p.2 (i, m))

/-- **The signing oracle returned `σ` to user `i`** on some message, for one of the requests
`reqs`. -/
def Returned (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (reqs : List Req)
    (i : Fin n) (σ : Sch.Sig) : Prop :=
  ∃ m, F.ReturnedPair keys tabs reqs i m σ

end SignRelay

/-- **A forgery of the multi-user strong-unforgeability game** for the candidate `(pk, m, σ)`, at
the users' coins `keys`, with the predicates `corrupted` of the users and `returned` of the
signatures returned to them: `σ` verifies on `m` under `pk`, and `pk` is the key of a user that is
not corrupted and to which `σ` was not returned. -/
structure StrongForgery (keys : Fin n → Sch.KeyCoins) (corrupted : Fin n → Prop)
    (returned : Fin n → Sch.Sig → Prop) (f : Sch.PK × Sch.Msg × Sch.Sig) : Prop where
  /-- The signature verifies. -/
  verify_eq : Sch.verify f.1 f.2.1 f.2.2 = true
  /-- The key is that of an uncorrupted user to which the signature was not returned. -/
  exists_user : ∃ i, Sch.pk (keys i) = f.1 ∧ ¬ corrupted i ∧ ¬ returned i f.2.2

/-- **A forgery of the game has a fresh message-signature pair**: for the signatures returned by a
signing relay, the user of the forgery was not returned `σ` on the forgery's message `m`, the
freshness of strong unforgeability. -/
theorem StrongForgery.not_returnedPair {Req Resp Req' Resp' : Type}
    {F : SignRelay Sch n Req Resp Req' Resp'} {Q : ℕ} {keys : Fin n → Sch.KeyCoins}
    {tabs : Fin Q → SignTable Sch n} {reqs : List Req} {corrupted : Fin n → Prop}
    {f : Sch.PK × Sch.Msg × Sch.Sig}
    (h : StrongForgery keys corrupted (F.Returned keys tabs reqs) f) :
    ∃ i, Sch.pk (keys i) = f.1 ∧ ¬ corrupted i ∧ ¬ F.ReturnedPair keys tabs reqs i f.2.1 f.2.2 := by
  obtain ⟨i, hi, hc, hr⟩ := h.exists_user
  exact ⟨i, hi, hc, fun hp => hr ⟨_, hp⟩⟩

/-- **The single output of a strong forger** among the candidates `cands`: a candidate that is a
strong forgery (`pickForgery`), or `none`. -/
noncomputable abbrev pickStrong (keys : Fin n → Sch.KeyCoins) (corrupted : Fin n → Prop)
    (returned : Fin n → Sch.Sig → Prop) (cands : Set (Sch.PK × Sch.Msg × Sch.Sig)) :
    Option (Sch.PK × Sch.Msg × Sch.Sig) :=
  pickForgery (StrongForgery keys corrupted returned) cands

/-! ### Forgers through a signing relay -/

section Forger

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {N : ℕ}

variable (Sch n) in
/-- **A forger of the multi-user strong-unforgeability game through a signing relay** for the
spBCS compilation `M` with proofs in the format `B`: auxiliary input, an interactive quantum
algorithm with requests `Req` and replies `Resp` outputting a claim, a signing relay of its
requests to main requests `Stmt'` answered by the simulator `sim` with coins `SC` (which programs
the oracle), and the straight-line database extractor `extractor` with the decoding `decode` of
its witnesses into candidates. Its run is `extAdv` of the absorbed algorithm
(`SignRelayForger.success`). The keys enter its run only through the base oracles. -/
structure SignRelayForger (M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e) (B : ℕ)
    [∀ j i, Fintype ((M.comp j).MessageWrite i)] (Req Resp Stmt' SC : Type) [Fintype Req]
    [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Stmt'] [DecidableEq Stmt']
    [Inhabited Stmt'] [Fintype SC] [DecidableEq SC] where
  /-- The values of the auxiliary input. -/
  Aux : Type
  /-- The distribution of the auxiliary input. -/
  aux : PMF Aux
  /-- The shape of the algorithm on each value. -/
  sh : Aux → AlgShape (Bits (queryBits k kN kS L)) (XOut k e) Req Resp
  /-- The algorithm on each value. -/
  alg : (a : Aux) → AdaptiveIAlg (sh a) (Claim (RingStmt Sch RMsg N) M.NIProof)
  /-- The signing relay. -/
  relay : SignRelay Sch n Req Resp Stmt' (M.Response B)
  /-- The simulator answering the main requests. -/
  sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) Stmt' (M.Response B) SC
  /-- The straight-line database extractor. -/
  extractor : RingStmt Sch RMsg N → DB (Bits (queryBits k kN kS L)) (Out k e) →
    Multiset (RingWit Sch)
  /-- The decoding of a statement and an extracted witness into a candidate. -/
  decode : RingStmt Sch RMsg N → RingWit Sch → Option (Sch.PK × Sch.Msg × Sch.Sig)

namespace SignRelayForger

variable {M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e} {B : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Vr : RingStmt Sch RMsg N → FullTr P τ → Bool}
  (Qs : ∀ x, M.IOPQueries Vr x) {Req Resp Stmt' SC : Type} [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Stmt'] [DecidableEq Stmt'] [Inhabited Stmt']
  [Fintype SC] [DecidableEq SC] (F : SignRelayForger Sch n M B Req Resp Stmt' SC) (Q kq : ℕ)

/-- **The run of the forger** at the users' coins `keys`, the signing tables `tabs` of the first
`Q` requests and the auxiliary value `a`: `extAdv` of the algorithm with its requests absorbed
through the relay at `keys` and `tabs`. -/
noncomputable abbrev run (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    (a : F.Aux) :=
  extAdv Qs ((F.alg a).absorb (F.relay.atKeys keys tabs)) F.sim Q kq

/-- The requests the algorithm made (its first `Q`), read from the run's registers. -/
noncomputable def made (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (a : F.Aux)
    (c : SPBCS.Reg ((F.alg a).absorb (F.relay.atKeys keys tabs)) F.sim Q) : List Req :=
  (requests (advWorkspace ((F.alg a).absorb (F.relay.atKeys keys tabs)).toTPKindAlg F.sim Q
    c).1.logs).take Q

/-- **The users corrupted** by the relay's base calls on the requests made. -/
def Corrupted (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (a : F.Aux)
    (c : SPBCS.Reg ((F.alg a).absorb (F.relay.atKeys keys tabs)) F.sim Q) (i : Fin n) : Prop :=
  BaseRequest.corrupt i ∈ F.relay.calls keys tabs (F.made Q keys tabs a c)

/-- **The candidates of the run** at the registers `c` and the database `D`: the decodings of the
witnesses the extractor returns for the claim's statement. -/
def candidates (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (a : F.Aux)
    (c : SPBCS.Reg ((F.alg a).absorb (F.relay.atKeys keys tabs)) F.sim Q)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Set (Sch.PK × Sch.Msg × Sch.Sig) :=
  {f | ∃ w ∈ F.extractor (advOut ((F.alg a).absorb (F.relay.atKeys keys tabs)).toTPKindAlg F.sim Q
      c).stmt D,
    f ∈ F.decode (advOut ((F.alg a).absorb (F.relay.atKeys keys tabs)).toTPKindAlg F.sim Q c).stmt w}

/-- **The forger's single output** at a run's registers `c` and database `D`: a candidate that is
a strong forgery for the users corrupted, and the signatures returned, by the relay's base calls
on the requests made (`pickStrong`). -/
noncomputable def output (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    (a : F.Aux) (c : SPBCS.Reg ((F.alg a).absorb (F.relay.atKeys keys tabs)) F.sim Q)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Option (Sch.PK × Sch.Msg × Sch.Sig) :=
  pickStrong keys (F.Corrupted Q keys tabs a c) (F.relay.Returned keys tabs (F.made Q keys tabs a c))
    (F.candidates Q keys tabs a c D)

/-- **The success probability of the forger in the multi-user strong-unforgeability game with
adaptive corruption** (Bader, Hofheinz, Jager, Kiltz, Li, TCC 2015, ePrint 2014/797, Definition 2,
p. 6, with strong freshness and the forger identifying the user by public key): averaged over the
users' uniform key-generation coins `keys`, the uniform signing tables of the first `Q` requests
and the auxiliary input, the probability that the forger's single output (`output`) is a strong
forgery at `keys`: a signature that verifies on its message under the key of a user the relay's
base calls did not corrupt and to which the signing oracle did not return that signature. The keys
and the tables enter the run only through the base oracles of the relay. -/
noncomputable def success : ℝ≥0∞ :=
  ∑ keys, PMF.uniformOfFintype (Fin n → Sch.KeyCoins) keys *
    ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs *
      ∑' a, F.aux a * simProb (outEquiv k e) (F.run Qs Q kq keys tabs a) fun c D =>
        ∃ f, F.output Q keys tabs a c D = some f ∧
          StrongForgery keys (F.Corrupted Q keys tabs a c)
            (F.relay.Returned keys tabs (F.made Q keys tabs a c)) f

end SignRelayForger

end Forger

end GordieHowe.Ring
