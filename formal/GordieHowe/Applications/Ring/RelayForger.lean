-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.InsiderRelays
public import GordieHowe.SPBCS.SimExtract

@[expose] public section

/-!
# Forgers of the multi-user game that reach the keys only through the base oracles

The multi-user signature game with adaptive corruption (MU-EUF-CMA^corr, Bader, Hofheinz, Jager,
Kiltz, Li, TCC 2015, ePrint 2014/797, Definition 2, p. 6): the challenger draws `n` key pairs; the
forger has oracles for the public keys, for signatures and for the corruption of users; it outputs
a candidate `(pk, m, σ)` and wins if `σ` verifies on `m` under the key `pk` of a user it did not
corrupt and did not ask to sign `m`. The forger here identifies the user by public key.

- `BaseRelay`: a relay of an adversary's requests to a main challenger whose route and answer are
  programs over the base oracles (`BaseRequest`: public keys and corruption; no signing request,
  `route_no_sign`, `answer_no_sign`), with its own coins. `BaseRelay.atKeys F keys ω` is the relay
  (`SideRelay`) obtained by running those programs against the base oracles at the users' coins
  `keys`; `BaseRelay.calls` are the base calls of a list of requests.
- `RelayForger`: a forger of the multi-user game that runs an interactive quantum algorithm `alg`
  with its requests absorbed through a base relay (`AdaptiveIAlg.absorb`), the main requests
  answered by a simulator that programs the oracle (`simExtChallenger`), simulates the random
  oracle by a compressed oracle and extracts from the measured database (`extAdv`), and outputs one
  candidate (`pickForgery`). The keys enter its run only through the base relay's programs, which
  `absorb` runs on the requests the algorithm makes; its success (`RelayForger.success`) counts the
  users corrupted by those programs' base calls.
- `bkmBaseRelay`: the base relay of the requests of BKM06 Definition 7 (public keys, corruptions
  and ring-signing requests, asking the signer's public key), with the public values of the ring
  signatures drawn from its own coins; `atKeys_bkmBaseRelay`: at the users' coins it is
  `seRelay`.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm
open scoped ENNReal

variable {Sch : SigScheme} {n : ℕ}

variable [Nonempty Sch.KeyCoins]

/-- The public keys are inhabited (by the key of any key-generation coins). -/
noncomputable instance SigScheme.instNonemptyPK : Nonempty Sch.PK :=
  ⟨Sch.pk (Classical.arbitrary _)⟩

variable [DecidableEq Sch.PK] [Nonempty Sch.Pub] [Fintype Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins]

variable (Sch n) in
/-- **A program over the base oracles** of the multi-user game. -/
abbrev BaseProg (α : Type) : Type := OracleProg (BaseRequest Sch n) (BaseResponse Sch) α

/-- **A relay of requests through the base oracles**: request number `c` with request `r` is sent
to the main challenger as the result of the program `route ω c r` over the base oracles, and its
reply is the result of `answer ω c r` applied to the main reply, at the relay's coins `ω`. The
programs make no signing request. The relay holds its coin type only: the finiteness and decidable
equality of the coins are instance-implicit binders on its projection (`[Fintype F.Coins]`). -/
structure BaseRelay (Sch : SigScheme) (n : ℕ) (Req Resp Req' Resp' : Type) where
  /-- The relay's coins. -/
  Coins : Type
  /-- Their distribution. -/
  coins : PMF Coins
  /-- The main request, from the base oracles. -/
  route : Coins → ℕ → Req → BaseProg Sch n Req'
  /-- The reply, from the base oracles and the main reply. -/
  answer : Coins → ℕ → Req → BaseProg Sch n (Option Resp' → Option Resp)
  /-- The routes make no signing request. -/
  route_no_sign : ∀ ω c r O, ∀ b ∈ (route ω c r).trace O, b.isSign = false
  /-- The answers make no signing request. -/
  answer_no_sign : ∀ ω c r O, ∀ b ∈ (answer ω c r).trace O, b.isSign = false

namespace BaseRelay

variable {Req Resp Req' Resp' : Type} (F : BaseRelay Sch n Req Resp Req' Resp')

/-- **The base oracles at the users' coins `keys`**, the signing oracle at fixed coins (a base
relay makes no signing request). -/
noncomputable def oracle (keys : Fin n → Sch.KeyCoins) : BaseRequest Sch n → BaseResponse Sch :=
  baseAnswer keys (Classical.arbitrary _)

/-- **The relay at the users' coins `keys`** and the relay's coins `ω`: the route and the answer
run against the base oracles at `keys`. -/
noncomputable def atKeys (keys : Fin n → Sch.KeyCoins) (ω : F.Coins) :
    SideRelay Req Resp Req' Resp' where
  route c r := (F.route ω c r).run (oracle keys)
  answer c r := (F.answer ω c r).run (oracle keys)

/-- **The base calls of the requests `reqs`**, numbered in order: those of each request's route
and answer against the base oracles at `keys`. -/
noncomputable def calls (keys : Fin n → Sch.KeyCoins) (ω : F.Coins) (reqs : List Req) :
    List (BaseRequest Sch n) :=
  reqs.zipIdx.flatMap fun p =>
    (F.route ω p.2 p.1).trace (oracle keys) ++ (F.answer ω p.2 p.1).trace (oracle keys)

omit [Nonempty Sch.KeyCoins] [DecidableEq Sch.PK] [Nonempty Sch.Pub] [Fintype Sch.KeyCoins]
  [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins] in
/-- **A base relay makes no signing request.** -/
theorem not_sign_mem_calls (keys : Fin n → Sch.KeyCoins) (ω : F.Coins) (reqs : List Req)
    (i : Fin n) (m : Sch.Msg) : BaseRequest.sign i m ∉ F.calls keys ω reqs := by
  intro h
  simp only [calls, List.mem_flatMap, List.mem_append] at h
  obtain ⟨p, -, h⟩ := h
  rcases h with h | h
  · simpa [BaseRequest.isSign] using F.route_no_sign ω p.2 p.1 _ _ h
  · simpa [BaseRequest.isSign] using F.answer_no_sign ω p.2 p.1 _ _ h

end BaseRelay

/-! ### Forgers through a base relay -/

section Forger

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {N : ℕ}

variable (Sch n) in
/-- **A forger of the multi-user game through a base relay** for the spBCS compilation `M` with
proofs in the format `B`: auxiliary input, an interactive quantum algorithm with requests `Req`
and replies `Resp` outputting a claim, a base relay of its requests to main requests `Stmt'`
answered by the simulator `sim` with coins `SC` (which programs the oracle), and the
straight-line database extractor `extractor` with the decoding `decode` of its witnesses into
candidates. Its run is `extAdv` of the absorbed algorithm (`RelayForger.success`). -/
structure RelayForger (M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e) (B : ℕ)
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
  /-- The base relay. -/
  relay : BaseRelay Sch n Req Resp Stmt' (M.Response B)
  /-- The simulator answering the main requests. -/
  sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) Stmt' (M.Response B) SC
  /-- The straight-line database extractor. -/
  extractor : RingStmt Sch RMsg N → DB (Bits (queryBits k kN kS L)) (Out k e) → Multiset (RingWit Sch)
  /-- The decoding of a statement and an extracted witness into a candidate. -/
  decode : RingStmt Sch RMsg N → RingWit Sch → Option (Sch.PK × Sch.Msg × Sch.Sig)

namespace RelayForger

variable {M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e} {B : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Vr : RingStmt Sch RMsg N → FullTr P τ → Bool}
  (Qs : ∀ x, M.IOPQueries Vr x) {Req Resp Stmt' SC : Type} [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Stmt'] [DecidableEq Stmt'] [Inhabited Stmt']
  [Fintype SC] [DecidableEq SC] (F : RelayForger Sch n M B Req Resp Stmt' SC)
  [DecidableEq F.relay.Coins] (Q kq : ℕ)

/-- **The run of the forger** at the users' coins `keys`, the relay's coins `ω` and the auxiliary
value `a`: `extAdv` of the algorithm with its requests absorbed through the relay at `keys`. -/
noncomputable abbrev run (keys : Fin n → Sch.KeyCoins) (ω : F.relay.Coins) (a : F.Aux) :=
  extAdv Qs ((F.alg a).absorb (F.relay.atKeys keys ω)) F.sim Q kq

/-- The requests the algorithm made (its first `Q`), read from the run's registers. -/
noncomputable def made (keys : Fin n → Sch.KeyCoins) (ω : F.relay.Coins) (a : F.Aux)
    (c : SPBCS.Reg ((F.alg a).absorb (F.relay.atKeys keys ω)) F.sim Q) : List Req :=
  (requests (advWorkspace ((F.alg a).absorb (F.relay.atKeys keys ω)).toTPKindAlg F.sim Q c).1.logs).take Q

/-- **The forger's single output** at a run's registers `c` and database `D`: a candidate decoded
from a witness the extractor returns for the claim's statement that is a forgery for the users
corrupted, and the messages signed, by the relay's base calls on the requests made
(`pickForgery`). -/
noncomputable def output (keys : Fin n → Sch.KeyCoins) (ω : F.relay.Coins) (a : F.Aux)
    (c : SPBCS.Reg ((F.alg a).absorb (F.relay.atKeys keys ω)) F.sim Q)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Option (Sch.PK × Sch.Msg × Sch.Sig) :=
  pickForgery (BaseForgery keys (fun i => BaseRequest.corrupt i ∈ F.relay.calls keys ω (F.made Q keys ω a c))
      fun i m => BaseRequest.sign i m ∈ F.relay.calls keys ω (F.made Q keys ω a c))
    {f | ∃ w ∈ F.extractor (advOut ((F.alg a).absorb (F.relay.atKeys keys ω)).toTPKindAlg F.sim Q c).stmt D,
      f ∈ F.decode (advOut ((F.alg a).absorb (F.relay.atKeys keys ω)).toTPKindAlg F.sim Q c).stmt w}

variable [Fintype F.relay.Coins]

/-- **The success probability of the forger in the multi-user game with adaptive corruption**
(Bader, Hofheinz, Jager, Kiltz, Li, TCC 2015, ePrint 2014/797, Definition 2, p. 6, with the
forger identifying the user by public key and making no signing request): averaged over the
users' uniform key-generation coins `keys`, the relay's coins and the auxiliary input, the
probability that the forger's single output (`output`) is a forgery at `keys`: a signature that
verifies on its message under the key of a user the relay's base calls did not corrupt. The keys
enter the run only through the base oracles of the relay. -/
noncomputable def success : ℝ≥0∞ :=
  ∑ keys, PMF.uniformOfFintype (Fin n → Sch.KeyCoins) keys * ∑ ω, F.relay.coins ω *
    ∑' a, F.aux a * simProb (outEquiv k e) (F.run Qs Q kq keys ω a) fun c D =>
      ∃ f, F.output Q keys ω a c D = some f ∧
        BaseForgery keys (fun i => BaseRequest.corrupt i ∈ F.relay.calls keys ω (F.made Q keys ω a c))
          (fun i m => BaseRequest.sign i m ∈ F.relay.calls keys ω (F.made Q keys ω a c)) f

end RelayForger

end Forger

/-! ### The base relay of the requests of BKM06 -/

section BKM

variable {N : ℕ} {RMsg : Type} [Nonempty RMsg]

/-- **The public key a request needs**: the signer's, asked from the base oracle, for a
ring-signing request; none otherwise. -/
noncomputable def signerKeyProg : BKMRequest Sch n N RMsg → BaseProg Sch n Sch.PK
  | .ringSign s _ _ => .query (.publicKey s) fun
      | .publicKey pk => .pure pk
      | _ => .pure (Classical.arbitrary _)
  | _ => .pure (Classical.arbitrary _)

/-- **The reply program of a request** through the base oracles, with the public values `pubs`:
a public-key or corruption request is forwarded and its answer returned; a ring-signing request
asks the signer's public key and returns the main proof with the request's public value when the
signer is a member of an admissible ring. -/
noncomputable def bkmAnswerProg {Resp : Type} (adm : List Sch.PK → Prop) {Q : ℕ}
    (pubs : Fin Q → Sch.Pub) (c : ℕ) :
    BKMRequest Sch n N RMsg → BaseProg Sch n (Option Resp → Option (RingResponse Sch Resp))
  | .publicKey i => .query (.publicKey i) fun b => .pure fun _ => if c < Q then some (.base b) else none
  | .corrupt i => .query (.corrupt i) fun b => .pure fun _ => if c < Q then some (.base b) else none
  | .ringSign s R m => (signerKeyProg (.ringSign s R m : BKMRequest Sch n N RMsg)).bind fun pk =>
      .pure fun a => Ring.sideAnswer (fun _ => pk) (fun _ => Classical.arbitrary _) adm pubs c
        (.ringSign s R m) a

omit [Fintype Sch.KeyCoins] in
variable (Sch n N RMsg) in
/-- **The base relay of the requests of BKM06 Definition 7** with `Q` answered requests, for the
admissible rings `adm` and the public values `pubOf` of signing coins: its coins are signing coins
per request (uniform), read only through their public values; request number `c` is sent as its
statement `stmtAt` (at the signer's public key, asked from the base oracle, and the public value of
the request's coins) with the request, and answered by `bkmAnswerProg`.

Running time: per request, one base call and a lookup of the signer's key in the ring; per reply,
one base call. This running time is argued here, not proved in Lean. -/
noncomputable def bkmBaseRelay (Resp : Type) (adm : List Sch.PK → Prop)
    (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ) :
    BaseRelay Sch n (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) (RelayStmt Sch n N RMsg) Resp where
  Coins := Fin Q → Sch.SignCoins
  coins := PMF.uniformOfFintype _
  route ω c r := (signerKeyProg r).bind fun pk =>
    .pure (stmtAt (fun _ => pk) adm (fun j => pubOf (ω j)) c r, r)
  answer ω c r := bkmAnswerProg adm (fun j => pubOf (ω j)) c r
  route_no_sign ω c r O b hb := by
    rcases r with i | i | ⟨s, R, m⟩
    · simp [signerKeyProg] at hb
    · simp [signerKeyProg] at hb
    · simp only [signerKeyProg, OracleProg.trace_bind, OracleProg.trace_query, List.cons_append,
        List.mem_cons] at hb
      rcases hb with rfl | hb
      · rfl
      · split at hb <;> simp at hb
  answer_no_sign ω c r O b hb := by
    rcases r with i | i | ⟨s, R, m⟩
    · simp only [bkmAnswerProg, OracleProg.trace_query, List.mem_cons] at hb
      rcases hb with rfl | hb
      · rfl
      · simp at hb
    · simp only [bkmAnswerProg, OracleProg.trace_query, List.mem_cons] at hb
      rcases hb with rfl | hb
      · rfl
      · simp at hb
    · simp only [bkmAnswerProg, signerKeyProg, OracleProg.trace_bind, OracleProg.trace_query,
        List.cons_append, List.mem_cons] at hb
      rcases hb with rfl | hb
      · rfl
      · split at hb <;> simp at hb

/-! The instances of the relay's coins: those of `Fin Q → Sch.SignCoins`. -/

section BKMBaseRelayInstances

variable {Resp : Type} {adm : List Sch.PK → Prop} {pubOf : Sch.SignCoins → Sch.Pub} {Q : ℕ}

omit [Fintype Sch.KeyCoins] in
instance bkmBaseRelay.instFintypeCoins :
    Fintype (bkmBaseRelay Sch n N RMsg Resp adm pubOf Q).Coins :=
  inferInstanceAs (Fintype (Fin Q → Sch.SignCoins))

omit [Fintype Sch.KeyCoins] in
instance bkmBaseRelay.instDecEqCoins :
    DecidableEq (bkmBaseRelay Sch n N RMsg Resp adm pubOf Q).Coins :=
  inferInstanceAs (DecidableEq (Fin Q → Sch.SignCoins))

end BKMBaseRelayInstances

omit [Nonempty RMsg] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
/-- The statement of a request depends on the public keys only through the signer's. -/
theorem stmtAt_signerKey [Nonempty RMsg] (pkOf : Fin n → Sch.PK) (adm : List Sch.PK → Prop) {Q : ℕ}
    (pubs : Fin Q → Sch.Pub) (c : ℕ) (r : BKMRequest Sch n N RMsg) {pk : Sch.PK}
    (hpk : ∀ s R m, r = .ringSign s R m → pk = pkOf s) :
    stmtAt (fun _ => pk) adm pubs c r = stmtAt pkOf adm pubs c r := by
  rcases r with i | i | ⟨s, R, m⟩
  · simp [stmtAt, signerIn]
  · simp [stmtAt, signerIn]
  · rw [hpk s R m rfl]
    rfl

omit [Fintype Sch.KeyCoins] [DecidableEq Sch.SignCoins] in
/-- **At the users' coins, the base relay of BKM06 is the relay of statements** `seRelay` at their
public keys and coins, with the public values of the relay's coins. -/
theorem atKeys_bkmBaseRelay {Resp : Type} (adm : List Sch.PK → Prop)
    (pubOf : Sch.SignCoins → Sch.Pub) {Q : ℕ} (keys : Fin n → Sch.KeyCoins) (ω : Fin Q → Sch.SignCoins) :
    (bkmBaseRelay Sch n N RMsg Resp adm pubOf Q).atKeys keys ω =
      seRelay (fun i => Sch.pk (keys i)) keys adm fun j => pubOf (ω j) := by
  classical
  simp only [BaseRelay.atKeys, seRelay, SideRelay.mk.injEq]
  constructor
  · funext c r
    rcases r with i | i | ⟨s, R, m⟩
    · simp [bkmBaseRelay, signerKeyProg, stmtAt, signerIn]
    · simp [bkmBaseRelay, signerKeyProg, stmtAt, signerIn]
    · simp only [bkmBaseRelay, signerKeyProg, OracleProg.run_bind, OracleProg.run_query,
        BaseRelay.oracle, baseAnswer, OracleProg.run_pure]
      rfl
  · funext c r a
    rcases r with i | i | ⟨s, R, m⟩
    · simp only [bkmBaseRelay, bkmAnswerProg, OracleProg.run_query, BaseRelay.oracle, baseAnswer,
        OracleProg.run_pure, sideAnswer]
      split_ifs <;> rfl
    · simp only [bkmBaseRelay, bkmAnswerProg, OracleProg.run_query, BaseRelay.oracle, baseAnswer,
        OracleProg.run_pure, sideAnswer]
      split_ifs <;> rfl
    · simp only [bkmBaseRelay, bkmAnswerProg, signerKeyProg, OracleProg.run_bind,
        OracleProg.run_query, BaseRelay.oracle, baseAnswer, OracleProg.run_pure, sideAnswer,
        signerIn]
      split_ifs <;> rfl

omit [Fintype Sch.KeyCoins] [DecidableEq Sch.SignCoins] in
/-- **The base calls of the requests of BKM06 corrupt exactly the users whose corruption was
requested.** -/
theorem corrupt_mem_calls_bkmBaseRelay {Resp : Type} (adm : List Sch.PK → Prop)
    (pubOf : Sch.SignCoins → Sch.Pub) {Q : ℕ} (keys : Fin n → Sch.KeyCoins) (ω : Fin Q → Sch.SignCoins)
    (reqs : List (BKMRequest Sch n N RMsg)) (i : Fin n) :
    BaseRequest.corrupt i ∈ (bkmBaseRelay Sch n N RMsg Resp adm pubOf Q).calls keys ω reqs ↔
      BKMRequest.corrupt i ∈ reqs := by
  simp only [BaseRelay.calls, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨p, hp, h⟩
    have hmem := List.fst_mem_of_mem_zipIdx hp
    rcases hr : p.1 with j | j | ⟨s, R, m⟩ <;> rw [hr] at h
    · simp [bkmBaseRelay, bkmAnswerProg, signerKeyProg] at h
    · simp only [bkmBaseRelay, bkmAnswerProg, signerKeyProg, OracleProg.trace_bind,
        OracleProg.trace_pure, OracleProg.trace_query] at h
      simp only [List.nil_append, List.mem_cons, BaseRequest.corrupt.injEq, List.not_mem_nil,
        or_false] at h
      rcases h with h | h
      · simp at h
      · subst h; rw [← hr]; exact hmem
    · simp only [bkmBaseRelay, bkmAnswerProg, signerKeyProg, OracleProg.trace_bind,
        OracleProg.trace_query, OracleProg.run_query] at h
      simp [BaseRelay.oracle, baseAnswer] at h
  · intro h
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem h
    refine ⟨(reqs[j], j), List.mem_zipIdx_iff_getElem?.2 (by simp), ?_⟩
    simp only [hji, bkmBaseRelay, bkmAnswerProg, signerKeyProg, OracleProg.trace_bind,
      OracleProg.trace_pure, OracleProg.trace_query]
    simp

end BKM

end GordieHowe.Ring
