-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerMU
public import GordieHowe.Applications.Ring.RingInsiderRelays
public import GordieHowe.Model.Quantum.Interactive.SumChallenger
public import GordieHowe.Model.QROM.NIZK

@[expose] public section

/-!
# The strong relay: signatures from the multi-user challenger, proofs from a proof challenger

The first step of the reduction from BKM06 Definition 7 for `ofBase B PS adm`, at every base
message, to MU-SUF-CMA^corr with the ring-aware signing oracle: each request of the unforgeability
game is relayed (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) to main requests of two
challengers, the multi-user challenger and a challenger of proof queries (`ProofQuery`, answered by
the honest prover or by a simulator, `GordieHowe/Model/Quantum/Interactive/ZeroKnowledge.lean`),
asked of their sum (`Quantum.Challenger.sum`). Every request makes exactly two main requests, a
multi-user request and then a proof query, so that the multi-user and proof requests of request
number `j` are both number `j` of their kind. A corruption is asked as a corruption, then a dummy
proof query (`dummyQuery`: the empty ring, with no witness); a ring-signing request by a member
`s` of a supported ring `R` on `m` is asked as the signing request of user `s` on `(R, m)`, and for
a base signature `σ` the proof query of the statement `(R, m, pub σ)` with the witness `σ` at the
first position of `s`'s key follows (the dummy proof query for a refusal); the ring signature is
the public value and the proof. Another ring-signing request asks for the signer's public key and
the dummy proof query, and is refused. `qPub` queries per request. Unlike the
relay of `GordieHowe/Applications/Ring/RingForgerMU.lean` (`relayRingSign`), the relay computes no
proof: the proof is a main request, so that a simulator may answer it.

- `StrongReq`, `StrongResp`: the main requests and replies (the multi-user request or reply on the
  left, the proof query or proof on the right).
- `dummyQuery`, `askDummy`: the dummy proof query of a request, and asking it before a reply.
- `strongRingSign`, `strongProg`, `strongRelay pks i₁`: the relay programs, with the users' public
  keys `pks` and the idle request the public key of user `i₁`.
- `strongForger A pks Q`: the adversary of the game at the public keys `pks`, relayed by
  `strongRelay` answering `Q` requests.
-/

namespace GordieHowe.RingSignature

open Quantum Signature QROM
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  [Fintype T.BMsg] [DecidableEq T.BMsg]
  [Nonempty T.KeyCoins]
  {B : BaseSigner X Y N T RMsg} {TPS : PSTypes} [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ}

variable [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins]
  [DecidableEq T.KeyCoins]

variable (B PS adm n) in
/-- **The main requests of the strong relay**: a request of the multi-user challenger with the
ring-aware signing oracle, or a proof query of a ring statement with the request it answers
(`Insider.RelayStmt`) and a witness (`Insider.RelayWit`: a position below `N + 1` and a base
signature). -/
abbrev StrongReq : Type :=
  MURequest (SignOracle.ring B) n ⊕ ProofQuery (Insider.RelayStmt B PS adm n) (Insider.RelayWit B)

variable (B PS) in
/-- **The main replies of the strong relay**: a reply of the multi-user challenger, or a proof. -/
abbrev StrongResp : Type := MUResponse B.core ⊕ PS.Proof

section Programs

variable [Zero Y] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]

variable (B PS adm) in
/-- **The dummy proof query of a request**: the empty ring's statement (`Insider.dummyStmt`, which
has no witness) with the request, and a fixed witness. -/
noncomputable def dummyQuery (r : RReq B PS adm n (SideOracle.none _)) :
    ProofQuery (Insider.RelayStmt B PS adm n) (Insider.RelayWit B) :=
  ⟨(Insider.dummyStmt B, r), (0, Classical.arbitrary _)⟩

variable (B PS adm) in
/-- **The dummy proof query of a request, then the reply `o`.** -/
noncomputable def askDummy (r : RReq B PS adm n (SideOracle.none _))
    (o : Option (RResp B PS adm (SideOracle.none _))) :
    OracleProg (X ⊕ StrongReq B PS adm n) (Y ⊕ Option (StrongResp B PS))
      (Option (RResp B PS adm (SideOracle.none _))) :=
  (askResp (.inr (dummyQuery B PS adm r))).mapOutput fun _ => o

variable (B PS adm) in
/-- **The strongly relayed ring signing** by user `s` on `(R, m)`, with the users' public keys
`pks`: the signing request of user `s` on `(R, m)`; for a base signature `σ`, its public value
`y` (relay queries) and the proof query of `(R, m, y)` (with the request) with the witness `σ` at
the first position of `pks s` (capped at `N`), and the ring signature `(y, π)` for a proof `π`;
otherwise the dummy proof query and `none`. Two main requests. -/
noncomputable def strongRingSign (pks : Fin n → B.PK) (s : Fin n) (R : KeyRing B.PK N) (m : B.Msg) :
    OracleProg (X ⊕ StrongReq B PS adm n) (Y ⊕ Option (StrongResp B PS))
      (Option (RResp B PS adm (SideOracle.none _))) :=
  (askResp (.inl (.sign s (R, m)))).bind fun
    | some (.inl (.signature σ)) => (MultiRelay.liftQ (B.pub (pks s) σ)).bind fun y =>
        (askResp (.inr ⟨(⟨R, m, y⟩, .sign s R m),
          (⟨min (R.1.idxOf (pks s)) N, by omega⟩, σ)⟩)).mapOutput fun
          | some (.inr π) => some (.signature ((y, π) : B.Pub × PS.Proof))
          | _ => none
    | _ => askDummy B PS adm (.sign s R m) none

variable (B PS adm) in
/-- **The strong relay program of a request**, with the users' public keys `pks`: every request
makes exactly two main requests, a multi-user request and then a proof query. A corruption is
asked as it is, then the dummy proof query; a ring-signing request by a member of a supported ring
is relayed by `strongRingSign`; another ring-signing request `(s, R, m)` asks for the public key of
user `s` and the dummy proof query, and is refused. -/
noncomputable def strongProg (pks : Fin n → B.PK) :
    RReq B PS adm n (SideOracle.none _) → OracleProg (X ⊕ StrongReq B PS adm n)
      (Y ⊕ Option (StrongResp B PS)) (Option (RResp B PS adm (SideOracle.none _)))
  | .corrupt i => (askResp (.inl (.corrupt i))).bind fun
      | some (.inl (.keyCoins kc)) => askDummy B PS adm (.corrupt i) (some (.keyCoins kc))
      | _ => askDummy B PS adm (.corrupt i) none
  | .sign s R m => if pks s ∈ R.1 ∧ adm R then strongRingSign B PS adm pks s R m else
      (askResp (.inl (.publicKey s))).bind fun _ => askDummy B PS adm (.sign s R m) none
  | .sideSign _ bm => bm.elim

variable (B PS adm) in
/-- **The strong relay** of the game's requests to the sum of the multi-user challenger and a proof
challenger: the programs `strongProg pks`, two main requests and `qPub` queries per request, the
idle request the public key of user `i₁`. -/
noncomputable def strongRelay (pks : Fin n → B.PK) (i₁ : Fin n) :
    MultiRelay X Y (RReq B PS adm n (SideOracle.none _)) (RResp B PS adm (SideOracle.none _))
      (StrongReq B PS adm n) (StrongResp B PS) where
  prog := MultiRelay.plainProg (strongProg B PS adm pks)
  K := 2
  K_pos := Nat.two_pos
  qR := B.qPub
  idle := .inl (.publicKey i₁)

end Programs

section Game

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] {t : ℕ}

/-- The default main request: the public key of user `0`. -/
instance [NeZero n] : Inhabited (StrongReq B PS adm n) := ⟨.inl (.publicKey 0)⟩

variable [NeZero n]

variable (B PS adm) in
/-- **The strongly relayed forger** of an adversary of BKM06 Definition 7 at the users' public keys
`pks`: the adversary relayed by `strongRelay pks i₁` answering `Q` requests, an adversary of the
sum of the multi-user challenger and a proof challenger. At most `t + Q · qPub` queries. -/
noncomputable def strongForger
    (A : UnforgeAdversary (ofBase B PS adm) n (SideOracle.none _) (OracleView.queriesOnly X Y) t)
    (pks : Fin n → B.PK) (i₁ : Fin n) (Q : ℕ) :
    QueryBoundedAdversary X Y (StrongReq B PS adm n) (StrongResp B PS)
      (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) (t + Q * B.qPub) :=
  (A (pks, ())).relay (strongRelay B PS adm pks i₁) Q

end Game

end GordieHowe.RingSignature
