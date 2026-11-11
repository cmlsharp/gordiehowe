-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.InsiderSignedRelays

@[expose] public section

/-!
# The signing relay of the requests of BKM06 Definition 7

The relay through which a forger of the multi-user strong-unforgeability game
(`SignRelayForger`) answers the requests of an adversary of BKM06 Definition 7: public keys and
corruptions are forwarded; a ring-signing request `(s, R, m)` asks user `s`'s public key and, when
`s` is a member of an admissible ring, one signature `σ` by `s` on `bind R m`, and sends the
statement `(R, m, pub σ)` to the main challenger; the ring signature is the main proof with the
public value `pub σ`.

- `bkmSignProg`, `bkmSignRelay`: the program of a request and the signing relay.
- `atKeys_bkmSignRelay`: at the users' coins and the signing tables, the relay is `seRelayPub` with
  the public values of the signers' signatures at the tables' entries (`sigPubs` at `rdTable`).
- `corrupt_mem_calls_bkmSignRelay`: its base calls corrupt exactly the users whose corruption was
  requested. `exists_of_returned_bkmSignRelay`: a signature returned to user `i` is user `i`'s
  signature on `bind R m` at the entry of the table of a ring-signing request `(i, R, m)`.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS
open scoped ENNReal

variable {Sch : SigScheme} {n N : ℕ} {RMsg : Type} [Nonempty RMsg]

variable [Nonempty Sch.KeyCoins] [Nonempty Sch.SignCoins]

/-- **The signature of a base answer**: the signature of a signing answer, `dummySig` otherwise. -/
noncomputable def sigOfAnswer (bind : List Sch.PK → RMsg → Sch.Msg) : BaseResponse Sch → Sch.Sig
  | .signature σ => σ
  | _ => dummySig bind

/-- **The public key of a base answer**: the key of a public-key answer, any key otherwise. -/
noncomputable def pkOfAnswer : BaseResponse Sch → Sch.PK
  | .publicKey pk => pk
  | _ => Classical.arbitrary _

variable [DecidableEq Sch.PK] [Nonempty Sch.Pub]

open Classical in
/-- **The ring-signing step of request number `c` after the signer's public key `pk`**: for a
request below `Q` whose admissible ring holds `pk`, one signature `σ` by `s` on `bind R m`, sending
the statement `(R, m, pub σ)` and returning the main proof with the public value `pub σ`;
otherwise `dummyStmt` and `none`. -/
noncomputable def bkmSignStep (Resp : Type) (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) (Q c : ℕ) (s : Fin n) (R : RingOf Sch.PK N) (m : RMsg)
    (pk : Sch.PK) :
    BaseProg Sch n (RelayStmt Sch n N RMsg × (Option Resp → Option (RingResponse Sch Resp))) :=
  if c < Q ∧ signerIn (fun _ => pk) adm (.ringSign s R m : BKMRequest Sch n N RMsg) then
    .query (.sign s (bind R.1 m)) fun b =>
      .pure ((⟨R, m, Sch.pub (sigOfAnswer bind b)⟩, .ringSign s R m),
        fun a => a.map (.ringSignature (Sch.pub (sigOfAnswer bind b))))
  else .pure ((dummyStmt Sch RMsg N, .ringSign s R m), fun _ => none)

/-- **The program of request number `c`** through the base oracles, for `Q` answered requests: a
public-key or corruption request is forwarded and its answer returned (below `Q`), with the
statement `dummyStmt`; a ring-signing request `(s, R, m)` asks user `s`'s public key, then runs
`bkmSignStep`. -/
noncomputable def bkmSignProg (Resp : Type) (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) (Q c : ℕ) :
    BKMRequest Sch n N RMsg →
      BaseProg Sch n (RelayStmt Sch n N RMsg × (Option Resp → Option (RingResponse Sch Resp)))
  | .publicKey i => .query (.publicKey i) fun b =>
      .pure ((dummyStmt Sch RMsg N, .publicKey i), fun _ => if c < Q then some (.base b) else none)
  | .corrupt i => .query (.corrupt i) fun b =>
      .pure ((dummyStmt Sch RMsg N, .corrupt i), fun _ => if c < Q then some (.base b) else none)
  | .ringSign s R m => .query (.publicKey s) fun b => bkmSignStep Resp adm bind Q c s R m (pkOfAnswer b)

omit [Nonempty RMsg] in
/-- **The program of a request makes at most one signing call.** -/
theorem bkmSignProg_signs_le [Nonempty RMsg] (Resp : Type) (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) (Q c : ℕ) (r : BKMRequest Sch n N RMsg)
    (O : BaseRequest Sch n → BaseResponse Sch) :
    (((bkmSignProg Resp adm bind Q c r).trace O).filter BaseRequest.isSign).length ≤ 1 := by
  classical
  rcases r with i | i | ⟨s, R, m⟩
  · simp [bkmSignProg, BaseRequest.isSign]
  · simp [bkmSignProg, BaseRequest.isSign]
  · simp only [bkmSignProg, OracleProg.trace_query, bkmSignStep]
    split_ifs <;> simp [OracleProg.trace_query, List.filter, BaseRequest.isSign]

variable [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Fintype Sch.Sig]
  [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Fintype Sch.KeyCoins]
  [DecidableEq Sch.KeyCoins] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins]

variable (Sch n N RMsg) in
/-- **The signing relay of the requests of BKM06 Definition 7** with `Q` answered requests, for
the admissible rings `adm` and the base-message map `bind` (`bkmSignProg`).

Running time: per request, at most two base calls, a lookup of the signer's key in the ring and
one evaluation of the public value. This running time is argued here, not proved in Lean. -/
noncomputable def bkmSignRelay (Resp : Type) (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) (Q : ℕ) :
    SignRelay Sch n (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) (RelayStmt Sch n N RMsg)
      Resp where
  prog c r := bkmSignProg Resp adm bind Q c r
  prog_signs_le c r O := bkmSignProg_signs_le Resp adm bind Q c r O

variable {Resp : Type} (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg)

omit [Fintype Sch.PK] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [DecidableEq Sch.KeyCoins] [DecidableEq Sch.SignCoins] in
/-- **At the users' coins and the signing tables, the signing relay of BKM06 is the relay of
statements with the signers' public values** `seRelayPub`, at the public values of the signatures
at the tables' entries (`sigPubs` at `rdTable`). -/
theorem atKeys_bkmSignRelay {Q : ℕ} (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) :
    (bkmSignRelay Sch n N RMsg Resp adm bind Q).atKeys keys tabs =
      seRelayPub (fun i => Sch.pk (keys i)) keys adm (sigPubs keys bind (rdTable Sch n) tabs) := by
  classical
  simp only [SignRelay.atKeys, seRelayPub, SideRelay.mk.injEq]
  constructor
  · funext c r
    rcases r with i | i | ⟨s, R, m⟩
    · simp [bkmSignRelay, bkmSignProg, stmtAt, signerIn]
    · simp [bkmSignRelay, bkmSignProg, stmtAt, signerIn]
    · simp only [bkmSignRelay, bkmSignProg, OracleProg.run_query, SignRelay.oracleAt_publicKey,
        pkOfAnswer]
      unfold bkmSignStep
      by_cases h : c < Q ∧ signerIn (fun i => Sch.pk (keys i)) adm
          (.ringSign s R m : BKMRequest Sch n N RMsg)
      · have h' : c < Q ∧ signerIn (fun _ => Sch.pk (keys s)) adm
            (.ringSign s R m : BKMRequest Sch n N RMsg) := h
        rw [if_pos h', stmtAt, dif_pos h]
        simp only [OracleProg.run_query, OracleProg.run_pure, SignRelay.oracleAt_of_lt keys tabs h.1,
          tableAnswer, sigOfAnswer, sigPubs, sigOf, rdTable]
      · have h' : ¬ (c < Q ∧ signerIn (fun _ => Sch.pk (keys s)) adm
            (.ringSign s R m : BKMRequest Sch n N RMsg)) := h
        rw [if_neg h', stmtAt, dif_neg h]
        simp only [OracleProg.run_pure]
  · funext c r a
    rcases r with i | i | ⟨s, R, m⟩
    · simp only [bkmSignRelay, bkmSignProg, OracleProg.run_query, SignRelay.oracleAt,
        OracleProg.run_pure, sideAnswer]
      split_ifs <;> rfl
    · simp only [bkmSignRelay, bkmSignProg, OracleProg.run_query, SignRelay.oracleAt,
        OracleProg.run_pure, sideAnswer]
      split_ifs <;> rfl
    · simp only [bkmSignRelay, bkmSignProg, OracleProg.run_query, SignRelay.oracleAt_publicKey,
        pkOfAnswer]
      unfold bkmSignStep
      by_cases h : c < Q ∧ signerIn (fun i => Sch.pk (keys i)) adm
          (.ringSign s R m : BKMRequest Sch n N RMsg)
      · have h' : c < Q ∧ signerIn (fun _ => Sch.pk (keys s)) adm
            (.ringSign s R m : BKMRequest Sch n N RMsg) := h
        rw [if_pos h']
        simp only [OracleProg.run_query, OracleProg.run_pure, SignRelay.oracleAt_of_lt keys tabs h.1,
          tableAnswer, sigOfAnswer, sideAnswer, dif_pos h.1, sigPubs, sigOf, rdTable]
        rw [if_pos h.2]
      · have h' : ¬ (c < Q ∧ signerIn (fun _ => Sch.pk (keys s)) adm
            (.ringSign s R m : BKMRequest Sch n N RMsg)) := h
        rw [if_neg h']
        simp only [OracleProg.run_pure, sideAnswer]
        split_ifs with hc hs
        · exact absurd ⟨hc, hs⟩ h
        · rfl
        · rfl

omit [Nonempty RMsg] [Fintype Sch.PK] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [DecidableEq Sch.KeyCoins] [DecidableEq Sch.SignCoins] in
/-- **The base calls of a request of BKM06 through the signing relay**: a public key or
corruption is forwarded; a ring-signing request `(s, R, m)` asks `s`'s public key and, when it is
a member's request below `Q`, the signature of `s` on `bind R m`. -/
theorem callsAt_bkmSignRelay [Nonempty RMsg] {Q : ℕ} (keys : Fin n → Sch.KeyCoins)
    (tabs : Fin Q → SignTable Sch n) (c : ℕ) (r : BKMRequest Sch n N RMsg) :
    (bkmSignRelay Sch n N RMsg Resp adm bind Q).callsAt keys tabs c r =
      match r with
      | .publicKey i => [.publicKey i]
      | .corrupt i => [.corrupt i]
      | .ringSign s R m =>
        open Classical in
        if c < Q ∧ signerIn (fun i => Sch.pk (keys i)) adm (.ringSign s R m : BKMRequest Sch n N RMsg)
        then [.publicKey s, .sign s (bind R.1 m)] else [.publicKey s] := by
  classical
  rcases r with i | i | ⟨s, R, m⟩
  · simp [SignRelay.callsAt, bkmSignRelay, bkmSignProg]
  · simp [SignRelay.callsAt, bkmSignRelay, bkmSignProg]
  · simp only [SignRelay.callsAt, bkmSignRelay, bkmSignProg, OracleProg.trace_query,
      SignRelay.oracleAt_publicKey, pkOfAnswer]
    unfold bkmSignStep
    by_cases h : c < Q ∧ signerIn (fun i => Sch.pk (keys i)) adm
        (.ringSign s R m : BKMRequest Sch n N RMsg)
    · have h' : c < Q ∧ signerIn (fun _ => Sch.pk (keys s)) adm
          (.ringSign s R m : BKMRequest Sch n N RMsg) := h
      rw [if_pos h', if_pos h]
      simp [OracleProg.trace_query]
    · have h' : ¬ (c < Q ∧ signerIn (fun _ => Sch.pk (keys s)) adm
          (.ringSign s R m : BKMRequest Sch n N RMsg)) := h
      rw [if_neg h', if_neg h]
      simp

omit [Nonempty RMsg] in
/-- **The base calls of the requests of BKM06 through the signing relay corrupt exactly the users
whose corruption was requested.** -/
theorem corrupt_mem_calls_bkmSignRelay [Nonempty RMsg] {Q : ℕ} (keys : Fin n → Sch.KeyCoins)
    (tabs : Fin Q → SignTable Sch n) (reqs : List (BKMRequest Sch n N RMsg)) (i : Fin n) :
    BaseRequest.corrupt i ∈ (bkmSignRelay Sch n N RMsg Resp adm bind Q).calls keys tabs reqs ↔
      BKMRequest.corrupt i ∈ reqs := by
  classical
  simp only [SignRelay.calls, List.mem_flatMap, callsAt_bkmSignRelay]
  constructor
  · rintro ⟨p, hp, h⟩
    have hmem := List.fst_mem_of_mem_zipIdx hp
    rcases hr : p.1 with j | j | ⟨s, R, m⟩ <;> rw [hr] at h
    · simp at h
    · simp only [List.mem_singleton, BaseRequest.corrupt.injEq] at h
      subst h
      rw [← hr]
      exact hmem
    · dsimp only at h
      split_ifs at h <;> simp at h
  · intro h
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem h
    refine ⟨(reqs[j], j), List.mem_zipIdx_iff_getElem?.2 (by simp), ?_⟩
    simp [hji]

omit [Nonempty RMsg] in
/-- **A signature returned to user `i` through the signing relay** is user `i`'s signature on
`bind R m` at the entry `(i, bind R m)` of the table of a ring-signing request `(i, R, m)`
numbered below `Q`. -/
theorem exists_of_returned_bkmSignRelay [Nonempty RMsg] {Q : ℕ} {keys : Fin n → Sch.KeyCoins}
    {tabs : Fin Q → SignTable Sch n} {reqs : List (BKMRequest Sch n N RMsg)} {i : Fin n}
    {σ : Sch.Sig} (h : (bkmSignRelay Sch n N RMsg Resp adm bind Q).Returned keys tabs reqs i σ) :
    ∃ p ∈ reqs.zipIdx, ∃ (hp : p.2 < Q) (R : RingOf Sch.PK N) (m : RMsg),
      p.1 = .ringSign i R m ∧
        σ = Sch.signWith (Sch.sk (keys i)) (bind R.1 m) (tabs ⟨p.2, hp⟩ (i, bind R.1 m)) := by
  classical
  obtain ⟨m', p, hp, hs, rfl⟩ := h
  rw [callsAt_bkmSignRelay] at hs
  rcases hr : p.1 with j | j | ⟨s, R, m⟩ <;> rw [hr] at hs
  · simp at hs
  · simp at hs
  · dsimp only at hs
    split_ifs at hs with hc
    · simp only [List.mem_cons, reduceCtorEq, BaseRequest.sign.injEq, List.not_mem_nil,
        or_false, false_or] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨p, hp, hc.1, R, m, hr, ?_⟩
      simp only [SignRelay.tableAt, dif_pos hc.1]
    · simp at hs

end GordieHowe.Ring
