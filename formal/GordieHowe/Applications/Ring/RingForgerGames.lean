-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerCount
public import GordieHowe.Applications.Ring.RingForgerJoint
public import GordieHowe.Model.Signature.RingStdToStd

@[expose] public section

/-!
# BKM06 Definition 7 and the joint-security game from MU-EUF-CMA^corr

The instances of `forgeProb_le_muEufProb_schedule`
(`GordieHowe/Applications/Ring/RingForgerMUBound.lean`) for BKM06 Definition 7 (the game without
a side oracle) with the ring-aware signing oracle, and for the joint-security game (the side oracle
`baseSide`) with the ring-aware and the ordinary signing oracle: the relay families `insiderFam`
and `jointFam` (the idle request the public key of user `0`), and the adversary embedded into
`max n 2` users, so that user `1` carries the dummy request's key.

- `insiderFam`: the relay family of BKM06 Definition 7.
- `insiderForgeProb_le_muEufProb`: the forgery probability of BKM06 Definition 7 with
  `n` users is at most the success probability of the multi-user forger with `max n 2` users and
  `ringQ'` requests, plus the knowledge error.
- `jointFam`, `jointForgeProb_le_muEufProb`: the same for the joint-security game.
- `insiderForgeProb_le_muEufProbWithin`, `jointForgeProb_le_muEufProbWithin`:
  the bounds with the multi-user forger winning with at most `Q` signing and corruption requests
  (`Signature.muEufProbWithin`, `forgeProb_le_muEufProbWithin_schedule`).
- `insiderForgeProb_le_muEufProbWithin_one`: one user, through the forger with two users.
- `jointForgeProb_le_muEufProbWithin_std`: the joint-security game from the standard multi-user game
  (`SignOracle.std`), for a ring-aware signer signing as the ordinary signer (`RingSignsStd`).
- `insiderForgeProb_le_muEufProbWithin_std`: BKM06 Definition 7 from the standard multi-user game,
  for a ring-aware signer signing as the ordinary signer.
-/

namespace GordieHowe

open Quantum Signature RingSignature QROM IOP
open scoped ENNReal

variable {m k e N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits m) (XOut k e) N T RMsg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ}
  {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)} {β : ℕ → ℝ≥0∞}

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BMsg]
  [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub]
  [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins]
  [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

variable (B PS adm n) in
/-- **The relay family of BKM06 Definition 7** for `n` users: `forgerRelay` with the idle request
the public key of user `0`. -/
noncomputable abbrev insiderFam [NeZero n] :
    RelayFam (Bits m) (XOut k e) B PS adm n (SideOracle.none _) (SignOracle.ring B) :=
  fun pks => forgerRelay B PS adm pks 0

omit [Fintype T.BMsg] [DecidableEq T.BMsg] in
/-- **BKM06 Definition 7 for `ofBase B PS adm` from MU-EUF-CMA^corr**: for a ring-binding base
message (`hbind`), an oracle-free base signer (`hB`), a proof system given by a compiled verifier
`V` (`hC`) with a knowledge bound for `rel` at `ext` and `β` (`K`), every witness of `rel` one of
the ring relation at every oracle (`hrel`), and an adversary with `n` users, at most `t` queries,
`Q` requests and the schedule bound `S`, `w`, `P` (`hS`), the forgery probability is at most the
success probability in MU-EUF-CMA^corr with the ring-aware signing oracle, `max n 2` users and `Q' =
max Q ((S + P) · max w (1 + qPub + PS.q) + kq + 1)` requests of the multi-user forger `ringMUForger`
of the adversary embedded into `max n 2` users (`embedAdversary`), plus the knowledge error at `t +
Q · (qPub + PS.q) + kq` queries. -/
theorem insiderForgeProb_le_muEufProb (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :

    insiderForgeProb A Q ≤
      muEufProb (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) := by
  have hgame : ThroughRelay B PS adm (embedAdversary (le_max_left n 2) A)
      (insiderFam B PS adm (max n 2)) Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))) :=
    -- TODO(unbundle-M4): the stated `max n 2` (`Nat.instMax`) and `F.qR` differ from the
    -- lemma's form only past `forgerRelay`; matching whole terms unfolds `absorbQB`/`.sh`.
    by
      have h0 := insiderForgeProb_le_relayedForger hbind (embedAdversary (le_max_left n 2) A) 0 Q
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) (le_max_left _ _)
      unfold relayedForger insiderForgeProb at h0
      unfold ThroughRelay
      dsimp only [insiderFam, forgerRelay] at h0 ⊢
      with_reducible_and_instances exact h0
  have h := forgeProb_le_muEufProb_schedule (SignOracle.noQuery_ring hB) hC
    hB.verifiesWithoutOracle K hrel c₀
    f₀ (embedAdversary (le_max_left n 2) A) (scheduleLE_embedAdversary _ hS)
    (insiderFam B PS adm (max n 2)) (fun _ => le_rfl) (fun _ => le_rfl) (one_ne_zero_max_two n)
    Q hgame
  exact (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans h

omit [Fintype T.BMsg] [DecidableEq T.BMsg] in
/-- **The bound of `insiderForgeProb_le_muEufProb` with at most `Q` signing and
corruption requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem insiderForgeProb_le_muEufProbWithin (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) := by
  have hgame : ThroughRelay B PS adm (embedAdversary (le_max_left n 2) A)
      (insiderFam B PS adm (max n 2)) Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))) :=
    -- TODO(unbundle-M4): the stated `max n 2` (`Nat.instMax`) and `F.qR` differ from the
    -- lemma's form only past `forgerRelay`; matching whole terms unfolds `absorbQB`/`.sh`.
    by
      have h0 := insiderForgeProb_le_relayedForger hbind (embedAdversary (le_max_left n 2) A) 0 Q
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) (le_max_left _ _)
      unfold relayedForger insiderForgeProb at h0
      unfold ThroughRelay
      dsimp only [insiderFam, forgerRelay] at h0 ⊢
      with_reducible_and_instances exact h0
  have h := forgeProb_le_muEufProbWithin_schedule (SignOracle.noQuery_ring hB) hC
    hB.verifiesWithoutOracle K
    hrel c₀ f₀ (embedAdversary (le_max_left n 2) A) (scheduleLE_embedAdversary _ hS)
    (insiderFam B PS adm (max n 2)) (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl)
    (fun _ => le_rfl) (one_ne_zero_max_two n)
    Q hgame
  exact (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans h

omit [Fintype T.BMsg] [DecidableEq T.BMsg] in
/-- **BKM06 Definition 7 for one user, from MU-EUF-CMA^corr with two users**
(`insiderForgeProb_le_muEufProbWithin` at `n = 1`): the adversary of the one-user game is
embedded into two users (`embedAdversary`), user `1` carrying the dummy request's key, and the
forgery probability is at most the success probability of the multi-user forger with two users and
at most `Q` signing and corruption requests, plus the knowledge error. -/
theorem insiderForgeProb_le_muEufProbWithin_one (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : InsiderAdversary (ofBase B PS adm) 1 (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringMUForger B PS adm hC c₀ ext f₀
          (embedAdversary (show 1 ≤ 2 by decide) A) (insiderFam B PS adm 2) 1 Q
          (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) :=
  insiderForgeProb_le_muEufProbWithin hbind hB hC K hrel c₀ f₀ A hS Q

omit [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins] in
variable (B PS adm n) in
/-- **The relay family of the joint-security game** for `n` users: `forgerRelayStd` with the idle request
the public key of user `0`. -/
noncomputable abbrev jointFam [NeZero n] :
    RelayFam (Bits m) (XOut k e) B PS adm n (baseSide B PS adm) (SignOracle.ringStd B) :=
  fun pks => forgerRelayStd B PS adm pks 0

/-- **The joint-security game of `ofBase B PS adm` from MU-EUF-CMA^corr with the ring-aware and the
ordinary signing oracle**: the bound of
`insiderForgeProb_le_muEufProb` for the joint-security game (`jointFam`,
`jointForgeProb_le_relayedForgerStd`). -/
theorem jointForgeProb_le_muEufProb (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : JointAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :

    jointForgeProb A Q ≤
      muEufProb (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary (le_max_left n 2) A)
          (jointFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) := by
  have hgame : ThroughRelay B PS adm (embedAdversary (le_max_left n 2) A)
      (jointFam B PS adm (max n 2)) Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))) :=
    -- TODO(unbundle-M4): the stated `max n 2` (`Nat.instMax`) and `F.qR` differ from the
    -- lemma's form only past `forgerRelayStd`; matching whole terms unfolds `absorbQB`/`.sh`.
    by
      have h0 := jointForgeProb_le_relayedForgerStd hbind (embedAdversary (le_max_left n 2) A) 0 Q
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) (le_max_left _ _)
      unfold relayedForgerStd jointForgeProb at h0
      unfold ThroughRelay
      dsimp only [jointFam, forgerRelayStd] at h0 ⊢
      with_reducible_and_instances exact h0
  have h := forgeProb_le_muEufProb_schedule (SignOracle.noQuery_ringStd hB) hC
    hB.verifiesWithoutOracle K hrel
    c₀ f₀ (embedAdversary (le_max_left n 2) A) (scheduleLE_embedAdversary _ hS)
    (jointFam B PS adm (max n 2)) (fun _ => le_rfl) (fun _ => le_rfl) (one_ne_zero_max_two n)
    Q hgame
  exact (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans h

/-- **The bound of `jointForgeProb_le_muEufProb` with at most `Q` signing and
corruption requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem jointForgeProb_le_muEufProbWithin (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : JointAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      muEufProbWithin (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary (le_max_left n 2) A)
          (jointFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) := by
  have hgame : ThroughRelay B PS adm (embedAdversary (le_max_left n 2) A)
      (jointFam B PS adm (max n 2)) Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))) :=
    -- TODO(unbundle-M4): the stated `max n 2` (`Nat.instMax`) and `F.qR` differ from the
    -- lemma's form only past `forgerRelayStd`; matching whole terms unfolds `absorbQB`/`.sh`.
    by
      have h0 := jointForgeProb_le_relayedForgerStd hbind (embedAdversary (le_max_left n 2) A) 0 Q
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) (le_max_left _ _)
      unfold relayedForgerStd jointForgeProb at h0
      unfold ThroughRelay
      dsimp only [jointFam, forgerRelayStd] at h0 ⊢
      with_reducible_and_instances exact h0
  have h := forgeProb_le_muEufProbWithin_schedule (SignOracle.noQuery_ringStd hB) hC
    hB.verifiesWithoutOracle K
    hrel c₀ f₀ (embedAdversary (le_max_left n 2) A) (scheduleLE_embedAdversary _ hS)
    (jointFam B PS adm (max n 2)) (fun _ => rfl) (fun _ => rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) (one_ne_zero_max_two n)
    Q hgame
  exact (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans h


/-- **The joint-security game of `ofBase B PS adm` from the standard MU-EUF-CMA^corr game**: the bound of
`jointForgeProb_le_muEufProbWithin` with the combined oracle reduced to the ordinary one
(`muEufProbWithin_ringStd_le_std`), for a
ring-aware signer signing as the ordinary signer on the base message (`hstd`), with the same numbers
of requests and of signing and corruption requests (the extractor's data as separate
arguments). -/
theorem jointForgeProb_le_muEufProbWithin_std_of (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.MUForgery)
    (A : JointAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      muEufProbWithin (ringStdToStd 0 (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary
        (le_max_left n 2) A)
          (jointFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
          (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) :=
  (jointForgeProb_le_muEufProbWithin hbind hB hC K hrel c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ringStd_le_std hstd 0 _ _ _) le_rfl)

/-- **BKM06 Definition 7 for `ofBase B PS adm` from the standard MU-EUF-CMA^corr game**: the bound
of `insiderForgeProb_le_muEufProbWithin` with the ring-aware oracle reduced to the ordinary one
(`muEufProbWithin_ring_le_std`), for a
ring-aware signer signing as the ordinary signer on the base message (`hstd`), with the same numbers
of requests and of signing and corruption requests (the extractor's data as separate
arguments). -/
theorem insiderForgeProb_le_muEufProbWithin_std_of (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.MUForgery)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (ringToStd 0 (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary
        (le_max_left n 2) A)
          (insiderFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
          (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) :=
  (insiderForgeProb_le_muEufProbWithin hbind hB hC K hrel c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ring_le_std hstd 0 _ _ _) le_rfl)

/-! ### The binding route's bundle and named objects -/

/-- **A binding-route extractor of the proof system `PS`** compiled by the verifier `V`: a
relation `rel`, a database extractor `ext` with its knowledge bound `bound` (CMS19 Proposition 8.12
with the lifted database bound), whose database bound at `b` queries is `β b`, the claim `claim₀` the reduction reads where a
signature does not decode, the forgery `forgery₀` it outputs where no extracted witness gives a
forgery, the compilation `compiled`, and the inclusion of `rel` in the ring relation at every
oracle (`rel_sub`). The headlines' knowledge error at `b` queries is `V.knowledgeError X.β b`,
which adds the oracle-simulation term to `β b`. The bounds hold for every value of `claim₀` and
`forgery₀`. -/
structure _root_.GordieHowe.RingSignature.ProofSystem.RingExtractor
    (PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS) {Cl : Type}
    (V : NARG.QROM.Verifier m k e Cl (RingStmt B)) (adm : KeyRing B.PK N → Prop) where
  /-- The relation the extractor is sound for. -/
  rel : Set (RingStmt B × RingWit B)
  /-- The database extractor. -/
  ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)
  /-- The database bound of `bound` at a number of queries (the probability of a bad database);
  the knowledge error is `V.knowledgeError β`. -/
  β : ℕ → ℝ≥0∞
  /-- The claim read where a signature does not decode. -/
  claim₀ : Cl
  /-- The forgery output where extraction fails. -/
  forgery₀ : B.MUForgery
  /-- `PS` is compiled by `V`. -/
  compiled : PS.CompiledBy V
  /-- The knowledge bound. -/
  bound : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B))) β
  /-- The relation's pairs are in the ring relation at every oracle. -/
  rel_sub : rel ⊆ ringRelAll B adm

variable (B PS) in
/-- **The queries of the adversary and of answering `Q` ring-signing requests** in the binding
route: `t + Q · (qPub + PS.q)` (each request costs the public value and a proof). -/
abbrev ringSignQueries (t Q : ℕ) : ℕ :=
  t + Q * (B.qPub + PS.q)

variable (B PS V) in
/-- **The requests of the binding route's multi-user forger** for `Q` requests and the schedule
bound `S`, `w`, `P`: `ringQ'` with relays of length `1 + qPub + PS.q`. -/
abbrev ringStdRequests (Q S w P : ℕ) : ℕ :=
  ringQ' V Q S w P (1 + (B.qPub + PS.q))

/-- **The base-scheme forger of the binding route for BKM06 Definition 7**: the adversary embedded
into `max n 2` users (`embedAdversary`), relayed (`insiderFam`), run under the compressed-oracle
bridge (`ringMUForger`), its ring-aware requests answered by the ordinary signer (`ringToStd` at
the idle user `0`). -/
noncomputable abbrev insiderStdForger (X : PS.RingExtractor V adm)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (Q S w P : ℕ) : MUAdversary (SignOracle.std B.core) (max n 2)
      (OracleView.queriesOnly (Bits m) (XOut k e)) 0 :=
  ringToStd 0 (ringMUForger B PS adm X.compiled X.claim₀ X.ext X.forgery₀
    (embedAdversary (le_max_left n 2) A) (insiderFam B PS adm (max n 2)) 1 Q
    (ringStdRequests B PS V Q S w P)) (ringStdRequests B PS V Q S w P)

/-- **The base-scheme forger of the binding route for the joint (joint-security) game**:
`insiderStdForger` with `jointFam` and `ringStdToStd`. -/
noncomputable abbrev jointStdForger (X : PS.RingExtractor V adm)
    (A : JointAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (Q S w P : ℕ) : MUAdversary (SignOracle.std B.core) (max n 2)
      (OracleView.queriesOnly (Bits m) (XOut k e)) 0 :=
  ringStdToStd 0 (ringMUForger B PS adm X.compiled X.claim₀ X.ext X.forgery₀
    (embedAdversary (le_max_left n 2) A) (jointFam B PS adm (max n 2)) 1 Q
    (ringStdRequests B PS V Q S w P)) (ringStdRequests B PS V Q S w P)

/-- **The joint-security game of `ofBase B PS adm` from the standard MU-EUF-CMA^corr game**
(`jointForgeProb_le_muEufProbWithin_std_of` over the binding-route extractor `X`): for a
ring-aware signer signing as the ordinary signer on the base message (`hstd`), the forgery
probability is at most the success probability of `jointStdForger` with `ringStdRequests`
requests and `Q` signing and corruption requests, plus the verifier's knowledge error at
`ringSignQueries` queries. -/
@[headline]
theorem jointForgeProb_le_muEufProbWithin_std (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd) (X : PS.RingExtractor V adm)
    (A : JointAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      muEufProbWithin (jointStdForger X A Q S w P) (ringStdRequests B PS V Q S w P) Q +
        V.knowledgeError X.β (ringSignQueries B PS t Q + V.kq) :=
  jointForgeProb_le_muEufProbWithin_std_of hbind hB hstd X.compiled X.bound
    (ringRel_of_mem_ringRelAll · · <| X.rel_sub ·) X.claim₀ X.forgery₀ A hS Q

/-- **BKM06 Definition 7 for `ofBase B PS adm` from the standard MU-EUF-CMA^corr game**
(`insiderForgeProb_le_muEufProbWithin_std_of` over the binding-route extractor `X`): for a
ring-aware signer signing as the ordinary signer on the base message (`hstd`), the forgery
probability is at most the success probability of `insiderStdForger` with `ringStdRequests`
requests and `Q` signing and corruption requests, plus the verifier's knowledge error at
`ringSignQueries` queries. -/
@[headline]
theorem insiderForgeProb_le_muEufProbWithin_std (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd) (X : PS.RingExtractor V adm)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (insiderStdForger X A Q S w P) (ringStdRequests B PS V Q S w P) Q +
        V.knowledgeError X.β (ringSignQueries B PS t Q + V.kq) :=
  insiderForgeProb_le_muEufProbWithin_std_of hbind hB hstd X.compiled X.bound
    (ringRel_of_mem_ringRelAll · · <| X.rel_sub ·) X.claim₀ X.forgery₀ A hS Q

end GordieHowe
