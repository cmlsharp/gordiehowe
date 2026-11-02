-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerCount
public import GordieHowe.Applications.Ring.RingForgerKeyReuse
public import GordieHowe.Model.Signature.RingStdToStd

@[expose] public section

/-!
# BKM06 Definition 7 and the key-reuse game from MU-EUF-CMA^corr

The instances of `forgeProb_le_muEufProb_schedule`
(`GordieHowe/Applications/Ring/RingForgerMUBound.lean`) for BKM06 Definition 7 (the game without
a side oracle) with the ring-aware signing oracle, and for the key-reuse game (the side oracle
`baseSide`) with the ring-aware and the ordinary signing oracle: the relay families `insiderFam`
and `keyReuseFam` (the idle request the public key of user `0`), and the adversary embedded into
`max n 2` users, so that user `1` carries the dummy request's key.

- `insiderFam`: the relay family of BKM06 Definition 7.
- `insiderForgeProb_le_muEufProb`: the forgery probability of BKM06 Definition 7 with
  `n` users is at most the success probability of the multi-user forger with `max n 2` users and
  `ringQ'` requests, plus the knowledge error.
- `keyReuseFam`, `keyReuseForgeProb_le_muEufProb`: the same for the key-reuse game.
- `insiderForgeProb_le_muEufProbWithin`, `keyReuseForgeProb_le_muEufProbWithin`:
  the bounds with the multi-user forger winning with at most `Q` signing and corruption requests
  (`Signature.muEufProbWithin`, `forgeProb_le_muEufProbWithin_schedule`).
- `insiderForgeProb_le_muEufProbWithin_one`: one user, through the forger with two users.
- `keyReuseForgeProb_le_muEufProbWithin_std`: the key-reuse game from the standard multi-user game
  (`SignOracle.std`), for a ring-aware signer signing as the ordinary signer (`RingSignsStd`).
- `insiderForgeProb_le_muEufProbWithin_std`: BKM06 Definition 7 from the standard multi-user game,
  for a ring-aware signer signing as the ordinary signer.
-/

namespace GordieHowe

open Quantum Signature RingSignature QROM IOP
open scoped ENNReal

variable {m k e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits m) (XOut k e) N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ}
  {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)} {β : ℕ → ℝ≥0∞}

variable (B PS adm n) in
/-- **The relay family of BKM06 Definition 7** for `n` users: `forgerRelay` with the idle request
the public key of user `0`. -/
noncomputable abbrev insiderFam [NeZero n] :
    RelayFam (Bits m) (XOut k e) B PS adm n (SideOracle.none _) (SignOracle.ring B) :=
  fun pks => forgerRelay B PS adm pks 0

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

variable (B PS adm n) in
/-- **The relay family of the key-reuse game** for `n` users: `forgerRelayStd` with the idle request
the public key of user `0`. -/
noncomputable abbrev keyReuseFam [NeZero n] :
    RelayFam (Bits m) (XOut k e) B PS adm n (baseSide B PS adm) (SignOracle.ringStd B) :=
  fun pks => forgerRelayStd B PS adm pks 0

/-- **The key-reuse game of `ofBase B PS adm` from MU-EUF-CMA^corr with the ring-aware and the
ordinary signing oracle**: the bound of
`insiderForgeProb_le_muEufProb` for the key-reuse game (`keyReuseFam`,
`keyReuseForgeProb_le_relayedForgerStd`). -/
theorem keyReuseForgeProb_le_muEufProb (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :

    keyReuseForgeProb A Q ≤
      muEufProb (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) := by
  have hgame : ThroughRelay B PS adm (embedAdversary (le_max_left n 2) A)
      (keyReuseFam B PS adm (max n 2)) Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))) :=
    -- TODO(unbundle-M4): the stated `max n 2` (`Nat.instMax`) and `F.qR` differ from the
    -- lemma's form only past `forgerRelayStd`; matching whole terms unfolds `absorbQB`/`.sh`.
    by
      have h0 := keyReuseForgeProb_le_relayedForgerStd hbind (embedAdversary (le_max_left n 2) A) 0 Q
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) (le_max_left _ _)
      unfold relayedForgerStd keyReuseForgeProb at h0
      unfold ThroughRelay
      dsimp only [keyReuseFam, forgerRelayStd] at h0 ⊢
      with_reducible_and_instances exact h0
  have h := forgeProb_le_muEufProb_schedule (SignOracle.noQuery_ringStd hB) hC
    hB.verifiesWithoutOracle K hrel
    c₀ f₀ (embedAdversary (le_max_left n 2) A) (scheduleLE_embedAdversary _ hS)
    (keyReuseFam B PS adm (max n 2)) (fun _ => le_rfl) (fun _ => le_rfl) (one_ne_zero_max_two n)
    Q hgame
  exact (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans h

/-- **The bound of `keyReuseForgeProb_le_muEufProb` with at most `Q` signing and
corruption requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem keyReuseForgeProb_le_muEufProbWithin (hbind : B.BindsRing) (hB : B.OracleFree)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) := by
  have hgame : ThroughRelay B PS adm (embedAdversary (le_max_left n 2) A)
      (keyReuseFam B PS adm (max n 2)) Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))) :=
    -- TODO(unbundle-M4): the stated `max n 2` (`Nat.instMax`) and `F.qR` differ from the
    -- lemma's form only past `forgerRelayStd`; matching whole terms unfolds `absorbQB`/`.sh`.
    by
      have h0 := keyReuseForgeProb_le_relayedForgerStd hbind (embedAdversary (le_max_left n 2) A) 0 Q
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) (le_max_left _ _)
      unfold relayedForgerStd keyReuseForgeProb at h0
      unfold ThroughRelay
      dsimp only [keyReuseFam, forgerRelayStd] at h0 ⊢
      with_reducible_and_instances exact h0
  have h := forgeProb_le_muEufProbWithin_schedule (SignOracle.noQuery_ringStd hB) hC
    hB.verifiesWithoutOracle K
    hrel c₀ f₀ (embedAdversary (le_max_left n 2) A) (scheduleLE_embedAdversary _ hS)
    (keyReuseFam B PS adm (max n 2)) (fun _ => rfl) (fun _ => rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) (one_ne_zero_max_two n)
    Q hgame
  exact (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans h


/-- **The key-reuse game of `ofBase B PS adm` from the standard MU-EUF-CMA^corr game**: the bound of
`keyReuseForgeProb_le_muEufProbWithin` with the combined oracle reduced to the ordinary one
(`muEufProbWithin_ringStd_le_std`), for a
ring-aware signer signing as the ordinary signer on the base message (`hstd`), with the same numbers
of requests and of signing and corruption requests. -/
@[headline]
theorem keyReuseForgeProb_le_muEufProbWithin_std (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (ringStdToStd 0 (ringMUForger B PS adm hC c₀ ext f₀ (embedAdversary
        (le_max_left n 2) A)
          (keyReuseFam B PS adm (max n 2)) 1 Q (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
          (ringQ' V Q S w P (1 + (B.qPub + PS.q))))
        (ringQ' V Q S w P (1 + (B.qPub + PS.q))) Q +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + V.kq) :=
  (keyReuseForgeProb_le_muEufProbWithin hbind hB hC K hrel c₀ f₀ A hS Q).trans
    (add_le_add (muEufProbWithin_ringStd_le_std hstd 0 _ _ _) le_rfl)

/-- **BKM06 Definition 7 for `ofBase B PS adm` from the standard MU-EUF-CMA^corr game**: the bound
of `insiderForgeProb_le_muEufProbWithin` with the ring-aware oracle reduced to the ordinary one
(`muEufProbWithin_ring_le_std`), for a
ring-aware signer signing as the ordinary signer on the base message (`hstd`), with the same numbers
of requests and of signing and corruption requests. -/
@[headline]
theorem insiderForgeProb_le_muEufProbWithin_std (hbind : B.BindsRing) (hB : B.OracleFree)
    (hstd : B.RingSignsStd)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B)))
      β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
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

end GordieHowe
