-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplitHeadline
public import GordieHowe.Applications.Ring.RingForgerSplitKeyReuse

@[expose] public section

/-!
# The key-reuse game from MU-EUF-CMA^corr at a base signer reading the base component

The key-reuse form of `GordieHowe/Applications/Ring/RingForgerSplitHeadline.lean`: the relayed
forger of the key-reuse game (`relayedForgerStdThen`, through `forgerRelayStd` to the multi-user
challenger with the ring-aware and the ordinary signing oracle `SignOracle.ringStd B`) in place of
the insider game's, for a base signer whose ring and ordinary signers read only the base component.

- `splitStdMUForger`: the forger of the headline, at the adversary embedded into `max n 2`
  users.
- `splitStdAux`, `splitStdAuxLaw`, `splitStdAdv`, `splitStdForger`: the auxiliary inputs, the
  relayed forger followed by `P` as a family over the public keys, and the multi-user forger.
- `splitStdAdv_slots_le`, `bT_splitStdAdv`, `bT_splitStdAdv_le`, `splitStdAdv_slots_le_splitQ'`:
  the requests and queries of the forger under a schedule bound (`splitQ'`).
- `splitStdAdv_logInv`: the relayed forger followed by `P`, at the zero base component, logs at
  most `Q` signing and corruption requests.
- `keyReuseForgeProb_le_muEufProbWithin_split_of`, `keyReuseForgeProb_le_muEufProbWithin_split`:
  the reduction, at any `Q'` and `t'`, and at `splitQ'` under a schedule bound.

The positional reduction (`…_split_of`) needs `n ≥ 2` users (`hi₂ : i₂ ≠ 0`): the forger's relay
requests the public key of user `i₁` when idle, and the bridge's relay `muTwoRelay` sends the
request `publicKey i₂` in place of the dummy request `publicKey 0`, whose key the forger knows. The
headline embeds the adversary into `max n 2` users (`embedAdversary`), with `i₁ = 0` and `i₂ = 1`.
The multi-user game runs at the whole oracle `Y`, not at the base component `Y₁`.
-/

namespace GordieHowe

open Quantum Signature RingSignature RingSignature.OracleSplit QROM IOP
open scoped ENNReal

section Headline

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes}
  {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] [NeZero n] {X₀ Cl : Type} {V : NARG.QROM.Verifier m k e Cl X₀}
  {rel : Set (X₀ × RingWit B)} {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞} {t : ℕ}

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

variable (B PS adm) in
/-- **The auxiliary input of the split forger of the key-reuse game** at the public keys `pks`:
the prover's coins `ρ` and an auxiliary input of the relayed forger followed by `P` at `ρ`. -/
abbrev splitStdAux (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (q : ℕ) (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) : Type :=
  Σ ρ : Fin Q → PS.Coins, (relayedForgerStdThen B PS adm P q hP A pks i₁ Q ρ).Aux

variable (B PS adm) in
/-- **The law of the auxiliary input of the key-reuse game**: uniform prover's coins, then the
auxiliary input of the key-reuse relayed forger at them (`sigmaLaw`). -/
noncomputable abbrev splitStdAuxLaw
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (q : ℕ) (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) : PMF (splitStdAux B PS adm P q hP A i₁ Q pks) :=
  sigmaLaw fun ρ => (relayedForgerStdThen B PS adm P q hP A pks i₁ Q ρ).aux

variable (B PS adm) in
/-- **The relayed forger of the key-reuse game followed by `P`** at the public keys `pks` and the
auxiliary input `⟨ρ, a⟩`. -/
noncomputable abbrev splitStdAdv
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) (p : splitStdAux B PS adm P q hP A i₁ Q pks) :=
  (relayedForgerStdThen B PS adm P q hP A pks i₁ Q p.1).alg p.2

variable (sp B PS adm) in
/-- **The multi-user forger of the key-reuse split chain**: `tableForgerSplit` at the key-reuse
relayed forger followed by `P`, the inert challenger, the relay `muTwoRelay` with the key of user
`0` known, the expansion and default of the extraction run, and the forgery read by
`splitReadout`. -/
noncomputable abbrev splitStdForger
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q Q' : ℕ) (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, bT ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
      (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) V.kq + 1 ≤ t') :
    MUAdversary (SignOracle.ringStd B) n (OracleView.queriesOnly (Bits m) Y) t' :=
  tableForgerSplit sp (SignOracle.ringStd B) (outEquiv k e) (splitStdAux B PS adm P q hP A i₁ Q)
    (splitStdAuxLaw B PS adm P q hP A i₁ Q)
    (splitStdAdv B PS adm P q hP A i₁ Q)
    (fun _ _ => inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
    (fun pks _ => muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) (.publicKey 0)
    (fun pks p => splitExp V cl c₀ ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0) Q')
    V.kq
    (fun pks p => splitDefault Q' (pks 0) i₂
      ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0))
    (fun _ _ o => splitReadout B PS V cl c₀ rel ext f₀ o) t' ht



omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The split forger's slots** under a schedule bound: the adversary's slots and post batches,
each split into at most `max w (1 + qPub + PS.q)` single steps. -/
theorem splitStdAdv_slots_le
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    {A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t}
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (i₁ : Fin n) (Q : ℕ)
    (pks : Fin n → B.PK) (p : splitStdAux B PS adm P q hP A i₁ Q pks) :
    (splitStdAdv B PS adm P q hP A i₁ Q pks p).slots ≤ (S + P') * max w (1 + (B.qPub + PS.q)) := by
  change ((((A (pks, ())).alg p.2).slots + ((A (pks, ())).alg p.2).post) *
    max ((A (pks, ())).alg p.2).width (1 + (B.qPub + PS.q))) ≤ _
  exact Nat.mul_le_mul (Nat.add_le_add (hS.slots_le _ p.2) (hS.post_le _ p.2))
    (max_le_max (hS.width_le _ p.2) le_rfl)

omit [Nonempty Y₁] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The bridge's request points of the split forger**: its slots, the program's `q` queries and
the verifier's `kq`. -/
theorem bT_splitStdAdv
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q Q₁ : ℕ) (pks : Fin n → B.PK) (p : splitStdAux B PS adm P q hP A i₁ Q pks) :
    bT ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q₁)
      (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) V.kq =
      (splitStdAdv B PS adm P q hP A i₁ Q pks p).slots + q + V.kq := by
  rw [bT_eq]
  change (splitStdAdv B PS adm P q hP A i₁ Q pks p).slots * (0 + 1) + 1 * (0 + q) + V.kq = _
  omega

omit [Nonempty Y₁] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The bridge's request points of the split forger are at most `splitQ'`** under a schedule
bound. -/
theorem bT_splitStdAdv_le
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    {A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t}
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (i₁ i₂ : Fin n) (Q Q₁ : ℕ)
    (pks : Fin n → B.PK) (p : splitStdAux B PS adm P q hP A i₁ Q pks) :
    bT ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q₁)
      (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) V.kq + 1 ≤
      splitQ' V Q q S w P' (1 + (B.qPub + PS.q)) := by
  rw [bT_splitStdAdv, splitQ']
  have := splitStdAdv_slots_le P q hP hS i₁ Q pks p
  omega

omit [Nonempty Y₁] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The split forger's slots are at most `splitQ'`** under a schedule bound. -/
theorem splitStdAdv_slots_le_splitQ'
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    {A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t}
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (i₁ : Fin n) (Q : ℕ)
    (pks : Fin n → B.PK) (p : splitStdAux B PS adm P q hP A i₁ Q pks) :
    (splitStdAdv B PS adm P q hP A i₁ Q pks p).slots ≤
      splitQ' V Q q S w P' (1 + (B.qPub + PS.q)) := by
  rw [splitQ']
  have := splitStdAdv_slots_le P q hP hS i₁ Q pks p
  omega

variable (sp B PS adm) in
/-- **The multi-user forger of the key-reuse split chain under a schedule bound**:
`splitStdForger` at the adversary embedded into `max n 2` users (`embedAdversary`), the relayed
forger playing user `0` and the bridge's relay requesting the public key of user `1`, with
`splitQ'` requests and queries. -/
noncomputable abbrev splitStdMUForger
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ)
    (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl) (f₀ : B.PK × B.BMsg × B.BSig) :
    MUAdversary (SignOracle.ringStd B) (max n 2) (OracleView.queriesOnly (Bits m) Y)
      (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) :=
  splitStdForger sp B PS adm (rel := rel) (ext := ext) P q hP
    (embedAdversary (le_max_left n 2) A) 0 1 Q (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) cl c₀
    f₀ (splitQ' V Q q S w P' (1 + (B.qPub + PS.q)))
    fun pks p => bT_splitStdAdv_le P q hP (scheduleLE_embedAdversary _ hS) 0 1 Q _ pks p

omit [Nonempty Y₁] in
variable (sp B PS adm) in
omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The relayed forger followed by `P`, at the zero base component, logs at most `Q` signing and
corruption requests** (`AdaptiveIAlg.logInv_restrictAt_thenProgWith_relayAdv` with one main request
per request, `forgerRelayStd`): sets of its workspaces and absorbed logs carried by its steps, blind
to the base part of its workspace, on whose last one the logs hold at most `Q` signing and
corruption requests. -/
theorem splitStdAdv_logInv
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) (p : splitStdAux B PS adm P q hP A i₁ Q pks) :
    ∃ T, ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).LogInv
        (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) (tab₀ _) T ∧
      (∀ l x v, x ∈ T l →
        ((((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictBaseW sp).Lw.set x.1.1 v, x.1.2),
          x.2) ∈
          T l) ∧
      ∀ x ∈ T (((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).slots +
        ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).post + 1),
        (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Q := by
  -- TODO(unbundle-M4): `splitStdAdv`'s shape is the relayed forger's `sh` field; unfold the
  -- adversary constructors so it is the shape of `thenProgWith` of `relayAdv`
  dsimp only [splitStdAdv, relayedForgerStdThen, QueryBoundedAdversary.thenProgOut,
    AdaptiveIAlg.thenProgOut, relayedForgerStd, relayedForgerVia, QueryBoundedAdversary.mono,
    QueryBoundedAdversary.relay]
  -- TODO(unbundle-M4): the absorbed adversary is given explicitly and the lemma is elaborated
  -- against the goal (`refine … .imp`); left to `obtain` with `_`, its relay output, program and
  -- readout are only fixed when the final `exact` unifies them with the goal's dsimped fields
  have hK : (forgerRelayStd B PS adm pks i₁).K = 1 := rfl
  refine (AdaptiveIAlg.logInv_restrictAt_thenProgWith_relayAdv sp
    (((A (pks, ())).absorbQB (numRelay B PS adm n _ Q p.1) (numRelay_route_injective Q p.1)).alg
      p.2)
    (forgerRelayStd B PS adm pks i₁) Q _ _ q _ _ MURequest.isSignOrCorrupt rfl rfl
    (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) (tab₀ _)).imp
    fun T h => ⟨h.1, h.2.1, fun x hx => ?_⟩
  exact (h.2.2 x hx).trans (by rw [hK, one_mul])

/-- **`keyReuseForgeProb_le_muEufProbWithin_split` at any number `Q'` of the challenger's requests
and any bound `t'` on the forger's queries**, at least the bridge's request points (`ht`, `hQ'`),
`Q` (`hQ`) and the relayed forger's slots (`hslots`): for a
base message binding the ring (`hbind`), a base signer whose ring and ordinary signers read only
the base component (`hB`, `hStd`), a
proof system compiled by `V` at each base component (`hC`) whose claims factor through the program
statement (`hcl`), a knowledge bound for `rel` (`K`) whose witnesses for the program statement at a
base component are witnesses of the ring relation at every oracle with that base component
(`hrel`), and a program `P` computing the program statement of a forgery (`hPst`), the forgery
probability of an adversary with at most `Q` requests is at most the
probability that the split forger wins with at most `Q` signing and corruption requests, plus the
knowledge error. -/
theorem keyReuseForgeProb_le_muEufProbWithin_split_of (hbind : B.BindsRing)
    (hB : B.ReadsOnly (base sp)) (hStd : B.ReadsStdOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (hrel : ∀ ω h x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm (join sp ω h) x w)
    (c₀ : Cl) (f₀ : B.PK × B.BMsg × B.BSig)
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (hi₂ : i₂ ≠ 0) (Q Q' : ℕ) (hQ : Q ≤ Q') (t' : ℕ)
    (ht : ∀ pks p, bT ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
      (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) V.kq + 1 ≤ t')
    (hQ' : ∀ pks p, bT ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
      (muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) V.kq + 1 ≤ Q')
    (hslots : ∀ pks p, (splitStdAdv B PS adm P q hP A i₁ Q pks p).slots ≤ Q') :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (splitStdForger sp B PS adm (rel := rel) (ext := ext) P q hP A i₁ i₂ Q Q' cl
          c₀
          f₀ t' ht) Q' Q +
        V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have h1 := keyReuseForgeProb_le_split sp P q hP hbind A i₁ Q Q' hQ
  have hσ := forgeSum_le_extRun_split_sigma (adm := adm) (O := SignOracle.ringStd B) (Q := Q)
    (t' := t + Q * (B.qPub + PS.q) + q) (SignOracle.readsBase_ringStd hB hStd) hC hcl K c₀ P hPst
    (fun keys ρ => relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ) i₂ Q'
  have hTP : ∀ pks (p : splitStdAux B PS adm P q hP A i₁ Q pks),
      ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).TracePreserving := fun pks p =>
    (splitStdAdv B PS adm P q hP A i₁ Q pks p).tracePreserving_restrictAt sp 0
      ((relayedForgerStdThen B PS adm P q hP A pks i₁ Q p.1).tracePreserving p.2)
  have hF := sum_simLaw_extRun_le_muEufProbWithin_tableForgerSplit sp (SignOracle.ringStd B)
    (outEquiv k e) (splitStdAux B PS adm P q hP A i₁ Q) (splitStdAuxLaw B PS adm P q hP A i₁ Q)
    (splitStdAdv B PS adm P q hP A i₁ Q)
    (fun _ _ => inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
    (fun pks _ => muTwoRelay (SignOracle.ringStd B) n (pks 0) i₂) (.publicKey 0)
    (fun pks p => splitExp V cl c₀ ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0) Q')
    V.kq
    (fun pks p => splitDefault Q' (pks 0) i₂
      ((splitStdAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0))
    (fun _ _ o => splitReadout B PS V cl c₀ rel ext f₀ o) (SignOracle.readsBase_ringStd hB hStd)
    (fun pks p => (relayedForgerStdThen B PS adm P q hP A pks i₁ Q p.1).tracePreserving p.2)
    (fun pks _ => muTwoRelay_outer_ne (pks 0) hi₂) (fun _ _ h => by cases h)
    t' ht Q hQ'
    (fun keys p ω c => muTabAt sp ((splitStdAdv B PS adm P q hP A i₁ Q _ p).restrictAt sp ω) ω keys
      Q'
      c)
    (fun _ _ _ _ _ _ _ => rfl)
    (fun keys p ω => splitWin sp rel ext hC cl c₀ ω keys Q'
      ((splitStdAdv B PS adm P q hP A i₁ Q _ p).restrictAt sp 0))
    (fun keys p ω h c b hb hW => by
      obtain ⟨T, hT, hTD, hTQ⟩ := splitStdAdv_logInv sp B PS adm P q hP A i₁ i₂ Q _ p
      exact ⟨forgesReq_splitReadout_bridgeAlgDrop hC c₀ f₀ keys i₂ _ ω (join sp ω h) (hrel ω h) Q'
        _ (hTP _ p) (hslots _ p) _ _ _ _ _ ω _ hb hW.1 hW.2,
        countP_requests_bridgeAlgDrop_le _ i₂ (hTP _ p) _ _ _ _ _ ω hT hTD hTQ _ hb⟩)
  -- TODO(unbundle-M4): the chain in steps with named holes, `hF`'s forger matched to
  -- `splitStdForger` by `with_reducible rfl` (`?e3`); as one `refine` term the elaboration exceeded
  -- the heartbeats
  refine le_trans h1 (le_trans (le_of_eq ?e1) (le_trans hσ ?_))
  case e1 => with_reducible rfl
  refine add_le_add (le_trans (le_of_eq ?e2) (le_of_le_of_eq hF ?e3)) le_rfl
  case e3 => with_reducible rfl
  case e2 =>
    refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg₂ _ rfl
      (tsum_congr fun ω => congrArg _ (Finset.sum_congr rfl fun c _ => congrArg _ ?_)))
    with_reducible rfl

/-- **The key-reuse game from MU-EUF-CMA^corr with at most `Q` signing and corruption requests**,
for a base signer reading only the base component of the split oracle (module docstring): for a
base message binding the ring (`hbind`), a base signer whose ring and ordinary signers read only
the base component (`hB`, `hStd`), a
proof system compiled by `V` at each base component (`hC`) whose claims factor through the program
statement (`hcl`), a knowledge bound for `rel` (`K`) whose witnesses for the program statement at a
base component are witnesses of the ring relation at every oracle with that base component
(`hrel`), a program `P` with `q` queries computing the program statement of a forgery (`hPst`),
and an adversary with `n` users, at most `t` queries, `Q` requests and the schedule bound `S`, `w`,
`P'` (`hS`), the forgery probability is at most the probability that the split forger, with
`Q' = max Q ((S + P') · max w (1 + qPub + PS.q) + q + kq + 1)` queries (`splitQ'`), wins against
the challenger answering `Q'` requests with at most `Q` signing and corruption requests, plus the
knowledge error at `t + Q · (qPub + PS.q) + q + kq` queries. The forger plays the adversary
embedded into `max n 2` users (`splitStdMUForger`). -/
theorem keyReuseForgeProb_le_muEufProbWithin_split (hbind : B.BindsRing)
    (hB : B.ReadsOnly (base sp)) (hStd : B.ReadsStdOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (hrel : ∀ ω h x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm (join sp ω h) x w)
    (c₀ : Cl) (f₀ : B.PK × B.BMsg × B.BSig)
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      muEufProbWithin (splitStdMUForger sp B PS adm (V := V) (rel := rel) (ext := ext) P q hP A hS Q
          cl c₀ f₀)
        (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) Q +
        V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have hbT := fun pks p => bT_splitStdAdv_le (sp := sp) (V := V) P q hP
    (scheduleLE_embedAdversary (le_max_left n 2) hS) 0 1 Q
    (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) pks p
  have h := keyReuseForgeProb_le_muEufProbWithin_split_of hbind hB hStd hC hcl K hrel c₀ f₀ P q hP
      hPst
    (embedAdversary (le_max_left n 2) A) 0 1 (one_ne_zero_max_two n) Q
    (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) (le_max_left _ _)
    (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) hbT hbT
    (fun pks p => splitStdAdv_slots_le_splitQ' P q hP (scheduleLE_embedAdversary _ hS) 0 Q
      pks p)
  refine (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans (le_of_le_of_eq h ?_)
  with_reducible rfl

end Headline

end GordieHowe
