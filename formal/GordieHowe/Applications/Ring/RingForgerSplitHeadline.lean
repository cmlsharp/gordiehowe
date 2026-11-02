-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplitChain
public import GordieHowe.Applications.Ring.RingForgerTableSplitWin
public import GordieHowe.Model.Quantum.Interactive.LogInvRaw
public import GordieHowe.Model.RingSignature.Schedule

@[expose] public section

/-!
# BKM06 Definition 7 from MU-EUF-CMA^corr at a base signer reading the base component

The reduction from the unforgeability game of `ofBase B PS adm` (BKM06 Definition 7, a
ring-binding base message) to MU-EUF-CMA^corr with at most `Q` signing and corruption requests,
for a base signer that reads the oracle only through the base component of an additive split
`sp : Y ≃+ Y₁ × Y₂`: the game up to the extraction runs at a fixed base component
(`insiderForgeProb_le_extRun_split`, `GordieHowe/Applications/Ring/RingForgerSplitChain.lean`),
then the extraction runs as the multi-user forger with real base queries
(`sum_simLaw_extRun_le_muEufProbWithin_tableForgerSplit`,
`GordieHowe/Applications/Ring/RingForgerTableSplitWin.lean`).

- `sigmaLaw`, `sigmaLaw_apply`, `tsum_sigmaLaw_mul`: a uniform index followed by a law at it, on the
  dependent pairs.
- `simLaw_extRun_split_eq`: one extraction run's event as `simProb` with a test and as `simLaw`
  with a set.
- `forgeSum_le_extRun_split_sigma`: the step of `forgeSum_le_extRun_split` with the prover's coins
  and the auxiliary input as one dependent pair, the base component inside (the form of the table
  forger's bound).
- `splitExp`, `splitWin`: the expansion and the event of the extraction run, typed at the
  adversary at the zero base component.
- `splitMUForger`: the forger of the headline, at the adversary embedded into `max n 2`
  users.
- `splitAux`, `splitAuxLaw`, `splitAdv`, `splitForger`: the auxiliary inputs `⟨ρ, a⟩`, the relayed
  forger followed by `P` as a family over the public keys, and the multi-user forger.
- `splitQ'`, `splitAdv_slots_le`, `bT_splitAdv`, `bT_splitAdv_le`, `splitAdv_slots_le_splitQ'`:
  the requests and queries of the split forger under a schedule bound.
- `splitAdv_logInv`: the relayed forger followed by `P`, at the zero base component, logs at most
  `Q` signing and corruption requests.
- `insiderForgeProb_le_muEufProbWithin_split_of`, `insiderForgeProb_le_muEufProbWithin_split`:
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

section Sigma

variable {C : Type} [Fintype C] [Nonempty C] {Aux : C → Type}

/-- **A uniform index followed by a law at it**, on the dependent pairs. -/
noncomputable def sigmaLaw (μ : ∀ c, PMF (Aux c)) : PMF (Σ c, Aux c) :=
  (PMF.uniformOfFintype C).bind fun c => (μ c).map (Sigma.mk c)

/-- The law at `⟨c, a⟩` is the uniform weight of `c` times the weight of `a`. -/
theorem sigmaLaw_apply (μ : ∀ c, PMF (Aux c)) (c : C) (a : Aux c) :
    sigmaLaw μ ⟨c, a⟩ = PMF.uniformOfFintype C c * μ c a := by
  classical
  rw [sigmaLaw, PMF.bind_apply, tsum_eq_single c]
  · rw [PMF.map_apply, tsum_eq_single a]
    · simp
    · intro a' ha'
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h => ha' h.symm)
  · intro c' hc'
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.2 fun a' => ?_)
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hc' (congrArg Sigma.fst h).symm)

/-- **An average over the dependent pairs** is the average over the index and the law at it. -/
theorem tsum_sigmaLaw_mul (μ : ∀ c, PMF (Aux c)) (f : (Σ c, Aux c) → ℝ≥0∞) :
    ∑' p, sigmaLaw μ p * f p =
      ∑' c, PMF.uniformOfFintype C c * ∑' a, μ c a * f ⟨c, a⟩ := by
  rw [ENNReal.tsum_sigma']
  refine tsum_congr fun c => ?_
  simp only [sigmaLaw_apply, mul_assoc, ENNReal.tsum_mul_left]

end Sigma

section Chain


variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] [NeZero n] {X₀ Cl : Type} {V : NARG.QROM.Verifier m k e Cl X₀}
  {rel : Set (X₀ × RingWit B)} {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞}

variable (V) in
/-- **The expansion of the extraction run** of the adversary `A₀` at the zero base component
against the inert challenger: the claim of the forgery (`splitClaim`), typed at `A₀`'s
registers. -/
noncomputable def splitExp {O : SignOracle B} (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl)
    {shA₀ : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (A₀ : AdaptiveIAlg shA₀ (SplitOut B PS X₀))
    (Q' : ℕ) :
    Expansion (Bits m) (Out k e)
      (ExtReg A₀ (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (MURequest O n)
        (MUResponse B)) :=
  SPBCS.QROM.expansionVia V fun v => splitClaim cl c₀ (extForgery v)

variable (sp rel ext) in
/-- **The event of the extraction run** of the adversary `A₀` at the zero base component: the test
at the base component `ω` passes (`splitTest`) and the database yields a witness in `rel` for the
claim, typed at `A₀`'s registers. -/
def splitWin {O : SignOracle B} (hC : PS.CompiledBySplit sp V) (cl : X₀ → PS.Proof → Option Cl)
    (c₀ : Cl) (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    {shA₀ : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (A₀ : AdaptiveIAlg shA₀ (SplitOut B PS X₀)) :
    Set (BaseGame.Tuple (Bits m) (Out k e)
      (ExtReg A₀ (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (MURequest O n)
        (MUResponse B)) V.kq × DB (Bits m) (Out k e)) :=
  {x | splitTest sp hC cl c₀ ω keys Q' x.1.out ∧
    NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery x.1.out))) x.2}

omit [Nonempty Y₁] [Nonempty Y] in
/-- **One extraction run's event in the two forms** (`simProb` with a test and `simLaw` with a
set), at an adversary read at the base component `ω`. -/
theorem simLaw_extRun_split_eq {O : SignOracle B} (hC : PS.CompiledBySplit sp V)
    {cl : X₀ → PS.Proof → Option Cl} (c₀ : Cl)
    {shA₀ : AlgShape (Bits m) Y (MURequest O n) (MUResponse B)} (A₀ : AdaptiveIAlg shA₀ (SplitOut B PS X₀))
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ) (ω : Bits m → Y₁)
    (c : Fin Q' → O.Coins) :
    simLaw (outEquiv k e) (extRun (outEquiv k e) (A₀.restrictAt sp ω)
        (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
        (muTwoRelay O n (B.pk (keys 0)) i₂)
        (splitExp V cl c₀ (A₀.restrictAt sp 0) Q') V.kq
        (splitDefault Q' (B.pk (keys 0)) i₂ (A₀.restrictAt sp 0))
        (muTabAt sp (A₀.restrictAt sp ω) ω keys Q' c))
      (splitWin sp rel ext hC cl c₀ ω keys Q' (A₀.restrictAt sp 0)) =
      simProb (outEquiv k e) (extRun (outEquiv k e) (A₀.restrictAt sp ω)
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
          (muRelayAt O keys i₂)
          (SPBCS.QROM.expansionVia V fun (v : ExtReg (A₀.restrictAt sp 0)
            (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (MURequest O n)
              (MUResponse B)) => splitClaim cl c₀ (extForgery v)) V.kq
          (splitDefault Q' (B.pk (keys 0)) i₂ (A₀.restrictAt sp 0))
          (muTabAt sp (A₀.restrictAt sp ω) ω keys Q' c))
        (fun (v : ExtReg (A₀.restrictAt sp 0)
            (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (MURequest O n)
              (MUResponse B)) D => splitTest sp hC cl c₀ ω keys Q' v ∧
          NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery v))) D) :=
  rfl

/-- **The step to the extraction runs with the auxiliary input as a dependent pair**
(`forgeSum_le_extRun_split` with the prover's coins and the adversary's auxiliary input as one
pair `⟨ρ, a⟩`, `sigmaLaw`, and the base component's average inside), the form of the table
forger's bound (`sum_simLaw_extRun_le_muEufProbWithin_tableForgerSplit`). -/
theorem forgeSum_le_extRun_split_sigma {O : SignOracle B} (hO : O.ReadsBase sp)
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (c₀ : Cl) (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩) {Q t' : ℕ}
    (𝒜 : (Fin n → B.KeyCoins) → (Fin Q → PS.Coins) →
      QueryBoundedAdversary (Bits m) Y (MURequest O n) (MUResponse B) (SplitOut B PS X₀) t')
    (i₂ : Fin n) (Q' : ℕ) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
        ∑' h, PMF.uniformOfFintype (Bits m → XOut k e) h *
        ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          (((𝒜 keys ρ).restrictAt sp ω).transcriptLaw ((muChallenger O n keys Q').restrictAt sp ω)
            h).toOuterMeasure
            {x | ∃ p ∈ x,
              (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧
              MUFreshReq B (PS := PS) keys p.1.1 (p.2.map HistoryEntry.request) ∧
              p.1.2 = (P p.1.1).run (join sp ω h)} ≤
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' p, sigmaLaw (fun ρ => (𝒜 keys ρ).aux) p *
          ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              simLaw (outEquiv k e) (extRun (outEquiv k e) (((𝒜 keys p.1).alg p.2).restrictAt sp ω)
                  (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
                  (muTwoRelay O n (B.pk (keys 0)) i₂)
                  (splitExp V cl c₀ (((𝒜 keys p.1).alg p.2).restrictAt sp 0) Q') V.kq
                  (splitDefault Q' (B.pk (keys 0)) i₂ (((𝒜 keys p.1).alg p.2).restrictAt sp 0))
                  (muTabAt sp (((𝒜 keys p.1).alg p.2).restrictAt sp ω) ω keys Q' c))
                (splitWin sp rel ext hC cl c₀ ω keys Q' (((𝒜 keys p.1).alg p.2).restrictAt sp 0)) +
        V.knowledgeError β (t' + V.kq) := by
  refine (forgeSum_le_extRun_split (adm := adm) hO hC hcl K c₀ P hPst 𝒜 i₂ Q').trans
    (add_le_add (le_of_eq ?_) le_rfl)
  refine tsum_congr fun keys => congrArg _ ?_
  symm
  simp only [← tsum_fintype (L := .unconditional _), QueryBoundedAdversary.alg_restrictAt]
  rw [tsum_sigmaLaw_mul]
  refine (tsum_congr fun ρ => congrArg (_ * ·) (tsum_mul_tsum_mul_comm _ _ _)).trans ?_
  refine (tsum_mul_tsum_mul_comm _ _ _).trans ?_
  refine tsum_congr fun ω => congrArg _ (tsum_congr fun ρ => congrArg _
    (tsum_congr fun a => congrArg _ (tsum_congr fun c => congrArg _ ?_)))
  -- TODO(unbundle-M4): the goal carries `⟨ρ, a⟩.fst`/`.snd` inside the hidden shape arguments
  -- (`(𝒜 keys ⟨ρ, a⟩.fst).sh ⟨ρ, a⟩.snd`), which `dsimp` does not reach; state the step at a free
  -- pair `p` so the lemma's shape arguments are the goal's at `p := ⟨ρ, a⟩`
  exact (fun p : (Σ ρ, (𝒜 keys ρ).Aux) =>
    simLaw_extRun_split_eq hC c₀ ((𝒜 keys p.1).alg p.2) keys i₂ Q' ω c) ⟨ρ, a⟩

end Chain

section Headline

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] [NeZero n] {X₀ Cl : Type} {V : NARG.QROM.Verifier m k e Cl X₀}
  {rel : Set (X₀ × RingWit B)} {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞} {t : ℕ}

variable (B PS adm) in
/-- **The auxiliary input of the split forger** at the public keys `pks`: the prover's coins `ρ`
and an auxiliary input of the relayed forger followed by `P` at `ρ`. -/
abbrev splitAux (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (q : ℕ) (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) : Type :=
  Σ ρ : Fin Q → PS.Coins, (relayedForgerThen B PS adm P q hP A pks i₁ Q ρ).Aux

variable (B PS adm) in
/-- **The law of the auxiliary input**: uniform prover's coins, then the auxiliary input of the
relayed forger at them (`sigmaLaw`). -/
noncomputable abbrev splitAuxLaw
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (q : ℕ) (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) : PMF (splitAux B PS adm P q hP A i₁ Q pks) :=
  sigmaLaw fun ρ => (relayedForgerThen B PS adm P q hP A pks i₁ Q ρ).aux

variable (B PS adm) in
/-- **The relayed forger followed by `P`** at the public keys `pks` and the auxiliary input
`⟨ρ, a⟩`. -/
noncomputable abbrev splitAdv
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) (p : splitAux B PS adm P q hP A i₁ Q pks) :=
  (relayedForgerThen B PS adm P q hP A pks i₁ Q p.1).alg p.2

variable (sp B PS adm) in
/-- **The multi-user forger of the split chain**: `tableForgerSplit` at the relayed forger
followed by `P`, the inert challenger, the relay `muTwoRelay` with the key of user `0` known, the
expansion and default of the extraction run, and the forgery read by `splitReadout`. -/
noncomputable abbrev splitForger
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q Q' : ℕ) (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, bT ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
      (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) V.kq + 1 ≤ t') :
    MUAdversary (SignOracle.ring B) n (OracleView.queriesOnly (Bits m) Y) t' :=
  tableForgerSplit sp (SignOracle.ring B) (outEquiv k e) (splitAux B PS adm P q hP A i₁ Q)
    (splitAuxLaw B PS adm P q hP A i₁ Q)
    (splitAdv B PS adm P q hP A i₁ Q)
    (fun _ _ => inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
    (fun pks _ => muTwoRelay (SignOracle.ring B) n (pks 0) i₂) (.publicKey 0)
    (fun pks p => splitExp V cl c₀ ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0) Q')
    V.kq
    (fun pks p => splitDefault Q' (pks 0) i₂
      ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0))
    (fun _ _ o => splitReadout B PS V cl c₀ rel ext f₀ o) t' ht



variable (V) in
/-- **The requests and queries of the split forger** for an adversary with `Q` requests and the
schedule bound `S`, `w`, `P` (`GameAdversary.ScheduleLE`), a program with `q` queries and relays of
length at most `L`: at least `Q`, and the bridge's `(S + P) · max w L + q + kq + 1` request
points. -/
def splitQ' (Q q S w P L : ℕ) : ℕ :=
  max Q ((S + P) * max w L + q + V.kq + 1)

/-- **The split forger's slots** under a schedule bound: the adversary's slots and post batches,
each split into at most `max w (1 + qPub + PS.q)` single steps. -/
theorem splitAdv_slots_le
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    {A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t}
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (i₁ : Fin n) (Q : ℕ)
    (pks : Fin n → B.PK) (p : splitAux B PS adm P q hP A i₁ Q pks) :
    (splitAdv B PS adm P q hP A i₁ Q pks p).slots ≤ (S + P') * max w (1 + (B.qPub + PS.q)) := by
  change ((((A (pks, ())).alg p.2).slots + ((A (pks, ())).alg p.2).post) *
    max ((A (pks, ())).alg p.2).width (1 + (B.qPub + PS.q))) ≤ _
  exact Nat.mul_le_mul (Nat.add_le_add (hS.slots_le _ p.2) (hS.post_le _ p.2))
    (max_le_max (hS.width_le _ p.2) le_rfl)

omit [Nonempty Y₁] in
/-- **The bridge's request points of the split forger**: its slots, the program's `q` queries and
the verifier's `kq`. -/
theorem bT_splitAdv
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q Q₁ : ℕ) (pks : Fin n → B.PK) (p : splitAux B PS adm P q hP A i₁ Q pks) :
    bT ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q₁)
      (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) V.kq =
      (splitAdv B PS adm P q hP A i₁ Q pks p).slots + q + V.kq := by
  rw [bT_eq]
  change (splitAdv B PS adm P q hP A i₁ Q pks p).slots * (0 + 1) + 1 * (0 + q) + V.kq = _
  omega

omit [Nonempty Y₁] in
/-- **The bridge's request points of the split forger are at most `splitQ'`** under a schedule
bound. -/
theorem bT_splitAdv_le
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    {A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t}
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (i₁ i₂ : Fin n) (Q Q₁ : ℕ)
    (pks : Fin n → B.PK) (p : splitAux B PS adm P q hP A i₁ Q pks) :
    bT ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q₁)
      (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) V.kq + 1 ≤
      splitQ' V Q q S w P' (1 + (B.qPub + PS.q)) := by
  rw [bT_splitAdv, splitQ']
  have := splitAdv_slots_le P q hP hS i₁ Q pks p
  omega

omit [Nonempty Y₁] in
/-- **The split forger's slots are at most `splitQ'`** under a schedule bound. -/
theorem splitAdv_slots_le_splitQ'
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    {A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t}
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (i₁ : Fin n) (Q : ℕ)
    (pks : Fin n → B.PK) (p : splitAux B PS adm P q hP A i₁ Q pks) :
    (splitAdv B PS adm P q hP A i₁ Q pks p).slots ≤ splitQ' V Q q S w P' (1 + (B.qPub + PS.q)) := by
  rw [splitQ']
  have := splitAdv_slots_le P q hP hS i₁ Q pks p
  omega

variable (sp B PS adm) in
/-- **The multi-user forger of the split chain under a schedule bound**:
`splitForger` at the adversary embedded into `max n 2` users (`embedAdversary`), the relayed
forger playing user `0` and the bridge's relay requesting the public key of user `1`, with
`splitQ'` requests and queries. -/
noncomputable abbrev splitMUForger
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ)
    (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl) (f₀ : B.PK × B.BMsg × B.BSig) :
    MUAdversary (SignOracle.ring B) (max n 2) (OracleView.queriesOnly (Bits m) Y)
      (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) :=
  splitForger sp B PS adm (rel := rel) (ext := ext) P q hP
    (embedAdversary (le_max_left n 2) A) 0 1 Q (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) cl c₀
    f₀ (splitQ' V Q q S w P' (1 + (B.qPub + PS.q)))
    fun pks p => bT_splitAdv_le P q hP (scheduleLE_embedAdversary _ hS) 0 1 Q _ pks p

omit [Nonempty Y₁] in
variable (sp B PS adm) in
/-- **The relayed forger followed by `P`, at the zero base component, logs at most `Q` signing and
corruption requests** (`AdaptiveIAlg.logInv_restrictAt_thenProgWith_relayAdv` with one main
request per request, `forgerRelay`): sets of its workspaces and absorbed logs carried by its steps,
blind to the base part of its workspace, on whose last one the logs hold at most `Q` signing and
corruption requests. -/
theorem splitAdv_logInv
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q : ℕ) (pks : Fin n → B.PK) (p : splitAux B PS adm P q hP A i₁ Q pks) :
    ∃ T, ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).LogInv
        (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) (tab₀ _) T ∧
      (∀ l x v, x ∈ T l →
        ((((splitAdv B PS adm P q hP A i₁ Q pks p).restrictBaseW sp).Lw.set x.1.1 v, x.1.2), x.2) ∈
          T l) ∧
      ∀ x ∈ T (((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).slots +
        ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).post + 1),
        (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Q := by
  -- TODO(unbundle-M4): `splitAdv`'s shape is the relayed forger's `sh` field; unfold the
  -- adversary constructors so it is the shape of `thenProgWith` of `relayAdv`
  dsimp only [splitAdv, relayedForgerThen, QueryBoundedAdversary.thenProgOut,
    AdaptiveIAlg.thenProgOut, relayedForger, relayedForgerVia, QueryBoundedAdversary.mono,
    QueryBoundedAdversary.relay]
  -- TODO(unbundle-M4): the absorbed adversary is given explicitly and the lemma is elaborated
  -- against the goal (`refine … .imp`); left to `obtain` with `_`, its relay output, program and
  -- readout are only fixed when the final `exact` unifies them with the goal's dsimped fields
  have hK : (forgerRelay B PS adm pks i₁).K = 1 := rfl
  refine (AdaptiveIAlg.logInv_restrictAt_thenProgWith_relayAdv sp
    (((A (pks, ())).absorbQB (numRelay B PS adm n (SideOracle.none (ofBase B PS adm)) Q p.1)
      (numRelay_route_injective Q p.1)).alg p.2)
    (forgerRelay B PS adm pks i₁) Q _ _ q _ _ MURequest.isSignOrCorrupt rfl rfl
    (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) (tab₀ _)).imp
    fun T h => ⟨h.1, h.2.1, fun x hx => ?_⟩
  exact (h.2.2 x hx).trans (by rw [hK, one_mul])

/-- **`insiderForgeProb_le_muEufProbWithin_split` at any number `Q'` of the challenger's requests
and any bound `t'` on the forger's queries**, at least the bridge's request points (`ht`, `hQ'`),
`Q` (`hQ`) and the relayed forger's slots (`hslots`): for a
base message binding the ring (`hbind`), a base signer reading only the base component (`hB`), a
proof system compiled by `V` at each base component (`hC`) whose claims factor through the program
statement (`hcl`), a knowledge bound for `rel` (`K`) whose witnesses for the program statement at a
base component are witnesses of the ring relation at every oracle with that base component
(`hrel`), and a program `P` computing the program statement of a forgery (`hPst`), the forgery
probability of an adversary with at most `Q` requests is at most the
probability that the split forger wins with at most `Q` signing and corruption requests, plus the
knowledge error. -/
theorem insiderForgeProb_le_muEufProbWithin_split_of (hbind : B.BindsRing)
    (hB : B.ReadsOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (hrel : ∀ ω h x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm (join sp ω h) x w)
    (c₀ : Cl) (f₀ : B.PK × B.BMsg × B.BSig)
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (hi₂ : i₂ ≠ 0) (Q Q' : ℕ) (hQ : Q ≤ Q') (t' : ℕ)
    (ht : ∀ pks p, bT ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
      (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) V.kq + 1 ≤ t')
    (hQ' : ∀ pks p, bT ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0)
      (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
      (muTwoRelay (SignOracle.ring B) n (pks 0) i₂) V.kq + 1 ≤ Q')
    (hslots : ∀ pks p, (splitAdv B PS adm P q hP A i₁ Q pks p).slots ≤ Q') :
    insiderForgeProb A Q ≤
      muEufProbWithin (splitForger sp B PS adm (rel := rel) (ext := ext) P q hP A i₁ i₂ Q Q' cl c₀
          f₀ t' ht) Q' Q +
        V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have h1 := insiderForgeProb_le_split sp P q hP hbind A i₁ Q Q' hQ
  have hσ := forgeSum_le_extRun_split_sigma (adm := adm) (O := SignOracle.ring B) (Q := Q)
    (t' := t + Q * (B.qPub + PS.q) + q) (SignOracle.readsBase_ring hB) hC hcl K c₀ P hPst
    (fun keys ρ => relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ) i₂ Q'
  have hTP : ∀ pks (p : splitAux B PS adm P q hP A i₁ Q pks),
      ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0).TracePreserving := fun pks p =>
    (splitAdv B PS adm P q hP A i₁ Q pks p).tracePreserving_restrictAt sp 0
      ((relayedForgerThen B PS adm P q hP A pks i₁ Q p.1).tracePreserving p.2)
  have hF := sum_simLaw_extRun_le_muEufProbWithin_tableForgerSplit sp (SignOracle.ring B)
    (outEquiv k e) (splitAux B PS adm P q hP A i₁ Q) (splitAuxLaw B PS adm P q hP A i₁ Q)
    (splitAdv B PS adm P q hP A i₁ Q)
    (fun _ _ => inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
    (fun pks _ => muTwoRelay (SignOracle.ring B) n (pks 0) i₂) (.publicKey 0)
    (fun pks p => splitExp V cl c₀ ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0) Q')
    V.kq
    (fun pks p => splitDefault Q' (pks 0) i₂
      ((splitAdv B PS adm P q hP A i₁ Q pks p).restrictAt sp 0))
    (fun _ _ o => splitReadout B PS V cl c₀ rel ext f₀ o) (SignOracle.readsBase_ring hB)
    (fun pks p => (relayedForgerThen B PS adm P q hP A pks i₁ Q p.1).tracePreserving p.2)
    (fun pks _ => muTwoRelay_outer_ne (pks 0) hi₂) (fun _ _ h => by cases h)
    t' ht Q hQ'
    (fun keys p ω c => muTabAt sp ((splitAdv B PS adm P q hP A i₁ Q _ p).restrictAt sp ω) ω keys Q'
      c)
    (fun _ _ _ _ _ _ _ => rfl)
    (fun keys p ω => splitWin sp rel ext hC cl c₀ ω keys Q'
      ((splitAdv B PS adm P q hP A i₁ Q _ p).restrictAt sp 0))
    (fun keys p ω h c b hb hW => by
      obtain ⟨T, hT, hTD, hTQ⟩ := splitAdv_logInv sp B PS adm P q hP A i₁ i₂ Q _ p
      exact ⟨forgesReq_splitReadout_bridgeAlgDrop hC c₀ f₀ keys i₂ _ ω (join sp ω h) (hrel ω h) Q'
        _ (hTP _ p) (hslots _ p) _ _ _ _ _ ω _ hb hW.1 hW.2,
        countP_requests_bridgeAlgDrop_le _ i₂ (hTP _ p) _ _ _ _ _ ω hT hTD hTQ _ hb⟩)
  -- TODO(unbundle-M4): the chain in steps with named holes, `hF`'s forger matched to `splitForger`
  -- by `with_reducible rfl` (`?e3`); as one `refine` term the elaboration exceeded the heartbeats
  refine le_trans h1 (le_trans (le_of_eq ?e1) (le_trans hσ ?_))
  case e1 => with_reducible rfl
  refine add_le_add (le_trans (le_of_eq ?e2) (le_of_le_of_eq hF ?e3)) le_rfl
  case e3 => with_reducible rfl
  case e2 =>
    refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg₂ _ rfl
      (tsum_congr fun ω => congrArg _ (Finset.sum_congr rfl fun c _ => congrArg _ ?_)))
    with_reducible rfl

/-- **BKM06 Definition 7 from MU-EUF-CMA^corr with at most `Q` signing and corruption requests**,
for a base signer reading only the base component of the split oracle (module docstring): for a
base message binding the ring (`hbind`), a base signer reading only the base component (`hB`), a
proof system compiled by `V` at each base component (`hC`) whose claims factor through the program
statement (`hcl`), a knowledge bound for `rel` (`K`) whose witnesses for the program statement at a
base component are witnesses of the ring relation at every oracle with that base component
(`hrel`), a program `P` with `q` queries computing the program statement of a forgery (`hPst`),
and an adversary with `n` users, at most `t` queries, `Q` requests and the schedule bound `S`, `w`,
`P'` (`hS`), the forgery probability is at most the probability that the split forger, with
`Q' = max Q ((S + P') · max w (1 + qPub + PS.q) + q + kq + 1)` queries (`splitQ'`), wins against
the challenger answering `Q'` requests with at most `Q` signing and corruption requests, plus the
knowledge error at `t + Q · (qPub + PS.q) + q + kq` queries. The forger plays the adversary
embedded into `max n 2` users (`splitMUForger`). -/
theorem insiderForgeProb_le_muEufProbWithin_split (hbind : B.BindsRing) (hB : B.ReadsOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (hrel : ∀ ω h x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm (join sp ω h) x w)
    (c₀ : Cl) (f₀ : B.PK × B.BMsg × B.BSig)
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') (Q : ℕ) :
    insiderForgeProb A Q ≤
      muEufProbWithin (splitMUForger sp B PS adm (V := V) (rel := rel) (ext := ext) P q hP A hS Q
          cl c₀ f₀)
        (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) Q +
        V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have hbT := fun pks p => bT_splitAdv_le (sp := sp) (V := V) P q hP
    (scheduleLE_embedAdversary (le_max_left n 2) hS) 0 1 Q
    (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) pks p
  have h := insiderForgeProb_le_muEufProbWithin_split_of hbind hB hC hcl K hrel c₀ f₀ P q hP hPst
    (embedAdversary (le_max_left n 2) A) 0 1 (one_ne_zero_max_two n) Q
    (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) (le_max_left _ _)
    (splitQ' V Q q S w P' (1 + (B.qPub + PS.q))) hbT hbT
    (fun pks p => splitAdv_slots_le_splitQ' P q hP (scheduleLE_embedAdversary _ hS) 0 Q
      pks p)
  refine (forgeProb_le_embedAdversary (le_max_left n 2) A Q).trans (le_of_le_of_eq h ?_)
  with_reducible rfl

end Headline

end GordieHowe
