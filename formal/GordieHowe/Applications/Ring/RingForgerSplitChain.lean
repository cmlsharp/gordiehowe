-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplit
public import GordieHowe.Applications.Ring.RingForgerChain
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut
public import GordieHowe.Applications.Ring.SPBCSSplit

@[expose] public section

/-!
# The unforgeability game at a fixed base component of a split oracle

The first step of the reduction from BKM06 Definition 7 for `ofBase B PS adm` to MU-EUF-CMA^corr when
the base signer reads the oracle (the split form of `GordieHowe/Applications/Ring/RingForgerChain.lean`):
for an oracle split additively as `sp : Y ≃+ Y₁ × Y₂`, the game's forgery probability is at most the
average, over the users' key coins, a uniform base component `ω`, a uniform second component `h` and
the prover's coins, of the probability that the relayed forger followed by a classical program `P` on
its output (`QueryBoundedAdversary.thenProgOut`), read at the base component `ω`
(`QueryBoundedAdversary.restrictAt`), against the multi-user challenger at `ω`, outputs a ring
signature that verifies at the oracle `join sp ω h`, fresh for its multi-user requests, with the
program's result at that oracle.

- `relayAdv_width`: the relayed adversary has width `1`.
- `tsum_uniform_split`: an average over a uniform oracle is an average over its two components.
- `insiderForgeProb_le_split`: the step.
-/

namespace GordieHowe

open Quantum Signature RingSignature RingSignature.OracleSplit QROM IOP
open scoped ENNReal

/-- **The relayed adversary has width `1`.** -/
theorem Quantum.AdaptiveIAlg.relayAdv_width {X Y Req Resp Req' Resp' O O' : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
    [AddGroup Y] [Nonempty X] [Nonempty Y] [Inhabited X] [Inhabited Req']
    {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : MultiRelay X Y Req Resp Req' Resp') (Q : ℕ)
    (out' : A.RelayWS F → O') : (A.relayAdv F Q out').width = 1 :=
  rfl

section Split

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)

/-- **An average over a uniform oracle is an average over its two components** (along
`splitEquiv`, `map_uniform_split`). -/
theorem tsum_uniform_split [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Y₁] [Fintype Y₂]
    [Nonempty Y] [Nonempty Y₁] [Nonempty Y₂] (f : (X → Y) → ℝ≥0∞) :
    ∑' H, PMF.uniformOfFintype (X → Y) H * f H =
      ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
        f (join sp ω h) := by
  classical
  have hcard : (Fintype.card (X → Y) : ℝ≥0∞) =
      Fintype.card (X → Y₁) * Fintype.card (X → Y₂) := by
    rw [Fintype.card_congr (splitEquiv sp), Fintype.card_prod, Nat.cast_mul]
  simp only [tsum_fintype (L := .unconditional _), PMF.uniformOfFintype_apply, Finset.mul_sum]
  rw [← (splitEquiv sp).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun h _ => ?_
  rw [hcard, ENNReal.mul_inv (Or.inl (by exact_mod_cast Fintype.card_ne_zero))
    (Or.inr (by exact_mod_cast Fintype.card_ne_zero)), mul_assoc]
  rfl

section Game

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [Nonempty Y₂] {N n t : ℕ} [NeZero n] {TB : BaseTypes} {B : BaseSigner X Y N TB}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop} [DecidablePred adm]
  {R : Type} (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg X Y R) (q : ℕ)
  (hP : ∀ o, (P o).QueriesLE q)

variable (B PS adm) in
/-- **The relayed forger followed by the program `P` on its output**: at most
`t + Q · (qPub + PS.q) + q` queries (the relayed adversary has width `1`). -/
noncomputable abbrev relayedForgerThen
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t) (pks : Fin n → B.PK)
    (i₁ : Fin n) (Q : ℕ) (ρ : Fin Q → PS.Coins) :
    QueryBoundedAdversary X Y (MURequest (SignOracle.ring B) n) (MUResponse B)
      ((KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) × R) (t + Q * (B.qPub + PS.q) + q) :=
  (relayedForger B PS adm A pks i₁ Q ρ).thenProgOut P q hP q fun _ => (one_mul q).le

/-- **The game at a fixed base component** (module docstring): for a base message binding the ring
(`hbind`), the forgery probability of an adversary of BKM06 Definition 7 with `Q` requests is at most
the average, over the users' key coins, a uniform base component `ω`, a uniform second component `h`
and the prover's coins, of the probability that the relayed forger followed by `P`, read at `ω`,
against the multi-user challenger at `ω` with `Q' ≥ Q` requests at the second component `h`, outputs
a ring signature verifying at `join sp ω h` and fresh for its multi-user requests, with `P`'s result
at that oracle. -/
theorem insiderForgeProb_le_split (hbind : B.BindsRing)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t) (i₁ : Fin n)
    (Q Q' : ℕ) (hQ : Q ≤ Q') :
    insiderForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
        ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          (((relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).restrictAt sp
            ω).transcriptLaw ((muChallenger (SignOracle.ring B) n keys Q').restrictAt sp ω)
            h).toOuterMeasure
            {x | ∃ p ∈ x, (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧
              MUFreshReq B (PS := PS) keys p.1.1 (p.2.map HistoryEntry.request) ∧
              p.1.2 = (P p.1.1).run (join sp ω h)} := by
  refine (insiderForgeProb_le_relayedForger hbind A i₁ Q Q' hQ).trans_eq ?_
  refine tsum_congr fun keys => congrArg _ ?_
  rw [tsum_uniform_split sp]
  refine tsum_congr fun ω => congrArg _ (tsum_congr fun h => congrArg _ ?_)
  refine Finset.sum_congr rfl fun ρ _ => congrArg _ ?_
  have hjb : base sp (join sp ω h) = ω := base_join sp ω h
  have hjp : prf sp (join sp ω h) = h := prf_join sp ω h
  have hres := Quantum.QueryBoundedAdversary.transcriptLaw_restrictAt_base sp
    (relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ)
    (muChallenger (SignOracle.ring B) n keys Q') (muChallenger_noAssign _ keys Q') (join sp ω h)
  rw [hjb, hjp] at hres
  rw [hres]
  unfold relayedForgerThen
  have ht := QueryBoundedAdversary.transcriptLaw_thenProgOut
    (relayedForger B PS adm A (fun i => B.pk (keys i)) i₁ Q ρ) P q hP q (fun _ => (one_mul q).le)
    (muChallenger (SignOracle.ring B) n keys Q') (muChallenger_noAssign _ keys Q') (join sp ω h)
  refine Eq.trans ?_ (congrArg (fun μ => PMF.toOuterMeasure μ _) ht).symm
  refine Eq.trans ?_ (PMF.toOuterMeasure_map_apply _ _ _).symm
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hv, hf⟩
    exact ⟨_, by rw [hp]; rfl, hv, hf, rfl⟩
  · rintro ⟨p, hp, hv, hf, -⟩
    rcases x with _ | p'
    · simp at hp
    · simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact ⟨p', rfl, hv, hf⟩

end Game

end Split

/-! ### The knowledge step at a fixed base component -/

section Knowledge

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {O : SignOracle B} [NeZero n] {X₀ Cl : Type}
  {V : NARG.QROM.Verifier m k e Cl X₀} {rel : Set (X₀ × RingWit B)}
  {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)} {β : ℕ → ℝ≥0∞}

/-- The output of the relayed forger followed by the program: a ring signature and a program
statement. -/
abbrev SplitOut {TB : BaseTypes} (B : BaseSigner (Bits m) Y N TB) {TPS : PSTypes} (PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS)
    (X₀ : Type) : Type :=
  (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) × X₀

/-- **The claim of a forgery with its program statement**: `cl x₀ π`, the default `c₀` without
one. -/
def splitClaim (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl) (o : SplitOut B PS X₀) : Cl :=
  (cl o.2 o.1.2.2.2).getD c₀

variable (sp) in
/-- **The test of the extraction at the base component `ω`**: the program statement is the one of
the forgery's statement at `ω`, the claim's statement is the program statement, and the forgery is
fresh for the first `Q'` logged multi-user requests. -/
def splitTest (hC : PS.CompiledBySplit sp V) (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl)
    (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} {A : AdaptiveIAlg shA (SplitOut B PS X₀)}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit}
    (v : ExtReg A C₁ (MURequest O n) (MUResponse B)) : Prop :=
  (extForgery v).2 = hC.stmtAt ω ⟨(extForgery v).1.1, (extForgery v).1.2.1, (extForgery v).1.2.2.1⟩ ∧
    V.stmt (splitClaim cl c₀ (extForgery v)) = (extForgery v).2 ∧
    MUFreshReq B (PS := PS) keys (extForgery v).1 ((requests (extLogs v)).take Q')

omit [Fintype Y] [DecidableEq Y] in
/-- **A verifying ring signature at an oracle with base component `ω`, with its program statement
at `ω`, has an accepted claim** against the second component. -/
theorem accepted_splitClaim (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (c₀ : Cl) (ω : Bits m → Y₁)
    (h : Bits m → XOut k e) {o : SplitOut B PS X₀}
    (hv : (ofBase B PS adm).verify (join sp ω h) o.1.1 o.1.2.1 o.1.2.2 = true)
    (hx : o.2 = hC.stmtAt ω ⟨o.1.1, o.1.2.1, o.1.2.2.1⟩) :
    V.Accepted (outEquiv k e ∘ h) (splitClaim cl c₀ o) ∧ V.stmt (splitClaim cl c₀ o) = o.2 := by
  obtain ⟨c, hc, hacc⟩ := hC.accepted_of_verify (join sp ω h) ⟨o.1.1, o.1.2.1, o.1.2.2.1⟩ o.1.2.2.2 hv
  rw [base_join] at hc
  rw [prf_join] at hacc
  have hcl' : splitClaim cl c₀ o = c := by
    rw [hcl, ← hx] at hc
    simp [splitClaim, Option.mem_def.1 hc]
  refine ⟨hcl' ▸ hacc, ?_⟩
  rw [hcl', hC.stmt_eq _ _ _ _ hc, hx]

omit [Fintype Y] in
/-- **The knowledge step at one table and a fixed base component** (the split form of
`tsum_le_extRun`): for a proof system compiled by `V` at each base component (`hC`) whose claims
factor through the program statement (`hcl`), and a knowledge bound for `rel` (`K`), averaged over
the second component `h`, the probability that the forger holding a table, read at `ω`, against the
inert challenger, outputs a ring signature verifying at `join sp ω h`, fresh for its logged
multi-user requests, with its program statement at `ω`, is at most the probability that its
extraction run extracts a witness for the claim with the test passing, plus the knowledge error. -/
theorem tsum_le_extRun_split (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (c₀ : Cl) (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (A : AdaptiveIAlg shA (SplitOut B PS X₀))
    (tab : A.OuterTab (MURequest O n) (MUResponse B))
    (d₀ : ExtReg A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (MURequest O n) (MUResponse B))
    {t' : ℕ} (ht : A.width * (A.budget + A.post) ≤ t') :
    ∑' h, PMF.uniformOfFintype (Bits m → XOut k e) h *
      (((A.absorbTab (muRelayAt O keys i₂) tab).toKindAlg.composeBothOut
        (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw
        h).toOuterMeasure
        {o | ∃ v ∈ o, (fun w => (ofBase B PS adm).verify (join sp ω h) (extForgery w).1.1
          (extForgery w).1.2.1 (extForgery w).1.2.2 = true ∧
          MUFreshReq B (PS := PS) keys (extForgery w).1 ((requests (extLogs w)).take Q') ∧
          (extForgery w).2 = hC.stmtAt ω ⟨(extForgery w).1.1, (extForgery w).1.2.1,
            (extForgery w).1.2.2.1⟩)
          (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
            (muRelayAt O keys i₂) tab v)} ≤
      simProb (outEquiv k e) (extRun (outEquiv k e) A
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
          (muRelayAt O keys i₂)
          (SPBCS.QROM.expansionVia V fun v => splitClaim cl c₀ (extForgery v)) V.kq d₀ tab)
        (fun v D => splitTest sp hC cl c₀ ω keys Q' v ∧
          NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery v))) D) +
        V.knowledgeError β (t' + V.kq) := by
  have hK := Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound_defaultR K
    (A.absorbTab (muRelayAt O keys i₂) tab)
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
    ((fun v => splitClaim cl c₀ (extForgery v)) ∘
      dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
        tab)
    (fun w => splitTest sp hC cl c₀ ω keys Q' (dropTabCW A
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂) tab w))
    (insertTab A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab d₀) ht
  have hE := Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_drop (V := V)
    (((A.absorbTab (muRelayAt O keys i₂) tab).toTPKindAlg.composeBothOut
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).toQueryAlgCoh)
    (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab)
    (insertTab A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab d₀)
    (extOut A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂) d₀
      tab) (fun o => by cases o <;> rfl) (fun v => splitClaim cl c₀ (extForgery v)) V.kq
    (fun v D => splitTest sp hC cl c₀ ω keys Q' v ∧
      NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery v))) D)
  have hq : (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q').Q *
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q').q = 0 :=
    Nat.mul_zero _
  rw [hq, Nat.add_zero] at hK
  refine le_trans (ENNReal.tsum_le_tsum fun h => mul_le_mul' le_rfl
    (MeasureTheory.measure_mono fun o ho => ?_)) (hK.trans_eq (congrArg (· + _) hE))
  obtain ⟨v, hv, hver, hf, hx⟩ := ho
  obtain ⟨hacc, hst⟩ := accepted_splitClaim (adm := adm) hC hcl c₀ ω h hver hx
  exact ⟨v, hv, hacc, hx, hst, hf⟩

/-- **Transcripts against the restricted multi-user challenger as runs of the table form** (the
split form of `transcriptLaw_relayedForger_eq`): for a signing oracle reading only the base
component, an event of the output and the multi-user requests of an adversary of the oracle
`Bits m → XOut k e` against the multi-user challenger at `ω`, at the second component `h`, has the
average, over the auxiliary input and the challenger's coins, of the probability that the adversary
holding the table at the coins, against the inert challenger, ends with an output and logs of that
kind. -/
theorem transcriptLaw_restrictAt_eq_absorbTab (hO : O.ReadsBase sp) {Ot : Type} {t : ℕ}
    (𝒜 : QueryBoundedAdversary (Bits m) (XOut k e) (MURequest O n) (MUResponse B) Ot t)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ) (ω : Bits m → Y₁) (h : Bits m → XOut k e)
    (E : Ot → List (MURequest O n) → Prop) :
    (𝒜.transcriptLaw ((muChallenger O n keys Q').restrictAt sp ω) h).toOuterMeasure
        {x | ∃ p ∈ x, E p.1 (p.2.map HistoryEntry.request)} =
      ∑' a, 𝒜.aux a * ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        ((((𝒜.alg a).absorbTab (muRelayAt O keys i₂)
            (muTabAt sp (𝒜.alg a) ω keys Q' c)).toKindAlg.composeBothOut
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw h).toOuterMeasure
          {o | ∃ v ∈ o, (fun w => E (extForgery w) ((requests (extLogs w)).take Q'))
            (dropTabCW (𝒜.alg a) (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
              (muRelayAt O keys i₂) (muTabAt sp (𝒜.alg a) ω keys Q' c) v)} := by
  simp only [QueryBoundedAdversary.transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => congrArg _ ?_
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine Eq.trans ?_ (toOuterMeasure_outLaw_muChallenger_restrictAt_eq_absorbTab sp hO
    (𝒜.alg a) ω keys i₂ Q' h
    (fun d lg => E ((𝒜.alg a).out d.1.1.1) ((requests lg).take Q')))
  refine congrArg _ (Set.ext fun o => exists_congr fun v => and_congr_right fun _ => ?_)
  dsimp only
  rw [AdaptiveIAlg.map_request_history]
  rfl

end Knowledge

/-! ### The chain to the extraction runs -/

section Chain

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] [NeZero n] {X₀ Cl : Type} {V : NARG.QROM.Verifier m k e Cl X₀}
  {rel : Set (X₀ × RingWit B)} {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞} {t : ℕ}

variable (sp B PS adm) in
/-- **The relayed forger followed by `P`, read at the base component `ω`**, at the auxiliary value
`a`: an adversary of the oracle `Bits m → XOut k e`. -/
noncomputable abbrev splitAlg {X₀ : Type}
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (pks : Fin n → B.PK) (i₁ : Fin n) (Q : ℕ) (ρ : Fin Q → PS.Coins) (ω : Bits m → Y₁)
    (a : ((relayedForgerThen B PS adm P q hP A pks i₁ Q ρ).restrictAt sp ω).Aux) :=
  ((relayedForgerThen B PS adm P q hP A pks i₁ Q ρ).restrictAt sp ω).alg a

/-- **The default output of the extraction run** of an adversary of the oracle
`Bits m → XOut k e` with requests to the multi-user challenger: that of its run with the empty
table. -/
noncomputable abbrev splitDefault {O : SignOracle B} {Ot : Type} (Q' : ℕ) (pk₀ : B.PK) (i₂ : Fin n)
    {shA' : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (A' : AdaptiveIAlg shA' Ot) :
    ExtReg A' (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (MURequest O n) (MUResponse B) :=
  dropTabCW A' (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muTwoRelay O n pk₀ i₂)
    (tab₀ A') (((A'.absorbTab (muTwoRelay O n pk₀ i₂) (tab₀ A')).toTPKindAlg.composeBothOut
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id)).defaultOut

/-- **The game at a fixed base component up to the extraction runs** (the step after
`insiderForgeProb_le_split`, for any signing oracle reading only the base component, `hO`): for a
proof system compiled by `V` at each base component (`hC`) whose claims factor through the program
statement (`hcl`), a knowledge bound for `rel` (`K`), a program `P` computing the program statement
of a forgery at the base component of the oracle (`hPst`) and a family `𝒜 keys ρ` of adversaries with
at most `t'` queries, the average, over the users' key coins, uniform components `ω` and `h` and the
prover's coins, of the probability that `𝒜 keys ρ` read at `ω` against the multi-user challenger at
`ω` outputs a ring signature verifying at `join sp ω h`, fresh for its multi-user requests, with
`P`'s result at that oracle, is at most the average, over the key coins, `ω`, the prover's coins,
the auxiliary input and the challenger's coins `c`, of the probability that the extraction run of
`𝒜 keys ρ` read at `ω`, holding the table of the challenger's replies at `ω` and `c`, extracts a
witness with the test passing, plus the knowledge error at `t' + kq` queries. -/
theorem forgeSum_le_extRun_split {O : SignOracle B} (hO : O.ReadsBase sp)
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (c₀ : Cl) (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩) {Q t' : ℕ}
    (𝒜 : (Fin n → B.KeyCoins) → (Fin Q → PS.Coins) →
      QueryBoundedAdversary (Bits m) Y (MURequest O n) (MUResponse B) (SplitOut B PS X₀) t')
    (i₂ : Fin n) (Q' : ℕ) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω * ∑' h, PMF.uniformOfFintype (Bits m → XOut k e) h *
        ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          (((𝒜 keys ρ).restrictAt sp ω).transcriptLaw ((muChallenger O n keys Q').restrictAt sp ω)
            h).toOuterMeasure
            {x | ∃ p ∈ x, (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧
              MUFreshReq B (PS := PS) keys p.1.1 (p.2.map HistoryEntry.request) ∧
              p.1.2 = (P p.1.1).run (join sp ω h)} ≤
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑' ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
            ∑' a, ((𝒜 keys ρ).restrictAt sp ω).aux a *
              ∑' c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
                simProb (outEquiv k e) (extRun (outEquiv k e) (((𝒜 keys ρ).restrictAt sp ω).alg a)
                    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
                    (muRelayAt O keys i₂)
                    (SPBCS.QROM.expansionVia V fun (v : ExtReg (((𝒜 keys ρ).alg a).restrictAt sp 0)
                      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (MURequest O n)
                        (MUResponse B)) => splitClaim cl c₀ (extForgery v)) V.kq
                    (splitDefault Q' (B.pk (keys 0)) i₂ (((𝒜 keys ρ).alg a).restrictAt sp 0))
                    (muTabAt sp (((𝒜 keys ρ).restrictAt sp ω).alg a) ω keys Q' c))
                  (fun (v : ExtReg (((𝒜 keys ρ).alg a).restrictAt sp 0)
                      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (MURequest O n)
                        (MUResponse B)) D => splitTest sp hC cl c₀ ω keys Q' v ∧
                    NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery v))) D) +
        V.knowledgeError β (t' + V.kq) := by
  refine Ring.tsum_mul_le_tsum_mul_add _ fun keys => Ring.tsum_mul_le_tsum_mul_add _ fun ω => ?_
  -- the transcripts as runs of the table form
  have htab : ∀ h ρ, (((𝒜 keys ρ).restrictAt sp ω).transcriptLaw
      ((muChallenger O n keys Q').restrictAt sp ω) h).toOuterMeasure
      {x | ∃ p ∈ x, (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧
        MUFreshReq B (PS := PS) keys p.1.1 (p.2.map HistoryEntry.request) ∧
        p.1.2 = (P p.1.1).run (join sp ω h)} =
      ∑' a, ((𝒜 keys ρ).restrictAt sp ω).aux a * ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        ((((((𝒜 keys ρ).restrictAt sp ω).alg a).absorbTab
            (muRelayAt O keys i₂) (muTabAt sp (((𝒜 keys ρ).restrictAt sp ω).alg a) ω keys Q'
              c)).toKindAlg.composeBothOut
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw
          h).toOuterMeasure
          {o | ∃ v ∈ o, (fun w => (ofBase B PS adm).verify (join sp ω h) (extForgery w).1.1
              (extForgery w).1.2.1 (extForgery w).1.2.2 = true ∧
              MUFreshReq B (PS := PS) keys (extForgery w).1 ((requests (extLogs w)).take Q') ∧
              (extForgery w).2 = (P (extForgery w).1).run (join sp ω h))
            (dropTabCW (((𝒜 keys ρ).restrictAt sp ω).alg a)
              (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
              (muRelayAt O keys i₂) (muTabAt sp (((𝒜 keys ρ).restrictAt sp ω).alg a) ω keys Q'
                c) v)} := fun h ρ =>
    transcriptLaw_restrictAt_eq_absorbTab hO _ keys i₂ Q' ω h
      fun (o : SplitOut B PS X₀) (rs : List (MURequest O n)) =>
      (ofBase B PS adm).verify (join sp ω h) o.1.1 o.1.2.1 o.1.2.2 = true ∧
        MUFreshReq B (PS := PS) keys o.1 rs ∧ o.2 = (P o.1).run (join sp ω h)
  simp only [htab]
  simp only [hPst]
  -- the second component's average innermost
  simp only [← tsum_fintype (L := .unconditional _)]
  rw [tsum_mul_tsum_mul_comm]
  refine Ring.tsum_mul_le_tsum_mul_add _ fun ρ => ?_
  rw [tsum_mul_tsum_mul_comm]
  refine Ring.tsum_mul_le_tsum_mul_add _ fun a => ?_
  rw [tsum_mul_tsum_mul_comm]
  refine Ring.tsum_mul_le_tsum_mul_add _ fun c => ?_
  exact tsum_le_extRun_split hC hcl K c₀ ω keys i₂ Q' _ _ _
    (((𝒜 keys ρ).restrictAt sp ω).queries_le a)

/-- **The game up to the extraction runs at a fixed base component** (the split form of
`forgeProb_le_extRun`): for a base message binding the ring (`hbind`), a base signer reading only
the base component (`hB`), a proof system compiled by `V` at each base component (`hC`) whose
claims factor through the program statement (`hcl`), a knowledge bound for `rel` (`K`), and a
program `P` computing the program statement of a forgery at the base component of the oracle
(`hPst`), the forgery probability of an adversary of BKM06 Definition 7 is at most the average,
over the users' key coins, a uniform base component `ω`, the prover's coins, the auxiliary input and
the multi-user challenger's coins `c`, of the probability that the extraction run of the relayed
forger followed by `P`, read at `ω`, holding the table of the challenger's replies at `ω` and `c`,
extracts a witness with the test passing, plus the knowledge error. -/
theorem insiderForgeProb_le_extRun_split (hbind : B.BindsRing) (hB : B.ReadsOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (c₀ : Cl) (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q Q' : ℕ) (hQ : Q ≤ Q') :
    insiderForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
        ∑' ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          ∑' a, ((relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).restrictAt
              sp ω).aux a *
            ∑' c, PMF.uniformOfFintype (Fin Q' → (SignOracle.ring B).Coins) c *
              simProb (outEquiv k e) (extRun (outEquiv k e)
                  (splitAlg sp B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ ω a)
                  (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
                  (muRelayAt (SignOracle.ring B) keys i₂)
                  (SPBCS.QROM.expansionVia V fun (v : ExtReg
                    (((relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).alg
                      a).restrictAt sp 0)
                    (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
                    (MURequest (SignOracle.ring B) n) (MUResponse B)) =>
                      splitClaim cl c₀ (extForgery v)) V.kq
                  (splitDefault Q' (B.pk (keys 0)) i₂
                    (((relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).alg
                      a).restrictAt sp 0))
                  (muTabAt sp (splitAlg sp B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ ω a) ω
                    keys Q' c))
                (fun (v : ExtReg
                    (((relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).alg
                      a).restrictAt sp 0)
                    (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ring B) n) Q')
                    (MURequest (SignOracle.ring B) n) (MUResponse B)) D =>
                  splitTest sp hC cl c₀ ω keys Q' v ∧
                  NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery v))) D) +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have hg := forgeSum_le_extRun_split (adm := adm) (O := SignOracle.ring B) (Q := Q)
    (t' := t + Q * (B.qPub + PS.q) + q) (SignOracle.readsBase_ring hB) hC hcl K c₀ P hPst
    (fun keys ρ => relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ) i₂ Q'
  have h1 := insiderForgeProb_le_split sp P q hP hbind A i₁ Q Q' hQ
  refine le_trans h1 (le_trans (le_of_eq ?_) (le_trans hg (le_of_eq ?_)))
  · with_reducible rfl
  · with_reducible rfl

end Chain

/-! ### The extracted witness as a forgery -/

section Win

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] {Y : Type} [AddGroup Y] [Fintype Y]
  [DecidableEq Y] {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {O : SignOracle B} [NeZero n] {X₀ Cl : Type}
  {V : NARG.QROM.Verifier m k e Cl X₀}

variable (B) in
/-- **The decoding of a witness** `(i, σ)` for the ring statement `(R, m, y)`: the key at position
`i`, the base message `bmsg R m` and `σ`; none if `i` is outside the ring. -/
def splitDecode (x : RingStmt B) (w : RingWit B) : Option (B.PK × B.BMsg × B.BSig) :=
  if h : w.idx < x.ring.1.length then some (x.ring.1[w.idx], B.bmsg x.ring x.msg, w.sig) else none

variable (B PS V) in
/-- **The forgery read from the extraction run at a fixed base component**: the decoding of a
witness in `rel` among those `ext` returns from the measured database for the claim's statement, at
the forgery's ring statement; `f₀` if there is none. -/
noncomputable def splitReadout (cl : X₀ → PS.Proof → Option Cl) (c₀ : Cl) (rel : Set (X₀ × RingWit B))
    (ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)) (f₀ : B.PK × B.BMsg × B.BSig)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} {A : AdaptiveIAlg shA (SplitOut B PS X₀)}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit} {kq : ℕ}
    (o : BaseGame.Tuple (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B)) kq × DB (Bits m) (Out k e)) :
    B.PK × B.BMsg × B.BSig :=
  open Classical in
  if h : ∃ w ∈ ext (V.stmt (splitClaim cl c₀ (extForgery o.1.out))) o.2,
      (V.stmt (splitClaim cl c₀ (extForgery o.1.out)), w) ∈ rel then
    (splitDecode B ⟨(extForgery o.1.out).1.1, (extForgery o.1.out).1.2.1,
      (extForgery o.1.out).1.2.2.1⟩ h.choose).getD f₀
  else f₀

omit [Fintype Y] [DecidablePred adm] [NeZero n] in
/-- **An output passing the extraction's test at the base component `ω` with a witness in `rel`
reads as a forgery** of MU-EUF-CMA^corr for multi-user requests `mrs` at every oracle `H` with
base component `ω`, when every witness of `rel` for the program statement of a ring statement at `ω`
is one of the ring relation at `H` (`hrel`), the forger's logs have at most `Q'` requests (`hlen`)
and every corrupting or signing request of `mrs` is one of the forger's logged requests (`hmrs`). -/
theorem forgesReq_splitReadout (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (c₀ : Cl) {rel : Set (X₀ × RingWit B)}
    {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)} (f₀ : B.PK × B.BMsg × B.BSig)
    (keys : Fin n → B.KeyCoins) (ω : Bits m → Y₁) (H : Bits m → Y)
    (hrel : ∀ x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm H x w) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} {A : AdaptiveIAlg shA (SplitOut B PS X₀)}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit} {kq : ℕ}
    (o : BaseGame.Tuple (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B)) kq × DB (Bits m) (Out k e))
    (mrs : List (MURequest O n))
    (hlen : (requests (extLogs o.1.out)).length ≤ Q')
    (hmrs : ∀ r ∈ mrs, (∀ i, r = .corrupt i → r ∈ requests (extLogs o.1.out)) ∧
      ∀ i sm, r = .sign i sm → r ∈ requests (extLogs o.1.out))
    (ht : splitTest sp hC cl c₀ ω keys Q' o.1.out)
    (hx : NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery o.1.out))) o.2) :
    ForgesReq keys H (splitReadout B PS V cl c₀ rel ext f₀ o) mrs := by
  classical
  obtain ⟨hx₀, hst, hfr⟩ := ht
  rw [List.take_of_length_le hlen] at hfr
  have hx' : ∃ w ∈ ext (V.stmt (splitClaim cl c₀ (extForgery o.1.out))) o.2,
      (V.stmt (splitClaim cl c₀ (extForgery o.1.out)), w) ∈ rel := hx
  have hrd : splitReadout B PS V cl c₀ rel ext f₀ o =
      (splitDecode B ⟨(extForgery o.1.out).1.1, (extForgery o.1.out).1.2.1,
        (extForgery o.1.out).1.2.2.1⟩ hx'.choose).getD f₀ := by
    rw [splitReadout, dite_eq_left_of_eq_true (eq_true hx')]
  obtain ⟨-, hw⟩ := hx'.choose_spec
  rw [hrd]
  generalize hx'.choose = w at hw ⊢
  rw [hst, hx₀] at hw
  have hR := hrel _ _ hw
  have hi := hR.idx_lt
  rw [splitDecode, dite_eq_left_of_eq_true (eq_true hi), Option.getD_some]
  refine ⟨hR.verify_eq, ?_⟩
  have hmem : (extForgery o.1.out).1.1.1[w.idx] ∈ (extForgery o.1.out).1.1.1 :=
    List.getElem_mem hi
  obtain ⟨i, hpk, hc⟩ := hfr.1 _ hmem
  refine ⟨i, hpk, fun hm => hc ((hmrs _ hm).1 i rfl), fun sm hm hb => ?_⟩
  exact hfr.2 i sm ((hmrs _ hm).2 i sm rfl) (hpk ▸ hmem) hb

end Win

end GordieHowe
