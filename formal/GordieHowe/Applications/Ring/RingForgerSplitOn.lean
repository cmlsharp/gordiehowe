-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplitHeadline
public import GordieHowe.Model.RingSignature.WithVerify

@[expose] public section

/-!
# Forgeries in an event without witnesses

The split chain of `GordieHowe/Applications/Ring/RingForgerSplitChain.lean` restricted to the
forgeries in an event `E` of the forgery (`forgeProbOn`). When no witness of the relation `rel` of
the knowledge bound exists for the program statement of a forgery in `E`, the extraction run never
extracts, and the forgery probability in `E` is at most the knowledge error. On the empty ring the
ring relation has no witness (`RingRel.idx_lt`), so for witnesses of `rel` that are witnesses of
the ring relation, the forgery probability on the empty ring is at most the knowledge error.

- `forgeProbOn_le_relayedForger`, `forgeProbOn_le_split`: the game's forgeries in `E` through the
  relayed forger, and at a fixed base component (the restricted forms of
  `insiderForgeProb_le_relayedForger` and `insiderForgeProb_le_split`, without freshness, so for
  any base message).
- `tsum_le_knowledgeError_split_on`: the knowledge step at one table and a fixed base component,
  for forgeries in an event without witnesses.
- `forgeSum_le_knowledgeError_split_on`: the averaged knowledge step.
- `forgeProbOn_le_knowledgeError_split`: the forgery probability in an event without witnesses is
  at most the knowledge error.
- `ringStmt_ring_ne_nil_of_ringRel`: a statement with a ring-relation witness has a nonempty ring.
- `forgeProbOn_nil_le_knowledgeError_split`: the forgery probability on the empty ring is at most
  the knowledge error.
-/

namespace GordieHowe.RingSignature

open Quantum Signature
open scoped ENNReal

section Game

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N T RMsg} {TPS : PSTypes} [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ}
  [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [NeZero n] {t : ℕ}

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins]
  [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins]
  [Nonempty T.Coins]

/-- **The game's forgeries in an event `E` through the relayed forger** (the restricted form of
`insiderForgeProb_le_relayedForger` without freshness, for any base message): the forgery
probability in `E` is at most the average, over the users' key coins, the oracle and the prover's
coins, of the probability that the relayed forger against the multi-user challenger with `Q' ≥ Q`
requests outputs a ring signature in `E` that verifies. -/
theorem forgeProbOn_le_relayedForger
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t)
    (E : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → Prop) (i₁ : Fin n)
    (Q Q' : ℕ) (hQ : Q ≤ Q') :
    forgeProbOn A Q E ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' H, PMF.uniformOfFintype (X → Y) H * ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        ((relayedForger B PS adm A (fun i => B.pk (keys i)) i₁ Q ρ).transcriptLaw
          (muChallenger (SignOracle.ring B) n keys Q') H).toOuterMeasure
          {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧ E p.1} := by
  simp only [forgeProbOn, unforgeLaw, runLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_)
  have hsub : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (X → Y) ×
      Option ((KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) ×
        UnforgeHist (S := ofBase B PS adm) n (SideOracle.none _)) |
      ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2 ∧ E p.1} ⊆
      {x | ∃ p ∈ x, (fun o (_ : List (UnforgeRequest n (SideOracle.none (ofBase B PS adm)))) =>
        (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true ∧ E o) p.1
          (p.2.map HistoryEntry.request)} := by
    rintro x ⟨p, hp, hf, hE⟩
    exact ⟨p, hp, hf.verify_eq, hE⟩
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine le_of_eq_of_le (transcriptLaw_numRelay (A (fun i => B.pk (keys i), ())) keys Q H
    (fun o _ => (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true ∧ E o)) ?_
  refine Finset.sum_le_sum fun ρ _ => mul_le_mul' le_rfl ?_
  refine ((A (fun i => B.pk (keys i), ())).absorbQB (numRelay B PS adm n (SideOracle.none _) Q ρ)
    (numRelay_route_injective Q ρ)).transcriptLaw_le_relay
    (forgerRelay B PS adm (fun i => B.pk (keys i)) i₁)
    (numChallenger B PS adm n (SideOracle.none _) keys Q)
    (muChallenger (SignOracle.ring B) n keys Q') _ (relaysChallenger_forgerRelay keys i₁ hQ) H _ _
    ?_
  exact fun _ _ _ h _ => h

end Game

/-- **A statement with a witness of the ring relation has a nonempty ring** (`RingRel.idx_lt`). -/
theorem ringStmt_ring_ne_nil_of_ringRel {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes}
    {RMsg : Type}
    {B : BaseSigner X Y N T RMsg}
    {adm : KeyRing B.PK N → Prop} {H : X → Y} {x : RingStmt B} {w : RingWit B}
    (h : RingRel B adm H x w) : x.ring.1 ≠ [] := fun hx => by
  have := h.idx_lt
  rw [show x.ring.keys = [] from hx] at this
  exact Nat.not_lt_zero _ this

end GordieHowe.RingSignature

namespace GordieHowe

open Quantum Signature RingSignature RingSignature.OracleSplit QROM IOP
open scoped ENNReal

section Split

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [Nonempty Y₂] {N n t : ℕ} [NeZero n] {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N T RMsg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop} [DecidablePred adm]
  {R : Type} (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg X Y R) (q : ℕ)
  (hP : ∀ o, (P o).QueriesLE q)

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins]
  [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins]
  [Nonempty T.Coins]

/-- **The game's forgeries in an event `E` at a fixed base component** (the restricted form of
`insiderForgeProb_le_split` without freshness, for any base message): the forgery probability in
`E` is at most the average, over the users' key coins, uniform components `ω` and `h` and the
prover's coins, of the probability that the relayed forger followed by `P`, read at `ω`, against
the multi-user challenger at `ω` with `Q' ≥ Q` requests, outputs a ring signature in `E` verifying
at `join sp ω h`, with `P`'s result at that oracle. -/
theorem forgeProbOn_le_split
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t)
    (E : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → Prop) (i₁ : Fin n)
    (Q Q' : ℕ) (hQ : Q ≤ Q') :
    forgeProbOn A Q E ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
        ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          (((relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).restrictAt sp
            ω).transcriptLaw ((muChallenger (SignOracle.ring B) n keys Q').restrictAt sp ω)
            h).toOuterMeasure
            {x | ∃ p ∈ x,
              (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧ E p.1.1 ∧
              p.1.2 = (P p.1.1).run (join sp ω h)} := by
  refine (forgeProbOn_le_relayedForger A E i₁ Q Q' hQ).trans_eq ?_
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
  · rintro ⟨p, hp, hv, hE⟩
    exact ⟨_, by rw [hp]; rfl, hv, hE, rfl⟩
  · rintro ⟨p, hp, hv, hE, -⟩
    rcases x with _ | p'
    · simp at hp
    · simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact ⟨p', rfl, hv, hE⟩

end Split

section Knowledge

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] {Y : Type} [AddGroup Y] [Fintype Y]
  [DecidableEq Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits m) Y N T RMsg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {O : SignOracle B.core} [NeZero n] {X₀ Cl : Type}
  {V : NARG.QROM.Verifier m k e Cl X₀} {rel : Set (X₀ × RingWit B)}
  {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)} {β : ℕ → ℝ≥0∞}

variable [Fintype O.SMsg] [DecidableEq O.SMsg]

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]

omit [Fintype Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] in
/-- **The knowledge step at one table and a fixed base component for forgeries in an event without
witnesses** (the restricted form of `tsum_le_extRun_split`): for a proof system compiled by `V` at
each base component (`hC`) whose claims factor through the program statement (`hcl`), a knowledge
bound for `rel` (`K`), and an event `E` of the forgery under which the program statement at `ω`
has no witness in `rel` (`hE`), averaged over the second component `h`, the probability that the
forger holding a table, read at `ω`, against the inert challenger, outputs a ring signature in `E`
verifying at `join sp ω h`, with its program statement at `ω`, is at most the knowledge error. -/
theorem tsum_le_knowledgeError_split_on (hC : PS.CompiledBySplit sp V)
    {cl : X₀ → PS.Proof → Option Cl} (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π)
    (K : V.KnowledgeBound rel ext β) (c₀ : Cl) (ω : Bits m → Y₁)
    (E : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → Prop)
    (hE : ∀ o w, E o → (hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩, w) ∉ rel)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} (A : AdaptiveIAlg shA (SplitOut B PS X₀))
    (tab : A.OuterTab (MURequest O n) (MUResponse B.core))
    {t' : ℕ} (ht : A.width * (A.budget + A.post) ≤ t') :
    ∑' h, PMF.uniformOfFintype (Bits m → XOut k e) h *
      (((A.absorbTab (muRelayAt O keys i₂) tab).toKindAlg.composeBothOut
        (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw
        h).toOuterMeasure
        {o | ∃ v ∈ o, (fun w => (ofBase B PS adm).verify (join sp ω h) (extForgery w).1.1
          (extForgery w).1.2.1 (extForgery w).1.2.2 = true ∧ E (extForgery w).1 ∧
          (extForgery w).2 = hC.stmtAt ω ⟨(extForgery w).1.1, (extForgery w).1.2.1,
            (extForgery w).1.2.2.1⟩)
          (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
            (muRelayAt O keys i₂) tab v)} ≤
      V.knowledgeError β (t' + V.kq) := by
  have hK := Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound_defaultR K
    (A.absorbTab (muRelayAt O keys i₂) tab)
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
    ((fun v => splitClaim cl c₀ (extForgery v)) ∘
      dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
        tab)
    (fun w => (fun v => (extForgery v).2 = hC.stmtAt ω ⟨(extForgery v).1.1, (extForgery v).1.2.1,
        (extForgery v).1.2.2.1⟩ ∧ V.stmt (splitClaim cl c₀ (extForgery v)) = (extForgery v).2 ∧
        E (extForgery v).1)
      (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
        tab w))
    (insertTab A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
        (muRelayAt O keys i₂) tab
        (((A.absorbTab (muRelayAt O keys i₂) tab).toTPKindAlg.composeBothOut
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id)).defaultOut)) ht
  have hq : (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q').Q *
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q').q = 0 :=
    Nat.mul_zero _
  rw [hq, Nat.add_zero] at hK
  refine le_trans (ENNReal.tsum_le_tsum fun h => mul_le_mul' le_rfl
    (MeasureTheory.measure_mono fun o ho => ?_)) (hK.trans ((add_le_add (le_of_eq
      (simProb_eq_zero _ _ fun y D => ?_)) le_rfl).trans (zero_add _).le))
  · obtain ⟨v, hv, hver, hEv, hx⟩ := ho
    obtain ⟨hacc, hst⟩ := accepted_splitClaim (adm := adm) hC hcl c₀ ω h hver hx
    exact ⟨v, hv, hacc, hx, hst, hEv⟩
  · rintro ⟨⟨hx, hst, hEy⟩, w, -, hw⟩
    refine hE _ w hEy ?_
    dsimp only [Function.comp] at hw
    rw [hst, hx] at hw
    exact hw

end Knowledge

section Chain

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits m) Y N T RMsg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] [NeZero n] {X₀ Cl : Type} {V : NARG.QROM.Verifier m k e Cl X₀}
  {rel : Set (X₀ × RingWit B)} {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞} {t : ℕ}

/-- An average of values at most `c` is at most `c`. -/
private theorem tsum_pmf_mul_le {α : Type*} (μ : PMF α) {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, f a ≤ c) : ∑' a, μ a * f a ≤ c :=
  (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)).trans
    (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul])

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **The averaged knowledge step for forgeries in an event without witnesses** (the restricted
form of `forgeSum_le_extRun_split`, for any signing oracle reading only the base component, `hO`):
for a proof system compiled by `V` at each base component (`hC`) whose claims factor through the
program statement (`hcl`), a knowledge bound for `rel` (`K`), a program `P` computing the program
statement of a forgery at the base component of the oracle (`hPst`), an event `E` of the forgery
under which the program statement has no witness in `rel` at any base component (`hE`), and a
family `𝒜 keys ρ` of adversaries with at most `t'` queries, the average, over the users' key coins,
uniform components `ω` and `h` and the prover's coins, of the probability that `𝒜 keys ρ` read at
`ω` against the multi-user challenger at `ω` outputs a ring signature in `E` verifying at
`join sp ω h`, with `P`'s result at that oracle, is at most the knowledge error at `t' + kq`
queries. -/
theorem forgeSum_le_knowledgeError_split_on {O : SignOracle B.core} [Fintype O.SMsg] [DecidableEq O.SMsg]
    [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] (hO : O.ReadsBase sp)
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (c₀ : Cl) (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (E : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → Prop)
    (hE : ∀ ω o w, E o → (hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩, w) ∉ rel) {Q t' : ℕ}
    (𝒜 : (Fin n → B.KeyCoins) → (Fin Q → PS.Coins) →
      QueryBoundedAdversary (Bits m) Y (MURequest O n) (MUResponse B.core) (SplitOut B PS X₀) t')
    (i₂ : Fin n) (Q' : ℕ) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
        ∑' h, PMF.uniformOfFintype (Bits m → XOut k e) h *
        ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          (((𝒜 keys ρ).restrictAt sp ω).transcriptLaw ((muChallenger O n keys Q').restrictAt sp ω)
            h).toOuterMeasure
            {x | ∃ p ∈ x,
              (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧ E p.1.1 ∧
              p.1.2 = (P p.1.1).run (join sp ω h)} ≤
      V.knowledgeError β (t' + V.kq) := by
  refine tsum_pmf_mul_le _ fun keys => tsum_pmf_mul_le _ fun ω => ?_
  -- the transcripts as runs of the table form
  have htab : ∀ h ρ, (((𝒜 keys ρ).restrictAt sp ω).transcriptLaw
      ((muChallenger O n keys Q').restrictAt sp ω) h).toOuterMeasure
      {x | ∃ p ∈ x, (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧
        E p.1.1 ∧
        p.1.2 = (P p.1.1).run (join sp ω h)} =
      ∑' a, ((𝒜 keys ρ).restrictAt sp ω).aux a * ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        ((((((𝒜 keys ρ).restrictAt sp ω).alg a).absorbTab
            (muRelayAt O keys i₂) (muTabAt sp (((𝒜 keys ρ).restrictAt sp ω).alg a) ω keys Q'
              c)).toKindAlg.composeBothOut
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw
          h).toOuterMeasure
          {o | ∃ v ∈ o, (fun w => (ofBase B PS adm).verify (join sp ω h) (extForgery w).1.1
              (extForgery w).1.2.1 (extForgery w).1.2.2 = true ∧ E (extForgery w).1 ∧
              (extForgery w).2 = (P (extForgery w).1).run (join sp ω h))
            (dropTabCW (((𝒜 keys ρ).restrictAt sp ω).alg a)
              (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
              (muRelayAt O keys i₂) (muTabAt sp (((𝒜 keys ρ).restrictAt sp ω).alg a) ω keys Q'
                c) v)} := fun h ρ =>
    transcriptLaw_restrictAt_eq_absorbTab hO _ keys i₂ Q' ω h
      fun (o : SplitOut B PS X₀) (_ : List (MURequest O n)) =>
      (ofBase B PS adm).verify (join sp ω h) o.1.1 o.1.2.1 o.1.2.2 = true ∧ E o.1 ∧
        o.2 = (P o.1).run (join sp ω h)
  simp only [htab]
  simp only [hPst]
  -- the second component's average innermost
  simp only [← tsum_fintype (L := .unconditional _)]
  rw [tsum_mul_tsum_mul_comm]
  refine tsum_pmf_mul_le _ fun ρ => ?_
  rw [tsum_mul_tsum_mul_comm]
  refine tsum_pmf_mul_le _ fun a => ?_
  rw [tsum_mul_tsum_mul_comm]
  refine tsum_pmf_mul_le _ fun c => ?_
  exact tsum_le_knowledgeError_split_on hC hcl K c₀ ω E (hE ω) keys i₂ Q' _ _
    (((𝒜 keys ρ).restrictAt sp ω).queries_le a)

variable [Fintype RMsg] [DecidableEq RMsg] [Fintype T.Pub] [DecidableEq T.Pub]
  [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

/-- **The forgery probability in an event without witnesses is at most the knowledge error**: for
any base message, a base signer reading only the base component (`hB`), a
proof system compiled by `V` at each base component (`hC`) whose claims factor through the program
statement (`hcl`), a knowledge bound for `rel` (`K`), a program `P` with `q` queries computing the
program statement of a forgery (`hPst`), and an event `E` of the forgery under which the program
statement has no witness in `rel` at any base component (`hE`), the probability that an adversary
with at most `t` queries and `Q` requests forges in `E` is at most the knowledge error at
`t + Q · (qPub + PS.q) + q + kq` queries. -/
theorem forgeProbOn_le_knowledgeError_split (hB : B.ReadsOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (c₀ : Cl) (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (E : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → Prop)
    (hE : ∀ ω o w, E o → (hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩, w) ∉ rel)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t) (Q : ℕ) :
    forgeProbOn A Q E ≤ V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have h1 := forgeProbOn_le_split sp P q hP A E 0 Q Q le_rfl
  have hg := forgeSum_le_knowledgeError_split_on (adm := adm) (O := SignOracle.ring B) (Q := Q)
    (t' := t + Q * (B.qPub + PS.q) + q) (SignOracle.readsBase_ring hB) hC hcl K c₀ P hPst E hE
    (fun keys ρ => relayedForgerThen B PS adm P q hP A (fun i => B.pk (keys i)) 0 Q ρ) 0 Q
  exact le_trans h1 (le_trans (le_of_eq (by with_reducible rfl)) hg)

/-- **The forgery probability on the empty ring is at most the knowledge error**
(`forgeProbOn_le_knowledgeError_split` at the event that the ring is empty): for any base message,
a base signer reading only the base component (`hB`), a proof system
compiled by `V` at each base component (`hC`) whose claims factor through the program statement
(`hcl`), a knowledge bound for `rel` (`K`) whose witnesses for the program statement at a base
component are witnesses of the ring relation at every oracle with that base component (`hrel`),
and a program `P` with `q` queries computing the program statement of a forgery (`hPst`), the
probability that an adversary with at most `t` queries and `Q` requests forges on the empty ring is
at most the knowledge error at `t + Q · (qPub + PS.q) + q + kq` queries. -/
theorem forgeProbOn_nil_le_knowledgeError_split (hB : B.ReadsOnly (base sp))
    (hC : PS.CompiledBySplit sp V) {cl : X₀ → PS.Proof → Option Cl}
    (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π) (K : V.KnowledgeBound rel ext β)
    (hrel : ∀ ω h x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm (join sp ω h) x w)
    (c₀ : Cl) (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly (Bits m) Y) t) (Q : ℕ) :
    forgeProbOn A Q (fun o => o.1.1 = []) ≤
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) :=
  forgeProbOn_le_knowledgeError_split hB hC hcl K c₀ P q hP hPst _
    (fun ω _ w hnil hw => ringStmt_ring_ne_nil_of_ringRel (hrel ω (fun _ => 0) _ w hw) hnil) A Q

end Chain

end GordieHowe
