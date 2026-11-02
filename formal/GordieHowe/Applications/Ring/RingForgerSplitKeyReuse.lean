-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplitChain
public import GordieHowe.Applications.Ring.RingForgerKeyReuse

@[expose] public section

/-!
# The key-reuse game at a fixed base component, up to the extraction runs

The key-reuse form of `GordieHowe/Applications/Ring/RingForgerSplitChain.lean`: for a base signer
whose signer and ordinary signer read only the base component of an additive split
`sp : Y ≃+ Y₁ × Y₂`, the key-reuse game (`keyReuseForgeProb`, ring requests and base messages) is at
most an average over the base component of the extraction runs of the relayed forger
`relayedForgerStd` followed by a program `P`, read at that component, plus the knowledge error.

- `relayedForgerStdThen`: the relayed forger of the key-reuse game followed by `P` on its output.
- `keyReuseForgeProb_le_split`: the game at a fixed base component (the form of
  `insiderForgeProb_le_split`).
- `keyReuseForgeProb_le_extRun_split`: the game up to the extraction runs (the form of
  `insiderForgeProb_le_extRun_split`, by `forgeSum_le_extRun_split` with
  `SignOracle.readsBase_ringStd`).
-/

namespace GordieHowe

open Quantum Signature RingSignature RingSignature.OracleSplit QROM IOP
open scoped ENNReal

section Split

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [Nonempty Y₂] {N n t : ℕ} [NeZero n] {TB : BaseTypes} {B : BaseSigner X Y N TB}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop} [DecidablePred adm]
  {R : Type} (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg X Y R) (q : ℕ)
  (hP : ∀ o, (P o).QueriesLE q)

variable (B PS adm) in
/-- **The relayed forger of the key-reuse game followed by the program `P` on its output**: at most
`t + Q · (qPub + PS.q) + q` queries. -/
noncomputable abbrev relayedForgerStdThen
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly X Y) t) (pks : Fin n → B.PK)
    (i₁ : Fin n) (Q : ℕ) (ρ : Fin Q → PS.Coins) :
    QueryBoundedAdversary X Y (MURequest (SignOracle.ringStd B) n) (MUResponse B)
      ((KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) × R) (t + Q * (B.qPub + PS.q) + q) :=
  (relayedForgerStd B PS adm A pks i₁ Q ρ).thenProgOut P q hP q fun _ => (one_mul q).le

/-- **The key-reuse game at a fixed base component**: for a base message binding the ring
(`hbind`), the forgery probability of an adversary of the key-reuse game with `Q` requests is at
most the average, over the users' key coins, a uniform base component `ω`, a uniform second
component `h` and the prover's coins, of the probability that the relayed forger followed by `P`,
read at `ω`, against the multi-user challenger with the ring-aware and the ordinary signing oracle
at `ω` with `Q' ≥ Q` requests at the second component `h`, outputs a ring signature verifying at
`join sp ω h` and fresh for its multi-user requests, with `P`'s result at that oracle. -/
theorem keyReuseForgeProb_le_split (hbind : B.BindsRing)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly X Y) t) (i₁ : Fin n)
    (Q Q' : ℕ) (hQ : Q ≤ Q') :
    keyReuseForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
        ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          (((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ).restrictAt sp
            ω).transcriptLaw ((muChallenger (SignOracle.ringStd B) n keys Q').restrictAt sp ω)
            h).toOuterMeasure
            {x | ∃ p ∈ x, (ofBase B PS adm).verify (join sp ω h) p.1.1.1 p.1.1.2.1 p.1.1.2.2 = true ∧
              MUFreshReq B (PS := PS) keys p.1.1 (p.2.map HistoryEntry.request) ∧
              p.1.2 = (P p.1.1).run (join sp ω h)} := by
  refine (keyReuseForgeProb_le_relayedForgerStd hbind A i₁ Q Q' hQ).trans_eq ?_
  refine tsum_congr fun keys => congrArg _ ?_
  rw [tsum_uniform_split sp]
  refine tsum_congr fun ω => congrArg _ (tsum_congr fun h => congrArg _ ?_)
  refine Finset.sum_congr rfl fun ρ _ => congrArg _ ?_
  have hjb : base sp (join sp ω h) = ω := base_join sp ω h
  have hjp : prf sp (join sp ω h) = h := prf_join sp ω h
  have hres := Quantum.QueryBoundedAdversary.transcriptLaw_restrictAt_base sp
    (relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ)
    (muChallenger (SignOracle.ringStd B) n keys Q') (muChallenger_noAssign _ keys Q')
    (join sp ω h)
  rw [hjb, hjp] at hres
  rw [hres]
  unfold relayedForgerStdThen
  have ht := QueryBoundedAdversary.transcriptLaw_thenProgOut
    (relayedForgerStd B PS adm A (fun i => B.pk (keys i)) i₁ Q ρ) P q hP q
    (fun _ => (one_mul q).le) (muChallenger (SignOracle.ringStd B) n keys Q')
    (muChallenger_noAssign _ keys Q') (join sp ω h)
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

end Split

section Chain

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Y : Type} [AddGroup Y] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] [NeZero n] {X₀ Cl : Type} {V : NARG.QROM.Verifier m k e Cl X₀}
  {rel : Set (X₀ × RingWit B)} {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞} {t : ℕ}

/-- **The key-reuse game up to the extraction runs at a fixed base component**: the bound of
`insiderForgeProb_le_extRun_split` for the key-reuse game, for a base signer whose signer and
ordinary signer read only the base component (`hB`, `hS`), the relayed forger `relayedForgerStd`
followed by `P` and the multi-user challenger with the ring-aware and the ordinary signing
oracle. -/
theorem keyReuseForgeProb_le_extRun_split (hbind : B.BindsRing) (hB : B.ReadsOnly (base sp))
    (hS : B.ReadsStdOnly (base sp)) (hC : PS.CompiledBySplit sp V)
    {cl : X₀ → PS.Proof → Option Cl} (hcl : ∀ ω x π, hC.claim ω x π = cl (hC.stmtAt ω x) π)
    (K : V.KnowledgeBound rel ext β) (c₀ : Cl)
    (P : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → OracleProg (Bits m) Y X₀) (q : ℕ)
    (hP : ∀ o, (P o).QueriesLE q)
    (hPst : ∀ o ω h, (P o).run (join sp ω h) = hC.stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly (Bits m) Y) t)
    (i₁ i₂ : Fin n) (Q Q' : ℕ) (hQ : Q ≤ Q') :
    keyReuseForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
        ∑' ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
          ∑' a, ((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q
              ρ).restrictAt sp ω).aux a *
            ∑' c, PMF.uniformOfFintype (Fin Q' → (SignOracle.ringStd B).Coins) c *
              simProb (outEquiv k e) (extRun (outEquiv k e)
                  (((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q
                    ρ).restrictAt sp ω).alg a)
                  (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
                  (muRelayAt (SignOracle.ringStd B) keys i₂)
                  (SPBCS.QROM.expansionVia V fun (v : ExtReg
                    (((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q
                      ρ).alg a).restrictAt sp 0)
                    (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
                    (MURequest (SignOracle.ringStd B) n) (MUResponse B)) =>
                      splitClaim cl c₀ (extForgery v)) V.kq
                  (splitDefault Q' (B.pk (keys 0)) i₂
                    (((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q
                      ρ).alg a).restrictAt sp 0))
                  (muTabAt sp (((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i))
                    i₁ Q ρ).restrictAt sp ω).alg a) ω keys Q' c))
                (fun (v : ExtReg
                    (((relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q
                      ρ).alg a).restrictAt sp 0)
                    (inertChallenger (Bits m) (XOut k e) (MURequest (SignOracle.ringStd B) n) Q')
                    (MURequest (SignOracle.ringStd B) n) (MUResponse B)) D =>
                  splitTest sp hC cl c₀ ω keys Q' v ∧
                  NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery v))) D) +
      V.knowledgeError β (t + Q * (B.qPub + PS.q) + q + V.kq) := by
  have hg := forgeSum_le_extRun_split (adm := adm) (O := SignOracle.ringStd B) (Q := Q)
    (t' := t + Q * (B.qPub + PS.q) + q) (SignOracle.readsBase_ringStd hB hS) hC hcl K c₀ P hPst
    (fun keys ρ => relayedForgerStdThen B PS adm P q hP A (fun i => B.pk (keys i)) i₁ Q ρ) i₂ Q'
  have h1 := keyReuseForgeProb_le_split sp P q hP hbind A i₁ Q Q' hQ
  refine le_trans h1 (le_trans (le_of_eq ?_) (le_trans hg (le_of_eq ?_)))
  · with_reducible rfl
  · with_reducible rfl

end Chain

end GordieHowe
