-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerBridge
public import GordieHowe.Applications.Ring.MLDSAW1SplitRestrict
public import GordieHowe.Applications.Ring.MLDSAW1ReadsBase

@[expose] public section

/-!
# The multi-user challenger at a fixed base component as a table of replies

The split form of `GordieHowe/Applications/Ring/RingForgerBridge.lean`. For an oracle split
additively as `sp : Y ≃+ Y₁ × Y₂` (`GordieHowe/Applications/Ring/MLDSAW1Split.lean`) and a signing
oracle whose signer reads the oracle only through its base component (`SignOracle.ReadsBase`), the
multi-user challenger read at a fixed base component `ω` (`Challenger.restrictAt`,
`GordieHowe/Model/Quantum/Interactive/SplitRestrict.lean`), a challenger of the oracle `X → Y₂`,
answers every request by a function of its coins and `ω` (`muReplyAt`). So an adversary of the
oracle `X → Y₂` whose every request is a multi-user request is, against it, an average over the
challenger's coins of the adversary holding the table of the replies (`muTabAt`) against the inert
challenger.

- `OracleSplit.join sp ω h`: the oracle with base component `ω` and second component `h`;
  `OracleSplit.base_join`, `prf_join`.
- `SignOracle.ReadsBase O sp`: the signer's runs agree at oracles with the same base component;
  `SignOracle.readsBase_ring`, `SignOracle.readsBase_ringStd` (from `BaseSigner.ReadsOnly` and
  `BaseSigner.ReadsStdOnly`).
- `muReplyAt sp O ω keys Q' c k r`: the reply after `k` requests at the coins `c`, the signer run at
  `join sp ω 0`. `run_respond_muChallenger_restrictAt`: the restricted challenger answers by it.
- `muTabAt`, `answerAfter_muChallenger_restrictAt_eq`, `relays_muTwoRelay_restrictAt`,
  `toOuterMeasure_outLaw_muChallenger_restrictAt_eq_absorbTab`: the table form, as in the
  oracle-free case (`toOuterMeasure_outLaw_muChallenger_eq_absorbTab`).
-/

namespace GordieHowe

open Quantum Signature RingSignature RingSignature.OracleSplit
open scoped ENNReal

/-! ### Joining the components of an oracle -/

namespace RingSignature.OracleSplit

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)

/-- **The oracle with base component `ω` and second component `h`.** -/
def join (ω : X → Y₁) (h : X → Y₂) : X → Y := fun x => sp.symm (ω x, h x)

@[simp]
theorem base_join (ω : X → Y₁) (h : X → Y₂) : OracleSplit.base sp (join sp ω h) = ω :=
  funext fun x => by simp [join, base]

@[simp]
theorem prf_join (ω : X → Y₁) (h : X → Y₂) : prf sp (join sp ω h) = h :=
  funext fun x => by simp [join, prf]

end RingSignature.OracleSplit

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} {n : ℕ}

/-! ### Signing oracles reading the base component -/

/-- **The signing oracle reads only the base component**: its runs agree at oracles with the same
base component. -/
def Signature.SignOracle.ReadsBase (O : SignOracle B) : Prop :=
  ∀ kp sm c (H H' : X → Y), OracleSplit.base sp H = OracleSplit.base sp H' →
    (O.sign kp sm c).run H = (O.sign kp sm c).run H'

variable {sp}

/-- The ring-aware signing oracle of a base signer reading only the base component reads only
the base component. -/
theorem Signature.SignOracle.readsBase_ring (hB : B.ReadsOnly (OracleSplit.base sp)) :
    (SignOracle.ring B).ReadsBase sp := by
  intro kp p c H H' h
  change (if kp.1 ∈ p.1.1 then B.bsign kp.2 p.1 (p.1.1.idxOf kp.1) p.2 c else .pure none).run H =
    (if kp.1 ∈ p.1.1 then B.bsign kp.2 p.1 (p.1.1.idxOf kp.1) p.2 c else .pure none).run H'
  split_ifs
  · exact hB.run_bsign H H' h _ _ _ _ _
  · rfl

/-- The ring-aware and ordinary signing oracle of a base signer whose signers read only the base
component reads only the base component. -/
theorem Signature.SignOracle.readsBase_ringStd (hB : B.ReadsOnly (OracleSplit.base sp))
    (hS : B.ReadsStdOnly (OracleSplit.base sp)) : (SignOracle.ringStd B).ReadsBase sp := by
  intro kp sm c H H' h
  rcases sm with p | bm
  · exact SignOracle.readsBase_ring hB kp p c H H' h
  · exact hS H H' h _ _ _

variable (sp)

/-! ### The replies at a fixed base component -/

section Replies

variable (O : SignOracle B)

/-- **The multi-user challenger's reply after `k` requests at a fixed base component** `ω` and the
coins `c`: as `muReplyAfter`, with the signer run at the oracle `join sp ω 0`. -/
def muReplyAt (ω : X → Y₁) (keys : Fin n → B.KeyCoins) (Q' : ℕ) (c : Fin Q' → O.Coins) (k : ℕ)
    (r : MURequest O n) : Option (MUResponse B) :=
  if h : k < Q' then
    match r with
    | .publicKey i => some (.publicKey (B.pk (keys i)))
    | .sign i sm => ((O.sign (B.keyGen (keys i)) sm (c ⟨k, h⟩)).run (join sp ω 0)).map .signature
    | .corrupt i => some (.keyCoins (keys i))
  else none

variable {O}

/-- **The multi-user challenger at a fixed base component answers by `muReplyAt`**, without
assignments, at every second component, for a signing oracle reading only the base component. -/
theorem run_respond_muChallenger_restrictAt (hO : O.ReadsBase sp) (ω : X → Y₁)
    (keys : Fin n → B.KeyCoins) (Q' : ℕ) (c : Fin Q' → O.Coins) (hist : MUHist O n)
    (r : MURequest O n) (h₂ : X → Y₂) :
    (((muChallenger O n keys Q').restrictAt sp ω).respond c hist r).run h₂ =
      ⟨muReplyAt sp O ω keys Q' c hist.length r, []⟩ := by
  refine (Challenger.run_respond_restrictAt sp ω (muChallenger O n keys Q') c hist r h₂).trans ?_
  congr 1
  simp only [muChallenger, muReplyAt]
  split_ifs with hk
  · rcases r with i | ⟨i, sm⟩ | i
    · rfl
    · simp only [OracleProg.run_bind, OracleProg.run_pure]
      exact congrArg (Option.map MUResponse.signature)
        (hO _ _ _ _ _ (by rw [show (fun x => sp.symm (ω x, h₂ x)) = join sp ω h₂ from rfl,
          OracleSplit.base_join, OracleSplit.base_join]))
    · rfl
  · rfl

end Replies

/-! ### The table form -/

section Table

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Nonempty X]
  [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] {O : SignOracle B} [NeZero n]

/-- **The table of the replies at a fixed base component** for an adversary of the oracle
`X → Y₂`: the reply at request number `j` to the request `q` (`muReplyAt`). -/
def muTabAt {Req Resp Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] {shA : AlgShape X Y₂ Req Resp} (A : AdaptiveIAlg shA Ot) (ω : X → Y₁)
    (keys : Fin n → B.KeyCoins) (Q' : ℕ) (c : Fin Q' → O.Coins) :
    A.OuterTab (MURequest O n) (MUResponse B) :=
  fun j q => muReplyAt sp O ω keys Q' c j q

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [Nonempty X] [DecidableEq Y₂] [NeZero n] in
/-- **The restricted multi-user challenger's reply after the requests `rs`** is `muReplyAt` at
`|rs|`, for a signing oracle reading only the base component. -/
theorem answerAfter_muChallenger_restrictAt_eq (hO : O.ReadsBase sp) (ω : X → Y₁)
    (keys : Fin n → B.KeyCoins) (Q' : ℕ) (h₂ : X → Y₂) (c : Fin Q' → O.Coins)
    (rs : List (MURequest O n)) (r : MURequest O n) :
    ((muChallenger O n keys Q').restrictAt sp ω).toPureEnv.answerAfter (h₂, c) rs r =
      muReplyAt sp O ω keys Q' c rs.length r := by
  by_cases hi : rs.length < Q'
  · have hn := Challenger.noAssign_restrictAt sp ω (muChallenger O n keys Q')
    rw [hn.answerAfter_eq h₂ c rs r hi]
    refine (congrArg Reply.response
      (run_respond_muChallenger_restrictAt sp hO ω keys Q' c _ r _)).trans ?_
    obtain ⟨-, -, h3⟩ := hn.oracleIn h₂ c rs
    rw [h3]
    exact congrArg (fun j => muReplyAt sp O ω keys Q' c j r) (min_eq_left hi.le)
  · rw [Challenger.answerAfter_toPureEnv_of_le _ _ _ _ (not_lt.1 hi)]
    simp [muReplyAt, hi]

omit [Fintype Y] [Nonempty Y] [Nonempty X] in
/-- **The restricted multi-user challenger at the coins `c` relays the inert challenger** through
the relay at the table of its replies (`muTabAt`), on the logs of the `A.slots` slots of an
adversary `A` of the oracle `X → Y₂`. -/
theorem relays_muTwoRelay_restrictAt (hO : O.ReadsBase sp) {Ot : Type}
    {shA : AlgShape X Y₂ (MURequest O n) (MUResponse B)} (A : AdaptiveIAlg shA Ot) (ω : X → Y₁)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ) (h₂ : X → Y₂) (c : Fin Q' → O.Coins) :
    ((muRelayAt O keys i₂).atC (A.tabAt (muTabAt sp A ω keys Q' c))).Relays
      ((muChallenger O n keys Q').restrictAt sp ω).toPureEnv (h₂, c)
      (inertChallenger X Y₂ (MURequest O n) Q').toPureEnv (h₂, ()) A.slots where
  answer_eq lg k r hk := by
    simp only [Env.answer, hk, Option.elim]
    rw [answerAfter_muChallenger_restrictAt_eq sp hO]
    have hlt : (requestsBefore lg k).length < A.slots :=
      lt_of_le_of_lt (length_requestsBefore_le lg k) k.2
    cases r with
    | publicKey i =>
      simp only [TwoRelay.atC, muTwoRelay, AdaptiveIAlg.tabAt, dif_pos hlt, muTabAt, muReplyAt]
      split_ifs with h1 h2 <;> first | rfl | (subst h2; rfl)
    | sign i sm => simp only [TwoRelay.atC, muTwoRelay, AdaptiveIAlg.tabAt, dif_pos hlt, muTabAt]
    | corrupt i => simp only [TwoRelay.atC, muTwoRelay, AdaptiveIAlg.tabAt, dif_pos hlt, muTabAt]
  oracle_eq lg := by
    rw [(Challenger.noAssign_restrictAt sp ω (muChallenger O n keys Q')).oracle_eq h₂ c lg,
      (inertChallenger_noAssign (MURequest O n) Q').oracle_eq h₂ () _]

/-- **The run against the restricted multi-user challenger is an average of runs with tables**:
for a signing oracle reading only the base component (`hO`), every event `P` of an adversary's
registers and its logs has, against the multi-user challenger at the base component `ω` with `Q'`
requests, the average over uniform coins `c` of the probability that the adversary with the table
`muTabAt ω c` (`absorbTab`), against the inert challenger, ends with registers and logs in `P`. The
split form of `toOuterMeasure_outLaw_muChallenger_eq_absorbTab`. -/
theorem toOuterMeasure_outLaw_muChallenger_restrictAt_eq_absorbTab (hO : O.ReadsBase sp)
    {Ot : Type} {shA : AlgShape X Y₂ (MURequest O n) (MUResponse B)} (A : AdaptiveIAlg shA Ot) (ω : X → Y₁)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ) (h₂ : X → Y₂)
    (P : DReg A.toKindAlg.W A.width X Y₂ (MURequest O n) (MUResponse B) →
      LogReg (MURequest O n) A.slots → Prop) :
    ((A.toKindAlg.composeBothOut ((muChallenger O n keys Q').restrictAt sp ω) id).outLaw
        h₂).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        (((A.absorbTab (muRelayAt O keys i₂) (muTabAt sp A ω keys Q' c)).toKindAlg.composeBothOut
          (inertChallenger X Y₂ (MURequest O n) Q') id).outLaw h₂).toOuterMeasure
          {o | ∃ v ∈ o, (fun v' => P (A.absorbedAdv
              ((muRelayAt O keys i₂).atC (A.tabAt (muTabAt sp A ω keys Q' c))) v'.adv)
              v'.adv.1.1.1.logs)
            ((A.absorb (muRelayAt O keys i₂).base).forgetCWTo (muTabAt sp A ω keys Q' c)
              (A.stepTab (muRelayAt O keys i₂)) (inertChallenger X Y₂ (MURequest O n) Q')
              (A.absorb ((muRelayAt O keys i₂).atC
                (A.tabAt (muTabAt sp A ω keys Q' c)))).step v)} := by
  rw [A.outLaw_absorb (C := (muChallenger O n keys Q').restrictAt sp ω)
    (C' := inertChallenger X Y₂ (MURequest O n) Q') (PMF.uniformOfFintype _)
    (fun c => (muRelayAt O keys i₂).atC (A.tabAt (muTabAt sp A ω keys Q' c)))
    (Equiv.prodPUnit _).symm (fun c u => by
      cases u
      change PMF.uniformOfFintype _ c = PMF.uniformOfFintype _ c * PMF.pure () ()
      rw [PMF.pure_apply_self, mul_one])
    (fun h c _ => relays_muTwoRelay_restrictAt sp hO A ω keys i₂ Q' h c)
    (fun _ c => muTwoRelay_route_injective _ _ _ c) h₂ (fun v lg _ _ _ => P v lg)]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  exact (AdaptiveIAlg.toOuterMeasure_outLaw_absorbTab_of_forall A
    (muRelayAt O keys i₂) (muTwoRelay_outer _ _) (inertChallenger X Y₂ (MURequest O n) Q') h₂
    _).symm

end Table

end GordieHowe
