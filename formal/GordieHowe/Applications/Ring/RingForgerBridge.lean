-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerMU
public import GordieHowe.Applications.Ring.RingForgerExtract
public import GordieHowe.Model.Signature.MultiUserBridge
public import GordieHowe.Model.Signature.MultiUserCount

@[expose] public section

/-!
# The multi-user challenger as a table of replies

The third step of the reduction from BKM06 Definition 7 for `ofBase B PS adm` to MU-EUF-CMA^corr
(after `GordieHowe/Applications/Ring/RingForgerMU.lean`): an adversary whose every request is a
multi-user request, against the multi-user challenger at the users' key coins, is an average over
the challenger's coins `ω` of the adversary holding the table of the challenger's replies at `ω`
(`Quantum.AdaptiveIAlg.absorbTab`, `GordieHowe/Model/Quantum/Interactive/ReqBridge.lean`) against
an inert challenger. Every request is outer (`muTwoRelay`), so the table is read at the request
count, as the multi-user challenger reads its coins.

- `inertChallenger Q'`: answers nothing, with no coins and no queries.
- `muTwoRelay O n pk₀ i₂`, `muRelayAt`: every request an outer request, none of them
  `publicKey 0` (`muTwoRelay_outer_ne`). `muTwoRelay_outer_eq_self`,
  `isSignOrCorrupt_muTwoRelay_outer`: a signing or corruption outer request is the request itself,
  and an outer request is one exactly when the request is.
- `answerAfter_muChallenger_eq`: the multi-user challenger's reply after `rs` is
  `muReplyAfter` at `|rs|`, for a signing oracle without queries.
- `relays_muTwoRelay`: the multi-user challenger at `ω` relays the inert challenger through the
  relay at the table `muTab ω`, on the logs of the adversary's slots.
- `toOuterMeasure_outLaw_muChallenger_eq_absorbTab`: the adversary's run against the multi-user
  challenger is the average over `ω` of the run of the adversary with the table against the inert
  challenger, on every event of its registers and its logs.
-/

namespace GordieHowe

open Quantum Signature RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes}
  {B : BaseSigner X Y N TB} {O : SignOracle B.core} {n : ℕ}

/-! ### The inert challenger and the relay -/

variable (X Y) in
/-- **The inert challenger** with `Q'` requests of type `Req`: no coins, no queries, every reply
`none`. -/
noncomputable def inertChallenger (Req : Type) [Fintype Req] [DecidableEq Req] (Q' : ℕ) :
    Challenger X Y Req Unit where
  Coins := Unit
  coins := PMF.pure ()
  Q := Q'
  q := 0
  respond _ _ _ := .pure ⟨none, []⟩
  respond_queries _ _ _ _ := le_rfl

variable [NeZero n]

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable (O n) in
/-- **Every request an outer request, none of them the dummy `publicKey 0`**: request `r` is sent
to the inner challenger as itself; its outer request is `r`, except `publicKey 0`, whose outer
request is `publicKey i₂` and whose reply is the key `pk₀` when the outer request is answered. -/
def muTwoRelay (pk₀ : B.PK) (i₂ : Fin n) : TwoRelay (MURequest O n) (MUResponse B.core)
    (MURequest O n) Unit (MURequest O n) (MUResponse B.core) where
  route₁ _ r := r
  answer₁ _ _ _ := none
  outer
    | _, .publicKey i => some (.publicKey (if i = 0 then i₂ else i))
    | _, .sign i sm => some (.sign i sm)
    | _, .corrupt i => some (.corrupt i)
  answer₂
    | _, .publicKey i, x => if i = 0 then x.map fun _ => .publicKey pk₀ else x
    | _, .sign _ _, x => x
    | _, .corrupt _, x => x

variable (O) in
/-- The relay `muTwoRelay` at the users' key coins `keys`: the key of user `0` known. -/
abbrev muRelayAt (keys : Fin n → B.KeyCoins) (i₂ : Fin n) : TwoRelay (MURequest O n)
    (MUResponse B.core) (MURequest O n) Unit (MURequest O n) (MUResponse B.core) :=
  muTwoRelay O n (B.pk (keys 0)) i₂

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
theorem muTwoRelay_outer (pk₀ : B.PK) (i₂ : Fin n) :
    ∀ c r, ((muTwoRelay O n pk₀ i₂).outer c r).isSome := fun _ r => by
  cases r <;> rfl

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **No outer request of the relay is the dummy `publicKey 0`**, for `i₂ ≠ 0`. -/
theorem muTwoRelay_outer_ne (pk₀ : B.PK) {i₂ : Fin n} (hi₂ : i₂ ≠ 0) :
    ∀ c r q, (muTwoRelay O n pk₀ i₂).outer c r = some q → q ≠ .publicKey 0 := fun _ r q h => by
  cases r with
  | publicKey i =>
    simp only [muTwoRelay, Option.some.injEq] at h
    subst h
    intro h'
    have := MURequest.publicKey.inj h'
    split_ifs at this with hi
    · exact hi₂ this
    · exact hi this
  | sign i sm =>
    simp only [muTwoRelay, Option.some.injEq] at h
    subst h
    intro h'
    cases h'
  | corrupt i =>
    simp only [muTwoRelay, Option.some.injEq] at h
    subst h
    intro h'
    cases h'

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **The outer request of a corrupting or signing request is itself** (`muTwoRelay`). -/
theorem muTwoRelay_outer_eq_self {pk₀ : B.PK} {i₂ : Fin n} {c : ℕ} {r q : MURequest O n}
    (h : (muTwoRelay O n pk₀ i₂).outer c r = some q)
    (hq : (∃ i, q = .corrupt i) ∨ ∃ i sm, q = .sign i sm) : r = q := by
  cases r with
  | publicKey i =>
    simp only [muTwoRelay, Option.some.injEq] at h
    subst h
    rcases hq with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  | sign i sm =>
    simp only [muTwoRelay, Option.some.injEq] at h
    exact h
  | corrupt i =>
    simp only [muTwoRelay, Option.some.injEq] at h
    exact h

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **Through `muTwoRelay`, an outer request is a signing or corruption request exactly when the
request is.** -/
theorem isSignOrCorrupt_muTwoRelay_outer (pk₀ : B.PK) (i₂ : Fin n) (c : ℕ) (r : MURequest O n) :
    ((muTwoRelay O n pk₀ i₂).outer c r).any MURequest.isSignOrCorrupt = r.isSignOrCorrupt := by
  cases r <;> rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [Nonempty X]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y] [Nonempty X]
  in
/-- **The inert challenger never reprograms.** -/
theorem inertChallenger_noAssign (Req : Type) [Fintype Req] [DecidableEq Req] (Q' : ℕ) :
    (inertChallenger X Y Req Q').NoAssign := fun _ _ _ _ => rfl

omit [NeZero n] [Fintype O.SMsg] [DecidableEq O.SMsg] in
/-- **The multi-user challenger's reply after the requests `rs`** is `muReplyAfter` at `|rs|`, for a
signing oracle without queries. -/
theorem answerAfter_muChallenger_eq (hO : O.NoQuery) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    (H : X → Y) (ω : Fin Q' → O.Coins) (rs : List (MURequest O n)) (r : MURequest O n) :
    (muChallenger O n keys Q').toPureEnv.answerAfter (H, ω) rs r =
      muReplyAfter O keys Q' ω rs.length r := by
  by_cases hi : rs.length < Q'
  · have hn := muChallenger_noAssign O keys Q'
    rw [hn.answerAfter_eq H ω rs r hi, run_respond_muChallenger hO]
    obtain ⟨-, -, h3⟩ := hn.oracleIn H ω rs
    rw [h3]
    exact congrArg (fun j => muReplyAfter O keys Q' ω j r) (min_eq_left hi.le)
  · rw [Challenger.answerAfter_toPureEnv_of_le _ _ _ _ (not_lt.1 hi)]
    simp [muReplyAfter, hi]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

/-- **The multi-user challenger at the coins `ω` relays the inert challenger** through the relay at
the table of its replies, on the logs of the `A.slots` slots of an adversary `A`: the count of the
earlier requests stays below the number of slots, where the table is the challenger's reply. -/
theorem relays_muTwoRelay (hO : O.NoQuery) {Ot : Type}
    {shA : AlgShape X Y (MURequest O n) (MUResponse B.core)} (A : AdaptiveIAlg shA Ot) (keys : Fin n → B.KeyCoins)
    (i₂ : Fin n) (Q' : ℕ) (H : X → Y) (ω : Fin Q' → O.Coins) :
    ((muRelayAt O keys i₂).atC (A.tabAt (muTab A keys Q' ω))).Relays
      (muChallenger O n keys Q').toPureEnv (H, ω)
      (inertChallenger X Y (MURequest O n) Q').toPureEnv (H, ()) A.slots where
  answer_eq lg k r hk := by
    simp only [Env.answer, hk, Option.elim]
    rw [answerAfter_muChallenger_eq hO]
    have hlt : (requestsBefore lg k).length < A.slots :=
      lt_of_le_of_lt (length_requestsBefore_le lg k) k.2
    cases r with
    | publicKey i =>
      simp only [TwoRelay.atC, muTwoRelay, AdaptiveIAlg.tabAt, dif_pos hlt, muTab, muReplyAfter]
      split_ifs with h1 h2 <;> first | rfl | (subst h2; rfl)
    | sign i sm => simp only [TwoRelay.atC, muTwoRelay, AdaptiveIAlg.tabAt, dif_pos hlt, muTab]
    | corrupt i => simp only [TwoRelay.atC, muTwoRelay, AdaptiveIAlg.tabAt, dif_pos hlt, muTab]
  oracle_eq lg := by
    rw [(muChallenger_noAssign O keys Q').oracle_eq H ω lg,
      (inertChallenger_noAssign (MURequest O n) Q').oracle_eq H () _]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y] [Nonempty X]
  [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins]
  [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- The relay of the requests to the inert challenger is injective. -/
theorem muTwoRelay_route_injective (pk₀ : B.PK) (i₂ : Fin n)
    (b : ℕ → MURequest O n → Option (MUResponse B.core)) (c : ℕ) :
    Function.Injective (((muTwoRelay O n pk₀ i₂).atC b).route c) := fun _ _ h => h

/-! ### The run against the multi-user challenger as runs with tables -/

/-- **The run against the multi-user challenger is an average of runs with tables** (module
docstring): for a signing oracle without queries (`hO`), every event `P` of an adversary's
registers and its logs has, against the multi-user challenger at `keys` with `Q'` requests, the
average over uniform coins `ω` of the probability that the adversary with the table `muTab ω`
(`absorbTab`), against the inert challenger, ends with registers and logs (read through the table's
removal and the absorbed registers) in `P`. -/
theorem toOuterMeasure_outLaw_muChallenger_eq_absorbTab (hO : O.NoQuery) {Ot : Type}
    {shA : AlgShape X Y (MURequest O n) (MUResponse B.core)} (A : AdaptiveIAlg shA Ot) (keys : Fin n → B.KeyCoins)
    (i₂ : Fin n) (Q' : ℕ) (H : X → Y)
    (P : DReg A.toKindAlg.W A.width X Y (MURequest O n) (MUResponse B.core) →
      LogReg (MURequest O n) A.slots → Prop) :
    ((A.toKindAlg.composeBothOut (muChallenger O n keys Q') id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
        (((A.absorbTab (muRelayAt O keys i₂) (muTab A keys Q' ω)).toKindAlg.composeBothOut
          (inertChallenger X Y (MURequest O n) Q') id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, (fun v' => P (A.absorbedAdv
              ((muRelayAt O keys i₂).atC (A.tabAt (muTab A keys Q' ω))) v'.adv)
              v'.adv.1.1.1.logs)
            ((A.absorb (muRelayAt O keys i₂).base).forgetCWTo (muTab A keys Q' ω)
              (A.stepTab (muRelayAt O keys i₂)) (inertChallenger X Y (MURequest O n) Q')
              (A.absorb ((muRelayAt O keys i₂).atC (A.tabAt (muTab A keys Q' ω)))).step v)} := by
  rw [A.outLaw_absorb (C := muChallenger O n keys Q')
    (C' := inertChallenger X Y (MURequest O n) Q') (PMF.uniformOfFintype _)
    (fun ω => (muRelayAt O keys i₂).atC (A.tabAt (muTab A keys Q' ω)))
    (Equiv.prodPUnit _).symm (fun ω u => by
      cases u
      change PMF.uniformOfFintype _ ω = PMF.uniformOfFintype _ ω * PMF.pure () ()
      rw [PMF.pure_apply_self, mul_one])
    (fun H ω _ => relays_muTwoRelay hO A keys i₂ Q' H ω)
    (fun _ c => muTwoRelay_route_injective _ _ _ c) H (fun v lg _ _ _ => P v lg)]
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  exact (AdaptiveIAlg.toOuterMeasure_outLaw_absorbTab_of_forall A
    (muRelayAt O keys i₂) (muTwoRelay_outer _ _) (inertChallenger X Y (MURequest O n) Q') H _).symm

end GordieHowe
