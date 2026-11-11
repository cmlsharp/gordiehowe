-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.AnonCoupling
public import GordieHowe.Applications.Ring.AnonReplay
public import GordieHowe.Applications.Ring.RingAnonSim
public import GordieHowe.Model.Signature.Properties
public import GordieHowe.Model.RingSignature.AnonAnswers
public import GordieHowe.Model.RingSignature.BaseCompleteness
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

@[expose] public section

/-!
# Anonymity of the ring signature from a base signer and a proof system

The anonymity game of `GordieHowe/Model/RingSignature/Anonymity.lean` for the scheme
`ofBase B PS adm` of `GordieHowe/Model/RingSignature/Base.lean`, for a base signer whose
algorithms read no oracle (`BaseSigner.OracleFree`) or only the first part of an oracle split
(`BaseSigner.ReadsOnly`), every adversary of the game (any oracle view `V`, any query bound `t`),
and a proof system with witness indistinguishability with public outputs (`PubWI`,
`GordieHowe/Applications/Ring/AnonCoupling.lean`).

- `reply_classicalAt_anonChallenger`, `winProb_anonChallenger`: the anonymity challenger as a
  classical challenger replies with point masses: the `k`-th request is answered by the scheme's
  signature with the coins `ω k` (`anonAns`, `GordieHowe/Model/RingSignature/AnonAnswers.lean`), so
  a deterministic strategy wins with the probability, over the signing coins, that its play
  outputs `1` (`oracleIn_anonChallenger`: the challenger's state).
- `ProofSystem.proofLaw`, `BaseSigner.refusalPubLaw`: the law of an honest proof at an oracle, and
  the law of the refusal-or-public value of the base signer of a key on a ring and a message.
- `run_signAt_eq`, `run_sign_ofBase`: signing by `ofBase` on a ring holding the key.
- `BaseSigner.ReadsOnly B f`, `BaseSigner.OracleFree.readsOnly`, `BaseSigner.ReadsOnly.ringRel_eq`:
  the base signer reads the oracle only through `f` (an oracle-free one through any `f`).
- `anonEntry`, `anonStmt`, `anonWit`, `anonAns₁`, `anonAns_eq_anonAns₁`, `bind_uniform_anonAns₁`: a
  round of the game as a round with entries: user `b`'s entry of the request (its base signature
  with the public value, or its refusal) and the proof of the request's statement with user `b`'s
  witness.
- `PMF.pi_bind_eval_coord`, `anonChoice`, `anonOut`, `detAnonWinVia`, `histRun_pure_anonAns`,
  `detAnonWinVia_eq`: **the deterministic classical game, the oracle drawn through `ψ`, is the
  rounds with entries**
  (`GordieHowe/Applications/Ring/AnonReplay.lean` for the answers request by request, lazy sampling
  `bind_pi_histRun` for the signing coins).
- `map_anonEntry_some`, `abs_detAnonWinVia_sub_le`, `abs_detAnonWin_ofBase_sub_le`: the coupling
  bound of `abs_entryRounds_sub_le` at a key vector (`ψ = id` for an oracle-free base signer).
  `expect_eq_expect_split`, `abs_detAnonWin_split_sub_le`: for a base signer reading only the first
  part of an oracle split `(X → Y) ≃ Ω₂ × Ω₁`, at each value of that part.
- `detAnonWin_mem_Icc`, `anonAdvantage_ofBase_le`, `anonAdvantage_ofBase_split_le`: **anonymity**,
  for an oracle-free base signer and for one reading a separate part of the oracle, through
  `anonAdvantage_le_of_det` (`GordieHowe/Applications/Ring/RingAnonSim.lean`):
  `Q · (𝔼 ε + 2εc) + Q · wi (Q · C) + Pr[¬ Good]`, with `ε` the distance of the two users'
  refusal-or-public value laws, `εc` the correctness error and `C` the number of valid challenges.
- `tvDist_refusalPubLaw_le`, `anonAdvantage_ofBase_le_of_pubOfCoins`: when the public value is a
  function of the signing coins (`BaseSigner.PubOfCoins`: a salt read off the coins, or
  `Pub = Unit`, `pubOfCoins_unique`), the two laws differ by at most the sum of the two refusal
  probabilities, so the bound is `Q · wi (Q · C) + 2Q · εc + 2Q · ρ` with `ρ` a bound on the
  refusal probability at every input. `anonAdvantage_ofBase_le_of_pubOfCoins_avg`: with the refusal
  rate averaged over the keys (`RefuseAvgWithin` at `ρ`), the bound is
  `Q · wi (Q · C) + 2Q · εc + Q · n · ρ`.

## Differences from `GordieHowe/Applications/Ring/Anonymity.lean`

1. **Refusals by the signer.** The refusal rule of `Anonymity.lean` reads only the oracle, the ring
   and the message. Here `bsign` may refuse depending on the key; a refusal by one user only is a
   difference of the two refusal-or-public values, counted in `ε` (in the `PubOfCoins` corollary,
   the term `2Q · ρ`).
2. **One oracle.** The game of `Anonymity.lean` draws the base scheme's oracle and the proof
   system's oracle independently. Here there is one oracle `X → Y`: the base signer reads none of it
   (`anonAdvantage_ofBase_le`), or only the first part of an oracle split
   (`anonAdvantage_ofBase_split_le`), held fixed in the coupling.
3. **Adversaries.** The adversaries of `Anonymity.lean` are deterministic with a finite set of
   challenges; here the bound holds for the quantum interactive adversaries of the game, and `C`
   counts all challenges valid for the keys.
-/

open scoped ENNReal NNReal BigOperators

namespace GordieHowe.RingSignature

open GordieHowe.Quantum GordieHowe.Interaction GordieHowe.Ring

variable {X Y : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {N n : ℕ}

/-! ### The challenger of the anonymity game answers with point masses -/

section Challenger

variable {TS : RingTypes} (S : RingScheme X Y N TS) (keys : Fin n → S.KeyCoins) (b : Bool) (Q : ℕ)
  [DecidableEq TS.PK] [Fintype TS.SignCoins] [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] in
/-- **The state of the anonymity challenger after the requests `rs`**: the base oracle `H`, no
assignments, and a history of length `min |rs| Q`. -/
theorem oracleIn_anonChallenger (H : X → Y) (ω : Fin Q → S.SignCoins) :
    ∀ rs : List (AnonRequest S n),
      ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) rs).base = H ∧
      ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) rs).ass = [] ∧
      ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) rs).hist.length = min rs.length Q := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, by simp [Env.oracleIn_nil, Challenger.toPureEnv]⟩
  | append_singleton rs c ih =>
    rw [Env.oracleIn_append_singleton]
    obtain ⟨h1, h2, h3⟩ := ih
    generalize (anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) rs = st at h1 h2 h3
    have hQ : (anonChallenger S n keys b Q).Q = Q := rfl
    simp only [Env.update, hQ, List.length_append, List.length_singleton]
    split_ifs with hlt
    · simp only [Challenger.toPureEnv]
      rw [h2, assignments_run_anonChallenger]
      refine ⟨h1, rfl, ?_⟩
      rw [List.length_append, List.length_singleton, h3]
      omega
    · refine ⟨h1, h2, ?_⟩
      rw [h3]
      omega

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] in
/-- **The classical anonymity challenger replies with point masses**: a query slot gets no
response, the `k`-th request `c` gets `anonAns … k c`, both with the oracle `H`. -/
theorem reply_classicalAt_anonChallenger (H : X → Y) (ω : Fin Q → S.SignCoins)
    (h : Hist (Option (AnonRequest S n)) (Option S.Sig × (X → Y))) (e : Option (AnonRequest S n)) :
    ((anonChallenger S n keys b Q).classicalAt H).reply ω h e =
      PMF.pure (ansRep H (anonAns S keys b Q H ω) h e) := by
  simp only [Challenger.classicalAt, Env.toClassical]
  congr 1
  obtain ⟨h1, h2, h3⟩ := oracleIn_anonChallenger S keys b Q H ω (Env.histReqs h)
  cases e with
  | none =>
    change (none,
      ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) (Env.histReqs h)).base.reprogram
      ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) (Env.histReqs h)).ass) = (none, H)
    rw [h1, h2]
    rfl
  | some c =>
    obtain ⟨g1, g2, -⟩ := oracleIn_anonChallenger S keys b Q H ω (Env.histReqs h ++ [c])
    change ((anonChallenger S n keys b Q).toPureEnv.answerAfter (H, ω) (Env.histReqs h) c,
      ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) (Env.histReqs h ++ [c])).base.reprogram
        ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) (Env.histReqs h ++ [c])).ass) =
      (anonAns S keys b Q H ω (Env.histReqs h).length c, H)
    rw [g1, g2]
    congr 1
    simp only [Env.answerAfter]
    split_ifs with hlt
    · change (((anonChallenger S n keys b Q).respond ω
        ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) (Env.histReqs h)).hist c).run
          (((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω)
            (Env.histReqs h)).base.reprogram
          ((anonChallenger S n keys b Q).toPureEnv.oracleIn (H, ω) (Env.histReqs h)).ass)).response = _
      rw [response_run_anonChallenger, h1, h2, h3]
      have hlt' : (Env.histReqs h).length < Q := hlt
      rw [min_eq_left hlt'.le]
      rfl
    · have hlt' : ¬ (Env.histReqs h).length < Q := hlt
      simp [anonAns, hlt']

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] in
/-- **The win probability of a deterministic strategy** against the classical anonymity challenger
at `H`: the probability, over the signing coins, that its output after the play with the answers
`anonAns` is `1`. -/
theorem winProb_anonChallenger (s : AnonDetStrategy S n) (m : ℕ) (H : X → Y) :
    Interaction.winProb s.toStrategy ((anonChallenger S n keys b Q).classicalAt H) m
        {p | p.2 = some true} =
      (Pr[ω ~ PMF.uniformOfFintype (Fin Q → S.SignCoins) :
        s.out H (detPlay s H (ansRep H (anonAns S keys b Q H ω)) [] m) = some true]).toReal := by
  have hc : ∀ ω, Interaction.cont s.toStrategy ((anonChallenger S n keys b Q).classicalAt H) ω [] m =
      PMF.pure (detPlay s H (ansRep H (anonAns S keys b Q H ω)) [] m,
        s.out H (detPlay s H (ansRep H (anonAns S keys b Q H ω)) [] m)) := fun ω =>
    cont_toStrategy_eq_pure s _ ω _ (reply_classicalAt_anonChallenger S keys b Q H ω) m []
  have hb : ∀ {β : Type} (ν : PMF (Fin Q → S.SignCoins)) (g : (Fin Q → S.SignCoins) → β),
      ν.bind (fun ω => PMF.pure (g ω)) = ν.map g := fun ν g => PMF.bind_pure_comp g ν
  simp only [Interaction.winProb, Interaction.exper, hc]
  congr 1
  erw [hb, PMF.toOuterMeasure_map_apply]
  rfl

end Challenger

/-! ### The ring scheme of a base signer and a proof system -/

section OfBase

variable {TB : BaseTypes}
  (B : BaseSigner X Y N TB)
  {TPS : PSTypes} (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
  (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

/-- **The law of an honest proof** of `x` with the witness `w` at the oracle `H`: the prover's coins
uniform. -/
noncomputable def ProofSystem.proofLaw {Stmt Wit : Type} {TP : PSTypes} [Fintype TP.Coins]
    [Nonempty TP.Coins] (P : ProofSystem X Y Stmt Wit TP) (H : X → Y)
    (x : Stmt) (w : Wit) : PMF P.Proof :=
  (PMF.uniformOfFintype P.Coins).map fun c => (P.prove x w c).run H

variable [DecidableEq TB.PK] [Fintype TB.Coins] [Nonempty TB.Coins]

/-- **The law of the refusal-or-public value** of the base signer with key coins `kc` on the ring
`R` and the message `m`, at the first position of its key and the oracle `H`: `none` for a refusal,
otherwise the public value of the base signature. -/
noncomputable def BaseSigner.refusalPubLaw (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N)
    (m : B.Msg) : PMF (Option B.Pub) :=
  (PMF.uniformOfFintype B.Coins).map fun cb =>
    ((B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m cb).run H).map fun σ => (B.pub (B.pk kc) σ).run H

/-- **The base signer reads the oracle only through `f`**: its ring-aware signer, its public value
and its verification agree at two oracles with the same `f`. An oracle-free base signer reads it
through any function (`OracleFree.readsOnly`). -/
structure BaseSigner.ReadsOnly {Ω₂ : Type} (f : (X → Y) → Ω₂) : Prop where
  /-- The ring-aware signer. -/
  run_bsign : ∀ H H', f H = f H' → ∀ sk R i m c,
    (B.bsign sk R i m c).run H = (B.bsign sk R i m c).run H'
  /-- The public value. -/
  run_pub : ∀ H H', f H = f H' → ∀ pk σ, (B.pub pk σ).run H = (B.pub pk σ).run H'
  /-- Verification. -/
  bverify_eq : ∀ H H', f H = f H' → B.bverify H = B.bverify H'

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  in
/-- **An oracle-free base signer reads the oracle through any function.** -/
theorem BaseSigner.OracleFree.readsOnly {TB : BaseTypes}
    {B : BaseSigner X Y N TB} (hB : B.OracleFree) {Ω₂ : Type}
    (f : (X → Y) → Ω₂) : B.ReadsOnly f where
  run_bsign H H' _ sk R i m c := hB.run_bsign_eq sk R i m c H H'
  run_pub H H' _ pk σ := hB.run_pub_eq pk σ H H'
  bverify_eq H H' _ := hB.bverify_eq H H'

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  in
/-- **The ring relation of a base signer reading the oracle through `f`** is the same at two
oracles with the same `f`. -/
theorem BaseSigner.ReadsOnly.ringRel_eq {TB : BaseTypes}
    {B : BaseSigner X Y N TB} {Ω₂ : Type} {f : (X → Y) → Ω₂}
    (hB : B.ReadsOnly f) (adm : KeyRing B.PK N → Prop) {H H' : X → Y} (h : f H = f H') :
    ringRel B adm H = ringRel B adm H' := by
  ext ⟨x, w⟩
  constructor
  · rintro ⟨ha, hi, hv, hp⟩
    exact ⟨ha, hi, by rw [← hB.bverify_eq H H' h]; exact hv, by rw [← hB.run_pub H H' h]; exact hp⟩
  · rintro ⟨ha, hi, hv, hp⟩
    exact ⟨ha, hi, by rw [hB.bverify_eq H H' h]; exact hv, by rw [hB.run_pub H H' h]; exact hp⟩

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [DecidableEq TB.PK] [Fintype TB.Coins] [Nonempty TB.Coins] in
/-- **Signing at a position** is the base signature (or its refusal) with its public value and the
proof. -/
theorem run_signAt_eq (H : X → Y) (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (cb : B.Coins) (cp : PS.Coins) :
    (signAt B PS pk sk R i m (cb, cp)).run H = ((B.bsign sk R i m cb).run H).map fun σ =>
      ((B.pub pk σ).run H, (PS.prove ⟨R, m, (B.pub pk σ).run H⟩ ⟨i, σ⟩ cp).run H) := by
  simp only [signAt_eq, OracleProg.run_bind]
  rcases (B.bsign sk R i m cb).run H with _ | σ
  · rfl
  · simp only [OracleProg.run_bind, OracleProg.run_mapOutput, Option.map_some]

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [Fintype TB.Coins] [Nonempty TB.Coins] in
/-- **Signing by `ofBase` on a ring holding the signer's key**: on a supported ring, the base
signature at the key's first position (or its refusal) with its public value and the proof; on an
unsupported ring, a refusal. -/
theorem run_sign_ofBase (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (m : B.Msg)
    (cb : B.Coins) (cp : PS.Coins) (hR : B.pk kc ∈ R.1) :
    ((ofBase B PS adm).sign (B.keyGen kc) R m (cb, cp)).run H =
      if adm R then ((B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m cb).run H).map fun σ =>
        ((B.pub (B.pk kc) σ).run H,
          (PS.prove ⟨R, m, (B.pub (B.pk kc) σ).run H⟩ ⟨R.1.idxOf (B.pk kc), σ⟩ cp).run H)
      else none := by
  split_ifs with ha
  · rw [sign_ofBase_of_mem B PS adm hR ha]
    exact run_signAt_eq B PS H _ _ R _ m cb cp
  · simp only [ofBase_sign]
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => ha h.2)]
    rfl

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [Nonempty TB.KeyCoins] [DecidableEq TB.Coins]

variable {B PS adm} [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

open Classical in
/-- **The entry law of a challenge** in experiment `b` at the key coins `keys` and the oracle `H₀`:
for a valid challenge on a supported ring, user `b`'s base signature at its key's first position
with its public value, or its refusal; `none` for no challenge and for the other challenges. -/
noncomputable def anonEntry (H₀ : X → Y) (keys : Fin n → (ofBase B PS adm).KeyCoins) (b : Bool) :
    Option (AnonRequest (ofBase B PS adm) n) → PMF (Option (B.Pub × B.BSig))
  | none => PMF.pure none
  | some c =>
    if c.Valid keys ∧ adm c.ring then
      (PMF.uniformOfFintype B.Coins).map fun cb =>
        ((B.bsign (B.sk (keys (c.user b))) c.ring (c.ring.1.idxOf (B.pk (keys (c.user b)))) c.msg
          cb).run H₀).map fun σ => ((B.pub (B.pk (keys (c.user b))) σ).run H₀, σ)
    else PMF.pure none

/-- The statement of a challenge with a public value (the fallback challenge `c₀` for none). -/
def anonStmt (c₀ : AnonRequest (ofBase B PS adm) n) :
    Option (AnonRequest (ofBase B PS adm) n) → B.Pub → RingStmt B
  | some c, y => ⟨c.ring, c.msg, y⟩
  | none, y => ⟨c₀.ring, c₀.msg, y⟩

/-- The witness of user `b` of a challenge with a base signature: its key's first position. -/
def anonWit (keys : Fin n → (ofBase B PS adm).KeyCoins) (b : Bool) :
    Option (AnonRequest (ofBase B PS adm) n) → B.BSig → RingWit B
  | some c, σ => ⟨c.ring.1.idxOf (B.pk (keys (c.user b))), σ⟩
  | none, σ => ⟨0, σ⟩

/-- **The answer of a challenge to the signing coins `r`** at the oracle `H`, user `b`. -/
noncomputable def anonAns₁ (keys : Fin n → (ofBase B PS adm).KeyCoins) (b : Bool) (H : X → Y)
    (c : AnonRequest (ofBase B PS adm) n) (r : B.Coins × PS.Coins) :
    Option (B.Pub × PS.Proof) :=
  if c.Valid keys then
    ((ofBase B PS adm).sign ((ofBase B PS adm).keyGen (keys (c.user b))) c.ring c.msg r).run H
  else none

omit [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y] [Fintype X] [DecidableEq X]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [Nonempty TB.KeyCoins] [DecidableEq TB.Coins] in
/-- **The answer to request number `j < Q`** is the answer of the challenge to the coins `ω j`. -/
theorem anonAns_eq_anonAns₁ (keys : Fin n → (ofBase B PS adm).KeyCoins) (b : Bool) (Q : ℕ) (H : X → Y)
    (ω : Fin Q → (ofBase B PS adm).SignCoins) (j : Fin Q) (c : AnonRequest (ofBase B PS adm) n) :
    anonAns (ofBase B PS adm) keys b Q H ω j c = anonAns₁ keys b H c (ω j) := by
  unfold anonAns anonAns₁
  rw [dite_eq_left j.2]

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [DecidableEq TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [Nonempty TB.KeyCoins] [DecidableEq TB.Coins] in
/-- **One round of the anonymity game is a round with entries** (a base signer reading the oracle
through `f`, at an oracle `H` with the same `f` as `H₀`): drawing the signing coins and answering the
challenge `ch` is drawing user `b`'s entry of `ch` at `H₀` and, for an entry, the proof of its
statement with user `b`'s witness at `H`. -/
theorem bind_uniform_anonAns₁ {Ω₂ : Type} {f : (X → Y) → Ω₂} (hB : B.ReadsOnly f) (H₀ H : X → Y)
    (hH : f H = f H₀) (keys : Fin n → (ofBase B PS adm).KeyCoins)
    (b : Bool) (c₀ : AnonRequest (ofBase B PS adm) n) (ch : Option (AnonRequest (ofBase B PS adm) n)) :
    (PMF.uniformOfFintype (B.Coins × PS.Coins)).bind
        (fun r => PMF.pure (ch.elim none fun c => anonAns₁ keys b H c r)) =
      (anonEntry H₀ keys b ch).bind fun e => roundLaw PS.proofLaw RingStmtOf.pub H
        (e.map fun e => (anonStmt c₀ ch e.1, anonWit keys b ch e.2)) := by
  cases ch with
  | none =>
    simp only [Option.elim, anonEntry, PMF.pure_bind, Option.map_none]
    exact PMF.bind_const _ _
  | some c =>
    simp only [Option.elim, anonEntry]
    by_cases hv : c.Valid keys ∧ adm c.ring
    · rw [ite_eq_left hv, PMF.bind_map]
      rw [PMF.uniformOfFintype_prod_eq_bind]
      refine (PMF.bind_bind _ _ _).trans ?_
      congr 1
      funext cb
      rw [PMF.bind_map]
      have hmem : B.pk (keys (c.user b)) ∈ c.ring.1 := hv.1.pk_mem b
      have hsign : ∀ cp, anonAns₁ keys b H c (cb, cp) =
          ((B.bsign (B.sk (keys (c.user b))) c.ring (c.ring.1.idxOf (B.pk (keys (c.user b))))
            c.msg cb).run H₀).map fun σ =>
          ((B.pub (B.pk (keys (c.user b))) σ).run H₀,
            (PS.prove ⟨c.ring, c.msg, (B.pub (B.pk (keys (c.user b))) σ).run H₀⟩
              ⟨c.ring.1.idxOf (B.pk (keys (c.user b))), σ⟩ cp).run H) := fun cp => by
        rw [anonAns₁, ite_eq_left hv.1]
        erw [run_sign_ofBase B PS adm H (keys (c.user b)) c.ring c.msg cb cp hmem]
        rw [ite_eq_left hv.2]
        erw [hB.run_bsign H H₀ hH]
        congr 1
        funext σ
        erw [hB.run_pub H H₀ hH]
      simp only [Function.comp_def, hsign]
      cases (B.bsign (B.sk (keys (c.user b))) c.ring (c.ring.1.idxOf (B.pk (keys (c.user b))))
        c.msg cb).run H₀ with
      | none =>
        simp only [Option.map_none, roundLaw]
        exact PMF.bind_const _ _
      | some σ =>
        simp only [Option.map_some, roundLaw, ProofSystem.proofLaw, anonStmt, anonWit,
          PMF.map_comp]
        exact PMF.bind_pure_comp _ _
    · rw [ite_eq_right hv, PMF.pure_bind, Option.map_none]
      have hnone : ∀ r, anonAns₁ keys b H c r = none := fun r => by
        rw [anonAns₁]
        split_ifs with h1
        · obtain ⟨cb, cp⟩ := r
          erw [run_sign_ofBase B PS adm H (keys (c.user b)) c.ring c.msg cb cp (h1.pk_mem b)]
          rw [ite_eq_right fun ha => hv ⟨h1, ha⟩]
        · rfl
      simp only [hnone]
      exact PMF.bind_const _ _

/-! ### The classical game as rounds with entries -/

/-- **A coordinate of a product law has the coordinate's law**, for kernels. -/
theorem _root_.PMF.pi_bind_eval_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ι → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] {β : Type*} (ν : ∀ i, PMF (δ i)) (c : ι)
    (k : δ c → PMF β) : (PMF.pi ν).bind (fun f => k (f c)) = (ν c).bind k := by
  ext z
  simp only [PMF.bind_apply]
  rw [tsum_fintype (L := SummationFilter.unconditional _),
    tsum_fintype (L := SummationFilter.unconditional _)]
  exact PMF.sum_pi_mul_apply_coord ν c fun b => k b z

variable (keys : Fin n → (ofBase B PS adm).KeyCoins) (b : Bool) (Q : ℕ) (m : (X → Y) → ℕ)
  (s : (X → Y) → AnonDetStrategy (ofBase B PS adm) n)

/-- **The challenge of round `j`** of the play of the strategy `s H`, given the answers `v` to the
earlier requests (`reqAt`). -/
def anonChoice (j : Fin Q) (H : X → Y) (v : Fin j → Option (B.Pub × PS.Proof)) :
    Option (AnonRequest (ofBase B PS adm) n) :=
  reqAt (s H) H H (m H) j v

/-- **The output of the play** of the strategy `s H` with the answers of the vector `v`. -/
def anonOut (H : X → Y) (v : Fin Q → Option (B.Pub × PS.Proof)) : Option Bool :=
  (s H).out H (detPlay (s H) H (ansRep H (vecAns v)) [] (m H))

variable {Ω₁ : Type} [Fintype Ω₁] [Nonempty Ω₁] (ψ : Ω₁ → X → Y)

/-- **The probability that a family of deterministic strategies outputs `1`, the oracle drawn
through `ψ`**: `h₁` uniform, and the strategy `s (ψ h₁)` with `m (ψ h₁)` rounds against the
challenger of experiment `b` at `ψ h₁`. -/
noncomputable def detAnonWinVia : ℝ :=
  𝔼 h₁, Interaction.winProb (s (ψ h₁)).toStrategy
    ((anonChallenger (ofBase B PS adm) n keys b Q).classicalAt (ψ h₁)) (m (ψ h₁))
      {p | p.2 = some true}

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [Nonempty TB.KeyCoins] [DecidableEq TB.Coins] in
/-- **The answer vector as rounds**: rounds answering round `j`'s challenge with the coins `ω j`
at the oracle `ψ h₁` are `h₁` drawn and the answer vector of `anonAns` at `ψ h₁`. -/
theorem histRun_pure_anonAns (ω : Fin Q → (ofBase B PS adm).SignCoins) :
    ∀ j (hj : j ≤ Q), histRun (PMF.uniformOfFintype Ω₁)
        (fun j h₁ v => PMF.pure ((anonChoice Q m s j (ψ h₁) v).elim none
          fun c => anonAns₁ keys b (ψ h₁) c (ω j))) j hj =
      (PMF.uniformOfFintype Ω₁).map fun h₁ =>
        (h₁, ansVec (s (ψ h₁)) (ψ h₁) (ψ h₁) (m (ψ h₁))
          (anonAns (ofBase B PS adm) keys b Q (ψ h₁) ω) j)
  | 0, _ => by
    simp only [histRun]
    congr 1
  | j + 1, hj => by
    rw [histRun, histRun_pure_anonAns ω j (by omega)]
    refine (PMF.bind_map _ _ _).trans ?_
    simp only [PMF.pure_map]
    refine (PMF.bind_pure_comp _ _).trans ?_
    congr 1
    funext h₁
    simp only [ansVec, anonChoice]
    congr 2
    rcases reqAt (s (ψ h₁)) (ψ h₁) (ψ h₁) (m (ψ h₁)) j (ansVec (s (ψ h₁)) (ψ h₁) (ψ h₁) (m (ψ h₁))
        (anonAns (ofBase B PS adm) keys b Q (ψ h₁) ω) j) with _ | c
    · rfl
    · exact (anonAns_eq_anonAns₁ keys b Q (ψ h₁) ω ⟨j, by omega⟩ c).symm

omit [Nonempty X] [AddGroup Y] [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The deterministic classical game of the ring signature is a game of rounds with entries**
(a base signer reading the oracle through `f`, constant on the oracles `ψ h₁`): the probability
that a family of deterministic strategies outputs `1` in experiment `b`, the oracle drawn through
`ψ`, is that of the rounds over `h₁` whose round `j` reads, from a table of independent entries at
`H₀` (`anonEntry`), the entry of the strategy's request number `j` and proves it with user `b`'s
witness at `ψ h₁`, the output read off the play with the answers of the rounds. -/
theorem detAnonWinVia_eq {Ω₂ : Type} {f : (X → Y) → Ω₂} (hB : B.ReadsOnly f) (H₀ : X → Y)
    (hψ : ∀ h₁, f (ψ h₁) = f H₀) (c₀ : AnonRequest (ofBase B PS adm) n) :
    detAnonWinVia keys b Q m s ψ =
      (((entryLaw (Q := Q) (fun b ch => anonEntry H₀ keys b ch) b).bind fun T =>
        pubRun (fun h₁ => PS.proofLaw (ψ h₁)) RingStmtOf.pub
          (entrySel (fun j h₁ v => anonChoice Q m s j (ψ h₁) v) (anonStmt c₀) (anonWit keys) b T)
          Q le_rfl).toOuterMeasure {z | anonOut Q m s (ψ z.1) z.2 = some true}).toReal := by
  set U := PMF.uniformOfFintype Ω₁
  -- the rounds with entries are `h₁` and the answer vector of the challenger's answers
  have hL : ((entryLaw (Q := Q) (fun b ch => anonEntry H₀ keys b ch) b).bind fun T =>
      pubRun (fun h₁ => PS.proofLaw (ψ h₁)) RingStmtOf.pub
        (entrySel (fun j h₁ v => anonChoice Q m s j (ψ h₁) v) (anonStmt c₀) (anonWit keys) b T)
        Q le_rfl) =
      U.bind fun h₁ => (PMF.uniformOfFintype (Fin Q → (ofBase B PS adm).SignCoins)).map fun ω =>
        (h₁, (ansVec (s (ψ h₁)) (ψ h₁) (ψ h₁) (m (ψ h₁))
          (anonAns (ofBase B PS adm) keys b Q (ψ h₁) ω) Q : Fin Q → Option (B.Pub × PS.Proof))) := by
    let K : (j : Fin Q) → Ω₁ → (Fin j → Option (B.Pub × PS.Proof)) →
        (Option (AnonRequest (ofBase B PS adm) n) → Option (B.Pub × B.BSig)) →
          PMF (Option (B.Pub × PS.Proof)) := fun j h₁ v row =>
      roundLaw PS.proofLaw RingStmtOf.pub (ψ h₁) ((row (anonChoice Q m s j (ψ h₁) v)).map fun e =>
        (anonStmt c₀ (anonChoice Q m s j (ψ h₁) v) e.1,
          anonWit keys b (anonChoice Q m s j (ψ h₁) v) e.2))
    let K' : (j : Fin Q) → Ω₁ → (Fin j → Option (B.Pub × PS.Proof)) →
        (B.Coins × PS.Coins) → PMF (Option (B.Pub × PS.Proof)) := fun j h₁ v r =>
      PMF.pure ((anonChoice Q m s j (ψ h₁) v).elim none fun c => anonAns₁ keys b (ψ h₁) c r)
    have e2 : (fun j h₁ v => (PMF.pi fun ch => anonEntry H₀ keys b ch).bind (K j h₁ v)) =
        fun j h₁ v => (PMF.uniformOfFintype (B.Coins × PS.Coins)).bind (K' j h₁ v) := by
      funext j h₁ v
      exact (PMF.pi_bind_eval_coord _ _ _).trans
        (bind_uniform_anonAns₁ hB H₀ (ψ h₁) (hψ h₁) keys b c₀ _).symm
    calc ((entryLaw (Q := Q) (fun b ch => anonEntry H₀ keys b ch) b).bind fun T =>
          pubRun (fun h₁ => PS.proofLaw (ψ h₁)) RingStmtOf.pub
            (entrySel (fun j h₁ v => anonChoice Q m s j (ψ h₁) v) (anonStmt c₀) (anonWit keys) b T)
            Q le_rfl)
        = (PMF.pi fun _ => PMF.pi fun ch => anonEntry H₀ keys b ch).bind fun T =>
            histRun U (fun j h₁ v => K j h₁ v (T j)) Q le_rfl := by
          rw [entryLaw]
          congr 1
          funext T
          exact pubRun_eq_histRun _ _ _ Q le_rfl
      _ = histRun U (fun j h₁ v => (PMF.pi fun ch => anonEntry H₀ keys b ch).bind (K j h₁ v))
            Q le_rfl := bind_pi_histRun U _ K Q le_rfl
      _ = histRun U (fun j h₁ v => (PMF.uniformOfFintype (B.Coins × PS.Coins)).bind (K' j h₁ v))
            Q le_rfl := congrArg (fun st => histRun U st Q le_rfl) e2
      _ = (PMF.pi fun _ => PMF.uniformOfFintype (B.Coins × PS.Coins)).bind fun ω =>
            histRun U (fun j h₁ v => K' j h₁ v (ω j)) Q le_rfl :=
          (bind_pi_histRun U _ K' Q le_rfl).symm
      _ = _ := by
          rw [PMF.pi_uniformOfFintype]
          have e3 : (fun ω : Fin Q → B.Coins × PS.Coins =>
              histRun U (fun j h₁ v => K' j h₁ v (ω j)) Q le_rfl) = fun ω => U.map fun h₁ =>
                (h₁, ansVec (s (ψ h₁)) (ψ h₁) (ψ h₁) (m (ψ h₁))
                  (anonAns (ofBase B PS adm) keys b Q (ψ h₁) ω) Q) :=
            funext fun ω => histRun_pure_anonAns keys b Q m s ψ ω Q le_rfl
          rw [e3]
          refine (PMF.bind_comm _ _ _).trans ?_
          congr 1
  rw [hL]
  refine Eq.symm ((toReal_toOuterMeasure_bind (α := Ω₁ × PubHist B.Pub PS.Proof Q) U _
    _).trans ?_)
  rw [tsum_fintype (L := SummationFilter.unconditional _), sum_toReal_uniform_mul_eq_expect,
    detAnonWinVia]
  refine Finset.expect_congr rfl fun h₁ _ => ?_
  rw [winProb_anonChallenger]
  erw [PMF.toOuterMeasure_map_apply]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, anonOut]
  rw [detPlay_ansRep_eq_vecAns (s (ψ h₁)) (ψ h₁) (ψ h₁) (m (ψ h₁)) Q _
    fun k hk c => anonAns_of_le _ keys b Q (ψ h₁) ω hk c]
  exact Iff.rfl

/-! ### The bound at a key vector -/

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [DecidableEq TB.Coins] [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The refusal-or-public value law of an entry is the base signer's. -/
theorem map_anonEntry_some (H₀ : X → Y) (b : Bool) (c : AnonRequest (ofBase B PS adm) n)
    (hc : c.Valid keys ∧ adm c.ring) :
    (anonEntry H₀ keys b (some c)).map (Option.map Prod.fst) =
      B.refusalPubLaw H₀ (keys (c.user b)) c.ring c.msg := by
  simp only [anonEntry, ite_eq_left hc, PMF.map_comp, BaseSigner.refusalPubLaw]
  congr 1
  funext cb
  simp only [Function.comp_apply, Option.map_map]
  rfl

omit [Nonempty X] [AddGroup Y] [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The deterministic classical game at a key vector, the oracle drawn through `ψ`** (a base
signer reading the oracle through `f`, constant on the oracles `ψ h₁`, with the value of `f H₀`):
with witness indistinguishability at error `wi` of the proof law at `ψ h₁` for the ring relation at
`H₀`, at most `C` valid challenges for the keys, an `ε` bounding the distance of the two users'
refusal-or-public value laws at `H₀` of every valid challenge on a supported ring, and correctness
error `εc`, every family of deterministic strategies has advantage at most
`Q · (ε + 2εc) + Q · wi (Q · C)`. -/
theorem abs_detAnonWinVia_sub_le {Ω₂ : Type} {f : (X → Y) → Ω₂} (hB : B.ReadsOnly f)
    (H₀ : X → Y) (hψ : ∀ h₁, f (ψ h₁) = f H₀) {wi : ℕ → ℝ}
    (hwi : PubWI (fun h₁ => PS.proofLaw (ψ h₁)) RingStmtOf.pub (ringRel B adm H₀) wi) {C : ℕ}
    (hC : (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ c : AnonRequest (ofBase B PS adm) n, c.Valid keys → adm c.ring →
      PMF.tvDist (B.refusalPubLaw H₀ (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw H₀ (keys c.user₁) c.ring c.msg) ≤ ε)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) :
    |detAnonWinVia keys false Q m s ψ - detAnonWinVia keys true Q m s ψ| ≤
      Q * (ε + 2 * εc) + Q * wi (Q * C) := by
  classical
  have hwi0 : 0 ≤ (Q : ℝ) * wi (Q * C) :=
    mul_nonneg (Nat.cast_nonneg _) (hwi.wi_nonneg _)
  have hrhs : 0 ≤ (Q : ℝ) * (ε + 2 * εc) + Q * wi (Q * C) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hε0 (by positivity))) hwi0
  rcases isEmpty_or_nonempty (AnonRequest (ofBase B PS adm) n) with hE | ⟨⟨c₀⟩⟩
  · -- no challenges: the plays of the two experiments agree
    have heq : detAnonWinVia keys false Q m s ψ = detAnonWinVia keys true Q m s ψ := by
      simp only [detAnonWinVia, winProb_anonChallenger]
      refine Finset.expect_congr rfl fun h₁ _ => ?_
      congr 2
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [detPlay_ansRep_congr (s (ψ h₁)) (ψ h₁) (ψ h₁)
        (a' := anonAns (ofBase B PS adm) keys true Q (ψ h₁) ω) (m (ψ h₁)) []
        fun j hj => (IsEmpty.false (Env.histReqs (detPlay (s (ψ h₁)) (ψ h₁)
          (ansRep (ψ h₁) (anonAns (ofBase B PS adm) keys false Q (ψ h₁) ω)) [] (m (ψ h₁))))[j]).elim]
    rw [heq, sub_self, abs_zero]
    exact hrhs
  rw [detAnonWinVia_eq keys false Q m s ψ hB H₀ hψ c₀, detAnonWinVia_eq keys true Q m s ψ hB H₀ hψ c₀]
  set act : Finset (Option (AnonRequest (ofBase B PS adm) n)) :=
    Finset.univ.filter fun ch => ∃ c, ch = some c ∧ c.Valid keys ∧ adm c.ring
  have hact : act.card ≤ C := by
    refine le_trans (Finset.card_le_card_of_injOn (fun ch => ch.getD c₀) (fun ch hch => ?_)
      fun ch hch ch' hch' he => ?_) hC
    · obtain ⟨c, rfl, hv, -⟩ := (Finset.mem_filter.1 hch).2
      simpa using hv
    · obtain ⟨c, rfl, -⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hch)).2
      obtain ⟨c', rfl, -⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hch')).2
      simp only [Option.getD_some] at he
      rw [he]
  refine abs_entryRounds_sub_le (fun b ch => anonEntry H₀ keys b ch)
    (fun h₁ => PS.proofLaw (ψ h₁)) RingStmtOf.pub (fun j h₁ v => anonChoice Q m s j (ψ h₁) v)
    (anonStmt c₀) (anonWit keys) hwi act hact ?_ hε0 (NNReal.coe_nonneg εc) ?_ ?_
    (fun h₁ v => anonOut Q m s (ψ h₁) v = some true)
  · intro ch hch b
    rcases ch with _ | c
    · rfl
    · have hv : ¬ (c.Valid keys ∧ adm c.ring) := fun hv =>
        hch (Finset.mem_filter.2 ⟨Finset.mem_univ _, c, rfl, hv⟩)
      simp only [anonEntry, ite_eq_right hv]
  · intro ch hch
    obtain ⟨c, rfl, hv⟩ := (Finset.mem_filter.1 hch).2
    rw [map_anonEntry_some keys H₀ false c hv, map_anonEntry_some keys H₀ true c hv]
    exact hε c hv.1 hv.2
  · intro ch hch b
    obtain ⟨c, rfl, hv⟩ := (Finset.mem_filter.1 hch).2
    rw [show ENNReal.ofReal (εc : ℝ) = (εc : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal]
    simp only [anonEntry, ite_eq_left hv, PMF.toOuterMeasure_map_apply]
    have hmem : B.pk (keys (c.user b)) ∈ c.ring.1 := hv.1.pk_mem b
    have hi : c.ring.1.idxOf (B.pk (keys (c.user b))) < c.ring.1.length :=
      List.idxOf_lt_length_iff.2 hmem
    refine (PMF.toOuterMeasure_mono _ fun cb hcb => ?_).trans
      (hcorr H₀ (keys (c.user b)) c.ring (c.ring.1.idxOf (B.pk (keys (c.user b))))
        ((List.getElem?_eq_getElem hi).trans (congrArg some (List.getElem_idxOf hi))) c.msg)
    obtain ⟨p, hp, hrel⟩ := hcb.1
    simp only [Option.mem_def, Option.map_eq_some_iff] at hp
    obtain ⟨σ, hσ, rfl⟩ := hp
    refine ⟨σ, hσ, ?_⟩
    by_contra hver
    apply hrel
    refine ⟨hv.2, hi, ?_, ?_⟩
    · simp only [anonStmt, anonWit]
      simpa using hver
    · simp only [anonStmt, anonWit]
      congr 2
      exact List.getElem_idxOf hi


omit [Nonempty X] [AddGroup Y] [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The deterministic classical game at a key vector** (oracle-free base signer;
`abs_detAnonWinVia_sub_le` at `ψ = id`): with witness indistinguishability at error `wi` of the
proof system for the ring relation at every oracle, at most `C` valid challenges for the keys, an
`ε` bounding the distance of the two users' refusal-or-public value laws at every oracle of every
valid challenge on a supported ring, and correctness error `εc`, every family of deterministic
strategies has advantage at most `Q · (ε + 2εc) + Q · wi (Q · C)`. -/
theorem abs_detAnonWin_ofBase_sub_le (hB : B.OracleFree) {wi : ℕ → ℝ}
    (hwi : ∀ H, PubWI PS.proofLaw RingStmtOf.pub (ringRel B adm H) wi) {C : ℕ}
    (hC : (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ H (c : AnonRequest (ofBase B PS adm) n), c.Valid keys → adm c.ring →
      PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) :
    |detAnonWin keys false Q m s - detAnonWin keys true Q m s| ≤
      Q * (ε + 2 * εc) + Q * wi (Q * C) :=
  abs_detAnonWinVia_sub_le keys Q m s id (hB.readsOnly fun _ => ()) (fun _ => Classical.arbitrary Y)
    (fun _ => rfl) (hwi _) hC hε0 (hε _) hcorr

omit [Nonempty X] [AddGroup Y] [Nonempty Ω₁] [DecidableEq Y] [Nonempty Y] in
/-- **The oracle average split along an equivalence**: the average over the oracle is the average
over the first part of the average over the second. -/
theorem expect_eq_expect_split {Ω₂ : Type} [Fintype Ω₂] [Nonempty Ω₂] (e : (X → Y) ≃ Ω₂ × Ω₁)
    (F : (X → Y) → ℝ) : 𝔼 H, F H = 𝔼 ω₂, 𝔼 h₁, F (e.symm (ω₂, h₁)) := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.sum_equiv e.symm (fun p => F (e.symm p)) F (fun _ => rfl), Fintype.sum_prod_type,
    Fintype.card_congr e, Fintype.card_prod, ← Finset.sum_div, Nat.cast_mul, div_div]
  rw [mul_comm]

omit [Nonempty X] [AddGroup Y] [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The deterministic classical game at a key vector for a base signer reading the oracle through
the first part of a split** `e : (X → Y) ≃ Ω₂ × Ω₁` (`abs_detAnonWinVia_sub_le` at each value of
the first part, averaged): with witness indistinguishability at error `wi` of the proof law at the
oracles of each first part `ω₂`, for the ring relation there (`hwi`), the bounds of
`abs_detAnonWin_ofBase_sub_le` give `Q · (ε + 2εc) + Q · wi (Q · C)`. The base signer's part of the
oracle is drawn as in the game and held fixed in the coupling. -/
theorem abs_detAnonWin_split_sub_le {Ω₂ : Type} [Fintype Ω₂] [Nonempty Ω₂]
    (e : (X → Y) ≃ Ω₂ × Ω₁) (hB : B.ReadsOnly fun H => (e H).1) {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (e.symm (ω₂, h))) RingStmtOf.pub
      (ringRel B adm (e.symm (ω₂, h₁))) wi) {C : ℕ}
    (hC : (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ H (c : AnonRequest (ofBase B PS adm) n), c.Valid keys → adm c.ring →
      PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) :
    |detAnonWin keys false Q m s - detAnonWin keys true Q m s| ≤
      Q * (ε + 2 * εc) + Q * wi (Q * C) := by
  have hpt : ∀ ω₂, |detAnonWinVia keys false Q m s (fun h₁ => e.symm (ω₂, h₁)) -
      detAnonWinVia keys true Q m s (fun h₁ => e.symm (ω₂, h₁))| ≤
        Q * (ε + 2 * εc) + Q * wi (Q * C) := fun ω₂ => by
    let h₁z : Ω₁ := Classical.arbitrary Ω₁
    exact abs_detAnonWinVia_sub_le keys Q m s (fun h₁ => e.symm (ω₂, h₁)) hB (e.symm (ω₂, h₁z))
      (fun h₁ => by simp only [Equiv.apply_symm_apply]) (hwi ω₂ h₁z) hC hε0 (hε _) hcorr
  have hsplit : ∀ b', detAnonWin keys b' Q m s =
      𝔼 ω₂, detAnonWinVia keys b' Q m s (fun h₁ => e.symm (ω₂, h₁)) := fun b' =>
    expect_eq_expect_split e _
  rw [hsplit false, hsplit true, ← Finset.expect_sub_distrib, abs_le]
  constructor
  · calc -((Q : ℝ) * (ε + 2 * εc) + Q * wi (Q * C)) =
          𝔼 _ω₂ : Ω₂, -((Q : ℝ) * (ε + 2 * εc) + Q * wi (Q * C)) := (Fintype.expect_const _).symm
      _ ≤ _ := Finset.expect_le_expect fun ω₂ _ => (abs_le.1 (hpt ω₂)).1
  · calc _ ≤ 𝔼 _ω₂ : Ω₂, ((Q : ℝ) * (ε + 2 * εc) + Q * wi (Q * C)) :=
          Finset.expect_le_expect fun ω₂ _ => (abs_le.1 (hpt ω₂)).2
      _ = _ := Fintype.expect_const _

/-! ### Anonymity -/

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] in
/-- The probability that a family of deterministic strategies outputs `1` is in `[0, 1]`. -/
theorem detAnonWin_mem_Icc {TS : RingTypes} {S : RingScheme X Y N TS} [DecidableEq TS.PK]
    [Fintype TS.SignCoins] [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]
    (keys : Fin n → S.KeyCoins) (b : Bool) (Q : ℕ) (m : (X → Y) → ℕ)
    (s : (X → Y) → AnonDetStrategy S n) :
    0 ≤ detAnonWin keys b Q m s ∧ detAnonWin keys b Q m s ≤ 1 := by
  refine ⟨Finset.expect_nonneg fun H _ => ENNReal.toReal_nonneg, ?_⟩
  calc detAnonWin keys b Q m s ≤ 𝔼 _H : X → Y, (1 : ℝ) :=
        Finset.expect_le_expect fun H _ => toReal_toOuterMeasure_le_one _ _
    _ = 1 := Fintype.expect_const _

variable [Fintype TPS.Proof] [DecidableEq TPS.Proof]

/-- **Anonymity of the ring signature of an oracle-free base signer** (the coupling bound
`abs_detAnonWin_ofBase_sub_le` through `anonAdvantage_le_of_det`, for the scheme `ofBase B PS adm`
and every adversary of the game of `GordieHowe/Model/RingSignature/Anonymity.lean`): for a base
signer whose algorithms read no oracle (`hB`), a proof system with witness indistinguishability at
error `wi` for the ring relation at every oracle (`hwi`), at most `C` valid challenges for every key
vector (`hC`), an `ε keys` bounding, at the key vectors of a good event `Good`, the distance of the
two users' laws of the refusal-or-public value at every oracle of every valid challenge on a
supported ring (`hε`; a refusal of one user only counts here), and correctness error `εc` (`hcorr`),
every anonymity adversary with any oracle view `V` and any query bound `t` has advantage with `Q`
challenges at most `Q · (𝔼 ε + 2εc) + Q · wi (Q · C) + Pr[¬ Good]`. -/
@[headline]
theorem anonAdvantage_ofBase_le (hB : B.OracleFree) {wi : ℕ → ℝ}
    (hwi : ∀ H, PubWI PS.proofLaw RingStmtOf.pub (ringRel B adm H) wi) {C : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B PS adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    (Good : (Fin n → (ofBase B PS adm).KeyCoins) → Prop) [DecidablePred Good]
    (ε : (Fin n → (ofBase B PS adm).KeyCoins) → ℝ)
    (hε0 : ∀ keys, 0 ≤ ε keys)
    (hε : ∀ keys, Good keys → ∀ H (c : AnonRequest (ofBase B PS adm) n), c.Valid keys →
      adm c.ring → PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε keys)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) {V : OracleView X Y} {t : ℕ}
    (A : AnonAdversary (ofBase B PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * ((𝔼 keys, ε keys) + 2 * εc) + Q * wi (Q * C) +
      𝔼 keys, (if Good keys then 0 else 1 : ℝ) := by
  have hwi0 : 0 ≤ (Q : ℝ) * wi (Q * C) :=
    mul_nonneg (Nat.cast_nonneg _) ((hwi (fun _ => Classical.arbitrary Y)).wi_nonneg _)
  let φ : (Fin n → (ofBase B PS adm).KeyCoins) → ℝ := fun keys =>
    Q * (ε keys + 2 * εc) + Q * wi (Q * C) + (if Good keys then 0 else 1 : ℝ)
  refine (anonAdvantage_le_of_det A Q (ε := φ) fun keys m s => ?_).trans_eq ?_
  · by_cases hG : Good keys
    · simp only [φ, hG, ite_true, add_zero]
      exact abs_detAnonWin_ofBase_sub_le keys Q m s hB hwi (hC keys) (hε0 keys) (hε keys hG) hcorr
    · simp only [φ, hG, ite_false]
      have h0 := detAnonWin_mem_Icc keys false Q m s
      have h1 := detAnonWin_mem_Icc keys true Q m s
      have hQ : 0 ≤ (Q : ℝ) * (ε keys + 2 * εc) :=
        mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hε0 keys) (by positivity))
      rw [abs_sub_le_iff]
      constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  · simp only [φ, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]

/-- **Anonymity of the ring signature of a base signer reading a separate part of the oracle**: for
an oracle split `e : (X → Y) ≃ Ω₂ × Ω₁` whose first part is the only part the base signer reads
(`hB`), with witness indistinguishability at error `wi` of the proof law at the oracles of each
first part (`hwi`), and the other hypotheses of `anonAdvantage_ofBase_le`, every anonymity adversary
with any oracle view and query bound has advantage with `Q` challenges at most
`Q · (𝔼 ε + 2εc) + Q · wi (Q · C) + Pr[¬ Good]`. -/
@[headline]
theorem anonAdvantage_ofBase_split_le {Ω₂ : Type} [Fintype Ω₂] [Nonempty Ω₂]
    (e : (X → Y) ≃ Ω₂ × Ω₁) (hB : B.ReadsOnly fun H => (e H).1) {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (e.symm (ω₂, h))) RingStmtOf.pub
      (ringRel B adm (e.symm (ω₂, h₁))) wi) {C : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B PS adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    (Good : (Fin n → (ofBase B PS adm).KeyCoins) → Prop) [DecidablePred Good]
    (ε : (Fin n → (ofBase B PS adm).KeyCoins) → ℝ)
    (hε0 : ∀ keys, 0 ≤ ε keys)
    (hε : ∀ keys, Good keys → ∀ H (c : AnonRequest (ofBase B PS adm) n), c.Valid keys →
      adm c.ring → PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε keys)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) {V : OracleView X Y} {t : ℕ}
    (A : AnonAdversary (ofBase B PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * ((𝔼 keys, ε keys) + 2 * εc) + Q * wi (Q * C) +
      𝔼 keys, (if Good keys then 0 else 1 : ℝ) := by
  have hwi0 : 0 ≤ (Q : ℝ) * wi (Q * C) := mul_nonneg (Nat.cast_nonneg _)
    ((hwi (Classical.arbitrary Ω₂) (Classical.arbitrary Ω₁)).wi_nonneg _)
  let φ : (Fin n → (ofBase B PS adm).KeyCoins) → ℝ := fun keys =>
    Q * (ε keys + 2 * εc) + Q * wi (Q * C) + (if Good keys then 0 else 1 : ℝ)
  refine (anonAdvantage_le_of_det A Q (ε := φ) fun keys m s => ?_).trans_eq ?_
  · by_cases hG : Good keys
    · simp only [φ, hG, ite_true, add_zero]
      exact abs_detAnonWin_split_sub_le keys Q m s e hB hwi (hC keys) (hε0 keys) (hε keys hG) hcorr
    · simp only [φ, hG, ite_false]
      have h0 := detAnonWin_mem_Icc keys false Q m s
      have h1 := detAnonWin_mem_Icc keys true Q m s
      have hQ : 0 ≤ (Q : ℝ) * (ε keys + 2 * εc) :=
        mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hε0 keys) (by positivity))
      rw [abs_sub_le_iff]
      constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  · simp only [φ, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]

/-! ### Public values from the coins -/

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins] [DecidableEq TB.Coins] in
/-- **The refusal-or-public value laws of two signers whose public value is a function of the
coins** differ by at most the sum of their refusal probabilities. -/
theorem tvDist_refusalPubLaw_le {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) (H : X → Y)
    (kc₀ kc₁ : B.KeyCoins) (R : KeyRing B.PK N) (m : B.Msg) (h₀ : B.pk kc₀ ∈ R.1)
    (h₁ : B.pk kc₁ ∈ R.1) :
    PMF.tvDist (B.refusalPubLaw H kc₀ R m) (B.refusalPubLaw H kc₁ R m) ≤
      (Pr[cb ~ PMF.uniformOfFintype B.Coins :
          (B.bsign (B.sk kc₀) R (R.1.idxOf (B.pk kc₀)) m cb).run H = none]).toReal +
        (Pr[cb ~ PMF.uniformOfFintype B.Coins :
          (B.bsign (B.sk kc₁) R (R.1.idxOf (B.pk kc₁)) m cb).run H = none]).toReal := by
  classical
  have hval : ∀ kc, B.pk kc ∈ R.1 → ∀ cb σ,
      (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m cb).run H = some σ →
        (B.pub (B.pk kc) σ).run H = pubOf cb := fun kc hk cb σ hσ =>
    hpub H kc R _ ((List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hk)).trans
      (congrArg some (List.getElem_idxOf _))) m cb σ hσ
  refine (PMF.tvDist_map_map_le _ _ _).trans ?_
  rw [← ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _))]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _), ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)⟩) ?_
  refine (PMF.toOuterMeasure_mono _ fun cb hcb => ?_).trans (MeasureTheory.measure_union_le _ _)
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hc
  apply hcb.1
  obtain ⟨σ₀, hσ₀⟩ := Option.ne_none_iff_exists'.1 hc.1
  obtain ⟨σ₁, hσ₁⟩ := Option.ne_none_iff_exists'.1 hc.2
  simp only [hσ₀, hσ₁, Option.map_some, hval kc₀ h₀ cb σ₀ hσ₀, hval kc₁ h₁ cb σ₁ hσ₁]

/-- **Anonymity when the public value is a function of the signing coins** (a salt read off the
coins; `Pub = Unit`, `pubOfCoins_unique`), for an oracle-free base signer: with witness
indistinguishability at error `wi` (`hwi`), at most `C` valid challenges for every key vector
(`hC`), correctness error `εc` (`hcorr`), and refusal probability at most `ρ` at every oracle of
every honest key on every ring holding it and every message (`hρ`), every anonymity adversary with
any oracle view and query bound has advantage at most `Q · wi (Q · C) + 2Q · εc + 2Q · ρ`. The last term is the refusal difference. -/
@[headline]
theorem anonAdvantage_ofBase_le_of_pubOfCoins (hB : B.OracleFree) {wi : ℕ → ℝ}
    (hwi : ∀ H, PubWI PS.proofLaw RingStmtOf.pub (ringRel B adm H) wi) {C : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B PS adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {εc ρ : ℝ≥0} (hcorr : B.CorrectWithin εc)
    (hρ : ∀ H (kc : B.KeyCoins) (R : KeyRing B.PK N) (m : B.Msg), B.pk kc ∈ R.1 →
      Pr[cb ~ PMF.uniformOfFintype B.Coins :
        (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m cb).run H = none] ≤ ρ)
    {V : OracleView X Y} {t : ℕ} (A : AnonAdversary (ofBase B PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * wi (Q * C) + 2 * Q * εc + 2 * Q * ρ := by
  have hρ' : ∀ H (kc : B.KeyCoins) (R : KeyRing B.PK N) (m : B.Msg), B.pk kc ∈ R.1 →
      (Pr[cb ~ PMF.uniformOfFintype B.Coins :
        (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m cb).run H = none]).toReal ≤ ρ :=
    fun H kc R m hk => by
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hρ H kc R m hk)
      simpa using this
  have h := anonAdvantage_ofBase_le hB hwi hC (fun _ => True) (fun _ => 2 * ρ)
    (fun _ => by positivity) (fun keys _ H c hc _ =>
      (tvDist_refusalPubLaw_le hpub H _ _ c.ring c.msg (hc.pk_mem false) (hc.pk_mem true)).trans
        (by linarith [hρ' H _ c.ring c.msg (hc.pk_mem false), hρ' H _ c.ring c.msg (hc.pk_mem true)]))
    hcorr A Q
  simp only [Fintype.expect_const, ite_true, Finset.expect_const_zero, add_zero] at h
  linarith

/-- **Anonymity when the public value is a function of the signing coins, at the refusal rate
averaged over the keys** (`RefuseAvgWithin`): for an oracle-free base signer, with witness
indistinguishability at error `wi` (`hwi`), at most `C` valid challenges for every key vector
(`hC`), correctness error `εc` (`hcorr`) and an averaged refusal rate at most `ρ` on the supported
rings (`hρ`), every anonymity adversary with any oracle view and query bound has advantage at most
`Q · wi (Q · C) + 2Q · εc + Q · n · ρ`. The bound of `anonAdvantage_ofBase_le` with `ε keys` the sum
over the `n` users of the largest refusal probability of each user's key: a challenge's two
signers are two of the users, and the average of the sum is `n` times the averaged refusal rate. -/
@[headline]
theorem anonAdvantage_ofBase_le_of_pubOfCoins_avg (hB : B.OracleFree) {wi : ℕ → ℝ}
    (hwi : ∀ H, PubWI PS.proofLaw RingStmtOf.pub (ringRel B adm H) wi) {C : ℕ}
    (hC : ∀ keys : Fin n → (ofBase B PS adm).KeyCoins,
      (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {εc ρ : ℝ≥0} (hcorr : B.CorrectWithin εc)
    (hρ : B.RefuseAvgWithin adm ρ) {V : OracleView X Y} {t : ℕ}
    (A : AnonAdversary (ofBase B PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤ Q * wi (Q * C) + 2 * Q * εc + Q * n * ρ := by
  let g : B.KeyCoins → ℝ≥0∞ := fun kc =>
    ⨆ (H : X → Y) (R : KeyRing B.PK N) (_ : B.pk kc ∈ R.1) (_ : adm R) (m : B.Msg),
      Pr[c ~ PMF.uniformOfFintype B.Coins :
        (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H = none]
  have hg1 : ∀ kc, g kc ≠ ⊤ := fun kc => ne_top_of_le_ne_top ENNReal.one_ne_top
    (iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      PMF.toOuterMeasure_apply_le_one _ _)
  let ε : (Fin n → (ofBase B PS adm).KeyCoins) → ℝ := fun keys => ∑ i, (g (keys i)).toReal
  have hε0 : ∀ keys, 0 ≤ ε keys := fun keys => Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hrg : ∀ H (kc : B.KeyCoins) (R : KeyRing B.PK N) (m : B.Msg), B.pk kc ∈ R.1 → adm R →
      (Pr[c ~ PMF.uniformOfFintype B.Coins :
        (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H = none]).toReal ≤ (g kc).toReal :=
    fun H kc R m hk ha => ENNReal.toReal_mono (hg1 kc)
      (le_iSup_of_le H (le_iSup_of_le R (le_iSup_of_le hk (le_iSup_of_le ha (le_iSup_of_le m
        le_rfl)))))
  have hε : ∀ keys, (fun _ => True) keys → ∀ H (c : AnonRequest (ofBase B PS adm) n),
      c.Valid keys → adm c.ring → PMF.tvDist (B.refusalPubLaw H (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤ ε keys := by
    intro keys _ H c hc ha
    by_cases hu : c.user₀ = c.user₁
    · rw [hu, PMF.tvDist_self]
      exact hε0 keys
    refine (tvDist_refusalPubLaw_le hpub H _ _ c.ring c.msg (hc.pk_mem false)
      (hc.pk_mem true)).trans ?_
    refine (add_le_add (hrg H _ c.ring c.msg (hc.pk_mem false) ha)
      (hrg H _ c.ring c.msg (hc.pk_mem true) ha)).trans ?_
    change (g (keys c.user₀)).toReal + (g (keys c.user₁)).toReal ≤ ε keys
    rw [← Finset.sum_pair (f := fun i => (g (keys i)).toReal) hu]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => ENNReal.toReal_nonneg
  have hexp : (𝔼 keys, ε keys) ≤ n * ρ := by
    have hone : (𝔼 kc : B.KeyCoins, (g kc).toReal) ≤ ρ := by
      rw [← PMF.tsum_toReal_mul_comp_eq_expect (PMF.uniformOfFintype B.KeyCoins) id
        (PMF.map_id _) (f := fun kc => (g kc).toReal) fun _ => ENNReal.toReal_nonneg]
      have hsum : ∑' kc, (PMF.uniformOfFintype B.KeyCoins kc).toReal * (g (id kc)).toReal =
          (∑' kc, PMF.uniformOfFintype B.KeyCoins kc * g kc).toReal := by
        rw [ENNReal.tsum_toReal_eq fun kc => ENNReal.mul_ne_top (PMF.apply_ne_top _ kc) (hg1 kc)]
        simp only [id, ENNReal.toReal_mul]
      rw [hsum]
      exact (ENNReal.toReal_mono ENNReal.coe_ne_top hρ).trans_eq (ENNReal.coe_toReal _)
    calc (𝔼 keys, ε keys) = ∑ _i : Fin n, 𝔼 kc : B.KeyCoins, (g kc).toReal := by
          simp only [ε]
          rw [Finset.expect_sum_comm]
          exact Finset.sum_congr rfl fun i _ =>
            PMF.expect_apply_eval i fun kc => (g kc).toReal
      _ ≤ ∑ _i : Fin n, (ρ : ℝ) := Finset.sum_le_sum fun _ _ => hone
      _ = n * ρ := by simp
  have h := anonAdvantage_ofBase_le hB hwi hC (fun _ => True) ε hε0 hε hcorr A Q
  simp only [ite_true, Finset.expect_const_zero, add_zero] at h
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hexp hQ]

end OfBase

end GordieHowe.RingSignature
