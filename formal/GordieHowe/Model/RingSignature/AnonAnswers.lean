-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Anonymity
public import GordieHowe.Model.Quantum.Interactive.SaltReprogram

@[expose] public section

/-!
# The answers of the anonymity challenger

The challenger of the anonymity game (`anonChallenger`, `GordieHowe/Model/RingSignature/Anonymity.lean`)
answers request by request and reprograms nothing.

- `anonAns S keys b Q H ω k c`: the answer to request number `k` with request `c` at the oracle `H`
  and the signing coins `ω`. `anonAns_of_le`: `none` from request number `Q` on.
- `assignments_run_anonChallenger`, `response_run_anonChallenger`: a reply program of the
  challenger adds no assignments, and its response after the history `hist` is
  `anonAns … hist.length c`.
- `anonChallenger_answersBy`: the challenger answers request by request by `anonAns`
  (`Quantum.Challenger.AnswersBy`).
-/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum

variable {X Y : Type} {N n : ℕ} {TS : RingTypes} (S : RingScheme X Y N TS) (keys : Fin n → S.KeyCoins) (b : Bool)
  (Q : ℕ) [DecidableEq TS.PK]

/-- **The answer to request number `k`** of the anonymity game at the oracle `H` and the signing
coins `ω`: for `k < Q` and a valid challenge, the scheme's signature of user `b` with the coins
`ω k` (or its refusal); `none` otherwise. -/
noncomputable def anonAns (H : X → Y) (ω : Fin Q → S.SignCoins) (k : ℕ) (c : AnonRequest S n) :
    Option S.Sig :=
  if h : k < Q then
    if c.Valid keys then (S.sign (S.keyGen (keys (c.user b))) c.ring c.msg (ω ⟨k, h⟩)).run H
    else none
  else none

/-- **No answer past the last challenge**: request number `k ≥ Q` gets `none`. -/
theorem anonAns_of_le (H : X → Y) (ω : Fin Q → S.SignCoins) {k : ℕ} (hk : Q ≤ k)
    (c : AnonRequest S n) : anonAns S keys b Q H ω k c = none := by
  simp [anonAns, show ¬ k < Q by omega]

variable [Fintype TS.SignCoins] [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]

/-- The anonymity challenger adds no assignments. -/
theorem assignments_run_anonChallenger (ω : Fin Q → S.SignCoins)
    (hist : List (HistoryEntry (AnonRequest S n) S.Sig)) (c : AnonRequest S n) (H : X → Y) :
    (((anonChallenger S n keys b Q).respond ω hist c).run H).assignments = [] := by
  simp only [anonChallenger]
  split_ifs <;> simp [OracleProg.run_bind, OracleProg.run_pure]

/-- **The response of the anonymity challenger** after the history `hist` is the answer to
request number `|hist|`. -/
theorem response_run_anonChallenger (ω : Fin Q → S.SignCoins)
    (hist : List (HistoryEntry (AnonRequest S n) S.Sig)) (c : AnonRequest S n) (H : X → Y) :
    (((anonChallenger S n keys b Q).respond ω hist c).run H).response =
      anonAns S keys b Q H ω hist.length c := by
  simp only [anonChallenger, anonAns]
  split_ifs <;> simp [OracleProg.run_bind, OracleProg.run_pure]

/-- **The anonymity challenger answers request by request** by `anonAns`, and reprograms
nothing. -/
theorem anonChallenger_answersBy [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    (anonChallenger S n keys b Q).AnswersBy (fun ω H j c => anonAns S keys b Q H ω j c) := by
  intro (ω : Fin Q → S.SignCoins) hist c H _
  change _ = (⟨anonAns S keys b Q H ω hist.length c, []⟩ : Reply X Y S.Sig)
  rw [← response_run_anonChallenger S keys b Q ω hist c H,
    ← assignments_run_anonChallenger S keys b Q ω hist c H]

end GordieHowe.RingSignature
