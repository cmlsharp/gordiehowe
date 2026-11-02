-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity

@[expose] public section

/-!
# The anonymity game for signers that sign validly on a good event

The ring signature publishing `w₁` (`MLDSAPublicW1.lean`) is an instance of the one anonymity
game of `GordieHowe/Applications/Ring/Anonymity.lean` (`PubAnonAdversary`, BKM06 Definition 4,
ePrint 2005/304, p. 6, with the keys given at the start as in CCLM22 Experiment 2, p. 21). Its
signer outputs only valid signatures whenever its loop can keep and no ring of high defect passes
the check, so its invalidity bound is `η = 0` on that good event.

- `PubStmt`, `PubWit`: statements `(R, m, v)` and witnesses `(i, σ)` of a ring relation, for a
  `PubSigner` whose statement type is not fixed elsewhere.
- `PubAnonAdversary.SignsValidly`, `signsValidly_of_correct`, `SignerBounds.of_signsValidly`: every
  output of either user's signing law of every valid admitted challenge is valid, so the
  invalidity bound of `PubAnonAdversary.SignerBounds` is `0`.
- `PubAnonAdversary.advantage_le_of_signsValidly`: `PubAnonAdversary.advantage_le` at `η = 0`,
  with bound `Q · 𝔼 ε + Q · wiError δ (Q · C) + Pr[¬ Good]`.

The adversaries are deterministic, as in `Anonymity.lean` (a randomized adversary is a mixture,
not formalized). The base scheme's oracle and the compiled argument's oracle are independent in
the model; an implementation must domain-separate the random oracles of the ring signature (`H`
on `(µ, w₁)`, the check oracle `G`, the proof system's hash) from each other and from FIPS 204's
other uses of SHAKE, which is an implementation requirement, not a theorem here.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

/-- **A statement of a ring relation with a public value**: a ring of at most `N` keys, a ring
message and the public value. -/
structure PubStmt (PK RMsg Pub : Type) (N : ℕ) where
  /-- The ring. -/
  ring : RingOf PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The public value. -/
  pub : Pub

/-- **A witness of a ring relation**: the signer's position and the base signature. -/
structure PubWit (Sig : Type) where
  /-- The position. -/
  idx : ℕ
  /-- The base signature. -/
  sig : Sig

section Game

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {M : SPBCS Mg P S.Stmt k kN kS L e} {n Q : ℕ}

namespace PubAnonAdversary

variable (A : PubAnonAdversary S M n Q)

/-- **The signers of the valid admitted challenges sign validly** at the oracle `H` and the users'
coins `keys`: every output of either user's signing law of every challenge of the set valid for
`keys` whose ring the signer admits at `H` is valid at that user's position. -/
def SignsValidly (H : S.Orc) (keys : Fin n → S.KeyCoins) : Prop :=
  ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → ∀ (b : Bool) (x : S.Pub × S.Sig),
    x ∈ (c.signLaw H keys b).support → c.ValidAt H b x

/-- A correct signer signs validly at every oracle. -/
theorem signsValidly_of_correct (hS : S.Correct) (H : S.Orc) (keys : Fin n → S.KeyCoins) :
    A.SignsValidly H keys := by
  intro c _ hc hA b x hx
  cases b
  · exact hS H (keys c.user₀) c.ring c.idx₀ c.msg hc.idx₀_lt hA hc.key₀ x hx
  · exact hS H (keys c.user₁) c.ring c.idx₁ c.msg hc.idx₁_lt hA hc.key₁ x hx

/-- **Signers that sign validly on the good event have invalidity bound `0`.** -/
theorem SignerBounds.of_signsValidly {Good : (Fin n → S.KeyCoins) → S.Orc → Prop}
    (hS : ∀ keys H, Good keys H → A.SignsValidly H keys)
    {ε : (Fin n → S.KeyCoins) → S.Orc → ℝ} (hε0 : ∀ keys H, 0 ≤ ε keys H)
    (hε : ∀ keys H, Good keys H → ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg →
      PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤
        ε keys H) :
    A.SignerBounds Good ε 0 where
  ε_nonneg := hε0
  η_nonneg := le_rfl
  tvDist_le := hε
  invalid_le keys H hG c hcm hc hA b := by
    rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff]
    exact Set.disjoint_left.2 fun x hx hn => hn (hS keys H hG c hcm hc hA b x hx)

variable {E : (j : ι) → (M.comp j).Encoder} {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt}

/-- **Anonymity against full key exposure for signers that sign validly on a good event**
(`advantage_le` at `η = 0`; BKM06 Definition 4, ePrint 2005/304, p. 6, keys given at the start as
in CCLM22 Experiment 2, p. 21, `Q` adaptive challenges, both oracles visible, deterministic
adversaries): for the spBCS compilation `M` whose honest prover has honest-verifier zero knowledge
at error `δ` for the ring relation at every oracle `H` (`hz`), every adversary with at most `C`
challenges of its set valid for any key vector (`hC`), a predicate `Good` of the users' coins and
the oracle under which the signers of the valid admitted challenges sign validly (`hS`), and every
`ε` bounding, at good coins and oracles, the distance of the two users' public-value laws of every
valid admitted challenge (`hε`), the advantage of every distinguisher given the users' coins, both
oracles and the history is at most `Q · 𝔼_{keys, H} ε + Q · wiError δ (Q · C) + Pr_{keys, H}[¬ Good]`. -/
theorem advantage_le_of_signsValidly (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : S.Stmt → PubZ} {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : ℝ≥0}
    (hz : ∀ H, CausalHVZK (Rv H).MV (S.rel H) (honest H) pubZ (sim H) δ) {C : ℕ}
    (hC : A.ValidCountLe C) (Good : (Fin n → S.KeyCoins) → S.Orc → Prop)
    [∀ keys H, Decidable (Good keys H)] (hS : ∀ keys H, Good keys H → A.SignsValidly H keys)
    (ε : (Fin n → S.KeyCoins) → S.Orc → ℝ) (hε0 : ∀ keys H, 0 ≤ ε keys H)
    (hε : ∀ keys H, Good keys H → ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg →
      PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤
        ε keys H)
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) :
    A.advantage E Qs honest D ≤ Q * (𝔼 keys, 𝔼 H, ε keys H) + Q * M.wiError δ (Q * C) +
      𝔼 keys, 𝔼 H, (if Good keys H then 0 else 1 : ℝ) := by
  have h := A.advantage_le Rv hz hC (SignerBounds.of_signsValidly A hS hε0 hε) D
  simpa only [mul_zero, add_zero] using h

end PubAnonAdversary

end Game

end GordieHowe.Ring
