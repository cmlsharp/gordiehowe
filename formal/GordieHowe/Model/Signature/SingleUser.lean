-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUser

@[expose] public section

/-!
# Single-user unforgeability

The single-user games EUF-CMA and SUF-CMA (Kiltz, Lyubashevsky, Schaffner, "A Concrete Treatment of
Fiat-Shamir Signatures in the Quantum Random-Oracle Model", EUROCRYPT 2018, ePrint 2017/916,
§2.4, Definition 2.9 and Figure 7: the games UF-CMA and sUF-CMA for quantum adversaries) as the
multi-user games of `GordieHowe/Model/Signature/MultiUser.lean` with one user.

- `SUAdversary O V t`: an adversary of the multi-user game with one user (`MUAdversary O 1 V t`).
- `suEufProb A Q`, `suSufProb A Q`: `muEufProb` and `muSufProb` at one user.
- `Forges.not_corrupted`, `StrongForges.not_corrupted`: a forgery in the game with one user leaves
  user `0` uncorrupted. `forges_one_iff`, `strongForges_one_iff`: the winning conditions with one
  user, read at user `0`.
- `suEufProb_le_suSufProb`, `suEufProb_le_one`, `suSufProb_le_one`.

## Comparison with KLS18 Figure 7

KLS18's games: one key pair `(pk, sk) ← Gen`; the adversary gets `pk` and the signing oracle
`Sign(M)`, which records `M` (UF-CMA) or `(M, σ)` (sUF-CMA) in the set `𝓜`; it outputs
`(M*, σ*)` and wins if `M* ∉ 𝓜` (respectively `(M*, σ*) ∉ 𝓜`) and `Ver(pk, M*, σ*)`. The
adversary is quantum, with quantum random-oracle queries and classical signing queries. The game
here differs as the multi-user game does (`MultiUser.lean`, items 1–6), and at one user:

1. **A corruption oracle.** The request `corrupt 0` returns the key coins of the one user, and
   after it no output is a forgery (`Forges.not_corrupted`, `StrongForges.not_corrupted`).
2. **A public-key request.** The request `publicKey 0` returns `pk`, which the adversary also gets
   as its start input. It costs one of the `Q` answered requests.
3. **The forgery names a public key.** The output `(pk*, M*, σ*)` wins only if `pk*` is the key of
   user `0` (`forges_one_iff`).
4. **Signing through an interface.** At `SignOracle.std B` the signing oracle is the base scheme's
   signer on base messages, and `Signed` and `Returned` are KLS18's set `𝓜` for UF-CMA and
   sUF-CMA. A refused request is recorded in `𝓜` with no signature.
5. **Counted requests.** The challenger answers the first `Q` requests; later requests get `none`
   and are not recorded.
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} {O : SignOracle B}

/-! ### The winning conditions with one user -/

/-- **A forgery with one user leaves user `0` uncorrupted.** -/
theorem Forges.not_corrupted {keys : Fin 1 → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O 1} (h : Forges keys H f hist) :
    ¬ Corrupted hist 0 := by
  obtain ⟨i, -, hc, -⟩ := h.exists_user
  rwa [Fin.fin_one_eq_zero i] at hc

/-- **A strong forgery with one user leaves user `0` uncorrupted.** -/
theorem StrongForges.not_corrupted {keys : Fin 1 → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O 1} (h : StrongForges keys H f hist) :
    ¬ Corrupted hist 0 := by
  obtain ⟨i, -, hc, -⟩ := h.exists_user
  rwa [Fin.fin_one_eq_zero i] at hc

/-- **The existential forgery with one user**: the signature verifies, the key is that of user `0`,
user `0` is not corrupted and was not asked to sign for the base message. -/
theorem forges_one_iff {keys : Fin 1 → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    {hist : MUHist O 1} :
    Forges keys H f hist ↔ B.bverify H f.1 f.2.1 f.2.2 = true ∧ B.pk (keys 0) = f.1 ∧
      ¬ Corrupted hist 0 ∧ ¬ Signed hist 0 f.2.1 := by
  constructor
  · intro h
    obtain ⟨i, hi, hc, hs⟩ := h.exists_user
    rw [Fin.fin_one_eq_zero i] at hi hc hs
    exact ⟨h.verify_eq, hi, hc, hs⟩
  · rintro ⟨hv, hi, hc, hs⟩
    exact ⟨hv, 0, hi, hc, hs⟩

/-- **The strong forgery with one user**: the signature verifies, the key is that of user `0`,
user `0` is not corrupted and was not returned the signature on a message for the base message. -/
theorem strongForges_one_iff {keys : Fin 1 → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O 1} :
    StrongForges keys H f hist ↔ B.bverify H f.1 f.2.1 f.2.2 = true ∧ B.pk (keys 0) = f.1 ∧
      ¬ Corrupted hist 0 ∧ ¬ Returned hist 0 f.2.1 f.2.2 := by
  constructor
  · intro h
    obtain ⟨i, hi, hc, hs⟩ := h.exists_user
    rw [Fin.fin_one_eq_zero i] at hi hc hs
    exact ⟨h.verify_eq, hi, hc, hs⟩
  · rintro ⟨hv, hi, hc, hs⟩
    exact ⟨hv, 0, hi, hc, hs⟩

/-! ### The games -/

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

variable (O) in
/-- **An adversary of the single-user game**: an adversary of the multi-user game with one user. -/
abbrev SUAdversary (V : OracleView X Y) (t : ℕ) : Type 1 :=
  MUAdversary O 1 V t

variable {V : OracleView X Y} {t : ℕ}

/-- **The success probability of the adversary in EUF-CMA** (KLS18 Figure 7, UF-CMA) with `Q`
requests: `muEufProb` with one user. -/
noncomputable abbrev suEufProb (A : SUAdversary O V t) (Q : ℕ) : ℝ≥0∞ :=
  muEufProb A Q

/-- **The success probability of the adversary in SUF-CMA** (KLS18 Figure 7 with pairs recorded,
sUF-CMA) with `Q` requests: `muSufProb` with one user. -/
noncomputable abbrev suSufProb (A : SUAdversary O V t) (Q : ℕ) : ℝ≥0∞ :=
  muSufProb A Q

/-- **EUF-CMA is at most SUF-CMA**, adversary by adversary. -/
theorem suEufProb_le_suSufProb (A : SUAdversary O V t) (Q : ℕ) :
    suEufProb A Q ≤ suSufProb A Q :=
  muEufProb_le_muSufProb A Q

/-- The success probability in EUF-CMA is at most `1`. -/
theorem suEufProb_le_one (A : SUAdversary O V t) (Q : ℕ) : suEufProb A Q ≤ 1 :=
  muEufProb_le_one A Q

/-- The success probability in SUF-CMA is at most `1`. -/
theorem suSufProb_le_one (A : SUAdversary O V t) (Q : ℕ) : suSufProb A Q ≤ 1 :=
  muSufProb_le_one A Q

end GordieHowe.Signature
