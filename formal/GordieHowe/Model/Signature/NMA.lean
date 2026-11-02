-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.SingleUser

@[expose] public section

/-!
# Unforgeability under no-message attack

The multi-user game with adaptive corruption and no signing oracle, MU-EUF-NMA^corr, and its
single-user form EUF-NMA (Kiltz, Lyubashevsky, Schaffner, EUROCRYPT 2018, ePrint 2017/916, §2.4,
Definition 2.9 and Figure 7: the game UF-NMA, in which the adversary gets only `pk`), as the games
of `GordieHowe/Model/Signature/MultiUser.lean` at a signing oracle without messages.

- `SignOracle.none B`: the signing oracle with no messages (`SMsg := Empty`). A request of its game
  is a public-key request or a corruption.
- `muEufNmaProb A Q`, `suEufNmaProb A Q`: `muEufProb` at `SignOracle.none B`, with `n` users and
  with one user.
- `not_signed_none`, `not_returned_none`: no history of the game records a signing request.
  `strongForges_none_iff`: there the strong and the existential forgeries are the same, so
  `muSufProb_none_eq_muEufNmaProb`.

## Comparison with KLS18 Figure 7

KLS18's UF-NMA gives the adversary `pk` and no oracle besides the random oracle. The
single-user game here also answers `publicKey 0` and `corrupt 0`; after a corruption no output
is a forgery (`Forges.not_corrupted`), so a corruption only loses. The other differences are
those of `GordieHowe/Model/Signature/SingleUser.lean`.
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ}

variable {TB : BaseTypes} (B : BaseSigner X Y N TB) in
/-- **The signing oracle with no messages**: `SMsg := Empty`, so the game with it has public-key
requests and corruptions only. -/
def SignOracle.none : SignOracle B where
  SMsg := Empty
  Coins := Unit
  q := 0
  sign _ sm _ := sm.elim
  sign_queries _ sm _ := sm.elim
  base sm := sm.elim

variable {TB : BaseTypes} {B : BaseSigner X Y N TB} {n : ℕ}

/-- **No user was asked to sign** in a history of the game without messages. -/
theorem not_signed_none (hist : MUHist (SignOracle.none B) n) (i : Fin n) (bm : B.BMsg) :
    ¬ Signed hist i bm := by
  rintro ⟨-, -, sm, -, -⟩
  exact sm.elim

/-- **No user was returned a signature** in a history of the game without messages. -/
theorem not_returned_none (hist : MUHist (SignOracle.none B) n) (i : Fin n) (bm : B.BMsg)
    (σ : B.BSig) : ¬ Returned hist i bm σ :=
  fun h => not_signed_none hist i bm h.signed

/-- **Without messages, a strong forgery is an existential forgery.** -/
theorem strongForges_none_iff {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist (SignOracle.none B) n} :
    StrongForges keys H f hist ↔ Forges keys H f hist := by
  refine ⟨fun h => ?_, Forges.strongForges⟩
  obtain ⟨i, hi, hc, -⟩ := h.exists_user
  exact ⟨h.verify_eq, i, hi, hc, not_signed_none hist i _⟩

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {V : OracleView X Y} {t : ℕ}

/-- **The success probability of the adversary in MU-EUF-NMA^corr** with `Q` requests:
`muEufProb` at the signing oracle without messages. -/
noncomputable abbrev muEufNmaProb (A : MUAdversary (SignOracle.none B) n V t) (Q : ℕ) : ℝ≥0∞ :=
  muEufProb A Q

/-- **The success probability of the adversary in EUF-NMA** (KLS18 Figure 7, UF-NMA) with `Q`
requests: `muEufNmaProb` with one user. -/
noncomputable abbrev suEufNmaProb (A : SUAdversary (SignOracle.none B) V t) (Q : ℕ) : ℝ≥0∞ :=
  muEufNmaProb A Q

/-- **Without messages, MU-SUF-CMA^corr is MU-EUF-NMA^corr.** -/
theorem muSufProb_none_eq_muEufNmaProb (A : MUAdversary (SignOracle.none B) n V t) (Q : ℕ) :
    muSufProb A Q = muEufNmaProb A Q := by
  unfold muSufProb muEufNmaProb muEufProb
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, strongForges_none_iff]

end GordieHowe.Signature
