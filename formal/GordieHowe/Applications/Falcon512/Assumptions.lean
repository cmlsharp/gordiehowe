-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Scheme
public import GordieHowe.Model.Signature.Assumptions

@[expose] public section

/-!
# The named unforgeability assumptions on Falcon-512

The existential unforgeability of the Falcon-512 signature scheme `falconBaseScheme G`
(`GordieHowe/Applications/Falcon512/Scheme.lean`) as the predicates of
`GordieHowe/Model/Signature/Assumptions.lean`, for a theorem to take as hypotheses. Each predicate
is a bound `ε` for a named class `𝒜` of adversaries with `Q` requests, at any signing oracle of
the scheme: the ordinary signer `SignOracle.std` is the scheme's own game, which the cited
documents discuss; at other signing interfaces (such as the ring-aware oracles of a ring signature)
the predicate is the same bound for that interface, which they do not discuss.

- `Falcon512EufCma 𝒜 Q ε` and `Falcon512MUEufCma 𝒜 Q ε`: existential unforgeability, one user and
  `n` users with adaptive corruption.
- `Falcon512MUEufCmaWithin 𝒜 Q' Qs ε`: the multi-user predicate with at most `Qs` signing and
  corruption requests counted among `Q'` answered requests (`Signature.MUEufCmaHardWithin`), the
  form that bounds the right-hand sides of the ring unforgeability theorems
  (`Signature.muEufProbWithin`), whose forger pads with public-key requests.
  `Falcon512MUEufCmaWithin.le_muEufProbWithin`: the bound on `muEufProbWithin` for a member;
  `Falcon512MUEufCma.within`: the predicate counting every request gives it at every `Qs`.

## What the predicates assume

The scheme computes every hash with the signer `G` and the vendored verifier (fixed functions)
and never reads the game's oracle: signing makes no query and verification ignores the oracle
(`falconBaseScheme`'s fields `q := 0`, `qPub := 0` and `bverify`). So these predicates are
standard-model assumptions on the scheme with those hash functions: the game's random oracle plays
no part. Random-oracle and quantum-random-oracle proofs of the scheme (below) do not bound them as
defined. Because verification reads no oracle, no bound below `1` holds for the unrestricted class
when every key has a verifying signature (`Signature.not_muEufCmaHard_univ_of_bverify_eq`, under
`Signable`), so a meaningful class `𝒜` leaves out adversaries such as `Signature.drawBruteAdv`,
which reads a forgery off the public key.

## Source

Falcon specification v1.2, §2.2.1, p. 11: the GPV framework that Falcon instantiates "has been
proven to be secure in the random oracle model under the SIS assumption", adapted to an NTRU-SIS
assumption, and "has also been proven to be secure in the quantum oracle model". The specification
does not name the security notion; the predicates take existential unforgeability, the weaker of
the two games here (`muEufProb_le_muSufProb`).

The library proves none of these statements; the predicates name them.
-/

namespace GordieHowe.Falcon512

open GordieHowe.Signature GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {n : ℕ} {V : OracleView X Y} {t : ℕ}

variable {msgLen : ℕ} {G : Signer msgLen} {O : SignOracle (falconBaseScheme (X := X) (Y := Y) G)}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable [Fintype G.KeyCoins] [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins]

/-- **Falcon-512 is EUF-CMA for the class `𝒜`** (Falcon specification v1.2 §2.2.1; module
docstring): every single-user adversary of `𝒜` against the Falcon-512 signature scheme
`falconBaseScheme` with the signer `G` has success probability at most `ε` in EUF-CMA with `Q`
requests. -/
def Falcon512EufCma (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  SUEufCmaHard 𝒜 Q ε

/-- **Falcon-512 is MU-EUF-CMA^corr for the class `𝒜`**: every adversary of `𝒜` against `n` users
of the Falcon-512 signature scheme `falconBaseScheme` with the signer `G` has success probability at
most `ε` in MU-EUF-CMA^corr with `Q` requests. -/
def Falcon512MUEufCma (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUEufCmaHard 𝒜 Q ε

/-- **Falcon-512 is MU-EUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (Falcon specification v1.2 §2.2.1; module docstring): every adversary of `𝒜` against
`n` users of the Falcon-512 signature scheme `falconBaseScheme` with the signer `G`, against the
challenger answering `Q'` requests, wins MU-EUF-CMA^corr with at most `Qs` signing and corruption
requests with probability at most `ε`. -/
def Falcon512MUEufCmaWithin (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUEufCmaHardWithin 𝒜 Q' Qs ε

/-- **The bound on `muEufProbWithin` from `Falcon512MUEufCmaWithin`** for a member `A` of the
class. -/
theorem Falcon512MUEufCmaWithin.le_muEufProbWithin {𝒜 : Set (MUAdversary O n V t)} {Q' Qs : ℕ}
    {ε : ℝ≥0∞} (h : Falcon512MUEufCmaWithin 𝒜 Q' Qs ε) {A : MUAdversary O n V t} (hA : A ∈ 𝒜) :
    muEufProbWithin A Q' Qs ≤ ε :=
  h A hA

/-- **`Falcon512MUEufCma` with `Q'` requests gives `Falcon512MUEufCmaWithin`** at every `Qs`. -/
theorem Falcon512MUEufCma.within {𝒜 : Set (MUAdversary O n V t)} {Q' : ℕ} {ε : ℝ≥0∞}
    (h : Falcon512MUEufCma 𝒜 Q' ε) (Qs : ℕ) : Falcon512MUEufCmaWithin 𝒜 Q' Qs ε :=
  MUEufCmaHard.muEufCmaHardWithin h Qs

end GordieHowe.Falcon512
