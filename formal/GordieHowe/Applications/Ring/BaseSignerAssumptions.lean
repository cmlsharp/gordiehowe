-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSigners
public import GordieHowe.Model.Signature.Assumptions

@[expose] public section

/-!
# The named assumptions on the base signers

The unforgeability assumptions on the base signers of
`GordieHowe/Applications/Ring/BaseSigners.lean`, as the predicates of
`GordieHowe/Model/Signature/Assumptions.lean` at those signers, for a theorem to take as
hypotheses. Each predicate is a bound `ε` for a named class `𝒜` of adversaries with `Q`
requests, at any signing oracle of the base signer: the ordinary signer `SignOracle.std` is the
base scheme's own game, which the cited documents discuss; at the ring-aware oracles
(`SignOracle.ring`, `SignOracle.ringStd`) the predicate is the same bound for that signing
interface, which they do not discuss.

- `MLDSASufCma 𝒜 Q ε` (one user) and `MLDSAMUSufCma 𝒜 Q ε` (`n` users with adaptive corruption):
  strong unforgeability of the ML-DSA base signer `mldsaBaseSigner p prims maxAttempts bmsg`, at
  any parameter set `p`. `MLDSA44SufCma`, `MLDSA65SufCma`, `MLDSA87SufCma` and the multi-user
  `MLDSA44MUSufCma`, `MLDSA65MUSufCma`, `MLDSA87MUSufCma`: at the FIPS 204 parameter sets
  ML-DSA-44, ML-DSA-65, ML-DSA-87 (`MLDSA.mldsa44`, `MLDSA.mldsa65`, `MLDSA.mldsa87`).
- `Falcon512EufCma 𝒜 Q ε` and `Falcon512MUEufCma 𝒜 Q ε`: existential unforgeability of the
  Falcon-512 base signer `falconBaseSigner G bmsg`.
- `MLDSAMUSufCmaWithin 𝒜 Q' Qs ε`, `MLDSA44MUSufCmaWithin`, `MLDSA65MUSufCmaWithin`,
  `MLDSA87MUSufCmaWithin` and `Falcon512MUEufCmaWithin 𝒜 Q' Qs ε`: the multi-user predicates with at
  most `Qs` signing and corruption requests counted among `Q'` answered requests
  (`Signature.MUSufCmaHardWithin`, `Signature.MUEufCmaHardWithin`), the form that bounds the
  right-hand sides of the ring unforgeability theorems (`Signature.muEufProbWithin`), whose forger
  pads with public-key requests. `MLDSAMUSufCmaWithin.le_muEufProbWithin`,
  `Falcon512MUEufCmaWithin.le_muEufProbWithin`: the bound on `muEufProbWithin` for a member;
  `MLDSAMUSufCma.within`, `Falcon512MUEufCma.within`: the predicates counting every request give
  these at every `Qs`.

## What the predicates assume

The ML-DSA and Falcon-512 base signers compute every hash with the primitives they are given
(`prims`, the Falcon signer `G`: fixed functions, the FIPS 202 functions at the concrete
primitives) and never read the game's oracle: signing makes no query and verification ignores the
oracle (`mldsaBaseSigner_oracleFree`, `falconBaseSigner_oracleFree`,
`GordieHowe/Applications/Ring/BaseSignerFacts.lean`). So these predicates are standard-model
assumptions on the schemes with those hash functions: the game's random oracle plays no part.
Random-oracle and quantum-random-oracle proofs of the schemes (below) do not bound them as
defined. Because verification reads no oracle, no bound below `1` holds for the unrestricted
class when every key has a verifying signature (`Signature.not_muEufCmaHard_univ_of_bverify_eq`,
under `Signable`), so a meaningful class `𝒜` leaves out adversaries such as
`Signature.drawBruteAdv`, which reads a forgery off the public key.

## Sources

- **ML-DSA.** FIPS 204, §3.1, p. 9, for the deployed scheme: "ML-DSA is designed to be strongly
  existentially unforgeable under chosen message attack (SUF-CMA)." For comparison only: Kiltz,
  Lyubashevsky, Schaffner (EUROCRYPT 2018, ePrint 2017/916), Theorem 3.1 and eq. (21), bound the
  sUF-CMA advantage of (deterministic) Dilithium with `H` a quantum random oracle by MLWE,
  SelfTargetMSIS and MSIS advantages; Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang,
  Hülsing, Lee, Wu ("Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and
  Dilithium", ePrint 2023/246) and Devevey, Fallahpour, Passelègue, Stehlé ("A Detailed Analysis of
  Fiat-Shamir with Aborts", ePrint 2023/245) report a gap in that paper's reduction from
  chosen-message to no-message attacks (Theorem 3.2) and give corrected reductions in the ROM and
  the QROM. These are single-user statements in a random-oracle model; this library does not
  derive the predicates from them.
- **Falcon-512.** Falcon specification v1.2, §2.2.1, p. 11: the GPV framework that Falcon
  instantiates "has been proven to be secure in the random oracle model under the SIS assumption",
  adapted to an NTRU-SIS assumption, and "has also been proven to be secure in the quantum oracle
  model". The specification does not name the security notion; the predicates take existential
  unforgeability, the weaker of the two games here (`muEufProb_le_muSufProb`).

The library proves none of these statements; the predicates name them.
-/

namespace GordieHowe.Ring

open GordieHowe.Signature GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {n : ℕ} {V : OracleView X Y} {t : ℕ}

/-! ### ML-DSA -/

section MLDSA

open _root_.MLDSA

variable {p : Params} {prims : Primitives p} [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] {maxAttempts : ℕ}
  {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len}
  {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg)}

/-- **ML-DSA is SUF-CMA for the class `𝒜`** (FIPS 204 §3.1; module docstring): every single-user
adversary of `𝒜` against the ML-DSA base signer at the parameter set `p` has success probability
at most `ε` in SUF-CMA with `Q` requests. -/
def MLDSASufCma (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  SUSufCmaHard 𝒜 Q ε

/-- **ML-DSA is MU-SUF-CMA^corr for the class `𝒜`**: every adversary of `𝒜` against `n` users of
the ML-DSA base signer at the parameter set `p` has success probability at most `ε` in
MU-SUF-CMA^corr with `Q` requests. -/
def MLDSAMUSufCma (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUSufCmaHard 𝒜 Q ε

/-- **ML-DSA is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (FIPS 204 §3.1; module docstring): every adversary of `𝒜` against `n` users of the
ML-DSA base signer at the parameter set `p`, against the challenger answering `Q'` requests, wins
MU-SUF-CMA^corr with at most `Qs` signing and corruption requests with probability at most `ε`. -/
def MLDSAMUSufCmaWithin (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUSufCmaHardWithin 𝒜 Q' Qs ε

/-- **The bound on `muEufProbWithin` from `MLDSAMUSufCmaWithin`** for a member `A` of the class
(`Signature.MUSufCmaHardWithin.muEufCmaHardWithin`). -/
theorem MLDSAMUSufCmaWithin.le_muEufProbWithin {𝒜 : Set (MUAdversary O n V t)} {Q' Qs : ℕ}
    {ε : ℝ≥0∞} (h : MLDSAMUSufCmaWithin 𝒜 Q' Qs ε) {A : MUAdversary O n V t} (hA : A ∈ 𝒜) :
    muEufProbWithin A Q' Qs ≤ ε :=
  MUSufCmaHardWithin.muEufCmaHardWithin h A hA

/-- **`MLDSAMUSufCma` with `Q'` requests gives `MLDSAMUSufCmaWithin`** at every `Qs`. -/
theorem MLDSAMUSufCma.within {𝒜 : Set (MUAdversary O n V t)} {Q' : ℕ} {ε : ℝ≥0∞}
    (h : MLDSAMUSufCma 𝒜 Q' ε) (Qs : ℕ) : MLDSAMUSufCmaWithin 𝒜 Q' Qs ε :=
  MUSufCmaHard.muSufCmaHardWithin h Qs

end MLDSA

section MLDSAParams

open _root_.MLDSA

variable {prims44 : Primitives _root_.MLDSA.mldsa44} {prims65 : Primitives _root_.MLDSA.mldsa65}
  {prims87 : Primitives _root_.MLDSA.mldsa87} [nttOps : NTTRingOps] {maxAttempts : ℕ} {len : ℕ}
  {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-- **ML-DSA-44 is SUF-CMA for the class `𝒜`** (`MLDSASufCma` at `MLDSA.mldsa44`). -/
abbrev MLDSA44SufCma [Fintype prims44.Power2High] [DecidableEq prims44.Power2High]
    [Fintype prims44.Hint] [DecidableEq prims44.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa44 prims44) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa44 prims44 maxAttempts
      bmsg)}
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSASufCma 𝒜 Q ε

/-- **ML-DSA-65 is SUF-CMA for the class `𝒜`** (`MLDSASufCma` at `MLDSA.mldsa65`). -/
abbrev MLDSA65SufCma [Fintype prims65.Power2High] [DecidableEq prims65.Power2High]
    [Fintype prims65.Hint] [DecidableEq prims65.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa65 prims65) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa65 prims65 maxAttempts
      bmsg)}
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSASufCma 𝒜 Q ε

/-- **ML-DSA-87 is SUF-CMA for the class `𝒜`** (`MLDSASufCma` at `MLDSA.mldsa87`). -/
abbrev MLDSA87SufCma [Fintype prims87.Power2High] [DecidableEq prims87.Power2High]
    [Fintype prims87.Hint] [DecidableEq prims87.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa87 prims87) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa87 prims87 maxAttempts
      bmsg)}
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSASufCma 𝒜 Q ε

/-- **ML-DSA-44 is MU-SUF-CMA^corr for the class `𝒜`** (`MLDSAMUSufCma` at `MLDSA.mldsa44`). -/
abbrev MLDSA44MUSufCma [Fintype prims44.Power2High] [DecidableEq prims44.Power2High]
    [Fintype prims44.Hint] [DecidableEq prims44.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa44 prims44) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa44 prims44 maxAttempts
      bmsg)}
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCma 𝒜 Q ε

/-- **ML-DSA-44 is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (`MLDSAMUSufCmaWithin` at `MLDSA.mldsa44`). -/
abbrev MLDSA44MUSufCmaWithin [Fintype prims44.Power2High] [DecidableEq prims44.Power2High]
    [Fintype prims44.Hint] [DecidableEq prims44.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa44 prims44) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa44 prims44 maxAttempts
      bmsg)}
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-65 is MU-SUF-CMA^corr for the class `𝒜`** (`MLDSAMUSufCma` at `MLDSA.mldsa65`). -/
abbrev MLDSA65MUSufCma [Fintype prims65.Power2High] [DecidableEq prims65.Power2High]
    [Fintype prims65.Hint] [DecidableEq prims65.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa65 prims65) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa65 prims65 maxAttempts
      bmsg)}
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCma 𝒜 Q ε

/-- **ML-DSA-65 is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (`MLDSAMUSufCmaWithin` at `MLDSA.mldsa65`). -/
abbrev MLDSA65MUSufCmaWithin [Fintype prims65.Power2High] [DecidableEq prims65.Power2High]
    [Fintype prims65.Hint] [DecidableEq prims65.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa65 prims65) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa65 prims65 maxAttempts
      bmsg)}
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-87 is MU-SUF-CMA^corr for the class `𝒜`** (`MLDSAMUSufCma` at `MLDSA.mldsa87`). -/
abbrev MLDSA87MUSufCma [Fintype prims87.Power2High] [DecidableEq prims87.Power2High]
    [Fintype prims87.Hint] [DecidableEq prims87.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa87 prims87) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa87 prims87 maxAttempts
      bmsg)}
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCma 𝒜 Q ε

/-- **ML-DSA-87 is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (`MLDSAMUSufCmaWithin` at `MLDSA.mldsa87`). -/
abbrev MLDSA87MUSufCmaWithin [Fintype prims87.Power2High] [DecidableEq prims87.Power2High]
    [Fintype prims87.Hint] [DecidableEq prims87.Hint]
    {bmsg : KeyRing (PublicKey _root_.MLDSA.mldsa87 prims87) N → RMsg → Bytes len}
    {O : SignOracle (mldsaBaseSigner (X := X) (Y := Y) _root_.MLDSA.mldsa87 prims87 maxAttempts
      bmsg)}
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCmaWithin 𝒜 Q' Qs ε

end MLDSAParams

/-! ### Falcon-512 -/

section Falcon

open GordieHowe.Falcon512.Ring.Native

variable {msgLen : ℕ} {G : Signer msgLen} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing PublicKey N → RMsg → (Fin msgLen → UInt8)}
  {O : SignOracle (falconBaseSigner (X := X) (Y := Y) G bmsg)}

/-- **Falcon-512 is EUF-CMA for the class `𝒜`** (Falcon specification v1.2 §2.2.1; module
docstring): every single-user adversary of `𝒜` against the Falcon-512 base signer with the signer
`G` has success probability at most `ε` in EUF-CMA with `Q` requests. -/
def Falcon512EufCma (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  SUEufCmaHard 𝒜 Q ε

/-- **Falcon-512 is MU-EUF-CMA^corr for the class `𝒜`**: every adversary of `𝒜` against `n` users
of the Falcon-512 base signer with the signer `G` has success probability at most `ε` in
MU-EUF-CMA^corr with `Q` requests. -/
def Falcon512MUEufCma (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUEufCmaHard 𝒜 Q ε

/-- **Falcon-512 is MU-EUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (Falcon specification v1.2 §2.2.1; module docstring): every adversary of `𝒜` against
`n` users of the Falcon-512 base signer with the signer `G`, against the challenger answering `Q'`
requests, wins MU-EUF-CMA^corr with at most `Qs` signing and corruption requests with probability
at most `ε`. -/
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

end Falcon

end GordieHowe.Ring
