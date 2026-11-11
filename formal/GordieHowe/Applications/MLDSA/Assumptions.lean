-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Scheme
public import GordieHowe.Applications.MLDSA.SchemeT0
public import GordieHowe.Model.Signature.Assumptions

@[expose] public section

/-!
# The named unforgeability assumptions on ML-DSA

The strong unforgeability of the ML-DSA signature scheme `mldsaBaseScheme p prims maxAttempts len`
(`GordieHowe/Applications/MLDSA/Scheme.lean`) as the predicates of
`GordieHowe/Model/Signature/Assumptions.lean`, for a theorem to take as hypotheses. Each predicate
is a bound `ε` for a named class `𝒜` of adversaries with `Q` requests, at any signing oracle of
the scheme.

- `MLDSASufCma 𝒜 Q ε` (one user) and `MLDSAMUSufCma 𝒜 Q ε` (`n` users with adaptive corruption),
  at any parameter set `p`; `MLDSA44SufCma`, `MLDSA65SufCma`, `MLDSA87SufCma` and the multi-user
  `MLDSA44MUSufCma`, `MLDSA65MUSufCma`, `MLDSA87MUSufCma`: at ML-DSA-44, ML-DSA-65, ML-DSA-87.
- `MLDSAMUSufCmaWithin 𝒜 Q' Qs ε` and `MLDSA44MUSufCmaWithin`, `MLDSA65MUSufCmaWithin`,
  `MLDSA87MUSufCmaWithin`: the multi-user predicates with at most `Qs` signing and corruption
  requests counted among `Q'` answered requests; `MLDSAMUSufCmaWithin.le_muEufProbWithin`: the
  bound on `muEufProbWithin` for a member; `MLDSAMUSufCma.within`: the predicate counting every
  request gives these at every `Qs`.

The scheme computes every hash with the primitives `prims` it is given (fixed functions, the
FIPS 202 functions at the concrete primitives) and never reads the game's oracle: signing makes no
query and verification ignores the oracle (`mldsaBaseScheme`'s fields `q := 0`, `qPub := 0` and
`bverify`). So these predicates are standard-model assumptions on the scheme with those hash
functions: the game's random oracle plays no part. Random-oracle and quantum-random-oracle proofs
of the scheme (below) do not bound them as defined. Because verification reads no oracle, no bound
below `1` holds for the unrestricted class when every key has a verifying signature
(`Signature.not_muEufCmaHard_univ_of_bverify_eq`, under `Signable`), so a meaningful class `𝒜`
leaves out adversaries such as `Signature.drawBruteAdv`, which reads a forgery off the public key.

Source: FIPS 204, §3.1, p. 9, for the deployed scheme: "ML-DSA is designed to be strongly
existentially unforgeable under chosen message attack (SUF-CMA)." For comparison only: Kiltz,
Lyubashevsky, Schaffner (EUROCRYPT 2018, ePrint 2017/916), Theorem 3.1 and eq. (21), bound the
sUF-CMA advantage of (deterministic) Dilithium with `H` a quantum random oracle by MLWE,
SelfTargetMSIS and MSIS advantages; Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang,
Hülsing, Lee, Wu ("Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and
Dilithium", ePrint 2023/246) and Devevey, Fallahpour, Passelègue, Stehlé ("A Detailed Analysis of
Fiat-Shamir with Aborts", ePrint 2023/245) report a gap in that paper's reduction from
chosen-message to no-message attacks (Theorem 3.2) and give corrected reductions in the ROM and
the QROM. These are single-user statements in a random-oracle model; this library does not
derive the predicates from them. The library proves none of these statements; the predicates name
them.

## `t₀` published

- `MLDSAT0EufCma`, `MLDSAT0MUEufCma`, `MLDSAT0MUEufCmaWithin` (EUF-CMA: one user, `n` users with
  adaptive corruption, and the multi-user form counting at most `Qs` signing and corruption
  requests) and `MLDSAT0EufNma`, `MLDSAT0MUEufNma` (EUF-NMA, one user and `n` users with
  corruption): these games at the ML-DSA signer whose public key is `(ρ, t₁, t₀)`
  (`mldsaT0BaseScheme`, keys from `keyGen`), at any signing oracle of it: the
  standard call oracle `Rejection.stdOracle` (one call of hedged FIPS 204 signing), which the
  ring-binding theorems reach, and `SignOracle.none`, which the converted scheme's theorems reach.
  `MLDSA44T0EufCma` … `MLDSA87T0MUEufNma`: at ML-DSA-44, ML-DSA-65 and ML-DSA-87. This signer reads
  the game's random oracle (the message representative, the commitment hash and the masks are its
  points, and verification reads the commitment hash), so these are random-oracle assumptions.
- The justification: analyses of ML-DSA's unforgeability typically take `t₀` to be public
  (uncited), and FIPS 204, §6.1, p. 22, says of the low-order bits of `t` that the public key drops:
  "The low-order bits of 𝐭 can be reconstructed from a small number of signatures and, therefore,
  need not be regarded as secret." The library proves neither that `t₀` can be recovered from
  signatures nor that these predicates follow from the predicates above.
-/

namespace GordieHowe.MLDSA

open GordieHowe.Signature GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {n : ℕ} {V : OracleView X Y} {t : ℕ}

/-! ### ML-DSA -/

section MLDSA

open _root_.MLDSA

variable {p : Params} {prims : Primitives p} [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] {maxAttempts : ℕ}
  {len : ℕ} {O : SignOracle (mldsaBaseScheme (X := X) (Y := Y) p prims maxAttempts len)}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

/-- **ML-DSA is SUF-CMA for the class `𝒜`** (FIPS 204 §3.1; module docstring): every single-user
adversary of `𝒜` against the ML-DSA signature scheme `mldsaBaseScheme` at the parameter set `p` has
success probability at most `ε` in SUF-CMA with `Q` requests. -/
def MLDSASufCma (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  SUSufCmaHard 𝒜 Q ε

/-- **ML-DSA is MU-SUF-CMA^corr for the class `𝒜`**: every adversary of `𝒜` against `n` users of
the ML-DSA signature scheme `mldsaBaseScheme` at the parameter set `p` has success probability at
most `ε` in MU-SUF-CMA^corr with `Q` requests. -/
def MLDSAMUSufCma (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUSufCmaHard 𝒜 Q ε

/-- **ML-DSA is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (FIPS 204 §3.1; module docstring): every adversary of `𝒜` against `n` users of the
ML-DSA signature scheme `mldsaBaseScheme` at the parameter set `p`, against the challenger answering
`Q'` requests, wins MU-SUF-CMA^corr with at most `Qs` signing and corruption requests with
probability at most `ε`. -/
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

/-- **ML-DSA-44 is SUF-CMA for the class `𝒜`** (`MLDSASufCma` at `MLDSA.mldsa44`). -/
abbrev MLDSA44SufCma [Fintype prims44.Power2High] [DecidableEq prims44.Power2High]
    [Fintype prims44.Hint] [DecidableEq prims44.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa44 prims44 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSASufCma 𝒜 Q ε

/-- **ML-DSA-65 is SUF-CMA for the class `𝒜`** (`MLDSASufCma` at `MLDSA.mldsa65`). -/
abbrev MLDSA65SufCma [Fintype prims65.Power2High] [DecidableEq prims65.Power2High]
    [Fintype prims65.Hint] [DecidableEq prims65.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa65 prims65 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSASufCma 𝒜 Q ε

/-- **ML-DSA-87 is SUF-CMA for the class `𝒜`** (`MLDSASufCma` at `MLDSA.mldsa87`). -/
abbrev MLDSA87SufCma [Fintype prims87.Power2High] [DecidableEq prims87.Power2High]
    [Fintype prims87.Hint] [DecidableEq prims87.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa87 prims87 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSASufCma 𝒜 Q ε

/-- **ML-DSA-44 is MU-SUF-CMA^corr for the class `𝒜`** (`MLDSAMUSufCma` at `MLDSA.mldsa44`). -/
abbrev MLDSA44MUSufCma [Fintype prims44.Power2High] [DecidableEq prims44.Power2High]
    [Fintype prims44.Hint] [DecidableEq prims44.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa44 prims44 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCma 𝒜 Q ε

/-- **ML-DSA-44 is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (`MLDSAMUSufCmaWithin` at `MLDSA.mldsa44`). -/
abbrev MLDSA44MUSufCmaWithin [Fintype prims44.Power2High] [DecidableEq prims44.Power2High]
    [Fintype prims44.Hint] [DecidableEq prims44.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa44 prims44 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-65 is MU-SUF-CMA^corr for the class `𝒜`** (`MLDSAMUSufCma` at `MLDSA.mldsa65`). -/
abbrev MLDSA65MUSufCma [Fintype prims65.Power2High] [DecidableEq prims65.Power2High]
    [Fintype prims65.Hint] [DecidableEq prims65.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa65 prims65 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCma 𝒜 Q ε

/-- **ML-DSA-65 is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (`MLDSAMUSufCmaWithin` at `MLDSA.mldsa65`). -/
abbrev MLDSA65MUSufCmaWithin [Fintype prims65.Power2High] [DecidableEq prims65.Power2High]
    [Fintype prims65.Hint] [DecidableEq prims65.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa65 prims65 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-87 is MU-SUF-CMA^corr for the class `𝒜`** (`MLDSAMUSufCma` at `MLDSA.mldsa87`). -/
abbrev MLDSA87MUSufCma [Fintype prims87.Power2High] [DecidableEq prims87.Power2High]
    [Fintype prims87.Hint] [DecidableEq prims87.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa87 prims87 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCma 𝒜 Q ε

/-- **ML-DSA-87 is MU-SUF-CMA^corr for the class `𝒜` with at most `Qs` signing and corruption
requests** (`MLDSAMUSufCmaWithin` at `MLDSA.mldsa87`). -/
abbrev MLDSA87MUSufCmaWithin [Fintype prims87.Power2High] [DecidableEq prims87.Power2High]
    [Fintype prims87.Hint] [DecidableEq prims87.Hint]
    {O : SignOracle
      (mldsaBaseScheme (X := X) (Y := Y) _root_.MLDSA.mldsa87 prims87 maxAttempts len)}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAMUSufCmaWithin 𝒜 Q' Qs ε

end MLDSAParams

/-! ### ML-DSA with `t₀` published -/

section MLDSAT0

open _root_.MLDSA

variable {p : Params} {prims : Primitives p} [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] {Msg : Type}
  [Fintype Msg] [DecidableEq Msg]
  {W : MLDSAOracles X Y p Msg} {enc : Vector prims.High p.k → BucketVec p} {CL : Type}
  [Fintype CL] [DecidableEq CL] [Nonempty CL] {S : T0Signer X Y p prims Msg CL}
  {O : SignOracle (mldsaT0BaseScheme prims W enc S)}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

/-- **ML-DSA with `t₀` published is EUF-CMA for the class `𝒜`** (module docstring, section
"`t₀` published"): every single-user adversary of `𝒜`, against the signing oracle `O` of the
ML-DSA signer whose public keys are `(ρ, t₁, t₀)` (`mldsaT0BaseScheme`, `keyGen`), has success
probability at most `ε` in EUF-CMA with `Q` requests. -/
def MLDSAT0EufCma (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  SUEufCmaHard 𝒜 Q ε

/-- **ML-DSA with `t₀` published is MU-EUF-CMA^corr for the class `𝒜`**: every adversary of `𝒜`
against `n` users, at the signing oracle `O`, has success probability at most `ε` in
MU-EUF-CMA^corr with `Q` requests. -/
def MLDSAT0MUEufCma (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUEufCmaHard 𝒜 Q ε

/-- **ML-DSA with `t₀` published is MU-EUF-CMA^corr for the class `𝒜` with at most `Qs` signing
and corruption requests** among `Q'` answered requests (`Signature.MUEufCmaHardWithin`): the form
that bounds the right-hand side of the ring-binding unforgeability theorems
(`muEufProbWithin` at `Rejection.stdOracle`). -/
def MLDSAT0MUEufCmaWithin (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUEufCmaHardWithin 𝒜 Q' Qs ε

omit [Fintype Msg] [DecidableEq Msg] [Fintype CL] [DecidableEq CL] [Nonempty CL] in
/-- **The bound on `muEufProbWithin` from `MLDSAT0MUEufCmaWithin`** for a member `A` of the
class. -/
theorem MLDSAT0MUEufCmaWithin.le_muEufProbWithin {𝒜 : Set (MUAdversary O n V t)} {Q' Qs : ℕ}
    {ε : ℝ≥0∞} (h : MLDSAT0MUEufCmaWithin 𝒜 Q' Qs ε) {A : MUAdversary O n V t} (hA : A ∈ 𝒜) :
    muEufProbWithin A Q' Qs ≤ ε :=
  h A hA

omit [Fintype Msg] [DecidableEq Msg] [Fintype CL] [DecidableEq CL] [Nonempty CL] in
/-- **`MLDSAT0MUEufCma` with `Q'` requests gives `MLDSAT0MUEufCmaWithin`** at every `Qs`. -/
theorem MLDSAT0MUEufCma.within {𝒜 : Set (MUAdversary O n V t)} {Q' : ℕ} {ε : ℝ≥0∞}
    (h : MLDSAT0MUEufCma 𝒜 Q' ε) (Qs : ℕ) : MLDSAT0MUEufCmaWithin 𝒜 Q' Qs ε :=
  MUEufCmaHard.muEufCmaHardWithin h Qs

/-- **ML-DSA with `t₀` published is EUF-NMA for the class `𝒜`**: every single-user adversary of
`𝒜` against the signer with no signing requests has success probability at most `ε` with `Q`
requests. -/
def MLDSAT0EufNma
    (𝒜 : Set (SUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) V t))
    (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  SUEufNmaHard 𝒜 Q ε

/-- **ML-DSA with `t₀` published is MU-EUF-NMA^corr for the class `𝒜`**: every adversary of `𝒜`
against `n` users with no signing requests (public keys and corruption only) has success
probability at most `ε` with `Q` requests (`Signature.MUEufNmaHard`): the form that bounds the
right-hand side of the converted scheme's unforgeability theorems (`muEufNmaProb`). -/
def MLDSAT0MUEufNma
    (𝒜 : Set (MUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) n V t))
    (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MUEufNmaHard 𝒜 Q ε

omit [Fintype Msg] [DecidableEq Msg] [Fintype CL] [DecidableEq CL] [Nonempty CL] in
/-- **The bound on `muEufNmaProb` from `MLDSAT0MUEufNma`** for a member `A` of the class. -/
theorem MLDSAT0MUEufNma.le_muEufNmaProb
    {𝒜 : Set (MUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) n V t)}
    {Q : ℕ} {ε : ℝ≥0∞} (h : MLDSAT0MUEufNma 𝒜 Q ε)
    {A : MUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) n V t}
    (hA : A ∈ 𝒜) : muEufNmaProb A Q ≤ ε :=
  h A hA

end MLDSAT0

section MLDSAT0Params

open _root_.MLDSA

variable [nttOps : NTTRingOps] {Msg : Type} [Fintype Msg] [DecidableEq Msg] {CL : Type}
  [Fintype CL] [DecidableEq CL] [Nonempty CL]

/-- **ML-DSA-44 with `t₀` published is EUF-CMA for the class `𝒜`**
(`MLDSAT0EufCma` at ML-DSA-44). -/
abbrev MLDSA44T0EufCma {prims : Primitives _root_.MLDSA.mldsa44} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y _root_.MLDSA.mldsa44 Msg}
    {enc : Vector prims.High _root_.MLDSA.mldsa44.k → BucketVec _root_.MLDSA.mldsa44}
    {S : T0Signer X Y _root_.MLDSA.mldsa44 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0EufCma 𝒜 Q ε

/-- **ML-DSA-44 with `t₀` published is MU-EUF-CMA^corr for the class `𝒜`** (`MLDSAT0MUEufCma` at
ML-DSA-44). -/
abbrev MLDSA44T0MUEufCma {prims : Primitives _root_.MLDSA.mldsa44} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y _root_.MLDSA.mldsa44 Msg}
    {enc : Vector prims.High _root_.MLDSA.mldsa44.k → BucketVec _root_.MLDSA.mldsa44}
    {S : T0Signer X Y _root_.MLDSA.mldsa44 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufCma 𝒜 Q ε

/-- **ML-DSA-44 with `t₀` published is MU-EUF-CMA^corr for the class `𝒜` with at most `Qs` signing
and corruption requests** (`MLDSAT0MUEufCmaWithin` at ML-DSA-44). -/
abbrev MLDSA44T0MUEufCmaWithin {prims : Primitives _root_.MLDSA.mldsa44} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y _root_.MLDSA.mldsa44 Msg}
    {enc : Vector prims.High _root_.MLDSA.mldsa44.k → BucketVec _root_.MLDSA.mldsa44}
    {S : T0Signer X Y _root_.MLDSA.mldsa44 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-44 with `t₀` published is EUF-NMA for the class `𝒜`**
(`MLDSAT0EufNma` at ML-DSA-44). -/
abbrev MLDSA44T0EufNma {prims : Primitives _root_.MLDSA.mldsa44} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y _root_.MLDSA.mldsa44 Msg}
    {enc : Vector prims.High _root_.MLDSA.mldsa44.k → BucketVec _root_.MLDSA.mldsa44}
    {S : T0Signer X Y _root_.MLDSA.mldsa44 prims Msg CL}
    (𝒜 : Set (SUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) V t)) (Q : ℕ)
    (ε : ℝ≥0∞) : Prop :=
  MLDSAT0EufNma 𝒜 Q ε

/-- **ML-DSA-44 with `t₀` published is MU-EUF-NMA^corr for the class `𝒜`** (`MLDSAT0MUEufNma` at
ML-DSA-44). -/
abbrev MLDSA44T0MUEufNma {prims : Primitives _root_.MLDSA.mldsa44} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y _root_.MLDSA.mldsa44 Msg}
    {enc : Vector prims.High _root_.MLDSA.mldsa44.k → BucketVec _root_.MLDSA.mldsa44}
    {S : T0Signer X Y _root_.MLDSA.mldsa44 prims Msg CL}
    (𝒜 : Set (MUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) n V t))
    (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufNma 𝒜 Q ε

/-- **ML-DSA-65 with `t₀` published is EUF-CMA for the class `𝒜`**
(`MLDSAT0EufCma` at ML-DSA-65). -/
abbrev MLDSA65T0EufCma {prims : Primitives mldsa65} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa65 Msg}
    {enc : Vector prims.High mldsa65.k → BucketVec mldsa65}
    {S : T0Signer X Y mldsa65 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0EufCma 𝒜 Q ε

/-- **ML-DSA-65 with `t₀` published is MU-EUF-CMA^corr for the class `𝒜`** (`MLDSAT0MUEufCma` at
ML-DSA-65). -/
abbrev MLDSA65T0MUEufCma {prims : Primitives mldsa65} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa65 Msg}
    {enc : Vector prims.High mldsa65.k → BucketVec mldsa65}
    {S : T0Signer X Y mldsa65 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufCma 𝒜 Q ε

/-- **ML-DSA-65 with `t₀` published is MU-EUF-CMA^corr for the class `𝒜` with at most `Qs` signing
and corruption requests** (`MLDSAT0MUEufCmaWithin` at ML-DSA-65). -/
abbrev MLDSA65T0MUEufCmaWithin {prims : Primitives mldsa65} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa65 Msg}
    {enc : Vector prims.High mldsa65.k → BucketVec mldsa65}
    {S : T0Signer X Y mldsa65 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-65 with `t₀` published is EUF-NMA for the class `𝒜`**
(`MLDSAT0EufNma` at ML-DSA-65). -/
abbrev MLDSA65T0EufNma {prims : Primitives mldsa65} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa65 Msg}
    {enc : Vector prims.High mldsa65.k → BucketVec mldsa65}
    {S : T0Signer X Y mldsa65 prims Msg CL}
    (𝒜 : Set (SUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) V t)) (Q : ℕ)
    (ε : ℝ≥0∞) : Prop :=
  MLDSAT0EufNma 𝒜 Q ε

/-- **ML-DSA-65 with `t₀` published is MU-EUF-NMA^corr for the class `𝒜`** (`MLDSAT0MUEufNma` at
ML-DSA-65). -/
abbrev MLDSA65T0MUEufNma {prims : Primitives mldsa65} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa65 Msg}
    {enc : Vector prims.High mldsa65.k → BucketVec mldsa65}
    {S : T0Signer X Y mldsa65 prims Msg CL}
    (𝒜 : Set (MUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) n V t))
    (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufNma 𝒜 Q ε

/-- **ML-DSA-87 with `t₀` published is EUF-CMA for the class `𝒜`**
(`MLDSAT0EufCma` at ML-DSA-87). -/
abbrev MLDSA87T0EufCma {prims : Primitives mldsa87} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa87 Msg}
    {enc : Vector prims.High mldsa87.k → BucketVec mldsa87}
    {S : T0Signer X Y mldsa87 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0EufCma 𝒜 Q ε

/-- **ML-DSA-87 with `t₀` published is MU-EUF-CMA^corr for the class `𝒜`** (`MLDSAT0MUEufCma` at
ML-DSA-87). -/
abbrev MLDSA87T0MUEufCma {prims : Primitives mldsa87} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa87 Msg}
    {enc : Vector prims.High mldsa87.k → BucketVec mldsa87}
    {S : T0Signer X Y mldsa87 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufCma 𝒜 Q ε

/-- **ML-DSA-87 with `t₀` published is MU-EUF-CMA^corr for the class `𝒜` with at most `Qs` signing
and corruption requests** (`MLDSAT0MUEufCmaWithin` at ML-DSA-87). -/
abbrev MLDSA87T0MUEufCmaWithin {prims : Primitives mldsa87} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa87 Msg}
    {enc : Vector prims.High mldsa87.k → BucketVec mldsa87}
    {S : T0Signer X Y mldsa87 prims Msg CL}
    {O : SignOracle (mldsaT0BaseScheme prims W enc S)} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufCmaWithin 𝒜 Q' Qs ε

/-- **ML-DSA-87 with `t₀` published is EUF-NMA for the class `𝒜`**
(`MLDSAT0EufNma` at ML-DSA-87). -/
abbrev MLDSA87T0EufNma {prims : Primitives mldsa87} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa87 Msg}
    {enc : Vector prims.High mldsa87.k → BucketVec mldsa87}
    {S : T0Signer X Y mldsa87 prims Msg CL}
    (𝒜 : Set (SUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) V t)) (Q : ℕ)
    (ε : ℝ≥0∞) : Prop :=
  MLDSAT0EufNma 𝒜 Q ε

/-- **ML-DSA-87 with `t₀` published is MU-EUF-NMA^corr for the class `𝒜`** (`MLDSAT0MUEufNma` at
ML-DSA-87). -/
abbrev MLDSA87T0MUEufNma {prims : Primitives mldsa87} [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    {W : MLDSAOracles X Y mldsa87 Msg}
    {enc : Vector prims.High mldsa87.k → BucketVec mldsa87}
    {S : T0Signer X Y mldsa87 prims Msg CL}
    (𝒜 : Set (MUAdversary (SignOracle.none (mldsaT0BaseScheme prims W enc S)) n V t))
    (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  MLDSAT0MUEufNma 𝒜 Q ε

end MLDSAT0Params

end GordieHowe.MLDSA
