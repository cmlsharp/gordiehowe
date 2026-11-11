-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Ideal
public import GordieHowe.Applications.MLDSA.Signing.Flatten

@[expose] public section

/-!
# The random oracles of ML-DSA signing

* `MuOrc`, `ChOrc`, `SchOrc`, `Orc`, `schemeOrc`: the message-representative oracle
  `µ = H(tr ‖ M′)` (FIPS 204 Algorithm 7 line 6), the commitment-hash oracle
  `c̃ = H(µ ‖ w1Encode(w₁))` (line 15) on bucket vectors `w₁`, the pair of them, and their
  composition `H((tr, m), w₁)`.
* `MLDSAOracles`: the two oracles inside one random oracle `X → Y`: their points embedded in `X`
  and their values decoded from `Y`; `MLDSAOracles.muOrc`, `MLDSAOracles.chOrc`,
  `MLDSAOracles.hOrc`: the oracles read from it.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA

variable {p : Params} (prims : Primitives p)

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]
  {Msg : Type} [Fintype Msg] [DecidableEq Msg]

/-- **The commitment hash of a message point and a bucket vector**, as the base signer and the
verifier read it (`ringVerify`): `H((tr, m), w₁)`, the composition `H(µ ‖ w1Encode(w₁))` with
`µ = H(tr ‖ m)` of the game's two oracles (`schemeOrc`). -/
abbrev Orc (p : Params) (Msg : Type) : Type := (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p

/-- **The message-representative oracle**: `µ = H(tr ‖ M′)` (FIPS 204 Algorithm 7 line 6) on the
points `(tr, m)`. -/
abbrev MuOrc (Msg : Type) : Type := Bytes 64 × Msg → Bytes 64

/-- **The commitment-hash oracle**: `c̃ = H(µ ‖ w1Encode(w₁))` (FIPS 204 Algorithm 7 line 15) on
the points `(µ, w₁)`. -/
abbrev ChOrc (p : Params) : Type := Bytes 64 × BucketVec p → CommitHashBytes p

/-- **The scheme's oracles**: the message-representative oracle and the commitment-hash oracle,
independent random oracles in the game. -/
abbrev SchOrc (p : Params) (Msg : Type) : Type := MuOrc Msg × ChOrc p

/-- **The commitment hash of the scheme's oracles**: `H((tr, m), w₁) = H(µ ‖ w1Encode(w₁))` with
`µ = H(tr ‖ m)`. -/
def schemeOrc (H : SchOrc p Msg) : Orc p Msg := fun x => H.2 (H.1 x.1, x.2)

end GordieHowe.MLDSA

namespace GordieHowe.MLDSA

open _root_.MLDSA

variable {X Y : Type} {N : ℕ}

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  {Msg : Type} {reps : ℕ}

/-- **The oracles of ML-DSA inside the one random oracle `X → Y`**: the points of the
message-representative oracle `H_µ(tr, m)` (`µ = H(tr ‖ M′)`, FIPS 204 Algorithm 7 line 6) and of
the commitment-hash oracle `H(µ, w₁)` (`c̃ = H(µ ‖ w1Encode(w₁))`, line 15) embedded in `X`, and
their values decoded from `Y`. -/
structure MLDSAOracles (X Y : Type) (p : Params) (Msg : Type) where
  /-- The points of the message-representative oracle. -/
  muPt : Bytes 64 × Msg → X
  /-- The values of the message-representative oracle. -/
  muAns : Y → Bytes 64
  /-- The points of the commitment-hash oracle. -/
  chPt : Bytes 64 × BucketVec p → X
  /-- The values of the commitment-hash oracle. -/
  chAns : Y → CommitHashBytes p

variable {prims}

/-- The message-representative oracle `H_µ` read from the oracle. -/
def MLDSAOracles.muOrc (O : MLDSAOracles X Y p Msg) (H : X → Y) : MuOrc Msg :=
  fun pt => O.muAns (H (O.muPt pt))

/-- The commitment-hash oracle on `(µ, w₁)` read from the oracle. -/
def MLDSAOracles.chOrc (O : MLDSAOracles X Y p Msg) (H : X → Y) : ChOrc p :=
  fun pt => O.chAns (H (O.chPt pt))

/-- **The commitment hash** `H((tr, m), w₁) = H(H_µ(tr, m), w₁)` read from the oracle
(`schemeOrc`). -/
def MLDSAOracles.hOrc (O : MLDSAOracles X Y p Msg) (H : X → Y) : Orc p Msg :=
  schemeOrc (O.muOrc H, O.chOrc H)

end GordieHowe.MLDSA
