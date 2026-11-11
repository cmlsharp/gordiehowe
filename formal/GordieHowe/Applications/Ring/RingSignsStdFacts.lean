-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSigners
public import GordieHowe.Model.Signature.RingStdToStd

@[expose] public section

/-!
# The base signers of the generic rings sign rings as the ordinary signer

The Falcon-512 and ML-DSA base signers of `GordieHowe/Applications/Ring/BaseSigners.lean` sign a
ring and a message by signing the base message `bmsg R m` as the ordinary signer does
(`BaseSigner.RingSignsStd`), so their key-reuse games reduce to the standard multi-user game
(`Signature.muEufProbWithin_ringStd_le_std`).

- `falconBaseSigner_ringSignsStd`, `mldsaBaseSigner_ringSignsStd`.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature

variable {X Y : Type} {N : ℕ}

/-- **The Falcon-512 base signer signs a ring as the ordinary signer on the base message.** -/
theorem falconBaseSigner_ringSignsStd {msgLen : ℕ} (G : Falcon512.Signer msgLen)
    {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing Falcon512.PublicKey N → RMsg → (Fin msgLen → UInt8)) :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).RingSignsStd :=
  BaseSigner.ofCore_ringSignsStd _ _

open _root_.MLDSA in
/-- **The ML-DSA base signer signs a ring as the ordinary signer on the base message.** -/
theorem mldsaBaseSigner_ringSignsStd (p : Params) (prims : Primitives p) [NTTRingOps]
    [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
    [DecidableEq prims.Hint] (maxAttempts : ℕ) {len : ℕ} {RMsg : Type} [Fintype RMsg]
    [DecidableEq RMsg] (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len) :
    (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).RingSignsStd :=
  BaseSigner.ofCore_ringSignsStd _ _

end GordieHowe.Ring
