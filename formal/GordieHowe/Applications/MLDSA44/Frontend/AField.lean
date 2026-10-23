-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Semantics
public import GordieHowe.Foundations.Fields.Goldilocks

@[expose] public section

/-!
# GordieHowe frontend: the field facts of an emulated ML-DSA program's domain `A`

The emulated ML-DSA programs carry domain `A` over a Goldilocks extension: Goldilocks² at the ROM
parameters (`GordieHowe.RealizedProgram.gold2`), Goldilocks⁴ at the QROM parameters
(`GordieHowe.RealizedProgram.gold4`). The emulated
frontend reads domain `A` only through the facts below (`GordieHowe.MLDSA44.AField`), discharged once per field
(the instances sit with each configuration): characteristic `p = 2^64 − 2^32 + 1`, constants decode
as casts, and the integer reading reads a natural below `p` as itself (the constant coordinate).
-/

namespace GordieHowe.RealizedProgram

/-- **The field facts of an emulated program's domain `A`**: characteristic `pGold` (also as the
registry entry states it), constants as casts, and the integer reading of a natural below `pGold`. -/
class _root_.GordieHowe.MLDSA44.AField (F0 : FieldInterp) : Prop where
  /-- The field has characteristic `pGold`. -/
  charP : CharP F0.K pGold
  /-- The registry entry's characteristic is `pGold`. -/
  char_spec : F0.spec.characteristic = pGold
  /-- Constants decode as casts. -/
  decode_eq : ∀ c, F0.decode c = (c : F0.K)
  /-- A natural below `pGold` is read as itself. -/
  toNat_natCast : ∀ k < pGold, F0.toNat (k : F0.K) = k

instance _root_.GordieHowe.MLDSA44.AField.instCharP (F0 : FieldInterp) [h : MLDSA44.AField F0] : CharP F0.K pGold :=
  h.charP

end GordieHowe.RealizedProgram
