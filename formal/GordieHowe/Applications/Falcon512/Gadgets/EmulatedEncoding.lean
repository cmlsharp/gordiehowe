-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Applications.Params
public import GordieHowe.Foundations.Algebra.IntLift

@[expose] public section

/-!
# Intended emulated Falcon encodability checks

The C++ transcription is `lib/schemes/falcon/falcon_encoding.h`
(`falcon_encoding_emulated`); the requests agree with this file one for one. No signature bytes are computed here. The external codec theorem consumes
the coefficient and high-part bounds derived from these lookup requests.

The two existing s2 magnitude advice values become the magnitude `a` and its
high part `h`. Looking up `a`, `h`, and `16*(a-128*h)` in table 2048 establishes
the coefficient split after integer lifting. The final lookup bounds the
sum of high parts by the parameter-derived encoding budget.
-/

namespace GordieHowe.Falcon512.EmulatedEncoding

variable {F : Type*} [Field F]

/-- Natural magnitudes recovered from the lookup, with their encoding budget. -/
structure Lifted (P : Params) (a : Fin P.n → F) (mags : Fin P.n → ℕ) : Prop where
  bounded : ∀ i, mags i < Codec.magnitudeBound
  cast_eq : ∀ i, (mags i : F) = a i
  highSum : ∑ i, mags i / Codec.lowRadix ≤ P.encodingHighBudget

end GordieHowe.Falcon512.EmulatedEncoding
