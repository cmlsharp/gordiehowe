-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.Ligero.Routing

@[expose] public section

/-!
# Fixed multiplication routing for masked GKR transcripts

Every layer's product operands and result are its three committed claim pads.
Their selectors depend only on the pad layout, fixed before commitment. Public
transcripts change the affine finalization equations but never these product
selectors. This bridge proves the GKR pad system is a source system for the
generic Ligero routing theorem. It does not identify concrete C++ addresses.
-/

namespace GordieHowe.GKR.TranscriptRouting
open IOP

variable {F ι PadIdx : Type} [Field F] {L : ℕ}

/-- The product support is independent of all public transcript values. -/
def products (layout : Transcript.Layout PadIdx L) (coord : PadIdx → ι) :
    Ligero.Routing.ProductLayout ι (Fin (L + 1)) where
  source l s := coord (layout.claimPad l s)

/-- The transcript-dependent portion consists only of affine finalization rows. -/
noncomputable def finals (layout : Transcript.Layout PadIdx L)
    (tr : GKR.Transcript F PadIdx L layout) (coord : PadIdx → ι)
    (l : Fin (L + 1)) : MvPolynomial ι F :=
  (Transcript.finalExpr layout tr coord l).polynomial

theorem finals_degree (layout : Transcript.Layout PadIdx L)
    (tr : GKR.Transcript F PadIdx L layout) (coord : PadIdx → ι)
    (l : Fin (L + 1)) : (finals layout tr coord l).totalDegree ≤ 1 :=
  Transcript.Affine.polynomial_degree _

/-- The fixed-product source presentation is precisely the existing GKR system. -/
theorem sourceSystem_eq (layout : Transcript.Layout PadIdx L)
    (tr : GKR.Transcript F PadIdx L layout) (coord : PadIdx → ι) :
    Ligero.Routing.sourceSystem (products layout coord) (finals layout tr coord)
      (finals_degree layout tr coord) = Transcript.system layout tr coord := rfl

/-- All source equations hold exactly when the unmasked GKR recurrence and
claim-product pad checks hold on the same assignment. -/
theorem sourceSystem_holds_iff (layout : Transcript.Layout PadIdx L)
    (tr : GKR.Transcript F PadIdx L layout) (coord : PadIdx → ι) (w : ι → F) :
    (Ligero.Routing.sourceSystem (products layout coord) (finals layout tr coord)
      (finals_degree layout tr coord)).Holds w ↔
        Transcript.PadOK layout tr (w ∘ coord) := by
  rw [sourceSystem_eq]
  exact Transcript.system_holds_iff layout tr coord w

end GordieHowe.GKR.TranscriptRouting
