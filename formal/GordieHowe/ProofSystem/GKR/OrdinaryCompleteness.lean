-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.ProofSystem.GKR.TranscriptRouting

@[expose] public section

/-! Honest source GKR with committed pads proves the exact ordinary-half
terminal equations.

The honest prover draws free pads `π : FreePads S.circuit`; the committed pads
are `π.pads`, whose product pad is `claim 0 * claim 1`, so `ProductsHold`
holds by construction. The prover sends the masked honest trace
(`GKR.HonestTranscript.maskedFamily`). The witness carries the pads at the pad
coordinates: `withPads pad w π` writes the flat pad vector `padValues π` there
and keeps the source values `w` elsewhere. Completeness holds for every pad
value and every verifier challenge. -/
namespace GordieHowe.GKR.LayeredCircuit
open IOP
open LayeredCircuit HonestTranscript GKR.Circuit PadTranslation CircuitFlatten
open scoped Classical
variable {F Pub ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] {d N R : ℕ}

/-- The flat pad vector of the free pads `π`, with the derived product pads. -/
def padValues (S : LayeredCircuit F d) (π : FreePads S.circuit) : S.PadIdx → F :=
  flatPads S.circuit π.pads

/-- Soundness of the source GKR interaction on the affine input `I` with pads at `pad`, for
satisfaction of the source circuit on the input. -/
noncomputable def soundIP (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι) :=
  S.sound nodes I.input (fun w => w ∘ pad)
    (fun pub w => S.Satisfied (I.input pub w)) (fun _ _ h => h)

/-- The source prover sends the masked honest trace for the committed pads
`π.pads`; it uses only its fixed coordinate assignment and past coins. -/
def family (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι)
    (pub : Pub) (w : ι → F) (π : FreePads S.circuit) :
    CausalTranscript (S.interaction nodes).spec := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact HonestTranscript.maskedFamily nodes (.layer Q tail) (I.input pub w)
      π.pads

omit [Fintype ι] in
/-- The honest family reads the public input and the witness only through the
circuit input. -/
theorem family_congr (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι)
    {pub pub' : Pub} {w w' : ι → F} (h : I.input pub w = I.input pub' w')
    (π : FreePads S.circuit) :
    family S nodes I pad pub w π = family S nodes I pad pub' w' π := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact congrArg (fun x => maskedFamily nodes _ x π.pads) h

/-- **The simulated source GKR transcript**: `GKR.HonestTranscript.valueFamily`, which sends the
values `vals` in the shape of the free pads and runs no prover. -/
def valueFamily (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι) (vals : FreePads S.circuit) :
    CausalTranscript (S.interaction nodes).spec := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact HonestTranscript.valueFamily (.layer Q tail) vals

omit [Fintype ι] in
/-- **Hiding of the source GKR transcript.** For fixed challenges, the honest transcript under
uniform free pads has the law of `valueFamily` under uniform values, on every public input and
witness (`GKR.HonestTranscript.maskedFamily_identDistrib`). -/
theorem family_identDistrib (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι)
    (pub : Pub) (w : ι → F) (ch : (S.interaction nodes).spec.Challenges) :
    (fun π : FreePads S.circuit => (family S nodes I pad pub w π).transcript ch) =ᵈ
      (fun vals : FreePads S.circuit => (valueFamily S nodes I pad vals).transcript ch) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact maskedFamily_identDistrib nodes _ _ ch

omit [Fintype ι] in
/-- The premises are the honest input: the witness holds the pad values of `π`
at the pad coordinates, and the source circuit is satisfied. Every pad value
and every verifier challenge is permitted. -/
theorem claimOut (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (I : SourceInput.InputForms F ι Pub d) (pad : S.PadIdx → ι)
    (pub : Pub) (w : ι → F) (π : FreePads S.circuit) (hpad : w ∘ pad = padValues S π)
    (h : S.Satisfied (I.input pub w))
    (ch : (S.interaction nodes).spec.Challenges) :
    (soundIP S nodes I pad).reduction.claimOut (pub,w)
      ((family S nodes I pad pub w π).transcript ch) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    change ProtocolEvents.terminal F nodes (.layer Q tail)
      (I.input pub w, CircuitFlatten.pads _ (w ∘ pad)) _
    erw [hpad]
    unfold padValues
    erw [pads_flatPads]
    exact maskedFamily_terminal nodes _ _ _ h π.productsHold ch

end GordieHowe.GKR.LayeredCircuit
