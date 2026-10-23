-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.ProtocolReduction
public import GordieHowe.ProofSystem.GKR.CircuitFlatten

@[expose] public section

/-!
# Source-derived GKR transcript reduction

The concrete protocol, challenges, errors, interpolation coefficients, wiring
values, and terminal claim are constructed from the recursive source circuit.
The caller supplies its functional compiler theorem; no GKR soundness or
transcript-correspondence premise remains in this constructor.
-/
namespace GordieHowe.GKR.SourceReduction
open IOP
open GKR.Circuit CircuitFlatten Schedule ProtocolEvents
section
variable {F Pub Wit : Type} [Field F] [Fintype F]

/-- **The concrete GKR interaction of a source circuit** (computable): the typed schedule, the
terminal input points and the flat transcript computed from the source circuit and the challenge
stream (`CircuitFlatten.transcript`). Its soundness is `ofCircuitSound`. -/
def ofCircuit [DecidableEq F] (nodes : Sumcheck.Nodes F) {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim) :
    Transcript.Interaction F (PadIndex (.layer Q tail)) tail.inputDim
      (layout Q tail) where
  n := 1 + circuitLength F (.layer Q tail)
  spec := Schedule.spec F (.layer Q tail)
  g0 t := (inputPoints nodes (.layer Q tail)
    (initialPoint F _ t) (initialPoint F _ t) (trace F _ t)).1
  g1 t := (inputPoints nodes (.layer Q tail)
    (initialPoint F _ t) (initialPoint F _ t) (trace F _ t)).2
  transcript t := CircuitFlatten.transcript nodes Q tail
    (initialPoint F _ t) (initialPoint F _ t) (trace F _ t)

/-- **Soundness of the source GKR interaction** on the caller's fixed input and pad readouts, with
the per-round errors `ProtocolReduction.error`; the caller supplies its functional compiler
theorem `hcompile`, and no GKR soundness or transcript-correspondence premise remains. -/
noncomputable def ofCircuitSound [DecidableEq F] (nodes : Sumcheck.Nodes F) {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim)
    (input : Pub → Wit → Fin (2^tail.inputDim) → F)
    (pad : Wit → PadIndex (.layer Q tail) → F)
    (sat : Pub → Wit → Prop)
    (hcompile : ∀ pub w, (Circuit.layer Q tail).Satisfied (input pub w) → sat pub w) :
    (ofCircuit nodes Q tail).Sound input pad sat
      (ProtocolReduction.error F (.layer Q tail)) where
  reduction := ((ProtocolReduction.reduction F nodes (.layer Q tail)).comap
    (fun pw : Pub × Wit => (input pw.1 pw.2, pads _ (pad pw.2)))).weakenClaim
      (fun pw => sat pw.1 pw.2) (fun pw h => hcompile pw.1 pw.2 h)
  claim_iff _ _ := Iff.rfl
  claimOut_iff pub w t :=
    (CircuitFlatten.terminal_iff nodes Q tail
      (initialPoint F _ t) (initialPoint F _ t) (trace F _ t) (pad w) (input pub w)).symm

end
end GordieHowe.GKR.SourceReduction
