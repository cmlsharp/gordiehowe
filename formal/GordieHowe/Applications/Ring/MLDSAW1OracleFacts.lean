-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1IdealDist
public import GordieHowe.Applications.Ring.MLDSAW1Split

@[expose] public section

/-!
# The oracle facts of the ML-DSA ring publishing `w₁`

The hypotheses on the base signer's oracles `O` and the mask oracle `M` that the hops from
BKM06 Definition 7 to the key-free relay challenger take, in components by the hops that use them
together, bundled as one structure for the headline.

- `W1MaskPoints O M`: the mask points are injective and disjoint from the base signer's points
  (the hop from hedged to fresh masks).
- `W1SplitMask O M`: the base signer's oracles are a uniform split (`W1Oracles.UniformSplit`) and
  the masks of a uniform value are uniform (the reprogramming hops).
- `W1ReadsFst O M sp`: the decodings of both oracles read only the first component of `sp`.
- `W1OracleFacts O M sp`: all three, which the headline takes.
- `W1SplitMask.hch`, `W1SplitMask.hdisj`, `W1SplitMask.hdisjg` (and the same on `W1OracleFacts`):
  the commitment-hash points are injective and differ from the message and check points
  (projections of the uniform split).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature PMF

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y] [Nonempty Y]
  {p : Params} {prims : Primitives p} {Msg : Type} {N reps T : ℕ} [Nonempty (MaskBox p)]

/-- **The mask points of the ring publishing `w₁`**: the mask points are injective, and the base
signer's points are not mask points (the facts of the hop from hedged to fresh masks). -/
structure W1MaskPoints (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) :
    Prop where
  /-- The mask points are injective. -/
  hMinj : Function.Injective M.pt
  /-- The base signer's points are not mask points. -/
  hdisjM : ∀ x, O.IsPt x → x ∉ Set.range M.pt

/-- **The split and the masks of the ring publishing `w₁`**: the base signer's oracles are a
uniform split (`W1Oracles.UniformSplit`: injective points with pairwise disjoint ranges and uniform
decodings), and the masks of a uniform value are uniform (the facts of the reprogramming hops). -/
structure W1SplitMask (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) :
    Prop where
  /-- The base signer's oracles are a uniform split. -/
  uniformSplit : O.UniformSplit
  /-- The masks of a uniform value are uniform. -/
  hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p)

/-- **The decodings of the ring publishing `w₁` read only the first component** of the split
`sp`. -/
structure W1ReadsFst (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (sp : Y ≃+ Y₁ × Y₂) : Prop where
  /-- The base signer's decodings read only the first component. -/
  hO : O.ReadsFst sp
  /-- The mask decoding reads only the first component. -/
  hM : M.ReadsFst sp

/-- **The oracle facts of the ring publishing `w₁`**: for the base signer's oracles `O`, the mask
oracle `M` and the split `sp` of the oracle's values, the mask points (`W1MaskPoints`), the split
and the masks (`W1SplitMask`) and the first-component decodings (`W1ReadsFst`). -/
structure W1OracleFacts (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (sp : Y ≃+ Y₁ × Y₂) : Prop extends W1MaskPoints O M, W1SplitMask O M, W1ReadsFst O M sp

namespace W1SplitMask

variable {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg}

/-- The commitment-hash points are injective. -/
theorem hch (h : W1SplitMask O M) : Function.Injective O.chPt :=
  h.uniformSplit.chPt_injective

/-- Message points are not commitment-hash points. -/
theorem hdisj (h : W1SplitMask O M) : ∀ a b, O.muPt a ≠ O.chPt b :=
  h.uniformSplit.muPt_ne_chPt

/-- Check points are not commitment-hash points. -/
theorem hdisjg (h : W1SplitMask O M) : ∀ a b, O.gPt a ≠ O.chPt b :=
  fun a b => (h.uniformSplit.chPt_ne_gPt b a).symm

end W1SplitMask

namespace W1OracleFacts

variable {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg}
  {sp : Y ≃+ Y₁ × Y₂}

/-- The commitment-hash points are injective. -/
theorem hch (h : W1OracleFacts O M sp) : Function.Injective O.chPt :=
  h.toW1SplitMask.hch

/-- Message points are not commitment-hash points. -/
theorem hdisj (h : W1OracleFacts O M sp) : ∀ a b, O.muPt a ≠ O.chPt b :=
  h.toW1SplitMask.hdisj

/-- Check points are not commitment-hash points. -/
theorem hdisjg (h : W1OracleFacts O M sp) : ∀ a b, O.gPt a ≠ O.chPt b :=
  h.toW1SplitMask.hdisjg

end W1OracleFacts

end GordieHowe.Ring.MLDSAW1
