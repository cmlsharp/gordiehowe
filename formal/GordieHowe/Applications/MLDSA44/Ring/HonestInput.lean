-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Scheme
public import GordieHowe.Applications.MLDSA44.PoP.Configuration
public import GordieHowe.Applications.MLDSA44.Spec.ExpandA

@[expose] public section

/-!
# The honest data of an ML-DSA-44 ring input

An honest input of an ML-DSA-44 ring (`GordieHowe.MLDSA44.Ring.RingIn`: a ring statement and a
witness of the ring relation) carries a signature `(c̃, z, h)` under the signer's key `pk` that
verifies on the statement's message representative `M′` (`MLDSA.Concrete.verify`, FIPS 204
Algorithm 8 with the bounded samplers). This file reads the data the honest prover of the ring
programs computes from it (`lib/gordiehowe/examples/rings/mldsa_ring_testing.h`, `ring_witness`):

* the signer's key (`RingIn.key`), its signature's parts (`RingIn.ctilde`, `RingIn.z`,
  `RingIn.h`), the positions the fixed-stream selection takes on `c̃`'s stream
  (`RingIn.positions`), the challenge they select (`RingIn.c`, `GordieHowe.MLDSA44.PoP.challenge`)
  and the message representative's `μ = H(tr ‖ M′)` (`RingIn.mu`, FIPS 204 Algorithm 8 line 7, at
  `tr = H(pk)`);
* the input's verification as `MLDSA44.Verifies` (`RingIn.verifies`: the ring's keys have an
  `ExpandA` within the byte budget, `ringAdm`) and the checks of Algorithm 8 it gives
  (`RingIn.checks`): the selection succeeds at the positions, `‖z‖∞ < γ₁ − β`,
  `c̃ = H(μ ‖ w1Encode(w1))` at `w1 = UseHint(h, w′)` with the selected challenge, and the hint
  weight is at most `ω`.
-/

namespace GordieHowe.MLDSA44.Ring

open _root_.MLDSA.Concrete (concretePrimitives Hint)

variable {msgLen : ℕ} (y : RingIn msgLen)

namespace RingIn

/-- **The signer's position is a position of the ring.** -/
theorem idx_lt_length : y.w.idx < y.x.ring.1.length := y.mem.2.idx_lt

/-- **The signer's key**: the ring's key at the signer's position. -/
def key : PublicKey := y.x.ring.1[y.w.idx]'y.idx_lt_length

/-- **The signature's `c̃`.** -/
abbrev ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44 := y.w.sig.cTilde

/-- **The signature's `z`.** -/
abbrev z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l := y.w.sig.z

/-- **The signature's hint `h`.** -/
abbrev h : Vector Hint _root_.MLDSA.mldsa44.k := y.w.sig.h

/-- **The positions of the fixed-stream selection on `c̃`'s stream** (`MLDSA44.acceptedCandidates`
of `GordieHowe.MLDSA44.PoP.stream c̃`; `0` where the selection fails, which a verifying signature
excludes, `checks`).

Running time: one SHAKE256 call of `272` bytes and the scan of its `264` candidates. This running
time is argued here, not proved in Lean. -/
-- spec-side
def positions : Fin mldsa44.τ → ℕ :=
  (MLDSA44.acceptedCandidates mldsa44 (MLDSA44.PoP.stream y.ctilde)).getD 0

/-- **The challenge** the positions select (`GordieHowe.MLDSA44.PoP.challenge`: the memory shuffle of
the positions and the stream's sign bits). -/
-- spec-side
def c : Fin mldsa44.N → ℤ := MLDSA44.PoP.challenge y.ctilde y.positions

/-- **The message representative's `μ`**: `H(tr ‖ M′)` at `tr = H(pk)` (FIPS 204 Algorithm 8,
lines 6 and 7). -/
-- spec-side
def mu : _root_.MLDSA.Bytes 64 :=
  _root_.MLDSA.Concrete.hashMessage (cprims.hashPublicKey y.key.rho y.key.t1) y.x.msg.toList

/-- **The signature verifies** under the signer's key on the message representative
(`MLDSA.Concrete.verify`). -/
theorem verify : _root_.MLDSA.Concrete.verify _root_.MLDSA.mldsa44 y.key y.x.msg.toList y.w.sig = true :=
  y.mem.2.verify_eq

/-- **The signer's `ExpandA(ρ)` finishes within the byte budget** (`ringAdm`). -/
theorem expandAWithin : MLDSA44.ExpandAWithin _root_.MLDSA.mldsa44 y.key.rho :=
  y.mem.1.2 _ (List.getElem_mem _)

/-- **The signature verifies as `MLDSA44.Verifies`**: the bounded `ExpandA` is `expandAFull`
within the byte budget (`expandA_eq_expandABounded`, `expandABounded_eq_expandAFull`). -/
theorem verifies : MLDSA44.Verifies y.key y.x.msg.toList y.w.sig := by
  have hv := y.verify
  unfold _root_.MLDSA.Concrete.verify at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨-, hs⟩, hf⟩ := hv
  refine ⟨y.expandAWithin, hs, ?_⟩
  rw [MLDSA44.fipsVerify_eq_verifyChecks] at hf
  have he : (concretePrimitives _root_.MLDSA.mldsa44).expandA y.key.rho =
      MLDSA44.expandAFull _root_.MLDSA.mldsa44 y.key.rho :=
    (MLDSA44.expandA_eq_expandABounded y.expandAWithin).trans
      (MLDSA44.expandABounded_eq_expandAFull y.expandAWithin)
  rwa [he] at hf

/-- **The fixed-stream selection succeeds at the positions**: `SampleInBall(c̃)` finishes within
the stream's `264` candidates (`acceptedCandidates_isSome_of_sampleInBallPoly?`). -/
theorem positions_eq :
    MLDSA44.acceptedCandidates mldsa44 (MLDSA44.PoP.stream y.ctilde) = some y.positions := by
  have hsel : (MLDSA44.acceptedCandidates mldsa44 (MLDSA44.PoP.stream y.ctilde)).isSome := by
    rw [MLDSA44.PoP.stream_eq]
    exact MLDSA44.acceptedCandidates_isSome_of_sampleInBallPoly? y.verifies.sampleInBall
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsel
  rw [positions, hp]
  rfl

/-- **The checks Algorithm 8 makes on the honest input**: the norm bound, the commitment
`c̃ = H(μ ‖ w1Encode(w1))` and the hint weight, with `SampleInBall(c̃)` replaced by the selected
challenge (`GordieHowe.MLDSA44.PoP.sampleInBall_eq`). -/
theorem checks :
    _root_.MLDSA.polyVecNorm y.z < _root_.MLDSA.mldsa44.gamma1 - _root_.MLDSA.mldsa44.beta ∧
      _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44 y.mu
          (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
            (MLDSA44.PoP.Compose.honestW1 y.key y.c y.z y.h)) = y.ctilde ∧
      _root_.MLDSA.Concrete.hintWeightVec y.h ≤ _root_.MLDSA.mldsa44.omega := by
  have hv := y.verifies.checks
  unfold MLDSA44.verifyChecks at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnorm, hcommit⟩, hweight⟩ := hv
  rw [MLDSA44.PoP.sampleInBall_eq y.positions_eq] at hcommit
  exact ⟨hnorm, (congrArg (fun w => _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44 _
    (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 w))
      (MLDSA44.PoP.Compose.useHintVec_honestWApprox y.key y.c y.z y.h)).symm.trans hcommit,
    hweight⟩

end RingIn

end GordieHowe.MLDSA44.Ring
