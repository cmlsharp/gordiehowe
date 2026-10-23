-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.System.MAC
public import GordieHowe.Applications.MLDSA44.PoP.Native.Algebra
public import GordieHowe.Applications.MLDSA44.System.Application

@[expose] public section

/-!
# ML-DSA native: the application

The application of ML-DSA native as the ML-DSA-44 proof-of-possession relation
(`GordieHowe.MLDSA44.PoP.rel`: the signature verifies under the decoded key at the empty context,
`GordieHowe.MLDSA44.VerifiesBytes`, FIPS 204 Algorithm 3 with `ExpandA` within `1008` SHAKE128 bytes per `RejNTTPoly`
call).

The extracted witness is the message bytes read from the message bits and the signature encoded
(`sigEncode`, FIPS 204 Algorithm 26) from `c̃'` (the bytes of H's `h2c.c_tilde.out`), the extracted
`z` and the hint read from its Boolean cells. It verifies, at a key whose `ExpandA` finishes
within the byte budget (`GordieHowe.MLDSA44.ExpandAWithin`), by these facts: the selection and SampleInBall's source make
H's decoded challenge the vendored `SampleInBall(c̃')` (`GordieHowe.MLDSA44.fixedStreamChallenge_agree`); the
crossing's agreement makes it A's challenge and H's `w1` A's `hint.w1`; the hash constraints make
`c̃'` the commitment hash of `μ` and `w1Encode(w1)` (`cTilde_eq_hashCommitment`, this file's
theorem); the algebra constraints give `w' = computeWApprox(Â, c, z, t1)`, `w1 = UseHint(h, w')`,
the norm and the hint weight; then `GordieHowe.MLDSA44.verifiesBytes_of_parts`.

**The key check.** The statements are the keys whose `ExpandA` finishes within `1008` SHAKE128
bytes per `RejNTTPoly` call (`GordieHowe.MLDSA44.ExpandAWithin`, the bound FIPS 204 Appendix C
permits). The verifier prepares `Â = ExpandA(ρ)` within that budget
(`GordieHowe.MLDSA44.expandABounded`).

The parts ML-DSA emulated also uses are in `GordieHowe/Applications/MLDSA44/System/Application.lean`.
-/

namespace GordieHowe.MLDSA44.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits Params
open _root_.MLDSA.Concrete (sigEncode useHintCoeff)
open scoped NNReal

variable {P : Profile} {KH F S : Type} [Field KH] [Fintype KH] [DecidableEq KH] [Field F]
  [Fintype F] [DecidableEq F] [Field S] [Fintype S] (D : FieldData P KH F S) {msgLen : ℕ}

variable [CharP KH 2] [CharP F _root_.MLDSA.modulus]

omit [Fintype KH] [Fintype F] [Fintype S] in
/-- **The extracted `c̃` is the commitment hash** `H(μ ‖ w1Encode(w1), 32)` with
`μ = H(tr ‖ M', 64)`, `M' = frame([], msg)`, at A's extracted `w1` (FIPS 204 Algorithm 8, line 12). -/
theorem cTilde_eq_hashCommitment {x : Statement} {a : Source KH F msgLen}
    (h : BitsAgree (xhOf P a) (xaOf P a)) (hc : AppConstraints D x a) :
    _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44
        (_root_.MLDSA.Concrete.hashMessage
          ((_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44).hashPublicKey x.pk.rho
            x.pk.t1)
          (MLDSA44.frame [] (List.ofFn (messageOf a.msg))))
        (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 (MLDSA44.PoP.Native.decodeW1 a.w1A)) =
      cTildeOf D a := by
  have hw1 : (List.ofFn fun i : Fin 768 => natOfBits (Falcon512.HashCircuit.byteWires a.w1H i)) =
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
        (MLDSA44.PoP.Native.decodeW1 a.w1A)).map UInt8.toNat := by
    have hlen := MLDSA44.w1Encode_length_mldsa44 (MLDSA44.PoP.Native.decodeW1 a.w1A)
    apply List.ext_getElem (by rw [List.length_ofFn, List.length_map, hlen])
    intro j h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [HashCircuit.natOfBits_byteWires_w1Encode (w1H_eq h hc.hash.w1Bool hc.algebra.w1Bool),
      List.getD_eq_getElem]
  have htr : (List.ofFn fun i => (MLDSA44.PoP.Compose.trOf x.pk i).toNat) =
      ((_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44).hashPublicKey x.pk.rho
        x.pk.t1).toList.map UInt8.toNat := by
    apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList,
      MLDSA44.PoP.Compose.trOf, Vector.get_eq_getElem]
  have hmu : (fun j => natOfBits (muOut D.packing a.states j)) =
      HashCircuit.mu ((((_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44).hashPublicKey
        x.pk.rho x.pk.t1).toList.map UInt8.toNat)) [] (List.ofFn (messageOf a.msg)) := by
    funext j
    rw [hc.hash.mu_eq (Falcon512.HashCircuit.wiresOfByteVec_allBool _) j, inputBytes_muInput, htr]
    rfl
  apply Vector.ext
  intro i hi
  apply UInt8.toNat_inj.mp
  have hl := MLDSA44.hashCommitment_get
    (_root_.MLDSA.Concrete.hashMessage
      ((_root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44).hashPublicKey x.pk.rho
        x.pk.t1) (MLDSA44.frame [] (List.ofFn (messageOf a.msg))))
    (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 (MLDSA44.PoP.Native.decodeW1 a.w1A)) ⟨i, hi⟩
  change UInt8.toNat (Vector.get _ ⟨i, hi⟩) = UInt8.toNat (Vector.get _ ⟨i, hi⟩)
  refine hl.trans ?_
  rw [← HashCircuit.ofFn_mu, ← hw1, ← hmu]
  have hct := hc.hash.cTilde_eq ⟨i, hi⟩
  rw [HashCircuit.inputBytes_commitInput] at hct
  simp only [cTildeOf, Vector.get_ofFn]
  rw [toNat_toUInt8_natOfBits]
  exact hct.symm

end GordieHowe.MLDSA44.Native
