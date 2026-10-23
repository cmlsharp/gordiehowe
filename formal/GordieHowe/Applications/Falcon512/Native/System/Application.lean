-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.System.Algebra
public import GordieHowe.Foundations.Probability.RangeGroups
public import GordieHowe.Applications.Falcon512.Native.System.Source
public import GordieHowe.Language.Realizations.MACEquality
public import GordieHowe.Language.Realizations.ModEquality
public import GordieHowe.Foundations.Algebra.ParityReduction
public import GordieHowe.Foundations.Algebra.ConvMatrix
public import GordieHowe.Foundations.Algebra.ReconstructSum
public import GordieHowe.Applications.Falcon512.System.Source
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Applications.Falcon512.Gadgets.SelectFirstN
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Applications.Falcon512.PoP.Relation

@[expose] public section

/-!
# Falcon native: the application extraction

The extraction of Falcon native (`lib/gordiehowe/examples/falcon/falcon_native.h`) from its source
assignment into the Falcon-512 proof-of-possession relation (`GordieHowe.Falcon512.PoP.rel`).

* **The extraction** (`extract`): the message bytes read from the message bits, and the signature
  encoded from the nonce bytes and the centered `s2`, as in Falcon emulated.
* **Soundness** (`extract_mem_rel_of_spec`): a stream whose samples are Falcon's candidate stream,
  the selected samples its first accepted samples, `select.raw` and `c_A` denoting the same samples,
  and Falcon's algebraic verifier and the encoding bounds on the extracted values
  (`GordieHowe.Falcon512.Emulated.AlgebraSpec`); then the relation holds on the extracted witness. The
  frontend at the realized program supplies these from the realized program
  (`GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Basic.lean`).
-/

namespace GordieHowe.Falcon512.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits
open GordieHowe.Falcon512.Emulated (PublicKey nonceOf messageOf bytesOf nonceOf_toNat messageOf_toNat)

variable {KH F : Type} [Field KH] [DecidableEq KH] [Field F] [DecidableEq F]
  {msgLen : ℕ}

/-- **The extracted witness**: the message bytes, and the signature encoded from the nonce bytes and
the centered `s2` (the default signature if the encoding fails).

Running time: `msgLen + 40` bytes read from their bits, the `512`
coefficients of `s2` lifted to `[0, q]` (`Range.natBelow`, a search below `q + 1`) and centered,
and `Falcon512.encodeSignature` (the vendored `compress`, linear in `512`).
This running time is argued here, not proved in Lean. -/
-- spec-side
def extract (a : Source KH F msgLen) : Falcon512.PoP.Witness msgLen :=
  ⟨messageOf a.message,
    (Falcon512.encodeSignature falcon512 (nonceOf a.nonce) (Emulated.decodeS2Int a.s2)).getD
      default⟩

variable [CharP KH 2] [CharP F Emulated.Params.q]

omit [CharP KH 2] [CharP F Emulated.Params.q] in
/-- **Soundness of the application on a stream, from the algebra's conclusion**: if the samples of
a stream `stream` are Falcon's candidate stream of the nonce and message bytes, the selected samples
`select.raw` are the stream's first accepted samples, `select.raw` and `c_A` denote the same samples,
and Falcon's algebraic verifier and the encoding bounds hold on the samples `c_A` reads and the
extracted `s2` (`Emulated.AlgebraSpec`), then the proof-of-possession relation holds on the
extracted witness. Falcon native's algebra constraints conclude `AlgebraSpec` by `algebra_sound`,
the realized programs' predicates by their frontends. -/
theorem extract_mem_rel_of_spec {pk : PublicKey} {a : Source KH F msgLen}
    {stream : Fin falcon512.S → BitWires KH falconSampleBits}
    (hstream : ∀ i, natOfBits (stream i) =
      Falcon512.streamCandidates falcon512 shake256 (bytesOf a.nonce) (bytesOf a.message) i)
    (hfirst : firstAccepted (fun v => decide (v < Emulated.Params.cutoff))
      (fun i => natOfBits (stream i)) Emulated.Params.n = some fun j => natOfBits (a.raw j))
    (hraw : ∀ j, natOfBits (a.raw j) = Emulated.cNat a.cA j)
    (hspec : Emulated.AlgebraSpec pk.h a.cA a.s2) :
    (pk, extract a) ∈ Falcon512.PoP.rel msgLen := by
  have hcand : Falcon512.acceptedCandidates falcon512 shake256
      ((nonceOf a.nonce).toList.map UInt8.toNat)
      ((List.ofFn (messageOf a.message)).map UInt8.toNat) = some (Emulated.cNat a.cA) := by
    rw [nonceOf_toNat, messageOf_toNat]
    have hs : (fun i => natOfBits (stream i)) =
        Falcon512.streamCandidates falcon512 shake256 (bytesOf a.nonce) (bytesOf a.message) :=
      funext hstream
    have ho : (fun j => natOfBits (a.raw j)) = Emulated.cNat a.cA := funext hraw
    rw [hs, ho] at hfirst
    exact hfirst
  have hdec := Falcon512.verifyDecoded_of_acceptedCandidates (pk := pk)
    (msg := List.ofFn (messageOf a.message)) (salt := nonceOf a.nonce)
    (s₂ := (Emulated.decodeS2Int a.s2).toRq) hcand
    (by rw [Emulated.decodeS2Int_toRq]; exact hspec.algebra)
  obtain ⟨sig, henc, hver⟩ := Falcon512.extract_accepted_signature hspec.encoding hdec
  show Falcon512.verify pk (List.ofFn (messageOf a.message))
    ((Falcon512.encodeSignature falcon512 (nonceOf a.nonce)
      (Emulated.decodeS2Int a.s2)).getD default)
  rw [henc]
  exact hver

end GordieHowe.Falcon512.Native
