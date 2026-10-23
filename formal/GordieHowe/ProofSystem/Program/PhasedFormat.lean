-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Phased
public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.SPBCS.Sampler.ChallengeReader

@[expose] public section

/-!
# The codecs and readers of a phased application phase

The pieces of a setting (`GordieHowe.SPBCS.Setting`, through `GordieHowe/ProofSystem/Program/ForkJoinFormat.lean`)
for the protocol of a phased application phase (`PhaseLayout.spec`: phase `k` draws its challenge,
then sends its message):

- `PhaseLayout.writes`: the message round of phase `k` by a codec of the phase's message
  (`PhaseMsg k`, the masked late values of the phase); the challenge rounds have no codec;
- `PhaseLayout.readers`: the challenge round of phase `k` by a reader of the phase's challenge
  (`Ch k`), with `readers_allLoads`;
- `Codec.FieldBytes.ofSection`: the bytes of a subfield's elements as the bytes of their images in
  the field (the C++ absorbs a late value over a masking subfield as elements of the domain's field,
  `system.h`, `absorb_messages`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec SPBCS GordieHowe.QROM

/-! ### Subfield elements as field elements -/

namespace SPBCS.Codec.FieldBytes

/-- **The bytes of a subfield's elements** through an embedding `e : S → F` with a left inverse
`c`: the bytes of `e s` in `F`; a byte string parses when it is the bytes of an element of `F` in
the image of `e`. -/
def ofSection {S F : Type} [DecidableEq F] {fb : ℕ} (FB : FieldBytes F fb) (e : S → F)
    (c : F → S) (hce : ∀ s, c (e s) = s) : FieldBytes S fb where
  toBytes s := FB.toBytes (e s)
  ofBytes v := (FB.ofBytes v).bind fun x => if e (c x) = x then some (c x) else none
  ofBytes_toBytes s := by simp [FB.ofBytes_toBytes, hce]
  toBytes_ofBytes {v s} h := by
    obtain ⟨x, hx, hs⟩ := Option.bind_eq_some_iff.1 h
    split_ifs at hs with he
    obtain rfl := Option.some_inj.1 hs
    rw [he]
    exact FB.toBytes_ofBytes hx

end SPBCS.Codec.FieldBytes

/-! ### The rounds of a phased application phase -/

namespace RealizedProgram.ProofSystem.PhaseLayout

variable {K : ℕ} (L : PhaseLayout K)

variable {L} in
/-- A prover round of the protocol is a message round (an odd round). -/
theorem not_even_of_messageIdx (i : L.spec.MessageIdx) : ¬ (i.1 : ℕ) % 2 = 0 := fun h => by
  have h' := (spec_dir_eq_V_to_P_iff (L := L) i.1).mpr h
  rw [i.2] at h'
  cases h'

/-- **The codecs of a phased application phase**: the message round of phase `k` by `cw k`, each
of at most `B` bytes (`hB`); the challenge rounds have no codec. -/
def writes {B : ℕ} (cw : ∀ k, WriteCodec (L.PhaseMsg k)) (hB : ∀ k, (cw k).B ≤ B) :
    SpecWrites L.spec B where
  write i := (cw (roundPhase i.1)).mapEquiv (Equiv.cast (spec_type_of_odd i.1
    (not_even_of_messageIdx i)))
  le _ := hB _

/-- **The challenge readers of a phased application phase**: the challenge round of phase `k` by
`cr k`. -/
def readers (cr : ∀ k, CReader (L.Ch k)) : SpecReaders L.spec :=
  fun j => (cr (roundPhase j.1)).cast (spec_challenge_eq j).symm

/-- The readers' loads satisfy `good` when every phase's reader's load does. -/
theorem readers_allLoads {cr : ∀ k, CReader (L.Ch k)} {good : Load → Prop}
    (h : ∀ k, good (cr k).load) : (L.readers cr).AllLoads good := fun j => by
  rw [readers, CReader.cast_load]
  exact h _

end RealizedProgram.ProofSystem.PhaseLayout

end GordieHowe
