-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# The witness of a proof of possession

A proof of possession proves knowledge of a message and a signature on it under the statement's
public key. Both schemes share the witness structure `GordieHowe.Configuration.Witness`: the message bytes, of a length
the circuit fixes (so it lives in the type), and the signature, of the scheme's signature type
(the Falcon-512 signature `_root_.Falcon.Signature`, the ML-DSA-44 signature bytes `ByteArray`).
-/

namespace GordieHowe.SPBCS.Configurations

/-- **The witness of a proof of possession**: the `msgLen` bytes of the message and the signature
on it, of the scheme's signature type `Sig`. -/
structure _root_.GordieHowe.Configuration.Witness (msgLen : ℕ) (Sig : Type) where
  /-- The message bytes. -/
  message : Fin msgLen → UInt8
  /-- The signature. -/
  signature : Sig

/-- The zero message with the default signature, returned by an extractor when decoding fails. -/
instance {msgLen : ℕ} {Sig : Type} [Inhabited Sig] : Inhabited (Configuration.Witness msgLen Sig) :=
  ⟨⟨fun _ => 0, default⟩⟩

end GordieHowe.SPBCS.Configurations
