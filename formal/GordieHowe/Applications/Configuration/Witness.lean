-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs

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

/-- **A witness of a message of at most `nm` bytes** (the paper's `n_m`): its length `L ≤ nm` and a
witness at that length. -/
structure _root_.GordieHowe.Configuration.VarWitness (nm : ℕ) (Sig : Type) where
  /-- The length of the witness's message. -/
  len : Fin (nm + 1)
  /-- The witness at the length of its message. -/
  wit : Configuration.Witness len Sig

/-- **A variable-length witness is a length and a witness at it** (`Configuration.VarWitness` as the
dependent pair it replaces). -/
def _root_.GordieHowe.Configuration.VarWitness.equivSigma (nm : ℕ) (Sig : Type) :
    Configuration.VarWitness nm Sig ≃ Σ L : Fin (nm + 1), Configuration.Witness L Sig where
  toFun w := ⟨w.len, w.wit⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The relation for messages of at most `nm` bytes** (paper `applications`, the relation at a
public maximal message length `n_m`), from the relation `rel L` at each length `L`: the witness's
message, of its length `L ≤ nm`, and its signature are in `rel L`. -/
def _root_.GordieHowe.Configuration.relUpTo {Stmt Sig : Type}
    (rel : (L : ℕ) → Set (Stmt × Configuration.Witness L Sig)) (nm : ℕ) :
    Set (Stmt × Configuration.VarWitness nm Sig) :=
  Function.uncurry fun s w => (s, w.wit) ∈ rel w.len

end GordieHowe.SPBCS.Configurations
