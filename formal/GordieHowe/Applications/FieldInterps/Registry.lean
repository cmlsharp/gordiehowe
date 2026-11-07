-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.FieldCodes
public import GordieHoweNative.Language.TableauCheck
public import GordieHoweNative.Language.FieldNums
public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Applications.FieldInterps.Fq20
public import GordieHowe.Applications.FieldInterps.P256
public import GordieHowe.Applications.Falcon512.Frontend.Fields
public import GordieHowe.Applications.MDL.Frontend
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.SPBCS.Format.FieldCodecs
public import GordieHowe.ProofSystem.Program.Transcript.FieldReaders
public import GordieHowe.ProofSystem.Program.Transcript.Format
public import GordieHowe.ProofSystem.Program.ProgramFigures
public import GordieHowe.Applications.MLDSA44.Ring.Tableaux

@[expose] public section

/-!
# The field registry

The Lean objects of each field the compiler uses, keyed by the small descriptors of a program's
field table (`GordieHowe.FieldKey`, `GordieHowe.OpaqueKey`, `GordieHowe.InterpDesc`,
`GordieHoweNative/Language/ProgramData.lean`): the field interpretation, its packing facts, its
code arithmetic, its byte codec and reader, its branch name, and the models and homomorphisms
the proofs use.

Every definition here is a shape function, by cases on a descriptor, whose values are named library
constants. `InterpDesc.interp` is `Interp.twoField`'s or the constant interpretation's spelling, the
spellings of `mldsaInterpOf` and `falconInterpOf`. A provider at every field identifier
(`InterpDesc.provide`) is defined by cases on the descriptor and the identifier, so its type
`(D.interp f).…` matches a program's types syntactically at any `f`: no construction cases on a
program's domain or circuit.

`FieldInterp` bundles its carrier's instances (`TODO(instance-hazard)` on the structure); the
registry passes the `FieldInterp` constants and never rebuilds their instance fields.
-/

namespace GordieHowe

open RealizedProgram

/-! ## The fields -/

/-- **The Lean field of a key.** -/
@[reducible] def FieldKey.interp : FieldKey → FieldInterp
  | .gf128 => RealizedProgram.gf128
  | .gf256 => RealizedProgram.gf256
  | .fq6 => RealizedProgram.fq6
  | .fq9 => RealizedProgram.fq9
  | .fq11 => RealizedProgram.fq11
  | .fq20 => RealizedProgram.fq20
  | .gold2 => RealizedProgram.gold2
  | .gold4 => RealizedProgram.gold4
  | .p256 => RealizedProgram.p256

/-- **The opaque functions of a set.** -/
@[reducible] def OpaqueKey.fn : OpaqueKey → (String → List (ℕ → ℕ) → ℕ → ℕ)
  | .none => fun _ _ _ => 0
  | .targetBits => RealizedProgram.targetBitsFn
  | .falcon => falconOps
  | .mdoc => mdocOps

/-- **The interpretation of a descriptor**: the constant interpretation of `one`, the two-field
interpretation `Interp.twoField` of `two`. -/
@[reducible] def InterpDesc.interp : InterpDesc → Interp
  | .one k o => ⟨fun _ => k.interp, o.fn⟩
  | .two k0 k1 o => Interp.twoField k0.interp k1.interp o.fn

/-- **A provider at every field identifier**: `h k` at each key, read at the identifier's key, by
cases on the descriptor and the identifier. -/
def InterpDesc.provide {P : FieldInterp → Sort _} (h : ∀ k : FieldKey, P k.interp) :
    (D : InterpDesc) → ∀ f, P (D.interp f)
  | .one k _, _ => h k
  | .two k0 _ _, 0 => h k0
  | .two _ k1 _, _ + 1 => h k1

/-! ## Per key -/

/-- **The packing facts of a key's field.** -/
def FieldKey.packing : (k : FieldKey) → k.interp.Packing
  | .gf128 => gf128Packing
  | .gf256 => gf256Packing
  | .fq6 => fq6Packing
  | .fq9 => fq9Packing
  | .fq11 => fq11Packing
  | .fq20 => fq20Packing
  | .gold2 => gold2Packing
  | .gold4 => gold4Packing
  | .p256 => p256Packing

/-- **A key's packing facts have sumcheck nodes** (`FieldInterp.Packing.nodes`). -/
theorem FieldKey.packing_nodes (k : FieldKey) : k.packing.nodes.isSome = true := by
  cases k <;> rfl

/-- **The prime-subfield nodes of a key's field's model.** -/
def FieldKey.primes : FieldKey → List String
  | .gf128 | .gf256 => ["bit"]
  | .p256 => ["F_p256"]
  | _ => ["GF(p^1)"]

/-- **The bit nodes of a key's field's model.** -/
def FieldKey.bits : FieldKey → List String
  | .gf128 | .gf256 => ["bit"]
  | _ => []

/-- **The model of a key's field.** -/
theorem FieldKey.model : (k : FieldKey) → k.interp.Model k.primes k.bits
  | .gf128 => gf128_model
  | .gf256 => gf256_model
  | .fq6 => fq6_model
  | .fq9 => fq9_model
  | .fq11 => fq11_model
  | .fq20 => fq20_model
  | .gold2 => gold2_model
  | .gold4 => gold4_model
  | .p256 => p256_model

/-- **A key's code arithmetic is its field's.** -/
theorem FieldKey.codeHom : (k : FieldKey) → k.interp.CodeHom k.code
  | .gf128 => gf128_codeHom
  | .gf256 => gf256_codeHom
  | .fq6 => fq6_codeHom.withPrime fq6Code_primeOn
  | .fq9 => fq9_codeHom.withPrime fq9Code_primeOn
  | .fq11 => fq11_codeHom.withPrime fq11Code_primeOn
  | .fq20 => fq20_codeHom.withPrime fq20Code_primeOn
  | .gold2 => gold2_codeHom.withPrime gold2Code_primeOn
  | .gold4 => gold4_codeHom.withPrime gold4Code_primeOn
  | .p256 => p256_codeHom.withPrime p256Code_primeOn

/-- **The C++ byte codec and reader of a key's field.** -/
def FieldKey.codec : (k : FieldKey) → FieldCodec k.interp
  | .gf128 => ⟨16, SPBCS.Codec.FieldBytes.gf2_128, SPBCS.CReader.gf2_128⟩
  | .gf256 => ⟨32, SPBCS.Codec.FieldBytes.gf2_256, SPBCS.CReader.gf2_256⟩
  | .fq6 => ⟨18, SPBCS.Codec.FieldBytes.mldsaNative, SPBCS.CReader.mldsaNative⟩
  | .fq9 => ⟨18, SPBCS.Codec.FieldBytes.falconNative, SPBCS.CReader.falconNative⟩
  | .fq11 => ⟨32, SPBCS.Codec.FieldBytes.mldsaNative11, SPBCS.CReader.mldsaNative11⟩
  | .fq20 => ⟨35, SPBCS.Codec.FieldBytes.falconNative20, SPBCS.CReader.falconNative20⟩
  | .gold2 => ⟨16, SPBCS.Codec.FieldBytes.goldilocksExt2, SPBCS.CReader.goldilocksExt2⟩
  | .gold4 => ⟨32, SPBCS.Codec.FieldBytes.goldilocksExt4, SPBCS.CReader.goldilocksExt4⟩
  | .p256 => ⟨32, SPBCS.Codec.FieldBytes.p256, SPBCS.CReader.p256⟩

/-- **The branch name of a key's field**: the C++ field name. -/
def FieldKey.name : FieldKey → String
  | .gf128 => "GF(2^128)"
  | .gf256 => "GF(2^256)"
  | .fq6 => "F_q^6"
  | .fq9 => "F_q^9"
  | .fq11 => "F_q^11"
  | .fq20 => "F_q^20"
  | .gold2 => "Goldilocks^2"
  | .gold4 => "Goldilocks^4"
  | .p256 => "F_p256"

/-- **Every key's branch name has at most `2^10` bytes.** -/
theorem FieldKey.name_le (k : FieldKey) :
    (SPBCS.Configurations.asciiBytes k.name).length ≤ 2 ^ 10 := by
  cases k <;> decide

/-- **The tableau of a library key.** -/
def TableauKey.cert : TableauKey → LigeroCert
  | .gf128K265R2 => gf128K265R2Cert
  | .gf128K282R2 => gf128K282R2Cert
  | .gf128K300R2 => gf128K300R2Cert
  | .gf256K339R2 => gf256K339R2Cert
  | .fq20K271 => fq20K271Cert
  | .falconNativeROMA => falconNativeROMACert
  | .falconRingNativeROMA => falconRingNativeROMACert
  | .gold2K512R2 => gold2K512R2Cert
  | .gold4K512 => gold4K512Cert
  | .gold4K512R2 => gold4K512R2Cert
  | .gold4K1024 => gold4K1024Cert

/-- **A library tableau has its key's numbers.** -/
theorem TableauKey.cert_nums (k : TableauKey) : k.cert.nums = k.nums := by
  cases k <;> rfl

/-! ## Per field identifier -/

namespace InterpDesc

variable (D : InterpDesc)

/-- **The packing facts of every field.** -/
def packing : ∀ f, (D.interp f).Packing := D.provide FieldKey.packing

/-- **The fields' models**, at the keys' node lists. -/
theorem models : D.interp.Models (fun f => (D.key f).primes) (fun f => (D.key f).bits) := by
  intro f
  cases D with
  | one k o => exact k.model
  | two k0 k1 o => cases f with
    | zero => exact k0.model
    | succ n => exact k1.model

/-- **Every field's code arithmetic is the field's.** -/
theorem codeHom (f : ℕ) : (D.interp f).CodeHom (D.key f).code := by
  cases D with
  | one k o => exact k.codeHom
  | two k0 k1 o => cases f with
    | zero => exact k0.codeHom
    | succ n => exact k1.codeHom

/-- **Every field's packing facts have sumcheck nodes.** -/
theorem packing_nodes (f : ℕ) : (D.packing f).nodes.isSome = true := by
  cases D with
  | one k o => exact k.packing_nodes
  | two k0 k1 o => cases f with
    | zero => exact k0.packing_nodes
    | succ n => exact k1.packing_nodes

/-- **The fields' sizes are their specifications'.** -/
theorem card (f : ℕ) : Fintype.card (D.interp f).K = D.interp.specCard f :=
  (D.models f).card

/-- **The byte codec and reader of every field.** -/
def codec : ∀ f, FieldCodec (D.interp f) := D.provide FieldKey.codec

/-- **The bytes of the fields' elements.** -/
def bytes : FieldBytesOf D.interp where
  fb f := (D.codec f).fb
  bytes f := (D.codec f).FB

/-- **The C++ readers of the fields' elements.** -/
def reader (f : ℕ) : SPBCS.CReader (D.interp f).K := (D.codec f).rd

/-! ## The registry's numbers -/

/-- **The bytes of an element are the numeral.** -/
theorem fb_eq (f : ℕ) : (D.codec f).fb = D.fbN f := by
  have key : ∀ k : FieldKey, k.codec.fb = k.fbN := by
    intro k; cases k <;> rfl
  cases D with
  | one k o => exact key k
  | two k0 k1 o => cases f with
    | zero => exact key k0
    | succ n => exact key k1

/-- **The challenge reader's load is the numeral.** -/
theorem load_eq (f : ℕ) :
    (D.reader f).load.draws = (D.loadN f).1 ∧ (D.reader f).load.bytes = (D.loadN f).2 := by
  have key : ∀ k : FieldKey,
      k.codec.rd.load.draws = k.loadN.1 ∧ k.codec.rd.load.bytes = k.loadN.2 := by
    intro k
    cases k
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · change SPBCS.CReader.mldsaNative.load.draws = 6 ∧ SPBCS.CReader.mldsaNative.load.bytes = 3
      decide +kernel
    · change SPBCS.CReader.falconNative.load.draws = 9 ∧ SPBCS.CReader.falconNative.load.bytes = 2
      decide +kernel
    · change SPBCS.CReader.mldsaNative11.load.draws = 11 ∧
        SPBCS.CReader.mldsaNative11.load.bytes = 3
      decide +kernel
    · change SPBCS.CReader.falconNative20.load.draws = 20 ∧
        SPBCS.CReader.falconNative20.load.bytes = 2
      decide +kernel
    · change SPBCS.CReader.goldilocksExt2.load.draws = 2 ∧
        SPBCS.CReader.goldilocksExt2.load.bytes = 8
      decide +kernel
    · change SPBCS.CReader.goldilocksExt4.load.draws = 4 ∧
        SPBCS.CReader.goldilocksExt4.load.bytes = 8
      decide +kernel
    · change SPBCS.CReader.p256.load.draws = 1 ∧ SPBCS.CReader.p256.load.bytes = 32
      rw [SPBCS.CReader.p256_load]
      exact ⟨rfl, rfl⟩
  cases D with
  | one k o => exact key k
  | two k0 k1 o => cases f with
    | zero => exact key k0
    | succ n => exact key k1

/-- **The challenge reader grants no stream.** -/
theorem grant_eq (f : ℕ) : (D.reader f).grant = D.grantN f := by
  have key : ∀ k : FieldKey, k.codec.rd.grant = k.grantN := by
    intro k
    cases k
    · change SPBCS.CReader.gf2_128.grant = 0; decide +kernel
    · change SPBCS.CReader.gf2_256.grant = 0; decide +kernel
    · change SPBCS.CReader.mldsaNative.grant = 0; decide +kernel
    · change SPBCS.CReader.falconNative.grant = 0; decide +kernel
    · change SPBCS.CReader.mldsaNative11.grant = 0; decide +kernel
    · change SPBCS.CReader.falconNative20.grant = 0; decide +kernel
    · change SPBCS.CReader.goldilocksExt2.grant = 0; decide +kernel
    · change SPBCS.CReader.goldilocksExt4.grant = 0; decide +kernel
    · change SPBCS.CReader.p256.grant = 0; decide +kernel
  cases D with
  | one k o => exact key k
  | two k0 k1 o => cases f with
    | zero => exact key k0
    | succ n => exact key k1

/-- The interpretation selects the full numeric specification at its descriptor's field key. -/
theorem spec_eq (f : ℕ) : (D.interp f).spec = (D.key f).specN := by
  have key : ∀ k : FieldKey, k.interp.spec = k.specN := by intro k; cases k <;> rfl
  cases D with
  | one k o => exact key k
  | two k0 k1 o => cases f with
    | zero => exact key k0
    | succ n => exact key k1

/-- **The size of a field is the numeral.** -/
theorem specCard_eq (f : ℕ) : D.interp.specCard f = D.cardN f := by
  have key : ∀ k : FieldKey, k.interp.spec = k.specN := by intro k; cases k <;> rfl
  cases D with
  | one k o => simp only [Interp.specCard, InterpDesc.cardN, FieldKey.cardN, ← key]
  | two k0 k1 o => cases f with
    | zero => simp only [Interp.specCard, InterpDesc.cardN, FieldKey.cardN, ← key]
    | succ n => simp only [Interp.specCard, InterpDesc.cardN, FieldKey.cardN, ← key]

end InterpDesc

end GordieHowe
