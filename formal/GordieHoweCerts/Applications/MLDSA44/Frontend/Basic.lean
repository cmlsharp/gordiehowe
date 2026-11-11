-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Frontend.Reads
public import GordieHowe.Applications.Keccak.Frontend.Sponge
public import GordieHowe.Applications.MLDSA44.Interp
public import GordieHowe.Applications.MLDSA44.HPreds
public import GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.ShapeFacts
public import GordieHowe.Applications.MLDSA44.Frontend.HField
public import GordieHowe.Applications.MLDSA44.Frontend.QField
public import GordieHowe.Applications.MLDSA44.Fields.MLDSANative6Coords

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, the relation and the extractor

The frontend of the theorem at the realized program for the native ML-DSA-44 proof of possession at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program`, export `c825eb05`), the parts that do not
read the Keccak trace's shape, the sampler's predicates or domain `A`'s layout:

* **The statement** (`KeyOf`): the program's statement values are the verifier's preprocessing of
  the key, `key.a_hat` (value `55`, `4 × 4 × 256` coordinates of `F_q^6`) the matrix
  `Â = ExpandA(ρ)` in NTT form, `key.t1` (value `56`, `4 × 256`) the coefficients of `t1`, and `tr`
  (value `66`, `512` bits of `GF(2^128)`) the bits of `tr = H(pk)`. The statement holds no `ρ`, so
  a key cannot be decoded from it: `KeyOf pk x` says that `x` holds `pk`'s preprocessing (the
  `F_q^6` entries read at their constant coordinate, `FieldInterp.toNat`, as the program's integer
  readings do).
* **The relation** (`rel`): for every key whose preprocessing the statement holds and whose
  `ExpandA` finishes within `1008` SHAKE128 bytes per `RejNTTPoly` call
  (`GordieHowe.MLDSA44.ExpandAWithin`, the configurations' statement check), the
  ML-DSA-44 proof-of-possession relation for messages of at most `32` bytes holds for the witness
  (`MLDSA44.PoP.relUpTo 32`). The maximal length `32` is the program's: its message buffer is one
  `136`-byte SHAKE256 block holding the `66`-byte head `tr ‖ 0 ‖ 0` and at most `32` message
  bytes. The verifier reads a key only through `Â`, `t1`
  and `tr`, so every such key verifies alike.
* **The extractor** (`proj`, `extractor`): the message bytes at the length the in-message flags
  encode (`lenOf`, `messageBytes`) and `sigEncode(c̃', z, h)` with `c̃'` the bytes of H's
  `h2c.c_tilde.out`, `z` and `h` read from domain `A` (`sigOf`).
* **Domain `H`'s two parts**: the core (`HSatCore`, `MldsaHBaseCore`: predicates `48 … 270`, `c̃'`,
  the SampleInBall stream and SampleInBall) and `μ`'s call (`HSatMu`, `MldsaHBaseMu`: predicates
  `18 … 47`, the message, its flags and `tr`); `HSat` is both (`HSat.core`, `HSat.mu`,
  `HSat.ofParts`). The hash view splits alike (`HashViewCore`, `HashViewMu`), and the core's facts
  (`sibStream_eq_core`, `cTildeOf_eq_hashCommitment`, `SampleView.sound`) read `μ` only as the bits
  of value `120` (`muBits`).
-/

namespace GordieHowe.MLDSA44

open Generated.MLDSA44.Native.ROMParams.Program (program)
open GordieHowe.Bits IOP

/-! ## Domain `H`, for any field `0` -/

section H

/-- **The program facts of domain `H` the frontend's base reads**: the predicates `18 … 270` and the
values `hTyped` are source predicates and node-typed source values, and `tr` (value `66`) is an
opaque statement value of no argument. Each program instantiates it by `decide`. -/
class MldsaHBase (program : RealizedProgram) : Prop where
  /-- The predicates `18 … 270` are source predicates. -/
  hPreds : ∀ k, hPredLo ≤ k → k ≤ hPredHi → k < program.predicates.length ∧
    program.inSource (program.predicate k) = true
  /-- The values `hTyped` are node-typed source values. -/
  hTyped : ∀ v ∈ [67, 68, 556, 560, 561, 562, 563, 564, 565], v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node
  /-- `tr` is an opaque statement value of no argument. -/
  trKind : (program.value 66).kind = .pub (.opaque "tr" [])

/-- **The program facts of domain `H`'s core**: the predicates `48 … 270` (`c̃'`'s absorbs, the
SampleInBall stream, the selection and the memory check) are source predicates and the values
`hTypedCore` (the selected bytes and the memory check's cells) node-typed source values. A program
holding domain `H` without `μ`'s call instantiates it. -/
class MldsaHBaseCore (program : RealizedProgram) : Prop where
  /-- The predicates `48 … 270` are source predicates. -/
  predsCore : ∀ k, corePredLo ≤ k → k ≤ hPredHi → k < program.predicates.length ∧
    program.inSource (program.predicate k) = true
  /-- The values `hTypedCore` are node-typed source values. -/
  typedCore : ∀ v ∈ [556, 560, 561, 562, 563, 564, 565], v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node

/-- **The program facts of `μ`'s call in domain `H`**: the predicates `18 … 47` (`μ`'s absorb and
padding) are source predicates, the values `hTypedMu` (the message and its in-message flags)
node-typed source values, and `tr` (value `66`) an opaque statement value of no argument. -/
class MldsaHBaseMu (program : RealizedProgram) : Prop where
  /-- The predicates `18 … 47` are source predicates. -/
  predsMu : ∀ k, 18 ≤ k → k ≤ 47 → k < program.predicates.length ∧
    program.inSource (program.predicate k) = true
  /-- The values `hTypedMu` are node-typed source values. -/
  typedMu : ∀ v ∈ [67, 68], v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node
  /-- `tr` is an opaque statement value of no argument. -/
  trKind : (program.value 66).kind = .pub (.opaque "tr" [])

variable {program : RealizedProgram} {F0 FH : RealizedProgram.FieldInterp}

/-- A program with domain `H`'s base facts has those of its core. -/
instance [h : MldsaHBase program] : MldsaHBaseCore program where
  predsCore k h1 h2 := h.hPreds k (by unfold hPredLo; unfold corePredLo at h1; omega) h2
  typedCore v hv := h.hTyped v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    omega)

/-- A program with domain `H`'s base facts has those of `μ`'s call. -/
instance [h : MldsaHBase program] : MldsaHBaseMu program where
  predsMu k h1 h2 := h.hPreds k h1 (by unfold hPredHi; omega)
  typedMu v hv := h.hTyped v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    omega)
  trKind := h.trKind

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-- **The statement's `tr` bits** (value `66`, `512` bits of domain `H`): bit `8 k + b` is bit `b`
of byte `k` of `tr`. -/
def trBits (x : program.Valuation interp) : BitWires (interp 1).K (8 * 64) :=
  fun k => program.evalE x 1 (.leaf 66) k

/-- **The message's length** read off the in-message flags (value `68`, `136` bits of domain `H`,
`f_i = [i < 66 + L]` over `μ`'s buffer `tr ‖ 0x00 ‖ 0x00 ‖ M`): the number of flags set, less the
buffer's `66`-byte head, at most the relation's maximum `32`.

Running time: `136` readings of a committed value and a count.
This running time is argued here, not proved in Lean. -/
def lenOf (rd : program.Valuation interp) : ℕ :=
  min 32 ((Finset.univ.filter fun i : Fin 136 => program.evalE rd 1 (.leaf 68) i = 1).card - 66)

theorem lenOf_le (rd : program.Valuation interp) : lenOf rd ≤ 32 := min_le_left _ _

/-- **The message bits** at a length `L`: the first `8 L` bits of the message's part of `μ`'s buffer
(value `67`, `70 × 8` bits of domain `H`: the message, its padding at the private length, zeros). -/
def messageBits (rd : program.Valuation interp) (L : ℕ) :
    BitWires (interp 1).K (8 * L) :=
  fun k => program.evalE rd 1 (.leaf 67) k

/-- **The message bytes**: the message bits at the length the flags encode (`lenOf`), as bytes. -/
def messageBytes (rd : program.Valuation interp) : Fin (lenOf rd) → UInt8 :=
  fun i => (natOfBits (Falcon512.HashCircuit.byteWires (messageBits rd (lenOf rd)) i)).toUInt8

/-- **The bits of `c̃'`** (value `457`, `h2c.c_tilde.out`, `256` bits of domain `H`). -/
def cTildeBits (rd : program.Valuation interp) : BitWires (interp 1).K (8 * 32) :=
  fun k => program.evalE rd 1 (.leaf 457) k

/-- **The extracted `c̃`**: the bytes of `c̃'`. -/
def cTildeOf (rd : program.Valuation interp) :
    _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44 :=
  Vector.ofFn fun i => (natOfBits (Falcon512.HashCircuit.byteWires (cTildeBits rd) i)).toUInt8

/-- **The bits of `μ`** (value `120`, `h2c.mu.out`, `512` bits of domain `H`). -/
def muBits (rd : program.Valuation interp) : BitWires (interp 1).K (8 * 64) :=
  fun k => program.evalE rd 1 (.leaf 120) k

/-- **H's `w1` bits** (value `70`, `4 × 256 × 6` bits of domain `H`, `w1Encode`'s bit order: bit
`b` of coefficient `k` of row `i` at `(256 i + k) · 6 + b`). -/
def w1HBits (rd : program.Valuation interp) : BitWires (interp 1).K (8 * 768) :=
  fun t => program.evalE rd 1 (.leaf 70) t

/-- **The SampleInBall stream's bits** (`h2c.sib.out`: the two squeezed blocks, values `554` and
`555`, `1088` bits each). -/
def sibBits (rd : program.Valuation interp) : BitWires (interp 1).K (8 * 272) :=
  fun t => if (t : ℕ) < 1088 then program.evalE rd 1 (.leaf 554) t
    else program.evalE rd 1 (.leaf 555) (t - 1088)

/-- **The SampleInBall stream** as bytes: byte `o` of `h2c.sib.out`. -/
def sibStream (rd : program.Valuation interp) : Fin (264 + 8) → ℕ :=
  fun o => natOfBits (Falcon512.HashCircuit.byteWires (sibBits rd) o)

/-- **H's decoded challenge's support** (the shared expression `523`,
`c_enc + (θ + 1)(c_enc² + c_enc)`) at coefficient `k`, read as a natural. -/
def supH (rd : program.Valuation interp) (k : Fin 256) : ℕ :=
  (interp 1).toNat (program.evalE rd 1 (.ref 523) k)

/-- **H's decoded challenge's sign** (the shared expression `522`, `c_enc² + c_enc`) at coefficient
`k`, read as a natural. -/
def sgnH (rd : program.Valuation interp) (k : Fin 256) : ℕ :=
  (interp 1).toNat (program.evalE rd 1 (.ref 522) k)

/-- **H's decoded challenge**: `support − 2 · sign` at each coefficient. -/
def chalH (rd : program.Valuation interp) (k : Fin 256) : ℤ :=
  (supH rd k : ℤ) - 2 * (sgnH rd k : ℤ)

/-- **The values of domain `H` the frontend reads by their node types**: the message and its
in-message flags (`67`, `68`), the selected bytes (`556`), the memory check's cells (`560`, `562`,
`563`, `564`, `565`) and its sign bits (`561`). -/
def hTyped : List ℕ := [67, 68, 556, 560, 561, 562, 563, 564, 565]

/-- **The values of domain `H`'s core read by their node types**: the selected bytes (`556`), the
memory check's cells (`560`, `562`, `563`, `564`, `565`) and its sign bits (`561`). -/
def hTypedCore : List ℕ := [556, 560, 561, 562, 563, 564, 565]

/-- **The values of `μ`'s call read by their node types**: the message and its in-message flags
(`67`, `68`). -/
def hTypedMu : List ℕ := [67, 68]

theorem mem_hTyped_of_core {v : ℕ} (hv : v ∈ hTypedCore) : v ∈ hTyped := by
  simp only [hTyped, hTypedCore, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
  omega

theorem mem_hTyped_of_mu {v : ℕ} (hv : v ∈ hTypedMu) : v ∈ hTyped := by
  simp only [hTyped, hTypedMu, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
  omega

theorem mem_hTyped_cases {v : ℕ} (hv : v ∈ hTyped) : v ∈ hTypedMu ∨ v ∈ hTypedCore := by
  simp only [hTyped, hTypedCore, hTypedMu, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
  omega

/-- **Domain `H`'s part of the source program holds**: the predicates `18 … 270` (the Keccak trace,
`μ`'s padding, the selection and the memory check; the cross-field `equal` `272` relates `H` to `A`
and is not among them), and the values `hTyped` lie in their node types. The frontend's facts about
domain `H` read nothing else, so they hold for every program holding these predicates and types
(`SourceSatAt.toHSat`; an arm sharing domain `H` up to a renaming of its values, `GordieHowe/Language/RealizedProgram/Embed.lean`). -/
structure HSat (e : program.Env interp) : Prop where
  /-- The predicates of domain `H` hold. -/
  preds : ∀ k, hPredLo ≤ k → k ≤ hPredHi → program.HoldsAt e (program.predicate k).body
  /-- The values `hTyped` lie in their node types. -/
  types : ∀ v ∈ hTyped, ∀ i < (program.value v).size,
    (interp (program.valueField v)).InType (program.value v).type (program.reader e v i)

/-- **Domain `H`'s core holds**: the predicates `48 … 270` (`c̃'`'s seven absorbs, the SampleInBall
stream's absorb and squeeze, the selection and the memory check), and the values `hTypedCore` lie
in their node types. The core's facts (`c̃'`'s and the stream's calls, SampleInBall) read nothing
else: `μ` enters them only as the bits of value `120` (`muBits`). -/
structure HSatCore (e : program.Env interp) : Prop where
  /-- The predicates of domain `H`'s core hold. -/
  preds : ∀ k, corePredLo ≤ k → k ≤ hPredHi → program.HoldsAt e (program.predicate k).body
  /-- The values `hTypedCore` lie in their node types. -/
  types : ∀ v ∈ hTypedCore, ∀ i < (program.value v).size,
    (interp (program.valueField v)).InType (program.value v).type (program.reader e v i)

/-- **`μ`'s part of domain `H` holds**: the predicates `18 … 47` (`μ`'s absorb and its padding),
and the values `hTypedMu` lie in their node types. -/
structure HSatMu (e : program.Env interp) : Prop where
  /-- The predicates of `μ`'s call hold. -/
  preds : ∀ k, 18 ≤ k → k ≤ 47 → program.HoldsAt e (program.predicate k).body
  /-- The values `hTypedMu` lie in their node types. -/
  types : ∀ v ∈ hTypedMu, ∀ i < (program.value v).size,
    (interp (program.valueField v)).InType (program.value v).type (program.reader e v i)

/-- **Domain `H`'s part gives its core.** -/
theorem HSat.core {e : program.Env interp} (hs : HSat e) : HSatCore e where
  preds k h1 h2 := hs.preds k (by unfold hPredLo; unfold corePredLo at h1; omega) h2
  types v hv := hs.types v (mem_hTyped_of_core hv)

/-- **Domain `H`'s part gives `μ`'s part.** -/
theorem HSat.mu {e : program.Env interp} (hs : HSat e) : HSatMu e where
  preds k h1 h2 := hs.preds k h1 (by unfold hPredHi; omega)
  types v hv := hs.types v (mem_hTyped_of_mu hv)

/-- **Domain `H`'s part from its core and `μ`'s part.** -/
theorem HSat.ofParts {e : program.Env interp} (hc : HSatCore e) (hm : HSatMu e) : HSat e where
  preds k h1 h2 := by
    by_cases h : k ≤ 47
    · exact hm.preds k h1 h
    · exact hc.preds k (by unfold corePredLo; omega) h2
  types v hv := (mem_hTyped_cases hv).elim (hm.types v) (hc.types v)

/-- The predicates `18 … 270` are source predicates of the table. -/
theorem hPreds_facts [MldsaHBase program] : ∀ k, hPredLo ≤ k → k ≤ hPredHi →
    k < program.predicates.length ∧ program.inSource (program.predicate k) = true :=
  MldsaHBase.hPreds

/-- The values `hTyped` are node-typed source values of the table. -/
theorem hTyped_facts [MldsaHBase program] : ∀ v ∈ hTyped, v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node :=
  MldsaHBase.hTyped

/-- **The source program gives domain `H`'s part.** -/
theorem _root_.GordieHowe.RealizedProgram.SourceSatAt.toHSat [MLDSA44.MldsaHBase program]
    {e : program.Env interp}
    (hs : program.SourceSatAt e) : MLDSA44.HSat e where
  preds k h1 h2 := hs.preds _ (RealizedProgram.predicate_mem (MLDSA44.hPreds_facts k h1 h2).1)
    (MLDSA44.hPreds_facts k h1 h2).2
  types v hv := hs.types v (MLDSA44.hTyped_facts v hv).1 (MLDSA44.hTyped_facts v hv).2.1 (MLDSA44.hTyped_facts v hv).2.2

/-- **The source program gives domain `H`'s core.** -/
theorem _root_.GordieHowe.RealizedProgram.SourceSatAt.toHSatCore [MLDSA44.MldsaHBaseCore program]
    {e : program.Env interp} (hs : program.SourceSatAt e) : MLDSA44.HSatCore e where
  preds k h1 h2 := hs.preds _ (RealizedProgram.predicate_mem (MLDSA44.MldsaHBaseCore.predsCore k h1 h2).1)
    (MLDSA44.MldsaHBaseCore.predsCore k h1 h2).2
  types v hv := hs.types v (MLDSA44.MldsaHBaseCore.typedCore v hv).1 (MLDSA44.MldsaHBaseCore.typedCore v hv).2.1
    (MLDSA44.MldsaHBaseCore.typedCore v hv).2.2

/-- **The source program gives `μ`'s part of domain `H`.** -/
theorem _root_.GordieHowe.RealizedProgram.SourceSatAt.toHSatMu [MLDSA44.MldsaHBaseMu program]
    {e : program.Env interp} (hs : program.SourceSatAt e) : MLDSA44.HSatMu e where
  preds k h1 h2 := hs.preds _ (RealizedProgram.predicate_mem (MLDSA44.MldsaHBaseMu.predsMu k h1 h2).1)
    (MLDSA44.MldsaHBaseMu.predsMu k h1 h2).2
  types v hv := hs.types v (MLDSA44.MldsaHBaseMu.typedMu v hv).1 (MLDSA44.MldsaHBaseMu.typedMu v hv).2.1
    (MLDSA44.MldsaHBaseMu.typedMu v hv).2.2

variable (program F0 FH) in
/-- **One SHAKE256 call of domain `H`**, squeezing `outLen` bytes, sound where `Sat` holds:
`SpongeView` with `Sat` for the source program. -/
structure SpongeOn (Sat : program.Env interp → Prop) (outLen : ℕ) where
  /-- The number of input bytes. -/
  len : program.Env interp → ℕ
  /-- The input bytes. -/
  input : (e : program.Env interp) → Fin (len e) → BitWires (interp 1).K 8
  /-- The output bytes. -/
  out : program.Env interp → Fin outLen → BitWires (interp 1).K 8
  /-- **The hash's soundness**: where `Sat` holds, output byte `o` is byte `o` of the SHAKE256
  output of the input bytes. -/
  sound : ∀ e, Sat e → ∀ o, natOfBits (out e o) =
    xofFin Shake256.SpongeSpec.shake256.xof (Shake256.inputBytes (input e)) outLen o

variable (program F0 FH) in
/-- **One SHAKE256 call of domain `H`** sound where domain `H`'s part holds (`HSat`). -/
abbrev HSponge (outLen : ℕ) := SpongeOn program F0 FH (fun e => HSat e) outLen

variable (program F0 FH) in
/-- **One SHAKE256 call of domain `H`'s core** sound where the core holds (`HSatCore`). -/
abbrev HSpongeCore (outLen : ℕ) := SpongeOn program F0 FH (fun e => HSatCore e) outLen

variable (program F0 FH) in
/-- **One SHAKE256 call of `μ`'s part** sound where `μ`'s part holds (`HSatMu`). -/
abbrev HSpongeMu (outLen : ℕ) := SpongeOn program F0 FH (fun e => HSatMu e) outLen

/-- **A call sound under a weaker hypothesis** is sound under a stronger one. -/
def SpongeOn.mono {Sat Sat' : program.Env interp → Prop} {outLen : ℕ}
    (s : SpongeOn program F0 FH Sat outLen) (h : ∀ e, Sat' e → Sat e) :
    SpongeOn program F0 FH Sat' outLen where
  len := s.len
  input := s.input
  out := s.out
  sound e hs o := s.sound e (h e hs) o

variable (program F0 FH) in
/-- **The core of the hash as the frontend reads it**: the two SHAKE256 calls of domain `H`'s core
(`SpongeView`), `c̃' = SHAKE256(μ ‖ w1Encode(w1), 32)` over the bits of `μ` (value `120`) and H's
`w1`, and the SampleInBall stream `SHAKE256(c̃', 272)`, each call's input and output the program's
readings where the core holds (`HSatCore`). -/
structure HashViewCore where
  /-- `c̃'`'s call. -/
  cTilde : HSpongeCore program F0 FH 32
  /-- The SampleInBall stream's call. -/
  sib : HSpongeCore program F0 FH 272
  /-- `c̃'`'s input is `μ ‖ w1`. -/
  cTilde_input : ∀ e, HSatCore e → Shake256.inputBytes (cTilde.input e) =
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) ++
      Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits (program.reader e)))
  /-- `c̃'`'s output is `h2c.c_tilde.out`. -/
  cTilde_out : ∀ e, HSatCore e → ∀ o,
    natOfBits (cTilde.out e o) = natOfBits (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)) o)
  /-- The stream's input is `c̃'`. -/
  sib_input : ∀ e, HSatCore e → Shake256.inputBytes (sib.input e) =
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)))
  /-- The stream's output is `h2c.sib.out`. -/
  sib_out : ∀ e, HSatCore e → ∀ o,
    natOfBits (sib.out e o) = sibStream (program.reader e) o

variable (program F0 FH) in
/-- **`μ`'s call as the frontend reads it**: `μ = SHAKE256(tr ‖ 0x00 ‖ 0x00 ‖ M, 64)` over the
message at the length the in-message flags encode, its input and output the program's readings
where `μ`'s part holds (`HSatMu`). -/
structure HashViewMu where
  /-- `μ`'s call. -/
  mu : HSpongeMu program F0 FH 64
  /-- `μ`'s input is `tr ‖ 0x00 ‖ 0x00 ‖ M`. -/
  mu_input : ∀ e, HSatMu e → Shake256.inputBytes (mu.input e) =
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (trBits (program.reader e))) ++ [0, 0] ++
      (List.ofFn (messageBytes (program.reader e))).map UInt8.toNat
  /-- `μ`'s output is `h2c.mu.out` where `tr`'s entries are bits (the statement's `tr` is a public
  value the program does not range-check; a statement holding a key's preprocessing has bits
  there, `KeyOf.tr`). -/
  mu_out : ∀ e, HSatMu e → AllBool (trBits (program.reader e)) → ∀ o,
    natOfBits (mu.out e o) = natOfBits (Falcon512.HashCircuit.byteWires (muBits (program.reader e)) o)

variable (program F0 FH) in
/-- **The hash of `MLDSA44.Native.ROMParams` as the frontend reads it**: the three SHAKE256 calls of
domain `H` (`SpongeView`), `μ`'s (`HashViewMu`) and the core's, `c̃'` and the SampleInBall stream
(`HashViewCore`). -/
structure HashView extends HashViewCore program F0 FH, HashViewMu program F0 FH

/-- **SampleInBall's outcome at a valuation**: the fixed-stream `SampleInBall`
(`MLDSA44.fixedStreamChallenge`: the rising selection, then the Fisher–Yates swaps) of the stream
succeeds with H's decoded challenge, and H's decoded support and sign are read as bits (the memory
check confines `c_enc` to `{0, 1, θ}`). -/
structure SampledAt (rd : program.Valuation interp) : Prop where
  /-- The fixed-stream `SampleInBall` of the stream is H's decoded challenge. -/
  challenge : MLDSA44.fixedStreamChallenge mldsa44 (sibStream rd) = some (chalH rd)
  /-- The supports are bits. -/
  sup_lt : ∀ k, supH rd k < 2
  /-- The signs are bits. -/
  sgn_lt : ∀ k, sgnH rd k < 2

variable (program F0 FH) in
/-- **SampleInBall as the frontend reads it**: per-challenge events at the source challenges
(`h2c.sample.select.delta`, `h2c.sample.mem.delta`) with the challenge-use rule and their
probability bounds, and, where the source program holds and no event occurred, the fixed-stream
`SampleInBall` (`MLDSA44.fixedStreamChallenge`: the rising selection, then the Fisher–Yates swaps)
of the stream succeeds with H's decoded challenge. The instance reads the selection's and the
memory check's predicates, in domain `H`'s core (`HSatCore`). -/
structure SampleView where
  /-- The event at each challenge. -/
  event : ℕ → program.Env interp → Prop
  /-- The error at each challenge. -/
  eps : ℕ → NNReal
  /-- Each event reads only what is fixed when its challenge is drawn, and the challenge. -/
  use : RealizedProgram.ChallengeUseAt program interp event
  /-- The events' probability bounds. -/
  bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env interp,
    Pr[c ← program.ChalVal interp j : event j (e.setChal j c)] ≤ eps j
  /-- **SampleInBall's soundness**: the fixed-stream `SampleInBall` of the stream is H's decoded
  challenge, whose support and sign are bits. -/
  sound : ∀ e, HSatCore e → (∀ j, program.IsSourceChal j → ¬ event j e) →
    SampledAt (program.reader e)

/-- **The bytes of `c̃'` are the extracted `c̃`.** -/
theorem inputBytes_cTilde (rd : program.Valuation interp) :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (cTildeBits rd)) =
      (cTildeOf rd).toList.map UInt8.toNat := by
  apply List.ext_getElem
  · simp only [Shake256.inputBytes, cTildeOf, List.length_ofFn, List.length_map,
      Vector.length_toList]
    rfl
  · intro i hi hj
    simp only [Shake256.inputBytes, cTildeOf, Vector.toList_ofFn, List.getElem_map,
      List.getElem_ofFn]
    rw [Native.toNat_toUInt8_natOfBits]
    rfl

/-- **The bytes of `tr`** of a statement whose `tr` holds the bits of `H(pk)` are `H(pk)`. -/
theorem inputBytes_tr {pk : MLDSA44.PublicKey44} {x : program.Valuation interp}
    (htr : trBits x = Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf pk i).toNat) :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (trBits x)) =
      (Native.Rows.prims.hashPublicKey pk.rho pk.t1).toList.map UInt8.toNat := by
  rw [htr, Shake256.inputBytes]
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp only [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
  rw [Falcon512.HashCircuit.natOfBits_byteWires_wiresOfByteVec (fun i => UInt8.toNat_lt _)]
  simp only [MLDSA44.PoP.Compose.trOf, Vector.get_eq_getElem]

/-- **`tr` reads the statement** (an opaque value of no argument). -/
theorem trBits_reader [MldsaHBaseMu program] (e : program.Env interp) :
    trBits (program.reader e) = trBits e.stmt := by
  funext k
  simp only [trBits, RealizedProgram.evalE_leaf]
  rw [RealizedProgram.reader_of_opaque_nil e MldsaHBaseMu.trKind]

/-- **The SampleInBall stream is `SHAKE256(c̃')`** where domain `H`'s core holds. -/
theorem sibStream_eq_core (hv : HashViewCore program F0 FH) {e : program.Env interp}
    (hs : HSatCore e) :
    sibStream (program.reader e) =
      xofFin GordieHowe.shake256 ((cTildeOf (program.reader e)).toList.map UInt8.toNat) (264 + 8) := by
  funext o
  rw [← hv.sib_out e hs o, hv.sib.sound e hs o, hv.sib_input e hs, inputBytes_cTilde,
    Shake256.SpongeSpec.xof_shake256]

/-- **The SampleInBall stream is `SHAKE256(c̃')`** where the source program holds. -/
theorem sibStream_eq (hv : HashView program F0 FH) {e : program.Env interp} (hs : HSat e) :
    sibStream (program.reader e) =
      xofFin GordieHowe.shake256 ((cTildeOf (program.reader e)).toList.map UInt8.toNat) (264 + 8) :=
  sibStream_eq_core hv.toHashViewCore hs.core

/-- **`c̃'` is the commitment hash** `H(μ ‖ w, 32)` (FIPS 204 Algorithm 8, line 12, at its
`hashCommitment`) where domain `H`'s core holds, at any `μ` whose bytes are those of `muBits` and
any `w` whose bytes are those of H's `w1` bits. -/
theorem cTildeOf_eq_hashCommitment (hv : HashViewCore program F0 FH) {e : program.Env interp}
    (hs : HSatCore e) {mu : _root_.MLDSA.Bytes 64} {w : List UInt8}
    (hmu : Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) =
      mu.toList.map UInt8.toNat)
    (hw : Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits (program.reader e))) =
      w.map UInt8.toNat) :
    _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44 mu w = cTildeOf (program.reader e) := by
  apply Vector.ext
  intro i hi
  apply UInt8.toNat_inj.mp
  have hl := MLDSA44.hashCommitment_get mu w ⟨i, hi⟩
  change UInt8.toNat (Vector.get _ ⟨i, hi⟩) = UInt8.toNat (Vector.get _ ⟨i, hi⟩)
  refine hl.trans ?_
  rw [← hmu, ← hw, ← Shake256.SpongeSpec.xof_shake256, ← hv.cTilde_input e hs,
    ← hv.cTilde.sound e hs ⟨i, hi⟩, hv.cTilde_out e hs ⟨i, hi⟩]
  simp only [cTildeOf, Vector.get_ofFn]
  rw [Native.toNat_toUInt8_natOfBits]
  rfl

/-- **`μ`'s bytes** are `SHAKE256(tr ‖ frame([], M), 64)` where `μ`'s part holds, at a statement
whose `tr` holds the bits of `H(pk)`. -/
theorem muBytes_eq_mu [MldsaHBaseMu program] (hv : HashViewMu program F0 FH) {e : program.Env interp}
    (hs : HSatMu e) {pk : MLDSA44.PublicKey44}
    (hkey : trBits e.stmt = Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf pk i).toNat) :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) =
      (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1)
        (MLDSA44.frame [] (List.ofFn (messageBytes (program.reader e))))).toList.map UInt8.toNat := by
  have htr : AllBool (trBits (program.reader e)) := by
    rw [trBits_reader, hkey]
    exact Falcon512.HashCircuit.wiresOfByteVec_allBool _
  rw [← HashCircuit.ofFn_mu, Shake256.inputBytes]
  refine congrArg List.ofFn (funext fun o => ?_)
  rw [← hv.mu_out e hs htr o, hv.mu.sound e hs o, hv.mu_input e hs, trBits_reader, inputBytes_tr hkey,
    Shake256.SpongeSpec.xof_shake256, HashCircuit.mu, MLDSA44.frame]
  simp

/-- **`μ`'s bytes** are `SHAKE256(tr ‖ frame([], M), 64)` where the source program holds, at a
statement whose `tr` holds the bits of `H(pk)`. -/
theorem muBytes_eq [MldsaHBaseMu program] (hv : HashView program F0 FH) {e : program.Env interp} (hs : HSat e)
    {pk : MLDSA44.PublicKey44}
    (hkey : trBits e.stmt = Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf pk i).toNat) :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) =
      (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1)
        (MLDSA44.frame [] (List.ofFn (messageBytes (program.reader e))))).toList.map UInt8.toNat :=
  muBytes_eq_mu hv.toHashViewMu hs.mu hkey

/-- **The message bytes depend only on the message and its flags** (values `68` and `69`). -/
theorem ofFn_messageBytes_congr {rd rd' : program.Valuation interp} (h68 : rd 67 = rd' 67)
    (h69 : rd 68 = rd' 68) : List.ofFn (messageBytes rd) = List.ofFn (messageBytes rd') := by
  have hL : lenOf rd = lenOf rd' := by
    unfold lenOf
    rw [Finset.filter_congr (q := fun i : Fin 136 => program.evalE rd' 1 (.leaf 68) i = 1)
      fun i _ => by simp only [RealizedProgram.evalE_leaf, h69]]
  unfold messageBytes messageBits
  simp only [RealizedProgram.evalE_leaf, h68]
  rw [hL]

end H

/-- The native program at the ROM parameters has domain `H`'s base facts. -/
instance : MldsaHBase program where
  hPreds := Generated.MLDSA44.Native.ROMParams.ShapeFacts.predicate_h2c_2emu_2eblocks_2er0_source_range
  hTyped := by shape_decide
  trKind := Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_tr_kind

/-- **The program facts of domain `A` the native frontend's composition reads** (`MldsaHBase` and):
the values the extractor reads read nothing from the run. Each program instantiates it by
`decide`. -/
class MldsaABase (program : RealizedProgram) : Prop extends MldsaHBase program where
  /-- The values the extractor reads read nothing from the run. -/
  projReads : ∀ v ∈ [57, 58, 67, 68, 457], program.nodeReads program.fuel v = []

/-- The native program at the ROM parameters has the composition's facts. -/
instance : MldsaABase program where
  projReads := by shape_decide

section A

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaABase program] {F0 FH : RealizedProgram.FieldInterp} [QField F0]
  [HField FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The statement -/

/-- **The statement's `Â`** at row `i`, column `j`, spectrum index `k`: coordinate
`(4 i + j) · 256 + k` of `key.a_hat` (value `55`, the operand layout of `polyMatVec`), read as a
natural (the constant coordinate of `F_q^6`). -/
def aHatAt (x : program.Valuation interp) (i j : Fin 4) (k : Fin 256) : ℕ :=
  (interp 0).toNat (program.evalE x 0 (.leaf 55) (((i : ℕ) * 4 + j) * 256 + k))

/-- **The statement's `t1`** at row `i`, coefficient `k`: coordinate `256 i + k` of `key.t1`
(value `56`), read as a natural. -/
def t1At (x : program.Valuation interp) (i : Fin 4) (k : Fin 256) : ℕ :=
  (interp 0).toNat (program.evalE x 0 (.leaf 56) ((i : ℕ) * 256 + k))

/-- **The statement holds a key's preprocessing**: `key.a_hat` holds `Â = ExpandA(ρ)` in NTT form
(`Rows.aHat`, the C++ `fill_public_key`'s `of_scalar` of each spectrum entry), `key.t1`
the coefficients of `t1`, and `tr` the bits of `tr = H(pk)` (`MLDSA44.PoP.Compose.trOf`, the
C++ `key_hash`). -/
structure KeyOf (pk : MLDSA44.PublicKey44) (x : program.Valuation interp) : Prop where
  /-- `key.a_hat` holds `Â`. -/
  aHat : ∀ i j k, aHatAt x i j k = ((((Native.Rows.aHat pk).get i).get j).coeffs.get k).val
  /-- `key.t1` holds `t1`. -/
  t1 : ∀ i k, t1At x i k = ((pk.t1.get i).get k).val
  /-- `tr` holds the bits of `H(pk)`. -/
  tr : trBits x = Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf pk i).toNat

/-! ## The relation -/

/-- **The maximal message length of the ML-DSA-44 proofs of possession** (the paper's `n_m`):
`32` bytes, the exported programs' message buffer (`statement.msgLen`). -/
abbrev msgLenMax : ℕ := 32

/-- **The witness of `MLDSA44.Native.ROMParams`**: a message of some length `L ≤ msgLenMax` (the
program's maximum, its `statement.msgLen`) and the signature bytes
(`MLDSA44.PoP.VarWitness msgLenMax`). -/
abbrev VarWitness : Type := MLDSA44.PoP.VarWitness msgLenMax

/-- **The relation of the theorem at the realized program of `MLDSA44.Native.ROMParams`**: at every encoded key whose
decoded key's `ExpandA` finishes within the byte budget (`MLDSA44.ExpandAWithin`) and whose
preprocessing the statement
holds (`KeyOf`), the ML-DSA-44 proof-of-possession relation for messages of at most `32` bytes holds
for the witness (`MLDSA44.PoP.relUpTo 32`: `MLDSA44.VerifiesBytes` at the empty context). -/
def rel : Set (program.Valuation interp × VarWitness) :=
  Function.uncurry fun x w => ∀ s : MLDSA44.PoP.Statement 0, s.ExpandAWithin →
    KeyOf (MLDSA44.pkDecode44 s.key) x → (s, w) ∈ MLDSA44.PoP.relUpTo msgLenMax

/-! ## The readings of the committed values -/

/-- **`z`** (value `57` of domain `A`, `4 × 256`), read in `F_q^6`. -/
def zVals (rd : program.Valuation interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) : (interp 0).K :=
  program.evalE rd 0 (.leaf 57) ((j : ℕ) * 256 + k)

/-- **The hint `h`** (value `58` of domain `A`, `4 × 256`), read in `F_q^6`. -/
def hVals (rd : program.Valuation interp) (i : Fin Native.Rows.nRows)
    (k : Fin Native.Rows.deg) : (interp 0).K :=
  program.evalE rd 0 (.leaf 58) ((i : ℕ) * 256 + k)

/-- **The extracted `z`**: each coefficient the natural below `q` its reading is the cast of
(`NativeAlgebraCircuit.coeffRep`). -/
def zOf (rd : program.Valuation interp) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l :=
  Vector.ofFn fun j => MLDSA44.ofCoeff fun k => NativeAlgebraCircuit.coeffRep (zVals rd j k)

/-- **The extracted signature**: `sigEncode(c̃', z, h)` (FIPS 204 Algorithm 26) of the extracted
`c̃`, `z` and the hint read from its cells (`MLDSA44.PoP.Native.decodeH`). -/
def sigOf (rd : program.Valuation interp) : ByteArray :=
  _root_.MLDSA.Concrete.sigEncode _root_.MLDSA.mldsa44 (cTildeOf rd) (zOf rd)
    (MLDSA44.PoP.Native.decodeH (hVals rd))

/-! ## The extractor -/

/-- **The environment of a statement and a committed assignment** with every challenge and late
value `0`: what the extractor reads the committed values from (they read nothing from the run). -/
def commitEnv (x : program.Valuation interp) (a : program.Assignment interp) :
    program.Env interp :=
  ⟨x, a, fun _ _ => 0, fun _ _ => 0⟩

/-- **The witness extracted from a statement and a committed assignment**: the length the flags
encode (`lenOf`), the message bytes at it (`messageBytes`) and the signature `sigEncode(c̃', z, h)`
(`sigOf`), all read in the environment of the statement and the committed assignment
(`commitEnv`).

Running time: `136` flag readings, `8 · 32` message bits, `256` bits of `c̃'`, `2 · 1024` readings
of `z` and `h` in domain `A` (each a committed value or a bound value's digit sum), `1024`
coefficients lifted below `q` (`NativeAlgebraCircuit.coeffRep`, a search below `q`), and the vendored
`sigEncode`, polynomial in the program's size.
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) :
    VarWitness :=
  ⟨⟨lenOf (program.reader (commitEnv x a)), Nat.lt_succ_of_le (lenOf_le _)⟩,
    ⟨messageBytes (program.reader (commitEnv x a)), sigOf (program.reader (commitEnv x a))⟩⟩

/-- **The extractor of `Π_P₀`** for `MLDSA44.Native.ROMParams` (`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec interp) (program.Valuation interp) VarWitness :=
  program.sourceExtractor interp proj


/-! ## The readings of the hash and the crossing -/

/-- **A's `w1` bits** (value `62`, `hint.w1`, `4 × 256 × 6` bits of domain `A`, the same order). -/
def w1ABits (rd : program.Valuation interp) : BitWires (interp 0).K (8 * 768) :=
  fun t => program.evalE rd 0 (.leaf 62) t

/-- **A's challenge bits** (value `59`, `challenge.c`, `256 × 2` bits of domain `A`: the support of
coefficient `k` at `2 k`, its sign at `2 k + 1`). -/
def cABits (rd : program.Valuation interp) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) :
    (interp 0).K :=
  program.evalE rd 0 (.leaf 59) (2 * k + s)

/-- **A's challenge polynomial**: `support − 2 · sign` of its challenge bits
(`Rows.bitCoeff`). -/
def cPolyA (rd : program.Valuation interp) : _root_.MLDSA.Rq :=
  MLDSA44.ofCoeff fun k =>
    Native.Rows.bitCoeff (cABits rd k 0) - 2 * Native.Rows.bitCoeff (cABits rd k 1)

/-- **`w'`** (value `60`, `signature.w`, `4 × 256` of domain `A`). -/
def wVals (rd : program.Valuation interp) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) : (interp 0).K :=
  program.evalE rd 0 (.leaf 60) ((i : ℕ) * 256 + k)

/-- **The extracted `w'`**: each coefficient lifted below `q`. -/
def wOf (rd : program.Valuation interp) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun k => NativeAlgebraCircuit.coeffRep (wVals rd i k)

/-! ## The views -/

/-- **The crossing at a valuation** (`mac.equal`): A's `hint.w1` bits and challenge bits read as
naturals are H's `w1` bits and H's decoded support and sign. -/
structure CrossAt (rd : program.Valuation interp) : Prop where
  /-- The `w1` bits agree. -/
  w1 : ∀ t, (interp 0).toNat (w1ABits rd t) = (interp 1).toNat (w1HBits rd t)
  /-- The supports agree. -/
  sup : ∀ k, (interp 0).toNat (cABits rd k 0) = supH rd k
  /-- The signs agree. -/
  sgn : ∀ k, (interp 0).toNat (cABits rd k 1) = sgnH rd k

/-- **The crossing wherever the source program holds and H's decoded support and sign are bits**
(`mac.equal`, the cross-field `equal`'s meaning: the readings agree where H's operand is read as
bits; its `w1` part is a bit view, its challenge part bits by SampleInBall's soundness). -/
def CrossSound : Prop :=
  ∀ e : program.Env interp, program.SourceSatAt e → (∀ k, supH (program.reader e) k < 2) →
    (∀ k, sgnH (program.reader e) k < 2) → CrossAt (program.reader e)

/-- **The algebra holds at a key** (domain `A`'s obligation), on the readings of domain `A`: the
challenge and `w1` bits are Boolean, `w' = computeWApprox(Â, c, z, t1)` with `c` A's challenge
polynomial, `w1 = UseHint(h, w')` coefficientwise, `‖z‖∞ < γ₁ − β` and the hint weight at most `ω`
(`Native.AlgebraConstraints` on the program's readings). -/
structure AlgebraAt (pk : MLDSA44.PublicKey44) (rd : program.Valuation interp) : Prop where
  /-- The challenge bits are Boolean. -/
  cBool : ∀ k s, cABits rd k s = 0 ∨ cABits rd k s = 1
  /-- The `w1` bits are Boolean. -/
  w1Bool : AllBool (w1ABits rd)
  /-- `w' = computeWApprox(Â, c, z, t1)`. -/
  algebra : wOf rd = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
    (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk) (cPolyA rd)
    (zOf rd) pk.t1
  /-- `w1 = UseHint(h, w')`. -/
  useHint : ∀ i k, NativeAlgebraCircuit.w1Coeff (w1ABits rd) i k =
    _root_.MLDSA.Concrete.useHintCoeff (NativeAlgebraCircuit.decodeHint (hVals rd) i k)
      (MLDSA44.coeff ((wOf rd).get i) k) mldsa44.γ₂
  /-- `‖z‖∞ < γ₁ − β`. -/
  norm : ∀ j k,
    (LatticeCrypto.centeredRepr (MLDSA44.coeff ((zOf rd).get j) k)).natAbs < mldsa44.normBound
  /-- The hint weight is at most `ω`. -/
  hintWeight : (Finset.univ.filter fun ik : Fin Native.Rows.nRows × Fin Native.Rows.deg =>
    NativeAlgebraCircuit.decodeHint (hVals rd) ik.1 ik.2 = true).card ≤ mldsa44.ω

/-- **Domain `A`'s obligation** (`AlgebraAt` wherever the source program holds): at every
environment where the source program holds and every key whose preprocessing the statement holds,
the algebra holds at the key. -/
def AlgebraSound : Prop :=
  ∀ e : program.Env interp, program.SourceSatAt e → ∀ pk, KeyOf pk e.stmt →
    AlgebraAt pk (program.reader e)


/-! ## Readings of `F_q^6` -/

/-- The integer reading of `F_q^6` reads a natural below `q` as itself. -/
theorem toNat_fq6_natCast {k : ℕ} (hk : k < 8380417) :
    (interp 0).toNat (k : (interp 0).K) = k :=
  QField.toNat_natCast hk

/-- **A Boolean element of `F_q^6` as a coefficient** is its integer reading. -/
theorem bitCoeff_eq_toNat {v : (interp 0).K} (hv : v = 0 ∨ v = 1) :
    Native.Rows.bitCoeff v = ((interp 0).toNat v : _root_.MLDSA.Coeff) := by
  rcases hv with rfl | rfl
  · rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm,
      toNat_fq6_natCast (by decide)]
    unfold Native.Rows.bitCoeff
    simp
  · rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
      toNat_fq6_natCast (by decide)]
    unfold Native.Rows.bitCoeff
    simp

/-- **A Boolean element of `F_q^6` is read as `0` or `1`.** -/
theorem toNat_lt_two_of_bool {v : (interp 0).K} (hv : v = 0 ∨ v = 1) : (interp 0).toNat v < 2 := by
  rcases hv with rfl | rfl
  · rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm,
      toNat_fq6_natCast (by decide)]
    decide
  · rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
      toNat_fq6_natCast (by decide)]
    decide

/-- **A Boolean element of `F_q^6` is `1` exactly when it is read as `1`.** -/
theorem eq_one_iff_toNat {v : (interp 0).K} (hv : v = 0 ∨ v = 1) :
    v = 1 ↔ (interp 0).toNat v = 1 := by
  rcases hv with rfl | rfl
  · rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm,
      toNat_fq6_natCast (by decide)]
    simp
  · simp only [true_iff]
    rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
      toNat_fq6_natCast (by decide)]

/-! ## The composition's parts -/

/-- **A's challenge polynomial is H's decoded challenge**, given the crossing and the Booleanity
of A's challenge bits. -/
theorem cPolyA_eq {rd : program.Valuation interp} (hx : CrossAt rd)
    (hb : ∀ k s, cABits rd k s = 0 ∨ cABits rd k s = 1) :
    cPolyA rd = MLDSA44.ofCoeff fun k => (chalH rd k : _root_.MLDSA.Coeff) := by
  unfold cPolyA
  refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
  rw [bitCoeff_eq_toNat (hb k 0), bitCoeff_eq_toNat (hb k 1),
    show (interp 0).toNat (cABits rd k 0) = supH rd k from hx.sup k,
    show (interp 0).toNat (cABits rd k 1) = sgnH rd k from hx.sgn k]
  change _ = (((supH rd k : ℤ) - 2 * (sgnH rd k : ℤ) : ℤ) : _root_.MLDSA.Coeff)
  push_cast
  ring

/-- **H's `w1` bits are the bits of A's UseHint outputs**, given the crossing and the Booleanity of
A's `w1` bits. -/
theorem w1HBits_eq {rd : program.Valuation interp} (hx : CrossAt rd) (hb : AllBool (w1ABits rd))
    (i : Fin _root_.MLDSA.mldsa44.k) (c : Fin _root_.MLDSA.ringDegree) (b : Fin 6) :
    w1HBits rd ⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩ =
      Bits.constBit (((MLDSA44.PoP.Native.decodeW1 (w1ABits rd)).get i).get c).val b := by
  have hidx : (⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩ :
      Fin (8 * 768)) = ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (4 * 256)) + b, by
        have := HashCircuit.w1Bit_lt i c b
        simp only [finProdFinEquiv_apply_val]
        change 6 * ((c : ℕ) + 256 * i) + b < 8 * 768
        change ((i : ℕ) * 256 + c) * 6 + b < 8 * 768 at this
        omega⟩ := Fin.ext (by
    simp only [finProdFinEquiv_apply_val]
    change ((i : ℕ) * 256 + c) * 6 + b = 6 * ((c : ℕ) + 256 * i) + b
    ring)
  have hbits : AllBool (NativeAlgebraCircuit.outputBits (w1ABits rd) (finProdFinEquiv (i, c))) :=
    fun _ => hb _
  rw [MLDSA44.PoP.Native.decodeW1_get, ZMod.val_natCast,
    Nat.mod_eq_of_lt ((MLDSA44.PoP.Native.w1Coeff_lt (w1ABits rd) i c).trans (by decide)),
    NativeAlgebraCircuit.w1Coeff, SelectFirstTau.constBit_eq_ite_testBit]
  have hiff := Native.bit_eq_testBit hbits b
  rw [hidx]
  set t : Fin (8 * 768) := ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (4 * 256)) + b, _⟩
  have hA : w1ABits rd t = 1 ↔ (natOfBits (NativeAlgebraCircuit.outputBits (w1ABits rd)
      (finProdFinEquiv (i, c)))).testBit b := hiff
  have hH := HField.eq_of_toNat_lt_two (hx.w1 t).symm (toNat_lt_two_of_bool (hb t))
  change w1HBits rd t = _ at hH
  rw [hH]
  by_cases ht : (natOfBits (NativeAlgebraCircuit.outputBits (w1ABits rd) (finProdFinEquiv (i, c)))).testBit b
  · rw [if_pos ((eq_one_iff_toNat (hb t)).1 (hA.2 ht)), if_pos ht]
  · rw [if_neg fun h => ht (hA.1 ((eq_one_iff_toNat (hb t)).2 h)), if_neg ht]

/-- **`c̃'` is the commitment hash** `H(μ ‖ w1Encode(w1), 32)` with `μ = H(tr ‖ frame([], M), 64)`
and `w1` A's UseHint outputs, where the source program holds, at a key whose preprocessing the
statement holds (FIPS 204 Algorithm 8, line 12). -/
theorem cTilde_eq_hashCommitment (hv : HashView program F0 FH) {e : program.Env interp}
    (hs : HSat e) {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (hx : CrossAt (program.reader e)) (hb : AllBool (w1ABits (program.reader e))) :
    _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44
        (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1)
          (MLDSA44.frame [] (List.ofFn (messageBytes (program.reader e)))))
        (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
          (MLDSA44.PoP.Native.decodeW1 (w1ABits (program.reader e)))) =
      cTildeOf (program.reader e) := by
  set rd := program.reader e
  have hw1 : Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits rd)) =
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
        (MLDSA44.PoP.Native.decodeW1 (w1ABits rd))).map UInt8.toNat := by
    have hlen := MLDSA44.w1Encode_length_mldsa44 (MLDSA44.PoP.Native.decodeW1 (w1ABits rd))
    apply List.ext_getElem (by rw [Shake256.inputBytes, List.length_ofFn, List.length_map, hlen])
    intro j h₁ h₂
    simp only [Shake256.inputBytes, List.getElem_ofFn, List.getElem_map]
    rw [HashCircuit.natOfBits_byteWires_w1Encode (w1HBits_eq hx hb), List.getD_eq_getElem]
  exact cTildeOf_eq_hashCommitment hv.toHashViewCore hs.core (muBytes_eq hv hs hk.tr) hw1


/-! ## The extractor's readings -/

/-- The values the extractor reads read nothing from the run (`RealizedProgram.nodeReads`). -/
theorem projReads_nil : ∀ v ∈ [57, 58, 67, 68, 457], program.nodeReads program.fuel v = [] :=
  MldsaABase.projReads

/-- **The values the extractor reads read alike** in an environment and in the environment of its
statement and committed assignment (`commitEnv`). -/
theorem reader_commitEnv (e : program.Env interp) {v : ℕ} (hv : v ∈ [57, 58, 67, 68, 457]) :
    program.reader (commitEnv e.stmt e.asg) v = program.reader e v :=
  RealizedProgram.reader_eq_of_nodeReads_nil (projReads_nil v hv) rfl rfl

/-- **The signature depends only on `c̃'`, `z` and `h`** (values `457`, `57` and `58`). -/
theorem sigOf_congr {rd rd' : program.Valuation interp} (h458 : rd 457 = rd' 457)
    (h58 : rd 57 = rd' 57) (h59 : rd 58 = rd' 58) : sigOf rd = sigOf rd' := by
  unfold sigOf cTildeOf cTildeBits zOf zVals hVals
  simp only [RealizedProgram.evalE_leaf, h458, h58, h59]

/-- **The extracted message** is the environment's message bytes. -/
theorem ofFn_proj_message (e : program.Env interp) :
    List.ofFn (proj e.stmt e.asg).2.message = List.ofFn (messageBytes (program.reader e)) :=
  ofFn_messageBytes_congr (reader_commitEnv e (by simp)) (reader_commitEnv e (by simp))

/-- **The extracted signature** is the environment's `sigEncode(c̃', z, h)`. -/
theorem proj_signature (e : program.Env interp) :
    (proj e.stmt e.asg).2.signature = sigOf (program.reader e) :=
  sigOf_congr (reader_commitEnv e (by simp)) (reader_commitEnv e (by simp))
    (reader_commitEnv e (by simp))

/-! ## The composition -/

/-- **The frontend's composition, the views as hypotheses**: where the source program holds and no
SampleInBall event occurred, the relation holds at the statement and the extracted witness, given
the hash view, SampleInBall's view, the crossing and the algebra. At a key whose preprocessing the
statement holds: SampleInBall's stream is `SHAKE256(c̃')` (`sibStream_eq`) and its fixed-stream
`SampleInBall` H's decoded challenge (`SampleView.sound`), which the crossing makes A's challenge
polynomial (`cPolyA_eq`); the algebra gives `w' = computeWApprox(Â, c, z, t1)`, UseHint, the norm
and the hint weight; `c̃'` is the commitment hash of `μ` and A's `w1` (`cTilde_eq_hashCommitment`);
so `MLDSA44.verifiesBytes_of_parts`. -/
theorem mem_rel_of_source (hv : HashView program F0 FH) (sv : SampleView program F0 FH) (hx : CrossSound (program := program) (F0 := F0) (FH := FH)) (hA : AlgebraSound (program := program) (F0 := F0) (FH := FH))
    {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ∀ j, program.IsSourceChal j → ¬ sv.event j e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  intro s hexp hkey
  have halg := hA e hs _ hkey
  have hsam := sv.sound e hs.toHSat.core hno
  have hcr := hx e hs hsam.sup_lt hsam.sgn_lt
  change MLDSA44.VerifiesBytes _ (List.ofFn s.ctx) (List.ofFn (proj e.stmt e.asg).2.message)
    (proj e.stmt e.asg).2.signature
  rw [ofFn_proj_message, proj_signature, List.ofFn_zero, sigOf]
  refine MLDSA44.verifiesBytes_of_parts (C := 264) (c := chalH (program.reader e))
    (W := wOf (program.reader e)) (by decide) hexp ?_ ?_ ?_
    (cTilde_eq_hashCommitment hv hs.toHSat hkey hcr halg.w1Bool) halg.norm ?_
  · rw [← sibStream_eq hv hs.toHSat]
    exact hsam.challenge
  · rw [← cPolyA_eq hcr halg.cBool, ← halg.algebra]
  · exact MLDSA44.PoP.Compose.useHintVec_eq_of_get (fun i k => (MLDSA44.coeff_apply _ k).symm)
      fun i k => by
        rw [MLDSA44.coeff_apply, MLDSA44.PoP.Native.decodeW1_get]
        erw [MLDSA44.PoP.Native.decodeH_get, halg.useHint i k]
        rfl
  · have hwt := MLDSA44.hintWeightVec_ofFn fun i k =>
      NativeAlgebraCircuit.decodeHint (hVals (program.reader e)) i k
    exact hwt.trans_le halg.hintWeight

/-- **The relation from the source program without an event** (`RealizedProgram.rbr_of_events`'
`hsound`), given the views. -/
theorem sound_of_views (hv : HashView program F0 FH) (sv : SampleView program F0 FH) (hx : CrossSound (program := program) (F0 := F0) (FH := FH)) (hA : AlgebraSound (program := program) (F0 := F0) (FH := FH)) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ sv.event j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ _ hs hno => mem_rel_of_source hv sv hx hA hs hno

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Native.ROMParams`**, the hypothesis of the
proof system's headline (`RealizedProgram.rbr_of_events`), given the obligations the frontend leaves to the
program's predicates: the hash view (`HashView`, the Keccak trace's instance), SampleInBall's view
(`SampleView`, its events and errors at `h2c.sample.select.delta` and `h2c.sample.mem.delta`), the
crossing (`CrossSound`, `mac.equal`) and the algebra at every key whose preprocessing the statement
holds (`AlgebraSound`, domain `A`). The extractor is `extractor`. -/
theorem rbr_of_views (hv : HashView program F0 FH) (sv : SampleView program F0 FH) (hx : CrossSound (program := program) (F0 := F0) (FH := FH)) (hA : AlgebraSound (program := program) (F0 := F0) (FH := FH)) :
    RBRKnowledgeSound rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sv.event sv.use (sound_of_views hv sv hx hA))
      (program.roundError interp sv.eps) :=
  program.rbr_of_events interp rel proj sv.event sv.eps sv.use sv.bound (sound_of_views hv sv hx hA)

end A

end GordieHowe.MLDSA44
