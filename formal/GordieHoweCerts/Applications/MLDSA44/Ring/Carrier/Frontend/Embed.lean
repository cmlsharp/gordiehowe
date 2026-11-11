-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHowe.Applications.MLDSA44.EmbedFacts
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: an ML-DSA ring carrier holds the native core and the emulated gadgets

An ML-DSA-44 ring carrier (`MLDSA44.Ring.Carrier.ROMParams`, `MLDSA44.Ring.Carrier.QROMParams`;
C++ `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`) holds two parts of the ML-DSA-44
proof-of-possession programs at the same parameters, each up to a renaming of value,
shared-expression and challenge identifiers; the carrier's challenge `j + 2` is the proof of
possession's challenge `j` (the carrier draws the member table's challenge and the signature
relation's `r` first).

* **Domain `H`'s core of the native program** (`MLDSA44.Native.ROMParams`,
  `MLDSA44.Native.QROMParams`; `lib/gordiehowe/examples/mldsa/mldsa_native.h`), under its renaming: native
  predicates `48 … 270` (the Keccak rounds of `c̃'`, SampleInBall's stream, the selection and the
  memory check) are carrier predicates `26 … 248`, renamed source predicates. The native `μ`
  (values `119`, `120`) is renamed to the carrier's committed `μ` (`mu.words`, `mu`, values `73`,
  `74`); the native part reading `μ` from `tr` and the message (predicates `18 … 47`) is not held.
  So the native frontend's core (`GordieHowe.MLDSA44.HSatCore`) holds in the
  carrier's environment read as the native program's (`hSatCore`).
* **Domain `A`'s gadgets of the emulated program** (`MLDSA44.Emulated.ROMParams`,
  `MLDSA44.Emulated.QROMParams`), under its renaming: emulated predicates `aPreds` (the hint's `w1` bound,
  decomposition and interval, the norm range's top row, the Booleanities of `h`, `c` and the hint's
  flags, the ranges of `w'`, `z`, the hint's offset and slack, the hint weight) are carrier
  predicates `CarrierAEmbed.pred k` (`aSat`). The signature relation and the MAC are not held: the carrier
  reads the public key from the committed member and checks the relation at a random point, and its
  MAC's operands differ.

The compiler computes each renaming, the part's values and shared expressions and the predicate
pairs from the two programs, and exports them as the carrier's checked embedding data (C++
`lib/gordiehowe/compiler/embedding.h`); the classes read them from the data, with the predicate
correspondences and the layout facts the frontends read, decided per carrier.

The native program's domain `A` (over `F_q^6`) is not the carrier's (Goldilocks²), and the
native frontend's facts of domain `H` are stated over the native program, so the carrier is read
as two programs: the native one in domain `H` (`CarrierHEmbed`, `pullH`) and the emulated one in
domain `A` (`CarrierAEmbed`, `pullA`). Each class is decided per carrier.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

/-! ## Domain `H`: the native program's core -/

/-- **The native values the frontends read by their identifiers**: `w1` (`70`), `μ` (`120`), the
extracted challenge's `457`, the core's typed values. -/
def readValsH : List ℕ := [70, 120, 457, 556, 560, 561, 562, 563, 564, 565]

/-- **The native shared expressions the frontends read by their identifiers**: H's decoded
challenge's sign and support (`522 … 524`), which the carrier's crossing reads in its own operand. -/
def readExprsH : List ℕ := [522, 523, 524]

/-- **A carrier holds the native program's domain `H` core**: the embedding under its renaming `σ`
of the part's values `V` and shared expressions `R` (`RealizedProgram.Embedding`), each read from
the carrier's checked embedding data; native predicate `k` of the core (`48 … 270`) is carrier
predicate `pred k`, renamed and a source predicate; the values the core reads by their node types
(`GordieHowe.MLDSA44.hTypedCore`) are renamed to node-typed source values; the renamed challenges
have the native ones' phases, two later. Each carrier instantiates it from its data,
naming its native program (`nat`), and decides the facts about the data the frontends read: the
values and shared expressions they read by identifier are held (`readV`, `readR`), and `pred` is the
data's pairing of held predicates (`held`, `pred_held`). -/
class CarrierHEmbed (program : RealizedProgram) where
  /-- The native program. -/
  nat : RealizedProgram
  /-- The renaming. -/
  σ : RealizedProgram.Renaming
  /-- The part's values. -/
  V : List ℕ
  /-- The part's shared expressions. -/
  R : List ℕ
  /-- The carrier predicate of each held native predicate. -/
  pred : ℕ → ℕ
  /-- The embedding. -/
  embedding : nat.Embedding program σ V R
  /-- Native predicate `k` of domain `H`'s core is carrier predicate `pred k`. -/
  hPredCorr : ∀ k, corePredLo ≤ k → k ≤ hPredHi →
    nat.equalCorrB program σ V R (nat.predicate k).body
      (program.predicate (pred k)).body = true ∧
      pred k < program.predicates.length ∧ program.inSource (program.predicate (pred k)) = true
  /-- The core's typed values are renamed to node-typed source values. -/
  typedCorr : ∀ v ∈ MLDSA44.hTypedCore, v ∈ V ∧ σ.val v < program.values.length ∧
    program.IsSourceValue (σ.val v) ∧ (program.value (σ.val v)).typeSource = .node
  /-- The renamed challenges have the native ones' phases. -/
  chalPhase : ∀ j, (program.challenge (σ.chal j)).phase = (nat.challenge j).phase
  /-- The native challenge `j` is the carrier's `j + 2` (the carrier draws the member table's
  challenge and the signature relation's `r` first). -/
  chal2 : ∀ j, σ.chal j = j + 2
  /-- The values the frontends read by identifier are held. -/
  readV : ∀ v ∈ readValsH, v ∈ V
  /-- The shared expressions the frontends read by identifier are held. -/
  readR : ∀ k ∈ readExprsH, k ∈ R
  /-- The held pairs (native predicate, carrier predicate) of the data. -/
  held : List (ℕ × ℕ)
  /-- `pred` pairs each held native predicate with its carrier predicate. -/
  pred_held : ∀ p ∈ held, pred p.1 = p.2

/-! ## Domain `A`: the emulated program's gadgets -/

/-- **Domain `A`'s gadget predicates** of the emulated program: the hint's `w1` bound,
decomposition and interval (`0`, `1`, `2`), the norm range's top row (`5`), the Booleanities of
`h`, `c`, the hint's `w1` and nonpositive flags (`6 … 9`), the ranges of `w'`, `z`, the hint's
offset and slack (`11 … 14`), the hint weight (`15`). -/
def aPreds : List ℕ := [0, 1, 2, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]

/-- **Domain `A`'s gadget predicates whose carrier predicates are source predicates**: `aPreds`
without the norm range's top row (`5`, a realization). -/
def aSource : List ℕ := [0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15]

/-- **A carrier holds the emulated program's domain `A` gadgets**: the embedding under its renaming
`σ` of the part's values `V` and shared expressions `R` (`RealizedProgram.Embedding`), each read
from the carrier's checked embedding data; emulated predicate `k` of `aPreds` is carrier predicate
`pred k`, renamed (`RealizedProgram.bodyCorrB`), a source predicate for `k ∈ aSource`; the renamed
challenges have the emulated ones' phases, in order and distinct. Each carrier instantiates it
from its data, naming its emulated program (`emu`), and decides the facts about the data the
frontends read: the emulated `z`, `h`, `challenge.c`, `w′` and `hint.w1` are held (`readV`), and
`pred` is the data's pairing of held predicates (`held`, `pred_held`). Where the carrier reads the
held values is the carrier frontend's (`MldsaCarrierFront.valsA`). -/
class CarrierAEmbed (program : RealizedProgram) where
  /-- The emulated program. -/
  emu : RealizedProgram
  /-- The renaming. -/
  σ : RealizedProgram.Renaming
  /-- The part's values. -/
  V : List ℕ
  /-- The part's shared expressions. -/
  R : List ℕ
  /-- The carrier predicate of each held emulated predicate. -/
  pred : ℕ → ℕ
  /-- The embedding. -/
  embedding : emu.Embedding program σ V R
  /-- Emulated predicate `k` of domain `A`'s gadgets is carrier predicate `pred k`. -/
  aPredCorr : ∀ k ∈ aPreds,
    emu.bodyCorrB program σ V R (emu.predicate k).body
      (program.predicate (pred k)).body = true ∧ pred k < program.predicates.length
  /-- The carrier predicates of `aSource` are source predicates. -/
  aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (pred k)) = true
  /-- The renamed challenges have the emulated ones' phases. -/
  chalPhase : ∀ j, (program.challenge (σ.chal j)).phase = (emu.challenge j).phase
  /-- The challenge renaming keeps the order and is injective. -/
  chalStrict : StrictMono σ.chal
  /-- `z`, `h`, `challenge.c`, `w′` and `hint.w1` are held. -/
  readV : ∀ v ∈ [58, 59, 60, 61, 63], v ∈ V
  /-- The held pairs (emulated predicate, carrier predicate) of the data. -/
  held : List (ℕ × ℕ)
  /-- `pred` pairs each held emulated predicate with its carrier predicate. -/
  pred_held : ∀ p ∈ held, pred p.1 = p.2

set_option linter.unusedSectionVars false

/-! ## Transport of domain `H` -/

section H

variable {program : RealizedProgram} [CarrierHEmbed program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "σH" => CarrierHEmbed.σ program

set_option hygiene false in
local notation "hV" => CarrierHEmbed.V program

/-- **An environment of the carrier read as one of the native program** (through `σH`,
`RealizedProgram.pullEnv`). -/
abbrev pullH (e : program.Env I) : (nat).Env I := (nat).pullEnv σH hV e

/-- **The readers agree on `hV`**: a native value of the core, read in the environment read as the
native program's, is its renamed carrier value. -/
theorem readerH_pull (e : program.Env I) {v : ℕ} (hv : v ∈ hV) (i : ℕ) :
    (nat).reader (pullH e) v i = RealizedProgram.castElt (program.reader e ((σH).val v) i) :=
  RealizedProgram.reader_pullEnv CarrierHEmbed.embedding e hv i

/-- **Domain `H`'s core holds** in the environment read as the native program's, where the carrier
source program holds: native predicates `48 … 270`. -/
theorem hPreds_pull {e : program.Env I} (hs : program.SourceSatAt e) :
    ∀ k, corePredLo ≤ k → k ≤ hPredHi → (nat).HoldsAt (pullH e) ((nat).predicate k).body := by
  intro k h1 h2
  obtain ⟨hc, hl, hsrc⟩ := CarrierHEmbed.hPredCorr (program := program) k h1 h2
  exact (RealizedProgram.holdsAt_pullEnv CarrierHEmbed.embedding e hc).1
    (hs.preds _ (RealizedProgram.predicate_mem hl) hsrc)

/-- **Environments agreeing up to the carrier's challenge `(σH).chal j` agree, read as the native
program's, up to the native challenge `j`** (`RealizedProgram.Env.EqUpTo`). -/
theorem eqUpToH_pull {j : ℕ} {e₁ e₂ : program.Env I}
    (h : RealizedProgram.Env.EqUpTo ((σH).chal j) e₁ e₂) :
    RealizedProgram.Env.EqUpTo j (pullH e₁) (pullH e₂) :=
  RealizedProgram.eqUpTo_pullEnv CarrierHEmbed.embedding CarrierHEmbed.chalPhase
    (fun a b h => by rw [CarrierHEmbed.chal2, CarrierHEmbed.chal2]; omega) h

variable {F0 FH : RealizedProgram.FieldInterp}

/-- **The native frontend's domain `H` core holds** (`GordieHowe.MLDSA44.HSatCore`)
in the environment read as the native program's, where the carrier source program holds: the
predicates `48 … 270` (`hPreds_pull`) and the typed values `hTypedCore` in their node types. -/
theorem hSatCore {e : program.Env (RealizedProgram.mldsaInterpOf F0 FH)}
    (hs : program.SourceSatAt e) : MLDSA44.HSatCore (pullH e) where
  preds := hPreds_pull hs
  types v hv i hi := by
    obtain ⟨hvV, hl, hsrc, hts⟩ := CarrierHEmbed.typedCorr (program := program) v hv
    refine RealizedProgram.inType_pullEnv CarrierHEmbed.embedding e hvV
      (hs.types _ hl hsrc hts i ?_)
    rw [((CarrierHEmbed.embedding (program := program)).vals v hvV).2.2.2.1]
    exact hi

end H

/-! ## Transport of domain `A` -/

section A

variable {program : RealizedProgram} [CarrierAEmbed program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

set_option hygiene false in
local notation "σA" => CarrierAEmbed.σ program

set_option hygiene false in
local notation "aV" => CarrierAEmbed.V program

/-- **An environment of the carrier read as one of the emulated program** (through `σA`,
`RealizedProgram.pullEnv`). -/
abbrev pullA (e : program.Env I) : (emu).Env I := (emu).pullEnv σA aV e

/-- **The readers agree on `aV`**: an emulated value of the gadgets, read in the environment read
as the emulated program's, is its renamed carrier value. -/
theorem readerA_pull (e : program.Env I) {v : ℕ} (hv : v ∈ aV) (i : ℕ) :
    (emu).reader (pullA e) v i = RealizedProgram.castElt (program.reader e ((σA).val v) i) :=
  RealizedProgram.reader_pullEnv CarrierAEmbed.embedding e hv i

/-- **The integer readings agree on `aV`** (`RealizedProgram.intOf`): an emulated value of the
gadgets, read on the integers in the environment read as the emulated program's, is its renamed
carrier value's reading. -/
theorem intOfA_pull (e : program.Env I) {v : ℕ} (hv : v ∈ aV) (i : ℕ) :
    (emu).intOf ((emu).reader (pullA e)) v i = program.intOf (program.reader e) ((σA).val v) i :=
  (RealizedProgram.intOf_pullEnv CarrierAEmbed.embedding e hv i).symm

/-- **Domain `A`'s gadgets hold** in the environment read as the emulated program's, where the
carrier source program holds: the emulated predicates `aSource` (the hint's `w1` bound,
decomposition and interval, the Booleanities of `h`, `c` and the hint's flags, the ranges of `w'`,
`z`, the hint's offset and slack, the hint weight). -/
theorem aSat {e : program.Env I} (hs : program.SourceSatAt e) :
    ∀ k ∈ aSource, (emu).HoldsAt (pullA e) ((emu).predicate k).body := by
  intro k hk
  have hkA : k ∈ aPreds := (by decide : ∀ k ∈ aSource, k ∈ aPreds) k hk
  obtain ⟨hc, hl⟩ := CarrierAEmbed.aPredCorr (program := program) k hkA
  exact (RealizedProgram.holdsAt_pullEnv_body CarrierAEmbed.embedding e hc).1
    (hs.preds _ (RealizedProgram.predicate_mem hl) (CarrierAEmbed.aSourceCorr k hk))

/-- **Environments agreeing up to the carrier's challenge `(σA).chal j` agree, read as the emulated
program's, up to the emulated challenge `j`** (`RealizedProgram.Env.EqUpTo`). -/
theorem eqUpToA_pull {j : ℕ} {e₁ e₂ : program.Env I}
    (h : RealizedProgram.Env.EqUpTo ((σA).chal j) e₁ e₂) :
    RealizedProgram.Env.EqUpTo j (pullA e₁) (pullA e₂) :=
  RealizedProgram.eqUpTo_pullEnv CarrierAEmbed.embedding CarrierAEmbed.chalPhase
    CarrierAEmbed.chalStrict.monotone h

end A

end GordieHowe.MLDSA44.Ring.Carrier
