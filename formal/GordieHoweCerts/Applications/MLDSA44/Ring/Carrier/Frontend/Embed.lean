-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: an ML-DSA ring carrier holds the native core and the emulated gadgets

An ML-DSA-44 ring carrier (`MLDSA44.Ring.Carrier.ROMParams`, `MLDSA44.Ring.Carrier.QROMParams`;
C++ `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`) holds two parts of the ML-DSA-44
proof-of-possession programs at the same parameters, each up to a renaming of value,
shared-expression and challenge identifiers; the carrier's challenge `j + 1` is the proof of
possession's challenge `j` (the carrier draws the member table's challenge first).

* **Domain `H`'s core of the native program** (`MLDSA44.Native.ROMParams`,
  `MLDSA44.Native.QROMParams`; `lib/gordiehowe/examples/mldsa/mldsa_native.h`), under `σH`: native
  predicates `48 … 270` (the Keccak rounds of `c̃'`, SampleInBall's stream, the selection and the
  memory check) are carrier predicates `23 … 245`, renamed source predicates. The native `μ`
  (values `119`, `120`) is renamed to the carrier's committed `μ` (`mu.words`, `mu`, values `70`,
  `71`); the native part reading `μ` from `tr` and the message (predicates `18 … 47`) is not held.
  So the native frontend's core (`GordieHowe.MLDSA44.HSatCore`) holds in the
  carrier's environment read as the native program's (`hSatCore`).
* **Domain `A`'s gadgets of the emulated program** (`MLDSA44.Emulated.ROMParams`,
  `MLDSA44.Emulated.QROMParams`), under `σA`: emulated predicates `aPreds` (the hint's `w1` bound,
  decomposition and interval, the norm range's top row, the Booleanities of `h`, `c` and the hint's
  flags, the ranges of `w'`, `z`, the hint's offset and slack, the hint weight) are carrier
  predicates `predMapA k` (`aSat`). The signature relation and the MAC are not held: the carrier
  reads the public key from the committed member, and its MAC's operands differ.

The native program's domain `A` (over `F_q^6`) is not the carrier's (Goldilocks²), and the
native frontend's facts of domain `H` are stated over the native program, so the carrier is read
as two programs: the native one in domain `H` (`CarrierHEmbed`, `pullH`) and the emulated one in
domain `A` (`CarrierAEmbed`, `pullA`). Each class is decided per carrier.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

/-! ## Domain `H`: the native program's core -/

/-- **The native values' identifiers in the carrier**: the constants of domain `H` the core reads
(`6`, `9 … 33`, `35`, `36`, `40 … 54`) at the carrier's constants of equal entries, the native
`w1` (`69`, `70`) three larger, the native `μ` (`119`, `120`) as the carrier's committed `μ`
(`70`, `71`), the core's values from `121` on `47` smaller. Values the core does not read are left
in place. -/
def valH (v : ℕ) : ℕ :=
  if v = 6 then 8
  else if v < 9 then v
  else if v < 34 then v + 2
  else if v = 35 then 43
  else if v = 36 then 41
  else if v < 40 then v
  else if v = 40 then 10
  else if v < 46 then v - 5
  else if v = 46 then 42
  else if v < 55 then v - 3
  else if v < 69 then v
  else if v < 71 then v + 3
  else if v < 119 then v
  else if v < 121 then v - 49
  else v - 47

/-- **The renaming of domain `H`**: values by `valH`, shared expression `k` is `k − 20`, challenge
`j` is `j + 1`. -/
def σH : RealizedProgram.Renaming := ⟨valH, (· - 20), (· + 1)⟩

/-- **The native values of domain `H`'s core**: the constants `6`, `9 … 33`, `35`, `36`,
`40 … 54`, the native `w1` (`69`, `70`), `μ` (`119`, `120`) and the core's values `121 … 566`. -/
def hV : List ℕ :=
  [6] ++ List.range' 9 25 ++ [35, 36] ++ List.range' 40 15 ++ [69, 70] ++ List.range' 119 448

/-- **The native shared expressions of domain `H`'s core**: `66 … 524` (`522 … 524` H's decoded
challenge's sign and support, which the carrier's crossing reads in its own operand). -/
def hR : List ℕ := List.range' 66 459

/-- **A carrier holds the native program's domain `H` core**: the embedding under `σH`
(`RealizedProgram.Embedding`); native predicate `k` of the core (`48 … 270`) is carrier predicate
`k − 25`, renamed and a source predicate; the values the core reads by their node types
(`GordieHowe.MLDSA44.hTypedCore`) are renamed to node-typed source values; the
renamed challenges have the native ones' phases. Each carrier instantiates it by `decide`, naming
its native program (`nat`). -/
class CarrierHEmbed (program : RealizedProgram) where
  /-- The native program. -/
  nat : RealizedProgram
  /-- The embedding. -/
  embedding : nat.Embedding program σH hV hR
  /-- Native predicate `k` of domain `H`'s core is carrier predicate `k − 25`. -/
  hPredCorr : ∀ k, 48 ≤ k → k ≤ 270 →
    nat.equalCorrB program σH hV hR (nat.predicate k).body
      (program.predicate (k - 25)).body = true ∧
      k - 25 < program.predicates.length ∧ program.inSource (program.predicate (k - 25)) = true
  /-- The core's typed values are renamed to node-typed source values. -/
  typedCorr : ∀ v ∈ MLDSA44.hTypedCore, v ∈ hV ∧ σH.val v < program.values.length ∧
    program.IsSourceValue (σH.val v) ∧ (program.value (σH.val v)).typeSource = .node
  /-- The renamed challenges have the native ones' phases. -/
  chalPhase : ∀ j, (program.challenge (σH.chal j)).phase = (nat.challenge j).phase

/-! ## Domain `A`: the emulated program's gadgets -/

/-- **The emulated values' identifiers in the carrier**: the constants `0 … 6` at the carrier's
constants of equal entries (`2, 3, 4, 1, 5, 6, 7`), `z`, `h`, `c` and `w'` (`58 … 61`) two
larger, `z`'s offset (`62`) at `65`, the hint's values (`63 … 66`) three larger, the range digits
from `577` on `47` smaller. Values the gadgets do not read are left in place. -/
def valA (v : ℕ) : ℕ :=
  if v < 7 then [2, 3, 4, 1, 5, 6, 7].getD v v
  else if v < 58 then v
  else if v < 62 then v + 2
  else if v = 62 then 65
  else if v < 67 then v + 3
  else if v < 577 then v
  else v - 47

/-- **The emulated shared expressions' identifiers in the carrier**: `0 … 5` (UseHint's) `30`
larger, the others (the norm range's top row `10`, the hint weight's complement `11`) `33` larger. -/
def refA (k : ℕ) : ℕ := if k < 6 then k + 30 else k + 33

/-- **The renaming of domain `A`**: values by `valA`, shared expressions by `refA`, challenge `j`
is `j + 1`. -/
def σA : RealizedProgram.Renaming := ⟨valA, refA, (· + 1)⟩

/-- **The emulated values of domain `A`'s gadgets**: the constants `0 … 6`, `z`, `h`, `c`, `w'`,
`z`'s offset and the hint's values (`58 … 66`), and the range digits and top rows
(`577 … 589`). -/
def aV : List ℕ := List.range' 0 7 ++ List.range' 58 9 ++ List.range' 577 13

/-- **The emulated shared expressions of domain `A`'s gadgets**: UseHint's `0 … 5`, the norm
range's top row `10` and the hint weight's complement `11`. -/
def aR : List ℕ := [0, 1, 2, 3, 4, 5, 10, 11]

/-- **The emulated predicates' identifiers in the carrier**: `0`, `1` one larger, `2` two larger,
`5` one larger, `6 …` three larger. -/
def predMapA (k : ℕ) : ℕ := if k < 2 then k + 1 else if k < 5 then k + 2 else if k < 6 then k + 1
  else k + 3

/-- **Domain `A`'s gadget predicates** of the emulated program: the hint's `w1` bound,
decomposition and interval (`0`, `1`, `2`), the norm range's top row (`5`), the Booleanities of
`h`, `c`, the hint's `w1` and nonpositive flags (`6 … 9`), the ranges of `w'`, `z`, the hint's
offset and slack (`11 … 14`), the hint weight (`15`). -/
def aPreds : List ℕ := [0, 1, 2, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15]

/-- **Domain `A`'s gadget predicates whose carrier predicates are source predicates**: `aPreds`
without the norm range's top row (`5`, a realization). -/
def aSource : List ℕ := [0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15]

/-- **A carrier holds the emulated program's domain `A` gadgets**: the embedding under `σA`
(`RealizedProgram.Embedding`); emulated predicate `k` of `aPreds` is carrier predicate
`predMapA k`, renamed (`RealizedProgram.bodyCorrB`), a source predicate for `k ∈ aSource`; the
renamed challenges have the emulated ones' phases. Each carrier instantiates it by `decide`,
naming its emulated program (`emu`). -/
class CarrierAEmbed (program : RealizedProgram) where
  /-- The emulated program. -/
  emu : RealizedProgram
  /-- The embedding. -/
  embedding : emu.Embedding program σA aV aR
  /-- Emulated predicate `k` of domain `A`'s gadgets is carrier predicate `predMapA k`. -/
  aPredCorr : ∀ k ∈ aPreds,
    emu.bodyCorrB program σA aV aR (emu.predicate k).body
      (program.predicate (predMapA k)).body = true ∧ predMapA k < program.predicates.length
  /-- The carrier predicates of `aSource` are source predicates. -/
  aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predMapA k)) = true
  /-- The renamed challenges have the emulated ones' phases. -/
  chalPhase : ∀ j, (program.challenge (σA.chal j)).phase = (emu.challenge j).phase

set_option linter.unusedSectionVars false

/-- The challenge renaming of domain `H` keeps the order. -/
theorem σH_chal_mono : Monotone σH.chal := fun _ _ h => Nat.add_le_add_right h 1

/-- The challenge renaming of domain `A` keeps the order. -/
theorem σA_chal_mono : Monotone σA.chal := fun _ _ h => Nat.add_le_add_right h 1

/-! ## Transport of domain `H` -/

section H

variable {program : RealizedProgram} [CarrierHEmbed program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

/-- **An environment of the carrier read as one of the native program** (through `σH`,
`RealizedProgram.pullEnv`). -/
abbrev pullH (e : program.Env I) : (nat).Env I := (nat).pullEnv σH hV e

/-- **The readers agree on `hV`**: a native value of the core, read in the environment read as the
native program's, is its renamed carrier value. -/
theorem readerH_pull (e : program.Env I) {v : ℕ} (hv : v ∈ hV) (i : ℕ) :
    (nat).reader (pullH e) v i = RealizedProgram.castElt (program.reader e (σH.val v) i) :=
  RealizedProgram.reader_pullEnv CarrierHEmbed.embedding e hv i

/-- **Domain `H`'s core holds** in the environment read as the native program's, where the carrier
source program holds: native predicates `48 … 270`. -/
theorem hPreds_pull {e : program.Env I} (hs : program.SourceSatAt e) :
    ∀ k, 48 ≤ k → k ≤ 270 → (nat).HoldsAt (pullH e) ((nat).predicate k).body := by
  intro k h1 h2
  obtain ⟨hc, hl, hsrc⟩ := CarrierHEmbed.hPredCorr (program := program) k h1 h2
  exact (RealizedProgram.holdsAt_pullEnv CarrierHEmbed.embedding e hc).1
    (hs.preds _ (RealizedProgram.predicate_mem hl) hsrc)

/-- **Environments agreeing up to the carrier's challenge `σH.chal j` agree, read as the native
program's, up to the native challenge `j`** (`RealizedProgram.Env.EqUpTo`). -/
theorem eqUpToH_pull {j : ℕ} {e₁ e₂ : program.Env I}
    (h : RealizedProgram.Env.EqUpTo (σH.chal j) e₁ e₂) :
    RealizedProgram.Env.EqUpTo j (pullH e₁) (pullH e₂) :=
  RealizedProgram.eqUpTo_pullEnv CarrierHEmbed.embedding CarrierHEmbed.chalPhase σH_chal_mono h

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

/-- **An environment of the carrier read as one of the emulated program** (through `σA`,
`RealizedProgram.pullEnv`). -/
abbrev pullA (e : program.Env I) : (emu).Env I := (emu).pullEnv σA aV e

/-- **The readers agree on `aV`**: an emulated value of the gadgets, read in the environment read
as the emulated program's, is its renamed carrier value. -/
theorem readerA_pull (e : program.Env I) {v : ℕ} (hv : v ∈ aV) (i : ℕ) :
    (emu).reader (pullA e) v i = RealizedProgram.castElt (program.reader e (σA.val v) i) :=
  RealizedProgram.reader_pullEnv CarrierAEmbed.embedding e hv i

/-- **The integer readings agree on `aV`** (`RealizedProgram.intOf`): an emulated value of the
gadgets, read on the integers in the environment read as the emulated program's, is its renamed
carrier value's reading. -/
theorem intOfA_pull (e : program.Env I) {v : ℕ} (hv : v ∈ aV) (i : ℕ) :
    (emu).intOf ((emu).reader (pullA e)) v i = program.intOf (program.reader e) (σA.val v) i :=
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

/-- **Environments agreeing up to the carrier's challenge `σA.chal j` agree, read as the emulated
program's, up to the emulated challenge `j`** (`RealizedProgram.Env.EqUpTo`). -/
theorem eqUpToA_pull {j : ℕ} {e₁ e₂ : program.Env I}
    (h : RealizedProgram.Env.EqUpTo (σA.chal j) e₁ e₂) :
    RealizedProgram.Env.EqUpTo j (pullA e₁) (pullA e₂) :=
  RealizedProgram.eqUpTo_pullEnv CarrierAEmbed.embedding CarrierAEmbed.chalPhase σA_chal_mono h

end A

end GordieHowe.MLDSA44.Ring.Carrier
