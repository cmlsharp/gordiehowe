-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed

@[expose] public section

/-!
# GordieHowe frontend: a native ML-DSA ring program holds the native ML-DSA program's core

A native ML-DSA-44 ring program (`MLDSA44.Ring.Native.ROMParams`, `MLDSA44.Ring.Native.QROMParams`;
C++ `lib/gordiehowe/examples/rings/mldsa_ring_native.h`) holds two parts of the native ML-DSA-44
program at the same parameters (`MLDSA44.Native.ROMParams`, `MLDSA44.Native.QROMParams`;
`lib/gordiehowe/examples/mldsa/mldsa_native.h`) up to a renaming (`σR`, `σQ`): its values, shared
expressions and challenges are numbered differently, and the ring program's challenge `j + 1` is
the native program's challenge `j` (the ring draws the member table's challenge first).

* **Domain `H`'s core** (native predicates `48 … 270`: the Keccak rounds of `c̃'`, SampleInBall's
  stream, the selection and the memory check) is ring predicates `24 … 246`. The native program's
  part reading `μ` from `tr` and the message (predicates `18 … 47`) is not held: the ring program
  commits `μ` (`mu.words`, `mu`) in domain `H`, and the native `μ` (values `119`, `120`) is renamed
  to it. The MAC crossing is not held (its operands differ).
* **Domain `A`'s gadgets** (native predicates `1, 2, 3, 5, 6 … 14`: the hint's `w1` bound,
  decomposition and interval, the norm range's top row, the Booleanities, the norm of `z`, the
  hint's offset and slack, the hint weight) are ring predicates `5, 6, 7, 9, 12 … 20`. The relation
  `signature.relation` is not held (the ring program reads the public key from the committed
  member).

The values `ringV` and shared expressions `ringR` are those the two parts read, closed under what
they read; `MldsaRingEmbed` collects the embedding and the predicate correspondences, decided per
pair of programs. Through `RealizedProgram.pullEnv` the ring program's source predicates give the
native program's predicates of both parts (`hPreds_pull`, `aSat`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

/-- **The native values' identifiers in the ring program at the ROM parameters**: the constants,
domain `A`'s values `57 … 65` three larger, domain `H`'s `w1` (`69`, `70`) two larger, `μ`
(`119`, `120`) as the ring's committed `μ` (`69`, `70`), domain `H`'s values `121 … 574` and the
range digits `575 … 587` shifted down. Values the parts do not read are left in place. -/
def valR (v : ℕ) : ℕ :=
  if v < 10 then [6, 3, 4, 5, 1, 7, 8, 9, 8, 11].getD v v
  else if v < 34 then v + 2
  else if v < 47 then [34, 43, 41, 37, 38, 39, 10, 36, 37, 38, 39, 40, 42].getD (v - 34) v
  else if v < 55 then v - 3
  else if v < 57 then v
  else if v < 66 then v + 3
  else if v < 69 then v
  else if v < 71 then v + 2
  else if v < 119 then v
  else if v < 121 then v - 50
  else if v < 575 then v - 48
  else v - 46

/-- **The native values' identifiers in the ring program at the QROM parameters**: those at the
ROM parameters, every identifier from `10` one smaller (the ROM program's constant `9` is merged
into an earlier constant). -/
def valQ (v : ℕ) : ℕ := if 10 ≤ valR v then valR v - 1 else valR v

/-- **The native shared expressions' identifiers in the ring program**: `2 … 8` (domain `A`) are
`43` larger, `66 …` (domain `H`) `12` smaller. -/
def refMap (k : ℕ) : ℕ := if k < 66 then k + 43 else k - 12

/-- **The renaming at the ROM parameters**: values by `valR`, shared expressions by `refMap`,
challenge `j` is `j + 1`. -/
def σR : RealizedProgram.Renaming := ⟨valR, refMap, (· + 1)⟩

/-- **The renaming at the QROM parameters**: values by `valQ`, shared expressions by `refMap`,
challenge `j` is `j + 1`. -/
def σQ : RealizedProgram.Renaming := ⟨valQ, refMap, (· + 1)⟩

/-- **The native values of the two parts**: the constants `0 … 6`, `9 … 33`, `35`, `36`,
`40 … 54`, domain `A`'s values `57 … 65`, domain `H`'s `w1` (`69`, `70`), `μ` and the core's values
(`119 … 566`), the MAC's blind (`567`) and the range digits and top row (`575 … 583`). -/
def ringV : List ℕ :=
  List.range' 0 7 ++ List.range' 9 25 ++ [35, 36] ++ List.range' 40 15 ++ List.range' 57 9 ++
    [69, 70] ++ List.range' 119 449 ++ List.range' 575 9

/-- **The native shared expressions of the two parts**: domain `A`'s `2 … 6` and `8`, domain `H`'s
`66 … 524` (`522 … 524` H's decoded challenge's sign and support, which the ring's crossing reads
in its own operand). -/
def ringR : List ℕ := List.range' 2 5 ++ [8] ++ List.range' 66 459

/-- **The native predicates' identifiers in the ring program**: `1 … 5` four larger, `6 … 14` six
larger, domain `H`'s core `24` smaller. -/
def predMap (k : ℕ) : ℕ := if k ≤ 5 then k + 4 else if k ≤ 14 then k + 6 else k - 24

/-- **Domain `A`'s gadget predicates** of the native program: the hint's `w1` bound, decomposition
and interval (`1`, `2`, `3`), the norm range's top row (`5`), the Booleanities of `h`, `c`, the
hint's `w1` and nonpositive flags and the MAC's blind (`6 … 10`), the norm of `z`, the hint's
offset and slack and the hint weight (`11 … 14`). -/
def aPreds : List ℕ := [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- **Domain `A`'s gadget predicates whose ring predicates are source predicates**: `aPreds`
without the norm range's top row (`5`, a realization) and the MAC blind's Booleanity (`10`, the type
check of a realization value). -/
def aSource : List ℕ := [1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14]

/-- **A ring program holds the native program's domain `H` core and domain `A` gadgets**: the
embedding under its renaming `σ` (`RealizedProgram.Embedding`); native predicate `k` of domain
`H`'s core is ring predicate `k − 24`, renamed and a source predicate; native predicate `k` of
`aPreds` is ring predicate `predMap k`, renamed (`RealizedProgram.bodyCorrB`), a source predicate
for `k ∈ aSource`; the renamed challenges have the native ones' phases, in order. Each ring program
instantiates it by `decide`, naming its native program (`nat`). -/
class MldsaRingEmbed (program : RealizedProgram) where
  /-- The native program. -/
  nat : RealizedProgram
  /-- The renaming. -/
  σ : RealizedProgram.Renaming
  /-- The embedding. -/
  embedding : nat.Embedding program σ ringV ringR
  /-- Native predicate `k` of domain `H`'s core is ring predicate `k − 24`. -/
  hPredCorr : ∀ k, 48 ≤ k → k ≤ 270 →
    nat.equalCorrB program σ ringV ringR (nat.predicate k).body
      (program.predicate (k - 24)).body = true ∧
      k - 24 < program.predicates.length ∧ program.inSource (program.predicate (k - 24)) = true
  /-- Native predicate `k` of domain `A`'s gadgets is ring predicate `predMap k`. -/
  aPredCorr : ∀ k ∈ aPreds,
    nat.bodyCorrB program σ ringV ringR (nat.predicate k).body
      (program.predicate (predMap k)).body = true ∧ predMap k < program.predicates.length
  /-- The ring predicates of `aSource` are source predicates. -/
  aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predMap k)) = true
  /-- The renamed challenges have the native ones' phases. -/
  chalPhase : ∀ j, (program.challenge (σ.chal j)).phase = (nat.challenge j).phase
  /-- The challenge renaming keeps the order. -/
  chalMono : Monotone σ.chal

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingEmbed program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

/-- **An environment of the ring program read as one of the native program** (through `σ`,
`RealizedProgram.pullEnv`). -/
abbrev pull (e : program.Env I) : (nat).Env I := (nat).pullEnv σ ringV e

/-- **The readers agree on `ringV`**: a native value of the parts, read in the environment read as
the native program's, is its renamed ring value. -/
theorem reader_pull (e : program.Env I) {v : ℕ} (hv : v ∈ ringV) (i : ℕ) :
    (nat).reader (pull e) v i = RealizedProgram.castElt (program.reader e ((σ).val v) i) :=
  RealizedProgram.reader_pullEnv MldsaRingEmbed.embedding e hv i

/-- **Domain `H`'s core holds** in the environment read as the native program's, where the ring
source program holds: native predicates `48 … 270`. -/
theorem hPreds_pull {e : program.Env I} (hs : program.SourceSatAt e) :
    ∀ k, 48 ≤ k → k ≤ 270 → (nat).HoldsAt (pull e) ((nat).predicate k).body := by
  intro k h1 h2
  obtain ⟨hc, hl, hsrc⟩ := MldsaRingEmbed.hPredCorr (program := program) k h1 h2
  exact (RealizedProgram.holdsAt_pullEnv MldsaRingEmbed.embedding e hc).1
    (hs.preds _ (RealizedProgram.predicate_mem hl) hsrc)

/-- **Domain `A`'s gadgets hold** in the environment read as the native program's, where the ring
source program holds: the native predicates `aSource` (the hint's `w1` bound, decomposition and
interval, the Booleanities of `h`, `c` and the hint's flags, the norm of `z`, the hint's offset
and slack, the hint weight). -/
theorem aSat {e : program.Env I} (hs : program.SourceSatAt e) :
    ∀ k ∈ aSource, (nat).HoldsAt (pull e) ((nat).predicate k).body := by
  intro k hk
  have hkA : k ∈ aPreds := (by decide : ∀ k ∈ aSource, k ∈ aPreds) k hk
  obtain ⟨hc, hl⟩ := MldsaRingEmbed.aPredCorr (program := program) k hkA
  exact (RealizedProgram.holdsAt_pullEnv_body MldsaRingEmbed.embedding e hc).1
    (hs.preds _ (RealizedProgram.predicate_mem hl) (MldsaRingEmbed.aSourceCorr k hk))

/-- **Environments agreeing up to the ring program's challenge `σ.chal j` agree, read as the
native program's, up to the native challenge `j`** (`RealizedProgram.Env.EqUpTo`). -/
theorem eqUpTo_pull {j : ℕ} {e₁ e₂ : program.Env I}
    (h : RealizedProgram.Env.EqUpTo ((σ).chal j) e₁ e₂) :
    RealizedProgram.Env.EqUpTo j (pull e₁) (pull e₂) :=
  RealizedProgram.eqUpTo_pullEnv MldsaRingEmbed.embedding MldsaRingEmbed.chalPhase
    MldsaRingEmbed.chalMono h

end GordieHowe.MLDSA44.Ring.Native
