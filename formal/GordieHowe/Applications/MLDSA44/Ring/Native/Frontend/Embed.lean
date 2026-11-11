-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHowe.Applications.MLDSA44.EmbedFacts

@[expose] public section

/-!
# GordieHowe frontend: a native ML-DSA ring program holds the native ML-DSA program's core

A native ML-DSA-44 ring program (`MLDSA44.Ring.Native.ROMParams`, `MLDSA44.Ring.Native.QROMParams`;
C++ `lib/gordiehowe/examples/rings/mldsa_ring_native.h`) holds two parts of the native ML-DSA-44
program at the same parameters (`MLDSA44.Native.ROMParams`, `MLDSA44.Native.QROMParams`;
`lib/gordiehowe/examples/mldsa/mldsa_native.h`) up to a renaming: its values, shared
expressions and challenges are numbered differently, and the ring program's challenge `j + 2` is
the native program's challenge `j` (the ring draws the member table's challenge and the signature
relation's `r` first).

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

The compiler computes the renaming, the part's values and shared expressions (those the two parts
and the frontends read, closed under what they read) and the predicate pairs from the two programs,
and exports them as each ring program's checked embedding data (C++
`lib/gordiehowe/compiler/embedding.h`); `MldsaRingEmbed` reads them from the data, with the
predicate correspondences and the layout facts the frontends read, decided per pair of programs. Through `RealizedProgram.pullEnv` the ring program's source predicates give the
native program's predicates of both parts (`hPreds_pull`, `aSat`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

/-- **The native values the frontends read by their identifiers**: domain `A`'s `57 … 65`, `w1`
(`70`), `μ` (`120`), the extracted challenge's `457` and SampleInBall's cells. Each ring program's
part holds them (`MldsaRingEmbed.readV`). -/
def readVals : List ℕ :=
  [57, 58, 59, 60, 61, 62, 63, 64, 65, 70, 120, 457, 556, 557, 560, 561, 562, 563, 564, 565]

/-- **The native shared expressions the frontends read by their identifiers**: H's decoded
challenge's sign and support (`522 … 524`), which the ring's crossing reads in its own operand. -/
def readExprs : List ℕ := [522, 523, 524]

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
embedding under its renaming `σ` of the part's values `V` and shared expressions `R`
(`RealizedProgram.Embedding`), each read from the program's checked embedding data; native
predicate `k` of domain `H`'s core is ring predicate `pred k`, renamed and a source predicate;
native predicate `k` of `aPreds` is ring predicate `pred k`, renamed
(`RealizedProgram.bodyCorrB`), a source predicate for `k ∈ aSource`; the renamed challenges have
the native ones' phases, in order. Each ring program instantiates it from its data, naming its
native program (`nat`), and decides the facts about the data the frontends read: the values and
shared expressions they read by identifier are held (`readV`, `readR`), and `pred` is the data's
pairing of held predicates (`held`, `pred_held`). -/
class MldsaRingEmbed (program : RealizedProgram) where
  /-- The native program. -/
  nat : RealizedProgram
  /-- The renaming. -/
  σ : RealizedProgram.Renaming
  /-- The part's values. -/
  V : List ℕ
  /-- The part's shared expressions. -/
  R : List ℕ
  /-- The ring predicate of each held native predicate. -/
  pred : ℕ → ℕ
  /-- The embedding. -/
  embedding : nat.Embedding program σ V R
  /-- Native predicate `k` of domain `H`'s core is ring predicate `pred k`. -/
  hPredCorr : ∀ k, corePredLo ≤ k → k ≤ hPredHi →
    nat.equalCorrB program σ V R (nat.predicate k).body
      (program.predicate (pred k)).body = true ∧
      pred k < program.predicates.length ∧ program.inSource (program.predicate (pred k)) = true
  /-- Native predicate `k` of domain `A`'s gadgets is ring predicate `pred k`. -/
  aPredCorr : ∀ k ∈ aPreds,
    nat.bodyCorrB program σ V R (nat.predicate k).body
      (program.predicate (pred k)).body = true ∧ pred k < program.predicates.length
  /-- The ring predicates of `aSource` are source predicates. -/
  aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (pred k)) = true
  /-- The renamed challenges have the native ones' phases. -/
  chalPhase : ∀ j, (program.challenge (σ.chal j)).phase = (nat.challenge j).phase
  /-- The challenge renaming keeps the order. -/
  chalMono : Monotone σ.chal
  /-- The values the frontends read by identifier are held. -/
  readV : ∀ v ∈ readVals, v ∈ V
  /-- The shared expressions the frontends read by identifier are held. -/
  readR : ∀ k ∈ readExprs, k ∈ R
  /-- The held pairs (native predicate, ring predicate) of the data. -/
  held : List (ℕ × ℕ)
  /-- `pred` pairs each held native predicate with its ring predicate. -/
  pred_held : ∀ p ∈ held, pred p.1 = p.2

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingEmbed program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

set_option hygiene false in
local notation "ringV" => MldsaRingEmbed.V program

set_option hygiene false in
local notation "predMap" => MldsaRingEmbed.pred program

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
    ∀ k, corePredLo ≤ k → k ≤ hPredHi → (nat).HoldsAt (pull e) ((nat).predicate k).body := by
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
