-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Statement
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Relation
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Ring.Table
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Algebra

@[expose] public section

/-!
# GordieHowe frontend: the readings of the ML-DSA-44 ring carriers

The facts of an ML-DSA-44 ring carrier (`lib/gordiehowe/examples/rings/mldsa_ring.h`,
`mldsa_ring_carrier.h`) its frontend's composition reads, beyond the two embeddings of the proofs
of possession's parts (`CarrierHEmbed`, `CarrierAEmbed`), the signature relation
(`MldsaCarrierRelation`), the statement values (`Native.MldsaRingStmt`) and the public table's
selection (`GordieHowe.RealizedProgram.TableSelect`):

* **The program facts** (`MldsaCarrierFront`, decided per carrier): the table's shape (the record,
  shared expression `1`: `member.a_hat ‖ member.t1 ‖` the `24` limbs of the zero-extended `μ` bits,
  shared expression `0`; the row map `carrierMap`); `member.mu.boolean` (predicate `7`); the
  crossing `mac.equal` (predicate `247`, `cross(H, x, A, y)` with `x` the shared expression `505`,
  H's `μ ‖ w1 ‖` the decoded challenge's support and sign alternately, and `y` the shared
  expression `42`, A's `member.mu ‖ hint.w1 ‖ challenge.c`); domain `H`'s `μ` and `w1` bit views;
  the challenges (the carrier's challenge `j + 1` is the native program's `j`); the values the
  extractor reads.
* **The native readers of domain `H` at the carrier's environment** (`evalE_pullH`, `muBits_pull`,
  `w1HBits_pull`, `supH_pull`, `sgnH_pull`): the native frontend's readers in the environment read
  as the native program's are the carrier's readers at the renamed values: H's `μ` (value `71`),
  `w1` (value `73`), the decoded support and sign (shared expressions `503`, `504`).
* **The emulated readers of domain `A` at the carrier's environment** (`evalE_pullA`, `zOf_pullA`,
  `wOf_pullA`, `cBits_pullA`, `cPolyA_pullA`, `w1ABits_pullA`, `hVals_pullA`): the emulated
  frontend's readers in the environment read as the emulated program's are the carrier's (`z`
  value `60`, `h` `61`, `challenge.c` `62`, `w′` `63`, `hint.w1` `66`).
* **Domain `A`'s gadgets** (`eaSat`): the emulated frontend's `EASat` in that environment, where
  the carrier's source program holds.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt)

/-- **The program facts of an ML-DSA-44 ring carrier's frontend** (decided per carrier; the
identifiers are those of both carriers): the table's shape (the record, shared expression `1`, the
column blocks `ring.keys`, `ring.mu`, the row map `carrierMap`, `64` rows and `6` index bits, the
challenge `0`); the record's expressions (`0`: the `512` `μ` bits of `member.mu`, value `57`, and
`15` zeros; `1`: `member.a_hat ‖ member.t1 ‖` the `24` limbs `fromDigits 22 2`);
`member.mu.boolean` (predicate `7`); the crossing `mac.equal` (predicate `247`) of the shared
expressions `505` and `42`, their parts and index maps, the sign part `504` the shared expression
`502`; H's `μ` (`71`) and `w1` (`73`) bit views; the challenges and the values the extractor reads
(`c̃'`, value `410`; `z`, `60`; `h`, `61`). -/
class MldsaCarrierFront (program : RealizedProgram) [CarrierHEmbed program]
    [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program] : Prop where
  /-- The table's shape. -/
  shape : (TableSelect.shape program).dom = 0 ∧ (TableSelect.shape program).chal = 0 ∧
    (TableSelect.shape program).mOne = 18446744069414584320 ∧
    (TableSelect.shape program).zero = 0 ∧ (TableSelect.shape program).record = .ref 1 ∧
    (TableSelect.shape program).parts =
      [(MldsaRingStmt.keys program, 5120), (MldsaRingStmt.mu program, 24)] ∧
    (TableSelect.shape program).map = carrierMap ∧ (TableSelect.shape program).rows = 64 ∧
    (TableSelect.shape program).bits = 6
  /-- Domain `A` is field `0`, domain `H` field `1`. -/
  domains : program.domainField 0 = 0 ∧ program.domainField 1 = 1
  /-- The program has the shared expressions `0 … 505`. -/
  lt505 : 505 < program.exprs.length
  /-- Shared expression `0`: the `μ` bits and `15` zeros. -/
  expr0 : program.expr 0 = .reindex [(0, 1, 513), (512, 0, 15)] (.concat (.leaf 57) (.leaf 0))
  /-- Shared expression `1`: the record. -/
  expr1 : program.expr 1 = .reindex [(0, 1, 5144)]
    (.concat (.reindex [(0, 1, 5120)] (.concat (.reindex [(0, 1, 4096)] (.leaf 55))
      (.reindex [(0, 1, 1024)] (.leaf 56))))
      (.reindex [(0, 1, 24)] (.apply (.batched 24 (.fromDigits 22 2)) (.ref 0))))
  /-- `member.mu` has `512` coordinates. -/
  muSize : (program.value 57).size = 512
  /-- `member.mu.boolean` checks the `μ` bits, a source predicate. -/
  muBool : (program.predicate 7).body.boolCheck? = some ⟨0, 57⟩ ∧
    7 < program.predicates.length ∧ program.inSource (program.predicate 7) = true
  /-- `mac.equal` crosses `505` of domain `H` and `42` of domain `A`, a source predicate. -/
  cross : 247 < program.predicates.length ∧ program.inSource (program.predicate 247) = true ∧
    ∃ c, (program.predicate 247).body = .cross 1 (.ref 505) 0 (.ref 42) {} c
  /-- The crossing's `x`: H's `μ`, `w1`, then the decoded support and sign alternately. -/
  exprH : ∃ m : IndexMap, program.expr 505 = .reindex m (concatR (.leaf 71)
      [.leaf 73, .ref 503, .ref 504]) ∧
    (∀ t < 6656, m.entry t = t) ∧ (∀ k < 256, m.entry (6656 + 2 * k) = 6656 + k) ∧
    (∀ k < 256, m.entry (6656 + (2 * k + 1)) = 6912 + k)
  /-- The crossing's sign part is the decoded sign. -/
  expr504 : program.expr 504 = .ref 502
  /-- The crossing's `y`: A's `μ`, `w1` and challenge bits, in order. -/
  exprA : ∃ m : IndexMap, program.expr 42 = .reindex m (concatR (.leaf 57)
      [.leaf 66, .leaf 62]) ∧ ∀ t < 7168, m.entry t = t
  /-- The crossing's lengths. -/
  lens : program.exprLen (.ref 505) = 7168 ∧ (program.value 71).size = 512 ∧
    (program.value 73).size = 6144 ∧ program.exprLen (.ref 503) = 256 ∧
    program.exprLen (.ref 504) = 256 ∧ (program.value 66).size = 6144
  /-- Domain `H`'s `μ` and `w1` are bit views. -/
  bitViews : program.isBitView 71 = true ∧ program.isBitView 73 = true
  /-- The table's challenge `0` is a source challenge. -/
  chal0 : program.IsSourceChal 0
  /-- The carrier's source challenge `j + 1` is the native source challenge `j`. -/
  chalIff : ∀ j, program.IsSourceChal (j + 1) ↔ (CarrierHEmbed.nat program).IsSourceChal j
  /-- The native source challenges and their carrier challenges: one coordinate drawn from the
  same field. -/
  chalShape : ∀ j, (CarrierHEmbed.nat program).IsSourceChal j →
    (program.challenge (j + 1)).size = 1 ∧ (program.challenge (j + 1)).sampler = .full ∧
    ((CarrierHEmbed.nat program).challenge j).size = 1 ∧
    ((CarrierHEmbed.nat program).challenge j).sampler = .full ∧
    program.chalField (j + 1) = (CarrierHEmbed.nat program).chalField j
  /-- The values the extractor reads (`c̃'`, `z`, `h`) read nothing from the run. -/
  projReads : ∀ v ∈ [410, 60, 61], program.nodeReads program.fuel v = []

set_option linter.unusedSectionVars false

/-! ## The renamings' identifiers -/

/-- The renamed native `μ` is the carrier's `μ` (value `71`). -/
theorem σH_val120 : σH.val 120 = 71 := by decide

/-- The renamed native `w1` is the carrier's `w1` (value `73`). -/
theorem σH_val70 : σH.val 70 = 73 := by decide

/-- The renamed native `c̃'` is the carrier's value `410`. -/
theorem σH_val457 : σH.val 457 = 410 := by decide

/-- The renamed native decoded support is the carrier's shared expression `503`. -/
theorem σH_ref523 : σH.ref 523 = 503 := rfl

/-- The renamed native decoded sign is the carrier's shared expression `502`. -/
theorem σH_ref522 : σH.ref 522 = 502 := rfl

/-- The renamed emulated `z`, `h`, `challenge.c`, `w′` and `hint.w1` are the carrier's values
`60`, `61`, `62`, `63` and `66`. -/
theorem σA_vals : σA.val 58 = 60 ∧ σA.val 59 = 61 ∧ σA.val 60 = 62 ∧ σA.val 61 = 63 ∧
    σA.val 63 = 66 := by decide

/-! ## The native readers of domain `H` -/

section PullH

variable {program : RealizedProgram} [CarrierHEmbed program] [MldsaCarrierRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaCarrierFront program]
  {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

/-- **A native value of domain `H`'s core, read in the environment read as the native
program's**, is the carrier's renamed value. -/
theorem evalE_pullH (e : program.Env interp) {f v : ℕ} (hv : v ∈ hV) (i : ℕ) :
    (nat).evalE ((nat).reader (pullH e)) f (.leaf v) i =
      program.evalE (program.reader e) f (.leaf (σH.val v)) i :=
  (congrFun (RealizedProgram.evalE_rename (CarrierHEmbed.embedding (program := program)) e
    (f := f) (e := .leaf v) rfl (by simp [Expr.directNodes, hv]) (by simp [Expr.refs])) i).symm

/-- **A native shared expression of domain `H`'s core, read in the environment read as the native
program's**, is the carrier's renamed one. -/
theorem evalE_ref_pullH (e : program.Env interp) {f k : ℕ} (hk : k ∈ hR) (i : ℕ) :
    (nat).evalE ((nat).reader (pullH e)) f (.ref k) i =
      program.evalE (program.reader e) f (.ref (σH.ref k)) i :=
  (congrFun (RealizedProgram.evalE_rename (CarrierHEmbed.embedding (program := program)) e
    (f := f) (e := .ref k) rfl (by simp [Expr.directNodes]) (by simp [Expr.refs, hk])) i).symm

/-- The native `μ` bits are the carrier's domain `H` `μ` (value `71`). -/
theorem muBits_pull (e : program.Env interp) (t : Fin (8 * 64)) :
    MLDSA44.muBits ((nat).reader (pullH e)) t =
      program.evalE (program.reader e) 1 (.leaf 71) t := by
  unfold MLDSA44.muBits
  rw [evalE_pullH e (by decide), σH_val120]

/-- The native H's `w1` bits are the carrier's (value `73`). -/
theorem w1HBits_pull (e : program.Env interp) (t : Fin (8 * 768)) :
    MLDSA44.w1HBits ((nat).reader (pullH e)) t =
      program.evalE (program.reader e) 1 (.leaf 73) t := by
  unfold MLDSA44.w1HBits
  rw [evalE_pullH e (by decide), σH_val70]

/-- The native H's decoded support is the carrier's shared expression `503`. -/
theorem supH_pull (e : program.Env interp) (k : Fin 256) :
    MLDSA44.supH ((nat).reader (pullH e)) k =
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 503) k) := by
  unfold MLDSA44.supH
  rw [evalE_ref_pullH e (by decide), σH_ref523]

/-- The native H's decoded sign is the carrier's shared expression `504` (`502`). -/
theorem sgnH_pull (e : program.Env interp) (k : Fin 256) :
    MLDSA44.sgnH ((nat).reader (pullH e)) k =
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 504) k) := by
  unfold MLDSA44.sgnH
  rw [evalE_ref_pullH e (by decide), σH_ref522,
    RealizedProgram.evalE_ref MldsaCarrierRelation.refsOrdered _ _ (k := 504)
      (by have := MldsaCarrierFront.lt505 (program := program); omega),
    MldsaCarrierFront.expr504]

end PullH

/-! ## The emulated readers of domain `A` -/

section PullA

variable {program : RealizedProgram} [CarrierAEmbed program] {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

/-- **An emulated value of domain `A`'s gadgets, read in the environment read as the emulated
program's**, is the carrier's renamed value. -/
theorem evalE_pullA (e : program.Env interp) {f v : ℕ} (hv : v ∈ aV) (i : ℕ) :
    (emu).evalE ((emu).reader (pullA e)) f (.leaf v) i =
      program.evalE (program.reader e) f (.leaf (σA.val v)) i :=
  (congrFun (RealizedProgram.evalE_rename (CarrierAEmbed.embedding (program := program)) e
    (f := f) (e := .leaf v) rfl (by simp [Expr.directNodes, hv]) (by simp [Expr.refs])) i).symm

/-- The emulated `z` is the carrier's (value `60`). -/
theorem zVals_pullA (e : program.Env interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    Emulated.zVals ((emu).reader (pullA e)) j k = zVals (program.reader e) j k := by
  unfold Emulated.zVals zVals
  rw [evalE_pullA e (by decide), σA_vals.1]

/-- The emulated extracted `z` is the carrier's. -/
theorem zOf_pullA (e : program.Env interp) :
    Emulated.zOf ((emu).reader (pullA e)) = zOf (program.reader e) := by
  unfold Emulated.zOf zOf
  simp only [zVals_pullA]

/-- The emulated extracted `w′` is the carrier's (value `63`). -/
theorem wOf_pullA (e : program.Env interp) :
    Emulated.wOf ((emu).reader (pullA e)) = wOf (program.reader e) := by
  unfold Emulated.wOf wOf Emulated.wVals wVals
  simp only [evalE_pullA e (show 61 ∈ aV by decide), σA_vals.2.2.2.1]

/-- The emulated challenge bits are the carrier's (value `62`). -/
theorem cBits_pullA (e : program.Env interp) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) :
    Emulated.cABits ((emu).reader (pullA e)) k s = cBits (program.reader e) k s := by
  unfold Emulated.cABits cBits
  rw [evalE_pullA e (by decide), σA_vals.2.2.1]

/-- The emulated challenge polynomial is the carrier's. -/
theorem cPolyA_pullA (e : program.Env interp) :
    Emulated.cPolyA ((emu).reader (pullA e)) = cPoly (program.reader e) := by
  unfold Emulated.cPolyA cPoly
  simp only [cBits_pullA]

/-- The emulated `hint.w1` bits are the carrier's (value `66`). -/
theorem w1ABits_pullA (e : program.Env interp) (t : Fin (8 * 768)) :
    Emulated.w1ABits ((emu).reader (pullA e)) t =
      program.evalE (program.reader e) 0 (.leaf 66) t := by
  unfold Emulated.w1ABits
  rw [evalE_pullA e (by decide), σA_vals.2.2.2.2]

/-- The emulated hint is the carrier's (value `61`). -/
theorem hVals_pullA (e : program.Env interp) (i : Fin MLDSA44.Native.Rows.nRows)
    (k : Fin MLDSA44.Native.Rows.deg) :
    Emulated.hVals ((emu).reader (pullA e)) i k =
      program.evalE (program.reader e) 0 (.leaf 61) ((i : ℕ) * 256 + k) := by
  unfold Emulated.hVals
  rw [evalE_pullA e (by decide), σA_vals.2.1]

/-- **Domain `A`'s gadgets hold in the environment read as the emulated program's**
(`Emulated.EASat`), where the carrier's source program holds (`aSat`). -/
theorem eaSat {e : program.Env interp} (hs : program.SourceSatAt e) :
    Emulated.EASat (pullA e) :=
  ⟨fun p hp => aSat hs p hp⟩

end PullA

end GordieHowe.MLDSA44.Ring.Carrier
