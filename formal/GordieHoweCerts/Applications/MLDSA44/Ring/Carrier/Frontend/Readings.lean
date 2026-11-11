-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Statement
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Relation
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Ring.Table
public import GordieHoweCerts.Applications.MLDSA44.Emulated.Frontend.Algebra

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
  shared expression `0`; the row map `carrierMap`); `member.mu.boolean` (predicate `10`); the
  crossing `mac.equal` (predicate `250`, `cross(H, x, A, y)` with `x` the shared expression `558`,
  H's `μ ‖ w1 ‖` the decoded challenge's support and sign alternately, and `y` the shared
  expression `95`, A's `member.mu ‖ hint.w1 ‖ challenge.c`); domain `H`'s `μ` and `w1` bit views;
  the challenges (the carrier's challenge `1` is the signature relation's `r`, its challenge
  `j + 2` the native program's `j`); the values the extractor reads.
* **The native readers of domain `H` at the carrier's environment** (`evalE_pullH`, `muBits_pull`,
  `w1HBits_pull`, `supH_pull`, `sgnH_pull`): the native frontend's readers in the environment read
  as the native program's are the carrier's readers at the renamed values: H's `μ` and `w1`, the
  decoded support and sign.
* **The emulated readers of domain `A` at the carrier's environment** (`evalE_pullA`, `zOf_pullA`,
  `wOf_pullA`, `cBits_pullA`, `cPolyA_pullA`, `w1ABits_pullA`, `hVals_pullA`): the emulated
  frontend's readers in the environment read as the emulated program's are the carrier's, at the
  carrier frontend's values (`MldsaCarrierFront.valsA`).
* **Domain `A`'s gadgets** (`eaSat`): the emulated frontend's `EASat` in that environment, where
  the carrier's source program holds.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

set_option hygiene false in
local notation "σH" => CarrierHEmbed.σ program

set_option hygiene false in
local notation "hV" => CarrierHEmbed.V program

set_option hygiene false in
local notation "σA" => CarrierAEmbed.σ program

set_option hygiene false in
local notation "aV" => CarrierAEmbed.V program

set_option hygiene false in
local notation "predMapA" => CarrierAEmbed.pred program

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt)

/-- **The program facts of an ML-DSA-44 ring carrier's frontend** (decided per carrier): the
carrier's values the emulated program's `h` and `hint.w1` are (`hA`, `w1A`), the predicates of
`member.mu`'s Booleanity and of the crossing (`muBoolPred`, `crossPred`) and where the emulated
values land among the carrier's (`valsA`); the table's shape (the record, shared expression `1`,
the column blocks `ring.keys`, `ring.mu`, the row map `carrierMap`, `64` rows and `6` index bits,
the challenge `0`); the record's expressions (`0`: the `512` `μ` bits of `member.mu`, value `58`,
and `15` zeros; `1`: `member.a_hat ‖ member.t1 ‖` the `24` limbs `fromDigits 22 2`);
`member.mu.boolean`; the crossing `mac.equal` of the shared expressions `558` and `95`, their
parts (the renamed native `μ`, `w1`, decoded support and sign; the member's `μ`, `hint.w1`, the
challenge bits) and index maps; the renamed native `μ` and `w1` bit views; the challenges
(`signature.r`, challenge `1`, and the native program's, from `2`) and the values the extractor
reads (the renamed native `c̃'`, `z`, `h`). -/
class MldsaCarrierFront (program : RealizedProgram) [CarrierHEmbed program] [CarrierAEmbed program]
    [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program] where
  /-- The emulated `h`'s value in the carrier. -/
  hA : ℕ
  /-- The emulated `hint.w1`'s value in the carrier. -/
  w1A : ℕ
  /-- `member.mu.boolean`, the `μ` bits' Booleanity. -/
  muBoolPred : ℕ
  /-- `mac.equal`, the crossing. -/
  crossPred : ℕ
  /-- **The emulated values the carrier reads**: `z`, `challenge.c` and `w′` are the relation's,
  `h` and `hint.w1` the values `hA` and `w1A`. -/
  valsA : (CarrierAEmbed.σ program).val 58 = MldsaRandomPoint.z program ∧
    (CarrierAEmbed.σ program).val 59 = hA ∧
    (CarrierAEmbed.σ program).val 60 = MldsaRandomPoint.c program ∧
    (CarrierAEmbed.σ program).val 61 = MldsaRandomPoint.w program ∧
    (CarrierAEmbed.σ program).val 63 = w1A
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
  /-- The program has the shared expressions `0 … 558`. -/
  lt558 : 558 < program.exprs.length
  /-- Shared expression `0`: the `μ` bits and `15` zeros. -/
  expr0 : program.expr 0 = .reindex [(0, 1, 513), (512, 0, 15)] (.concat (.leaf 58) (.leaf 0))
  /-- Shared expression `1`: the record. -/
  expr1 : program.expr 1 = .reindex [(0, 1, 5144)]
    (.concat (.reindex [(0, 1, 5120)] (.concat (.reindex [(0, 1, 4096)] (.leaf 56))
      (.reindex [(0, 1, 1024)] (.leaf 57))))
      (.reindex [(0, 1, 24)] (.apply (.batched 24 (.fromDigits 22 2)) (.ref 0))))
  /-- `member.mu` has `512` coordinates. -/
  muSize : (program.value 58).size = 512
  /-- `member.mu.boolean` checks the `μ` bits, a source predicate. -/
  muBool : (program.predicate muBoolPred).body.boolCheck? = some ⟨0, 58⟩ ∧
    muBoolPred < program.predicates.length ∧
    program.inSource (program.predicate muBoolPred) = true
  /-- `mac.equal` crosses `558` of domain `H` and `95` of domain `A`, a source predicate. -/
  cross : crossPred < program.predicates.length ∧
    program.inSource (program.predicate crossPred) = true ∧
    ∃ c, (program.predicate crossPred).body = .cross 1 (.ref 558) 0 (.ref 95) {} c
  /-- The crossing's `x`: H's `μ`, `w1`, then the decoded support and sign alternately. -/
  exprH : ∃ m : IndexMap, program.expr 558 = .reindex m
      (concatR (.leaf ((CarrierHEmbed.σ program).val 120))
        [.leaf ((CarrierHEmbed.σ program).val 70), .ref ((CarrierHEmbed.σ program).ref 523),
          .ref 557]) ∧
    (∀ t < 6656, m.entry t = t) ∧ (∀ k < 256, m.entry (6656 + 2 * k) = 6656 + k) ∧
    (∀ k < 256, m.entry (6656 + (2 * k + 1)) = 6912 + k)
  /-- The crossing's sign part is the decoded sign. -/
  expr557 : program.expr 557 = .ref ((CarrierHEmbed.σ program).ref 522)
  /-- The crossing's `y`: A's `μ`, `w1` and challenge bits, in order. -/
  exprA : ∃ m : IndexMap, program.expr 95 = .reindex m (concatR (.leaf 58)
      [.leaf w1A, .leaf 63]) ∧ ∀ t < 7168, m.entry t = t
  /-- The crossing's lengths. -/
  lens : program.exprLen (.ref 558) = 7168 ∧
    (program.value ((CarrierHEmbed.σ program).val 120)).size = 512 ∧
    (program.value ((CarrierHEmbed.σ program).val 70)).size = 6144 ∧
    program.exprLen (.ref ((CarrierHEmbed.σ program).ref 523)) = 256 ∧
    program.exprLen (.ref 557) = 256 ∧ (program.value w1A).size = 6144
  /-- Domain `H`'s `μ` and `w1` are bit views. -/
  bitViews : program.isBitView ((CarrierHEmbed.σ program).val 120) = true ∧
    program.isBitView ((CarrierHEmbed.σ program).val 70) = true
  /-- The table's challenge `0` is a source challenge. -/
  chal0 : program.IsSourceChal 0
  /-- The signature relation's challenge `1` is a source challenge. -/
  chal1 : program.IsSourceChal 1
  /-- The carrier's source challenge `j + 2` is the native source challenge `j`. -/
  chalIff : ∀ j, program.IsSourceChal (j + 2) ↔ (CarrierHEmbed.nat program).IsSourceChal j
  /-- The native source challenges and their carrier challenges: one coordinate drawn from the
  same field. -/
  chalShape : ∀ j, (CarrierHEmbed.nat program).IsSourceChal j →
    (program.challenge (j + 2)).size = 1 ∧ (program.challenge (j + 2)).sampler = .full ∧
    ((CarrierHEmbed.nat program).challenge j).size = 1 ∧
    ((CarrierHEmbed.nat program).challenge j).sampler = .full ∧
    program.chalField (j + 2) = (CarrierHEmbed.nat program).chalField j
  /-- The values the extractor reads (`c̃'`, `z`, `h`) read nothing from the run. -/
  projReads : ∀ v ∈ [(CarrierHEmbed.σ program).val 457, MldsaRandomPoint.z program, hA],
    program.nodeReads program.fuel v = []
  /-- The values the relation's event reads (`w′`, the quotient, the high halves, `member.t1`,
  `member.a_hat`, `z`, the challenge bits) read nothing from the run. -/
  relReads : ∀ v ∈ [64, 65, 66, 57, 56, 61, 63], program.nodeReads program.fuel v = []

set_option linter.unusedSectionVars false


/-! ## The native readers of domain `H` -/

section PullH

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program]
  {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

/-- **A native value of domain `H`'s core, read in the environment read as the native
program's**, is the carrier's renamed value. -/
theorem evalE_pullH (e : program.Env interp) {f v : ℕ} (hv : v ∈ hV) (i : ℕ) :
    (nat).evalE ((nat).reader (pullH e)) f (.leaf v) i =
      program.evalE (program.reader e) f (.leaf ((σH).val v)) i :=
  (congrFun (RealizedProgram.evalE_rename (CarrierHEmbed.embedding (program := program)) e
    (f := f) (e := .leaf v) rfl (by simp [Expr.directNodes, hv]) (by simp [Expr.refs])) i).symm

/-- **A native shared expression of domain `H`'s core, read in the environment read as the native
program's**, is the carrier's renamed one. -/
theorem evalE_ref_pullH (e : program.Env interp) {f k : ℕ} (hk : k ∈ CarrierHEmbed.R program) (i : ℕ) :
    (nat).evalE ((nat).reader (pullH e)) f (.ref k) i =
      program.evalE (program.reader e) f (.ref ((σH).ref k)) i :=
  (congrFun (RealizedProgram.evalE_rename (CarrierHEmbed.embedding (program := program)) e
    (f := f) (e := .ref k) rfl (by simp [Expr.directNodes]) (by simp [Expr.refs, hk])) i).symm

/-- The native `μ` bits are the carrier's renamed ones. -/
theorem muBits_pull (e : program.Env interp) (t : Fin (8 * 64)) :
    MLDSA44.muBits ((nat).reader (pullH e)) t =
      program.evalE (program.reader e) 1 (.leaf ((σH).val 120)) t := by
  unfold MLDSA44.muBits
  rw [evalE_pullH e (CarrierHEmbed.readV _ (by decide))]

/-- The native H's `w1` bits are the carrier's renamed ones. -/
theorem w1HBits_pull (e : program.Env interp) (t : Fin (8 * 768)) :
    MLDSA44.w1HBits ((nat).reader (pullH e)) t =
      program.evalE (program.reader e) 1 (.leaf ((σH).val 70)) t := by
  unfold MLDSA44.w1HBits
  rw [evalE_pullH e (CarrierHEmbed.readV _ (by decide))]

/-- The native H's decoded support is the carrier's renamed shared expression. -/
theorem supH_pull (e : program.Env interp) (k : Fin 256) :
    MLDSA44.supH ((nat).reader (pullH e)) k =
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref ((σH).ref 523)) k) := by
  unfold MLDSA44.supH
  rw [evalE_ref_pullH e (CarrierHEmbed.readR _ (by decide))]

/-- The native H's decoded sign is the carrier's shared expression `557`, the renamed sign. -/
theorem sgnH_pull (e : program.Env interp) (k : Fin 256) :
    MLDSA44.sgnH ((nat).reader (pullH e)) k =
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 557) k) := by
  unfold MLDSA44.sgnH
  rw [evalE_ref_pullH e (CarrierHEmbed.readR _ (by decide)),
    RealizedProgram.evalE_ref MldsaRandomPoint.refsOrdered _ _ (k := 557)
      (by have := MldsaCarrierFront.lt558 (program := program); omega),
    MldsaCarrierFront.expr557]

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
      program.evalE (program.reader e) f (.leaf ((σA).val v)) i :=
  (congrFun (RealizedProgram.evalE_rename (CarrierAEmbed.embedding (program := program)) e
    (f := f) (e := .leaf v) rfl (by simp [Expr.directNodes, hv]) (by simp [Expr.refs])) i).symm

variable [CarrierHEmbed program] [MldsaCarrierRelation program] [MldsaRingStmt program]
  [TableSelect program] [MldsaCarrierFront program]

/-- The emulated `z` is the carrier's. -/
theorem zVals_pullA (e : program.Env interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    Emulated.zVals ((emu).reader (pullA e)) j k = zVals (program.reader e) j k := by
  unfold Emulated.zVals zVals
  rw [evalE_pullA e (CarrierAEmbed.readV _ (by decide)), MldsaCarrierFront.valsA.1, z_eq]

/-- The emulated extracted `z` is the carrier's. -/
theorem zOf_pullA (e : program.Env interp) :
    Emulated.zOf ((emu).reader (pullA e)) = zOf (program.reader e) := by
  unfold Emulated.zOf zOf
  simp only [zVals_pullA]

/-- The emulated extracted `w′` is the carrier's. -/
theorem wOf_pullA (e : program.Env interp) :
    Emulated.wOf ((emu).reader (pullA e)) = wOf (program.reader e) := by
  unfold Emulated.wOf wOf Emulated.wVals wVals
  simp only [evalE_pullA e (CarrierAEmbed.readV 61 (by decide)), MldsaCarrierFront.valsA.2.2.2.1,
    w_eq]

/-- The emulated challenge bits are the carrier's. -/
theorem cBits_pullA (e : program.Env interp) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) :
    Emulated.cABits ((emu).reader (pullA e)) k s = cBits (program.reader e) k s := by
  unfold Emulated.cABits cBits
  rw [evalE_pullA e (CarrierAEmbed.readV _ (by decide)), MldsaCarrierFront.valsA.2.2.1, c_eq]

/-- The emulated challenge polynomial is the carrier's. -/
theorem cPolyA_pullA (e : program.Env interp) :
    Emulated.cPolyA ((emu).reader (pullA e)) = cPoly (program.reader e) := by
  unfold Emulated.cPolyA cPoly
  simp only [cBits_pullA]

/-- The emulated `hint.w1` bits are the carrier's (`MldsaCarrierFront.w1A`). -/
theorem w1ABits_pullA (e : program.Env interp) (t : Fin (8 * 768)) :
    Emulated.w1ABits ((emu).reader (pullA e)) t =
      program.evalE (program.reader e) 0 (.leaf (MldsaCarrierFront.w1A program)) t := by
  unfold Emulated.w1ABits
  rw [evalE_pullA e (CarrierAEmbed.readV _ (by decide)), MldsaCarrierFront.valsA.2.2.2.2]

/-- The emulated hint is the carrier's (`MldsaCarrierFront.hA`). -/
theorem hVals_pullA (e : program.Env interp) (i : Fin MLDSA44.Native.Rows.nRows)
    (k : Fin MLDSA44.Native.Rows.deg) :
    Emulated.hVals ((emu).reader (pullA e)) i k =
      program.evalE (program.reader e) 0 (.leaf (MldsaCarrierFront.hA program))
        ((i : ℕ) * 256 + k) := by
  unfold Emulated.hVals
  rw [evalE_pullA e (CarrierAEmbed.readV _ (by decide)), MldsaCarrierFront.valsA.2.1]

/-- **Domain `A`'s gadgets hold in the environment read as the emulated program's**
(`Emulated.EASat`), where the carrier's source program holds (`aSat`). -/
theorem eaSat {e : program.Env interp} (hs : program.SourceSatAt e) :
    Emulated.EASat (pullA e) :=
  ⟨fun p hp => aSat hs p hp⟩

end PullA

end GordieHowe.MLDSA44.Ring.Carrier
