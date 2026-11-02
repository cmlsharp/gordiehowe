-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Statement
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Relation
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Ring.Table
public import GordieHowe.Applications.MLDSA44.Native.Frontend.Algebra

@[expose] public section

/-!
# GordieHowe frontend: the readings of the native ML-DSA-44 ring programs

The facts of a native ML-DSA-44 ring program (`lib/gordiehowe/examples/rings/mldsa_ring.h`,
`mldsa_ring_native.h`) its frontend's composition reads, beyond the embedding of the native
proof of possession's parts (`MldsaRingEmbed`), the signature relation (`MldsaRingRelation`), the
statement values (`MldsaRingStmt`) and the public table's selection
(`GordieHowe.RealizedProgram.TableSelect`):

* **The program facts** (`MldsaRingFront`, decided per program): the committed `μ` (`member.mu`),
  the hint (`h`), the UseHint output (`hint.w1`), domain `H`'s `μ` and `w1` bit views; the table's
  shape; the record (shared expression `1`: `member.a_hat ‖ member.t1 ‖` the `24` limbs of the
  zero-extended `μ` bits, shared expression `0`); `member.mu.boolean`; the crossing `mac.equal`
  (predicate `248`, `cross(H, x, A, y)` with `x` the shared expression `513`, H's `μ ‖ w1 ‖` the
  decoded challenge's support and sign alternately, and `y` the shared expression `50`, A's
  `member.mu ‖ hint.w1 ‖ challenge.c`); the renaming's values; the typed values of domain `H`'s
  core; the challenges (the ring's challenge `j + 1` is the native program's `j`).
* **The native readers at the ring's environment** (`evalE_pull`, `zOf_pull`, `wOf_pull`,
  `cPolyA_pull`, `supH_pull`, `sgnH_pull`, …): the native frontend's readers in the environment
  read as the native program's are the ring program's readers at the renamed values.
* **Domain `H`'s core and domain `A`'s gadgets** (`hSatCore`, `aSatNat`): the native frontend's
  `HSatCore` and `ASat` in that environment, where the ring's source program holds.
* **The record** (`rec_aHat`, `rec_t1`, `rec_mu`, `record_row`): the selection
  (`TableSelect.record_eq_of_not_bad`) makes the record row `idx` of the statement; at a
  statement holding a ring's rows (`RowsOf`) the committed `â` and `t̂` are the key's
  (`aHatVals_eq`, `t1HatVals_eq`) and the committed `μ` bits are those of the key's `μ`
  (`muA_eq`, through the limbs: the record's limb is `Σ_b 2^b μ_{22 l + b}`, a natural below
  `2^22 < q`).
* **The crossing** (`RingCrossAt`, `ringCross`): `mac.equal` gives A's `μ`, `w1` and challenge bits
  read as naturals equal to H's, where H's decoded support and sign are bits; `crossAt_pull`: the
  native frontend's crossing (`MLDSA44.CrossAt`) in the environment read as the native
  program's.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram

/-- **The program facts of a native ML-DSA-44 ring program's frontend** (decided per program;
the values of the program at the ROM parameters in parentheses): `member.mu` (`muA`, `57`), `h`
(`hA`, `61`), `hint.w1` (`w1A`, `65`), domain `H`'s `mu` (`muH`, `70`) and `w1` (`w1H`, `72`);
the table's shape (the record, shared expression `1`, the column blocks `ring.keys`, `ring.mu`,
the identity row map, `64` rows and `6` index bits, the challenge `0`); the record's expressions
(`0`: the `512` `μ` bits and `15` zeros, `1`: `â ‖ t̂ ‖` the `24` limbs `fromDigits 22 2`);
`member.mu.boolean`; the crossing `mac.equal` (predicate `248`) of the shared expressions `513`
and `50`, their parts and index maps; the renaming's values, the typed values of domain `H`'s
core, the challenges and the values the extractor reads. -/
class MldsaRingFront (program : RealizedProgram) [MldsaRingEmbed program]
    [MldsaRingRelation program] [MldsaRingStmt program] [TableSelect program] where
  /-- `member.mu`. -/
  muA : ℕ
  /-- `h`. -/
  hA : ℕ
  /-- `hint.w1`. -/
  w1A : ℕ
  /-- Domain `H`'s `mu`. -/
  muH : ℕ
  /-- Domain `H`'s `w1`. -/
  w1H : ℕ
  /-- The table's shape. -/
  shape : (TableSelect.shape program).dom = 0 ∧ (TableSelect.shape program).chal = 0 ∧
    (TableSelect.shape program).mOne = 8380416 ∧ (TableSelect.shape program).zero = 0 ∧
    (TableSelect.shape program).record = .ref 1 ∧
    (TableSelect.shape program).parts =
      [(MldsaRingStmt.keys program, 5120), (MldsaRingStmt.mu program, 24)] ∧
    (TableSelect.shape program).map = nativeMap ∧ (TableSelect.shape program).rows = 64 ∧
    (TableSelect.shape program).bits = 6
  /-- Domain `A` is field `0`, domain `H` field `1`. -/
  domains : program.domainField 0 = 0 ∧ program.domainField 1 = 1
  /-- The program has the shared expressions `0 … 513`. -/
  lt513 : 513 < program.exprs.length
  /-- Shared expression `0`: the `μ` bits and `15` zeros. -/
  expr0 : program.expr 0 = .reindex [(0, 1, 513), (512, 0, 15)] (.concat (.leaf muA) (.leaf 0))
  /-- Shared expression `1`: the record. -/
  expr1 : program.expr 1 = .reindex [(0, 1, 5144)]
    (.concat (.reindex [(0, 1, 5120)] (.concat (.reindex [(0, 1, 4096)]
        (.leaf (MldsaRingRelation.aHat program)))
      (.reindex [(0, 1, 1024)] (.leaf (MldsaRingRelation.t1 program)))))
      (.reindex [(0, 1, 24)] (.apply (.batched 24 (.fromDigits 22 2)) (.ref 0))))
  /-- `member.mu` has `512` coordinates. -/
  muSize : (program.value muA).size = 512
  /-- `member.mu.boolean` checks the `μ` bits, a source predicate. -/
  muBool : (program.predicate 10).body.boolCheck? = some ⟨0, muA⟩ ∧
    10 < program.predicates.length ∧ program.inSource (program.predicate 10) = true
  /-- `mac.equal` crosses `513` of domain `H` and `50` of domain `A`, a source predicate. -/
  cross : 248 < program.predicates.length ∧ program.inSource (program.predicate 248) = true ∧
    ∃ c, (program.predicate 248).body = .cross 1 (.ref 513) 0 (.ref 50) {} c
  /-- The crossing's `x`: H's `μ`, `w1`, then the decoded support and sign alternately. -/
  exprH : ∃ m : IndexMap, program.expr 513 = .reindex m (concatR (.leaf muH)
      [.leaf w1H, .ref ((MldsaRingEmbed.σ program).ref 523),
        .ref ((MldsaRingEmbed.σ program).ref 524)]) ∧
    (∀ t < 6656, m.entry t = t) ∧ (∀ k < 256, m.entry (6656 + 2 * k) = 6656 + k) ∧
    (∀ k < 256, m.entry (6656 + (2 * k + 1)) = 6912 + k)
  /-- The crossing's `y`: A's `μ`, `w1` and challenge bits, in order. -/
  exprA : ∃ m : IndexMap, program.expr 50 = .reindex m (concatR (.leaf muA)
      [.leaf w1A, .leaf (MldsaRingRelation.c program)]) ∧ ∀ t < 7168, m.entry t = t
  /-- The crossing's lengths. -/
  lens : program.exprLen (.ref 513) = 7168 ∧ (program.value muH).size = 512 ∧
    (program.value w1H).size = 6144 ∧
    program.exprLen (.ref ((MldsaRingEmbed.σ program).ref 523)) = 256 ∧
    program.exprLen (.ref ((MldsaRingEmbed.σ program).ref 524)) = 256 ∧
    (program.value w1A).size = 6144
  /-- Domain `H`'s `μ` and `w1` are bit views. -/
  bitViews : program.isBitView muH = true ∧ program.isBitView w1H = true
  /-- The renaming's values: the native `z`, `h`, `challenge.c`, `signature.w`, `hint.w1`,
  H's `w1` and `μ`. -/
  vals : (MldsaRingEmbed.σ program).val 57 = MldsaRingRelation.z program ∧
    (MldsaRingEmbed.σ program).val 58 = hA ∧
    (MldsaRingEmbed.σ program).val 59 = MldsaRingRelation.c program ∧
    (MldsaRingEmbed.σ program).val 60 = MldsaRingRelation.w program ∧
    (MldsaRingEmbed.σ program).val 62 = w1A ∧ (MldsaRingEmbed.σ program).val 70 = w1H ∧
    (MldsaRingEmbed.σ program).val 120 = muH
  /-- The renamed typed values of domain `H`'s core are node-typed source values. -/
  typedCore : ∀ v ∈ MLDSA44.hTypedCore,
    (MldsaRingEmbed.σ program).val v < program.values.length ∧
      program.IsSourceValue ((MldsaRingEmbed.σ program).val v) ∧
      (program.value ((MldsaRingEmbed.σ program).val v)).typeSource = .node
  /-- The native challenge `j` is the ring's challenge `j + 1`. -/
  chalSucc : ∀ j, (MldsaRingEmbed.σ program).chal j = j + 1
  /-- The table's challenge `0` is a source challenge. -/
  chal0 : program.IsSourceChal 0
  /-- The ring's source challenge `j + 1` is the native source challenge `j`. -/
  chalIff : ∀ j, program.IsSourceChal (j + 1) ↔ (MldsaRingEmbed.nat program).IsSourceChal j
  /-- The native source challenges and their ring challenges: one coordinate drawn from the same
  field. -/
  chalShape : ∀ j, (MldsaRingEmbed.nat program).IsSourceChal j →
    (program.challenge (j + 1)).size = 1 ∧ (program.challenge (j + 1)).sampler = .full ∧
    ((MldsaRingEmbed.nat program).challenge j).size = 1 ∧
    ((MldsaRingEmbed.nat program).challenge j).sampler = .full ∧
    program.chalField (j + 1) = (MldsaRingEmbed.nat program).chalField j
  /-- The values the extractor reads (`c̃'`, `z`, `h`) read nothing from the run. -/
  projReads : ∀ v ∈ [(MldsaRingEmbed.σ program).val 457, (MldsaRingEmbed.σ program).val 57,
    (MldsaRingEmbed.σ program).val 58], program.nodeReads program.fuel v = []

/-- **The rows' natural row map is the identity**: a map of identity leaves applied to a row is
the row, below the map's width. -/
theorem rowApply_id {K : Type*} [Field K] (dec : ℕ → K) :
    ∀ (m : List RowLeaf), (∀ l ∈ m, l.ntt = false) → ∀ (row : ℕ → K) {c : ℕ},
      c < mapWidth m → rowApply dec m row c = row c
  | [], _, _, c, hc => by simp [mapWidth] at hc
  | l :: ls, hm, row, c, hc => by
    rw [rowApply]
    by_cases h : c < l.n
    · rw [if_pos h, RowLeaf.apply, if_neg (by rw [hm l (by simp)]; decide)]
    · rw [if_neg h, rowApply_id dec ls (fun l' hl' => hm l' (by simp [hl'])) _
        (by rw [mapWidth_cons] at hc; omega)]
      congr 1
      omega

/-- The native row map has `5144` cells, all of identity leaves. -/
theorem nativeMap_facts : mapWidth nativeMap = 5144 ∧ ∀ l ∈ nativeMap, l.ntt = false := by
  decide +kernel

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program]
  {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

/-! ## The native readers at the ring's environment -/

section Pull

/-- **A native value of the parts, read in the environment read as the native program's**, is
the ring's renamed value. -/
theorem evalE_pull (e : program.Env interp) {f v : ℕ} (hv : v ∈ ringV) (i : ℕ) :
    (nat).evalE ((nat).reader (pull e)) f (.leaf v) i =
      program.evalE (program.reader e) f (.leaf ((σ).val v)) i :=
  (congrFun (RealizedProgram.evalE_rename (MldsaRingEmbed.embedding (program := program)) e
    (f := f) (e := .leaf v) rfl (by simp [Expr.directNodes, hv]) (by simp [Expr.refs])) i).symm

/-- **A native shared expression of the parts, read in the environment read as the native
program's**, is the ring's renamed one. -/
theorem evalE_ref_pull (e : program.Env interp) {f k : ℕ} (hk : k ∈ ringR) (i : ℕ) :
    (nat).evalE ((nat).reader (pull e)) f (.ref k) i =
      program.evalE (program.reader e) f (.ref ((σ).ref k)) i :=
  (congrFun (RealizedProgram.evalE_rename (MldsaRingEmbed.embedding (program := program)) e
    (f := f) (e := .ref k) rfl (by simp [Expr.directNodes]) (by simp [Expr.refs, hk])) i).symm

/-- The native `z` is the ring's. -/
theorem zVals_pull (e : program.Env interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.zVals ((nat).reader (pull e)) j k = zVals (program.reader e) j k := by
  unfold MLDSA44.zVals zVals
  rw [evalE_pull e (by decide), MldsaRingFront.vals.1]

/-- The native extracted `z` is the ring's. -/
theorem zOf_pull (e : program.Env interp) :
    MLDSA44.zOf ((nat).reader (pull e)) = zOf (program.reader e) := by
  unfold MLDSA44.zOf zOf
  simp only [zVals_pull]

/-- The native `w'` is the ring's. -/
theorem wOf_pull (e : program.Env interp) :
    MLDSA44.wOf ((nat).reader (pull e)) = wOf (program.reader e) := by
  unfold MLDSA44.wOf wOf MLDSA44.wVals wVals
  simp only [evalE_pull e (show 60 ∈ ringV by decide), MldsaRingFront.vals.2.2.2.1]

/-- The native challenge bits are the ring's. -/
theorem cABits_pull (e : program.Env interp) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) :
    MLDSA44.cABits ((nat).reader (pull e)) k s = cBits (program.reader e) k s := by
  unfold MLDSA44.cABits cBits
  rw [evalE_pull e (by decide), MldsaRingFront.vals.2.2.1]

/-- The native challenge polynomial is the ring's. -/
theorem cPolyA_pull (e : program.Env interp) :
    MLDSA44.cPolyA ((nat).reader (pull e)) = cPoly (program.reader e) := by
  unfold MLDSA44.cPolyA cPoly
  simp only [cABits_pull]

/-- The native `hint.w1` bits are the ring's. -/
theorem w1ABits_pull (e : program.Env interp) (t : Fin (8 * 768)) :
    MLDSA44.w1ABits ((nat).reader (pull e)) t =
      program.evalE (program.reader e) 0 (.leaf (MldsaRingFront.w1A program)) t := by
  unfold MLDSA44.w1ABits
  rw [evalE_pull e (by decide), MldsaRingFront.vals.2.2.2.2.1]

/-- The native H's `w1` bits are the ring's. -/
theorem w1HBits_pull (e : program.Env interp) (t : Fin (8 * 768)) :
    MLDSA44.w1HBits ((nat).reader (pull e)) t =
      program.evalE (program.reader e) 1 (.leaf (MldsaRingFront.w1H program)) t := by
  unfold MLDSA44.w1HBits
  rw [evalE_pull e (by decide), MldsaRingFront.vals.2.2.2.2.2.1]

/-- The native `μ` bits are the ring's domain `H` `μ`. -/
theorem muBits_pull (e : program.Env interp) (t : Fin (8 * 64)) :
    MLDSA44.muBits ((nat).reader (pull e)) t =
      program.evalE (program.reader e) 1 (.leaf (MldsaRingFront.muH program)) t := by
  unfold MLDSA44.muBits
  rw [evalE_pull e (by decide), MldsaRingFront.vals.2.2.2.2.2.2]

/-- The native H's decoded support is the ring's renamed shared expression. -/
theorem supH_pull (e : program.Env interp) (k : Fin 256) :
    MLDSA44.supH ((nat).reader (pull e)) k =
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref ((σ).ref 523)) k) := by
  unfold MLDSA44.supH
  rw [evalE_ref_pull e (by decide)]

variable [MLDSA44.MldsaHCross nat] in
/-- The native H's decoded sign is the ring's renamed shared expression `σ.ref 524` (native
`524` is `522`). -/
theorem sgnH_pull (e : program.Env interp) (k : Fin 256) :
    MLDSA44.sgnH ((nat).reader (pull e)) k =
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref ((σ).ref 524)) k) := by
  unfold MLDSA44.sgnH
  rw [← evalE_ref_pull e (k := 524) (by decide),
    RealizedProgram.evalE_ref MLDSA44.MldsaHCross.refsOrdered _ _
      MLDSA44.MldsaHCross.lt524, MLDSA44.MldsaHCross.expr524]

/-- **Domain `H`'s core holds in the environment read as the native program's**, where the ring
source program holds: the predicates `48 … 270` (`hPreds_pull`) and the typed values. -/
theorem hSatCore {e : program.Env interp} (hs : program.SourceSatAt e) :
    MLDSA44.HSatCore (pull e) where
  preds := hPreds_pull hs
  types v hv i hi := by
    obtain ⟨hl, hsrc, hts⟩ := MldsaRingFront.typedCore (program := program) v hv
    have hvV : v ∈ ringV := by
      simp only [MLDSA44.hTypedCore, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [ringV, List.mem_append, List.mem_range'_1, List.mem_cons,
          List.not_mem_nil] <;> omega
    refine RealizedProgram.inType_pullEnv MldsaRingEmbed.embedding e hvV
      (hs.types _ hl hsrc hts i ?_)
    rw [((MldsaRingEmbed.embedding (program := program)).vals v hvV).2.2.2.1]
    exact hi

/-- **Domain `A`'s gadgets hold in the environment read as the native program's**, where the ring
source program holds (`aSat`). -/
theorem aSatNat {e : program.Env interp} (hs : program.SourceSatAt e) :
    MLDSA44.Native.ASat (pull e) :=
  ⟨aSat hs⟩

end Pull

end GordieHowe.MLDSA44.Ring.Native
