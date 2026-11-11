-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Codecs
public import GordieHoweNative.ProofSystem.GKR.CertificateBridge
public import GordieHoweNative.ProofSystem.Program.ForkNums
public import GordieHoweNative.Language.Realizations.Circuit.RelFamily
public import GordieHoweNative.Language.Realizations.SharedNorm

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Circuit.RelEntry`

The definitions of `GordieHowe.Language.Realizations.Circuit.RelEntry` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Circuit/RelEntry.lean`, which imports this module.
-/

local notation "ℕ" => Nat

public section

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin GordieHowe.GKR.CertificateBridge
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert relOkE)

section Meaning

variable (ir : RealizedProgram)

/-- **The printed sides of a placed field equation**: an `equal`, or a `mod_q` with `q = 0` or in
the field form. -/
@[expose] def placedSides? : PredBody → Option (ℕ × Expr × Expr)
  | .equal d l r _ => some (d, l, r)
  | .mod d q l r real =>
    if Nat.beq q 0 || decide (real.form = .field) then some (d, l, r) else none
  | _ => none

/-- **`X` is `Y` or `−Y`** (the code `neg1` times `Y`) as normal forms in domain `d`'s field of
characteristic `chr`, at every coordinate of `X`: with `A`, `B` the normal forms of `X` and `Y`
(`nfS`, shared expressions as atoms), `A − B` is zero, or `neg1 < chr` and `A − neg1 · B` is zero
(`zeroLoop`, unfolding shared expressions until the difference vanishes). -/
@[expose] def nfUnitEqB (d chr neg1 : ℕ) («X» «Y» : Expr) : Bool :=
  let f := ir.domainField d
  let L := ir.exprLen «X»
  let k := ir.normFuel «X» «Y» «Y»
  match ir.nfS f chr k (List.range L) «X», ir.nfS f chr k (List.range L) «Y» with
  | some a, some b =>
    let n := ir.exprs.length + 1
    let mb := sScale chr (intCode chr (-1)) b
    ir.zeroLoop f chr k L n (sAdd chr a mb) ||
      (Nat.blt neg1 chr && ir.zeroLoop f chr k L n (sAdd chr a (sScale chr neg1 mb)))
  | _, _ => false

/-- **The meaning of an entry's asserted root** with print `X` in circuit `c` (field
characteristic `chr`, `neg1` the code of `−1`): a Boolean check or a placed field equation `l = r`
in the circuit's domain, `X` as long as `l` and `X = ±(l − r)` as normal forms; an alignment
entry, no root. A realization entry is rejected. -/
@[expose] def entryMeaningB (c chr neg1 : ℕ) (en : CircuitEntry) («X» : Option Expr) : Bool :=
  match en, «X» with
  | .alignment _, none => true
  | .typeCheck p, some «X» | .pred p, some «X» =>
    match placedSides? (ir.predicate p).body with
    | some (d, l, r) =>
      Nat.beq d (ir.circuit c).domain && Nat.beq (ir.exprLen l) (ir.exprLen «X») &&
        ir.nfUnitEqB d chr neg1 «X» (.sub l r)
    | none => false
  | _, _ => false

end Meaning

section Entries

variable (ir : RealizedProgram) (c : ℕ) (ar : CodeArith) (cd : CircuitData)

/-- **Node `k` of entry `e`**: its cuts, accepted by the relational check. -/
@[expose] def nodeOkE (e k : ℕ) : Except CertFailure Unit :=
  match ir.nodeCutsE c (cd.env ar) cd.table k with
  | .error r => .error ⟨e, k, r⟩
  | .ok cs =>
    mapE (fun f => ⟨e, k, .rel f⟩) (relOkE cd.w cd.dag cd.consts ar cs [])

/-- **Cuts `s, …, s + n − 1` of node `k` of entry `e`** (`n = 0`: every cut from `s` on), accepted
by the relational check: a node too large for one kernel check is checked in slices. -/
@[expose] def nodeSliceE (e k s n : ℕ) : Except CertFailure Unit :=
  match ir.nodeCutsE c (cd.env ar) cd.table k with
  | .error r => .error ⟨e, k, r⟩
  | .ok cs => mapE (fun f => ⟨e, k, .rel f⟩)
    (relOkE cd.w cd.dag cd.consts ar (cond (Nat.beq n 0) (cs.drop s) ((cs.drop s).take n)) [])

/-- **The nodes `lo, …, lo + n − 1` of entry `e`.** -/
@[expose] def entryNodesE (e lo n : ℕ) : Except CertFailure Unit :=
  allE (fun _ k => ir.nodeOkE c ar cd e k) 0 (List.range' lo n)

/-- **The assertion items of a root `r`**: per coordinate `i`, `(Z, U, W r i)`. -/
@[expose] def rootItems (r : ℕ) (as : List Assert) : List (ℕ × ℕ × TE) :=
  List.zipWith Assert.item as (cd.table.get r).wires

/-- **An asserted item read as a multiple of its asserted node scales it by `±1`**: an item with an
asserted node (`Z ≠ 0`) whose tree expression is `0 + c · U` has `c` the code `1` or `−1`, so the
asserted node is zero exactly when the item is. -/
@[expose] def unitScaleB (z : ℕ × ℕ × TE) : Bool :=
  Nat.beq z.1 0 || !(z.2.2.scalesNode z.2.1) ||
    match z.2.2 with
    | .wire _ c1 _ => Nat.beq c1 1 || Nat.beq c1 cd.neg1
    | _ => true

/-- **The head of entry `k`**: its block continues the previous one within the table; its root
(cut, one assertion pair per coordinate) and assertion pairs accepted by the
relational check; its meaning (`entryMeaningB`) at the root's print. An entry with no root is an
alignment or realization entry: its family record's head (`famHeadE`). -/
@[expose] def entryHeadE (k : ℕ) : Except CertFailure Unit :=
  let en := cd.entries.getD k default
  let prevHi := cond (Nat.beq k 0) 0 (cd.entries.getD (k - 1) default).hi
  let ce := (ir.circuit c).entries.getD k default
  let env := cd.env ar
  seqE (guardE (Nat.beq en.entry k && Nat.beq en.lo prevHi && Nat.ble en.lo en.hi &&
      Nat.ble en.hi cd.table.size) ⟨k, en.lo, .partition⟩)
    (match en.root with
     | some r =>
       seqE (guardE (Nat.blt r cd.table.size && (cd.table.get r).cut &&
           Nat.beq en.asserts.length (cd.table.get r).len &&
           (rootItems cd r en.asserts).all (unitScaleB cd))
           ⟨k, r, .root⟩)
         (seqE (mapE (fun f => ⟨k, r, .rel f⟩)
             (relOkE cd.w cd.dag cd.consts ar []
               (rootItems cd r en.asserts)))
           (guardE (ir.entryMeaningB c cd.chr cd.neg1 ce (some (cd.table.print env r)))
             ⟨k, r, .meaning⟩))
     | none =>
       match en.fam with
       | some f => ir.famHeadE c ar cd k f
       | none => .error ⟨k, 0, .meaning⟩)

/-- **Entry `k` checks**, as its failure-reporting twin: its head, its block's nodes, and its family
cuts. -/
@[expose] def entryCertE (k : ℕ) : Except CertFailure Unit :=
  let en := cd.entries.getD k default
  seqE (ir.entryHeadE c ar cd k)
    (seqE (ir.entryNodesE c ar cd k en.lo (en.hi - en.lo)) (ir.famSliceE c ar cd k 0 0))

/-- Defining equation for `entryCertE`. -/
theorem entryCertE_eq (k : ℕ) :
    ir.entryCertE c ar cd k = (let en := cd.entries.getD k default
  seqE (ir.entryHeadE c ar cd k)
    (seqE (ir.entryNodesE c ar cd k en.lo (en.hi - en.lo)) (ir.famSliceE c ar cd k 0 0))) := rfl

/-- **Entry `k` checks.** -/
@[expose] def entryCertB (k : ℕ) : Bool := okB (ir.entryCertE c ar cd k)

/-- Defining equation for `entryCertB`. -/
theorem entryCertB_eq (k : ℕ) :
    ir.entryCertB c ar cd k = (okB (ir.entryCertE c ar cd k)) := rfl

/-- **Every asserted DAG node is some entry's** (merge-join against the sorted nonzero `Z`s). -/
@[expose] def assertsCoveredB : Bool :=
  subsetSorted cd.dag.asserts
    (sortNat ((cd.entries.flatMap fun en => en.asserts.map (·.Z)).filter fun z => !(z == 0)))

/-- Defining equation for `assertsCoveredB`. -/
theorem assertsCoveredB_eq  :
    assertsCoveredB cd = (subsetSorted cd.dag.asserts
    (sortNat ((cd.entries.flatMap fun en => en.asserts.map (·.Z)).filter fun z => !(z == 0)))) := rfl

/-- **Every asserted DAG node is an assertion `0 · 1 · U`**: one term, constant `0`, first operand
the constant one (node `0`). -/
@[expose] def assertTermsB : Bool :=
  cd.dag.asserts.all fun z =>
    match nodeTerms cd.w cd.dag z with
    | [t] => Nat.beq t.k 0 && Nat.beq t.a 0
    | _ => false

/-- Defining equation for `assertTermsB`. -/
theorem assertTermsB_def  :
    assertTermsB cd = (cd.dag.asserts.all fun z =>
    match nodeTerms cd.w cd.dag z with
    | [t] => Nat.beq t.k 0 && Nat.beq t.a 0
    | _ => false) := rfl

/-- **Asserted node `z` is an assertion `0 · 1 · U`** (`assertTermsB` at one node). -/
@[expose] def assertTermOk (z : ℕ) : Bool :=
  match nodeTerms cd.w cd.dag z with
  | [t] => Nat.beq t.k 0 && Nat.beq t.a 0
  | _ => false

/-- Defining equation for `assertTermOk`. -/
theorem assertTermOk_eq (z : ℕ) :
    assertTermOk cd z = (match nodeTerms cd.w cd.dag z with
  | [t] => Nat.beq t.k 0 && Nat.beq t.a 0
  | _ => false) := rfl

/-- **Part 9 at the asserted nodes `[s, s + n)`** (from `s` on when `n = 0`). -/
@[expose] def assertTermsSliceB (s n : ℕ) : Bool := (sliceL cd.dag.asserts s n).all (assertTermOk cd)

/-- Defining equation for `assertTermsSliceB`. -/
theorem assertTermsSliceB_eq (s n : ℕ) :
    assertTermsSliceB cd s n = ((sliceL cd.dag.asserts s n).all (assertTermOk cd)) := rfl

/-- **The entries' nonzero asserted nodes**, in entry order (part 6's list before its sort). -/
@[expose] def entryAssertNodes : List ℕ :=
  (cd.entries.flatMap fun en => en.asserts.map (·.Z)).filter fun z => !(z == 0)

/-- Defining equation for `entryAssertNodes`. -/
theorem entryAssertNodes_eq  :
    entryAssertNodes cd = ((cd.entries.flatMap fun en => en.asserts.map (·.Z)).filter fun z => !(z == 0)) := rfl

/-- **Part 6 without the sort**: the merge-join of the asserted nodes against the entries' nonzero
asserted nodes in entry order, which accepts when those do not decrease (repeats included), as the
compiler numbers them
(`headerPartB_six`). -/
@[expose] def assertsCoveredMergeB : Bool := subsetSorted cd.dag.asserts (entryAssertNodes cd)

/-- Defining equation for `assertsCoveredMergeB`. -/
theorem assertsCoveredMergeB_eq  :
    assertsCoveredMergeB cd = (subsetSorted cd.dag.asserts (entryAssertNodes cd)) := rfl

/-- **The header of circuit `c`'s certificate**, as its twin: the circuit's index; the constant of
index `1` is the code `1`; the constant one is a public input; the scheduling
certificate (`check`) at the DAG's width; one assertion per gate and the shape at the circuit's
width and layers (the bridge); the layered circuit's inputs the circuit's input count; the node
table's check against the printed program; the environment's codes; one block per entry of the
circuit, the last ending at the table's size; every asserted DAG node an entry's; every challenge's
value in the challenge's field; no DAG output node; every asserted node an assertion `0 · 1 · U`. -/
@[expose] def headerEC : Except CertFailure Unit :=
  let env := cd.env ar
  let n := cd.entries.length
  seqE (guardE (Nat.beq cd.c c && Nat.beq cd.sched.width cd.w &&
      Nat.beq cd.layered.inputs (ir.circuit c).inputCount && Nat.beq (cd.consts.code 1) 1 &&
      Nat.blt 0 (ir.circuit c).publicInputs) ⟨0, 0, .header⟩)
    (seqE (guardE (check cd.dag cd.layered cd.sched) ⟨0, 1, .header⟩)
      (seqE (guardE (uniqueAssertsB cd.w cd.layered &&
          shapeB cd.layered (ForkReader.circW ir c) (ir.circuit c).layers) ⟨0, 2, .header⟩)
        (seqE (guardE (ir.emitTableOkB env cd.table) ⟨0, 3, .header⟩)
          (seqE (guardE env.arithB ⟨0, 4, .header⟩)
            (seqE (guardE (Nat.beq n (ir.circuit c).entries.length &&
                Nat.beq (cond (Nat.beq n 0) 0 (cd.entries.getD (n - 1) default).hi) cd.table.size)
                ⟨0, 5, .partition⟩)
              (seqE (guardE (assertsCoveredB cd) ⟨0, 6, .header⟩)
                (seqE (guardE ir.chalFieldsB ⟨0, 7, .header⟩)
                  (seqE (guardE cd.dag.outputs.isEmpty ⟨0, 8, .header⟩)
                    (guardE (assertTermsB cd) ⟨0, 9, .header⟩)))))))))

/-- The compiled header, using the numeric circuit width. -/
@[expose] def headerBC : Bool := okB (ir.headerEC c ar cd)

/-- The compiled circuit check; the kernel header is related by the circuit-width equation. -/
@[expose] def circuitCertBC : Bool :=
  ir.headerBC c ar cd && (List.range cd.entries.length).all (ir.entryCertB c ar cd)

/-- Defining equation for the compiled header. -/
theorem headerEC_eq : ir.headerEC c ar cd = (let env := cd.env ar
  let n := cd.entries.length
  seqE (guardE (Nat.beq cd.c c && Nat.beq cd.sched.width cd.w &&
      Nat.beq cd.layered.inputs (ir.circuit c).inputCount && Nat.beq (cd.consts.code 1) 1 &&
      Nat.blt 0 (ir.circuit c).publicInputs) ⟨0, 0, .header⟩)
    (seqE (guardE (check cd.dag cd.layered cd.sched) ⟨0, 1, .header⟩)
      (seqE (guardE (uniqueAssertsB cd.w cd.layered &&
          shapeB cd.layered (ForkReader.circW ir c) (ir.circuit c).layers) ⟨0, 2, .header⟩)
        (seqE (guardE (ir.emitTableOkB env cd.table) ⟨0, 3, .header⟩)
          (seqE (guardE env.arithB ⟨0, 4, .header⟩)
            (seqE (guardE (Nat.beq n (ir.circuit c).entries.length &&
                Nat.beq (cond (Nat.beq n 0) 0 (cd.entries.getD (n - 1) default).hi) cd.table.size)
                ⟨0, 5, .partition⟩)
              (seqE (guardE (assertsCoveredB cd) ⟨0, 6, .header⟩)
                (seqE (guardE ir.chalFieldsB ⟨0, 7, .header⟩)
                  (seqE (guardE cd.dag.outputs.isEmpty ⟨0, 8, .header⟩)
                    (guardE (assertTermsB cd) ⟨0, 9, .header⟩)))))))))) := rfl

/-- Defining equation for the compiled header verdict. -/
theorem headerBC_eq : ir.headerBC c ar cd = okB (ir.headerEC c ar cd) := rfl

/-- Defining equation for the compiled circuit verdict. -/
theorem circuitCertBC_eq : ir.circuitCertBC c ar cd =
    (ir.headerBC c ar cd && (List.range cd.entries.length).all (ir.entryCertB c ar cd)) := rfl

end Entries

end GordieHowe.RealizedProgram
