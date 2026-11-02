-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Codecs
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

@[expose] public section

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert relOkE)

section Meaning

variable (ir : RealizedProgram)

/-- **The printed sides of a placed field equation**: an `equal`, or a `mod_q` with `q = 0` or in
the field form. -/
def placedSides? : PredBody → Option (ℕ × Expr × Expr)
  | .equal d l r _ => some (d, l, r)
  | .mod d q l r real =>
    if Nat.beq q 0 || decide (real.form = .field) then some (d, l, r) else none
  | _ => none

/-- **`X` is `Y` or `−Y`** (the code `neg1` times `Y`) as normal forms in domain `d`'s field of
characteristic `chr`, at every coordinate of `X`: with `A`, `B` the normal forms of `X` and `Y`
(`nfS`, shared expressions as atoms), `A − B` is zero, or `neg1 < chr` and `A − neg1 · B` is zero
(`zeroLoop`, unfolding shared expressions until the difference vanishes). -/
def nfUnitEqB (d chr neg1 : ℕ) («X» «Y» : Expr) : Bool :=
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
in the circuit's domain, `X` as long as `l` and `X = ±(l − r)` as normal forms; a placed
product form, `X` its asserted equation; an alignment entry, no root. A realization entry is
rejected. -/
def entryMeaningB (c chr neg1 : ℕ) (en : CircuitEntry) («X» : Option Expr) : Bool :=
  match en, «X» with
  | .alignment _, none => true
  | .typeCheck p, some «X» | .pred p, some «X» =>
    match placedSides? (ir.predicate p).body with
    | some (d, l, r) =>
      Nat.beq d (ir.circuit c).domain && Nat.beq (ir.exprLen l) (ir.exprLen «X») &&
        ir.nfUnitEqB d chr neg1 «X» (.sub l r)
    | none =>
      match (ir.predicate p).body with
      | .mod d q P N real =>
        real.form.isProduct && Nat.blt 2 q && Nat.beq d (ir.circuit c).domain &&
          ir.productEquationB d q «X» P N real
      | _ => false
  | _, _ => false

end Meaning

section Entries

variable (ir : RealizedProgram) (c : ℕ) (ar : CodeArith) (cd : CircuitData)

/-- **Node `k` of entry `e`**: its cuts, accepted by the relational check. -/
def nodeOkE (e k : ℕ) : Except CertFailure Unit :=
  match ir.nodeCutsE c (cd.env ar) cd.table k with
  | .error r => .error ⟨e, k, r⟩
  | .ok cs =>
    mapE (fun f => ⟨e, k, .rel f⟩) (relOkE cd.w cd.dag cd.consts ar cs [])

/-- **Cuts `s, …, s + n − 1` of node `k` of entry `e`** (`n = 0`: every cut from `s` on), accepted
by the relational check: a node too large for one kernel check is checked in slices. -/
def nodeSliceE (e k s n : ℕ) : Except CertFailure Unit :=
  match ir.nodeCutsE c (cd.env ar) cd.table k with
  | .error r => .error ⟨e, k, r⟩
  | .ok cs => mapE (fun f => ⟨e, k, .rel f⟩)
    (relOkE cd.w cd.dag cd.consts ar (cond (Nat.beq n 0) (cs.drop s) ((cs.drop s).take n)) [])

/-- **The nodes `lo, …, lo + n − 1` of entry `e`.** -/
def entryNodesE (e lo n : ℕ) : Except CertFailure Unit :=
  allE (fun _ k => ir.nodeOkE c ar cd e k) 0 (List.range' lo n)

/-- **The assertion items of a root `r`**: per coordinate `i`, `(Z, U, W r i)`. -/
def rootItems (r : ℕ) (as : List Assert) : List (ℕ × ℕ × TE) :=
  List.zipWith Assert.item as (cd.table.get r).wires

/-- **An asserted item read as a multiple of its asserted node scales it by `±1`**: an item with an
asserted node (`Z ≠ 0`) whose tree expression is `0 + c · U` has `c` the code `1` or `−1`, so the
asserted node is zero exactly when the item is. -/
def unitScaleB (z : ℕ × ℕ × TE) : Bool :=
  Nat.beq z.1 0 || !(z.2.2.scalesNode z.2.1) ||
    match z.2.2 with
    | .wire _ c1 _ => Nat.beq c1 1 || Nat.beq c1 cd.neg1
    | _ => true

/-- **The head of entry `k`**: its block continues the previous one within the table; its root
(cut, one assertion pair per coordinate) and assertion pairs accepted by the
relational check; its meaning (`entryMeaningB`) at the root's print. An entry with no root is an
alignment or realization entry: its family record's head (`famHeadE`). -/
def entryHeadE (k : ℕ) : Except CertFailure Unit :=
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

end Entries

end GordieHowe.RealizedProgram
