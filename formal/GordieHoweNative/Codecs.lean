-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Terms
public import GordieHoweNative.Language.RealizedProgram.Annotations
public import GordieHoweNative.Language.Completeness.Deriv
public meta import GordieHoweNative.Derive

public section

/-!
# GordieHowe: the decoders of the certificate types, and the section types

Every type of `Data.lean` gets its `.ghc` decoder by derivation (`Derive.lean`); `IndexMap`'s is the
override of `Ghc.lean`. `sectionTypes` lists the types a section may have, which `load_ghc` reads.
A new kind of certificate data adds its types to this library, derives their decoders here and
lists its section types.
-/

namespace GordieHowe.Ghc

open GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Certificate GordieHowe.GKR.Fold

deriving instance Decode for Coef
deriving instance Decode for ConvForm
deriving instance Decode for NttOrder
deriving instance Decode for NamedOp
deriving instance Decode for Wire
deriving instance Decode for Place
deriving instance Decode for NTree
deriving instance Decode for GKR.Certificate.Table
deriving instance Decode for Layered
deriving instance Decode for Cert
deriving instance Decode for BinOp
deriving instance Decode for CmpOp
deriving instance Decode for CmpArg
deriving instance Decode for EOp
deriving instance Decode for ETerm
deriving instance Decode for ENode
deriving instance Decode for ENodeInfo
deriving instance Decode for Trie
deriving instance Decode for ETable
deriving instance Decode for Assert
deriving instance Decode for Dag
deriving instance Decode for Frac
deriving instance Decode for FracTree
deriving instance Decode for LogupCert
deriving instance Decode for MacHCert
deriving instance Decode for FamCert
deriving instance Decode for EntryCert
deriving instance Decode for Consts
deriving instance Decode for CircuitData

/-- The numeral spelling retained by ordinary Lean constructor literals. -/
def printedNatE (n : Nat) : Lean.Expr :=
  Lean.mkApp3 (Lean.mkConst ``OfNat.ofNat [Lean.Level.zero]) (Lean.mkConst ``Nat)
    (Lean.mkRawNatLit n) (Lean.mkApp (Lean.mkConst ``instOfNatNat) (Lean.mkRawNatLit n))

/-- Program certificates retain their original value expressions; existing GKR sections keep raw
literals. Only expression construction differs: both decoders read the same Nat bytes and value. -/
@[instance_reducible] def printedNatDecode : Decode Nat :=
  { (inferInstance : Decode Nat) with
    toE := printedNatE
    spineE := spineEWith (.const "Nat") printedNatE nat (throw "Nat: no constructor form") }

section
attribute [local instance] printedNatDecode
deriving instance Decode for ExprAnn
deriving instance Decode for Gen
end

/-- The binary let tree used by Lean's `%[... | tail]` list notation. The elements and their
type are closed; the tail may reference an enclosing let. -/
partial def printedListTree (t : Lean.Expr) (xs : Array Lean.Expr) (tail : Lean.Expr) : Lean.Expr :=
  if xs.size < 8 then
    xs.foldr (fun x rest => Lean.mkApp3 (Lean.mkConst ``List.cons [Lean.Level.zero]) t x rest) tail
  else
    let m := xs.size / 2
    .letE `y (Lean.mkApp (Lean.mkConst ``List [Lean.Level.zero]) t)
      (printedListTree t (xs.extract m xs.size) tail)
      (printedListTree t (xs.extract 0 m) (.bvar 0)) true

/-- The expression of the compiler's list notation, which has no trailing comma. Lean switches
from a cons chain to binary lets when the syntax has at least 64 elements and separators,
that is, at 33 list elements. -/
def printedListE (t : Lean.Expr) (xs : Array Lean.Expr) : Lean.Expr :=
  if xs.size <= 32 then listE t xs
  else printedListTree t xs (Lean.mkApp (Lean.mkConst ``List.nil [Lean.Level.zero]) t)

/-- A list decoder retaining the compiler's printed literal expression. Its wire format and
runtime reader are unchanged; only expression construction uses the list notation's let tree. -/
@[instance_reducible] def printedListDecode (α : Type) [Decode α] : Decode (List α) :=
  let toE (xs : List α) := printedListE (Decode.tyE (α := α)) (xs.toArray.map Decode.toE)
  { (inferInstance : Decode (List α)) with
    toE
    spineE := spineEWith (tyOf (listTyE (α := α))) toE listDec
      (do pure (printedListE (Decode.tyE (α := α)) (← itemsE (← nat) (Decode.spineE (α := α))))) }

section
attribute [local instance] printedNatDecode
local instance : Decode (List Nat) := printedListDecode Nat

deriving instance Decode for LogicOp
deriving instance Decode for RealizedProgram.Expr
deriving instance Decode for IvlSrc
deriving instance Decode for LinOpStep
deriving instance Decode for Step
deriving instance Decode for MacRole
deriving instance Decode for CStep

local instance : Decode (List CStep) := printedListDecode CStep
local instance : Decode (List (List CStep)) := printedListDecode (List CStep)
deriving instance Decode for CDerivations
end

/-- The completeness derivations retain their original constructor and list expressions. -/
def cderivsEntry : Entry :=
  { Entry.of CDerivations with splitLists := false }

/-- The generator list keeps the original `Gens` alias in its declaration type and its whole
literal body. The wire type and reader remain those of `List Gen`. -/
def gensEntry : Entry :=
  letI := printedListDecode Gen
  { Entry.of (List Gen) with tyE := Lean.mkConst ``Gens, splitLists := false }

/-- The honest nodes retain the original list of pairs, including ordinary numeral spelling.
Their wire format and runtime reader are those of `List (Nat × String)`. -/
def nodesEntry : Entry :=
  letI := printedNatDecode
  letI := printedListDecode (Nat × String)
  { Entry.of (List (Nat × String)) with splitLists := false }

/-- **The types a section may have**: a GKR circuit's certificate and its parts, and the
realized program's packed annotations, completeness certificate, honest nodes and assignment-read hints. -/
def sectionTypes : Array Entry := #[
  .of Nat, .of (List Nat), .of Consts, .of NTree, .of Dag, .of GKR.Certificate.Table, .of Layered,
  .of Cert, .of (Trie ENodeInfo), .of ETable, .of (List EntryCert), .of CircuitData, .of ExprAnn,
  gensEntry, nodesEntry, cderivsEntry, .of (List (List Nat))]

end GordieHowe.Ghc
