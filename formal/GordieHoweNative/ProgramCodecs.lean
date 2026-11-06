-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Codecs
public import GordieHoweNative.Language.RealizedProgram.Structure
public import Lean.Environment
public meta import GordieHoweNative.Derive

public section

/-!
# Program literal sections

The program registry preserves the constructor expressions of compiler-printed literals.
It is selected explicitly by `load_program_ghc`; the default GKR registry is unchanged.
Both profiles use the same wire values and runtime decoders. Only the kernel-checked
expressions of the loaded definitions differ in numeral spelling and list notation.
-/

namespace GordieHowe.Ghc

open Lean GordieHowe.RealizedProgram

deriving instance Decode for RealCircuit
deriving instance Decode for Fact
deriving instance Decode for SharedEntry
deriving instance Decode for GadgetKind
deriving instance Decode for GadgetPart
deriving instance Decode for Gadget
deriving instance Decode for Origin
deriving instance Decode for Route
deriving instance Decode for IvlSource
deriving instance Decode for Structure

/-- The compiler's literal spelling of a decoded value of `ty`. Expected field types come from
constructor metadata; implicit type arguments and named references are retained. Index-map
stand-ins must already have been replaced by their named constants. Unknown applications reject. -/
partial def programLiteralExpr (env : Environment) (ty e : Lean.Expr) : Except String Lean.Expr := do
  if e.isConst || e.isBVar then return e
  if ty == mkConst ``String && e.isLit then return e
  if ty == mkConst ``Nat then
    match e with
    | .lit (.natVal n) => return printedNatE n
    | _ =>
      if e.isAppOfArity ``OfNat.ofNat 3 && e.getArg! 0 == ty then return e
      throw "Nat: unsupported literal expression"
  if ty == mkConst ``Int then
    if e.isAppOfArity ``OfNat.ofNat 3 && e.getArg! 0 == ty then return e
    if e.isAppOfArity ``Neg.neg 3 && e.getArg! 0 == ty then
      let v := e.getArg! 2
      if v.isAppOfArity ``OfNat.ofNat 3 && v.getArg! 0 == ty then
        if let .lit (.natVal (n + 1)) := v.getArg! 1 then
          return mkApp (mkConst ``Int.negSucc) (printedNatE n)
    throw "Int: unsupported literal expression"
  if let .letE n t v b nondep := e then
    return .letE n t (← programLiteralExpr env t v)
      (← programLiteralExpr env ty b) nondep
  if ty.isAppOfArity ``List 1 then
    if e.isAppOfArity ``List.nil 1 then return e
    if e.isAppOfArity ``List.cons 3 then
      let (xs, tail) := consChain e
      let xs ← xs.mapM (programLiteralExpr env (ty.getArg! 0))
      if tail.isAppOfArity ``List.nil 1 then
        return printedListE (ty.getArg! 0) xs
      -- Preserve tails bound by a pre-existing printed-list let expression.
      if tail.isBVar || tail.isConst then
        return xs.foldr (fun x rest => mkApp3 (mkConst ``List.cons [Level.zero])
          (ty.getArg! 0) x rest) tail
      throw "List: unsupported literal tail"
  let f := e.getAppFn
  let .const name levels := f | throw "unsupported literal head"
  let some (.ctorInfo ctor) := env.find? name | throw s!"unsupported literal constructor {name}"
  let mut ctorTy := ctor.type.instantiateLevelParams ctor.levelParams levels
  let mut args : Array Lean.Expr := #[]
  for arg in e.getAppArgs do
    let .forallE _ argTy body bi := ctorTy | throw "constructor arity mismatch"
    let argNew ← if bi.isExplicit then programLiteralExpr env argTy arg else pure arg
    args := args.push argNew
    ctorTy := body.instantiate1 arg
  return mkAppN f args

/-- A program section with unchanged public type and reader, retaining its literal expression
instead of introducing auxiliary list definitions. -/
def programEntry (env : Environment) (α : Type) [Decode α] : Entry :=
  let entry := Entry.of α
  let formatExpr (read : D Lean.Expr) : D Lean.Expr := do
    match programLiteralExpr env entry.tyE (← read) with
    | .ok e => pure e
    | .error error => throw error
  { entry with
    plainE := formatExpr entry.plainE
    spineE := formatExpr entry.spineE
    splitLists := false }

/-- The derivation and structure payload types. Their public declaration types retain exactly these expressions;
this registry is independent of the default GKR registry, including its `List Nat` entry. -/
def programSectionTypes (env : Environment) : Array Entry := #[
  programEntry env (List (Nat × List Step)), programEntry env (List Nat),
  programEntry env (List SharedEntry), programEntry env (List (Nat × List (Nat × List Step))),
  programEntry env Structure]

end GordieHowe.Ghc
