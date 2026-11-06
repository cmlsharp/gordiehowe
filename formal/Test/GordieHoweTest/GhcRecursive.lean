-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Codecs
public meta import GordieHoweNative.Codecs
public meta import GordieHoweNative.Derive
public meta import GordieHoweNative.Language.Completeness.Deriv
public meta import GordieHoweNative.Language.RealizedProgram

public section

/-! # Recursive certificate decoders

A parameterized tree exercises direct recursion and recursion through a list, including both
spine forms and rejection of malformed nested data. These are decoder tests, not proof axioms.
-/

namespace GordieHoweTest.GhcRecursive

open GordieHowe.Ghc

/-- A recursive codec fixture with a type parameter. -/
inductive Tree (α : Type) where
  | leaf (value : α)
  | pair (left right : Tree α)
  | forest (children : List (Tree α))
  deriving Repr, Inhabited

deriving instance Decode for Tree

open Lean Elab Command in
run_cmd do
  let expected : Tree Nat := .forest [.leaf 7, .pair (.leaf 8) (.forest [])]
  let plain := ByteArray.mk #[2, 2, 0, 7, 1, 0, 8, 2, 0]
  let inline := ByteArray.mk #[2, 2, 2, 2, 2, 0, 0, 7, 2, 1, 2, 0, 0, 8, 2, 2, 2, 0]
  let check (bytes : ByteArray) (reader : D (Tree Nat)) := do
    match reader.run 0 |>.run { bytes } with
    | .ok (actual, pos) =>
      unless Decode.toE actual == Decode.toE expected && pos == bytes.size do
        throwError "recursive value or consumed byte count differs"
    | .error e => throwError e
  check plain Decode.dec
  check (ByteArray.mk #[0] ++ plain) Decode.spine
  check inline Decode.spine
  for bytes in [ByteArray.mk #[0] ++ plain, inline] do
    match (Decode.spineE (α := Tree Nat)).run 0 |>.run { bytes } with
    | .ok (actual, pos) =>
      unless actual == Decode.toE expected && pos == bytes.size do
        throwError "recursive expression or consumed byte count differs"
    | .error e => throwError e
  for bytes in [ByteArray.mk #[2, 1, 9], ByteArray.mk #[2, 1, 0]] do
    match (Decode.dec (α := Tree Nat)).run 0 |>.run { bytes } with
    | .error _ => pure ()
    | .ok _ => throwError "malformed nested value was accepted"
  match (Decode.spine (α := Tree Nat)).run 0 |>.run { bytes := ByteArray.mk #[3] } with
  | .error _ => pure ()
  | .ok _ => throwError "invalid spine tag was accepted"

open Lean Elab Command in
run_cmd do
  let bytes := ByteArray.mk #[2, 1, 0, 7, 1, 0]
  let context : Ctx :=
    { bytes, cur := 1, names := #[`earlierTree],
      secs := #[{ name := "earlierTree", ty := tyOf (Decode.tyE (α := Tree Nat)),
                  flags := 0, off := 0, len := 4 }] }
  match (Decode.spine (α := Tree Nat)).run 4 |>.run context with
  | .ok (value, pos) =>
    unless Decode.toE value == Decode.toE (Tree.forest [.leaf (7 : Nat)]) && pos == 6 do
      throwError "recursive section reference changed its value or position"
  | .error e => throwError e
  match (Decode.spineE (α := Tree Nat)).run 4 |>.run context with
  | .ok (value, pos) =>
    unless value == mkConst `earlierTree && pos == 6 do
      throwError "recursive expression reference did not preserve its constant"
  | .error e => throwError e
  match (Decode.spine (α := Tree Nat)).run 4 |>.run { context with cur := 0 } with
  | .error _ => pure ()
  | .ok _ => throwError "forward recursive section reference was accepted"
  -- The complete schema also reads constructors not currently emitted by the compiler.
  let expected : GordieHowe.RealizedProgram.CStep :=
    .pure (.inDom 3 (.subst (.logic .lt 8 [.leaf 1, .leaf 2]) (.leaf 4)))
  let bytes := ByteArray.mk #[0, 29, 3, 1, 12, 0, 8, 2, 0, 1, 0, 2, 0, 4]
  match (Decode.dec (α := GordieHowe.RealizedProgram.CStep)).run 0 |>.run { bytes } with
  | .ok (value, pos) =>
    unless Decode.toE value == Decode.toE expected && pos == bytes.size do
      throwError "pure completeness step with nested expression differs"
  | .error e => throwError e

end GordieHoweTest.GhcRecursive
