-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Codecs
public meta import GordieHoweNative.Codecs

public section

/-! # Rejection of unknown tags in `.ghc` files

The container (`Ghc.sections`) rejects a section whose flags set a bit outside `Ghc.knownFlags`,
and every reader of a natural rejects a non-minimal LEB128 encoding, so a tag has one encoding.
The type-directed decoders reject an unknown constructor index (derived inductives, `Bool`,
`Option`, `Ty`), an unknown spine tag, and a section of a type outside the registry. The same
files with known tags decode. These are decoder tests, not proof axioms.
-/

namespace GordieHoweTest.GhcMalformed

open GordieHowe.Ghc GordieHowe.RealizedProgram

open Lean Elab Command in
run_cmd do
  /- A value of `α` read from `bytes` by `d`, every byte consumed. -/
  let run {α : Type} (d : D α) (bytes : Array UInt8) : Except String α :=
    match (d.run 0).run { bytes := ByteArray.mk bytes } with
    | .ok (x, pos) => if pos == bytes.size then .ok x else .error "trailing bytes"
    | .error e => .error e
  let rejects {α : Type} (what : String) (r : Except String α) : CommandElabM Unit :=
    match r with
    | .error _ => pure ()
    | .ok _ => throwError "accepted: {what}"
  let accepts {α : Type} (what : String) (r : Except String α) : CommandElabM Unit :=
    match r with
    | .ok _ => pure ()
    | .error e => throwError "rejected: {what}: {e}"
  -- Naturals: minimal encodings decode, a zero last group of a multi-byte natural is rejected.
  unless (run nat #[0x85, 0x01]).toOption == some 133 do throwError "133 misread"
  unless (run nat #[0x00]).toOption == some 0 do throwError "0 misread"
  rejects "natural 0 as 0x80 0x00" (run nat #[0x80, 0x00])
  rejects "natural 5 as 0x85 0x00" (run nat #[0x85, 0x00])
  rejects "natural 5 as 0x85 0x80 0x00" (run nat #[0x85, 0x80, 0x00])
  -- Constructor tags of the primitive inductives and of type descriptors.
  rejects "Bool 2" (run (Decode.dec (α := Bool)) #[2])
  rejects "Bool 1 as 0x81 0x00" (run (Decode.dec (α := Bool)) #[0x81, 0x00])
  rejects "Option tag 2" (run (Decode.dec (α := Option Nat)) #[2, 5])
  rejects "Ty tag 2" (run ty #[2, 0])
  -- Constructor tags of derived inductives: `NttOrder` has 2 constructors, `ConvForm` 3.
  accepts "NttOrder 1" (run (Decode.dec (α := NttOrder)) #[1])
  rejects "NttOrder 2" (run (Decode.dec (α := NttOrder)) #[2])
  rejects "NttOrder 0 as 0x80 0x00" (run (Decode.dec (α := NttOrder)) #[0x80, 0x00])
  accepts "ConvForm.ntt 7" (run (Decode.dec (α := ConvForm)) #[1, 7])
  rejects "ConvForm 3" (run (Decode.dec (α := ConvForm)) #[3, 7])
  rejects "ConvForm 3 in spine form" (run (Decode.spine (α := ConvForm)) #[2, 3, 7])
  rejects "ConvForm 3 as an expression" (run (Decode.spineE (α := ConvForm)) #[2, 3, 7])
  -- Spine tags.
  accepts "spine tag 0" (run (Decode.spine (α := ConvForm)) #[0, 0])
  rejects "spine tag 3" (run (Decode.spine (α := ConvForm)) #[3, 0])
  rejects "spine tag 3 of an expression" (run (Decode.spineE (α := Nat)) #[3, 0])
  -- Section flags: a one-section file `n : Nat := 5` with each flag value.
  let file (flags : Array UInt8) (tyName : String := "Nat") : ByteArray :=
    ByteArray.mk (#[0x47, 0x48, 0x43, 3, 1, 'n'.toUInt8, 0, tyName.length.toUInt8] ++
      tyName.toUTF8.data ++ flags ++ #[1, 5, 0])
  for f in ([0, 1, 2, 4, 7] : List UInt8) do
    match sections (file #[f]) with
    | .ok secs =>
      unless secs.size == 1 && secs[0]!.flags == f.toNat do throwError "flags {f} misread"
    | .error e => throwError "flags {f} rejected: {e}"
  for f in ([#[8], #[9], #[64], #[0x88, 0x01], #[0x80, 0x00]] : List (Array UInt8)) do
    rejects s!"flags {f}" (sections (file f))
  -- A section of a type outside the registry, and one read at another type.
  match sections (file #[0] "Foo") with
  | .ok secs =>
    rejects "a section of type Foo" (loadDefs sectionTypes `T (file #[0] "Foo") secs
      (fun _ => none) #[])
  | .error e => throwError "the container of a Foo section rejected: {e}"
  let ok := file #[0]
  match sections ok with
  | .ok secs =>
    accepts "a Nat section" (loadDefs sectionTypes `T ok secs (fun _ => none) #[])
    unless (decodeSection (α := Nat) { bytes := ok, secs } 0).toOption == some 5 do
      throwError "the Nat section misread"
    rejects "a Nat section read as a Bool" (decodeSection (α := Bool) { bytes := ok, secs } 0)
  | .error e => throwError "a Nat section rejected: {e}"

end GordieHoweTest.GhcMalformed
