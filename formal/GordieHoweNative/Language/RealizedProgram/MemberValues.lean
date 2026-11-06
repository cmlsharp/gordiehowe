-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Annotations

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.MemberValues`

The definitions of `GordieHowe.Language.RealizedProgram.MemberValues` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/MemberValues.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open GordieHowe.Twin

/-- **The member checks' values** (`Structure.memberValues`), keyed by the check's index, as a table
built once. -/
def Structure.memberValueTab (S : Structure) : NatTrie ℕ := NatTrie.ofList S.memberValues

/-- The pointer lookup table is built from the emitted member-value entries. -/
theorem Structure.memberValueTab_eq (S : Structure) :
    S.memberValueTab = NatTrie.ofList S.memberValues := rfl

section

variable (ir : RealizedProgram)

/-- **Whether value `x` is the statement member `member`** (`isMemberOf`, on the value). -/
def isMemberV (member : String) (x : Value) : Bool :=
  match x.kind with
  | .pub (.«opaque» name []) => name == "statement." ++ member || name == member
  | _ => false

/-- **Check `m` holds at value `v`**: `CheckOk`'s arms, the value given. -/
def checkAtB (v : ℕ) (m : MemberCheck) : Bool :=
  match m.kind? with
  | some (.below _ w) => decide (m.bytes = w * (ir.value v).size)
  | some .p256Point => decide (m.bytes = 64 ∧ (ir.value v).size = 2 ∧
      (ir.field (ir.valueField v)).characteristic = p256Prime ∧
      (ir.field (ir.valueField v)).degree = 1)
  | some (.limbBits b w L) => decide (m.bytes * 8 = b ∧ (ir.value v).size = L ∧
      b ≤ w * L ∧ 2 ^ w ≤ (ir.field (ir.valueField v)).characteristic)
  | none => false

/-- **Check `k` (`m`) at its pointer `v`**: `v` is a value that is the member (`notMember`), no
earlier value is (`earlierMember`, a sweep of the values naming the earlier one), and the check
holds at `v` (`checkFails`). -/
def memberAtE (k : ℕ) (m : MemberCheck) (v : ℕ) : Except StructFailure Unit :=
  seqE (guardE (decide (v < ir.values.length) && ir.isMemberOf m.member v) ⟨k, v, .notMember⟩) <|
    seqE (allE (fun w x => guardE (decide (v ≤ w) || !isMemberV m.member x)
        ⟨k, w, .earlierMember⟩) 0 ir.values)
      (guardE (ir.checkAtB v m) ⟨k, v, .checkFails⟩)

/-- **The `memberValues` records check**: every member check has an entry (`noRecord`), checked at
its pointer (`memberAtE`). -/
def memberValuesE (S : Structure) : Except StructFailure Unit :=
  allE (fun k m =>
    match S.memberValueTab.get? k with
    | some v => ir.memberAtE k m v
    | none => .error ⟨k, 0, .noRecord⟩) 0 ir.statement.checks

/-- **`memberValuesE` as a `Bool`.** -/
def memberValuesB (S : Structure) : Bool := okB (ir.memberValuesE S)

end

end GordieHowe.RealizedProgram
