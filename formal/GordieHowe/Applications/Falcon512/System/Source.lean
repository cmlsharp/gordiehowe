-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.System.Hash
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Falcon512.System.Params

@[expose] public section

/-!
# Falcon: the statement

The statement of both Falcon configurations (`PublicKey`): a Falcon-512 public key. Each
configuration's source assignment (the variables the application declares, by domain, before the
randomized lowerings) is its own; Falcon native's is `GordieHowe.Falcon512.Native.Source`
(`GordieHowe/Applications/Falcon512/Native/System/Source.lean`).
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits Params

/-- The statement: a Falcon-512 public key. -/
abbrev PublicKey : Type := _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512

/-- **Equality of statements is decidable**: two public keys are equal when their polynomials `h`
are, compared coefficient by coefficient. -/
instance : DecidableEq PublicKey := fun a b =>
  decidable_of_iff (a.h = b.h) ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

end GordieHowe.Falcon512.Emulated
