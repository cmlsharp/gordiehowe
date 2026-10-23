-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.System.Algebra
public import GordieHowe.Language.Realizations.MACEquality
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Applications.MLDSA44.PoP.Relation
public import GordieHowe.Applications.MLDSA44.System.MAC

@[expose] public section

/-!
# ML-DSA native: the application constraints

The application constraints of ML-DSA native (`lib/gordiehowe/examples/mldsa/mldsa_native.h`,
`mldsa_hash.h`, `mldsa_gadgets.h`) on the source assignment at a statement (`AppConstraints`): the
hash constraints of domain H at the statement's `tr` and the algebra constraints of domain A at its
key.

The field data, the statement and the stream readings, which ML-DSA emulated also uses, are in
`GordieHowe/Applications/MLDSA44/System/MAC.lean`.
-/

namespace GordieHowe.MLDSA44.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout Range Params
open GordieHowe (MaskSubfield)
open scoped NNReal ENNReal

variable (P : Profile) (KH F S : Type) [Field KH] [Fintype KH] [DecidableEq KH] [Field F]
  [Fintype F] [DecidableEq F] [Field S] [Fintype S]

variable {P KH F S}

variable (P) (σ : MaskSubfield S F)

variable {P}

variable (D : FieldData P KH F S) (msgLen : ℕ)

variable [CharP F _root_.MLDSA.modulus]

/-! ### The application constraints -/

section App

variable {msgLen}

/-- **The application constraints** on the source assignment at a statement: the hash constraints
of domain H at the statement's `tr` and the algebra constraints of domain A at its key. -/
structure AppConstraints (x : Statement) (a : Source KH F msgLen) : Prop where
  /-- The hash constraints. -/
  hash : HashConstraints D.packing (trWires x) a.msg a.w1H a.states
  /-- The algebra constraints. -/
  algebra : AlgebraConstraints x.pk a

end App

end GordieHowe.MLDSA44.Native
