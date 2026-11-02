-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.Rel

/-!
# The certificate of a GKR circuit's emission, as the relational check reads it

The C++ emitter exports, per circuit, the scheduling DAG `D` (`GKR.Certificate.Dag`, with its
layered circuit and scheduling certificate), the node table of the trees it emitted (one node per
emitted expression node or value read), and, per node-table coordinate, the wire it produced
(`GKR.Rel.Wire`). Per circuit entry it exports a block (`EntryCert`): the node ids the entry
introduced, its asserted root, and per coordinate of the root the assertion pair (`Assert`).

An alignment or realization entry also carries its family record (`FamCert`): the filler block an
alignment entry asserts, or a realization's raw-call results (a LogUp's fraction tree, a MAC H's
chunks) as wires, with pointers to the table nodes and input block it reads.

Every field is a pointer the checker verifies; none is trusted. A value leaf of the node table
names where the circuit reads the value (`Place`): the input block holding it, the message and pad
blocks of a late value, or the node computing a value's definition.

The types are in `GordieHoweNative/Data.lean`; this module has the definitions the certificate
checkers run on them, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to a
shared library (`precompileModules`): native mode runs the checkers as compiled code.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.GKR.Rel

/-- **The relational check's assertion item** for coordinate wire `W` of the root: `(Z, U, W)`. -/
def Assert.item (a : Assert) (W : Wire) : ℕ × ℕ × TE := (a.Z, a.U, .wire W.c0 W.c1 W.n)

end GordieHowe.GKR.Rel
