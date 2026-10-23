-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.CellsLowering
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Valid

@[expose] public section

/-!
# GordieHowe: the checks of `Falcon512.Native.ROMParams`

The decided checks of the realized program of the native Falcon proof of possession at the ROM parameters
(`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program`, export `c825eb05`: domain `H` over
`GF(2^128)` with the GKR circuit `c.H`, domain `A` over `F_q^9` with the GKR circuit `c.A`; the late
value `mac.value` of `H` and `mac.acc`, `mac.gq`, `range.dynamic:A.64` of `A`), by `decide`;
`GordieHowe.RealizedProgram.Derivable` is `GordieHowe.Generated.Falcon512.Native.ROMParams.Realize.derivable`:

* **the source part** (`sourceValid`, `GordieHowe.RealizedProgram.SourceValid`) and **the cells checks**
  (`cellsValid`, `GordieHowe.RealizedProgram.CellsValid`: the committing domains `A` and `H`, every field `equal` and
  `mod_0` lowered into its domain, the parts of the bits batch `h2p.shake.blocks.r0` among them,
  its affine part `h2p.shake.padding.output` padded to the batch's shape `a · b + c` (`Pad`), the
  LogUp identities in `c.A`, the H predicate `mac.H` an affine row of `H`);
* **locality** (`locality`, `GordieHowe.RealizedProgram.Local` through `GordieHowe.RealizedProgram.Local.of_localB`): every predicate of a
  domain reads only its domain (the cross-field `equal` `mac.equal` relates the two and is not
  checked), the placed predicates, the batches' parts and the LogUp identities are of their
  circuit's or batch's domain, every input block holds a value of its circuit's domain, every late
  value's pad space is a node of its domain's tree.
-/

namespace GordieHowe.Falcon512.Native.ROMParams.Locality

open Generated.Falcon512.Native.ROMParams.Program (program)

/-- **The source part is well formed** (`RealizedProgram.SourceValid`). -/
theorem sourceValid : program.SourceValid := by decide +kernel

/-- **The cells checks** (`RealizedProgram.CellsValid`): the committing domains `H` and `A`, every field
`equal` and `mod_0` lowered into its domain (the parts of the bits batch `h2p.shake.blocks.r0`
included, its affine part `h2p.shake.padding.output`, predicate `29`, padded to `0 · 0 + c` as
`batch_form`'s `pad_affine` does), every group's LogUp identity a realization circuit of `c.A`, the
node-typed values at their nodes, every circuit entry covered by the honest prover. -/
theorem cellsValid : program.CellsValid := by decide +kernel

/-- **The domains of `Falcon512.Native.ROMParams` are local** (`RealizedProgram.Local`), by the checker. -/
theorem locality :
    program.Local (RealizedProgram.treeNodesOf Generated.Falcon512.Native.ROMParams.Plan.plan program) :=
  RealizedProgram.Local.of_localB Generated.Falcon512.Native.ROMParams.Valid.wellFormed (by decide +kernel)

end GordieHowe.Falcon512.Native.ROMParams.Locality
