-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Locality
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Valid

@[expose] public section

/-!
# GordieHowe: locality and late values of `MLDSA44.Native.QROMParams`

The checks of the two committing domains of the realized program of the native ML-DSA-44 proof of possession at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`, export `c825eb05`: domain `A` over `F_q^11`
with the GKR circuit `c.A`, domain `H` over `GF(2^256)` with the GKR circuit `c.H`; the late values
`mac.value` of `H` and `mac.acc`, `mac.low`, `range.dynamic:A.512` of `A`), by `decide`:

* **locality** (`locality`, `GordieHowe.RealizedProgram.Local` through `GordieHowe.RealizedProgram.Local.of_localB`): every predicate
  of a domain reads only its domain (the cross-field `equal` `mac.equal` relates the two and is not
  checked), the placed predicates, the batches' parts and the LogUp identity of `A.512` are of
  their circuit's or batch's domain, every input block holds a value of its circuit's domain,
  every late value's pad space is a node of its domain's tree.

Both domains' circuit proofs are the generic per-field ones, their checks decided
(`GordieHowe.MLDSA44.Native.QROMParams.fieldOkA`, `GordieHowe.MLDSA44.Native.QROMParams.fieldOkH`); the proof system and the headlines are in
`GordieHowe/Applications/MLDSA44/Native/QROMParams/ProofSystem.lean`.
-/

namespace GordieHowe.MLDSA44.Native.QROMParams.Locality

open Generated.MLDSA44.Native.QROMParams.Program (program)

/-- **The domains of `MLDSA44.Native.QROMParams` are local** (`RealizedProgram.Local`), by the checker. -/
theorem locality :
    program.Local (RealizedProgram.treeNodesOf Generated.MLDSA44.Native.QROMParams.Plan.plan program) :=
  RealizedProgram.Local.of_localB Generated.MLDSA44.Native.QROMParams.Valid.wellFormed (by decide +kernel)

end GordieHowe.MLDSA44.Native.QROMParams.Locality
