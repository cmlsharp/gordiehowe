-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.TableSelect

@[expose] public section

/-!
# The ML-DSA-44 rings' public table

The row maps of the ML-DSA-44 rings' public table (`lib/gordiehowe/examples/rings/mldsa_ring.h`,
`member.table`): a row is a member's key record `â ‖ t₁` (`20` blocks of `256` coefficients) and
the `24` limbs of its message representative `μ`, the column blocks `ring.keys` (`[64, 5120]`) and
`ring.mu` (`[64, 24]`).

* `nativeMap`: the native rings' map, `21` identity leaves (`20` of `256` cells, then `24`).
* `carrierMap`: the carriers' map, the `20` key leaves the scheme-order negacyclic transform of
  length `256` at the Goldilocks root `carrierPsi` (a key's `â` and `t₁` are committed as their
  FIPS 204 spectra over the carrier field), then the identity leaf of `24`.
-/

namespace GordieHowe.MLDSA44.Ring

open RealizedProgram

/-- **The native rings' row map**: `20` identity leaves of `256` cells, then one of `24`. -/
def nativeMap : List RowLeaf :=
  (List.range 20).map (fun i => ⟨false, false, 256, 256 * i, 0⟩) ++ [⟨false, false, 24, 5120, 0⟩]

/-- **The carriers' transform root** (`ψ` of length `256` over Goldilocks, the natural of the
C++ encoding). -/
abbrev carrierPsi : ℕ := 1803076106186727246

/-- **The carriers' row map**: `20` scheme-order transforms of length `256` at `carrierPsi`, then
an identity leaf of `24` cells. -/
def carrierMap : List RowLeaf :=
  (List.range 20).map (fun i => ⟨true, false, 256, 256 * i, carrierPsi⟩) ++
    [⟨false, false, 24, 5120, 0⟩]

end GordieHowe.MLDSA44.Ring
