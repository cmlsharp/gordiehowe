-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Params
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Applications.Shared.MACProfiles
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Foundations.Fields.GF2_128

@[expose] public section

/-!
# Falcon: the parameters both configurations use

The parameters of the Falcon-512 proofs of possession (`lib/gordiehowe/examples/falcon/falcon_emulated.h`,
`examples/falcon/falcon_native.h`, the hash-to-point call in `examples/falcon/falcon_hash.h`; `msgLen = 32`) that
Falcon emulated and Falcon native share: Falcon's constants (`q`, `n`, `betaSq`), the ordered
selection's cutoff (`cutoff`) and the MAC field profiles. The configurations' range plans, domain
sizes, challenge points with extended stream budgets and Ligero tableaus are the generated plan data's
(`GordieHowe/Generated/`), whose validity `Plan.Valid` states (`GordieHowe/Language/Export/Valid.lean`). Falcon
emulated's remaining parameters are in `GordieHowe/Applications/Falcon512/Emulated/System/Params.lean`.
-/

namespace GordieHowe.Falcon512.Emulated.Params

open scoped NNReal

/-! ## Constants -/

/-- Falcon's modulus `q = 12289` (`examples/falcon/falcon_hash.h`, `kQ`). -/
abbrev q : ℕ := 12289

/-- Falcon-512's degree `n = 512` (`examples/falcon/falcon_hash.h`, `kN`). -/
abbrev n : ℕ := 512

/-- Falcon-512's squared norm bound `β² = 34034726`, inclusive (`examples/falcon/falcon_emulated.h`,
`kBetaSq`). -/
abbrev betaSq : ℕ := 34034726

/-! ## The ordered selection

`h2p.select`: `select_first_n(s, H, stream, Cutoff{uint32_t(kCutoff)}, Count{kN})`
(`examples/falcon/falcon_hash.h`, `hash_to_point`): the first `n` of the `nSamples` samples below
`cutoff`. -/

/-- The rejection cutoff `5q` (`examples/falcon/falcon_hash.h`, `kCutoff`). -/
abbrev cutoff : ℕ := 5 * q

/-! ## The profiles

The MAC's field `GF(2^w)` with its reduction taps (`../params/param_sets.h`,
`MACShape<w>`): `w = 256` with taps `{0, 2, 5, 10}` (QROM parameters), `w = 128` with taps
`{0, 1, 2, 7}` (ROM parameters). The MAC's chunk count, accumulator bound and high limb, the dynamic support of the range
table and the MAC requests' honest bounds follow from them as the C++ computes them. -/

end GordieHowe.Falcon512.Emulated.Params
