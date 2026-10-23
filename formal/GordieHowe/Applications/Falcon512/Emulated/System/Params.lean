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
public import GordieHowe.Applications.Falcon512.System.Params

@[expose] public section

/-!
# Falcon emulated: the parameters

The parameters of the Falcon-512 emulated proof of possession
(`lib/gordiehowe/examples/falcon/falcon_emulated.h`, with the hash-to-point call in
`examples/falcon/falcon_hash.h`; `msgLen = 32`) beyond those Falcon native shares
(`GordieHowe/Applications/Falcon512/System/Params.lean`): the honest bound of the magnitude request `magnitudes.mag1`
(`mag1Honest`). The C++ compiles two field profiles (`../params/param_sets.h`): the QROM
parameters (H over `GF(2^256)`, A over Goldilocks⁴) and the ROM parameters (`GF(2^128)`,
Goldilocks²). Citations are
`file:line` at commit `bf04ccb3`, relative to `lib/gordiehowe/` unless they name another directory,
except those of the range plan, at `1740dd07`. Names are the C++'s scoped node names
(`signature.s1`, `h2p.select.delta`, …), as in the generated plan data.
-/

namespace GordieHowe.Falcon512.Emulated.Params

open scoped NNReal

/-! ## The range plan

The requests of domain A in declaration order: Falcon's seven, declared by the gadgets
`signature_relation`, `magnitudes`, `assert_encoding_budget` and `assert_norm`
(`examples/falcon/falcon_emulated.h`), then the MAC's three, declared by the
modular lowering's digits (`mod.h:425-428,439-440`). `signature.s1` has no request: the two-sided
bound on `mag1` and the magnitude relation `(mag1 − s1)(mag1 − (q − s1)) = 0` pin `s1` to `[0, q]`
(`examples/falcon/falcon_emulated.h`; `examples/falcon/falcon_emulated_test.cc`). For each request,
the realization the planner selects (`examples/falcon/falcon_emulated_test.cc`, `Realizations`;
the compile report's range lowering lines), its limb count or scaling constant, and the request's
honest bound and maximum (`examples/falcon/falcon_emulated.h`, `FalconBounds::derive`; a request
without `MaxBound` has maximum its honest bound). -/

/-- `magnitudes.mag1` (request `1`): honest bound and maximum `q / 2 + 1`, no `MaxBound`
(`examples/falcon/falcon_emulated.h`). -/
abbrev mag1Honest : ℕ := q / 2 + 1

/-! ## The Ligero tableau of domain A

Ligero at an agreement threshold, with the mask test, over the relatively packed commitment of domain A (the tree
plan's `LigeroParam`, `compiler/tree_zk.h`), in both profiles, at the rate, `block_enc`, opened
columns `t` (blinding width `r = t`) and masking the compiler chooses (`compiler/ligero_choice.h`),
as the generated plan data records them. The code is `k = block = (block_enc + 1) / (2 + rate)` and
`N = block_ext = block_enc − (2k − 1)` (`../ligero/ligero_param.h`, `LigeroParam`). The relative
packing degree is `4` at the QROM parameters (Goldilocks⁴ over Goldilocks) and `2` at the ROM
parameters (Goldilocks²).

The agreement threshold `A` and the exceptional count `B` are not C++ parameters: they are the
proof's choice for the line certificate of the code at threshold `A` (a weighted Johnson
certificate), taken where the commit and column rounds balance at the query count `t`. The
shared tableaus prove each per-round error below `c / 2^260` (QROM parameters) or `c / 2^140` (ROM parameters) for
an explicit natural `c`. -/

/-! ### ROM parameters: Goldilocks²

The Goldilocks² tableaus of the generated plans at the ROM parameters are shared
(`GordieHowe/Applications/Shared/Tableaux.lean`, `Tableau.gold2K512R2Shape`). -/

end GordieHowe.Falcon512.Emulated.Params
