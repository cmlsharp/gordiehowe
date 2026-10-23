-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.MACProfile

@[expose] public section

/-!
# The concrete MAC profiles

The two MAC profiles of the C++ field profiles (`../params/param_sets.h`,
`MACShape<w>`), shared by the configurations' parameters: `w = 256` with taps `{0, 2, 5, 10}`
(`GordieHowe.MACProfile.qrom`) and `w = 128` with taps `{0, 1, 2, 7}` (`GordieHowe.MACProfile.rom`).
-/

namespace GordieHowe

namespace MACProfile

/-- **The MAC profile of the QROM parameters** (`../params/param_sets.h`, `MACShape<256>`): `w = 256`,
the taps `{0, 2, 5, 10}` of `X^256 + X^10 + X^5 + X^2 + 1` (`../circuits/mac/linear_mac.h:96`,
`Shape<256>::kTaps`), `convMax = 1017` (`Conv.convMax_gf2_256`; `mac_conv_max`,
`lib/gordiehowe/ops/operators.h:868`). -/
def qrom : MACProfile where
  macWidth := 256
  macTaps := Conv.gf2_256Taps
  convMax := 1017
  convMax_eq := Conv.convMax_gf2_256

/-- **The MAC profile of the ROM parameters** (`../params/param_sets.h`, `MACShape<128>`): `w = 128`,
the taps `{0, 1, 2, 7}` of `X^128 + X^7 + X^2 + X + 1` (`../circuits/mac/linear_mac.h:92`,
`Shape<128>::kTaps`), `convMax = 504` (`Conv.convMax_gf2_128`; `mac_conv_max`,
`lib/gordiehowe/ops/operators.h:868`). -/
def rom : MACProfile where
  macWidth := 128
  macTaps := Conv.gf2_128Taps
  convMax := 504
  convMax_eq := Conv.convMax_gf2_128

end MACProfile

end GordieHowe
