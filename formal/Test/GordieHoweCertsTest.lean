-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnit
import GordieHoweTest.StructureRecords
import GordieHoweTest.ProgramDataTypes
import GordieHoweTest.FiguresCheck
import GordieHoweTest.MacStructure
import GordieHoweTest.StructureRows
import GordieHoweTest.StructureLookups
import GordieHoweTest.StructurePlacement
import GordieHoweTest.StructurePlacementRSA
import GordieHoweTest.StructureNames
import GordieHoweTest.ProgramCerts
import GordieHoweTest.SelectionCheck

/-! The tests that read exported programs, plans or certificates (`GordieHowe/Generated/`). Their
modules keep the `GordieHoweTest` names; this root collects them apart from `GordieHoweTest`, so
`lake build GordieHoweTest` checks no certificate. -/
