# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Post-quantum mdoc, Longfellow style.  Reuses the ML-DSA-44
# split baseline's circuits, MAC binding, witness, profiles and wide field
# (baselines/ml-dsa-44-split, on the include path), and links upstream's
# ML-DSA host code (ml_dsa), SHA-3 witness code (sha3) and SHA-256 witness
# code (flatsha).  Needs ml-dsa-44-split's sources only, not its targets.
#
# One driver source, two targets:
#  - pq_mdoc_driver, the narrow profile, on upstream alone;
#  - pq_mdoc_driver_wide, the wide profile, with baselines/common-wide's
#    hash domain (lfb_use_common_wide).
set(LFB_PQ_MDOC_INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/../ml-dsa-44-split)

lfb_add_driver(pq_mdoc_driver pq_mdoc_driver.cc
               $<TARGET_OBJECTS:ml_dsa> $<TARGET_OBJECTS:sha3>
               $<TARGET_OBJECTS:flatsha>)
target_include_directories(pq_mdoc_driver PRIVATE ${LFB_PQ_MDOC_INCLUDES})

lfb_add_driver(pq_mdoc_driver_wide pq_mdoc_driver.cc
               $<TARGET_OBJECTS:ml_dsa> $<TARGET_OBJECTS:sha3>
               $<TARGET_OBJECTS:flatsha>)
target_include_directories(pq_mdoc_driver_wide PRIVATE
                           ${LFB_PQ_MDOC_INCLUDES})
lfb_use_common_wide(pq_mdoc_driver_wide)
