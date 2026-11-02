# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Falcon proof of possession (Falcon-512 and Falcon-1024, --falcon-set),
# split Longfellow-style baseline: native and emulated arms in one driver.  falcon_split_driver serves the narrow profile
# on upstream's library alone; falcon_split_driver_wide the wide profile,
# with baselines/common-wide's hash domain (GF(2^256), SHA-384) shadowing
# upstream's transcript, Merkle and Ligero hashing in every one of its
# translation units.
lfb_add_driver(falcon_split_driver falcon_split_driver.cc $<TARGET_OBJECTS:sha3>)
target_include_directories(falcon_split_driver PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})

lfb_add_driver(falcon_split_driver_wide falcon_split_driver.cc
               $<TARGET_OBJECTS:sha3>)
lfb_use_common_wide(falcon_split_driver_wide)
target_include_directories(falcon_split_driver_wide PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})

# The gadget audit (falcon_split_audit.cc): concrete assignments for the
# audit's findings, evaluated with upstream's EvaluationBackend.
lfb_add_driver(falcon_split_audit falcon_split_audit.cc $<TARGET_OBJECTS:sha3>)
target_include_directories(falcon_split_audit PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})
