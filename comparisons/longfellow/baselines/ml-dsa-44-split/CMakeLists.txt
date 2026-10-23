# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# ML-DSA-44 proof of possession, Longfellow-style field split.
# Links upstream's ML-DSA host code (the ml_dsa object library: reference
# implementation and examples) and SHA-3 witness code (sha3).
#
# One driver source, two targets:
#  - ml_dsa_44_split_driver, the narrow profile, on upstream alone;
#  - ml_dsa_44_split_driver_wide, the wide profile, which also sees
#    baselines/common-wide's hash domain (GF(2^256) and the SHA-384 Merkle
#    tree, Ligero and transcript, as shadows of upstream headers), so every
#    one of its translation units is compiled with lfb_use_common_wide.
lfb_add_driver(ml_dsa_44_split_driver ml_dsa_44_split_driver.cc
               $<TARGET_OBJECTS:ml_dsa> $<TARGET_OBJECTS:sha3>)
target_include_directories(ml_dsa_44_split_driver PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})

lfb_add_driver(ml_dsa_44_split_driver_wide ml_dsa_44_split_driver.cc
               $<TARGET_OBJECTS:ml_dsa> $<TARGET_OBJECTS:sha3>)
target_include_directories(ml_dsa_44_split_driver_wide PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})
lfb_use_common_wide(ml_dsa_44_split_driver_wide)
