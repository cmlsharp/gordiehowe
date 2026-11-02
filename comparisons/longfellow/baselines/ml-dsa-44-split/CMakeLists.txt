# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# ML-DSA proof of possession (ML-DSA-44, -65 and -87), Longfellow-style
# field split.  Links upstream's ML-DSA reference code with its templates
# instantiated for every set (ml_dsa_ref_sets.cc, which compiles upstream's
# ml_dsa_ref.cc, and upstream's ml_dsa_shared.cc, in place of upstream's
# ml_dsa object library) and SHA-3 witness code (sha3).
#
# One driver source, two targets:
#  - ml_dsa_44_split_driver, the narrow profile, on upstream alone;
#  - ml_dsa_44_split_driver_wide, the wide profile, which also sees
#    baselines/common-wide's hash domain (GF(2^256) and the SHA-384 Merkle
#    tree, Ligero and transcript, as shadows of upstream headers), so every
#    one of its translation units is compiled with lfb_use_common_wide.
set(LFB_ML_DSA_SOURCES ml_dsa_ref_sets.cc
    ${LFB_UPSTREAM_LIB}/circuits/tests/pq/ml_dsa/ml_dsa_shared.cc
    $<TARGET_OBJECTS:sha3>)
lfb_add_driver(ml_dsa_44_split_driver ml_dsa_44_split_driver.cc
               ${LFB_ML_DSA_SOURCES})
target_include_directories(ml_dsa_44_split_driver PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})

lfb_add_driver(ml_dsa_44_split_driver_wide ml_dsa_44_split_driver.cc
               ${LFB_ML_DSA_SOURCES})
target_include_directories(ml_dsa_44_split_driver_wide PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})
lfb_use_common_wide(ml_dsa_44_split_driver_wide)

# Checks of the ML-DSA baselines' gadgets on concrete assignments
# (ml_dsa_gadget_test.cc: the private-length SHAKE256, UseHint with the exact
# Decompose, SampleInBall over the 272-byte stream); also reads the
# monolith's ml_dsa_monolith_verify.h.  Not a benchmark driver.
lfb_add_driver(ml_dsa_gadget_test ml_dsa_gadget_test.cc ${LFB_ML_DSA_SOURCES})
target_include_directories(ml_dsa_gadget_test PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR}
                           ${CMAKE_CURRENT_SOURCE_DIR}/../ml-dsa-44-monolith)
