# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# ML-DSA proof of possession (ML-DSA-44, -65 and -87) over upstream's
# monolith circuit: upstream's ML-DSA reference code with its templates
# instantiated for every set (ml-dsa-44-split's ml_dsa_ref_sets.cc, with
# upstream's ml_dsa_shared.cc) and SHA-3 witness code (sha3), this
# directory's driver, and ml-dsa-44-split's shared parameter sets, fixtures,
# mu derivation and host code (on the include path).
set(LFB_ML_DSA_SPLIT_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../ml-dsa-44-split)
lfb_add_driver(ml_dsa_44_monolith ml_dsa_44_monolith_driver.cc
               ${LFB_ML_DSA_SPLIT_DIR}/ml_dsa_ref_sets.cc
               ${LFB_UPSTREAM_LIB}/circuits/tests/pq/ml_dsa/ml_dsa_shared.cc
               $<TARGET_OBJECTS:sha3>)
target_include_directories(ml_dsa_44_monolith PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR} ${LFB_ML_DSA_SPLIT_DIR})
