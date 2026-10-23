# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# ML-DSA-44 proof of possession over upstream's monolith circuit: upstream's
# ml_dsa and sha3 object libraries, this directory's driver and mu
# derivation.
lfb_add_driver(ml_dsa_44_monolith ml_dsa_44_monolith_driver.cc
               $<TARGET_OBJECTS:ml_dsa> $<TARGET_OBJECTS:sha3>)
target_include_directories(ml_dsa_44_monolith PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR})
