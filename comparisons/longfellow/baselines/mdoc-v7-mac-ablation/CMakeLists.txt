# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The MAC ablation of Longfellow mdoc v7: baselines/mdoc-v7's driver and
# upstream's mdoc sources, every one compiled with include/ first on the
# include path, so that upstream's mdoc circuits see this directory's
# circuits/mac/mac_circuit.h (upstream's file with the MAC products and
# checks switched off) instead of upstream's.
lfb_add_driver(mdoc_v7_nomac ${LFB_MDOC_DRIVER} ${LFB_MDOC_SOURCES}
               $<TARGET_OBJECTS:flatsha>)
target_include_directories(mdoc_v7_nomac BEFORE PRIVATE
                           ${CMAKE_CURRENT_SOURCE_DIR}/include)
