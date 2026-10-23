# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Longfellow mdoc (ZkSpec v7): upstream's mdoc circuits and prover, timed by
# mdoc_v7_driver.cc.  The driver #includes upstream's mdoc_zk.cc, so it links
# upstream's other mdoc sources directly rather than the mdoc_static library.
set(LFB_MDOC_SOURCES
    ${LFB_UPSTREAM_LIB}/circuits/mdoc/mdoc_decompress.cc
    ${LFB_UPSTREAM_LIB}/circuits/mdoc/mdoc_generate_circuit.cc
    ${LFB_UPSTREAM_LIB}/circuits/mdoc/mdoc_circuit_id.cc
    ${LFB_UPSTREAM_LIB}/circuits/mdoc/zk_spec.cc
    CACHE INTERNAL "")
set(LFB_MDOC_DRIVER ${CMAKE_CURRENT_SOURCE_DIR}/mdoc_v7_driver.cc
    CACHE INTERNAL "")
lfb_add_driver(mdoc_v7 ${LFB_MDOC_DRIVER} ${LFB_MDOC_SOURCES}
               $<TARGET_OBJECTS:flatsha>)
