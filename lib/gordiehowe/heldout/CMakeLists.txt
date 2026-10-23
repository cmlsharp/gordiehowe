# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The held-out programs: relations a new user could write, which test
# whether the Lean validity checking of the realized programs generalizes
# beyond the applications (heldout_env.h). One test binary of one file per
# program beside heldout_test.cc, and the exporter of every program (heldout_export.cc, in the
# build tree's bench/).
set(GH_HELDOUT_SETS gf128_sha256 gold2_sha256 rom_emu fp14_9)
gordiehowe_add_test(heldout_test
                    merkle_sha256_test.cc date_age_test.cc kyber_ntt_test.cc
                    memory_check_test.cc three_phase_test.cc
                    bits_across_test.cc congruence_chain_test.cc
                    index_maps_test.cc degenerate_test.cc custom_ops_test.cc
                    credential_test.cc derivation_test.cc mac_padded_test.cc
                    SETS ${GH_HELDOUT_SETS})
target_link_libraries(heldout_test flatsha sha3 util)

gordiehowe_add_bench(heldout_export SETS ${GH_HELDOUT_SETS})
target_link_libraries(heldout_export flatsha sha3 util gtest)
# The setup measurement of every program (compile, and with
# GH_COMPILE_CACHE the cache-hit setup).
gordiehowe_add_bench(heldout_measure SETS ${GH_HELDOUT_SETS})
target_link_libraries(heldout_measure flatsha sha3 util gtest)
