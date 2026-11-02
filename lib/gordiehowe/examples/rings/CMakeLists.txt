# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The private rings: ML-DSA (mldsa_ring.h, with the native and carrier
# arms, at ML-DSA-44, ML-DSA-65 as mldsa65_* and ML-DSA-87 as mldsa87_*)
# and Falcon-512 and Falcon-1024 (falcon_ring.h, both arms; one example
# system per (set, arm)).
gordiehowe_add_example_system(mldsa_ring_native)
gordiehowe_add_example_system(mldsa_ring_carrier)
gordiehowe_add_example_system(mldsa65_ring_native)
gordiehowe_add_example_system(mldsa65_ring_carrier)
gordiehowe_add_example_system(mldsa87_ring_native)
gordiehowe_add_example_system(mldsa87_ring_carrier)
gordiehowe_add_example_system(falcon_ring_carrier)
gordiehowe_add_example_system(falcon_ring_native)
gordiehowe_add_example_system(falcon1024_ring_carrier)
gordiehowe_add_example_system(falcon1024_ring_native)

gordiehowe_add_test(mldsa_ring_test mldsa_ring_carrier_test.cc
                    EXAMPLES mldsa_ring_native mldsa_ring_carrier
                    SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(mldsa_ring_test ml_dsa sha3 OpenSSL::Crypto)
# The ML-DSA-65 and ML-DSA-87 rings, both arms and both profiles
# (mldsa_ring_sets_test.cc): one translation unit per set, profile and arm
# (sets/), and the host checks.
set(MLDSA_RING_SET_TESTS)
foreach(SET 65 87)
  foreach(ARM native carrier)
    foreach(PROFILE rom qrom)
      list(APPEND MLDSA_RING_SET_TESTS
           sets/mldsa${SET}_ring_${ARM}_${PROFILE}_test.cc)
    endforeach()
  endforeach()
endforeach()
gordiehowe_add_test(mldsa_ring_sets_test ${MLDSA_RING_SET_TESTS}
                    EXAMPLES mldsa65_ring_native mldsa65_ring_carrier
                             mldsa87_ring_native mldsa87_ring_carrier
                    SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(mldsa_ring_sets_test ml_dsa sha3 OpenSSL::Crypto)
gordiehowe_add_test(falcon_ring_test falcon_ring_threads_test.cc
                    EXAMPLES falcon_ring_carrier falcon_ring_native
                    SETS gold2_sha256 gold4 fp14_9 falcon20)
gordiehowe_add_test(falcon1024_ring_test falcon1024_ring_native_test.cc
                    EXAMPLES falcon1024_ring_carrier falcon1024_ring_native
                    SETS gold2_sha256 gold4 fp14_9 falcon20)

# The bench executables (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(falcon_ring_bench
                     EXAMPLES falcon_ring_carrier falcon_ring_native
                              falcon1024_ring_carrier falcon1024_ring_native
                     SETS gold2_sha256 gold4 fp14_9 falcon20)
gordiehowe_add_bench(mldsa_ring_bench
                     EXAMPLES mldsa_ring_native mldsa_ring_carrier
                              mldsa65_ring_native mldsa65_ring_carrier
                              mldsa87_ring_native mldsa87_ring_carrier
                     SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(mldsa_ring_bench ml_dsa sha3 OpenSSL::Crypto)
