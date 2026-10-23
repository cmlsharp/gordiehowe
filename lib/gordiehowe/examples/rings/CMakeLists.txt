# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The private rings: ML-DSA-44 (mldsa_ring.h, with the native and carrier
# arms) and Falcon-512 (falcon_ring.h, both arms).
gordiehowe_add_example_system(mldsa_ring_native)
gordiehowe_add_example_system(mldsa_ring_carrier)
gordiehowe_add_example_system(falcon_ring)

gordiehowe_add_test(mldsa_ring_test mldsa_ring_carrier_test.cc
                    EXAMPLES mldsa_ring_native mldsa_ring_carrier
                    SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(mldsa_ring_test ml_dsa sha3 OpenSSL::Crypto)
gordiehowe_add_test(falcon_ring_test falcon_ring_threads_test.cc
                    EXAMPLES falcon_ring
                    SETS gold2_sha256 gold4 fp14_9 falcon20)

# The bench executables (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(falcon_ring_bench
                     EXAMPLES falcon_ring
                     SETS gold2_sha256 gold4 fp14_9 falcon20)
gordiehowe_add_bench(mldsa_ring_bench
                     EXAMPLES mldsa_ring_native mldsa_ring_carrier
                     SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(mldsa_ring_bench ml_dsa sha3 OpenSSL::Crypto)
