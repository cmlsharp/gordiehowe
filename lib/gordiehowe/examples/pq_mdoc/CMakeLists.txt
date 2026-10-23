# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Post-quantum mdoc in one proof (pq_mdoc.h): plain mdoc's hash domain with
# ML-DSA-44 for the issuer and the device, the device's key private
# (ExpandA in H, its A_hat and t1 crossed into domain A), in both arms of
# A: the ML-DSA native field, and a Goldilocks extension with ML-DSA's
# arithmetic emulated.
gordiehowe_add_test(pq_mdoc_test SETS rom_ml_dsa qrom_ml_dsa rom_emu
                    qrom_emu)
target_link_libraries(pq_mdoc_test ml_dsa sha3 flatsha util OpenSSL::Crypto)

# The bench executable (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(pq_mdoc_bench
                     SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(pq_mdoc_bench ml_dsa sha3 flatsha util OpenSSL::Crypto)
