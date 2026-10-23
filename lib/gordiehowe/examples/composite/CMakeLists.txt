# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The proof of possession of a composite signature (composite.h): ML-DSA-44
# and ECDSA P-256 over one message, as draft-ietf-lamps-pq-composite-sigs
# forms it, in three domains (H, F_p256, the ML-DSA native field) with two
# MACs, and each signature's proof of possession alone.
gordiehowe_add_example_system(composite)

gordiehowe_add_test(composite_test
                    EXAMPLES composite
                    SETS rom_composite qrom_composite mdoc qrom_ecdsa
                    rom_ml_dsa qrom_ml_dsa)
target_link_libraries(composite_test ml_dsa sha3 flatsha util OpenSSL::Crypto)

# The bench executable (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(composite_bench
                     EXAMPLES composite
                     SETS rom_composite qrom_composite mdoc qrom_ecdsa
                     rom_ml_dsa qrom_ml_dsa)
target_link_libraries(composite_bench ml_dsa sha3 flatsha util OpenSSL::Crypto)
