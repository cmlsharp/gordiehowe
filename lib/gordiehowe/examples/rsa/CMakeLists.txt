# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# RSA-2048 PKCS#1 v1.5 (SHA-256) proof of possession (rsa_pkcs1.h): SHA-256
# in H, the exponentiation in Goldilocks^k or Fp128, three multiplication
# variants.
gordiehowe_add_test(rsa_pkcs1_test
                    SETS rom_emu qrom_emu rom_fp128)
target_link_libraries(rsa_pkcs1_test flatsha util OpenSSL::Crypto)

# The bench executable (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(rsa_pkcs1_bench SETS rom_emu qrom_emu rom_fp128)
target_link_libraries(rsa_pkcs1_bench flatsha util OpenSSL::Crypto)
