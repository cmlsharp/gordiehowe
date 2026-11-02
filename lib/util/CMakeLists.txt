# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
proofs_add_tests(optimization_options_test)
# Longfellow's own tests, unchanged (third_party/longfellow/lib/util).
longfellow_add_tests(ceildiv_test)
# The linked OpenSSL was built with its assembly (on aarch64: the ARMv8
# AES, PMULL and SHA-256 code).
proofs_add_test(openssl_asm_test)
target_link_libraries(openssl_asm_test OpenSSL::Crypto)
