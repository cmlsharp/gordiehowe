# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The hash comparison harnesses: SHA-256 and Keccak proved alone, the
# batched mode against GKR and, for SHA-256, against Longfellow's own
# pipeline.

# The SHAKE256 work of the H domains alone, batched against in-GKR Keccak.
gordiehowe_add_test(keccak_compare_test SETS gf128_sha256 gf256)
target_link_libraries(keccak_compare_test ml_dsa sha3)
# SHA-256 alone: Longfellow's own pipeline, its flat circuit inside
# GordieHowe, and the batched gadget.
gordiehowe_add_test(sha256_compare_test SETS gf128_sha256 gf256)
target_link_libraries(sha256_compare_test flatsha)

# The bench executables (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(keccak_compare_bench SETS gf128_sha256 gf256)
target_link_libraries(keccak_compare_bench ml_dsa sha3)
gordiehowe_add_bench(sha256_compare_bench SETS gf128_sha256 gf256)
target_link_libraries(sha256_compare_bench flatsha)
