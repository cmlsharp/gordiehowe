# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Domain H of v7 mdoc (mdoc_hash.h) on Longfellow's test vectors, through
# Longfellow's witness parser.
gordiehowe_add_test(mdoc_hash_test SETS gf128_sha256)
target_link_libraries(mdoc_hash_test flatsha)
# Domain A of plain mdoc, F_p256: ECDSA P-256 by fixed- and variable-base
# chains (p256_ecdsa.h, mdoc_signatures.h).
gordiehowe_add_test(mdoc_signatures_test SETS p256)
target_link_libraries(mdoc_signatures_test flatsha util OpenSSL::Crypto)
# Plain mdoc in one proof (mdoc.h): domain H = GF(2^128) hashes, domain
# A = F_p256 verifies the signatures, and the MAC equality of e, dpkx and
# dpky joins them.
gordiehowe_add_test(mdoc_test SETS mdoc)
target_link_libraries(mdoc_test flatsha util OpenSSL::Crypto)

# The bench executable (bench/cli.h), in the build tree's bench/, and the
# measurement bench of plain mdoc's domain H alone.
gordiehowe_add_bench(mdoc_bench SETS mdoc)
target_link_libraries(mdoc_bench flatsha util OpenSSL::Crypto)
gordiehowe_add_bench(mdoc_hash_bench SETS gf128_sha256)
target_link_libraries(mdoc_hash_bench flatsha)
