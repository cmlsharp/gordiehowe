# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The example applications, one directory each: the relation headers, their
# host and testing headers, their tests and their bench executable.
#   mldsa/             ML-DSA-44 proofs of possession (native and emulated)
#   falcon/            Falcon-512 proofs of possession (native and emulated)
#   rings/             ML-DSA-44 and Falcon-512 private rings
#   rsa/               RSA-2048 PKCS#1 v1.5 proof of possession
#   p256/              P-256 gadgets (ECDSA verification, scalar mult)
#   mdoc/              the ECDSA mDL (v7 mdoc)
#   pq_mdoc/           the post-quantum mDL
#   composite/         the ML-DSA-44 + ECDSA P-256 composite signature
#   sha256/            SHA-256 preimage (bench/hash_comparisons/ runs it)
#   keccak/            SHA3-256 preimage (bench/hash_comparisons/ runs it)
#   shared/            setup and test helpers the applications share
#
# The example systems' builders are explicitly instantiated for both
# parameter sets (instances.h): one static library per system,
# gordiehowe_example_<system>, of one translation unit per parameter set
# (<app>/instantiations/<system>_rom.cc and _qrom.cc), so they compile once
# and in parallel, and a test or bench lists the systems it uses after
# EXAMPLES. Every other unit that includes instances.h sees the builders as
# extern templates and compiles none.
macro(gordiehowe_add_example_system SYS)
  add_library(gordiehowe_example_${SYS} STATIC
              ${CMAKE_CURRENT_SOURCE_DIR}/instantiations/${SYS}_rom.cc
              ${CMAKE_CURRENT_SOURCE_DIR}/instantiations/${SYS}_qrom.cc)
  gordiehowe_use_pch(gordiehowe_example_${SYS})
endmacro()

add_subdirectory(mldsa)
add_subdirectory(falcon)
add_subdirectory(rings)
add_subdirectory(p256)
add_subdirectory(mdoc)
add_subdirectory(pq_mdoc)
add_subdirectory(rsa)
add_subdirectory(composite)
