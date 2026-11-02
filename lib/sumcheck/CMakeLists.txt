# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
proofs_add_tests(boolean_skip_test quad_test skip_gfni_test sumcheck_test)
target_link_libraries(boolean_skip_test sha3)
target_link_libraries(quad_test sha3)
target_link_libraries(skip_gfni_test sha3)
target_link_libraries(sumcheck_test sha3)
# The aarch64 kernels against scalar references and their timings, and the
# same test with every kernel on its portable path (PROOFS_NO_NEON).
proofs_add_test(neon_kernels_test)
target_link_libraries(neon_kernels_test sha3)
add_executable(neon_kernels_scalar_test neon_kernels_test.cc)
target_compile_definitions(neon_kernels_scalar_test PRIVATE PROOFS_NO_NEON=1)
target_link_libraries(neon_kernels_scalar_test ec algebra util)
proofs_add_testing_libraries(neon_kernels_scalar_test)
target_link_libraries(neon_kernels_scalar_test sha3)
