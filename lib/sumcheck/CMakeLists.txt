# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
proofs_add_tests(boolean_skip_test quad_test skip_gfni_test sumcheck_test)
target_link_libraries(boolean_skip_test sha3)
target_link_libraries(quad_test sha3)
target_link_libraries(skip_gfni_test sha3)
target_link_libraries(sumcheck_test sha3)
