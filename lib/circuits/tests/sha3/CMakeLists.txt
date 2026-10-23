# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
proofs_add_tests(sha3_circuit_test)
# Longfellow's own tests, unchanged (third_party/longfellow/lib/circuits/tests/sha3).
longfellow_add_tests(sha3_reference_test)
target_link_libraries(sha3_circuit_test sha3)
target_link_libraries(sha3_reference_test sha3)
