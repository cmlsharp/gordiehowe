# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
proofs_add_tests(logic_test)
# Longfellow's own tests, unchanged (third_party/longfellow/lib/circuits/logic).
longfellow_add_tests(bit_adder_test bit_plucker_test counter_test logic_circuit_test memcmp_test polynomial_test routing_test)
