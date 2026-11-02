# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
# Longfellow's own tests, unchanged (third_party/longfellow/lib/circuits/compiler).
longfellow_add_tests(canonicalization_test compiler_test)
# The certificate export on small circuits (cert_export_test.cc).
proofs_add_test(cert_export_test)
