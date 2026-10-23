# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
proofs_add_tests(fields256_test fp14_8_test fp24_6_test fp_goldilocks_test fp_test native_wide_test subgroup_reed_solomon_test)
# Longfellow's own tests, unchanged (third_party/longfellow/lib/algebra).
longfellow_add_tests(crt_test fft_test fp2_test interpolation_test limb_test nat_test poly_test reed_solomon_test rfft_test sysdep_test utility_test)
