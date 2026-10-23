# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# SHA-256 of a private message to a public digest on upstream Longfellow,
# configured as mdoc's hash circuit.  sha256_driver serves the narrow profile
# on upstream's library alone; sha256_driver_wide the wide profile, with
# baselines/common-wide's hash domain (GF(2^256), SHA-384) shadowing
# upstream's transcript, Merkle and Ligero hashing.
lfb_add_driver(sha256_driver sha256_driver.cc $<TARGET_OBJECTS:flatsha>)

lfb_add_driver(sha256_driver_wide sha256_driver.cc $<TARGET_OBJECTS:flatsha>)
lfb_use_common_wide(sha256_driver_wide)
