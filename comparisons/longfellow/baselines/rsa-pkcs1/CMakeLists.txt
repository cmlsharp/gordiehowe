# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# RSA-2048 PKCS#1 v1.5 (SHA-256) proof of possession on upstream Longfellow.
# The sources keep the layout they were written in (upstream/lib/circuits/rsa/
# of an upstream checkout), here under src/, so their includes are unchanged.
# The default layout is set in rsa_zk.cc (RSA_LOGN*, RSA_W*, RSA_PLUCK*); the
# worker mode takes any other layout at run time.
lfb_add_driver(rsa_zk src/circuits/rsa/rsa_zk.cc $<TARGET_OBJECTS:flatsha>)
target_include_directories(rsa_zk PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src)
