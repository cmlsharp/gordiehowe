/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 * Compiles the C Keccak-p[1600] implementation chosen in xkcp-target.h. */
#include "config.h"
#if defined(XKCP_TARGET_AVX512)
#include "../upstream/lib/low/KeccakP-1600/AVX512/C/KeccakP-1600-AVX512.c"
#elif defined(XKCP_TARGET_OPT64)
#include "../upstream/lib/low/KeccakP-1600/plain-64bits/KeccakP-1600-opt64.c"
#elif defined(XKCP_TARGET_INPLACE32)
#include "../upstream/lib/low/KeccakP-1600/plain-32bits-inplace/KeccakP-1600-inplace32BI.c"
#endif
/* XKCP_TARGET_AVX2: keccakp1600-avx2.S.
 * XKCP_TARGET_ARMV7NEON: keccakp1600-armv7a-neon.S. */
typedef int longfellow_xkcp_keccakp1600_nonempty;
