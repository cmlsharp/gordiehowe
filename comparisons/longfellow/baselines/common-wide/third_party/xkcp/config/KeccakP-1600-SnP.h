/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 * The SnP interface of the Keccak-p[1600] implementation chosen in
 * xkcp-target.h. */
#ifndef LONGFELLOW_XKCP_SNP_SELECT_H
#define LONGFELLOW_XKCP_SNP_SELECT_H
#include "config.h"
#if defined(XKCP_TARGET_AVX512)
#include "../upstream/lib/low/KeccakP-1600/AVX512/C/KeccakP-1600-SnP.h"
#elif defined(XKCP_TARGET_AVX2)
#include "../upstream/lib/low/KeccakP-1600/AVX2/SnP/KeccakP-1600-SnP.h"
#elif defined(XKCP_TARGET_ARMV7NEON)
#include "../upstream/lib/low/KeccakP-1600/ARMv7A-NEON/KeccakP-1600-SnP.h"
#elif defined(XKCP_TARGET_OPT64)
#include "../upstream/lib/low/KeccakP-1600/plain-64bits/SnP/KeccakP-1600-SnP.h"
#else
#include "../upstream/lib/low/KeccakP-1600/plain-32bits-inplace/KeccakP-1600-SnP.h"
#endif
#endif
