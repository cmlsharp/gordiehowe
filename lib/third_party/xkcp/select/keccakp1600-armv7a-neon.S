/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 * Assembles XKCP's ARMv7A-NEON Keccak-p[1600] when xkcp-target.h picks it;
 * empty on every other target. */
#include "xkcp-target.h"
#if defined(XKCP_TARGET_ARMV7NEON)
#include "../upstream/lib/low/KeccakP-1600/ARMv7A-NEON/KeccakP-1600-armv7a-le-neon-gcc.s"
#endif
#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
