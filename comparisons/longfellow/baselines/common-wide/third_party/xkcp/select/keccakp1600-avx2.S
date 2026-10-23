/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 * Assembles XKCP's AVX2 Keccak-p[1600] (CRYPTOGAMS license,
 * LICENSE.CRYPTOGAMS) when xkcp-target.h picks it; empty on every other
 * target. The preprocessor leaves the upstream file's code unchanged; it
 * only cuts short the "#" comment lines that contain "//". */
#include "xkcp-target.h"
#if defined(XKCP_TARGET_AVX2)
#include "../upstream/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s"
#elif defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
