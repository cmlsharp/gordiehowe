/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 * Stands in for the config.h that XKCP's build generates: the vendored
 * subset provides one Keccak-p[1600] and its sponge. */
#ifndef LONGFELLOW_XKCP_CONFIG_H
#define LONGFELLOW_XKCP_CONFIG_H
#include "xkcp-target.h"
#define XKCP_has_KeccakP1600
#if defined(XKCP_TARGET_OPT64)
#define KeccakP1600_plain64_implementation_config "all rounds unrolled"
#define KeccakP1600_plain64_fullUnrolling
#endif
#endif
