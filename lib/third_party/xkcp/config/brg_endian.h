/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 * Stands in for XKCP's lib/common/brg_endian.h (not CC0, not vendored): the
 * byte-order macros the vendored files test, from the compiler's
 * __BYTE_ORDER__. */
#ifndef LONGFELLOW_XKCP_BRG_ENDIAN_H
#define LONGFELLOW_XKCP_BRG_ENDIAN_H
#define IS_BIG_ENDIAN 4321
#define IS_LITTLE_ENDIAN 1234
#if defined(__BYTE_ORDER__) && (__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
#define PLATFORM_BYTE_ORDER IS_LITTLE_ENDIAN
#elif defined(__BYTE_ORDER__) && (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
#define PLATFORM_BYTE_ORDER IS_BIG_ENDIAN
#else
#error "unknown byte order"
#endif
#endif
