/* Copyright 2026 Chad Sharp and Paul Grubbs
 * SPDX-License-Identifier: Apache-2.0
 *
 * Compile-time choice of the vendored Keccak-p[1600] implementation, from
 * compiler-predefined macros only (so cross builds pick the target's). See
 * README.md for the implementations and their test status.
 *   XKCP_TARGET_AVX512    x86-64 with AVX-512F and AVX-512VL: AVX512/C
 *   XKCP_TARGET_AVX2      x86-64 with AVX2, without AVX-512, only when
 *                         LONGFELLOW_XKCP_USE_AVX2 is defined: AVX2
 *                         (CRYPTOGAMS assembler, LICENSE.CRYPTOGAMS). The
 *                         single-state AVX2 core took 14-21% more cycles
 *                         than plain-64bits on an Intel Core Ultra 5 125H
 *                         (README.md), so plain-64bits is the default.
 *   XKCP_TARGET_ARMV7NEON 32-bit ARMv7-A with NEON, little endian:
 *                         ARMv7A-NEON (GNU assembler)
 *   XKCP_TARGET_OPT64     any other 64-bit target: plain-64bits, all rounds
 *                         unrolled (XKCP's choice for ARMv8-A)
 *   XKCP_TARGET_INPLACE32 any other 32-bit target: plain-32bits-inplace
 */
#ifndef LONGFELLOW_XKCP_TARGET_H
#define LONGFELLOW_XKCP_TARGET_H

#if defined(__x86_64__) && defined(__AVX512F__) && defined(__AVX512VL__)
#define XKCP_TARGET_AVX512 1
#elif defined(LONGFELLOW_XKCP_USE_AVX2) && defined(__x86_64__) && \
    defined(__AVX2__) && defined(__ELF__)
#define XKCP_TARGET_AVX2 1
#elif defined(__arm__) && defined(__ARM_NEON) && defined(__ARM_ARCH) && \
    (__ARM_ARCH >= 7) && !defined(__ARMEB__) && !defined(__thumb__)
#define XKCP_TARGET_ARMV7NEON 1
#elif defined(__SIZEOF_POINTER__) && (__SIZEOF_POINTER__ == 8)
#define XKCP_TARGET_OPT64 1
#else
#define XKCP_TARGET_INPLACE32 1
#endif

#endif
