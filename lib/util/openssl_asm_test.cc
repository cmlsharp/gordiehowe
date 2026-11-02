// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The linked OpenSSL has its assembly: OPENSSL_info reports the CPU
// capability vector only when OpenSSL was built with its CPU-detection
// assembly (OPENSSL_CPUID_OBJ, crypto/info.c), which a generic target such
// as linux-generic64 lacks. On aarch64 Linux, the vector also has the ARMv8
// AES, PMULL and SHA-256 bits (arm_arch.h) whenever the CPU reports them
// (getauxval(AT_HWCAP)), so OpenSSL's SHA-256 (the ring benchmarks'
// out-of-circuit hashing) runs on the SHA-2 instructions. The aarch64 cross
// build's OpenSSL (flake.nix, aarch64-cross) is configured for this.
#include <openssl/crypto.h>

#include <cstdlib>
#include <cstring>
#include <string>

#include "gtest/gtest.h"

#if defined(__aarch64__) && defined(__linux__)
#include <asm/hwcap.h>
#include <sys/auxv.h>
#endif

namespace {

TEST(OpensslAsm, CpuCapabilities) {
  const char *info = OpenSSL_version(OPENSSL_VERSION);
  const char *cpu = OPENSSL_info(OPENSSL_INFO_CPU_SETTINGS);
  ASSERT_NE(cpu, nullptr) << info << ": no CPU capability vector, so no "
                          << "assembly (a generic Configure target?)";
#if defined(__x86_64__)
  EXPECT_EQ(std::strncmp(cpu, "OPENSSL_ia32cap=", 16), 0) << cpu;
#elif defined(__aarch64__)
  ASSERT_EQ(std::strncmp(cpu, "OPENSSL_armcap=", 15), 0) << cpu;
  const unsigned long cap = std::strtoul(cpu + 15, nullptr, 16);
#if defined(__linux__)
  // arm_arch.h: ARMV8_AES, ARMV8_SHA256, ARMV8_PMULL.
  constexpr unsigned long kAes = 1u << 2, kSha256 = 1u << 4,
                          kPmull = 1u << 5;
  const unsigned long hw = getauxval(AT_HWCAP);
  if (hw & HWCAP_AES) EXPECT_NE(cap & kAes, 0u) << cpu;
  if (hw & HWCAP_PMULL) EXPECT_NE(cap & kPmull, 0u) << cpu;
  if (hw & HWCAP_SHA2) EXPECT_NE(cap & kSha256, 0u) << cpu;
#endif
  (void)cap;
#endif
}

}  // namespace
