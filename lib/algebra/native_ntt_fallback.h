// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVACY_PROOFS_ZK_LIB_ALGEBRA_NATIVE_NTT_FALLBACK_H_
#define PRIVACY_PROOFS_ZK_LIB_ALGEBRA_NATIVE_NTT_FALLBACK_H_

#include <stddef.h>
#include <stdio.h>

#include <atomic>

namespace proofs {

// A native Reed-Solomon NTT needs a root of unity whose order is at least the
// codeword length, which the base field supplies only up to its 2-adicity:
// 4096 over GF(12289) (12288 = 3 * 2^12) and 8192 over GF(8380417)
// (8380416 = 1023 * 2^13).  Past that the encoder falls back to CRT
// convolution, which is correct but roughly halves commitment throughput -- on
// the Falcon ring arm, commit went 31.6 to 54.1 ms when block_enc crossed
// 4096.
//
// The caller asks for the native transform and otherwise gets the fallback
// with no signal, and the codeword length is not something the caller picks:
// LigeroParam derives block_enc from (nw, nq, rate, req) to minimise predicted
// proof size in powers of two, so it moves when the rate or the circuit does.
// Both Falcon native arms sit exactly on 4096, one step from the fallback.
//
// Writes to stderr rather than through util/log.h, because every PQ test calls
// set_log_level(ERROR) to quiet intermediate output and would therefore
// suppress a WARNING.  This is one line per process, matching how the other
// layout diagnostics here (PQ_LIGERO) report.
//
// Templated on the limit so encoders over different base fields do not share
// one another's flag.
template <size_t kLimit>
inline void warn_native_ntt_fallback(const char* field, size_t m) {
  static std::atomic<bool> warned{false};
  if (warned.exchange(true)) return;
  std::fprintf(stderr,
               "warning: native RS NTT requested but codeword length %zu "
               "exceeds %zu, the largest power of two dividing the order of "
               "%s*; falling back to CRT convolution (correct, about 2x "
               "slower to commit)\n",
               m, kLimit, field);
  std::fflush(stderr);
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ALGEBRA_NATIVE_NTT_FALLBACK_H_
