// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host's message part of a hash buffer (message.h's
// Layout), the witness member a proof of possession commits: the message,
// its padding at HEAD + |MSG| and zeros, built without branching on the
// length (ct.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_MESSAGE_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_MESSAGE_BUILDERS_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"

namespace proofs::gordiehowe::lib::message {

namespace host {

// MSG zero-extended to LAYOUT's part.
inline std::vector<uint8_t> part_of(const Layout &l,
                                    const std::vector<uint8_t> &msg) {
  if (msg.size() > l.max)
    fail("message part: a message of " + std::to_string(msg.size()) +
         " bytes, at most " + std::to_string(l.max));
  std::vector<uint8_t> b = msg;
  b.resize(l.part, 0);
  return b;
}

}  // namespace host

// The message part of SHAKE256's buffer: MSG, the suffix 0x1F at buffer
// byte HEAD + |MSG| and 0x80 at the last byte of that block (FIPS 202's
// pad10*1), zeros.
inline std::vector<uint8_t> shake256_part(const Layout &l,
                                          const std::vector<uint8_t> &msg) {
  std::vector<uint8_t> b = host::part_of(l, msg);
  const uint64_t rate = lib::keccak::kShake256.rate;
  const uint8_t suffix = lib::keccak::kShake256.suffix;
  const uint64_t at = l.head + msg.size();
  const uint64_t end =
      rate * (uint64_t(ct::Divisor64(rate).divmod(at).q) + 1) - 1;
  for (size_t i = 0; i < l.part; ++i) {
    const uint64_t j = l.head + i;
    b[i] ^= uint8_t(suffix & ct::mask(ct::eq(j, at)));
    b[i] ^= uint8_t(0x80 & ct::mask(ct::eq(j, end)));
  }
  return b;
}
// The message part of SHA-256's buffer: MSG, 0x80 at byte |MSG|, zeros,
// and the 64-bit big-endian bit length 8 |MSG| ending block
// ceil((|MSG| + 9) / 64) (FIPS 180-4, section 5.1.1).
inline std::vector<uint8_t> sha256_part(const Layout &l,
                                        const std::vector<uint8_t> &msg) {
  std::vector<uint8_t> b = host::part_of(l, msg);
  const uint64_t len = msg.size();
  const uint64_t end = 64 * uint64_t(ct::Divisor64(64).divmod(len + 72).q);
  const uint64_t bits = 8 * len;
  for (size_t i = 0; i < l.part; ++i) {
    b[i] |= uint8_t(0x80 & ct::mask(ct::eq(i, len)));
    const uint64_t in = ct::lt(i, end) & (ct::lt(i, end - 8) ^ 1);
    const uint64_t o = (i + 8 - end) & 7;
    b[i] |= uint8_t((bits >> (8 * (7 - o))) & ct::mask(in));
  }
  return b;
}

}  // namespace proofs::gordiehowe::lib::message

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_MESSAGE_BUILDERS_H_
