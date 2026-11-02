// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// SHAKE256(prefix || M) for a message M of private length L <= MAX, on
// upstream's Sha3Circuit (its Keccak-f[1600] with block witnesses) and
// Sha3Witness: the baselines' form of GordieHowe's private-length message
// (lib/gordiehowe/lib/message.h), for the ML-DSA mu and Falcon's
// HashToPoint input.
//
// The circuit commits MAX message bytes and MAX in-message flags
// f_0..f_{MAX-1}, f_i = [i < L]. The flags are bits (Logic::input) and
// monotone (f_{i+1} implies f_i), so they are 1^L 0^(MAX-L) for exactly one
// L in [0, MAX]. Byte P + i of the padded input (P = |prefix|) is
//   (f_i ? M_i : 0) xor (e_i ? 0x1F : 0),  e_i = f_{i-1} and not f_i
// (f_{-1} = 1, f_MAX = 0), so e marks exactly position P + L, where FIPS
// 202's pad10*1 puts 0x1F; byte 135 of the block carries 0x80. The bytes of
// M past L do not enter the hash.
//
// Condition (checked when the circuit is built): the message and its first
// padding byte fit the prefix's last partial block, (P mod 136) + MAX < 135,
// so the number of absorbed blocks, (P + L + 136) / 136, does not depend on
// L, and the host's block witnesses of prefix || M (upstream's
// Sha3Witness::compute_witness_shake256 on the actual message) have the
// count the circuit consumes.

#ifndef LFB_COMMON_SHAKE256_PRIVATE_LENGTH_H_
#define LFB_COMMON_SHAKE256_PRIVATE_LENGTH_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "util/panic.h"

namespace proofs::lfb {

constexpr size_t kShake256Rate = 136;

// Whether a prefix of PREFIX bytes and a message of at most MAX bytes meet
// the condition above.
constexpr bool shake256_private_length_fits(size_t prefix, size_t max) {
  return prefix % kShake256Rate + max + 1 < kShake256Rate;
}

// The number of block witnesses of SHAKE256(prefix || M) with OUTLEN output
// bytes, for every |M| <= MAX (upstream's count).
inline size_t shake256_private_length_blocks(size_t prefix, size_t max,
                                             size_t outlen) {
  check(shake256_private_length_fits(prefix, max),
        "shake256_private_length: the message does not fit the last block");
  return (prefix + max + kShake256Rate) / kShake256Rate +
         (outlen == 0 ? 0 : (outlen - 1) / kShake256Rate);
}

// Host: the in-message flags of a message of LENGTH bytes at most MAX.
inline std::vector<uint8_t> shake256_in_message(size_t length, size_t max) {
  check(length <= max, "shake256_in_message: the message exceeds its maximum");
  std::vector<uint8_t> f(max, 0);
  for (size_t i = 0; i < length; ++i) f[i] = 1;
  return f;
}

// Host: the message padded with zeros to MAX bytes.
inline std::vector<uint8_t> shake256_padded_message(
    const std::vector<uint8_t>& msg, size_t max) {
  check(msg.size() <= max, "shake256_padded_message: the message exceeds its maximum");
  std::vector<uint8_t> m = msg;
  m.resize(max, 0);
  return m;
}

// Circuit: OUTLEN bytes of SHAKE256(PREFIX || M) into OUT, M the first L
// bytes of MSG (MAX bytes) as the flags IN_MESSAGE (MAX bits) select, over
// the block witnesses BWS (shake256_private_length_blocks of them). Asserts
// the flags monotone.
template <class Logic>
void assert_shake256_private_length(
    const Logic& lc, const std::vector<typename Logic::v8>& prefix,
    const std::vector<typename Logic::v8>& msg,
    const std::vector<typename Logic::BitW>& in_message, size_t outlen,
    std::vector<typename Logic::v8>& out,
    const std::vector<typename Sha3Circuit<Logic>::BlockWitness>& bws) {
  using v8 = typename Logic::v8;
  using v64 = typename Logic::template bitvec<64>;
  using BitW = typename Logic::BitW;
  constexpr size_t rate = kShake256Rate;
  const size_t max = msg.size();
  check(in_message.size() == max, "shake256_private_length: one flag per byte");
  const size_t nabsorb = prefix.size() / rate + 1;
  const size_t nsqueeze = outlen == 0 ? 0 : (outlen - 1) / rate;
  check(bws.size() == shake256_private_length_blocks(prefix.size(), max, outlen),
        "shake256_private_length: block witness count");
  check(bws.size() == nabsorb + nsqueeze,
        "shake256_private_length: block witness count");
  Sha3Circuit<Logic> sha3(lc);

  // f_{i+1} implies f_i.
  for (size_t i = 0; i + 1 < max; ++i) {
    lc.assert_implies(in_message[i + 1], in_message[i]);
  }

  // The state before block b: zero, or the previous block's output.
  auto state_before = [&](size_t b, v64 A[5][5]) {
    for (size_t x = 0; x < 5; ++x) {
      for (size_t y = 0; y < 5; ++y) {
        if (b == 0) {
          A[x][y] = lc.template vbit<64>(0);
        } else {
          A[x][y] = bws[b - 1].a_intermediate[23][x][y];
        }
      }
    }
  };
  // FIPS 202 Algorithm 8, step 6: the block's RATE bytes xored into A.
  auto xorin = [&](v64 A[5][5], const std::vector<v8>& block) {
    size_t x = 0, y = 0;
    for (size_t i = 0; i < rate; i += 8) {
      v64 a;
      for (size_t b = 0; b < 8; ++b) {
        for (size_t j = 0; j < 8; ++j) a[b * 8 + j] = block[i + b][j];
      }
      A[x][y] = lc.vxor(A[x][y], a);
      if (++x == 5) {
        ++y;
        x = 0;
      }
    }
  };

  // The prefix's full blocks.
  size_t bw = 0;
  for (size_t b = 0; b + 1 < nabsorb; ++b) {
    std::vector<v8> block(prefix.begin() + b * rate,
                          prefix.begin() + (b + 1) * rate);
    v64 A[5][5];
    state_before(bw, A);
    xorin(A, block);
    sha3.keccak_f_1600(A, bws[bw++]);
  }

  // The last block: the prefix's tail, the selected message bytes, the
  // padding at P + L, zeros, and 0x80 in byte 135.
  const size_t p = prefix.size() % rate;
  std::vector<v8> block(rate, lc.template vbit<8>(0));
  for (size_t i = 0; i < p; ++i) block[i] = prefix[(nabsorb - 1) * rate + i];
  const v8 pad1 = lc.template vbit<8>(0x1F);
  for (size_t i = 0; i <= max; ++i) {
    // e_i = f_{i-1} and not f_i, with f_{-1} = 1 and f_MAX = 0.
    const BitW prev = i == 0 ? lc.bit(1) : in_message[i - 1];
    const BitW e = i == max ? prev : lc.land(prev, lc.lnot(in_message[i]));
    v8 byte = lc.vand(e, pad1);
    if (i < max) byte = lc.vxor(byte, lc.vand(in_message[i], msg[i]));
    block[p + i] = byte;
  }
  block[rate - 1] = lc.vxor(block[rate - 1], lc.template vbit<8>(0x80));
  {
    v64 A[5][5];
    state_before(bw, A);
    xorin(A, block);
    sha3.keccak_f_1600(A, bws[bw++]);
  }

  // The squeezed blocks.
  for (size_t i = 0; i < nsqueeze; ++i) {
    v64 A[5][5];
    state_before(bw, A);
    sha3.keccak_f_1600(A, bws[bw++]);
  }
  check(bw == bws.size(), "shake256_private_length: unused block witnesses");

  // The output: the first RATE bytes of the state after the last absorbed
  // block, then of each squeezed block's.
  out.resize(outlen);
  for (size_t o = 0; o < outlen; ++o) {
    const size_t blk = nabsorb - 1 + o / rate, i = o % rate;
    const size_t lane = i / 8, b = i % 8;
    const v64& a = bws[blk].a_intermediate[23][lane % 5][lane / 5];
    for (size_t j = 0; j < 8; ++j) out[o][j] = a[b * 8 + j];
  }
}

// Host: the block witnesses of SHAKE256(PREFIX || MSG) with OUTLEN output
// bytes (upstream's), for a message of at most MAX bytes.
inline void shake256_private_length_witness(
    const std::vector<uint8_t>& prefix, const std::vector<uint8_t>& msg,
    size_t max, size_t outlen, std::vector<Sha3Witness::BlockWitness>& bws) {
  check(msg.size() <= max, "shake256_private_length: the message exceeds its maximum");
  std::vector<uint8_t> in = prefix;
  in.insert(in.end(), msg.begin(), msg.end());
  bws.clear();
  Sha3Witness::compute_witness_shake256(in, outlen, bws);
  check(bws.size() == shake256_private_length_blocks(prefix.size(), max, outlen),
        "shake256_private_length: host block witness count");
}

}  // namespace proofs::lfb

#endif  // LFB_COMMON_SHAKE256_PRIVATE_LENGTH_H_
