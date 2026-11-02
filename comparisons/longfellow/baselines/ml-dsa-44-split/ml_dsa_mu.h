// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the ML-DSA (FIPS 204) message representative mu,
// derived in the circuit for a message of private length:
//
//   mu = SHAKE256(tr || IntegerToBytes(0, 1) || IntegerToBytes(|ctx|, 1)
//                 || ctx || M, 64)          (FIPS 204 Algorithm 7, line 6)
//
// tr = SHAKE256(pk, 64) is a function of the public key and a public input
// (the verifier computes it, ml_dsa_host.h's Statement); ctx is public, of
// a length fixed per circuit; M is committed as MAX bytes and MAX
// in-message flags [i < L] for its private length L <= MAX, and hashed by
// common/shake256_private_length.h on upstream's Sha3Circuit, as
// GordieHowe's mu hashes a message of private length (lib/gordiehowe/lib/
// message.h).  The returned mu feeds the c_tilde check, so it is no free
// input.  (The fork's ml_dsa_mu.h, mac-bench 8d8e0aa4, hashed a message of
// public length.)

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_MU_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_MU_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_circuit.h"
#include "shake256_private_length.h"
#include "util/panic.h"

namespace proofs {

// In-circuit: mu = SHAKE256(tr || 0x00 || |ctx| || ctx || M, 64) over the
// block witnesses BWS (lfb::shake256_private_length_blocks(66 + |ctx|, MAX,
// 64) of them), M the first L bytes of MSG (MAX bytes) as IN_MESSAGE (MAX
// flags) selects.  Returns the 64 squeezed bytes.
template <class Logic>
std::array<typename Logic::v8, 64> ml_dsa_derive_mu(
    const Logic& lc, const std::array<typename Logic::v8, 64>& tr,
    const std::vector<typename Logic::v8>& ctx,
    const std::vector<typename Logic::v8>& msg,
    const std::vector<typename Logic::BitW>& in_message,
    const std::vector<typename Sha3Circuit<Logic>::BlockWitness>& bws) {
  check(ctx.size() <= 255, "ML-DSA context exceeds 255 bytes");
  using v8 = typename Logic::v8;
  std::vector<v8> prefix(tr.begin(), tr.end());
  prefix.push_back(lc.template vbit<8>(0));           // domain separator
  prefix.push_back(lc.template vbit<8>(ctx.size()));  // |ctx|
  prefix.insert(prefix.end(), ctx.begin(), ctx.end());
  std::vector<v8> out;
  lfb::assert_shake256_private_length(lc, prefix, msg, in_message, 64, out,
                                      bws);
  std::array<v8, 64> mu;
  for (size_t i = 0; i < 64; ++i) mu[i] = out[i];
  return mu;
}

}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_MU_H_
