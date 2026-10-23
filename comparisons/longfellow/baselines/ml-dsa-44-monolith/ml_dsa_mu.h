// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA (FIPS 204) message representative mu, derived in the circuit.
//
// Fork-derived: lib/circuits/tests/pq/ml_dsa/ml_dsa_mu.h of the fork
// (branch mac-bench, 8d8e0aa4), less its KeccakSponge overload (a fork
// gadget).  Built only on upstream's Sha3Circuit and Sha3Witness.
//
//   mu = SHAKE256(tr || IntegerToBytes(0, 1) || IntegerToBytes(|ctx|, 1)
//                 || ctx || M, 64)
//
// tr = SHAKE256(pk, 64) is a function of the public key and is a public
// input (upstream's MLDSAVerify::Pk carries it); M is committed.
#ifndef LFB_BASELINES_ML_DSA_44_MONOLITH_ML_DSA_MU_H_
#define LFB_BASELINES_ML_DSA_44_MONOLITH_ML_DSA_MU_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "util/panic.h"

namespace proofs {

// Host: tr || 0x00 || |ctx| || ctx || M.
inline std::vector<uint8_t> ml_dsa_mu_input(const std::vector<uint8_t>& tr,
                                            const std::vector<uint8_t>& msg,
                                            const std::vector<uint8_t>& ctx) {
  check(ctx.size() <= 255, "ML-DSA context exceeds 255 bytes");
  std::vector<uint8_t> in = tr;
  in.push_back(0x00);
  in.push_back(static_cast<uint8_t>(ctx.size()));
  in.insert(in.end(), ctx.begin(), ctx.end());
  in.insert(in.end(), msg.begin(), msg.end());
  return in;
}

// Host: the SHAKE256 block witnesses of the derivation.
inline void ml_dsa_mu_witness(const std::vector<uint8_t>& tr,
                              const std::vector<uint8_t>& msg,
                              std::vector<Sha3Witness::BlockWitness>& bws,
                              const std::vector<uint8_t>& ctx) {
  Sha3Witness::compute_witness_shake256(ml_dsa_mu_input(tr, msg, ctx), 64,
                                        bws);
}

// Circuit: tr || 0x00 || |ctx| || ctx || M as byte wires; |ctx| is a
// circuit constant.
template <class Logic>
std::vector<typename Logic::v8> ml_dsa_mu_input(
    const Logic& lc, const std::array<typename Logic::v8, 64>& tr,
    const std::vector<typename Logic::v8>& msg,
    const std::vector<typename Logic::v8>& ctx) {
  check(ctx.size() <= 255, "ML-DSA context exceeds 255 bytes");
  std::vector<typename Logic::v8> in(tr.begin(), tr.end());
  in.push_back(lc.template vbit<8>(0));
  in.push_back(lc.template vbit<8>(ctx.size()));
  in.insert(in.end(), ctx.begin(), ctx.end());
  in.insert(in.end(), msg.begin(), msg.end());
  return in;
}

// Circuit: mu over the block witnesses bws, for assert_valid_signature_on_mu.
template <class Logic>
std::array<typename Logic::v8, 64> ml_dsa_derive_mu(
    const Logic& lc, const std::array<typename Logic::v8, 64>& tr,
    const std::vector<typename Logic::v8>& msg,
    const std::vector<typename Sha3Circuit<Logic>::BlockWitness>& bws,
    const std::vector<typename Logic::v8>& ctx) {
  Sha3Circuit<Logic> sha3(lc);
  std::vector<typename Logic::v8> out(64);
  sha3.assert_shake256(ml_dsa_mu_input(lc, tr, msg, ctx), 64, out, bws);
  std::array<typename Logic::v8, 64> mu;
  for (size_t i = 0; i < 64; ++i) mu[i] = out[i];
  return mu;
}

}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_MONOLITH_ML_DSA_MU_H_
