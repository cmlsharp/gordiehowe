// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the fork's lib/circuits/tests/pq/ml_dsa/ml_dsa_mu.h
// (mac-bench 8d8e0aa4) without its KeccakSponge overload (fork-only
// circuits/keccak); everything else unchanged.
//
// ML-DSA (FIPS 204) mu validation -- the message binding that the field-split
// verify was MISSING.  The H-world hash side asserts SHAKE256(mu || w1) == c_tilde
// but takes `mu` as a committed prover input, with nothing tying it to the actual
// message: a prover could commit any mu that makes the check pass, i.e. "prove" a
// signature over an arbitrary message.  UNSOUND.
//
// Fix: derive mu IN-CIRCUIT per FIPS 204 and feed the derived value into the
// c_tilde check (so mu is no longer a free input):
//
//   mu = SHAKE256( tr || IntegerToBytes(0,1) || IntegerToBytes(|ctx|,1) || ctx || M , 64 )
//
// tr = SHAKE256(pk, 64) is a deterministic function of the PUBLIC key, so the
// verifier supplies tr as a public input (no reason to hide it or let the prover
// pick it).  M is the message (committed if it must stay private, e.g. selective
// disclosure).  For a 32-byte message + empty ctx the SHAKE input is
// 64 + 2 + 32 = 98 bytes < 136 (rate) -> ONE Keccak-f permutation.
//
// (To also bind tr to pk, run tr = SHAKE256(pk) in-circuit as well -- ~10 more
// Keccak-f for the 1312-byte -44 key.  Kept out here: tr is public and
// verifier-recomputable, so tr-forgery is not a prover degree of freedom.)

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_MU_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_MU_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "util/panic.h"

namespace proofs {

// Host: the FIPS 204 message representative tr || 0x00 || |ctx| || ctx || M.
inline std::vector<uint8_t> ml_dsa_mu_input(const std::vector<uint8_t>& tr,
                                            const std::vector<uint8_t>& msg,
                                            const std::vector<uint8_t>& ctx = {}) {
  check(ctx.size() <= 255, "ML-DSA context exceeds 255 bytes");
  std::vector<uint8_t> in = tr;                       // 64 bytes
  in.push_back(0x00);                                 // domain separator (pure)
  in.push_back((uint8_t)ctx.size());                  // |ctx|
  in.insert(in.end(), ctx.begin(), ctx.end());
  in.insert(in.end(), msg.begin(), msg.end());
  return in;
}

// Host: mu = SHAKE256(tr || M', 64).
inline std::array<uint8_t, 64> ml_dsa_mu_ref(const std::vector<uint8_t>& tr,
                                             const std::vector<uint8_t>& msg,
                                             const std::vector<uint8_t>& ctx = {}) {
  auto in = ml_dsa_mu_input(tr, msg, ctx);
  std::array<uint8_t, 64> mu{};
  Sha3Reference::shake256Hash(in.data(), in.size(), mu.data(), 64);
  return mu;
}

// Host: SHAKE block witnesses for the in-circuit mu derivation.
inline void ml_dsa_mu_witness(const std::vector<uint8_t>& tr,
                              const std::vector<uint8_t>& msg,
                              std::vector<Sha3Witness::BlockWitness>& bws,
                              const std::vector<uint8_t>& ctx = {}) {
  Sha3Witness::compute_witness_shake256(ml_dsa_mu_input(tr, msg, ctx), 64, bws);
}

// The FIPS 204 message representative tr || 0x00 || |ctx| || ctx || M as
// wires.  tr (public) and msg (committed) are v8 wires; ctx_len is a
// compile-time constant with ctx bytes given as v8 wires.
template <class Logic>
std::vector<typename Logic::v8> ml_dsa_mu_input(
    const Logic& lc, const std::array<typename Logic::v8, 64>& tr,
    const std::vector<typename Logic::v8>& msg,
    const std::vector<typename Logic::v8>& ctx) {
  check(ctx.size() <= 255, "ML-DSA context exceeds 255 bytes");
  using v8 = typename Logic::v8;
  std::vector<v8> in(tr.begin(), tr.end());
  in.push_back(lc.template vbit<8>(0));                 // domain separator
  in.push_back(lc.template vbit<8>(ctx.size()));        // |ctx|
  in.insert(in.end(), ctx.begin(), ctx.end());
  in.insert(in.end(), msg.begin(), msg.end());
  return in;
}

template <class Logic>
std::array<typename Logic::v8, 64> ml_dsa_mu_bytes(
    const std::vector<typename Logic::v8>& out) {
  std::array<typename Logic::v8, 64> mu;
  for (size_t i = 0; i < 64; ++i) mu[i] = out[i];
  return mu;
}

// In-circuit: derive mu = SHAKE256(tr || 0x00 || |ctx| || ctx || M) in GKR
// over the block witnesses bws, and return the 64 squeezed bytes.
// The returned mu should be FED into the c_tilde' check (assert_ctilde), replacing
// the previously free `mu` input -- that is what closes the binding.
template <class Logic>
std::array<typename Logic::v8, 64> ml_dsa_derive_mu(
    const Logic& lc, const std::array<typename Logic::v8, 64>& tr,
    const std::vector<typename Logic::v8>& msg,
    const std::vector<typename Sha3Circuit<Logic>::BlockWitness>& bws,
    const std::vector<typename Logic::v8>& ctx = {}) {
  Sha3Circuit<Logic> sha3(lc);
  std::vector<typename Logic::v8> out(64);
  sha3.assert_shake256(ml_dsa_mu_input(lc, tr, msg, ctx), 64, out, bws);
  return ml_dsa_mu_bytes<Logic>(out);
}

}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_MU_H_
