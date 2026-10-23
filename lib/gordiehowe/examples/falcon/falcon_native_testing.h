// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: test support for the Falcon-512 native system
// (falcon_native.h), which a standalone implementation does not need:
//   FalconNativeSystem     the relation with the assignments of example
//                          values
//   a_domain               domain A of a built system
//   export_plan            the compiled plan as a Lean data file
//                          (plan_export.h), the bench hook
//   reference::            the benchmark instance and its host s1

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

#include "circuits/ntt/falcon_ntt.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/examples/falcon/falcon_builders.h"
#include "gordiehowe/examples/falcon/falcon_hash_to_point.h"
#include "gordiehowe/examples/falcon/falcon_native.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/system_testing.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::falcon::native {

// The relation for messages of at most MAX_BYTES bytes, with the
// assignments of example values, for the tests and benchmarks that drive
// the prover directly.
template <class P>
struct FalconNativeSystem
    : RelationSystem<typename Env<P>::Sys, FalconStatement<Value>,
                     FalconWitness<Value>> {
  using E = Env<P>;
  using HF = typename E::HF;
  using AF = typename E::AF;
  using PH = typename E::PH;
  using Base = RelationSystem<typename E::Sys, FalconStatement<Value>,
                              FalconWitness<Value>>;
  using typename Base::Assignment;

  size_t max_bytes;

  FalconNativeSystem(const E &env, size_t max, const BuildOptions &build = {})
      : Base(falcon_native<P>(env, max, build)), max_bytes(max) {}

  Assignment statement(const std::vector<uint64_t> &hhat) const {
    return Base::statement(falcon_statement(hhat));
  }
  Assignment witness(const std::vector<uint8_t> &nonce,
                     const std::vector<uint8_t> &msg,
                     const std::vector<uint64_t> &s2) const {
    return Base::witness(falcon_witness(nonce, msg, s2, max_bytes));
  }
};

// Domain A of system S (falcon_native declares H, then A).
template <class P>
auto &a_domain(const typename Env<P>::Sys &cs) {
  using Sys = typename Env<P>::Sys;
  using D = Domain<typename Env<P>::AF>;
  auto *d = dynamic_cast<const D *>(cs.domains().at(1).get());
  if (d == nullptr) throw std::runtime_error("domain 1 is not A");
  return *d;
}

// The plan export of profile P (plan_export.h): the system as the bench
// builds it for MSG_LEN-byte messages, compiled,
// written to DIR/<lean_plan_module>.lean, and its realized program
// (plan_program.h) to DIR/<lean_program_module>.lean. Returns the plan's
// path.
template <class P>
std::string export_plan(const std::string &dir, const std::string &commit,
                        const std::string &run_id, size_t msg_len) {
  const Env<P> env;
  FalconNativeSystem<P> t(env, msg_len);
  const auto c = t.compile();
  const compiler::ExportMeta meta{"falcon-native", P::kId, commit, run_id,
                                  msg_len};
  return write_plan(*c, dir, meta);
}

namespace reference {

// The benchmark instance: nonce and message from
// mt19937(20260915), then centered s1 and s2 with |x| <= 90 from the same
// generator until NTT(s2) is invertible, and h = (c - s1) / s2 in the NTT
// domain.
struct Instance {
  std::vector<uint8_t> nonce, msg;
  std::vector<uint64_t> s2, hhat, chat;
  FalconH2PWitness hw;
};
inline Instance instance(size_t msg_len = 32) {
  Instance in;
  std::mt19937 g(20260915);
  in.nonce.resize(kNonceBytes);
  in.msg.resize(msg_len);
  for (auto &x : in.nonce) x = uint8_t(g());
  for (auto &x : in.msg) x = uint8_t(g());
  in.hw = falcon_hash_to_point(in.nonce, in.msg, kN);
  const auto zetas = falcon_ntt_zetas(kN, kQ);
  auto ctr = [](uint64_t v) {
    return uint64_t(((int)(v % 181) - 90 + (int)kQ) % (int)kQ);
  };
  in.chat.resize(kN);
  for (size_t i = 0; i < kN; ++i) in.chat[i] = in.hw.c[i] % kQ;
  falcon_ntt_ref(in.chat, zetas, kQ);
  std::vector<uint64_t> s1c(kN);
  in.s2.resize(kN);
  in.hhat.resize(kN);
  for (;;) {
    for (size_t i = 0; i < kN; ++i) {
      s1c[i] = ctr(g());
      in.s2[i] = ctr(g());
    }
    std::vector<uint64_t> s1hat = s1c, s2hat = in.s2;
    falcon_ntt_ref(s1hat, zetas, kQ);
    falcon_ntt_ref(s2hat, zetas, kQ);
    bool ok = true;
    for (size_t i = 0; i < kN; ++i) ok = ok && s2hat[i] != 0;
    if (!ok) continue;
    for (size_t i = 0; i < kN; ++i)
      in.hhat[i] = uint64_t((__uint128_t)((in.chat[i] + kQ - s1hat[i]) % kQ) *
                            falcon_powmod(s2hat[i], kQ - 2, kQ) % kQ);
    break;
  }
  return in;
}

// s1 = c - s2 h in the coefficient domain: INTT(c_hat - NTT(s2) h_hat).
inline std::vector<uint64_t> s1(const Instance &in) {
  const auto zetas = falcon_ntt_zetas(kN, kQ);
  std::vector<uint64_t> s2hat = in.s2;
  falcon_ntt_ref(s2hat, zetas, kQ);
  std::vector<uint64_t> out(kN);
  for (size_t i = 0; i < kN; ++i)
    out[i] = (in.chat[i] + kQ - uint64_t((__uint128_t)s2hat[i] * in.hhat[i] % kQ)) % kQ;
  falcon_intt_ref(out, zetas, kQ);
  return out;
}

}  // namespace reference

}  // namespace proofs::gordiehowe::examples::falcon::native

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_TESTING_H_
