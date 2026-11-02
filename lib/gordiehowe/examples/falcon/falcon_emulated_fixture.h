// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon emulated tests (falcon_emulated_test*.cc, one binary): the
// benchmark instance, its host witness and the compiled fixture they share.
// Each test file has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_FIXTURE_H_

#include "bench/timing.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/falcon/falcon_emulated_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/shared/private_message_testing.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <random>
#include <set>
#include <string>
#include <vector>

#include "circuits/ntt/falcon_ntt.h"
#include "gordiehowe/examples/falcon/falcon_encoding.h"
#include "gordiehowe/examples/falcon/falcon_hash_to_point.h"
#include "gordiehowe/examples/falcon/falcon_instance_testing.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

using bench::Clock;
using bench::ms_since;
using bench::median;


// A bounded verification instance of set S: short coefficients of s1 and
// s2 from RNG (instance::short_residue) until NTT(s2) is invertible and
// (s1, s2) is a valid signature, and h = (c - s1) / s2 in the NTT domain
// (key generation is outside the proved statement).
template <class S, class RNG>
void short_instance(const std::vector<uint64_t> &chat,
                    const std::vector<uint64_t> &zetas, uint64_t q, RNG &rng,
                    std::vector<uint64_t> &s2, std::vector<uint64_t> &hhat) {
  const size_t n = chat.size();
  s2.resize(n);
  hhat.resize(n);
  std::vector<uint64_t> s1(n);
  for (;;) {
    for (size_t i = 0; i < n; ++i) {
      s1[i] = instance::short_residue<S>(rng);
      s2[i] = instance::short_residue<S>(rng);
    }
    auto s1hat = s1;
    auto s2hat = s2;
    falcon_ntt_ref(s1hat, zetas, q);
    falcon_ntt_ref(s2hat, zetas, q);
    bool invertible = true;
    for (auto x : s2hat) invertible &= x != 0;
    if (!invertible || !instance::valid_signature<S>(s1, s2)) continue;
    for (size_t i = 0; i < n; ++i) {
      hhat[i] = static_cast<uint64_t>(
          (__uint128_t)((chat[i] + q - s1hat[i]) % q) *
          falcon_powmod(s2hat[i], q - 2, q) % q);
    }
    return;
  }
}

// The benchmark instance of set S: nonce and message from
// mt19937(20260915), then the short (s1, s2) and h = (c - s1) / s2 of
// short_instance, from the same generator.
struct Instance {
  std::vector<uint8_t> nonce, msg;
  std::vector<uint64_t> s2, hhat, hcoeff;
  FalconH2PWitness hw;
};
template <class S = Falcon512>
Instance bench_instance(size_t msg_len = 32) {
  Instance in;
  std::mt19937 g(20260915);
  in.nonce.resize(kNonceBytes);
  in.msg.resize(msg_len);
  for (auto &x : in.nonce) x = uint8_t(g());
  for (auto &x : in.msg) x = uint8_t(g());
  in.hw = falcon_hash_to_point(in.nonce, in.msg, S::kN, S::kSamples);
  const auto zetas = falcon_ntt_zetas(S::kN, kQ);
  std::vector<uint64_t> chat(S::kN);
  for (size_t i = 0; i < S::kN; ++i) chat[i] = in.hw.c[i] % kQ;
  falcon_ntt_ref(chat, zetas, kQ);
  short_instance<S>(chat, zetas, kQ, g, in.s2, in.hhat);
  in.hcoeff = emulated_ntt::decode(in.hhat, zetas, kQ);
  return in;
}

// An instance of set S on the same nonce and message with chosen signed
// coefficients of s1 and s2 (an invertible s2), and h = (c - s1) / s2: a
// statement whose signature is not valid when the coefficients break the
// norm or the encoding budget.
template <class S = Falcon512>
Instance chosen_instance(const std::function<int64_t(size_t)> &s1c,
                         const std::function<int64_t(size_t)> &s2c) {
  constexpr size_t kN = S::kN;
  Instance in = bench_instance<S>();
  const auto zetas = falcon_ntt_zetas(kN, kQ);
  std::vector<uint64_t> chat(kN), s1(kN), s2(kN);
  for (size_t i = 0; i < kN; ++i) {
    chat[i] = in.hw.c[i] % kQ;
    s1[i] = uint64_t((s1c(i) % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
    s2[i] = uint64_t((s2c(i) % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
  }
  falcon_ntt_ref(chat, zetas, kQ);
  auto s1hat = s1, s2hat = s2;
  falcon_ntt_ref(s1hat, zetas, kQ);
  falcon_ntt_ref(s2hat, zetas, kQ);
  for (auto x : s2hat) EXPECT_NE(x, 0u) << "s2 is not invertible";
  for (size_t i = 0; i < kN; ++i)
    in.hhat[i] = uint64_t((__uint128_t)((chat[i] + kQ - s1hat[i]) % kQ) *
                          falcon_powmod(s2hat[i], kQ - 2, kQ) % kQ);
  in.s2 = s2;
  in.hcoeff = emulated_ntt::decode(in.hhat, zetas, kQ);
  return in;
}

// The host witness from the reference helpers (falcon_ntt_ref,
// falcon_encoding.h's falcon_encoding_advice, emulated_ntt's integer
// convolution): s1, the quotient dq, the centered magnitudes of s1, the
// norm (the sum of the squared magnitudes of s1 and s2), s2's encoding
// advice and the MAC chunks of c.
template <class P, class S = Falcon512>
struct HostWitness {
  std::vector<uint64_t> s1, dq, mag1;
  uint64_t norm = 0;
  FalconEncodingAdvice enc;
  std::vector<typename P::MacField::Elt> cref;

  explicit HostWitness(const Instance &in) {
    const size_t n = S::kN;
    const uint64_t Q = kQ;
    const auto zetas = falcon_ntt_zetas(n, Q);
    const auto &hw = in.hw;
    const auto &s2 = in.s2;
    const auto &hhat = in.hhat;
    std::vector<uint64_t> craw(n), c_hat(n);
    for (size_t i = 0; i < n; ++i) {
      craw[i] = hw.c[i];
      c_hat[i] = hw.c[i] % Q;
    }
    falcon_ntt_ref(c_hat, zetas, Q);
    std::vector<uint64_t> s1hat(n);
    {
      std::vector<uint64_t> s2hat = s2;
      falcon_ntt_ref(s2hat, zetas, Q);
      for (size_t i = 0; i < n; ++i)
        s1hat[i] = (uint64_t)(((__uint128_t)c_hat[i] + (__uint128_t)Q * Q -
                               (__uint128_t)s2hat[i] * hhat[i]) %
                              Q);
    }
    s1 = s1hat;
    falcon_intt_ref(s1, zetas, Q);
    auto mag = [Q](uint64_t v) { return v <= Q / 2 ? v : Q - v; };
    for (uint64_t v : s1) mag1.push_back(mag(v));
    for (uint64_t a : mag1) norm += a * a;
    for (uint64_t v : s2) norm += mag(v) * mag(v);
    // A multiple of q at least n (q - 1) q + q + 65535, so that dq >= 0 for
    // c < 2^16, h and s2 below q and s1 at most q.
    const uint64_t Bp = ((n * (Q - 1) * Q + Q + 65535 + Q - 1) / Q) * Q;
    auto hs2 = emulated_ntt::integer_convolution(in.hcoeff, s2);
    dq.resize(n);
    for (size_t j = 0; j < n; ++j) {
      const __int128_t residual = (__int128_t)Bp + craw[j] - hs2[j] - s1[j];
      dq[j] = (uint64_t)(residual / Q);
    }
    enc = falcon_encoding_advice(s2, Q, S::kHighBudget);
    using MF = typename P::MacField;
    const MF mf;
    const size_t kW = MF::kBits, nch = 16 * n / kW;
    std::vector<uint8_t> buf((16 * n + 7) / 8, 0);
    for (size_t j = 0; j < n; ++j)
      for (size_t b = 0; b < 16; ++b)
        if ((hw.c[j] >> b) & 1)
          buf[(j * 16 + b) / 8] |= 1u << ((j * 16 + b) % 8);
    cref.resize(nch);
    for (size_t c = 0; c < nch; ++c)
      cref[c] = mf.of_bytes_field(&buf[c * MF::kBytes]).value();
  }
};

// A compiled system of profile P on an instance.
template <class P, class S = Falcon512>
struct Fixture {
  using Set = S;
  using T = FalconEmulatedSystem<P, S>;
  using Value = typename T::Sys::Value;
  using ProveOptions = typename T::Sys::ProveOptions;
  using AF = typename P::EmulatedField;
  using HF = typename P::HashField;
  using AV = std::vector<typename AF::Elt>;
  using HV = std::vector<typename HF::Elt>;
  Env<P> env;
  Instance in;
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(Instance i = bench_instance<S>())
      : in(std::move(i)),
        t(env, in.msg.size()),
        c(t.compile()) {}

  typename T::Assignment witness() const {
    return t.witness(in.nonce, in.msg, in.s2);
  }
  // The cheating prover under TAMPER completes its proof; whether the
  // verifier accepts it.
  bool accepts(const std::function<void(size_t, Value &)> &tamper) const {
    auto prep = c->prepare(t.statement(in.hhat));
    ProveOptions opt;
    opt.tamper = tamper;
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    return prep.verify(prep.prove(witness(), rng, opt));
  }
  // Whether the honest prover's satisfaction check refuses.
  bool prover_refuses() const {
    auto prep = c->prepare(t.statement(in.hhat));
    SecureRandomEngine rng;
    try {
      prep.prove(witness(), rng);
    } catch (const std::runtime_error &) {
      return true;
    }
    return false;
  }
  size_t id(const std::string &name) const {
    const auto &N = t.cs.graph().nodes;
    for (size_t i = 0; i < N.size(); ++i)
      if (N[i].name == name) return i;
    ADD_FAILURE() << "no node " << name;
    return SIZE_MAX;
  }
};


}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_FIXTURE_H_
