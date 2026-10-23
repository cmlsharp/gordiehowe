// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon native tests (falcon_native_test*.cc, one binary): the timing
// helpers, the compiled fixture and the report parser they share. Each test
// file has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_FIXTURE_H_

#include "bench/timing.h"
#include "gordiehowe/examples/falcon/falcon_native.h"
#include "gordiehowe/examples/falcon/falcon_native_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/shared/private_message_testing.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <memory>
#include <random>
#include <regex>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::falcon::native {
namespace {

using bench::Clock;
using bench::ms_since;

// An instance on the benchmark instance's nonce and message with chosen signed
// coefficients of s1 and s2 (an invertible s2), and h = (c - s1) / s2: a
// statement whose signature is not valid when the coefficients break the
// norm or the encoding budget.
reference::Instance chosen_instance(const std::function<int64_t(size_t)> &s1c,
                                   const std::function<int64_t(size_t)> &s2c) {
  reference::Instance in = reference::instance();
  const auto zetas = falcon_ntt_zetas(kN, kQ);
  std::vector<uint64_t> s1(kN), s2(kN);
  for (size_t i = 0; i < kN; ++i) {
    s1[i] = uint64_t((s1c(i) % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
    s2[i] = uint64_t((s2c(i) % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
  }
  auto s1hat = s1, s2hat = s2;
  falcon_ntt_ref(s1hat, zetas, kQ);
  falcon_ntt_ref(s2hat, zetas, kQ);
  for (auto x : s2hat) EXPECT_NE(x, 0u) << "s2 is not invertible";
  for (size_t i = 0; i < kN; ++i)
    in.hhat[i] = uint64_t((__uint128_t)((in.chat[i] + kQ - s1hat[i]) % kQ) *
                          falcon_powmod(s2hat[i], kQ - 2, kQ) % kQ);
  in.s2 = s2;
  return in;
}

// A compiled system of profile P on an instance.
template <class P>
struct Fixture {
  using T = FalconNativeSystem<P>;
  using Value = typename T::Sys::Value;
  using ProveOptions = typename T::Sys::ProveOptions;
  using AF = typename P::FalconNativeField;
  using HF = typename P::HashField;
  using AV = std::vector<typename AF::Elt>;
  using HV = std::vector<typename HF::Elt>;
  Env<P> env;
  reference::Instance in;
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(reference::Instance i = reference::instance())
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


// One domain's circuit sizes in a compile report.
struct DomainSize {
  size_t layers = 0, quad = 0, committed = 0, inputs = 0, publics = 0,
         affine = 0;
};
DomainSize domain_size(const std::string &report, const std::string &d) {
  DomainSize s;
  const auto at = report.find("domain " + d + " (");
  if (at == std::string::npos) return s;
  const std::string r = report.substr(at, 3000);
  std::smatch m;
  if (std::regex_search(r, m, std::regex(R"(ninputs=(\d+) public=(\d+) committed=(\d+))"))) {
    s.inputs = std::stoul(m[1]);
    s.publics = std::stoul(m[2]);
    s.committed = std::stoul(m[3]);
  }
  if (std::regex_search(r, m, std::regex(R"(layers=(\d+))")))
    s.layers = std::stoul(m[1]);
  if (std::regex_search(r, m, std::regex(R"(quad_terms=(\d+))")))
    s.quad = std::stoul(m[1]);
  if (std::regex_search(r, m, std::regex(R"(affine_rows=(\d+))")))
    s.affine = std::stoul(m[1]);
  return s;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::native

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_FIXTURE_H_
