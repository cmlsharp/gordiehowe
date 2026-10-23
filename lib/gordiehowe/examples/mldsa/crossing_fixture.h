// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The crossing tests and bench (crossing_test.cc, crossing_bench.cc): the
// system that carries integers of H to A, and its sample integers. Each
// file has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_CROSSING_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_CROSSING_FIXTURE_H_

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

constexpr uint64_t kQ = 8380417;
constexpr size_t kW = 23;

template <class P>
struct CrossingSystem {
  using E = Env<P>;
  using HF = typename E::HF;
  using AF = typename E::AF;
  using Sys = typename E::Sys;
  using Value = typename Sys::Value;
  using HV = std::vector<typename HF::Elt>;
  using AV = std::vector<typename AF::Elt>;
  Sys cs{"crossing-test"};
  const E &env;
  size_t n;
  Ref<HF, Bit, Committed> x;

  CrossingSystem(const E &e, size_t count, Placement bit_checks)
      : env(e), n(count) {
    auto &H = cs.domain(domain_profile<P>(env.hf, env.rsh), "H");
    auto ap = domain_profile<P>(env.af, env.rsa);
    auto &A = cs.domain(ap, "A");
    A.pin_bit_checks(bit_checks);
    x = H.priv(Bit{}, "x", Shape({n, kW}));
    const Scope sc = cs.scope("crossing");
    // The bound is H's comparator: in F_q a range check of the integers
    // below q states nothing (their values wrap at q).
    assert_true(x.from_bits() < kQ, sc.name("below"));
    (void)x.to(sc[A], "bits");
  }
  typename Sys::Assignment witness(const std::vector<uint64_t> &v) const {
    HV b(n * kW, env.hf.zero());
    for (size_t i = 0; i < n; ++i)
      for (size_t j = 0; j < kW; ++j)
        if ((v[i] >> j) & 1) b[i * kW + j] = env.hf.one();
    typename Sys::Assignment w;
    w.set(x, b);
    return w;
  }
  size_t id(const std::string &name) const {
    const auto &N = cs.graph().nodes;
    for (size_t i = 0; i < N.size(); ++i)
      if (N[i].name == name) return i;
    throw std::runtime_error("no node named '" + name + "'");
  }
};

std::vector<uint64_t> sample_integers(size_t n) {
  std::vector<uint64_t> v(n);
  uint64_t s = 0x9e3779b97f4a7c15ull;
  for (size_t i = 0; i < n; ++i) {
    s = s * 6364136223846793005ull + 1442695040888963407ull;
    v[i] = (s >> 20) % kQ;
  }
  v[0] = kQ - 1;
  v[1] = 0;
  v[2] = 2;  // bits 0 and 1 are 0 and 1 (the wrong decomposition's case)
  return v;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_CROSSING_FIXTURE_H_
