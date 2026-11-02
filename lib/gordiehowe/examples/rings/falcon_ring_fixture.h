// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon ring tests (falcon_ring_test*.cc, one binary): the timing
// helpers and the compiled fixture they share. Each test file has its own
// copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_FIXTURE_H_

#include "bench/timing.h"
#include "gordiehowe/examples/rings/falcon_ring.h"
#include "gordiehowe/examples/instances.h"


#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <optional>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/rings/falcon_ring_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

using bench::Clock;
using bench::ms_since;
using bench::median;

// The system T on instance IN, compiled once.
template <class T, class I>
struct Fixture {
  using Sys = typename T::Sys;
  using Value = typename Sys::Value;
  using AF = typename T::AF;
  using AV = std::vector<typename AF::Elt>;
  typename T::Env env;
  I in;
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(I instance) : in(std::move(instance)), t(env, in.R) {
    c = t.compile();
  }
  typename T::Assignment statement() const {
    return t.statement(in.ring, in.c);
  }
  typename T::Assignment witness() const {
    return t.witness(in.signer, in.h, in.s2);
  }
  size_t id(const std::string &name) const {
    const auto &N = t.cs.graph().nodes;
    for (size_t i = 0; i < N.size(); ++i)
      if (N[i].name == name) return i;
    throw std::runtime_error("no node " + name);
  }
  // An honest proof, every generated value recorded in CAP.
  bool prove_verify(std::map<size_t, Value> *cap = nullptr) const {
    auto prep = c->prepare(statement());
    typename Sys::ProveOptions opt;
    if (cap) opt.tamper = [cap](size_t i, Value &v) { (*cap)[i] = v; };
    SecureRandomEngine rng;
    return prep.verify(prep.prove(witness(), rng, opt));
  }
  // Whether a cheating prover's proof fails: TAMPER changes generated
  // values, W the private inputs, ST the statement the proof is verified
  // against.
  bool rejects(std::function<void(size_t, Value &)> tamper,
               std::optional<typename T::Assignment> w = std::nullopt,
               std::optional<typename T::Assignment> st = std::nullopt) const {
    auto prep = c->prepare(statement());
    typename Sys::ProveOptions opt;
    opt.tamper = std::move(tamper);
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    try {
      const auto proof = prep.prove(w ? *w : witness(), rng, opt);
      if (st) return !c->prepare(*st).verify(proof);
      return !prep.verify(proof);
    } catch (const std::runtime_error &) {
      return true;
    } catch (const std::exception &e) {
      ADD_FAILURE() << "the cheating prover failed: " << e.what();
      return false;
    }
  }
  std::vector<uint64_t> ints(const std::map<size_t, Value> &cap,
                             const std::string &name) const {
    const auto &v = std::get<AV>(cap.at(id(name)));
    std::vector<uint64_t> out;
    for (const auto &x : v) out.push_back(uint64_t(nat_of(env.af, x)));
    return out;
  }
};

template <class P, class S = Falcon512>
using CarrierFixture = Fixture<FalconRingCarrierSystem<P, S>, CarrierInstance>;
template <class P, class S = Falcon512>
using NativeFixture = Fixture<FalconRingNativeSystem<P, S>, NativeInstance>;

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_FIXTURE_H_
