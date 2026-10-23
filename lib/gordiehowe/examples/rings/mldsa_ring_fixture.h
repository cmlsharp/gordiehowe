// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA private ring tests (mldsa_ring_test*.cc, one binary): the two
// arms, the compiled fixture, the checks both arms' suites run, and the
// timing support. Each test file has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_FIXTURE_H_

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/rings/mldsa_ring_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

using support::CarrierExisting;
using support::DomainSize;
using support::Existing;
using support::RingCase;
using support::bytes_of;
using support::domain_size;
using support::export_plan;
using support::ints_of;
using support::limbs;
using support::node_id;

// The two arms of profile P.
template <class P>
struct NativeArm {
  using E = Env<P>;
  using T = MLDSARingNativeSystem<P>;
  using AF = typename E::AF;
  static constexpr const char *kName = "native";
  static constexpr const char *kConfig = "mldsa-ring-native";
};
template <class P>
struct CarrierArm {
  using E = CarrierEnv<P>;
  using T = MLDSARingCarrierSystem<P>;
  using AF = typename E::AF;
  static constexpr const char *kName = "carrier";
  static constexpr const char *kConfig = "mldsa-ring-carrier";
};

// An arm's system on a ring of R members (signer at R - 1), compiled once.
template <class Arm>
struct Fixture {
  using T = typename Arm::T;
  using Sys = typename T::Sys;
  using Value = typename Sys::Value;
  typename Arm::E env;
  RingCase rc;
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(size_t R, const ml_dsa::MlDsa44SignatureExample &e =
                                 ml_dsa::GetMlDsa44BenchmarkExample())
      : rc(e, R, R - 1), t(env, R, e.msg.size(), e.ctx.size()) {
    c = t.compile();
  }
  typename T::Assignment statement() const {
    return t.statement(rc.ring, rc.ex.msg, rc.ex.ctx);
  }
  typename T::Assignment witness() const { return t.witness(rc.signer); }
  size_t id(const std::string &name) const { return node_id(t.cs, name); }
  bool prove_verify(std::map<size_t, Value> *cap = nullptr) const {
    auto prep = c->prepare(statement());
    typename Sys::ProveOptions opt;
    if (cap) opt.tamper = [cap](size_t i, Value &v) { (*cap)[i] = v; };
    SecureRandomEngine rng;
    return prep.verify(prep.prove(witness(), rng, opt));
  }
  // Whether a cheating prover's proof fails: TAMPER changes generated
  // values, W the assignment.
  bool rejects(std::function<void(size_t, Value &)> tamper,
               std::optional<typename T::Assignment> w = std::nullopt) const {
    auto prep = c->prepare(statement());
    typename Sys::ProveOptions opt;
    opt.tamper = std::move(tamper);
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    try {
      return !prep.verify(prep.prove(w ? *w : witness(), rng, opt));
    } catch (const std::runtime_error &) {
      return true;
    } catch (const std::exception &e) {
      ADD_FAILURE() << "the cheating prover failed: " << e.what();
      return false;
    }
  }
};
template <class Arm>
void proves_at(size_t R) {
  Fixture<Arm> f(R);
  EXPECT_TRUE(f.prove_verify()) << Arm::kName << " R=" << R;
}

// Domain H's values, both arms: c~', H's mu and w1Encode.
template <class P, class Fx, class Cap>
void expect_hash_domain(const Fx &f, const Cap &cap) {
  using HV = std::vector<typename P::HashField::Elt>;
  const auto &hf = f.env.hf;
  auto hv = [&](const std::string &n) { return std::get<HV>(cap.at(f.id(n))); };
  const auto &wg = *f.rc.old.wg;
  EXPECT_EQ(bytes_of(hf, hv("h2c.c_tilde.out")),
            std::vector<uint8_t>(wg.c_tilde_.begin(), wg.c_tilde_.end()));
  EXPECT_EQ(bytes_of(hf, hv("mu")),
            std::vector<uint8_t>(wg.mu_.begin(), wg.mu_.end()));
  EXPECT_EQ(bytes_of(hf, hv("w1")),
            std::vector<uint8_t>(wg.w1_tilde_.begin(), wg.w1_tilde_.end()));
}

// A cheating prover: each case changes one value and the proof fails.
template <class Arm>
void tamper_rejected() {
  using Fx = Fixture<Arm>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename Arm::E::HF::Elt>;
  Fx f(16);
  const auto &hf = f.env.hf;
  auto flip_h = [&](const std::string &name, size_t i) {
    const size_t id = f.id(name);
    return [&hf, id, i](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<HV>(x).at(i);
      v = hf.addf(v, hf.one());
    };
  };
  auto none = [](size_t, Value &) {};
  // Honest.
  EXPECT_TRUE(f.prove_verify()) << Arm::kName;
  // A wrong index: the record is the signer's, the index another member's.
  {
    RingSigner s = f.rc.signer;
    s.index ^= 1;
    EXPECT_TRUE(f.rejects(none, f.t.witness(s))) << Arm::kName << " index";
  }
  // A key off the ring: the signer's slot holds a decoy, the prover keeps
  // its key.
  {
    auto ring = f.rc.ring;
    ring[f.rc.index] =
        make_ml_dsa_ring_decoy_public_key<Params>(f.rc.members + 1, ::proofs::Shake256());
    auto prep = f.c->prepare(f.t.statement(ring, f.rc.ex.msg, f.rc.ex.ctx));
    typename Fx::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    bool rejected = true;
    try {
      rejected = !prep.verify(prep.prove(f.witness(), rng, opt));
    } catch (const std::runtime_error &) {
    }
    EXPECT_TRUE(rejected) << Arm::kName << " key off the ring";
  }
  // A bad signature: z moved by one.
  {
    RingSigner s = f.rc.signer;
    s.sig.z[5] = (s.sig.z[5] + 1) % kQ;
    EXPECT_TRUE(f.rejects(none, f.t.witness(s))) << Arm::kName << " z";
  }
  // A wrong mu: the prover's mu off the selected member's (H follows A's
  // copy, so domain H's checks hold; membership does not).
  {
    RingSigner s = f.rc.signer;
    s.mu[3] ^= 4;
    EXPECT_TRUE(f.rejects(none, f.t.witness(s))) << Arm::kName << " mu";
  }
  // A wrong mu: the verifier's message differs from the prover's.
  {
    auto prep = f.c->prepare(f.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(f.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    auto msg = f.rc.ex.msg;
    msg[0] ^= 1;
    EXPECT_FALSE(
        f.c->prepare(f.t.statement(f.rc.ring, msg, f.rc.ex.ctx)).verify(proof))
        << Arm::kName << " message";
  }
  // A broken MAC: H's copy of mu, of w1, off A's.
  EXPECT_TRUE(f.rejects(flip_h("mu", 7))) << Arm::kName << " MAC mu";
  EXPECT_TRUE(f.rejects(flip_h("w1", 100))) << Arm::kName << " MAC w1";
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_FIXTURE_H_
