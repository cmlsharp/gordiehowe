// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA native tests (mldsa_native_test*.cc, one binary): the compiled
// fixture they share. Each test file has its own copy (anonymous
// namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_FIXTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_FIXTURE_H_

#include "gordiehowe/examples/mldsa/mldsa_native.h"

#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_openssl_testing.h"
#include "gordiehowe/examples/shared/private_message_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {


using support::DomainSize;
using support::Existing;
using support::bytes_of;
using support::domain_size;
using support::export_plan;
using support::ints_of;
using support::node_id;

// The system at the parameter set S on one example (the set's benchmark
// example by default, benchmark_example), at its message and context
// lengths, compiled once; PACKING is the packing ablation (mldsa_native.h).
template <class P, class S = MLDSA44>
struct Fixture {
  using T = MLDSANativeSystem<P, S>;
  using Sys = typename T::Sys;
  using Value = typename Sys::Value;
  Env<P> env;
  const ml_dsa::MlDsa44SignatureExample &ex;
  Existing<S> old{ex};
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(const ml_dsa::MlDsa44SignatureExample &e =
                       support::benchmark_example<S>(),
                   PackingAblation packing = PackingAblation::kNone)
      : ex(e), t(env, e.msg.size(), e.ctx.size(), packing) {
    c = t.compile();
  }
  typename T::Assignment statement() const {
    return t.statement(ex.pkey, ex.ctx);
  }
  typename T::Assignment witness() const {
    return t.witness(ex.msg, old.signature());
  }
  size_t id(const std::string &name) const { return node_id(t.cs, name); }
  // An honest proof, with every generated value recorded.
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

// Honest proofs at profile P and the parameter set S; mu, c~, c, w', w1,
// the UseHint advice and the z digits equal the host witness's values.
template <class P, class S>
void prove_verify_matches_host_witness() {
  Fixture<P, S> f;
  ASSERT_TRUE(f.old.ok);
  using HV = std::vector<typename P::HashField::Elt>;
  using AV = std::vector<typename P::MLDSANativeField::Elt>;
  std::map<size_t, typename Fixture<P, S>::Value> cap;
  ASSERT_TRUE(f.prove_verify(&cap));
  const auto &hf = f.env.hf;
  const auto &af = f.env.af;
  auto hv = [&](const std::string &n) { return std::get<HV>(cap.at(f.id(n))); };
  auto av = [&](const std::string &n) {
    return ints_of(af, std::get<AV>(cap.at(f.id(n))));
  };
  const auto &wg = *f.old.wg;
  // mu, c~' (= c~), w1Encode in H.
  EXPECT_EQ(bytes_of(hf, hv("h2c.mu.out")),
            std::vector<uint8_t>(wg.mu_.begin(), wg.mu_.end()));
  EXPECT_EQ(bytes_of(hf, hv("h2c.c_tilde.out")),
            std::vector<uint8_t>(wg.c_tilde_.begin(), wg.c_tilde_.end()));
  EXPECT_EQ(bytes_of(hf, hv("w1")),
            std::vector<uint8_t>(wg.w1_tilde_.begin(), wg.w1_tilde_.end()));
  // c, w', w1 and the UseHint advice in A.
  EXPECT_EQ(av("challenge.c"), f.old.c_bits());
  EXPECT_EQ(av("signature.w"), f.old.w());
  EXPECT_EQ(av("hint.w1"), f.old.w1_bits());
  const auto hint = f.old.hint();
  EXPECT_EQ(av("hint.nonpositive"), hint.nonpositive);
  EXPECT_EQ(av("hint.offset"), hint.offset);
  EXPECT_EQ(av("hint.slack"), hint.slack);
  // The z digits: the shifted coefficient and its complement, in the
  // planner's table.
  const auto &rz = f.c->realization("norm.z");
  EXPECT_EQ(support::realized_digits(av, "norm.z", "d", rz.k),
            f.old.z_limbs(false, uint64_t(rz.table), rz.k));
  EXPECT_EQ(support::realized_digits(av, "norm.z", "h", rz.k),
            f.old.z_limbs(true, uint64_t(rz.table), rz.k));
}

// A cheating prover at profile P and the parameter set S, gadget by gadget:
// each case changes one value (a generated one after its generator ran, or
// an input) and the proof fails.
template <class P, class S>
void tamper_rejected() {
  using Fx = Fixture<P, S>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename P::HashField::Elt>;
  using AV = std::vector<typename P::MLDSANativeField::Elt>;
  constexpr size_t kR1Bits = S::kR1Bits;
  Fx f;
  const auto &af = f.env.af;
  const auto &hf = f.env.hf;
  // Adds D to coordinate I of the A value NAME.
  auto add_a = [&](const std::string &name, size_t i, int64_t d) {
    const size_t id = f.id(name);
    return [&af, id, i, d](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<AV>(x).at(i);
      v = d >= 0 ? af.addf(v, af.of_scalar(uint64_t(d)))
                 : af.subf(v, af.of_scalar(uint64_t(-d)));
    };
  };
  // Flips bit I of the H value NAME.
  auto flip_h = [&](const std::string &name, size_t i) {
    const size_t id = f.id(name);
    return [&hf, id, i](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<HV>(x).at(i);
      v = hf.addf(v, hf.one());
    };
  };
  auto both = [](auto a, auto b) {
    return [a, b](size_t at, Value &x) {
      a(at, x);
      b(at, x);
    };
  };
  auto none = [](size_t, Value &) {};

  // Key: a verifier holding another rho (same t1) rejects the proof.
  {
    auto prep = f.c->prepare(f.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(f.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    auto pk = f.ex.pkey;
    pk[0] ^= 1;
    EXPECT_FALSE(f.c->prepare(f.t.statement(pk, f.ex.ctx)).verify(proof));
  }
  // Challenge (A): a coefficient's sign bit off H's SampleInBall.
  EXPECT_TRUE(f.rejects(add_a("challenge.c", 1, 1)));
  // Signature relation: z moved by one with w' stale (its digits follow z,
  // so the norm holds).
  {
    auto sig = f.old.signature();
    sig.z[5] = (sig.z[5] + 1) % kQ;
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  // Norm: the digits of z + (bound - 1) with a low digit out of the table
  // (the value unchanged).
  const int64_t Tz = int64_t(f.c->realization("norm.z").table);
  EXPECT_TRUE(f.rejects(both(add_a("range.norm.z.d0", 3, Tz),
                             add_a("range.norm.z.d1", 3, -1))));
  // Norm: a coefficient at the bound, every value from the honest
  // generators (its complement leaves the table).
  {
    auto sig = f.old.signature();
    sig.z[7] = S::kBound;
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  // UseHint: the offset moved with the slack (the interval row holds, the
  // Decompose row does not), and the sign bit flipped.
  EXPECT_TRUE(f.rejects(both(add_a("hint.offset", 9, 1),
                             add_a("hint.slack", 9, -1))));
  EXPECT_TRUE(f.rejects(add_a("hint.nonpositive", 9, 1)));
  // UseHint: w1 = M (bits 001101 at M = 44) at a coefficient whose output
  // is 0 or 1 moves raw_high by M; the comparator refuses it. At M = 16
  // every 4-bit value is below M, so the case does not arise.
  if constexpr (S::kM < (uint64_t(1) << kR1Bits)) {
    const auto bits = f.old.w1_bits();
    size_t at = 0;
    auto high = [&](size_t i) {
      for (size_t b = 1; b < kR1Bits; ++b)
        if (bits[i * kR1Bits + b]) return true;
      return false;
    };
    while (high(at)) ++at;
    const size_t id = f.id("hint.w1");
    EXPECT_TRUE(f.rejects([&af, id, at](size_t i, Value &x) {
      if (i != id) return;
      auto &v = std::get<AV>(x);
      for (size_t b = 1; b < kR1Bits; ++b)
        if ((S::kM >> b) & 1) v[at * kR1Bits + b] = af.one();
    }));
  }
  // Hint weight: omega + 1 ones (the honest generators follow h).
  {
    auto sig = f.old.signature();
    size_t ones = 0;
    for (auto b : sig.h) ones += b;
    for (size_t i = 0; ones <= S::kOmega; ++i)
      if (!sig.h[i]) {
        sig.h[i] = 1;
        ++ones;
      }
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  // Crossing: H's copy of w1 off A's.
  EXPECT_TRUE(f.rejects(flip_h("w1", 100)));
  // Domain H: another message, a Keccak state word, the stream's
  // SampleInBall cells.
  {
    auto msg = f.ex.msg;
    msg[0] ^= 1;
    EXPECT_TRUE(f.rejects(none, f.t.witness(msg, f.old.signature())));
  }
  EXPECT_TRUE(f.rejects(flip_h("h2c.mu.blocks.r20.value.words", 0)));
  EXPECT_TRUE(f.rejects(flip_h("h2c.sample.select.j", 3)));
  EXPECT_TRUE(f.rejects(flip_h("h2c.sample.mem.c_enc", 17)));
  // Statement: another context (an example with one: a 10-byte message
  // under a 16-byte context).
  {
    const auto example = support::context_example<S>();
    Fx g(example);
    ASSERT_FALSE(g.ex.ctx.empty());
    auto prep = g.c->prepare(g.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(g.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    auto ctx = g.ex.ctx;
    ctx[0] ^= 1;
    EXPECT_FALSE(g.c->prepare(g.t.statement(g.ex.pkey, ctx)).verify(proof));
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_FIXTURE_H_
