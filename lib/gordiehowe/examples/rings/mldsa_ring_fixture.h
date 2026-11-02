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
#include <string_view>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mldsa/mldsa_openssl_testing.h"
#include "gordiehowe/examples/rings/mldsa_ring_testing.h"
#include "gordiehowe/threads_testing.h"
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

// The two arms of profile P at the parameter set S; KCONFIG names the
// bench config (mldsa-ring-native at ML-DSA-44, mldsa65-ring-native at
// ML-DSA-65).
template <class Profile, class Set = MLDSA44>
struct NativeArm {
  using P = Profile;
  using S = Set;
  using E = Env<P>;
  using T = MLDSARingNativeSystem<P, S>;
  using AF = typename E::AF;
  static constexpr const char *kName = "native";
  static inline const std::string kConfig =
      std::string(S::kConfigStem) + "-ring-native";
};
template <class Profile, class Set = MLDSA44>
struct CarrierArm {
  using P = Profile;
  using S = Set;
  using E = CarrierEnv<P>;
  using T = MLDSARingCarrierSystem<P, S>;
  using AF = typename E::AF;
  static constexpr const char *kName = "carrier";
  static inline const std::string kConfig =
      std::string(S::kConfigStem) + "-ring-carrier";
};

// An arm's system on a ring of R members (signer at R - 1), compiled once,
// on the arm's set's benchmark example by default.
template <class Arm>
struct Fixture {
  using S = typename Arm::S;
  using T = typename Arm::T;
  using Sys = typename T::Sys;
  using Value = typename Sys::Value;
  typename Arm::E env;
  RingCase<S> rc;
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(size_t R, const ml_dsa::MlDsa44SignatureExample &e =
                                 support::benchmark_example<S>())
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

// The ring setup with and without a runner (util/parallel.h: a pool of 8
// threads installed around prepare, as a multi-threaded prepare installs
// its own) on a ring of 100 members: the statement's cached public
// computations are the same values, fixed-seed proofs are the same bytes,
// and a proof made under one mode's prepare verifies under the other's;
// and single- and multi-threaded proofs cross-verify.
template <class Arm>
void setup_modes_agree() {
  using Fx = Fixture<Arm>;
  using Value = typename Fx::Value;
  Fx f(100);
  gordiehowe::internal::TaskPool pool(7);
  auto in_mode = [&pool](bool multi, auto fn) {
    parallel::Scope scope(multi ? &pool : nullptr);
    return fn();
  };
  auto values = [&](bool multi) {
    f.c->forget_setup();
    std::map<size_t, Value> out;
    in_mode(multi, [&] {
      f.c->prepare(f.statement(),
                   [&out](size_t id, Value &v) { out.emplace(id, v); });
      return 0;
    });
    return out;
  };
  const auto single = values(false);
  const auto multi = values(true);
  EXPECT_FALSE(single.empty()) << Arm::kName;
  EXPECT_TRUE(single == multi) << Arm::kName;
  // Fixed-seed proofs (the uncached mu limbs included) are the same bytes.
  std::vector<std::vector<uint8_t>> proofs;
  for (const bool prove_multi : {false, true}) {
    f.c->forget_setup();
    const auto proof = in_mode(prove_multi, [&] {
      auto prep = f.c->prepare(f.statement());
      typename Fx::Sys::ProveOptions opt;
      opt.fixed_seed = 7;
      opt.multithreaded = false;
      SecureRandomEngine rng;
      return prep.prove(f.witness(), rng, opt);
    });
    proofs.push_back(proof);
    f.c->forget_setup();
    EXPECT_TRUE(in_mode(!prove_multi, [&] {
      return f.c->prepare(f.statement()).verify(proof, nullptr, false);
    })) << Arm::kName << " proved with a runner: " << prove_multi;
  }
  EXPECT_TRUE(proofs[0] == proofs[1]) << Arm::kName;
  f.c->forget_setup();
  // Single- and multi-threaded proofs (the row digests on the pool among
  // them) verify in both modes.
  const auto prep = f.c->prepare(f.statement());
  gordiehowe::threads_testing::expect_threads_cross_verify(prep, f.witness());
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
  using S = typename Arm::S;
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
    RingSigner<S> s = f.rc.signer;
    s.index ^= 1;
    EXPECT_TRUE(f.rejects(none, f.t.witness(s))) << Arm::kName << " index";
  }
  // A key off the ring: the signer's slot holds a decoy, the prover keeps
  // its key.
  {
    auto ring = f.rc.ring;
    ring[f.rc.index] =
        make_ml_dsa_ring_decoy_public_key<typename S::Reference>(
            f.rc.members + 1, ::proofs::Shake256());
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
    RingSigner<S> s = f.rc.signer;
    s.sig.z[5] = (s.sig.z[5] + 1) % kQ;
    EXPECT_TRUE(f.rejects(none, f.t.witness(s))) << Arm::kName << " z";
  }
  // A wrong mu: the prover's mu off the selected member's (H follows A's
  // copy, so domain H's checks hold; membership does not).
  {
    RingSigner<S> s = f.rc.signer;
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
  // The carrier's relation quotient plus one (its first digit when the
  // range planner commits digits).
  if constexpr (std::string_view(Arm::kName) == "carrier") {
    using AV = std::vector<typename Arm::AF::Elt>;
    const auto &af = f.env.af;
    const bool digits = f.c->realization("signature.relation.q").k > 0;
    const size_t d = f.id(digits ? "range.signature.relation.q.d0"
                                 : "signature.relation.q");
    EXPECT_TRUE(f.rejects([&af, d](size_t at, Value &x) {
      if (at != d) return;
      auto &v = std::get<AV>(x).at(3);
      v = af.addf(v, af.one());
    })) << Arm::kName << " quotient";
  }
}


// The native arm's generated values on a ring of 64 members (R) equal the
// host witness's: c, w', w1, the UseHint advice and the z digits, and
// domain H's c~', mu and w1Encode.
template <class Arm>
void native_matches_host_witness(size_t R = 64) {
  Fixture<Arm> f(R);
  ASSERT_TRUE(f.rc.old.ok);
  using P = typename Arm::P;
  using AV = std::vector<typename Arm::AF::Elt>;
  std::map<size_t, typename Fixture<Arm>::Value> cap;
  ASSERT_TRUE(f.prove_verify(&cap));
  const auto &af = f.env.af;
  auto av = [&](const std::string &n) {
    return ints_of(af, std::get<AV>(cap.at(f.id(n))));
  };
  expect_hash_domain<P>(f, cap);
  const auto &old = f.rc.old;
  EXPECT_EQ(av("challenge.c"), old.c_bits());
  EXPECT_EQ(av("signature.w"), old.w());
  EXPECT_EQ(av("hint.w1"), old.w1_bits());
  const auto hint = old.hint();
  EXPECT_EQ(av("hint.nonpositive"), hint.nonpositive);
  EXPECT_EQ(av("hint.offset"), hint.offset);
  EXPECT_EQ(av("hint.slack"), hint.slack);
  // The z digits in the planner's table.
  const auto &rz = f.c->realization("norm.z");
  EXPECT_EQ(support::realized_digits(av, "norm.z", "d", rz.k),
            old.z_limbs(false, uint64_t(rz.table), rz.k));
  EXPECT_EQ(support::realized_digits(av, "norm.z", "h", rz.k),
            old.z_limbs(true, uint64_t(rz.table), rz.k));
}

// The carrier arm's generated values on a ring of R members equal the host
// witness's (ml_dsa_fp::advice and the relation's quotient), and so do
// the digits the planner commits for w', the quotient, the shifted z and
// its complement.
template <class Arm>
void carrier_matches_host_witness(size_t R = 64) {
  using S = typename Arm::S;
  using P = typename Arm::P;
  Fixture<Arm> f(R);
  ASSERT_TRUE(f.rc.old.ok);
  using AV = std::vector<typename Arm::AF::Elt>;
  std::map<size_t, typename Fixture<Arm>::Value> cap;
  ASSERT_TRUE(f.prove_verify(&cap));
  const auto &af = f.env.af;
  auto av = [&](const std::string &n) {
    return ints_of(af, std::get<AV>(cap.at(f.id(n))));
  };
  expect_hash_domain<P>(f, cap);
  const CarrierExisting<S> ce(f.rc.old, f.rc.signer.key);
  const auto &adv = ce.adv;
  EXPECT_EQ(av("challenge.c"), f.rc.old.c_bits());
  EXPECT_EQ(av("signature.w"), adv.wp);
  // The relation's committed quotient Q of w' - (A z - c 2^d t1) =
  // q (qlo + Q), qlo the lowering's: Q = wu - qlo for the host's wu.
  SignedInt qlo = 0;
  bool found = false;
  for (const auto &e : f.c->records().product_mod_equalities)
    if (e.name == "signature.relation") {
      qlo = e.qlo;
      found = true;
    }
  ASSERT_TRUE(found);
  ASSERT_TRUE(qlo < SignedInt(0));
  std::vector<uint64_t> quot;
  for (int64_t d : ce.wu) {
    const SignedInt x = SignedInt(d) - qlo;
    ASSERT_FALSE(x.negative());
    quot.push_back(uint64_t(x));
  }
  EXPECT_EQ(av("signature.relation.q"), quot);
  EXPECT_EQ(av("hint.w1"), f.rc.old.w1_bits());
  EXPECT_EQ(av("hint.nonpositive"), adv.sgn);
  EXPECT_EQ(av("hint.offset"), adv.vmag);
  EXPECT_EQ(av("hint.slack"), ce.slack());
  // Each value's base-T digits, for its realization's table T and digit
  // count.
  auto digits = [&](const std::string &n, size_t k) {
    std::vector<std::vector<uint64_t>> d;
    for (size_t l = 0; l < k; ++l) d.push_back(av(n + std::to_string(l)));
    std::vector<uint64_t> out;
    for (size_t i = 0; i < d[0].size(); ++i)
      for (size_t l = 0; l < k; ++l) out.push_back(d[l][i]);
    return out;
  };
  auto planned = [&](const std::string &req, const std::string &stem,
                     const std::vector<uint64_t> &x) {
    const RangeRealization &r = f.c->realization(req);
    EXPECT_EQ(digits(stem, r.k), limbs(x, uint64_t(r.table), r.k)) << req;
  };
  planned("signature.w", "range.signature.w.d", adv.wp);
  planned("signature.relation.q", "range.signature.relation.q.d", quot);
  std::vector<uint64_t> zc;
  for (uint64_t v : adv.zsh) zc.push_back(2 * S::kBound - 2 - v);
  planned("norm.z", "range.norm.z.d", adv.zsh);
  planned("norm.z", "range.norm.z.h", zc);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_FIXTURE_H_
