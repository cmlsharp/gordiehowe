// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// R = [k] P on P-256 in the F_p256 domain (p256_scalar_mult.h), with the
// point relations where the placement rule puts them and forced to field
// batches (CompileOptions::placement_force).
//
//   P256ScalarMult.Digits            the recoding reconstructs k mod n
//   P256ScalarMult.Proves/<points>   honest proofs verify for random and
//                                    edge scalars; a tampered doubling,
//                                    addition, entry or statement is
//                                    rejected
//   P256ScalarMult.DISABLED_Compare  commit, prove, verify and proof bytes
//                                    of each variant, medians of
//                                    GH_P256_REPS (default 5)

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <random>
#include <string>
#include <tuple>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/examples/p256/p256_scalar_mult.h"
#include "gordiehowe/examples/p256/p256_testing.h"
#include "gordiehowe/relation.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using namespace examples::mdoc::p256_testing;  // NOLINT
// Where the point relations go: the placement rule's choice, or field
// batches.
enum class Points { kPlaced, kBatch };
// The compile options of POINTS: the point relations forced to field
// batches (CompileOptions::placement_force) or left to the rule.
CompileOptions points_options(Points points) {
  CompileOptions o;
  if (points == Points::kBatch) o.placement_force = "A/point.*=batch";
  return o;
}
using Limbs = std::array<uint64_t, 4>;

// A random scalar in [1, n).
Limbs random_scalar(std::mt19937_64 &g) {
  for (;;) {
    Limbs k = {g(), g(), g(), g()};
    const Fp256Nat kn(k);
    if (kn < n256_order && kn != Fp256Nat(0)) return k;
  }
}
std::vector<uint8_t> bytes_of(const Limbs &k) {
  std::vector<uint8_t> b(32);
  for (size_t i = 0; i < 32; ++i) b[i] = uint8_t(k[i / 8] >> (8 * (i % 8)));
  return b;
}
Limbs order_minus(uint64_t d) {
  Limbs k = examples::mdoc::p256_sm::kOrder;
  k[0] -= d;  // the low limb of n exceeds every d used here
  return k;
}
// Scalars whose last addition is exceptional: the chain's partial sum 16 kappa
// before the last digit delta has 16 kappa = delta mod n, so A = T. For k = 2
// the recoded k - n has 16 kappa = 1 - n and delta = 1 (A = T = P); for
// k = n - 2, A = T = -P. Every other addition and doubling of the chain is
// exception-free.
std::vector<Limbs> exceptional_scalars() {
  return {{2, 0, 0, 0}, order_minus(2)};
}
// Ordinary edge scalars and random ones.
std::vector<Limbs> ordinary_scalars(std::mt19937_64 &g, size_t random) {
  std::vector<Limbs> ks = {{1, 0, 0, 0}, {3, 0, 0, 0}, {4, 0, 0, 0},
                           order_minus(1), order_minus(3),
                           {~0ull, ~0ull, ~0ull, 0}};
  for (size_t i = 0; i < random; ++i) ks.push_back(random_scalar(g));
  return ks;
}


// sum_j (2 t_j - 15) 16^j = k (mod n), every t_j in [0, 16).
TEST(P256ScalarMult, Digits) {
  std::mt19937_64 g(5);
  std::vector<Limbs> ks = ordinary_scalars(g, 200);
  for (const auto &k : exceptional_scalars()) ks.push_back(k);
  const auto &fn = p256_scalar;
  for (const auto &k : ks) {
    const auto t = examples::mdoc::p256_sm::host::signed_digits(k);
    auto acc = fn.zero();
    const auto sixteen = fn.of_scalar(16);
    for (size_t j = examples::mdoc::p256_sm::kWindows; j-- > 0;) {
      ASSERT_LT(t[j], 16u);
      acc = fn.mulf(acc, sixteen);
      fn.add(acc, fn.subf(fn.of_scalar(2 * t[j]), fn.of_scalar(15)));
    }
    EXPECT_EQ(fn.from_montgomery(acc), Fp256Nat(k));
  }
}

// A base point: [s] G for a random s.
P256::ECPoint base_point(std::mt19937_64 &g) {
  P256::ECPoint b = p256.scalar_multf(p256.generator(),
                                      Fp256Nat(random_scalar(g)));
  p256.normalize(b);
  return b;
}

// The host chain against the curve's scalar multiplication; on the
// exceptional scalars its inverse of 0 is 0, and the chain leaves the group
// law.
TEST(P256ScalarMult, HostMatchesReference) {
  std::mt19937_64 g(9);
  const P256::ECPoint base = base_point(g);
  namespace host = examples::mdoc::p256_sm::host;
  auto matches = [&](const Limbs &k) {
    P256::ECPoint r = p256.scalar_multf(base, Fp256Nat(k));
    p256.normalize(r);
    const host::Point h = host::scalar_mult(
        {host::of(base.x), host::of(base.y)}, k);
    return host::to(h.x) == r.x && host::to(h.y) == r.y;
  };
  for (const auto &k : ordinary_scalars(g, 40)) EXPECT_TRUE(matches(k)) << k[0];
  for (const auto &k : exceptional_scalars()) EXPECT_FALSE(matches(k)) << k[0];
}

// The relation for a base point and a scalar; SM is what it declares.
using examples::mdoc::p256_sm::ScalarMultStatement;
using examples::mdoc::p256_sm::ScalarMultWitness;
struct SmSystem {
  examples::mdoc::p256_sm::ScalarMult sm;
  Relation<ScalarMultStatement<Value>, ScalarMultWitness<Value>> rel;
  Sys &cs;
  explicit SmSystem(const Profile &p)
      : rel(compile<ScalarMultStatement, ScalarMultWitness>(
            CompileProfile{},
            [this, &p](Sys &cs, ScalarMultStatement<In> st,
                       ScalarMultWitness<In> w) {
              auto &A = cs.domain(p, "A");
              sm = examples::mdoc::p256_sm::scalar_mult(cs, A, st, w);
            },
            "gh-p256-scalar-mult")),
        cs(rel.typed<Sys>().system()) {}
  Assignment statement(const P256::ECPoint &r) const {
    return rel.typed<Sys>().statement(ScalarMultStatement<Value>{{r.x, r.y}});
  }
};
struct Instance {
  Assignment statement, witness;
};
Instance instance(const SmSystem &h, const Limbs &k,
                  const P256::ECPoint &base) {
  P256::ECPoint r = p256.scalar_multf(base, Fp256Nat(k));
  p256.normalize(r);
  ScalarMultWitness<Value> w{};
  w.p = {base.x, base.y};
  const std::vector<uint8_t> kb = bytes_of(k);
  std::copy(kb.begin(), kb.end(), w.k.begin());
  Instance in;
  in.statement = h.statement(r);
  in.witness = h.rel.typed<Sys>().witness(w);
  return in;
}

class Proves : public ::testing::TestWithParam<Points> {};

TEST_P(Proves, HonestAndTampered) {
  const F &f = fp();
  auto h = std::make_unique<SmSystem>(profile());
  auto c = compile(h->cs, CompileProfile{}, points_options(GetParam()));
  const examples::mdoc::p256_sm::ScalarMult &sm = h->sm;
  std::mt19937_64 g(17);
  const P256::ECPoint base = base_point(g);
  SecureRandomEngine rng;
  const std::vector<Limbs> ks = ordinary_scalars(g, 2);
  for (const auto &k : ks) {
    const Instance in = instance(*h, k, base);
    auto prep = c->prepare(in.statement);
    EXPECT_TRUE(prep.verify(prep.prove(in.witness, rng))) << k[0];
  }
  // An exceptional scalar: no accepted proof (the circuit's honest-prover
  // check refuses it; the batch's proof is rejected).
  for (const auto &k : exceptional_scalars()) {
    const Instance in = instance(*h, k, base);
    auto prep = c->prepare(in.statement);
    ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_FALSE(prep.verify(prep.prove(in.witness, rng, opt))) << k[0];
  }
  // Tampering, at a random scalar: a doubling's x3, an addition's lam, a
  // committed entry, and a wrong statement. Each generator's output is
  // changed after it runs; the later generators read the changed value.
  const Instance in = instance(*h, ks.back(), base);
  auto prep = c->prepare(in.statement);
  // (node, coordinate): doubling 37's x3, addition 20's lam, and entry
  // coordinate 9.
  const std::vector<std::pair<std::string, std::pair<size_t, size_t>>> cases =
      {{"double.x3", {sm.chain.doublings.id, 3 * 37 + 1}},
       {"add.lam", {sm.chain.additions.id, 4 * 20 + 1}},
       {"entry", {sm.entries.id, 9}}};
  for (const auto &[what, at] : cases) {
    ProveOptions opt;
    opt.require_satisfied = false;
    opt.tamper = [&, at = at](size_t id, Sys::Value &v) {
      if (id == at.first) f.add(std::get<Vec>(v).at(at.second), f.one());
    };
    EXPECT_FALSE(prep.verify(prep.prove(in.witness, rng, opt))) << what;
  }
  const P256::ECPoint other = base_point(g);
  auto bad = c->prepare(h->statement(other));
  ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(bad.verify(bad.prove(in.witness, rng, opt)));
}
INSTANTIATE_TEST_SUITE_P(P256ScalarMult, Proves,
                         ::testing::Values(Points::kPlaced, Points::kBatch),
                         [](const auto &info) {
                           return info.param == Points::kPlaced ? "Placed"
                                                                : "Batch";
                         });

// ------------------------------------------------------------- benches --

void compare(Points points) {
  const char *what = points == Points::kPlaced ? "a_placed" : "b_batch";
  auto [h, c] = compile_at_list_radius(
      [](const Profile &p) { return std::make_unique<SmSystem>(p); },
      points_options(points));
  std::mt19937_64 g(23);
  const P256::ECPoint base = base_point(g);
  const Instance in = instance(*h, random_scalar(g), base);
  report("P256_SM", what, 0, *c, measure(*c, in.statement, in.witness));
  const std::string r = c->report();
  for (size_t at = r.find("field skip:"); at != std::string::npos;
       at = r.find("field skip:", at + 1))
    std::printf("P256_SM %s %s\n", what,
                r.substr(at, r.find('\n', at) - at).c_str());
  std::fflush(stdout);
}
// GH_P256_ARITH selects a, b (default both).
TEST(P256ScalarMult, DISABLED_Compare) {
  const char *e = std::getenv("GH_P256_ARITH");
  const std::string which = e != nullptr ? e : "a,b";
  if (which.find('a') != std::string::npos) compare(Points::kPlaced);
  if (which.find('b') != std::string::npos) compare(Points::kBatch);
}

}  // namespace
}  // namespace proofs::gordiehowe
