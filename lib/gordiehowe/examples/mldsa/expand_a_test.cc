// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ML-DSA-44's ExpandA from a private seed (expand_a.h), in both
// profiles.
//
//   MatchesReference   honest proofs on the seeds of the ML-DSA-44 test
//                      vectors' keys; A's crossed coefficients and H's
//                      selections equal the host's bounded ExpandA
//                      (host::expand_a)
//   BudgetFailure      the honest prover's budget failure, 336 candidates
//                      (6 SHAKE128 blocks, FIPS 204 Appendix C's 894
//                      bytes), and the batch's 96 permutations
//   TamperRejected     a seed bit under the honest Keccak trace, an A_hat
//                      coefficient (A's crossed bits), a selected
//                      coefficient copied to both sides, two swapped
//                      outputs of a selection and a skipped accepted
//                      sample are each rejected
//   HostBounded        the host's bounded ExpandA (ml_dsa::ExpandABounded,
//                      6 blocks, the verifier's) equals the unbounded
//                      reference on the test keys and the ExpandA KAT;
//                      a call with fewer than 256 acceptances among its
//                      candidates fails, and the host refuses the key
//
// expand_a_bench (expand_a_bench.cc) measures the cost split.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/examples/mldsa/expand_a_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

using namespace expand_a_params;  // NOLINT(build/namespaces)

template <class Sys>
size_t node_id(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  throw std::runtime_error("no node named '" + name + "'");
}

// The full system of profile P, compiled once.
template <class P>
struct Fixture {
  using T = ExpandASystem<P>;
  using Sys = typename T::Sys;
  using Value = typename Sys::Value;
  using HV = std::vector<typename P::HashField::Elt>;
  using AV = std::vector<typename P::MLDSANativeField::Elt>;
  Env<P> env;
  T t{env, ExpandAConfig{}};
  std::shared_ptr<const typename T::Compiled> c = t.compile();

  size_t id(const std::string &name) const { return node_id(t.cs, name); }
  // An honest proof on SEED, with every generated value recorded.
  bool prove_verify(const std::vector<uint8_t> &seed,
                    std::map<size_t, Value> *cap = nullptr) const {
    auto prep = c->prepare(t.statement());
    typename Sys::ProveOptions opt;
    if (cap) opt.tamper = [cap](size_t i, Value &v) { (*cap)[i] = v; };
    SecureRandomEngine rng;
    return prep.verify(prep.prove(t.witness(seed), rng, opt));
  }
  // Whether a cheating prover's proof on SEED fails: TAMPER changes
  // generated values.
  bool rejects(const std::vector<uint8_t> &seed,
               std::function<void(size_t, Value &)> tamper) const {
    auto prep = c->prepare(t.statement());
    typename Sys::ProveOptions opt;
    opt.tamper = std::move(tamper);
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    try {
      return !prep.verify(prep.prove(t.witness(seed), rng, opt));
    } catch (const std::runtime_error &) {
      return true;
    } catch (const std::exception &e) {
      ADD_FAILURE() << "the cheating prover failed: " << e.what();
      return false;
    }
  }
};

// The integers of Bit values, W bits each, least significant first.
template <class F>
std::vector<uint64_t> words_of(const F &f, const std::vector<typename F::Elt> &b,
                               size_t w) {
  std::vector<uint64_t> out(b.size() / w, 0);
  for (size_t i = 0; i < b.size(); ++i)
    out[i / w] |= uint64_t(ct::bit_of(f, b[i])) << (i % w);
  return out;
}

template <class P>
class ExpandATest : public ::testing::Test {};
TYPED_TEST_SUITE(ExpandATest, param_sets::Profiles, param_sets::ProfileName);

TYPED_TEST(ExpandATest, MatchesReference) {
  using Fx = Fixture<TypeParam>;
  Fx f;
  std::vector<std::vector<uint8_t>> keys = {
      ml_dsa::GetMlDsa44BenchmarkExample().pkey};
  const auto ex = ml_dsa::GetMlDsa44Examples();
  for (size_t i = 0; i < ex.size() && keys.size() < 4; ++i)
    keys.push_back(ex[i].pkey);
  ASSERT_GE(keys.size(), 3u);
  for (const auto &pk : keys) {
    std::map<size_t, typename Fx::Value> cap;
    ASSERT_TRUE(f.prove_verify(seed_of(pk), &cap));
    const std::vector<uint64_t> want = host::expand_a(pk);
    const auto a = words_of(
        f.env.af, std::get<typename Fx::AV>(cap.at(f.id("crossing.bits"))),
        kCoeffBits);
    EXPECT_EQ(a, want);
    // H's selections, r major.
    for (size_t e = 0; e < kRows * kCols; ++e) {
      const auto h = words_of(
          f.env.hf,
          std::get<typename Fx::HV>(cap.at(
              f.id("expand_a.select." + std::to_string(e) + ".raw"))),
          kCoeffBits);
      EXPECT_TRUE(std::equal(h.begin(), h.end(), want.begin() + long(e * kDegree)))
          << "entry " << e;
    }
  }
}

TYPED_TEST(ExpandATest, BudgetFailure) {
  Fixture<TypeParam> f;
  const double b = f.t.ea.log2_budget_failure;
  std::printf("GH_EXPANDA_BUDGET profile=%s candidates=%zu "
              "log2_per_call=%.2f log2_union=%.2f\n",
              TypeParam::kId, kSamples, f.t.ea.selections[0].log2_budget_failure,
              b);
  // Pr[Bin(336, q / 2^23) < 256], exact: 2^-546.94; the union over 16
  // calls adds log2 16.
  EXPECT_NEAR(f.t.ea.selections[0].log2_budget_failure, -546.94, 0.01);
  EXPECT_NEAR(b, -542.94, 0.01);
  // 6 permutations per call: the absorb's gives the first block.
  EXPECT_EQ(f.t.ea.permutations, size_t{96});
}

TYPED_TEST(ExpandATest, TamperRejected) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = typename Fx::HV;
  using AV = typename Fx::AV;
  Fx f;
  const auto &hf = f.env.hf;
  const auto &af = f.env.af;
  const auto seed = seed_of(ml_dsa::GetMlDsa44BenchmarkExample().pkey);
  std::map<size_t, Value> honest;
  ASSERT_TRUE(f.prove_verify(seed, &honest));

  // A seed bit flipped, every generated value the honest seed's (the Keccak
  // trace absorbs the other rho).
  {
    auto bad = seed;
    bad[3] ^= 0x10;
    EXPECT_TRUE(f.rejects(bad, [&honest](size_t at, Value &x) {
      x = honest.at(at);
    }));
  }
  // An A_hat coefficient in A: one crossed bit flipped.
  {
    const size_t id = f.id("crossing.bits");
    EXPECT_TRUE(f.rejects(seed, [&af, id](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<AV>(x).at(5 * kCoeffBits + 2);
      v = af.subf(af.one(), v);
    }));
  }
  // A selected coefficient changed in H, so that A copies it (the crossing
  // holds, the selection does not).
  {
    const size_t id = f.id("expand_a.select.7.raw");
    EXPECT_TRUE(f.rejects(seed, [&hf, id](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<HV>(x).at(40 * kCoeffBits + 1);
      v = hf.addf(v, hf.one());
    }));
  }
  // A wrong selection: two outputs of entry 0 swapped (the order of the
  // stream's accepted samples).
  {
    const size_t id = f.id("expand_a.select.0.raw");
    EXPECT_TRUE(f.rejects(seed, [id](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<HV>(x);
      for (size_t j = 0; j < kCoeffBits; ++j)
        std::swap(v.at(10 * kCoeffBits + j), v.at(11 * kCoeffBits + j));
    }));
  }
  // A wrong selection: accepted sample 3 of entry 1 skipped (outputs 3..
  // shifted down by one, the last repeated).
  {
    const size_t raw = f.id("expand_a.select.1.raw");
    const auto &h = std::get<HV>(honest.at(raw));
    EXPECT_TRUE(f.rejects(seed, [&h, raw](size_t at, Value &x) {
      if (at != raw) return;
      auto &v = std::get<HV>(x);
      for (size_t k = 3; k + 1 < kDegree; ++k)
        for (size_t j = 0; j < kCoeffBits; ++j)
          v.at(k * kCoeffBits + j) = h.at((k + 1) * kCoeffBits + j);
    }));
  }
}

// The host's bound is the circuit's: 6 SHAKE128 blocks per call.
static_assert(ml_dsa::kRejNTTPolyBlocks == kBlocks);

// The canonical coefficients of a matrix A_hat, r major.
std::vector<uint64_t> flat(const ml_dsa::MLDsaTypes<Params>::MatrixA &a) {
  std::vector<uint64_t> out;
  for (size_t i = 0; i < kRows; ++i)
    for (size_t j = 0; j < kCols; ++j) {
      const auto p = host::canonical(a[i][j]);
      out.insert(out.end(), p.begin(), p.end());
    }
  return out;
}

// The accepted candidates (23-bit samples below q) among the first
// CANDIDATES of SHAKE128(RHO_PRIME).
size_t acceptances(const std::vector<uint8_t> &rho_prime, size_t candidates) {
  std::vector<uint8_t> out;
  ml_dsa::G(rho_prime, 3 * candidates, out);
  size_t n = 0;
  for (size_t i = 0; i < candidates; ++i) {
    const uint32_t z = uint32_t(out[3 * i]) | (uint32_t(out[3 * i + 1]) << 8) |
                       (uint32_t(out[3 * i + 2] & 0x7f) << 16);
    if (z < kModulus) ++n;
  }
  return n;
}

TEST(ExpandAHost, HostBounded) {
  std::vector<std::vector<uint8_t>> keys = {
      ml_dsa::GetMlDsa44BenchmarkExample().pkey};
  for (const auto &ex : ml_dsa::GetMlDsa44Examples()) keys.push_back(ex.pkey);
  for (const auto &ex : ml_dsa::GetMlDsa44FailExamples())
    keys.push_back(ex.pkey);
  for (const auto &pk : keys) {
    const std::vector<uint8_t> rho(pk.begin(), pk.begin() + 32);
    const auto want = flat(ml_dsa::ExpandA<Params>(rho));
    const auto bounded = ml_dsa::ExpandABounded<Params>(rho);
    ASSERT_TRUE(bounded.has_value());
    EXPECT_EQ(flat(*bounded), want);
    EXPECT_EQ(host::expand_a(pk), want);
    // A 4-block squeeze (224 candidates) cannot hold 256 acceptances.
    EXPECT_FALSE(ml_dsa::ExpandABounded<Params>(rho, 4).has_value());
    EXPECT_THROW(host::expand_a_within(pk, 4), StatementRefused);
  }
  // FIPS 204's ExpandA known-answer vector (ml_dsa_ref_test_vectors.inc).
  const std::vector<uint8_t> kat = {
      0x5e, 0x1b, 0xad, 0xb2, 0x92, 0x27, 0x6b, 0x20, 0x2a, 0x6f, 0x6a,
      0xf9, 0x0e, 0x3c, 0xdc, 0xf6, 0xc1, 0xb5, 0xcc, 0x62, 0x60, 0xc0,
      0x1b, 0x74, 0x7d, 0xac, 0x61, 0x9f, 0xe1, 0x61, 0x30, 0x28};
  const auto kat_a = ml_dsa::ExpandABounded<Params>(kat);
  ASSERT_TRUE(kat_a.has_value());
  const std::vector<uint64_t> got = flat(*kat_a);
  for (size_t i = 0; i < kRows; ++i)
    for (size_t j = 0; j < kCols; ++j)
      for (size_t k = 0; k < kDegree; ++k)
        EXPECT_EQ(got[(i * kCols + j) * kDegree + k],
                  ml_dsa::kExpectedExpandAVectors[i][j][k])
            << i << " " << j << " " << k;
  EXPECT_EQ(got, flat(ml_dsa::ExpandA<Params>(kat)));
}

// A RejNTTPoly call at B blocks succeeds exactly when its 56 B candidates
// hold 256 acceptances: at 4 blocks (224 candidates) it always fails, and
// at 6 every entry of the benchmark key succeeds.
TEST(ExpandAHost, BoundIsTheAcceptanceCount) {
  const auto &pk = ml_dsa::GetMlDsa44BenchmarkExample().pkey;
  for (uint8_t r = 0; r < kRows; ++r)
    for (uint8_t s = 0; s < kCols; ++s) {
      std::vector<uint8_t> rho_prime(pk.begin(), pk.begin() + 32);
      rho_prime.push_back(s);
      rho_prime.push_back(r);
      for (size_t blocks : {size_t{1}, size_t{4}, size_t{5}, kBlocks}) {
        const bool enough = acceptances(rho_prime, blocks * kRate / 3) >=
                            kDegree;
        EXPECT_EQ(ml_dsa::RejNTTPolyBounded(rho_prime, blocks).has_value(),
                  enough)
            << int(r) << " " << int(s) << " " << blocks;
      }
      EXPECT_FALSE(ml_dsa::RejNTTPolyBounded(rho_prime, 4).has_value());
      EXPECT_TRUE(ml_dsa::RejNTTPolyBounded(rho_prime).has_value());
    }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
