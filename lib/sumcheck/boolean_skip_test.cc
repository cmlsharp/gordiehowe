// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#include "circuits/tests/sha3/sha3_reference.h"
#include "sumcheck/boolean_skip.h"
#include "sumcheck/testing/boolean_skip_lookup_reference.h"
#include "gtest/gtest.h"
#include <cstdio>
#include <memory>
#include <random>
#include "random/secure_random_engine.h"
#include "random/transcript.h"
namespace proofs {
namespace {
using B = BooleanSkip;
// These seeds model a previously bound instance ONLY for this algebra test.
// No commitment, ZK masking, or authenticated opening is implemented here.
using Seed = Transcript::Seed;
// The prover's per-proof seed.
Seed draw_seed() {
  SecureRandomEngine rng;
  return BasicProofSeed<>::draw(rng);
}
std::unique_ptr<Transcript> transcript(unsigned width, unsigned trial,
                                       const Seed &sigma) {
  uint8_t seed[4] = {uint8_t(width), uint8_t(trial), 0x42, 0x53};
  return std::make_unique<Transcript>(seed, sizeof(seed), sigma);
}
// The verifier opens its transcript with the prover's seed.
bool verify(const B &b, const B::Proof &proof,
            const std::vector<B::Word> &words, unsigned trial,
            const Seed &sigma) {
  auto ts = transcript(b.width(), trial, sigma);
  return b.verify(proof, words.size(), *ts,
                  [&](const auto &r, const auto &s, const auto &v) {
                    return b.reference_open(words, r, s, v);
                  });
}
std::vector<B::Word> keccak_chi() {
  // Same 72-byte seed and 10 permutations as the full Falcon-512 benchmark
  // (2*639 SHAKE output bytes). Collect actual chi operands at every round.
  uint64_t state[5][5]{};
  uint8_t block[136]{};
  std::mt19937 rng(20260915);
  for (size_t i = 0; i < 72; ++i)
    block[i] = uint8_t(rng());
  block[72] = 0x1f;
  block[135] = 0x80;
  Sha3Reference::xorin(state, block, 136);
  std::vector<B::Word> words;
  for (unsigned perm = 0; perm < 10; ++perm)
    for (unsigned round = 0; round < 24; ++round) {
      Sha3Reference::theta(state);
      Sha3Reference::rho(state);
      uint64_t s[5][5];
      Sha3Reference::pi(state, s);
      for (unsigned x = 0; x < 5; ++x)
        for (unsigned y = 0; y < 5; ++y) {
          uint64_t a = ~s[(x + 1) % 5][y], b = s[(x + 2) % 5][y];
          words.push_back({a, b, a & b});
        }
      Sha3Reference::chi(s, state);
      Sha3Reference::iota(state, round);
    }
  return words;
}
TEST(BooleanSkip, HonestAndTampered) {
  B::Field f;
  std::mt19937_64 rng(923);
  for (unsigned w : {1u, 8u, 16u, 32u, 64u}) {
    B b(f, w);
    for (size_t count : {1u, 3u, 17u}) {
      std::vector<B::Word> words;
      for (size_t i = 0; i < count; ++i) {
        auto a = rng(), v = rng();
        words.push_back({a, v, a & v});
      }
      B::Stats stats;
      const Seed sigma = draw_seed();
      auto ts = transcript(w, count, sigma);
      auto proof = b.prove(words, *ts, stats);
      ASSERT_TRUE(verify(b, proof, words, count, sigma));
      auto altered = proof;
      if (!altered.rounds.empty()) {
        f.add(altered.rounds[0][1], f.one());
        EXPECT_FALSE(verify(b, altered, words, count, sigma));
      }
      altered = proof;
      f.add(altered.terminal[0], f.one());
      EXPECT_FALSE(verify(b, altered, words, count, sigma));
      if (w > 1) {
        altered = proof;
        f.add(altered.skip[0], f.one());
        EXPECT_FALSE(verify(b, altered, words, count, sigma));
      }
      words[0].c ^= uint64_t(1) << 63;
      const Seed sigma2 = draw_seed();
      ts = transcript(w, count, sigma2);
      auto bad = b.prove(words, *ts, stats);
      EXPECT_FALSE(verify(b, bad, words, count, sigma2));
    }
  }
}
TEST(BooleanSkip, FixedAccessMatchesLookup) {
  B::Field f;
  std::mt19937_64 rng(719);
  for (unsigned width : {1u, 2u, 4u, 8u, 16u, 32u, 64u}) {
    B fixed(f, width);
    BooleanSkipLookupReference reference(f, width);
    for (size_t n : {1u, 3u, 17u, 257u})
      for (bool masked : {false, true}) {
        std::vector<B::Word> words;
        std::vector<BooleanSkipLookupReference::Word> old;
        for (size_t i = 0; i < n; ++i) {
          uint64_t a = rng(), b = rng(), c = (i % 2) ? rng() : (a & b);
          if (i == 0)
            a = b = c = 0;
          if (i == 1)
            a = b = c = ~uint64_t(0);
          words.push_back({a, b, c});
          old.push_back({a, b, c});
        }
        std::vector<B::Elt> pads(256);
        for (auto &p : pads)
          p = f.of_scalar_field(
              std::array<uint64_t, 4>{rng(), rng(), rng(), rng()});
        const Seed sigma = draw_seed();
        auto tf = transcript(width, n, sigma), tr = transcript(width, n, sigma);
        B::Stats sf;
        BooleanSkipLookupReference::Stats sr;
        auto pf = fixed.prove(words, *tf, sf, masked ? &pads : nullptr);
        auto pr = reference.prove(old, *tr, sr, masked ? &pads : nullptr);
        EXPECT_EQ(pf.skip, pr.skip);
        EXPECT_EQ(pf.rounds, pr.rounds);
        EXPECT_EQ(pf.terminal, pr.terminal);
        uint8_t bf[32], br[32];
        tf->bytes(bf, 32);
        tr->bytes(br, 32);
        EXPECT_TRUE(std::equal(bf, bf + 32, br));
      }
  }
}
TEST(BooleanSkip, DISABLED_FixedVsLookup) {
  B::Field f;
  auto words = keccak_chi();
  std::vector<BooleanSkipLookupReference::Word> old;
  for (auto v : words)
    old.push_back({v.a, v.b, v.c});
  for (unsigned width : {8u, 16u, 32u}) {
    B fixed(f, width);
    BooleanSkipLookupReference reference(f, width);
    for (unsigned trial = 0; trial < 8; ++trial)
      for (unsigned order = 0; order < 2; ++order) {
        bool use_fixed = ((trial + order) % 2) == 0;
        auto ts = transcript(width, trial, draw_seed());
        double skip, bind, sumcheck;
        auto start = std::chrono::steady_clock::now();
        if (use_fixed) {
          B::Stats s;
          auto p = fixed.prove(words, *ts, s);
          skip = s.skip;
          bind = s.bind;
          sumcheck = s.sumcheck;
        } else {
          BooleanSkipLookupReference::Stats s;
          auto p = reference.prove(old, *ts, s);
          skip = s.skip;
          bind = s.bind;
          sumcheck = s.sumcheck;
        }
        printf("SKIP_ACCESS fixed=%d width=%u trial=%u total=%.6f skip=%.6f "
               "bind=%.6f sumcheck=%.6f\n",
               use_fixed, width, trial,
               std::chrono::duration<double, std::milli>(
                   std::chrono::steady_clock::now() - start)
                   .count(),
               skip, bind, sumcheck);
        fflush(stdout);
      }
  }
}
TEST(BooleanSkip, DISABLED_Bench) {
  B::Field f;
  auto words = keccak_chi();
  ASSERT_EQ(words.size(), 6000u);
  std::vector<std::unique_ptr<B>> reducers;
  for (unsigned w : {1u, 8u, 16u, 32u, 64u}) {
    auto start = std::chrono::steady_clock::now();
    reducers.push_back(std::make_unique<B>(f, w));
    printf("SKIP_SETUP width=%u ms=%.6f\n", w,
           std::chrono::duration<double, std::milli>(
               std::chrono::steady_clock::now() - start)
               .count());
  }
  for (unsigned trial = 0; trial < 10; ++trial)
    for (unsigned j = 0; j < reducers.size(); ++j) {
      const B &b = *reducers[(j + trial) % reducers.size()];
      B::Stats stats;
      const Seed sigma = draw_seed();
      auto ts = transcript(b.width(), trial, sigma);
      auto start = std::chrono::steady_clock::now();
      auto proof = b.prove(words, *ts, stats);
      double total = std::chrono::duration<double, std::milli>(
                         std::chrono::steady_clock::now() - start)
                         .count();
      ASSERT_TRUE(
          verify(b, proof, words, trial, sigma)); // Deliberately outside prover timer.
      printf("SKIP_BENCH trial=%u width=%u rows=%zu total=%.6f weights=%.6f "
             "skip=%.6f bind=%.6f sumcheck=%.6f message_bytes=%zu\n",
             trial, b.width(), stats.rows, total, stats.weights, stats.skip,
             stats.bind, stats.sumcheck,
             (proof.skip.size() + 2 * proof.rounds.size() + 3) *
                 B::Field::kBytes);
      fflush(stdout);
    }
}
} // namespace
} // namespace proofs
