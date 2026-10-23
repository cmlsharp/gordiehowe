// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test helpers of the threading knob (threads.h), for any construction:
// single- and multi-threaded proofs verify in both modes, tampered proofs
// are rejected, the batches over their live rows give the proof over all
// their rows, and the bit adjoint's two paths give the same proof, single-
// and multi-threaded alike.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_THREADS_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_THREADS_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

#include "gordiehowe/compiler/field_skip.h"
#include "gordiehowe/compiler/test_switches.h"
#include "random/random.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::threads_testing {

// PREP (a prepared statement) proves W single- and multi-threaded, both
// from OpenSSL's CSPRNG (SecureRandomEngine): each proof verifies in both
// modes. The proofs' bytes may differ, since the multi-threaded commitments
// draw from their threads' engines (threads.h).
template <class Prep, class Assignment>
void expect_threads_cross_verify(const Prep &prep, const Assignment &w) {
  typename Prep::ProveOptions single, multi;
  single.multithreaded = false;
  multi.multithreaded = true;
  SecureRandomEngine rng;
  const std::vector<uint8_t> ps = prep.prove(w, rng, single);
  const std::vector<uint8_t> pm = prep.prove(w, rng, multi);
  EXPECT_TRUE(prep.verify(ps, nullptr, false));
  EXPECT_TRUE(prep.verify(ps, nullptr, true));
  EXPECT_TRUE(prep.verify(pm, nullptr, false));
  EXPECT_TRUE(prep.verify(pm, nullptr, true));
}

// A RandomEngine of std::mt19937_64 from a fixed seed: the same draws for
// every proof it starts.
class SeededEngine : public RandomEngine {
 public:
  explicit SeededEngine(uint64_t seed) : g_(seed) {}
  void bytes(uint8_t *buf, size_t n) override {
    for (size_t i = 0; i < n; ++i) buf[i] = uint8_t(g_());
  }

 private:
  std::mt19937_64 g_;
};

// PREP proves W four ways from one seed: the batches over all their rows (the
// full_rows test switch, compiler/test_switches.h) and over their live rows,
// each single- and multi-threaded. The four proofs are the same bytes, and the
// live-row multi-threaded proof verifies in both modes. The commitments run in
// domain order on the calling thread (ProveOptions::serial_commitments), since
// a system of several domains' multi-threaded commitments otherwise draw from
// their threads' engines (threads.h).
template <class Prep, class Assignment>
void expect_live_rows_same_proof(const Prep &prep, const Assignment &w) {
  std::vector<std::vector<uint8_t>> proofs;
  for (const bool full : {true, false})
    for (const bool multi : {false, true}) {
      typename Prep::ProveOptions opt;
      opt.multithreaded = multi;
      opt.serial_commitments = true;
      compiler::test_switches().full_rows = full;
      SeededEngine rng(7);
      proofs.push_back(prep.prove(w, rng, opt));
      compiler::test_switches().full_rows = false;
    }
  for (size_t i = 1; i < proofs.size(); ++i)
    EXPECT_TRUE(proofs[i] == proofs[0])
        << (i < 2 ? "full rows" : "live rows")
        << (i % 2 == 0 ? ", single-threaded" : ", multi-threaded");
  EXPECT_TRUE(prep.verify(proofs.back(), nullptr, false));
  EXPECT_TRUE(prep.verify(proofs.back(), nullptr, true));
}

// A multi-threaded proof of W on PREP (prepared from the compiled system
// C) with one byte changed is rejected multi-threaded: a byte of each
// batch's messages (each batch branch) and a byte of each domain's GKR
// proof (its GKR branch); the single-threaded verifier rejects it too.
template <class Compiled, class Prep, class Assignment>
void expect_branch_tampers_rejected(const Compiled &c, const Prep &prep,
                                    const Assignment &w) {
  typename Prep::ProveOptions opt;
  opt.multithreaded = true;
  std::vector<size_t> sections;
  opt.domain_bytes = &sections;
  SecureRandomEngine rng;
  const std::vector<uint8_t> proof = prep.prove(w, rng, opt);
  ASSERT_TRUE(prep.verify(proof, nullptr, true));
  size_t begin = proof.size();
  for (size_t s : sections) begin -= s;
  for (size_t d = 0; d < sections.size(); ++d) {
    // A byte of each batch's messages (each batch branch).
    size_t msgs = 0;
    const auto sizes = c.compiled_domain(d).batch_message_bytes();
    for (size_t b = 0; b < sizes.size(); ++b) {
      if (sizes[b] > 1) {
        auto bad = proof;
        bad[begin + msgs + 1] ^= 0x01;
        EXPECT_FALSE(prep.verify(bad, nullptr, true))
            << "batch " << b << ", domain " << d;
        EXPECT_FALSE(prep.verify(bad, nullptr, false))
            << "batch " << b << ", domain " << d << ", single-threaded";
      }
      msgs += sizes[b];
    }
    const size_t gkr = begin + msgs + Prep::Hash::kDigestSize + 4;
    if (gkr < begin + sections[d]) {
      auto bad = proof;
      bad[gkr] ^= 0x01;
      EXPECT_FALSE(prep.verify(bad, nullptr, true)) << "GKR, domain " << d;
      EXPECT_FALSE(prep.verify(bad, nullptr, false))
          << "GKR, domain " << d << ", single-threaded";
    }
    // A byte near the end of the section: the Ligero column openings.
    {
      auto bad = proof;
      bad[begin + sections[d] - 2] ^= 0x01;
      EXPECT_FALSE(prep.verify(bad, nullptr, true)) << "opening, domain " << d;
      EXPECT_FALSE(prep.verify(bad, nullptr, false))
          << "opening, domain " << d << ", single-threaded";
    }
    begin += sections[d];
  }
}

// PREP proves W from one seed six ways: the bit batches' adjoint
// (view_map.h) by every template's lane-program steps, by every
// template's folded products, and by the cheaper of the two per template
// (the default), each single- and multi-threaded, with the adjoint's
// per-instance self-check on (compiler/test_switches.h). The six proofs are
// the same bytes, and each verifies in both modes under its own path. The
// commitments run in domain order, as in expect_live_rows_same_proof.
template <class Prep, class Assignment>
void expect_adjoint_paths_same_proof(const Prep &prep, const Assignment &w) {
  using compiler::AdjointPath;
  auto &path = compiler::test_switches().adjoint_path;
  const bool check = compiler::test_switches().adjoint_check;
  compiler::test_switches().adjoint_check = true;
  std::vector<std::vector<uint8_t>> proofs;
  for (const AdjointPath p :
       {AdjointPath::kSteps, AdjointPath::kFolded, AdjointPath::kChosen})
    for (const bool multi : {false, true}) {
      path = p;
      typename Prep::ProveOptions opt;
      opt.multithreaded = multi;
      opt.serial_commitments = true;
      SeededEngine rng(7);
      proofs.push_back(prep.prove(w, rng, opt));
      EXPECT_TRUE(prep.verify(proofs.back(), nullptr, false))
          << "path " << int(p) << (multi ? ", multi" : ", single");
      EXPECT_TRUE(prep.verify(proofs.back(), nullptr, true))
          << "path " << int(p) << (multi ? ", multi" : ", single");
    }
  path = AdjointPath::kChosen;
  compiler::test_switches().adjoint_check = check;
  for (size_t i = 1; i < proofs.size(); ++i)
    EXPECT_TRUE(proofs[i] == proofs[0])
        << (i < 2 ? "steps" : i < 4 ? "folded" : "chosen")
        << (i % 2 == 0 ? ", single-threaded" : ", multi-threaded");
}

}  // namespace proofs::gordiehowe::threads_testing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_THREADS_TESTING_H_
