// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The transcript forks and joins (transcript_fork.h): the byte layout of a
// branch's label and of the join, rebuilt by hand from the documented
// steps, and a branch's overrun reaching the joined transcript.

#include "gordiehowe/transcript_fork.h"

#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "random/transcript.h"
#include "util/crypto.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

template <class Hash>
void check_fork_join() {
  using T = BasicTranscript<Hash>;
  constexpr size_t k = Hash::kDigestSize;
  BasicProofSeed<Hash> seed;
  for (size_t i = 0; i < k; ++i) seed.bytes[i] = uint8_t(i);
  const uint8_t init[] = {'t', 'e', 's', 't'};
  const uint8_t x[] = {1, 2, 3}, a[] = {4, 5}, b[] = {6, 7, 8, 9};
  auto prefix = [&](T &t) {
    t.write(x, sizeof(x));
    uint8_t c[16];
    t.bytes(c, sizeof(c));  // a point open at the fork
  };
  // Each branch's items: branch 0 ends with a point open.
  auto items0 = [&](T &t, uint8_t *c) {
    t.write(a, sizeof(a));
    t.bytes(c, 40);
  };
  auto items1 = [&](T &t, uint8_t *c) {
    t.write(b, sizeof(b));
    t.bytes(c, 24);
    t.write(a, sizeof(a));
  };
  // The fork and join.
  T p(init, sizeof(init), seed);
  prefix(p);
  auto br = fork::split(p, 3, "GF(2^128)", 2);
  uint8_t c0[40], c1[24];
  items0(*br[0], c0);
  items1(*br[1], c1);
  fork::join(p, br, 3);
  // By hand: the parent closes its point; each branch is a copy that
  // writes its label, then its items; the parent writes each branch's
  // join item, its digest after its last point closes.
  T q(init, sizeof(init), seed);
  prefix(q);
  q.close_open_point();
  uint8_t dg[2][k], d0[40], d1[24];
  for (size_t i = 0; i < 2; ++i) {
    T r = q.clone();
    const auto l = fork::label(3, i, "GF(2^128)");
    r.write(l.data(), l.size());
    if (i == 0) items0(r, d0); else items1(r, d1);
    r.close_open_point();
    r.get(dg[i]);
  }
  EXPECT_EQ(0, std::memcmp(c0, d0, sizeof(c0)));
  EXPECT_EQ(0, std::memcmp(c1, d1, sizeof(c1)));
  for (size_t i = 0; i < 2; ++i) {
    const auto j = fork::join_item(3, i, dg[i], k);
    ASSERT_EQ(j.size(), 15u + 8 + 8 + k);
    q.write(j.data(), j.size());
  }
  uint8_t gp[k], gq[k];
  p.get(gp);
  q.get(gq);
  EXPECT_EQ(0, std::memcmp(gp, gq, k));
  // The next challenges agree.
  uint8_t e0[32], e1[32];
  p.bytes(e0, sizeof(e0));
  q.bytes(e1, sizeof(e1));
  EXPECT_EQ(0, std::memcmp(e0, e1, sizeof(e0)));
  // The label: "gordiehowe.branch" || u64le(3) || u64le(1) || name.
  const auto l1 = fork::label(3, 1, "GF(2^128)");
  ASSERT_EQ(l1.size(), 17u + 8 + 8 + 9);
  EXPECT_EQ(std::string(l1.begin(), l1.begin() + 17), "gordiehowe.branch");
  EXPECT_EQ(l1[17], 3);
  EXPECT_EQ(l1[25], 1);
  EXPECT_EQ(std::string(l1.begin() + 33, l1.end()), "GF(2^128)");
  const auto j = fork::join_item(3, 1, dg[1], k);
  EXPECT_EQ(std::string(j.begin(), j.begin() + 15), "gordiehowe.join");
  EXPECT_EQ(0, std::memcmp(j.data() + 31, dg[1], k));
}

TEST(TranscriptFork, ByteLayout) {
  check_fork_join<SHA256>();
  check_fork_join<SHA384>();
}

// A branch's overrun reaches the joined transcript.
TEST(TranscriptFork, JoinCarriesExhaustion) {
  BasicProofSeed<SHA256> seed{};
  const uint8_t init[] = {'t'};
  BasicTranscript<SHA256> p(init, sizeof(init), seed);
  auto br = fork::split(p, 0, "F", 2);
  br[1]->set_stream_budget(8);
  br[1]->write(init, sizeof(init));
  uint8_t c[64];
  br[1]->bytes(c, sizeof(c));
  EXPECT_FALSE(p.exhausted());
  fork::join(p, br, 0);
  EXPECT_TRUE(p.exhausted());
}

}  // namespace
}  // namespace proofs::gordiehowe
