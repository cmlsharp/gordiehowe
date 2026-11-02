// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon ring carrier (R = 64) under the threading knob (threads.h):
// single- and multi-threaded proofs verify in both modes, and a changed
// batch, GKR or opening byte is rejected in both modes, at both profiles.
// Both arms' statement setup with and without a runner (util/parallel.h,
// as a multi-threaded prepare installs one): the same cached values and
// the same fixed-seed proofs.

#include <map>
#include <vector>

#include "gordiehowe/examples/rings/falcon_ring_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

template <class P>
class FalconRingThreads : public ::testing::Test {};
TYPED_TEST_SUITE(FalconRingThreads, param_sets::Profiles,
                 param_sets::ProfileName);

// X's statement prepared without a runner and on a pool of 8 threads: the
// cached public computations are the same values, and fixed-seed proofs
// are the same bytes and verify under the other mode's prepare.
template <class Fx>
void expect_setup_modes_agree(const Fx &x) {
  using Value = typename Fx::Value;
  gordiehowe::internal::TaskPool pool(7);
  std::vector<std::map<size_t, Value>> values;
  std::vector<std::vector<uint8_t>> proofs;
  for (const bool multi : {false, true}) {
    x.c->forget_setup();
    parallel::Scope scope(multi ? &pool : nullptr);
    std::map<size_t, Value> v;
    auto prep = x.c->prepare(
        x.statement(), [&v](size_t id, Value &y) { v.emplace(id, y); });
    values.push_back(std::move(v));
    typename Fx::Sys::ProveOptions opt;
    opt.fixed_seed = 7;
    opt.multithreaded = false;
    SecureRandomEngine rng;
    proofs.push_back(prep.prove(x.witness(), rng, opt));
  }
  EXPECT_FALSE(values[0].empty());
  EXPECT_TRUE(values[0] == values[1]);
  EXPECT_TRUE(proofs[0] == proofs[1]);
  for (const bool multi : {false, true}) {
    x.c->forget_setup();
    parallel::Scope scope(multi ? &pool : nullptr);
    EXPECT_TRUE(x.c->prepare(x.statement()).verify(proofs[!multi], nullptr,
                                                    false));
  }
  x.c->forget_setup();
}

TYPED_TEST(FalconRingThreads, SetupModesAgree) {
  expect_setup_modes_agree(
      CarrierFixture<TypeParam>(carrier_instance<TypeParam>(100)));
  expect_setup_modes_agree(
      NativeFixture<TypeParam>(native_instance<TypeParam>(100)));
}

TYPED_TEST(FalconRingThreads, SameProof) {
  CarrierFixture<TypeParam> x(carrier_instance<TypeParam>(64));
  auto prep = x.c->prepare(x.statement());
  gordiehowe::threads_testing::expect_threads_cross_verify(prep, x.witness());
}

TYPED_TEST(FalconRingThreads, BranchTampersRejected) {
  CarrierFixture<TypeParam> x(carrier_instance<TypeParam>(64));
  auto prep = x.c->prepare(x.statement());
  gordiehowe::threads_testing::expect_branch_tampers_rejected(*x.c, prep, x.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring
