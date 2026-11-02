// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 native proof of possession (falcon_native.h):
// the typed suite FalconNative (falcon_native_cases.h) at Falcon-512, and
//
//   FalconNative512.Layout              cells, needles, groups, realizations
//
// The benches, the plan export and the compile report are
// falcon_native_bench's commands (falcon_native_bench.cc).

#include "gordiehowe/examples/falcon/falcon_native_cases.h"

namespace proofs::gordiehowe::examples::falcon::native {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon512, FalconNative,
                               instance::Cases<Falcon512>, instance::CaseName);

template <class P>
class FalconNative512 : public ::testing::Test {};
TYPED_TEST_SUITE(FalconNative512, param_sets::Profiles,
                 param_sets::ProfileName);

// A's layout: the norm's column carries in a table of 189 rows (one
// carry per column, below the honest 189), the
// other static needles and every late MAC needle in the table of 64 under
// one late histogram (one group of at most 12288 needles in both profiles),
// the field equality, and the MAC's grouping.
TYPED_TEST(FalconNative512, Layout) {
  using P = TypeParam;
  const Env<P> env;
  FalconNativeSystem<P, Falcon512> t(env, 32);
  auto c = t.compile();
  const std::string r = c->report();
  const bool qrom = P::kPostQuantum;
  for (const std::string want : {
           std::string("assert_mod 'signature.equation': m = p = 12289, the "
                       "field equality (512 affine rows)"),
           std::string("norm.cc: direct T=189 -> bound 189"),
           std::string("encoding.high: complement T=64"),
           qrom ? std::string("table A.64: 9925 static and 2304 dynamic "
                              "needles; one late histogram of 64")
                : std::string("table A.64: 9925 static and 1152 dynamic "
                              "needles; one late histogram of 64"),
           std::string("table A.189: 5120 static and 0 dynamic needles"),
       })
    EXPECT_NE(r.find(want), std::string::npos) << want << "\n" << r;
  const auto &A = a_domain<P>(t.cs);
  // A commits no unused top batch carries, one carry per norm column, the
  // budget's four digits and the 189 rows' histogram, with one range group
  // in the table of 64.
  EXPECT_EQ(c->coordinates(A.index), qrom ? 27336u : 25672u);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::native
