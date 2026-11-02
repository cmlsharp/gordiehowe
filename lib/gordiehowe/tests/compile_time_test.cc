// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Compile time of the post-quantum mDL, Falcon native, ML-DSA native and
// composite relations.
//
// CompileTime.DISABLED_Run builds, in PQ_FIELD_PROFILE's profile, the
// relation GH_CC_SYSTEM names (pq-mdoc: one attribute, the Fq arm;
// pq-mdoc-goldilocks: the same in the Goldilocks arm; mdoc: the ECDSA mDL
// at one attribute in its list-radius build, at the ROM parameters
// whichever profile is set; falcon-native: a 32-byte message; mldsa-native: the
// ML-DSA-44 benchmark example's lengths; composite: a 32-byte message,
// empty context) and prints
//   GH_CC system=S profile=P build=MS compile=MS total=MS digest=HEX
//         [cache=KIND]
// build: the example system's construction (its graph, lowering and the
// relation's compile); compile: the example system's compile() after it
// (the composite has none: 0). The compile cache is the directory
// GH_COMPILE_CACHE names (CompileOptions::cache; unset: off), and KIND is
// its outcome (off, hit, stored, not-stored, discarded).
//
// Provisional.ShapeMatchesCircuit: the provisional pass's tableau, which it
// takes from the circuit's shape (QuadCircuit::mkcircuit_shape), equals the
// one from the scheduled circuit, domain by domain, on Falcon native,
// Falcon emulated and ML-DSA native in the profile.
//
// Provisional.LazyMatchesEager: the composite, whose domain A costs an
// admissible triple, compiles to the same digest, report (placements and
// costs) and provisional tableaus whether the provisional pass gives the
// bit node's groups from its inputs and its full tableau on the first
// read, or its full tableau up front (CompileOptions::eager_provisional).

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <regex>
#include <string>
#include <vector>

#include "bench/timing.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/compiler/placement.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/examples/composite/composite.h"
#include "gordiehowe/examples/composite/composite_testing.h"
#include "gordiehowe/examples/falcon/falcon_emulated_testing.h"
#include "gordiehowe/examples/falcon/falcon_native_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/mdoc/mdoc_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples {
namespace {

using bench::Clock;
using bench::ms_since;

template <class C>
std::string outcome(const C &c) {
#if __has_include("gordiehowe/compiler/compile_cache.h")
  using K = CacheOutcome::Kind;
  switch (c.cache().kind) {
    case K::kOff:
      return " cache=off";
    case K::kHit:
      return " cache=hit";
    case K::kStored:
      return " cache=stored";
    case K::kNotStored:
      return " cache=not-stored(" + c.cache().reason + ")";
    case K::kDiscarded:
      return " cache=discarded(" + c.cache().reason + ")";
  }
#endif
  (void)c;
  return "";
}

template <class C>
void report(const char *system, const char *profile, double build,
            double compile, const C &c) {
  std::string hex;
  for (uint8_t b : c.digest()) {
    char x[3];
    std::snprintf(x, sizeof(x), "%02x", b);
    hex += x;
  }
  std::printf("GH_CC system=%s profile=%s build=%.1f compile=%.1f total=%.1f "
              "digest=%s%s\n",
              system, profile, build, compile, build + compile, hex.c_str(),
              outcome(c).c_str());
  std::fflush(stdout);
}

// An example system T built by MAKE, then compiled by its compile().
template <class Make>
void run_system(const char *system, const char *profile, Make make) {
  const auto t0 = Clock::now();
  auto t = make();
  const double build = ms_since(t0);
  const auto t1 = Clock::now();
  const auto c = t->compile();
  report(system, profile, build, ms_since(t1), *c);
}

TEST(CompileTime, DISABLED_Run) {
  const char *s = std::getenv("GH_CC_SYSTEM");
  ASSERT_NE(s, nullptr) << "GH_CC_SYSTEM";
  const std::string sys = s;
  BuildOptions bo;
  if (const char *d = std::getenv("GH_COMPILE_CACHE")) bo.compile.cache.dir = d;
  param_sets::with_profile([&](auto p) {
    using P = decltype(p);
    if (sys == "falcon-native") {
      static const falcon::native::Env<P> env;
      run_system(s, P::kId, [&bo] {
        return std::make_unique<falcon::native::FalconNativeSystem<P>>(env, 32,
                                                                       bo);
      });
    } else if (sys == "mldsa-native") {
      static const mldsa::Env<P> env;
      const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
      run_system(s, P::kId, [&ex, &bo] {
        return std::make_unique<mldsa::MLDSANativeSystem<P, mldsa::MLDSA44>>(
            env, ex.msg.size(), ex.ctx.size(), mldsa::PackingAblation::kNone,
            bo);
      });
    } else if (sys == "pq-mdoc") {
      using S = pq_mdoc::PqMdocSystem<P, pq_mdoc::FqArm>;
      static const typename S::E env;
      const size_t tbs = pq_mdoc::bench_instance(1).statement.device_tbs.size();
      pq_mdoc::PqMdocConfig cfg;
      cfg.cache = bo.compile.cache;
      run_system(s, P::kId,
                 [tbs, cfg] { return std::make_unique<S>(env, 1, tbs, cfg); });
    } else if (sys == "pq-mdoc-goldilocks") {
      using S = pq_mdoc::PqMdocSystem<P, pq_mdoc::GoldilocksArm>;
      static const typename S::E env;
      const size_t tbs = pq_mdoc::bench_instance(1).statement.device_tbs.size();
      pq_mdoc::PqMdocConfig cfg;
      cfg.cache = bo.compile.cache;
      run_system(s, P::kId,
                 [tbs, cfg] { return std::make_unique<S>(env, 1, tbs, cfg); });
    } else if (sys == "mdoc") {
      namespace full = mdoc::full;
      const auto t0 = Clock::now();
      const full::MdocSystem m(full::list_h_profile(), full::list_a_profile(),
                               1, examples::mdoc::kBlocks, true, bo);
      report(s, "narrow", ms_since(t0), 0, m.compiled());
    } else if (sys == "composite") {
      using Sys = typename composite::Env<P>::Sys;
      static const composite::Env<P> env;
      const auto t0 = Clock::now();
      const auto rel = composite::composite<P>(env, 32, 0, bo.compile);
      const double build = ms_since(t0);
      report(s, P::kId, build, 0, rel.template typed<Sys>().compiled());
    } else {
      FAIL() << "GH_CC_SYSTEM: " << sys;
    }
  });
}

TEST(Provisional, ShapeMatchesCircuit) {
  param_sets::with_profile([](auto p) {
    using P = decltype(p);
    using Record = std::map<std::string, std::vector<size_t>>;
    // The provisional tableaus of the system MAKE builds, by domain, with
    // FULL from the scheduled circuit.
    auto record = [](const auto &make, bool full, const char *what) {
      Record r;
      BuildOptions o;
      o.compile.full_provisional = full;
      o.compile.provisional_record = &r;
      const auto sys = make(o);
      (void)sys->compile();
      EXPECT_FALSE(r.empty()) << what;
      return r;
    };
    auto same = [&](const auto &make, const char *what) {
      const Record shape = record(make, false, what);
      const Record full = record(make, true, what);
      EXPECT_EQ(shape, full) << what << " " << P::kId;
    };
    static const falcon::native::Env<P> fn;
    same([](const BuildOptions &o) {
      return std::make_unique<falcon::native::FalconNativeSystem<P>>(fn, 32,
                                                                     o);
    }, "falcon-native");
    static const falcon::emulated::Env<P> fe;
    same([](const BuildOptions &o) {
      return std::make_unique<falcon::emulated::FalconEmulatedSystem<P>>(
          fe, 32, o);
    }, "falcon-emulated");
    static const mldsa::Env<P> md;
    const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
    same([&ex](const BuildOptions &o) {
      return std::make_unique<mldsa::MLDSANativeSystem<P, mldsa::MLDSA44>>(
          md, ex.msg.size(), ex.ctx.size(), mldsa::PackingAblation::kNone, o);
    }, "mldsa-native");
  });
}

TEST(Provisional, LazyMatchesEager) {
  param_sets::with_profile([](auto p) {
    using P = decltype(p);
    using Sys = typename composite::Env<P>::Sys;
    using Record = std::map<std::string, std::vector<size_t>>;
    static const composite::Env<P> env;
    struct Out {
      std::vector<uint8_t> digest;
      std::string report;
    };
    // The composite compiled with EAGER, its tableaus in RECORD when set.
    auto run = [](bool eager, Record *record) {
      CompileOptions o;
      o.eager_provisional = eager;
      o.provisional_record = record;
      const auto rel = composite::composite<P>(env, 32, 0, o);
      const auto &c = rel.template typed<Sys>().compiled();
      return Out{c.digest(), c.report()};
    };
    const Out lazy = run(false, nullptr);
    const Out eager = run(true, nullptr);
    // A's triple is admissible: the report shows its cost.
    EXPECT_TRUE(std::regex_search(lazy.report,
                                  std::regex("quadratic triples [0-9]")))
        << P::kId;
    EXPECT_EQ(lazy.digest, eager.digest) << P::kId;
    EXPECT_EQ(lazy.report, eager.report) << P::kId;
    Record lr, er;
    const Out lazy_rec = run(false, &lr);
    const Out eager_rec = run(true, &er);
    EXPECT_FALSE(lr.empty()) << P::kId;
    EXPECT_EQ(lr, er) << P::kId;
    EXPECT_EQ(lazy_rec.digest, lazy.digest) << P::kId;
    EXPECT_EQ(eager_rec.digest, lazy.digest) << P::kId;
  });
}

}  // namespace
}  // namespace proofs::gordiehowe::examples
