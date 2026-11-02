// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The crossing's bench executable (crossing_fixture.h): crossing_bench bench
// [FLAG...]. 4,096 integers of 23 bits below q (ExpandA's crossing without
// the Keccak batch), --reps proofs per placement of A's Boolean checks
// (pinned to the circuit, pinned to a field batch, and the placement
// rule's choice), medians per domain.

#include <cstdio>
#include <string>
#include <vector>

#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/examples/mldsa/crossing_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

int bench_crossing(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const Env<P> env;
    const size_t n = 4096;
    const auto v = sample_integers(n);
    for (Placement where :
         {Placement::kCircuit, Placement::kBatch, Placement::kAuto}) {
      CrossingSystem<P> t(env, n, where);
      const auto c = gordiehowe::compile(t.cs, compile_profile<P, MLDSA44>());
      if (f.on("print-report")) std::printf("%s\n", c->report().c_str());
      auto prep = c->prepare(typename CrossingSystem<P>::Sys::Assignment{});
      SecureRandomEngine rng;
      const auto wit = t.witness(v);
      const size_t nd = c->num_domains();
      std::vector<std::vector<double>> dc(nd), dp(nd), dv(nd), db(nd);
      for (size_t r = 0; r < reps; ++r) {
        ProveTimes times;
        std::vector<size_t> dbytes;
        typename CrossingSystem<P>::Sys::ProveOptions opt;
        opt.times = &times;
        opt.domain_bytes = &dbytes;
        const auto proof = prep.prove(wit, rng, opt);
        VerifyTimes vt;
        ok = prep.verify(proof, &vt) && ok;
        for (size_t d = 0; d < nd; ++d) {
          dc[d].push_back(times.domain_commit[d]);
          dp[d].push_back(times.domain_prove[d]);
          dv[d].push_back(vt.domain[d]);
          db[d].push_back(double(dbytes[d]));
        }
      }
      for (size_t d = 0; d < nd; ++d) {
        const DomainPlan pl = c->compiled_domain(d).plan();
        std::printf("CROSSING_DOMAIN profile=%s bit_checks=%s n=%zu "
                    "domain=%s commit=%.3f prove=%.3f commit+prove=%.3f "
                    "verify=%.3f bytes=%.0f quad_terms=%zu layers=%zu "
                    "nw=%zu\n",
                    P::kId, placement_name(where), reps,
                    c->domain(d).name.c_str(), bench::median(dc[d]),
                    bench::median(dp[d]),
                    bench::median(dc[d]) + bench::median(dp[d]),
                    bench::median(dv[d]), bench::median(db[d]),
                    pl.quad_terms, pl.layers, pl.nw);
      }
      std::fflush(stdout);
    }
  });
  return ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

int main(int argc, char **argv) {
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The crossing's bench.",
      {{"bench", "the three placements of A's Boolean checks, medians",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("reps", "7", "the proofs per placement")
              .toggle("print-report", "print each compile report");
        },
        proofs::gordiehowe::examples::mldsa::bench_crossing}});
}
