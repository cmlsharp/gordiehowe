// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The bench executable of mdoc's domain H (mdoc_hash.h): mdoc_hash_bench bench
// [FLAG...]. Domain H alone (commit, prove, verify, proof bytes) on
// doc 3 at each of --attrs attributes, --reps proofs each, medians, at
// Longfellow v7's profile (mdoc_hash_testing.h).

#include <cstdio>
#include <string>
#include <vector>

#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/examples/mdoc/mdoc_hash_fixture.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mdoc::testing {
namespace {

using bench::Clock;
using bench::ms_since;

int bench_attrs(const bench::Flags &f) {
  bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  std::vector<size_t> attrs;
  for (const std::string &s : f.list("attrs")) attrs.push_back(std::stoul(s));
  bool all_ok = true;
  for (size_t n : attrs) {
    const Case c = bench_case(3, n);
    const Witness w = witness_of(c);
    auto t0 = Clock::now();
    Compiled &x = compiled(n);
    const double build = ms_since(t0);
    const DomainPlan p = x.c->compiled_domain(0).plan();
    std::printf("MDOC_PLAN attrs=%zu build+compile=%.1f nw=%zu nq=%zu N=%zu "
                "k=%zu t=%zu nrow=%zu block_enc=%zu layers=%zu wires=%zu "
                "quad_terms=%zu ninputs=%zu\n",
                n, build, p.nw, p.nq, p.N, p.k, p.t, p.nrow,
                p.block_enc, p.layers, p.wires, p.quad_terms, p.ninputs);
    if (f.on("print-report"))
      std::printf("%s\n", x.c->report().c_str());
    std::fflush(stdout);
    auto prep = x.c->prepare(x.sys->statement(c, w));
    SecureRandomEngine rng;
    std::vector<double> wt, cm, pr, cp, vf, by;
    for (size_t i = 0; i < reps; ++i) {
      const auto wa = x.sys->witness(w.data);
      ProveTimes times;
      Sys::ProveOptions opt;
      opt.times = &times;
      const auto proof = prep.prove(wa, rng, opt);
      t0 = Clock::now();
      const bool ok = prep.verify(proof);
      vf.push_back(ms_since(t0));
      all_ok = all_ok && ok;
      wt.push_back(times.witness);
      cm.push_back(times.commit);
      pr.push_back(times.prove);
      cp.push_back(times.commit + times.prove);
      by.push_back(double(proof.size()));
      std::printf("MDOC_RUN attrs=%zu rep=%zu witness=%.3f commit=%.3f "
                  "prove=%.3f verify=%.3f bytes=%zu ok=%d\n",
                  n, i, times.witness, times.commit, times.prove, vf.back(),
                  proof.size(), int(ok));
      std::fflush(stdout);
    }
    std::printf("MDOC_MEDIAN attrs=%zu n=%zu witness=%.3f commit=%.3f "
                "prove=%.3f commit+prove=%.3f verify=%.3f bytes=%.0f\n",
                n, reps, bench::median(wt), bench::median(cm), bench::median(pr),
                bench::median(cp), bench::median(vf), bench::median(by));
    std::fflush(stdout);
  }
  return all_ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mdoc::testing

int main(int argc, char **argv) {
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The bench of mdoc's domain H.",
      {{"bench", "domain H alone at each attribute count, medians",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("attrs", "1,2,4", "the attribute counts")
              .flag("reps", "7", "the proofs per count")
              .toggle("print-report", "print each compile report");
        },
        proofs::gordiehowe::examples::mdoc::testing::bench_attrs}});
}
