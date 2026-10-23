// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ExpandA's bench executable (expand_a.h, expand_a_testing.h's configs):
// expand_a_bench bench [FLAG...]. The cost split: --configs, comma-separated
// among keccak, select, cross1, cross4 and full, each optionally suffixed
// .circuit or .batch for A's Boolean checks pinned there; --reps proofs
// each, medians, per domain.

#include <cstdio>
#include <string>
#include <vector>

#include "bench/cli.h"
#include "bench/timing.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "gordiehowe/examples/mldsa/expand_a_testing.h"
#include "gordiehowe/examples/instances.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

using bench::Clock;
using bench::ms_since;

template <class C>
std::string plan_line(const C &c, size_t d) {
  const DomainPlan p = c.compiled_domain(d).plan();
  char buf[400];
  std::snprintf(buf, sizeof(buf),
                "nw=%zu nq=%zu N=%zu k=%zu t=%zu nrow=%zu block_enc=%zu "
                "list_radius=%d layers=%zu wires=%zu quad_terms=%zu "
                "ninputs=%zu npub=%zu triples=%zu",
                p.nw, p.nq, p.N, p.k, p.t, p.nrow, p.block_enc,
                int(p.list_radius), p.layers, p.wires, p.quad_terms,
                p.ninputs, p.npub, p.quad_triples);
  return buf;
}

template <class P>
bool bench_config(const std::string &name, const ExpandAConfig &cfg,
                  size_t reps, bool report) {
  bool all_ok = true;
  const Env<P> env;
  auto t0 = Clock::now();
  ExpandASystem<P> t(env, cfg);
  const double build = ms_since(t0);
  t0 = Clock::now();
  const auto c = t.compile();
  const double compile = ms_since(t0);
  std::printf("EXPANDA_SETUP profile=%s config=%s build=%.1f compile=%.1f\n",
              P::kId, name.c_str(), build, compile);
  if (report)
    std::printf("%s\n", c->report().c_str());
  const size_t nd = c->num_domains();
  for (size_t d = 0; d < nd; ++d)
    std::printf("EXPANDA_PLAN profile=%s config=%s domain=%s %s\n", P::kId,
                name.c_str(), c->domain(d).name.c_str(),
                plan_line(*c, d).c_str());
  std::fflush(stdout);
  const auto seed = seed_of(ml_dsa::GetMlDsa44BenchmarkExample().pkey);
  const auto st = t.statement();
  const auto wit = t.witness(seed);
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  std::vector<double> wt, cm, pr, vf, cp, bytes;
  std::vector<std::vector<double>> dc(nd), dp(nd), dv(nd), db(nd);
  for (size_t r = 0; r < reps; ++r) {
    ProveTimes times;
    std::vector<size_t> dbytes;
    typename ExpandASystem<P>::Sys::ProveOptions opt;
    opt.times = &times;
    opt.domain_bytes = &dbytes;
    const auto proof = prep.prove(wit, rng, opt);
    VerifyTimes vt;
    const auto t1 = Clock::now();
    const bool ok = prep.verify(proof, &vt);
    const double verify = ms_since(t1);
    all_ok = all_ok && ok;
    std::printf("EXPANDA_RUN profile=%s config=%s rep=%zu witness=%.3f "
                "commit=%.3f prove=%.3f verify=%.3f bytes=%zu",
                P::kId, name.c_str(), r, times.witness, times.commit,
                times.prove, verify, proof.size());
    for (size_t d = 0; d < nd; ++d)
      std::printf(" %s_commit=%.3f %s_prove=%.3f %s_verify=%.3f %s_bytes=%zu",
                  c->domain(d).name.c_str(), times.domain_commit[d],
                  c->domain(d).name.c_str(), times.domain_prove[d],
                  c->domain(d).name.c_str(), vt.domain[d],
                  c->domain(d).name.c_str(), dbytes[d]);
    std::printf(" ok=%d\n", int(ok));
    std::fflush(stdout);
    wt.push_back(times.witness);
    cm.push_back(times.commit);
    pr.push_back(times.prove);
    cp.push_back(times.commit + times.prove);
    vf.push_back(verify);
    bytes.push_back(double(proof.size()));
    for (size_t d = 0; d < nd; ++d) {
      dc[d].push_back(times.domain_commit[d]);
      dp[d].push_back(times.domain_prove[d]);
      dv[d].push_back(vt.domain[d]);
      db[d].push_back(double(dbytes[d]));
    }
  }
  std::printf("EXPANDA_MEDIAN profile=%s config=%s n=%zu witness=%.3f "
              "commit=%.3f prove=%.3f commit+prove=%.3f verify=%.3f "
              "bytes=%.0f\n",
              P::kId, name.c_str(), reps, bench::median(wt), bench::median(cm), bench::median(pr),
              bench::median(cp), bench::median(vf), bench::median(bytes));
  for (size_t d = 0; d < nd; ++d)
    std::printf("EXPANDA_DOMAIN profile=%s config=%s domain=%s commit=%.3f "
                "prove=%.3f verify=%.3f bytes=%.0f\n",
                P::kId, name.c_str(), c->domain(d).name.c_str(),
                bench::median(dc[d]), bench::median(dp[d]), bench::median(dv[d]), bench::median(db[d]));
  std::fflush(stdout);
  return all_ok;
}

int bench_configs(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    for (const auto &name : f.list("configs")) {
      ExpandAConfig cfg;
      // <part>.circuit, <part>.batch: A's Boolean checks pinned there.
      std::string part = name;
      if (const size_t at = name.find('.'); at != std::string::npos) {
        part = name.substr(0, at);
        const std::string where = name.substr(at + 1);
        if (where == "circuit") {
          cfg.bit_checks = Placement::kCircuit;
        } else if (where == "batch") {
          cfg.bit_checks = Placement::kBatch;
        } else {
          throw bench::UsageError("unknown placement " + name);
        }
      }
      if (part == "keccak") {
        cfg.select = false;
      } else if (part == "select") {
        cfg.cross = 0;
      } else if (part == "cross1") {
        cfg.cross = 1;
      } else if (part == "cross4") {
        cfg.cross = 4;
      } else if (part != "full") {
        throw bench::UsageError("unknown config " + name);
      }
      ok = bench_config<P>(name, cfg, reps, f.on("print-report")) && ok;
    }
  });
  return ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

int main(int argc, char **argv) {
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "ExpandA's bench.",
      {{"bench", "the cost split of the configurations, medians",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("configs", "keccak,select,cross1,cross4,full",
                 "the configurations, comma-separated")
              .flag("reps", "7", "the proofs per configuration")
              .toggle("print-report", "print each compile report");
        },
        proofs::gordiehowe::examples::mldsa::bench_configs}});
}
