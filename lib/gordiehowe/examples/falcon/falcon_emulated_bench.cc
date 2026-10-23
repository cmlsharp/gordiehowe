// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon-512 emulated proof of possession's bench executable
// (falcon_emulated.h): falcon_emulated_bench COMMAND [FLAG...].
//   serve             a report_bench worker (bench_hook.h, bench/harness.h)
//   bench             the same records and --reps proofs without
//                     report_bench
//   export            the plan export and realized program (plan_export.h)
//   witness-profile   where the witness time goes, by node

#include <algorithm>
#include <cstdio>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/examples/shared/ablation_testing.h"
#include "gordiehowe/examples/falcon/falcon_emulated_fixture.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

namespace hook = examples::bench_hook;

// The system as the bench builds it under the ablation --ablation names,
// compiled, and handed to FN with its statement, witness and setup record.
template <class P, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const std::string which = ablation::from_flag(f.str("ablation"));
  Env<P> env;
  const Instance in = bench_instance();
  const std::string config = ablation::config("falcon-emulated", which);
  hook::Setup su{config.c_str(), P::kId};
  auto t0 = hook::Clock::now();
  const auto tp = ablation::build(
      [&](const BuildOptions &o) {
        return std::make_unique<FalconEmulatedSystem<P>>(env, in.msg.size(),
                                                         o);
      },
      [](const auto &s) -> const auto & { return *s.compile(); }, t0, which);
  auto &t = *tp;
  su.build = hook::ms_since(t0) - hook::relation_compile_ms(t);
  su.compile = hook::relation_compile_ms(t);
  const auto c = t.compile();
  fn(*c, t.statement(in.hhat),
     [&] { return t.witness(in.nonce, in.msg, in.s2); }, su);
}
auto systems(const bench::Flags &f) {
  return [&f](auto p, auto fn) { with_system<decltype(p)>(f, fn); };
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const std::string path = export_plan<P>(dir, f.str("commit"),
                                            f.str("run-id"),
                                            bench_instance().msg.size());
    std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId, path.c_str());
  });
  return 0;
}

// Where the witness time goes: the prover calls the tamper hook right
// after each generator, bit view and pad copy, so the time between two
// calls is the later node's generator, its type check and any derived
// views evaluated in between. --reps proofs; the median per node, largest
// first.
int witness_profile(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    using T = FalconEmulatedSystem<P>;
    Env<P> env;
    const Instance in = bench_instance();
    T t(env, in.msg.size());
    const auto c = t.compile();
    const auto prep = c->prepare(t.statement(in.hhat));
    SecureRandomEngine rng;
    std::map<size_t, std::vector<double>> per;
    std::vector<double> total;
    for (size_t r = 0; r < reps; ++r) {
      const auto w = t.witness(in.nonce, in.msg, in.s2);
      std::vector<std::pair<size_t, hook::Clock::time_point>> at;
      at.reserve(128);
      typename T::Sys::ProveOptions opt;
      ProveTimes pt;
      opt.times = &pt;
      opt.tamper = [&](size_t id, typename T::Sys::Value &) {
        at.push_back({id, hook::Clock::now()});
      };
      prep.prove(w, rng, opt);
      for (size_t i = 1; i < at.size(); ++i)
        per[at[i].first].push_back(
            std::chrono::duration<double, std::milli>(at[i].second -
                                                      at[i - 1].second)
                .count());
      total.push_back(pt.witness);
    }
    std::vector<std::pair<double, size_t>> rows;
    double listed = 0;
    for (auto &[id, v] : per) {
      rows.push_back({bench::median(v), id});
      // mac.value's interval spans the commitment and the first challenge
      // round.
      if (t.cs.graph().nodes[id].name != "mac.value")
        listed += bench::median(v);
    }
    std::sort(rows.rbegin(), rows.rend());
    std::printf("GH_WITNESS profile=%s median witness %.3f ms; not between "
                "two hooks (the first generator, h2p.shake.r0.value.words, and "
                "mac.value) %.3f ms\n",
                P::kId, bench::median(total), bench::median(total) - listed);
    for (const auto &[ms, id] : rows)
      std::printf("GH_WITNESS %-34s %8.3f ms\n",
                  t.cs.graph().nodes[id].name.c_str(), ms);
  });
  return 0;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::falcon::emulated;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  namespace ablation = proofs::gordiehowe::examples::ablation;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The Falcon-512 emulated proof of possession's benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          ablation::add_flag(f);
        },
        [](const Flags &f) { return hook::serve_command(f, app::systems(f)); }},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          ablation::add_flag(f);
        },
        [](const Flags &f) { return hook::bench_command(f, app::systems(f)); }},
       {"export", "the plan export and realized program",
        hook::add_export_flags, app::export_plans},
       {"witness-profile", "the witness time by node, median over --reps",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("reps", "20", "the proofs to time");
        },
        app::witness_profile}});
}
