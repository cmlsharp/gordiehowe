// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon native proof of possession's bench executable
// (falcon_native.h): falcon_native_bench COMMAND [FLAG...], every command
// at the set --falcon-set (512, the default, or 1024).
//   serve    a report_bench worker (bench_hook.h, bench/harness.h)
//   bench    the same records and --reps proofs without report_bench
//   export   the plan export and realized program (plan_export.h)
//   report   the compile report, with each domain's sizes on one line

#include <cstdio>
#include <memory>
#include <string>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "gordiehowe/examples/shared/ablation_testing.h"
#include "gordiehowe/examples/falcon/falcon_native_fixture.h"

namespace proofs::gordiehowe::examples::falcon::native {
namespace {

namespace hook = examples::bench_hook;

void add_set_flag(bench::Flags &f) {
  f.flag("falcon-set", "512", "the Falcon parameter set: 512 or 1024");
}

// The system of set S as the bench builds it under the ablation
// --ablation names, compiled, and handed to FN with its statement, witness
// and setup record.
template <class P, class S, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const std::string which = ablation::from_flag(f.str("ablation"));
  Env<P> env;
  const reference::Instance in = reference::instance<S>();
  const std::string config =
      ablation::config(std::string(S::kTag) + "-native", which);
  hook::Setup su{config.c_str(), P::kId};
  auto t0 = hook::Clock::now();
  const auto tp = ablation::build(
      [&](const BuildOptions &o) {
        return std::make_unique<FalconNativeSystem<P, S>>(env, in.msg.size(),
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
  return [&f](auto p, auto fn) {
    instance::with_set(f.str("falcon-set"), [&](auto s) {
      with_system<decltype(p), decltype(s)>(f, fn);
    });
  };
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  param_sets::with_profile(profile, [&](auto p) {
    instance::with_set(f.str("falcon-set"), [&](auto s) {
      using P = decltype(p);
      using S = decltype(s);
      const std::string path =
          export_plan<P, S>(dir, f.str("commit"), f.str("run-id"),
                            reference::instance<S>().msg.size());
      std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId,
                  path.c_str());
    });
  });
  return 0;
}

// The compile report of set S at profile P and each domain's sizes on one
// line.
template <class P, class S>
void report_at() {
  const Env<P> env;
  FalconNativeSystem<P, S> t(env, 32);
  auto c = t.compile();
  const std::string r = c->report();
  std::printf("%s", r.c_str());
  for (const char *d : {"H", "A"}) {
    const auto z = domain_size(r, d);
    std::printf("GH_FNN_SIZE set=%s profile=%s domain=%s layers=%zu quad=%zu "
                "inputs=%zu public=%zu committed=%zu affine=%zu\n",
                S::kName, P::kId, d, z.layers, z.quad, z.inputs, z.publics,
                z.committed, z.affine);
  }
}
int report(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  param_sets::with_profile(profile, [&](auto p) {
    instance::with_set(f.str("falcon-set"), [&](auto s) {
      report_at<decltype(p), decltype(s)>();
    });
  });
  return 0;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::native

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::falcon::native;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  namespace ablation = proofs::gordiehowe::examples::ablation;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The Falcon native proof of possession's benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          ablation::add_flag(f);
          app::add_set_flag(f);
        },
        [](const Flags &f) { return hook::serve_command(f, app::systems(f)); }},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          ablation::add_flag(f);
          app::add_set_flag(f);
        },
        [](const Flags &f) { return hook::bench_command(f, app::systems(f)); }},
       {"export", "the plan export and realized program",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_set_flag(f);
        },
        app::export_plans},
       {"report", "the compile report and each domain's sizes",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          app::add_set_flag(f);
        },
        app::report}});
}
