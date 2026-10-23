// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon-512 native proof of possession's bench executable
// (falcon_native.h): falcon_native_bench COMMAND [FLAG...].
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

// The system as the bench builds it under the ablation --ablation names,
// compiled, and handed to FN with its statement, witness and setup record.
template <class P, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const std::string which = ablation::from_flag(f.str("ablation"));
  Env<P> env;
  const reference::Instance in = reference::instance();
  const std::string config = ablation::config("falcon-native", which);
  hook::Setup su{config.c_str(), P::kId};
  auto t0 = hook::Clock::now();
  const auto tp = ablation::build(
      [&](const BuildOptions &o) {
        return std::make_unique<FalconNativeSystem<P>>(env, in.msg.size(), o);
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
    const std::string path =
        export_plan<P>(dir, f.str("commit"), f.str("run-id"),
                       reference::instance().msg.size());
    std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId, path.c_str());
  });
  return 0;
}

int report(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  param_sets::with_profile(profile, [](auto p) {
    using P = decltype(p);
    const Env<P> env;
    FalconNativeSystem<P> t(env, 32);
    auto c = t.compile();
    const std::string r = c->report();
    std::printf("%s", r.c_str());
    for (const char *d : {"H", "A"}) {
      const auto s = domain_size(r, d);
      std::printf("GH_FNN_SIZE profile=%s domain=%s layers=%zu quad=%zu "
                  "inputs=%zu public=%zu committed=%zu affine=%zu\n",
                  P::kId, d, s.layers, s.quad, s.inputs, s.publics,
                  s.committed, s.affine);
    }
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
      argc, argv, "The Falcon-512 native proof of possession's benches.",
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
       {"report", "the compile report and each domain's sizes",
        proofs::bench::add_common_flags, app::report}});
}
