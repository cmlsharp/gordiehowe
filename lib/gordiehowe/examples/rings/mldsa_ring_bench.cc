// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The ML-DSA-44 private ring's bench executable (mldsa_ring_native.h,
// mldsa_ring_carrier.h): mldsa_ring_bench COMMAND [FLAG...].
//   serve    a report_bench worker (bench_hook.h, bench/harness.h) of the
//            arm --ring-arm at --ring-size members
//   bench    the same records and --reps proofs without report_bench
//   export   both arms' plan exports and realized programs at --ring-size
//            members: GordieHowe/Generated/MLDSA44/Ring/{Native,Carrier}/
//            <parameter set>/{Plan,Program}.lean
//   report   the arm's compile report, with each domain's sizes on one line

#include <cstdio>
#include <stdexcept>
#include <string>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "gordiehowe/examples/rings/mldsa_ring_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

namespace hook = examples::bench_hook;

void add_ring_flags(bench::Flags &f, bool arm) {
  f.flag("ring-size", "256", "the ring's members");
  if (arm) f.flag("ring-arm", "native", "the arm: native or carrier");
}

// FN(arm, p) at the arm --ring-arm names, in the profile P.
template <class P, class Fn>
void with_arm(const bench::Flags &f, P p, Fn fn) {
  const std::string arm = f.str("ring-arm");
  if (arm == "carrier")
    fn(CarrierArm<P>{}, p);
  else if (arm == "native")
    fn(NativeArm<P>{}, p);
  else
    throw bench::UsageError("unknown ring arm " + arm);
}

// The arm's system on a ring of --ring-size members (signer at R - 1),
// compiled, and handed to FN with its statement, witness and setup record.
template <class P, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const size_t R = f.num("ring-size");
  with_arm(f, P{}, [&](auto arm, auto) {
    using Arm = decltype(arm);
    typename Arm::E env;
    const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
    const RingCase rc(ex, R, R - 1);
    hook::Setup su{Arm::kConfig, P::kId, R};
    auto t0 = hook::Clock::now();
    typename Arm::T t(env, R, ex.msg.size(), ex.ctx.size());
    su.build = hook::ms_since(t0) - hook::relation_compile_ms(t);
    su.compile = hook::relation_compile_ms(t);
    const auto c = t.compile();
    fn(*c, t.statement(rc.ring, ex.msg, ex.ctx),
       [&] { return t.witness(rc.signer); }, su);
  });
}
auto systems(const bench::Flags &f) {
  return [&f](auto p, auto fn) { with_system<decltype(p)>(f, fn); };
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const size_t R = f.num("ring-size");
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    auto one = [&](auto arm) {
      using Arm = decltype(arm);
      const typename Arm::E e;
      typename Arm::T t(e, R, ex.msg.size(), ex.ctx.size());
      const auto c = t.compile();
      const compiler::ExportMeta meta{Arm::kConfig,     P::kId,
                                      f.str("commit"),  f.str("run-id"),
                                      ex.msg.size(),    ex.ctx.size()};
      const std::string path = write_plan(*c, dir, meta);
      std::printf("GH_EXPORT_PLAN arm=%s profile=%s path=%s\n", Arm::kName,
                  P::kId, path.c_str());
    };
    one(NativeArm<P>{});
    one(CarrierArm<P>{});
  });
  return 0;
}

// The arm's compile report and sizes, and one honest proof.
int report(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t R = f.num("ring-size");
  bool ok = false;
  param_sets::with_profile(profile, [&](auto p) {
    with_arm(f, p, [&](auto arm, auto) {
      using Arm = decltype(arm);
      using P = decltype(p);
      Fixture<Arm> fx(R);
      const std::string r = fx.c->report();
      std::printf("%s", r.c_str());
      for (const char *d : {"A", "H"}) {
        const auto s = domain_size(r, d);
        std::printf("GH_MLRING_SIZE arm=%s profile=%s R=%zu domain=%s "
                    "layers=%zu quad=%zu inputs=%zu public=%zu committed=%zu "
                    "nw=%zu nq=%zu affine=%zu\n",
                    Arm::kName, P::kId, R, d, s.layers, s.quad, s.inputs,
                    s.publics, s.committed, s.nw, s.nq, s.affine);
      }
      ok = fx.prove_verify();
    });
  });
  return ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::mldsa;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The ML-DSA-44 private ring's benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          app::add_ring_flags(f, true);
        },
        [](const Flags &f) { return hook::serve_command(f, app::systems(f)); }},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          app::add_ring_flags(f, true);
        },
        [](const Flags &f) { return hook::bench_command(f, app::systems(f)); }},
       {"export", "both arms' plan exports and realized programs",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_ring_flags(f, false);
        },
        app::export_plans},
       {"report", "the arm's compile report and each domain's sizes",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          app::add_ring_flags(f, true);
        },
        app::report}});
}
