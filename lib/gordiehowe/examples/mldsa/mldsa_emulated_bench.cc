// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The ML-DSA emulated proof of possession's bench executable
// (mldsa_emulated.h): mldsa_emulated_bench COMMAND [FLAG...].
//   serve    a report_bench worker (bench_hook.h, bench/harness.h)
//   bench    the same records and --reps proofs without report_bench
//   export   the plan export and realized program (plan_export.h)
//   report   the compile report, with each domain's sizes on one line
//   parallel single- against multi-threaded proofs, interleaved
// serve, bench and report take --packing, a packing ablation (setup.h's
// PackingAblation: config mldsa-emulated-nobitpack or -subfieldrows), and
// --param-set, the parameter set (mldsa_bench_flags.h: config
// mldsa-emulated at ML-DSA-44, mldsa65-emulated or mldsa87-emulated).
// export writes ML-DSA-44's plan; parallel runs ML-DSA-44.

#include <chrono>
#include <cstdio>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/examples/shared/ablation_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_bench_flags.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated_fixture.h"

namespace proofs::gordiehowe::examples::mldsa::emulated {
namespace {

namespace hook = examples::bench_hook;

// The system at the parameter set S as the bench builds it under the
// ablations --ablation and --packing name, compiled, and handed to FN with
// its statement, witness and setup record.
template <class P, class S, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const std::string which = ablation::from_flag(f.str("ablation"));
  const PackingAblation pk = ablation::packing(f);
  Env<P> env;
  const auto &ex = examples::mldsa::support::benchmark_example<S>();
  const Existing<S> old{ex};
  const auto sig = old.signature();
  const std::string config = ablation::config(
      std::string(S::kConfigStem) + "-emulated" + packing_suffix(pk), which);
  hook::Setup su{config.c_str(), P::kId};
  auto t0 = hook::Clock::now();
  const auto tp = ablation::build(
      [&](const BuildOptions &o) {
        return std::make_unique<MLDSAEmulatedSystem<P, S>>(
            env, ex.msg.size(), ex.ctx.size(), pk, o);
      },
      [](const auto &s) -> const auto & { return *s.compile(); }, t0, which);
  auto &t = *tp;
  su.build = hook::ms_since(t0) - hook::relation_compile_ms(t);
  su.compile = hook::relation_compile_ms(t);
  const auto c = t.compile();
  fn(*c, t.statement(ex.pkey, ex.ctx), [&] { return t.witness(ex.msg, sig); },
     su);
}
auto systems(const bench::Flags &f) {
  return [&f](auto p, auto fn) {
    with_param_set_flag(f, [&](auto s) {
      with_system<decltype(p), decltype(s)>(f, fn);
    });
  };
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const std::string path =
        support::export_plan<P>(dir, f.str("commit"), f.str("run-id"));
    std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId, path.c_str());
  });
  return 0;
}

// The compile report and sizes, and one honest proof.
int report(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  bool ok = false;
  param_sets::with_profile(profile, [&](auto p) {
    with_param_set_flag(f, [&](auto set) {
      using P = decltype(p);
      using S = decltype(set);
      Fixture<P, S> fx(examples::mldsa::support::benchmark_example<S>(),
                       ablation::packing(f));
      const std::string r = fx.c->report();
      std::printf("%s", r.c_str());
      for (const char *d : {"A", "H"}) {
        const auto s = domain_size(r, d);
        std::printf("GH_MLEMU_SIZE profile=%s set=%s domain=%s layers=%zu "
                    "quad=%zu inputs=%zu public=%zu committed=%zu nw=%zu "
                    "nq=%zu affine=%zu\n",
                    P::kId, S::kName, d, s.layers, s.quad, s.inputs,
                    s.publics, s.committed, s.nw, s.nq, s.affine);
      }
      ok = fx.prove_verify();
    });
  });
  return ok ? 0 : 1;
}


// Single- against multi-threaded, from one prepared statement: --warmups
// unrecorded proofs per mode, then --reps rounds, each a single- and a
// multi-threaded proof and verification. Prints one GH_PAR_RUN line per
// proof and GH_PAR_MEDIAN, the median of every figure, per mode. Per
// domain X: X_commit_p (commitment and low-degree test), X_post_p (after
// the fork), X_pre_v (the verifier's commitment and low-degree test) and
// X_post_v.
int parallel(const bench::Flags &flags) {
  const std::string profile = bench::apply_common_flags(flags);
  const size_t warmups = flags.num("warmups"), reps = flags.num("reps");
  bool all_ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    Fixture<P> f;
    auto prep = f.c->prepare(f.statement());
    const size_t nd = f.c->num_domains();
    SecureRandomEngine rng;
    using Row = std::vector<std::pair<std::string, double>>;
    auto run = [&](bool multi, bool &ok, size_t &bytes) {
      const auto w = f.witness();
      ProveTimes pt;
      typename Fixture<P>::Sys::ProveOptions opt;
      opt.times = &pt;
      opt.multithreaded = multi;
      const auto proof = prep.prove(w, rng, opt);
      VerifyTimes vt;
      const auto t0 = std::chrono::steady_clock::now();
      ok = prep.verify(proof, &vt, multi);
      const double v = std::chrono::duration<double, std::milli>(
                           std::chrono::steady_clock::now() - t0)
                           .count();
      bytes = proof.size();
      Row r{{"prover", pt.commit + pt.prove},
            {"verify", v},
            {"witness", pt.witness},
            {"commit", pt.commit},
            {"prove", pt.prove}};
      for (size_t d = 0; d < nd; ++d) {
        const std::string x = f.c->domain(d).name;
        r.push_back({x + "_commit_p", pt.domain_commit[d]});
        r.push_back({x + "_post_p", pt.domain_prove[d]});
        r.push_back({x + "_pre_v", vt.domain[d] - vt.domain_post[d]});
        r.push_back({x + "_post_v", vt.domain_post[d]});
      }
      return r;
    };
    for (size_t i = 0; i < warmups; ++i) {
      bool ok;
      size_t bytes;
      run(false, ok, bytes);
      run(true, ok, bytes);
    }
    std::vector<Row> rows[2];
    for (size_t r = 0; r < reps; ++r) {
      for (int multi = 0; multi < 2; ++multi) {
        bool ok = false;
        size_t bytes = 0;
        const Row x = run(multi != 0, ok, bytes);
        std::printf("GH_PAR_RUN profile=%s mode=%s r=%zu", P::kId,
                    multi ? "multi" : "single", r);
        for (const auto &[k, val] : x) std::printf(" %s=%.3f", k.c_str(), val);
        std::printf(" bytes=%zu ok=%d\n", bytes, ok);
        all_ok = all_ok && ok;
        rows[multi].push_back(x);
      }
    }
    for (int multi = 0; multi < 2; ++multi) {
      std::printf("GH_PAR_MEDIAN profile=%s mode=%s", P::kId,
                  multi ? "multi" : "single");
      for (size_t k = 0; k < rows[multi][0].size(); ++k) {
        std::vector<double> col;
        for (const auto &x : rows[multi]) col.push_back(x[k].second);
        std::printf(" %s=%.3f", rows[multi][0][k].first.c_str(), bench::median(col));
      }
      std::printf("\n");
    }
    std::fflush(stdout);
  });
  return all_ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa::emulated

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::mldsa::emulated;
  namespace examples = proofs::gordiehowe::examples;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  namespace ablation = proofs::gordiehowe::examples::ablation;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The ML-DSA emulated proof of possession's benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          ablation::add_flag(f);
          ablation::add_packing_flag(f);
          examples::mldsa::add_param_set_flag(f);
        },
        [](const Flags &f) { return hook::serve_command(f, app::systems(f)); }},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          ablation::add_flag(f);
          ablation::add_packing_flag(f);
          examples::mldsa::add_param_set_flag(f);
        },
        [](const Flags &f) { return hook::bench_command(f, app::systems(f)); }},
       {"export", "the plan export and realized program",
        hook::add_export_flags, app::export_plans},
       {"report", "the compile report and each domain's sizes",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          ablation::add_packing_flag(f);
          examples::mldsa::add_param_set_flag(f);
        },
        app::report},
       {"parallel", "single- against multi-threaded proofs, interleaved",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("warmups", "2", "the unrecorded proofs per mode")
              .flag("reps", "9", "the rounds");
        },
        app::parallel}});
}
