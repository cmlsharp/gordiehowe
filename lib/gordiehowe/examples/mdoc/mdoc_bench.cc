// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Plain mdoc's bench executable (mdoc.h, ROM parameters only):
// mdoc_bench COMMAND [FLAG...].
//   serve        a report_bench worker (bench_hook.h, bench/harness.h) of
//                the list-radius build at --attrs attributes and --blocks
//                SHA-256 blocks of MSO buffer (default v7's 40), or with
//                --no-device of its device-signature ablation (config
//                mdoc-nodevice; mdoc.h's mdoc_relation, DEVICE_SIGNATURE
//                false), whose proofs each prepare the statement afresh,
//                timed, as every bench worker's do
//   bench        the same records and --reps proofs without report_bench
//   compare      the whole proof on doc 3 at each of --attrs attributes, at
//                v7's Ligero in both domains (rate 7, 132 columns) and at
//                list radius (--config v7, list or both), --reps proofs
//                each, medians. Each proof's setup (the public
//                computations: Q_I's fixed-base table and [e2] G) runs
//                uncached and is reported apart and inside the prover's and
//                the verifier's totals.
//   vega-report  the compile reports (circuit, Ligero tableau and per-round
//                soundness) of the list-radius build at 1 attribute, at
//                v7's 40 blocks and at Vega's bound (kVegaBlocks)
//   export       the plan export of the list-radius build at 1 attribute
//                (its tableaus chosen as the bench chooses them, on doc 3):
//                GordieHowe/Generated/MDL/ECDSA/ROMParams/{Plan,Program}.lean.
//                Plain mdoc has no fixed message, so msgLen is 0; the MSO's
//                buffer is in the sha256-varlen and filtered-permutation
//                records.

#include <cstdio>
#include <memory>
#include <string>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/shared/ablation_testing.h"
#include "gordiehowe/examples/mdoc/mdoc_fixture.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mdoc::full {
namespace {

namespace hook = examples::bench_hook;

// The common flags, with the field profile checked: plain mdoc is defined
// at the ROM parameters only, whatever --profile's default.
void apply_flags(const bench::Flags &f) {
  if (bench::apply_common_flags(f) != P::kId && f.given("profile"))
    throw bench::UsageError(std::string("plain mdoc runs at --profile ") +
                            P::kId + " only");
}

void add_system_flags(bench::Flags &f) {
  f.flag("attrs", "1", "the attributes")
      .flag("blocks", std::to_string(examples::mdoc::kBlocks),
            "the MSO buffer's SHA-256 blocks")
      .toggle("no-device", "the device-signature ablation (mdoc-nodevice)");
  ablation::add_flag(f);
}

// The list-radius build the flags select, compiled, and handed to FN with
// its statement, witness and setup record.
template <class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const size_t n = f.num("attrs");
  const size_t blocks = f.num("blocks");
  const bool device = !f.on("no-device");
  const std::string which = ablation::from_flag(f.str("ablation"));
  const Instance x = instance_of(bench_case(3, n), blocks);
  const std::string config =
      ablation::config(device ? "mdoc" : "mdoc-nodevice", which);
  hook::Setup su{config.c_str(), P::kId};
  auto t0 = Clock::now();
  const auto bp = ablation::build(
      [&](const examples::BuildOptions &o) {
        return std::make_unique<Built>(
            build_list_radius(n, blocks, device, o));
      },
      [](const Built &v) -> const Compiled & { return *v.c; }, t0, which);
  const Built &b = *bp;
  su.compile = b.sys->rel.typed<Sys>().compile_ms();
  su.build = ms_since(t0) - su.compile;
  fn(*b.c, b.sys->statement(x.statement),
     [&] { return b.sys->witness(x.data); }, su);
}

int serve(const bench::Flags &f) {
  apply_flags(f);
  const hook::Options opts = hook::hook_options(f);
  with_system(f, [&](const auto &c, const auto &st, auto w,
                     const hook::Setup &su) {
    hook::serve(c, st, w, su, opts);
  });
  return 0;
}
int bench_system(const bench::Flags &f) {
  apply_flags(f);
  const hook::Options opts = hook::hook_options(f);
  bool ok = false;
  with_system(f, [&](const auto &c, const auto &st, auto w,
                     const hook::Setup &su) {
    ok = hook::run(c, st, w, su, opts, f.num("reps"));
  });
  return ok ? 0 : 1;
}



bool compare_one(const char *config, size_t n, Built &b, const Instance &x,
                 size_t reps) {
  bool all = true;
  const Compiled &c = *b.c;
  for (size_t d = 0; d < c.num_domains(); ++d)
    std::printf("MDOC_PLAN config=%s attrs=%zu domain=%s %s\n", config, n,
                c.domain(d).name.c_str(), plan_line(c, d).c_str());
  std::fflush(stdout);
  const Assignment st = b.sys->statement(x.statement);
  const Assignment wit = b.sys->witness(x.data);
  SecureRandomEngine rng;
  std::vector<double> wt, cm, pr, sp, sv, vf, ptot, vtot;
  std::vector<std::vector<double>> dc(2), dp(2), dv(2), db(2);
  std::vector<double> bytes;
  for (size_t r = 0; r < reps; ++r) {
    std::vector<uint8_t> proof;
    ProveTimes times;
    std::vector<size_t> dbytes;
    double setup_p = 0, setup_v = 0, verify = 0;
    {
      c.forget_setup();
      const auto t0 = Clock::now();
      auto prep = c.prepare(st);
      setup_p = ms_since(t0);
      Sys::ProveOptions opt;
      opt.times = &times;
      opt.domain_bytes = &dbytes;
      proof = prep.prove(wit, rng, opt);
    }
    VerifyTimes vt;
    bool ok = false;
    {
      c.forget_setup();
      const auto t0 = Clock::now();
      auto prep = c.prepare(st);
      setup_v = ms_since(t0);
      const auto t1 = Clock::now();
      ok = prep.verify(proof, &vt);
      verify = ms_since(t1);
    }
    all = all && ok;
    std::printf("MDOC_RUN config=%s attrs=%zu rep=%zu witness=%.3f "
                "commit=%.3f prove=%.3f setup_p=%.3f setup_v=%.3f "
                "verify=%.3f bytes=%zu H_commit=%.3f H_prove=%.3f "
                "H_verify=%.3f H_bytes=%zu A_commit=%.3f A_prove=%.3f "
                "A_verify=%.3f A_bytes=%zu ok=%d\n",
                config, n, r, times.witness, times.commit, times.prove,
                setup_p, setup_v, verify, proof.size(), times.domain_commit[0],
                times.domain_prove[0], vt.domain[0], dbytes[0],
                times.domain_commit[1], times.domain_prove[1], vt.domain[1],
                dbytes[1], int(ok));
    std::fflush(stdout);
    wt.push_back(times.witness);
    cm.push_back(times.commit);
    pr.push_back(times.prove);
    sp.push_back(setup_p);
    sv.push_back(setup_v);
    vf.push_back(verify);
    ptot.push_back(setup_p + times.witness + times.commit + times.prove);
    vtot.push_back(setup_v + verify);
    bytes.push_back(double(proof.size()));
    for (size_t d = 0; d < 2; ++d) {
      dc[d].push_back(times.domain_commit[d]);
      dp[d].push_back(times.domain_prove[d]);
      dv[d].push_back(vt.domain[d]);
      db[d].push_back(double(dbytes[d]));
    }
  }
  std::printf("MDOC_MEDIAN config=%s attrs=%zu n=%zu witness=%.3f "
              "commit=%.3f prove=%.3f commit+prove=%.3f setup=%.3f "
              "prover_total=%.3f verify=%.3f verify_total=%.3f bytes=%.0f\n",
              config, n, reps, bench::median(wt), bench::median(cm), bench::median(pr),
              bench::median([&] {
                std::vector<double> v;
                for (size_t i = 0; i < cm.size(); ++i) v.push_back(cm[i] + pr[i]);
                return v;
              }()),
              bench::median(sv), bench::median(ptot), bench::median(vf), bench::median(vtot),
              bench::median(bytes));
  for (size_t d = 0; d < 2; ++d)
    std::printf("MDOC_DOMAIN config=%s attrs=%zu domain=%s commit=%.3f "
                "prove=%.3f verify=%.3f bytes=%.0f\n",
                config, n, c.domain(d).name.c_str(), bench::median(dc[d]),
                bench::median(dp[d]), bench::median(dv[d]), bench::median(db[d]));
  std::fflush(stdout);
  return all;
}

int compare(const bench::Flags &f) {
  apply_flags(f);
  const size_t reps = f.num("reps");
  std::vector<size_t> attrs;
  for (const std::string &s : f.list("attrs")) attrs.push_back(std::stoul(s));
  const std::string config = f.str("config");
  if (config != "v7" && config != "list" && config != "both")
    throw bench::UsageError("unknown config " + config);
  bool ok = true;
  for (size_t n : attrs) {
    const Instance x = instance_of(bench_case(3, n));
    if (config == "v7" || config == "both") {
      const auto t0 = Clock::now();
      // --unpacked-s0: H commits its GF(2^16) words unpacked
      // (DomainProfile::unpacked_s0).
      HProfile hp = h_profile();
      hp.unpacked_s0 = f.on("unpacked-s0");
      Built b = build(hp, a_profile(), n);
      std::printf("MDOC_BUILD config=v7 attrs=%zu build+compile=%.1f\n", n,
                  ms_since(t0));
      if (n == attrs.front() || f.on("print-report"))
        std::printf("%s\n", b.c->report().c_str());
      ok = compare_one("v7", n, b, x, reps) && ok;
    }
    if (config == "list" || config == "both") {
      Built b = build_list_radius(n);
      ok = compare_one("list", n, b, x, reps) && ok;
    }
  }
  return ok ? 0 : 1;
}

int vega_report(const bench::Flags &f) {
  apply_flags(f);
  for (size_t blocks : {examples::mdoc::kBlocks, kVegaBlocks}) {
    const Built b = build_list_radius(1, blocks);
    std::printf("MDOC_REPORT blocks=%zu\n%s\n", blocks,
                b.c->report().c_str());
  }
  return 0;
}

int export_plans(const bench::Flags &f) {
  apply_flags(f);
  const std::string dir = hook::export_dir(f);
  const Built b = build_list_radius(1);
  const compiler::ExportMeta meta{"mdoc", P::kId, f.str("commit"),
                                  f.str("run-id"), 0};
  const std::string path = write_plan(*b.c, dir, meta);
  std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId, path.c_str());
  return 0;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mdoc::full

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::mdoc::full;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "Plain mdoc's benches (ROM parameters).",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          app::add_system_flags(f);
        },
        app::serve},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          app::add_system_flags(f);
        },
        app::bench_system},
       {"compare", "v7's Ligero against list radius, medians",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("attrs", "1,2,4", "the attribute counts")
              .flag("reps", "9", "the proofs per build")
              .flag("config", "both", "v7, list or both")
              .toggle("unpacked-s0", "v7's H commits its GF(2^16) words "
                                     "unpacked")
              .toggle("print-report", "print every v7 build's report");
        },
        app::compare},
       {"vega-report", "the compile reports at v7's and Vega's bounds",
        proofs::bench::add_common_flags, app::vega_report},
       {"export", "the plan export and realized program",
        hook::add_export_flags, app::export_plans}});
}
