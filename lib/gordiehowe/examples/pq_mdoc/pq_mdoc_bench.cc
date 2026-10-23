// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Post-quantum mdoc's bench executable (pq_mdoc.h):
// pq_mdoc_bench COMMAND [FLAG...].
//   bench    the proof at each of --attrs attributes, --warmups warm-up
//            rounds (default 2) and then --reps measured rounds (default
//            9), one proof per arm and threading mode each, medians of the
//            measured rounds, per domain, in the arms --arm (fq, goldilocks, or a
//            comma-separated list, which interleaves the arms per attribute
//            count and repetition). At each count of --nodevice-attrs
//            (default none) each arm's device-signature ablation
//            (PqMdocConfig::device_signature false) runs beside it,
//            interleaved, as the arm <arm>-nodevice; at each count of
//            --unsound-no-mac-attrs (default none) each arm's MAC ablation
//            (PqMdocConfig::unsound_no_mac, unsound) likewise, as the arm
//            <arm>-nomac; and at each count of
//            --unsound-per-chunk-mac-attrs (default none) each arm's
//            per-chunk MAC ablation (PqMdocConfig::unsound_per_chunk_mac,
//            not zero-knowledge) likewise, as the arm <arm>-perchunk, which
//            also prints its GH_PER_CHUNK_MAC line (bench_hook.h). The
//            per-chunk arms take about 6 s (Goldilocks) and 17 s (F_q) to
//            prove at 1 attribute. Once per arm and count it prints GH_DOMAINS
//            profile=P arm=A attrs=N <domain>=<field> ...; per proof one
//            PQMDOC_RUN line with witness (the witness generation from the
//            instance: assemble, the private inputs' assignment from the
//            credential, plus the phase-0 generators), late (the later
//            phases' generators, inside prove; bench_hook.h's header), each
//            domain's commit, prove and bytes and, single-threaded, the
//            per-domain split of bench_hook.h's header (<domain>_prover,
//            <domain>_verify, shared_prover, shared_verify) of setup_p +
//            commit + prove and setup_v + verify. rep counts every round,
//            the warm-ups' first (rep < --warmups); the PQMDOC_MEDIAN and
//            PQMDOC_DOMAIN lines leave the warm-ups out. setup_p and setup_v are
//            the prover's and the verifier's prepares of the statement,
//            each afresh (bench_hook::fresh_prepare); verify_parse is the
//            verify call's proof parsing (VerifyTimes::parse), inside
//            verify. --hash-probe prints the PQ_HASH lines and makes no
//            proof.
//   export   the plan export (plan_export.h) and the realized program
//            (plan_program.h) of each arm of --arm (default fq,goldilocks)
//            at each count of --attrs (default 1), built as the bench
//            builds them, in --dir:
//            GordieHowe/Generated/MDL/{MLDSA44,MLDSA44Fq}/Attrs<n>/
//            <parameter set>/{Plan,Program}.lean (config pq-mdoc-<arm>-<n>,
//            as the bench's PQ_HASH line). A system the exporters do not
//            cover prints one GH_EXPORT_UNSUPPORTED line with the exporter's
//            reason (the plan stays when only the program fails) and the
//            others are still exported.

#include <algorithm>
#include <cstdio>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc_fixture.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::pq_mdoc {
namespace {

using bench::Clock;
using bench::ms_since;

std::vector<size_t> counts(const bench::Flags &f, const char *name) {
  std::vector<size_t> out;
  for (const std::string &s : f.list(name)) out.push_back(std::stoul(s));
  return out;
}

void add_config_flags(bench::Flags &f) {
  f.flag("bit-checks", "auto", "A's Boolean checks: auto (the placement "
                               "rule), circuit or batch")
      .toggle("unpacked-s0", "H commits its GF(2^16) words unpacked "
                             "(DomainProfile::unpacked_s0)")
      .toggle("a-unpacked-s0", "A commits its F_q coordinates unpacked "
                               "(PqMdocConfig::a_unpacked_s0)");
}

// The bench's configuration of ARM at N attributes in profile ID, from the
// flags.
PqMdocConfig bench_config(const bench::Flags &f, const char *id,
                          const std::string &arm, size_t n) {
  PqMdocConfig cfg;
  const std::string where = f.str("bit-checks");
  if (where == "circuit") {
    cfg.bit_checks = Placement::kCircuit;
  } else if (where == "batch") {
    cfg.bit_checks = Placement::kBatch;
  } else if (where != "auto") {
    throw bench::UsageError("unknown --bit-checks " + where);
  }
  cfg.h_unpacked_s0 = f.on("unpacked-s0");
  cfg.a_unpacked_s0 = f.on("a-unpacked-s0");
  std::printf("PQMDOC_CONFIG profile=%s arm=%s attrs=%zu bit_checks=%s "
              "h_unpacked_s0=%d a_unpacked_s0=%d\n",
              id, arm.c_str(), n, where.c_str(), int(cfg.h_unpacked_s0),
              int(cfg.a_unpacked_s0));
  return cfg;
}

// One arm's bench at N attributes: built and compiled once, then one proof
// and its verification per rep() (the caller interleaves the arms), and
// the medians at finish().
struct ArmBench {
  // The leading rounds left out of the medians.
  size_t warmups = 0;
  virtual ~ArmBench() = default;
  virtual void rep(size_t r) = 0;
  virtual void finish() = 0;
  virtual bool ok() const = 0;
};
template <class P, class Arm>
struct ArmBenchImpl final : ArmBench {
  using S = PqMdocSystem<P, Arm>;
  size_t n;
  // The arm's name, with -nodevice under the device-signature ablation,
  // -nomac under the MAC ablation and -perchunk under the per-chunk MAC
  // ablation.
  std::string label;
  Built<P, Arm> b;
  typename S::Assignment st;
  // The private inputs' assignment from the instance, made per proof.
  std::function<typename S::Assignment()> assign;
  SecureRandomEngine rng;
  std::vector<double> wt, sp, cm, pr, cp, ptot, sv, vf, vtot, bytes;
  std::vector<std::vector<double>> dc, dp, dv, db;

  // MODES: the threading modes of each round; REPORT: print the compile
  // report.
  std::vector<bench_hook::Mode> modes;
  bool all_ok = true;

  ArmBenchImpl(size_t n_attr, const PqMdocConfig &cfg,
               std::vector<bench_hook::Mode> modes_, bool report)
      : n(n_attr),
        label(std::string(arm_name<Arm>()) +
              (cfg.device_signature ? "" : "-nodevice") +
              (cfg.unsound_no_mac ? "-nomac" : "") +
              (cfg.unsound_per_chunk_mac ? "-perchunk" : "")),
        modes(std::move(modes_)) {
    const Instance x = bench_instance(n);
    auto t0 = Clock::now();
    b = build<P, Arm>(env<P, Arm>(), n, x.statement.device_tbs.size(), cfg);
    std::printf("PQMDOC_BUILD profile=%s arm=%s attrs=%zu build+compile=%.1f\n",
                P::kId, label.c_str(), n, ms_since(t0));
    bench_hook::print_hash<typename S::Sys::Set::Hash>(
        "pq-mdoc-" + label + "-" + std::to_string(n),
        P::kId);
    const auto &c = *b.c;
    if (report)
      std::printf("%s\n", c.report().c_str());
    const size_t nd = c.num_domains();
    for (size_t d = 0; d < nd; ++d)
      std::printf("PQMDOC_PLAN profile=%s arm=%s attrs=%zu domain=%s %s\n",
                  P::kId, label.c_str(), n, c.domain(d).name.c_str(),
                  plan_line(c, d).c_str());
    std::printf("GH_DOMAINS profile=%s arm=%s attrs=%zu%s\n", P::kId,
                label.c_str(), n, bench_hook::domain_fields(c).c_str());
    bench_hook::print_per_chunk_macs(
        c.report(), "pq-mdoc-" + label + "-" + std::to_string(n), P::kId);
    std::fflush(stdout);
    st = b.sys->statement(x.statement);
    assign = [this, x] { return b.sys->witness(x.data); };
    dc.resize(nd);
    dp.resize(nd);
    dv.resize(nd);
    db.resize(nd);
  }

  // One round: a proof per threading mode (bench_hook::modes), back to
  // back, both from the bench's SecureRandomEngine; the medians are
  // single-threaded.
  void rep(size_t r) override {
    for (const auto &mode : modes) {
      bench_hook::enter(mode);
      one(r, mode);
    }
  }
  void one(size_t r, const bench_hook::Mode &mode) {
    const auto &c = *b.c;
    const size_t nd = c.num_domains();
    ProveTimes times;
    std::vector<size_t> dbytes;
    std::vector<uint8_t> proof;
    double setup_p = 0;
    const auto ta = Clock::now();
    const typename S::Assignment wit = assign();
    const double assemble = ms_since(ta);
    {
      const auto prep = bench_hook::fresh_prepare(c, st, setup_p);
      typename S::Sys::ProveOptions opt;
      opt.times = &times;
      opt.domain_bytes = &dbytes;
      opt.multithreaded = mode.multi;
      proof = prep.prove(wit, rng, opt);
    }
    VerifyTimes vt;
    double setup_v = 0, verify = 0;
    bool ok = false;
    {
      const auto prep = bench_hook::fresh_prepare(c, st, setup_v);
      const auto t2 = Clock::now();
      ok = prep.verify(proof, &vt, mode.multi);
      verify = ms_since(t2);
    }
    all_ok = all_ok && ok;
    std::printf("PQMDOC_RUN profile=%s arm=%s attrs=%zu rep=%zu mode=%s "
                "witness=%.3f assemble=%.3f late=%.3f setup_p=%.3f "
                "commit=%.3f prove=%.3f setup_v=%.3f verify=%.3f "
                "verify_parse=%.3f bytes=%zu",
                P::kId, label.c_str(), n, r, mode.name(),
                assemble + times.witness, assemble, times.late, setup_p,
                times.commit, times.prove, setup_v, verify, vt.parse,
                proof.size());
    for (size_t d = 0; d < nd; ++d)
      std::printf(" %s_commit=%.3f %s_prove=%.3f %s_bytes=%zu",
                  c.domain(d).name.c_str(), times.domain_commit[d],
                  c.domain(d).name.c_str(), times.domain_prove[d],
                  c.domain(d).name.c_str(), dbytes[d]);
    // Single-threaded, the per-domain split (bench_hook.h's header) of the
    // reported prover (setup_p + commit + prove) and verifier (setup_v +
    // verify) times.
    if (!mode.multi)
      std::printf("%s", bench_hook::domain_split(
                            c, times, vt,
                            setup_p + times.commit + times.prove,
                            setup_v + verify)
                            .c_str());
    std::printf(" ok=%d\n", int(ok));
    std::fflush(stdout);
    if (mode.multi || r < warmups) return;
    wt.push_back(assemble + times.witness);
    sp.push_back(setup_p);
    cm.push_back(times.commit);
    pr.push_back(times.prove);
    cp.push_back(times.commit + times.prove);
    ptot.push_back(setup_p + times.commit + times.prove);
    sv.push_back(setup_v);
    vf.push_back(verify);
    vtot.push_back(setup_v + verify);
    bytes.push_back(double(proof.size()));
    for (size_t d = 0; d < nd; ++d) {
      dc[d].push_back(times.domain_commit[d]);
      dp[d].push_back(times.domain_prove[d]);
      dv[d].push_back(vt.domain[d]);
      db[d].push_back(double(dbytes[d]));
    }
  }

  bool ok() const override { return all_ok; }

  void finish() override {
    const auto &c = *b.c;
    std::printf("PQMDOC_MEDIAN profile=%s arm=%s attrs=%zu n=%zu witness=%.3f "
                "setup_p=%.3f commit=%.3f prove=%.3f commit+prove=%.3f "
                "prover_total=%.3f setup_v=%.3f verify=%.3f verify_total=%.3f "
                "bytes=%.0f\n",
                P::kId, label.c_str(), n, wt.size(), bench::median(wt), bench::median(sp),
                bench::median(cm), bench::median(pr), bench::median(cp), bench::median(ptot), bench::median(sv),
                bench::median(vf), bench::median(vtot), bench::median(bytes));
    for (size_t d = 0; d < c.num_domains(); ++d)
      std::printf("PQMDOC_DOMAIN profile=%s arm=%s attrs=%zu domain=%s "
                  "commit=%.3f prove=%.3f verify=%.3f bytes=%.0f\n",
                  P::kId, label.c_str(), n, c.domain(d).name.c_str(),
                  bench::median(dc[d]), bench::median(dp[d]), bench::median(dv[d]), bench::median(db[d]));
    std::fflush(stdout);
  }
};


int bench_arms(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  const size_t warmups = f.num("warmups");
  const std::vector<size_t> attrs = counts(f, "attrs");
  const std::vector<std::string> arms = f.list("arm");
  for (const std::string &arm : arms)
    if (arm != "fq" && arm != "goldilocks")
      throw bench::UsageError("unknown arm " + arm);
  const std::vector<size_t> nodevice = counts(f, "nodevice-attrs");
  const std::vector<size_t> nomac = counts(f, "unsound-no-mac-attrs");
  const std::vector<size_t> perchunk =
      counts(f, "unsound-per-chunk-mac-attrs");
  const auto modes = bench_hook::modes(f);
  const bool report = f.on("print-report");
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    for (size_t n : attrs) {
      std::vector<std::unique_ptr<ArmBench>> runs;
      const bool ablate =
          std::find(nodevice.begin(), nodevice.end(), n) != nodevice.end();
      const bool ablate_mac =
          std::find(nomac.begin(), nomac.end(), n) != nomac.end();
      const bool ablate_per_chunk =
          std::find(perchunk.begin(), perchunk.end(), n) != perchunk.end();
      for (const std::string &arm : arms) {
        PqMdocConfig cfg = bench_config(f, P::kId, arm, n);
        // The full system, then its ablations when requested: without
        // the device signature, without the MAC, and with Longfellow's
        // per-chunk MAC.
        for (const int variant : {0, 1, 2, 3}) {
          if ((variant == 1 && !ablate) || (variant == 2 && !ablate_mac) ||
              (variant == 3 && !ablate_per_chunk))
            continue;
          cfg.device_signature = variant != 1;
          cfg.unsound_no_mac = variant == 2;
          cfg.unsound_per_chunk_mac = variant == 3;
          if (arm == "fq")
            runs.push_back(std::make_unique<ArmBenchImpl<P, FqArm>>(
                n, cfg, modes, report));
          else
            runs.push_back(std::make_unique<ArmBenchImpl<P, GoldilocksArm>>(
                n, cfg, modes, report));
        }
      }
      // --hash-probe: the PQ_HASH lines only.
      if (f.on("hash-probe")) continue;
      // The arms interleaved: one proof of each per round, the warm-ups
      // first.
      for (auto &run : runs) run->warmups = warmups;
      for (size_t r = 0; r < warmups + reps; ++r)
        for (auto &run : runs) run->rep(r);
      for (auto &run : runs) {
        run->finish();
        ok = ok && run->ok();
      }
    }
  });
  return ok ? 0 : 1;
}

// ARM's system at N attributes, built as the bench builds it, exported to
// DIR. Returns the plan's path; a failed program check clears OK.
template <class P, class Arm>
std::string export_arm(const std::string &dir, size_t n,
                       const PqMdocConfig &cfg, const std::string &commit,
                       const std::string &run_id, bool *ok) {
  const Instance x = bench_instance(n);
  const Built<P, Arm> b =
      build<P, Arm>(env<P, Arm>(), n, x.statement.device_tbs.size(), cfg);
  // The statement has no fixed message: msgLen is 0.
  const compiler::ExportMeta meta{std::string("pq-mdoc-") + arm_name<Arm>() +
                                      "-" + std::to_string(n),
                                  P::kId, commit, run_id, 0};
  const std::string path = write_plan(*b.c, dir, meta);
  // The program's checks (no ProgramExport test: the system's compile is
  // the export's), as GH_EXPORT_ERROR lines.
  for (const std::string &e :
       program_problems(compiler::build_program(*b.c, meta))) {
    std::printf("GH_EXPORT_ERROR config=%s profile=%s what=%s\n",
                meta.config.c_str(), P::kId, e.c_str());
    *ok = false;
  }
  return path;
}


int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = bench_hook::export_dir(f);
  const std::vector<size_t> attrs = counts(f, "attrs");
  const std::vector<std::string> arms = f.list("arm");
  for (const std::string &arm : arms)
    if (arm != "fq" && arm != "goldilocks")
      throw bench::UsageError("unknown arm " + arm);
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    for (size_t n : attrs)
      for (const std::string &arm : arms) {
        const PqMdocConfig cfg = bench_config(f, P::kId, arm, n);
        try {
          const std::string path =
              arm == "fq"
                  ? export_arm<P, FqArm>(dir, n, cfg, f.str("commit"),
                                         f.str("run-id"), &ok)
                  : export_arm<P, GoldilocksArm>(dir, n, cfg, f.str("commit"),
                                                 f.str("run-id"), &ok);
          std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId,
                      path.c_str());
        } catch (const std::exception &e) {
          std::printf("GH_EXPORT_UNSUPPORTED config=pq-mdoc-%s-%zu profile=%s "
                      "what=%s\n",
                      arm.c_str(), n, P::kId, e.what());
        }
      }
  });
  return ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::pq_mdoc

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::pq_mdoc;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "Post-quantum mdoc's benches.",
      {{"bench", "the arms interleaved at each attribute count, medians",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          hook::add_mode_flags(f);
          app::add_config_flags(f);
          f.flag("warmups", "2", "the warm-up rounds first, outside the "
                                 "medians")
              .flag("reps", "9", "the measured rounds after the warm-ups")
              .flag("attrs", "1,2,4", "the attribute counts")
              .flag("arm", "fq", "the arms, comma-separated: fq, goldilocks")
              .flag("nodevice-attrs", "", "the counts at which each arm's "
                                          "device-signature ablation runs")
              .flag("unsound-no-mac-attrs", "",
                    "the counts at which each arm's MAC ablation (unsound) "
                    "runs")
              .flag("unsound-per-chunk-mac-attrs", "",
                    "the counts at which each arm's per-chunk MAC ablation "
                    "(not zero-knowledge) runs")
              .toggle("print-report", "print each compile report")
              .toggle("hash-probe", "print the PQ_HASH lines and prove "
                                    "nothing");
        },
        app::bench_arms},
       {"export", "the arms' plan exports and realized programs",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_config_flags(f);
          f.flag("attrs", "1", "the attribute counts")
              .flag("arm", "fq,goldilocks", "the arms, comma-separated");
        },
        app::export_plans}});
}
