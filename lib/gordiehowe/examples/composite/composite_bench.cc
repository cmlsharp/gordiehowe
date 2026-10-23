// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The composite signature's bench executable (composite.h):
// composite_bench COMMAND [FLAG...].
//   bench    the composite and the two proofs of possession on one instance
//            (a 32-byte message, the empty context), --warmups warm-up
//            rounds (default 2) and then --reps measured rounds (default
//            9), each round one proof of each system per threading mode,
//            the order rotated per round; prints every run (r counts every
//            round, the warm-ups' first) and the single-threaded medians
//            of the measured rounds. --hash-probe prints the PQ_HASH lines and proves
//            nothing.
//   export   the plan and the realized program (plan_export.h,
//            plan_program.h) of the composite on the bench's instance:
//            GordieHowe/Generated/Composite/<ROMParams|QROMParams>/
//            {Plan,Program}.lean in --dir, the program checked
//            (program_testing.h's program_problems).

#include <cstdio>
#include <map>
#include <string>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/composite/composite_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::composite {
namespace {

using bench::Clock;
using bench::ms_since;

// One proof: setup_p and setup_v = the prover's and the verifier's
// prepares of the statement, each afresh (bench_hook::fresh_prepare),
// prover = setup_p + commit + prove (ProveTimes), witness = the witness
// generation from the instance (assemble, the private inputs' assignment
// from the instance, plus the phase-0 generators), late = the later
// phases' generators (inside prove; bench_hook.h's header), verify =
// setup_v + the verify() call, parse = that call's proof
// parsing (VerifyTimes::parse), the proof's bytes; DOMAINS, each domain's
// section (" <domain>_bytes=N") and,
// single-threaded, the per-domain split of bench_hook.h's header of prover
// and verify.
struct Timing {
  double witness = 0, assemble = 0, late = 0, setup_p = 0, prover = 0,
         setup_v = 0, verify = 0, parse = 0, bytes = 0;
  bool ok = false;
  std::string domains;
};

// A system's statement assignment; its witness assignment is made per
// proof, timed (Timing::assemble).
template <class S>
struct Prepared {
  const S &s;
  typename S::Sys::Assignment statement;
  explicit Prepared(const S &sys)
      : s(sys), statement(sys.typed().statement(sys.statement())) {}
  Timing run(RandomEngine &rng, bool multi,
             std::vector<uint8_t> *proof_out) const {
    const auto &c = s.typed().compiled();
    Timing r;
    const auto ta = Clock::now();
    const typename S::Sys::Assignment witness =
        s.typed().witness(s.witness());
    r.assemble = ms_since(ta);
    ProveTimes pt;
    VerifyTimes vt;
    std::vector<size_t> sections;
    typename S::Sys::ProveOptions opt;
    opt.times = &pt;
    opt.domain_bytes = &sections;
    opt.multithreaded = multi;
    std::vector<uint8_t> proof;
    {
      const auto prep = bench_hook::fresh_prepare(c, statement, r.setup_p);
      proof = prep.prove(witness, rng, opt);
    }
    *proof_out = proof;
    {
      const auto prep = bench_hook::fresh_prepare(c, statement, r.setup_v);
      const auto t0 = Clock::now();
      r.ok = prep.verify(proof, &vt, multi);
      r.verify = r.setup_v + ms_since(t0);
    }
    r.parse = vt.parse;
    r.witness = r.assemble + pt.witness;
    r.late = pt.late;
    r.prover = r.setup_p + pt.commit + pt.prove;
    r.bytes = double(proof.size());
    for (size_t d = 0; d < sections.size(); ++d)
      r.domains += " " + c.domain(d).name + "_bytes=" +
                   std::to_string(sections[d]);
    if (!multi)
      r.domains += bench_hook::domain_split(c, pt, vt, r.prover, r.verify);
    return r;
  }
};

// The composite and the two proofs of possession (see the header).
int bench_systems(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  const size_t warmups = f.num("warmups");
  const auto modes = bench_hook::modes(f);
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const support::Instance x = support::instance(32, {});
    const Env<P> env;
    auto t0 = Clock::now();
    const support::CompositeSystem<P> cs(env, x);
    const double c_compile = ms_since(t0);
    t0 = Clock::now();
    const support::EcdsaSystem<P> es(env, x);
    const double e_compile = ms_since(t0);
    t0 = Clock::now();
    const support::MldsaSystem<P> ms(env, x);
    const double m_compile = ms_since(t0);
    const char *names[3] = {"composite", "ecdsa", "mldsa"};
    const Prepared<support::CompositeSystem<P>> c(cs);
    const Prepared<support::EcdsaSystem<P>> e(es);
    const Prepared<support::MldsaSystem<P>> m(ms);
    const double compiles[3] = {c_compile, e_compile, m_compile};
    // --print-report: each system's compile report.
    if (f.on("print-report")) {
      const std::string reports[3] = {cs.typed().compiled().report(),
                                      es.typed().compiled().report(),
                                      ms.typed().compiled().report()};
      for (size_t k = 0; k < 3; ++k)
        std::printf("GH_COMPOSITE_REPORT system=%s\n%s\n", names[k],
                    reports[k].c_str());
    }
    for (size_t k = 0; k < 3; ++k)
      std::printf("GH_COMPOSITE_SETUP profile=%s system=%s compile=%.1f\n",
                  P::kId, names[k], compiles[k]);
    std::printf("GH_DOMAINS profile=%s system=%s%s\n", P::kId, names[0],
                bench_hook::domain_fields(cs.typed().compiled()).c_str());
    std::printf("GH_DOMAINS profile=%s system=%s%s\n", P::kId, names[1],
                bench_hook::domain_fields(es.typed().compiled()).c_str());
    std::printf("GH_DOMAINS profile=%s system=%s%s\n", P::kId, names[2],
                bench_hook::domain_fields(ms.typed().compiled()).c_str());
    bench_hook::print_hash<
        typename support::CompositeSystem<P>::Sys::Set::Hash>(
        "composite", P::kId);
    bench_hook::print_hash<typename support::EcdsaSystem<P>::Sys::Set::Hash>(
        "composite-ecdsa", P::kId);
    bench_hook::print_hash<typename support::MldsaSystem<P>::Sys::Set::Hash>(
        "composite-mldsa", P::kId);
    // --hash-probe: the PQ_HASH lines only.
    if (f.on("hash-probe")) return;
    SecureRandomEngine rng;
    std::map<std::string, std::vector<Timing>> runs;
    // Each proof once per threading mode (bench_hook::modes), back to back,
    // both from RNG; the medians below are single-threaded.
    for (size_t r = 0; r < warmups + reps; ++r)
      for (size_t j = 0; j < 3; ++j) {
        const size_t k = (r + j) % 3;
        for (const auto &mode : modes) {
          bench_hook::enter(mode);
          std::vector<uint8_t> proof;
          const Timing t = k == 0   ? c.run(rng, mode.multi, &proof)
                           : k == 1 ? e.run(rng, mode.multi, &proof)
                                    : m.run(rng, mode.multi, &proof);
          ok = ok && t.ok;
          std::printf("GH_COMPOSITE_RUN profile=%s system=%s r=%zu mode=%s "
                      "witness=%.3f assemble=%.3f late=%.3f setup_p=%.3f "
                      "prover=%.3f setup_v=%.3f verify=%.3f "
                      "verify_parse=%.3f bytes=%.0f%s ok=%d\n",
                      P::kId, names[k], r, mode.name(), t.witness,
                      t.assemble, t.late, t.setup_p,
                      t.prover, t.setup_v, t.verify, t.parse, t.bytes,
                      t.domains.c_str(), int(t.ok));
          std::fflush(stdout);
          if (!mode.multi && r >= warmups) runs[names[k]].push_back(t);
        }
      }
    auto med = [&](const std::string &n, double Timing::*f) {
      std::vector<double> v;
      for (const auto &t : runs[n]) v.push_back(t.*f);
      return bench::median(v);
    };
    for (const char *n : names)
      std::printf("GH_COMPOSITE_MEDIAN profile=%s system=%s n=%zu "
                  "setup_p=%.3f prover=%.3f setup_v=%.3f verify=%.3f "
                  "bytes=%.0f\n",
                  P::kId, n, runs[n].size(), med(n, &Timing::setup_p),
                  med(n, &Timing::prover), med(n, &Timing::setup_v),
                  med(n, &Timing::verify), med(n, &Timing::bytes));
  });
  return ok ? 0 : 1;
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = bench_hook::export_dir(f);
  bool ok = true;
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    const support::Instance x = support::instance(32, {});
    const Env<P> env;
    const support::CompositeSystem<P> s(env, x);
    const auto &c = s.typed().compiled();
    const compiler::ExportMeta meta{"composite", P::kId, f.str("commit"),
                                    f.str("run-id"), x.msg.size(),
                                    x.ctx.size()};
    const std::string path = write_plan(c, dir, meta);
    for (const std::string &e :
         program_problems(compiler::build_program(c, meta))) {
      std::printf("GH_EXPORT_ERROR config=composite profile=%s what=%s\n",
                  P::kId, e.c_str());
      ok = false;
    }
    std::printf("GH_EXPORT_PLAN profile=%s path=%s program=%s\n", P::kId,
                path.c_str(), compiler::lean_program_file(dir, meta).c_str());
  });
  return ok ? 0 : 1;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::composite

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::composite;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The composite signature's benches.",
      {{"bench", "the composite and both proofs of possession, interleaved",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          hook::add_mode_flags(f);
          f.flag("warmups", "2", "the warm-up rounds first, outside the "
                                 "medians")
              .flag("reps", "9", "the measured rounds after the warm-ups")
              .toggle("print-report", "print each system's compile report")
              .toggle("hash-probe", "print the PQ_HASH lines and prove "
                                    "nothing");
        },
        app::bench_systems},
       {"export", "the composite's plan export and realized program",
        hook::add_export_flags, app::export_plans}});
}
