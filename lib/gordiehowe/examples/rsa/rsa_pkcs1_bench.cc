// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The RSA PKCS#1 v1.5 proof of possession's bench executable
// (rsa_pkcs1.h): rsa_pkcs1_bench COMMAND [FLAG...].
//   bench      every configuration of the flags' lists, compiled once,
//              then --warmups warm-up rounds (default 2, each printed as
//              r = 0) and --reps repetitions (default 9), interleaved (one proof of each
//              configuration per round), in the profile --profile names
//              (wide, narrow or narrow-fp128), or each in its own profile
//              when --configs names one: configurations of several
//              profiles then interleave in one process. --hash-probe
//              compiles and prints the plans only (the PQ_HASH lines
//              among them).
//   export     the plan export (plan_export.h) and the realized program
//              (plan_program.h) of every configuration of the same lists,
//              in --dir: GordieHowe/Generated/RSA2048/<Goldilocks2|Fp128>/
//              Msg<size>/ROMParams/{Plan,Program}.lean (lean_config_name),
//              config rsa-<key>, as its PQ_HASH line. A configuration the
//              exporters do not cover prints one GH_EXPORT_UNSUPPORTED line
//              with the exporter's reason (the plan stays when only the
//              program fails) and the others are still exported.
//   field-ops  the field operations' cost: ns per mul and add over arrays
//              and per dependent product, in Fp128, Goldilocks^2 (and its
//              base field) and GF(2^128)
//
// The configurations: --configs variant:t:msg:batched[:m[:profile]],...,
// or the product of --variants (auto is the compiler's choice, direct and
// batch pin conv), --t (digit widths), --m (digits per limb) and --msg
// (maximum message bytes, each proof at the maximum); SHA-256 is batched.
//
// Per configuration the bench prints the compile report, one GH_RSA_PLAN
// line per domain, one GH_DOMAINS cfg=K profile=P <domain>=<field> ...
// line, and per proof one GH_RSA_RUN line: prover = commit + prove, verify,
// witness (the witness generation from the instance: assemble, the private
// inputs' assignment from the message and signature, plus the phase-0
// generators), late (the later phases' generators, inside prove;
// bench_hook.h's header), the proof bytes and each domain's section
// (<domain>_bytes), and, single-threaded, the per-domain split of
// bench_hook.h's header (<domain>_prover, <domain>_verify, shared_prover,
// shared_verify; the domains' terms plus the shared term are prover and
// verify). Each proof prepares the statement afresh for the prover and for
// the verifier (bench_hook::fresh_prepare), setup_p and setup_v: commit is
// setup_p plus ProveTimes::commit, and verify is setup_v plus the verify()
// call, whose proof parsing verify_parse gives (VerifyTimes::parse).

#include <algorithm>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1_testing.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/instances.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"
#include "util/prover_profile.h"

namespace proofs::gordiehowe::examples::rsa {
namespace {

using bench::Clock;
using bench::ms_since;

void add_config_flags(bench::Flags &f) {
  f.flag("configs", "", "variant:t:msg:batched[:m[:profile]],... in place of "
                        "the lists' product")
      .flag("variants", "auto,direct,batch", "the multiplication variants")
      .flag("t", "10", "the digit widths")
      .flag("m", "1", "the digits per limb")
      .flag("msg", "64,2048", "the maximum message bytes");
}

// The configuration's key, prefixed fp128_ in narrow-fp128 (PID).
std::string config_key(const RsaConfig &c, const std::string &pid) {
  std::string v = conv_realization_name(c.mul);
  for (auto &ch : v)
    if (ch == '-') ch = '_';
  const std::string pre = pid == param_sets::ROMParamsFp128::kId ? "fp128_" : "";
  return pre + v + "_t" + std::to_string(c.t) +
         (c.m > 1 ? "_m" + std::to_string(c.m) : std::string()) + "_" +
         std::to_string(c.max_bytes) + "_batched";
}

struct Bench {
  virtual ~Bench() = default;
  virtual void run(size_t r) = 0;
  virtual bool ok() const = 0;
};

template <class P>
struct BenchImpl : Bench {
  using T = RsaSystem<P>;
  RsaConfig cfg;
  std::string key;
  Env<P> env;
  std::vector<uint8_t> msg;
  std::unique_ptr<T> t;
  std::shared_ptr<const typename T::Compiled> c;
  typename T::Sys::Assignment statement;
  SecureRandomEngine rng;

  // MODES: the threading modes of each round.
  std::vector<bench_hook::Mode> modes;
  bool all_ok = true;

  BenchImpl(const RsaConfig &k, std::vector<bench_hook::Mode> modes_)
      : cfg(k), key(config_key(k, P::kId)), modes(std::move(modes_)) {
    msg = message(cfg.max_bytes);
    auto t0 = Clock::now();
    t = std::make_unique<T>(env, cfg);
    // The relation lowers and compiles once, inside the construction.
    const double compile_ms =
        t->rel.template typed<typename T::Sys>().compile_ms();
    const double build = ms_since(t0) - compile_ms;
    // The shape at the carry group the compiler accepted.
    const RsaShape sh = t->shape(env);
    std::printf("GH_RSA_CONFIG cfg=%s profile=%s variant=%s t=%zu m=%zu w=%zu "
                "msg=%zu sha=batched L=%zu Lq=%zu K=%zu M=%zu k=%zu G=%zu "
                "W=%s shift=%s\n",
                key.c_str(), P::kId, conv_realization_name(cfg.mul), cfg.t,
                sh.m, sh.w,
                cfg.max_bytes, sh.L, sh.Lq, sh.K, sh.M, sh.k, sh.G, bound_str(sh.W).c_str(),
                bound_str(sh.shift).c_str());
    c = t->compile();
    statement = t->statement(vectors::kN);
    t0 = Clock::now();
    const auto prep = c->prepare(statement);
    const double prepare = ms_since(t0);
    std::printf("GH_RSA_REPORT_BEGIN cfg=%s profile=%s\n%sGH_RSA_REPORT_END\n",
                key.c_str(), P::kId, c->report().c_str());
    std::printf("GH_RSA_ONCE cfg=%s profile=%s build=%.3f compile=%.3f "
                "prepare=%.3f\n",
                key.c_str(), P::kId, build, compile_ms, prepare);
    bench_hook::print_hash<typename T::Sys::Set::Hash>("rsa-" + key, P::kId);
    for (size_t d = 0; d < c->num_domains(); ++d) {
      const DomainPlan p = c->compiled_domain(d).plan();
      std::printf("GH_RSA_PLAN cfg=%s profile=%s domain=%s N=%zu k=%zu "
                  "t=%zu nrow=%zu nw=%zu nq=%zu block_enc=%zu ninputs=%zu "
                  "public=%zu committed=%zu layers=%zu wires=%zu "
                  "quad_terms=%zu batches=%zu list_radius=%d\n",
                  key.c_str(), P::kId, c->domain(d).name.c_str(), p.N, p.k,
                  p.t, p.nrow, p.nw, p.nq, p.block_enc, p.ninputs, p.npub,
                  p.ninputs - p.npub, p.layers, p.wires, p.quad_terms,
                  p.batches.size(), int(p.list_radius));
      for (const auto &b : p.batches)
        std::printf("GH_RSA_BATCH cfg=%s profile=%s domain=%s name=%s "
                    "instances=%zu arity=%zu degree=%zu width=%zu rounds=%zu\n",
                    key.c_str(), P::kId, c->domain(d).name.c_str(),
                    b.name.c_str(), b.instances, b.arity, b.degree, b.width,
                    b.rounds);
    }
    std::printf("GH_DOMAINS cfg=%s profile=%s%s\n", key.c_str(), P::kId,
                bench_hook::domain_fields(*c).c_str());
    std::fflush(stdout);
  }

  bool ok() const override { return all_ok; }

  // One round: a proof per threading mode (bench_hook::modes), back to
  // back, both from the bench's SecureRandomEngine.
  void run(size_t r) override {
    for (const auto &mode : modes) {
      bench_hook::enter(mode);
      one(r, mode);
    }
  }
  void one(size_t r, const bench_hook::Mode &mode) {
    const auto ta = Clock::now();
    const auto w = t->witness(msg, signature(cfg.max_bytes));
    const double assemble = ms_since(ta);
    ProveTimes pt;
    std::vector<size_t> sections;
    typename T::Sys::ProveOptions opt;
    opt.times = &pt;
    opt.domain_bytes = &sections;
    opt.multithreaded = mode.multi;
    // With --diagnostics profile, one PQ_PHASE line per proof and per verification:
    // the phase timers of util/prover_profile.h (bin.* in H, odd.* in A).
    std::vector<uint8_t> proof;
    double setup_p = 0, setup_v = 0;
    {
      const auto prep = bench_hook::fresh_prepare(*c, statement, setup_p);
      profiling::Session ps("gh_prove", key.c_str(), r, 0);
      proof = prep.prove(w, rng, opt);
    }
    VerifyTimes vt;
    bool ok = false;
    double verify = 0;
    {
      const auto prep = bench_hook::fresh_prepare(*c, statement, setup_v);
      profiling::Session vs("gh_verify", key.c_str(), r, 0);
      const auto t0 = Clock::now();
      ok = prep.verify(proof, &vt, mode.multi);
      verify = setup_v + ms_since(t0);
    }
    const double commit = setup_p + pt.commit;
    std::printf("GH_RSA_RUN cfg=%s profile=%s r=%zu mode=%s prover=%.3f "
                "commit=%.3f prove=%.3f verify=%.3f setup_p=%.3f "
                "setup_v=%.3f verify_parse=%.3f witness=%.3f assemble=%.3f "
                "late=%.3f bytes=%zu",
                key.c_str(), P::kId, r, mode.name(), commit + pt.prove, commit,
                pt.prove, verify, setup_p, setup_v, vt.parse,
                assemble + pt.witness, assemble, pt.late, proof.size());
    for (size_t d = 0; d < sections.size(); ++d)
      std::printf(" %s_bytes=%zu", c->domain(d).name.c_str(), sections[d]);
    if (!mode.multi)
      std::printf("%s", bench_hook::domain_split(*c, pt, vt,
                                                 commit + pt.prove, verify)
                            .c_str());
    std::printf(" ok=%d\n", int(ok));
    std::fflush(stdout);
    all_ok = all_ok && ok;
  }
};

// The field operations' cost (N elements, REPS passes): ns per mul and add over arrays
// (a_i = a_i b_i, independent products), and per dependent product
// (x = x b_i, latency), in Fp128, Goldilocks^2 (and its base field, the
// twiddles' and the subgroup encoder's) and GF(2^128). One RSA_FIELD line
// per field and operation.
template <class F>
void field_ops(const char *name, const F &f, size_t n, size_t reps) {
  using Elt = typename F::Elt;
  std::vector<Elt> a(n), b(n);
  for (size_t i = 0; i < n; ++i) {
    a[i] = f.of_scalar(uint64_t(3 * i + 1));
    b[i] = f.of_scalar(uint64_t(7 * i + 5));
  }
  auto ns = [&](auto body) {
    std::vector<double> v;
    for (int k = 0; k < 7; ++k) {
      const auto t0 = Clock::now();
      body();
      v.push_back(ms_since(t0) * 1e6 / double(n * reps));
    }
    std::sort(v.begin(), v.end());
    return v[3];
  };
  const double mul = ns([&] {
    for (size_t r = 0; r < reps; ++r)
      for (size_t i = 0; i < n; ++i) f.mul(a[i], b[i]);
  });
  const double add = ns([&] {
    for (size_t r = 0; r < reps; ++r)
      for (size_t i = 0; i < n; ++i) f.add(a[i], b[i]);
  });
  Elt x = f.one();
  const double chain = ns([&] {
    for (size_t r = 0; r < reps; ++r)
      for (size_t i = 0; i < n; ++i) f.mul(x, b[i]);
  });
  // Keep the results live.
  bool keep = x == f.zero();
  for (size_t i = 0; i < n; ++i) keep = keep || a[i] == f.zero();
  std::printf("RSA_FIELD field=%s bytes=%zu mul_ns=%.3f add_ns=%.3f "
              "mul_chain_ns=%.3f%s\n",
              name, size_t(F::kBytes), mul, add, chain, keep ? " (zero)" : "");
  std::fflush(stdout);
}


// The configurations of the flags as (variant, t, msg, sha, m, profile)
// tuples: --configs, or the lists' cross product; each tuple's profile its
// own, else PROFILE.
std::vector<std::vector<std::string>> config_tuples(const bench::Flags &f,
                                                    const std::string &profile) {
  std::vector<std::vector<std::string>> tuples;
  if (f.given("configs")) {
    for (const auto &x : f.list("configs")) {
      if (x.empty()) continue;
      std::stringstream xs(x);
      std::vector<std::string> v;
      for (std::string y; std::getline(xs, y, ':');) v.push_back(y);
      if (v.size() == 4) v.push_back("1");
      if (v.size() == 5) v.push_back("");
      if (v.size() != 6) throw bench::UsageError("--configs: " + x);
      tuples.push_back(v);
    }
  } else {
    for (const auto &v : f.list("variants"))
      for (const auto &t : f.list("t"))
        for (const auto &dm : f.list("m"))
          for (const auto &m : f.list("msg"))
            tuples.push_back({v, t, m, "batched", dm, ""});
  }
  for (auto &tu : tuples)
    if (tu[5].empty()) tu[5] = profile;
  for (const auto &tu : tuples)
    if (tu[5] != param_sets::QROMParams::kId &&
        tu[5] != param_sets::ROMParams::kId &&
        tu[5] != param_sets::ROMParamsFp128::kId)
      throw bench::UsageError("no profile " + tu[5]);
  return tuples;
}

// The configuration of tuple TU.
RsaConfig to_config(const std::vector<std::string> &tu) {
  RsaConfig c;
  const std::string &v = tu[0];
  if (v == "auto") {
    c.mul = ConvRealization::kAuto;
  } else if (v == "direct") {
    c.mul = ConvRealization::kDirect;
  } else if (v == "batch") {
    c.mul = ConvRealization::kBatch;
  } else {
    throw bench::UsageError("unknown variant " + v);
  }
  c.t = std::stoul(tu[1]);
  c.m = std::stoul(tu[4]);
  c.max_bytes = std::stoul(tu[2]);
  if (tu[3] != "batched")
    throw bench::UsageError("--configs: SHA-256 " + tu[3] + " (batched only)");
  return c;
}

int bench_configs(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t reps = f.num("reps");
  const auto tuples = config_tuples(f, profile);
  const auto modes = bench_hook::modes(f);
  std::vector<std::unique_ptr<Bench>> runs;
  auto add = [&](auto p) {
    using P = decltype(p);
    for (const auto &tu : tuples)
      if (tu[5] == P::kId)
        runs.push_back(std::make_unique<BenchImpl<P>>(to_config(tu), modes));
  };
  add(param_sets::QROMParams{});
  add(param_sets::ROMParams{});
  add(param_sets::ROMParamsFp128{});
  if (f.on("hash-probe")) return 0;
  // The warm-up rounds (r = 0), then the repetitions interleaved.
  const size_t warmups = f.num("warmups");
  for (size_t i = 0; i < warmups; ++i)
    for (auto &b : runs) b->run(0);
  for (size_t r = 1; r <= reps; ++r)
    for (auto &b : runs) b->run(r);
  bool ok = true;
  for (const auto &b : runs) ok = ok && b->ok();
  return ok ? 0 : 1;
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = bench_hook::export_dir(f);
  const auto tuples = config_tuples(f, profile);
  bool ok = true;
  auto one = [&](auto p) {
    using P = decltype(p);
    using T = RsaSystem<P>;
    for (const auto &tu : tuples) {
      if (tu[5] != P::kId) continue;
      const RsaConfig cfg = to_config(tu);
      const Env<P> env;
      const T t(env, cfg);
      const auto c = t.compile();
      // The message is private: msgLen is 0.
      const compiler::ExportMeta meta{"rsa-" + config_key(cfg, P::kId), P::kId,
                                      f.str("commit"), f.str("run-id"), 0};
      try {
        const std::string path = write_plan(*c, dir, meta);
        for (const std::string &e :
             program_problems(compiler::build_program(*c, meta))) {
          std::printf("GH_EXPORT_ERROR config=%s profile=%s what=%s\n",
                      meta.config.c_str(), P::kId, e.c_str());
          ok = false;
        }
        std::printf("GH_EXPORT_PLAN profile=%s path=%s program=%s\n", P::kId,
                    path.c_str(),
                    compiler::lean_program_file(dir, meta).c_str());
      } catch (const std::exception &e) {
        std::printf("GH_EXPORT_UNSUPPORTED config=%s profile=%s what=%s\n",
                    meta.config.c_str(), P::kId, e.what());
      }
    }
  };
  one(param_sets::QROMParams{});
  one(param_sets::ROMParams{});
  one(param_sets::ROMParamsFp128{});
  return ok ? 0 : 1;
}

int field_ops_command(const bench::Flags &f) {
  bench::apply_common_flags(f);
  const size_t n = f.num("n"), reps = f.num("reps");
  const Fp128<> fp128;
  const Fp64G2 gold2;
  const GF2_128<> gf128;
  field_ops("Fp128", fp128, n, reps);
  field_ops("Goldilocks^2", gold2, n, reps);
  field_ops("Goldilocks", gold2.base_field(), n, reps);
  field_ops("GF(2^128)", gf128, n, reps);
  return 0;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::rsa

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::rsa;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The RSA PKCS#1 v1.5 proof of possession's benches.",
      {{"bench", "the configurations interleaved",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          hook::add_mode_flags(f);
          app::add_config_flags(f);
          f.flag("reps", "9", "the repetitions")
              .flag("warmups", "2", "the warm-up rounds before them")
              .toggle("hash-probe", "compile and print the plans only");
        },
        app::bench_configs},
       {"export", "the configurations' plan exports and realized programs",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_config_flags(f);
        },
        app::export_plans},
       {"field-ops", "the field operations' cost",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("n", "4096", "the elements per array")
              .flag("reps", "2000", "the passes");
        },
        app::field_ops_command}});
}
