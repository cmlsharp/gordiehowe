// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon-512 rings' bench executable (falcon_ring.h):
// falcon_ring_bench COMMAND [FLAG...].
//   serve             a report_bench worker (bench_hook.h, bench/harness.h)
//                     of the arm --ring-arm at --ring-size members
//   bench             the same records and --reps proofs without
//                     report_bench
//   export            both arms' plan exports and realized programs at
//                     --ring-size members
//   report            the circuit figures per arm at each of --ring-sizes
//   witness-profile   the prover's witness time by node, both arms

#include <cstdio>
#include <map>
#include <regex>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "bench/bench_hook.h"
#include "bench/cli.h"
#include "bench/timing.h"
#include "gordiehowe/examples/rings/falcon_ring_fixture.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

namespace hook = examples::bench_hook;

void add_size_flag(bench::Flags &f) {
  f.flag("ring-size", "256", "the ring's members");
}
void add_ring_flags(bench::Flags &f) {
  add_size_flag(f);
  f.flag("ring-arm", "carrier", "the arm: carrier or native");
}

// The arm's system on its instance at --ring-size members, compiled, and
// handed to FN with its statement, witness and setup record.
template <class T, class I, class Fn>
void with_arm_system(const char *config, const char *profile, I in, Fn fn) {
  typename T::Env env;
  hook::Setup su{config, profile, in.R};
  auto t0 = hook::Clock::now();
  T t(env, in.R);
  su.build = hook::ms_since(t0) - hook::relation_compile_ms(t);
  su.compile = hook::relation_compile_ms(t);
  const auto c = t.compile();
  fn(*c, t.statement(in.ring, in.c),
     [&] { return t.witness(in.signer, in.h, in.s2); }, su);
}
template <class P, class Fn>
void with_system(const bench::Flags &f, Fn fn) {
  const size_t R = f.num("ring-size");
  const std::string arm = f.str("ring-arm");
  if (arm == "native")
    with_arm_system<FalconRingNativeSystem<P>>("falcon-ring-native", P::kId,
                                               native_instance<P>(R), fn);
  else if (arm == "carrier")
    with_arm_system<FalconRingCarrierSystem<P>>(
        "falcon-ring-carrier", P::kId, carrier_instance<P>(R), fn);
  else
    throw bench::UsageError("unknown ring arm " + arm);
}
auto systems(const bench::Flags &f) {
  return [&f](auto p, auto fn) { with_system<decltype(p)>(f, fn); };
}

int export_plans(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const std::string dir = hook::export_dir(f);
  const size_t R = f.num("ring-size");
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    for (const auto &path :
         {export_plan<P, FalconRingCarrierSystem<P>>(
              dir, "falcon-ring-carrier", f.str("commit"), f.str("run-id"),
              R),
          export_plan<P, FalconRingNativeSystem<P>>(
              dir, "falcon-ring-native", f.str("commit"), f.str("run-id"),
              R)})
      std::printf("GH_EXPORT_PLAN profile=%s path=%s\n", P::kId, path.c_str());
  });
  return 0;
}

// ------------------------------------------------------------ figures --

// A domain's circuit and Ligero figures, and its range needles, from the
// compile report.
struct Figures {
  size_t layers = 0, quad = 0, inputs = 0, publics = 0, committed = 0,
         nw = 0, needles = 0, groups = 0;
};
Figures figures(const std::string &r) {
  Figures f;
  std::smatch m;
  auto num = [&](const std::string &s, const char *re, size_t k = 1) {
    return std::regex_search(s, m, std::regex(re)) ? size_t(std::stoul(m[k]))
                                                   : size_t(0);
  };
  const std::string a = r.substr(r.find("domain A ("));
  f.inputs = num(a, R"(ninputs=(\d+))");
  f.publics = num(a, R"( public=(\d+))");
  f.committed = num(a, R"(committed=(\d+))");
  f.layers = num(a, R"(layers=(\d+))");
  f.quad = num(a, R"(quad_terms=(\d+))");
  f.nw = num(a, R"(nw=(\d+))");
  std::regex tab(R"(table A\.\d+(?:\.g\d+)?: (\d+) static)");
  for (auto it = std::sregex_iterator(r.begin(), r.end(), tab);
       it != std::sregex_iterator(); ++it)
    f.needles += std::stoul((*it)[1]);
  f.groups = num(r, R"((\d+) groups of at most)");
  if (f.groups == 0) f.groups = 1;
  return f;
}

// The figures of system T at R members; GROUP_CAPACITY (0: the profile's)
// overrides the range groups' capacity, PRINT prints the whole report.
template <class T>
void report_sizes(const char *arm, const char *profile, size_t R,
                  size_t group_capacity, bool print) {
  const typename T::Env env;
  T t(env, R);
  CompileProfile cp = T::compile_profile();
  if (group_capacity != 0) cp.range.group_capacity = group_capacity;
  const auto c = t.compile(cp);
  const std::string r = c->report();
  if (print) std::printf("%s", r.c_str());
  const Figures f = figures(r);
  std::printf("GH_RING_SIZE arm=%s profile=%s R=%zu layers=%zu quad=%zu "
              "inputs=%zu public=%zu committed=%zu nw=%zu needles=%zu "
              "groups=%zu\n",
              arm, profile, R, f.layers, f.quad, f.inputs, f.publics,
              f.committed, f.nw, f.needles, f.groups);
}

int report(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  std::vector<size_t> sizes;
  for (const std::string &s : f.list("ring-sizes")) sizes.push_back(std::stoul(s));
  const size_t capacity = f.num("group-capacity");
  const bool print = f.on("print-report");
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    for (size_t R : sizes) {
      report_sizes<FalconRingCarrierSystem<P>>("carrier", P::kId, R, capacity,
                                               print);
      report_sizes<FalconRingNativeSystem<P>>("native", P::kId, R, capacity,
                                              print);
    }
  });
  return 0;
}

// Where the prover's witness time goes: the time between consecutive
// generator hooks, by node, median over REPS proofs, with the statement's
// setup.
template <class T, class I>
void witness_profile(const char *arm, const char *profile, I instance,
                     size_t reps) {
  const Fixture<T, I> fx(std::move(instance));
  const auto prep = fx.c->prepare(fx.statement());
  std::printf("GH_RING_WITNESS arm=%s profile=%s setup %.3f ms\n", arm,
              profile, prep.setup_ms());
  SecureRandomEngine rng;
  std::map<size_t, std::vector<double>> per;
  std::vector<double> total;
  for (size_t r = 0; r < reps; ++r) {
    const auto w = fx.witness();
    std::vector<std::pair<size_t, hook::Clock::time_point>> at;
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
  std::printf("GH_RING_WITNESS arm=%s profile=%s median witness %.3f ms\n",
              arm, profile, bench::median(total));
  for (auto &[id, v] : per)
    std::printf("GH_RING_WITNESS %-34s %8.3f ms\n",
                fx.t.cs.graph().nodes[id].name.c_str(), bench::median(v));
}

int witness_profiles(const bench::Flags &f) {
  const std::string profile = bench::apply_common_flags(f);
  const size_t R = f.num("ring-size");
  const size_t reps = f.num("reps");
  param_sets::with_profile(profile, [&](auto p) {
    using P = decltype(p);
    witness_profile<FalconRingCarrierSystem<P>>("carrier", P::kId,
                                                carrier_instance<P>(R), reps);
    witness_profile<FalconRingNativeSystem<P>>("native", P::kId,
                                               native_instance<P>(R), reps);
  });
  return 0;
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring

int main(int argc, char **argv) {
  namespace app = proofs::gordiehowe::examples::falcon::ring;
  namespace hook = proofs::gordiehowe::examples::bench_hook;
  using proofs::bench::Flags;
  return proofs::bench::run_commands(
      argc, argv, "The Falcon-512 rings' benches.",
      {{"serve", "a report_bench worker",
        [](Flags &f) {
          hook::add_serve_flags(f);
          app::add_ring_flags(f);
        },
        [](const Flags &f) { return hook::serve_command(f, app::systems(f)); }},
       {"bench", "the worker's records and --reps proofs, alone",
        [](Flags &f) {
          hook::add_bench_flags(f);
          app::add_ring_flags(f);
        },
        [](const Flags &f) { return hook::bench_command(f, app::systems(f)); }},
       {"export", "both arms' plan exports and realized programs",
        [](Flags &f) {
          hook::add_export_flags(f);
          app::add_size_flag(f);
        },
        app::export_plans},
       {"report", "the circuit figures per arm and ring size",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          f.flag("ring-sizes", "64,256,1024", "the ring sizes")
              .flag("group-capacity", "0",
                    "the range groups' capacity (0: the profile's)")
              .toggle("print-report", "print each compile report");
        },
        app::report},
       {"witness-profile", "the witness time by node, median over --reps",
        [](Flags &f) {
          proofs::bench::add_common_flags(f);
          app::add_size_flag(f);
          f.flag("reps", "10", "the proofs to time");
        },
        app::witness_profiles}});
}
